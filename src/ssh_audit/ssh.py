"""
   The MIT License (MIT)

   Copyright (C) 2017-2020 Joe Testa (jtesta@positronsecurity.com)
   Copyright (C) 2017 Andris Raugulis (moo@arthepsy.eu)

   Permission is hereby granted, free of charge, to any person obtaining a copy
   of this software and associated documentation files (the "Software"), to deal
   in the Software without restriction, including without limitation the rights
   to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
   copies of the Software, and to permit persons to whom the Software is
   furnished to do so, subject to the following conditions:

   The above copyright notice and this permission notice shall be included in
   all copies or substantial portions of the Software.

   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
   OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
   THE SOFTWARE.
"""
import base64
import binascii
import errno
import hashlib
import os
import random
import re
import select
import socket
import struct
import sys

# pylint: disable=unused-import
from typing import Dict, List, Set, Sequence, Tuple, Iterable  # noqa: F401
from typing import Callable, Optional, Union, Any  # noqa: F401

from ssh_audit import exitcodes
from ssh_audit.globals import SSH_HEADER
from ssh_audit.output import Output
from ssh_audit.readbuf import ReadBuf
from ssh_audit.utils import Utils
from ssh_audit.writebuf import WriteBuf


class SSH1:
    class CRC32:
        def __init__(self) -> None:
            self._table = [0] * 256
            for i in range(256):
                crc = 0
                n = i
                for _ in range(8):
                    x = (crc ^ n) & 1
                    crc = (crc >> 1) ^ (x * 0xedb88320)
                    n = n >> 1
                self._table[i] = crc

        def calc(self, v: bytes) -> int:
            crc, length = 0, len(v)
            for i in range(length):
                n = ord(v[i:i + 1])
                n = n ^ (crc & 0xff)
                crc = (crc >> 8) ^ self._table[n]
            return crc

    _crc32 = None  # type: Optional[SSH1.CRC32]
    CIPHERS = ['none', 'idea', 'des', '3des', 'tss', 'rc4', 'blowfish']
    AUTHS = ['none', 'rhosts', 'rsa', 'password', 'rhosts_rsa', 'tis', 'kerberos']

    @classmethod
    def crc32(cls, v: bytes) -> int:
        if cls._crc32 is None:
            cls._crc32 = cls.CRC32()
        return cls._crc32.calc(v)

    class KexDB:  # pylint: disable=too-few-public-methods
        FAIL_PLAINTEXT = 'no encryption/integrity'
        FAIL_OPENSSH37_REMOVE = 'removed since OpenSSH 3.7'
        FAIL_NA_BROKEN = 'not implemented in OpenSSH, broken algorithm'
        FAIL_NA_UNSAFE = 'not implemented in OpenSSH (server), unsafe algorithm'
        TEXT_CIPHER_IDEA = 'cipher used by commercial SSH'

        ALGORITHMS = {
            'key': {
                'ssh-rsa1': [['1.2.2']],
            },
            'enc': {
                'none': [['1.2.2'], [FAIL_PLAINTEXT]],
                'idea': [[None], [], [], [TEXT_CIPHER_IDEA]],
                'des': [['2.3.0C'], [FAIL_NA_UNSAFE]],
                '3des': [['1.2.2']],
                'tss': [[''], [FAIL_NA_BROKEN]],
                'rc4': [[], [FAIL_NA_BROKEN]],
                'blowfish': [['1.2.2']],
            },
            'aut': {
                'rhosts': [['1.2.2', '3.6'], [FAIL_OPENSSH37_REMOVE]],
                'rsa': [['1.2.2']],
                'password': [['1.2.2']],
                'rhosts_rsa': [['1.2.2']],
                'tis': [['1.2.2']],
                'kerberos': [['1.2.2', '3.6'], [FAIL_OPENSSH37_REMOVE]],
            }
        }  # type: Dict[str, Dict[str, List[List[Optional[str]]]]]

    class PublicKeyMessage:
        def __init__(self, cookie: bytes, skey: Tuple[int, int, int], hkey: Tuple[int, int, int], pflags: int, cmask: int, amask: int) -> None:
            if len(skey) != 3:
                raise ValueError('invalid server key pair: {}'.format(skey))
            if len(hkey) != 3:
                raise ValueError('invalid host key pair: {}'.format(hkey))
            self.__cookie = cookie
            self.__server_key = skey
            self.__host_key = hkey
            self.__protocol_flags = pflags
            self.__supported_ciphers_mask = cmask
            self.__supported_authentications_mask = amask

        @property
        def cookie(self) -> bytes:
            return self.__cookie

        @property
        def server_key_bits(self) -> int:
            return self.__server_key[0]

        @property
        def server_key_public_exponent(self) -> int:
            return self.__server_key[1]

        @property
        def server_key_public_modulus(self) -> int:
            return self.__server_key[2]

        @property
        def host_key_bits(self) -> int:
            return self.__host_key[0]

        @property
        def host_key_public_exponent(self) -> int:
            return self.__host_key[1]

        @property
        def host_key_public_modulus(self) -> int:
            return self.__host_key[2]

        @property
        def host_key_fingerprint_data(self) -> bytes:
            # pylint: disable=protected-access
            mod = WriteBuf._create_mpint(self.host_key_public_modulus, False)
            e = WriteBuf._create_mpint(self.host_key_public_exponent, False)
            return mod + e

        @property
        def protocol_flags(self) -> int:
            return self.__protocol_flags

        @property
        def supported_ciphers_mask(self) -> int:
            return self.__supported_ciphers_mask

        @property
        def supported_ciphers(self) -> List[str]:
            ciphers = []
            for i in range(len(SSH1.CIPHERS)):
                if self.__supported_ciphers_mask & (1 << i) != 0:
                    ciphers.append(Utils.to_text(SSH1.CIPHERS[i]))
            return ciphers

        @property
        def supported_authentications_mask(self) -> int:
            return self.__supported_authentications_mask

        @property
        def supported_authentications(self) -> List[str]:
            auths = []
            for i in range(1, len(SSH1.AUTHS)):
                if self.__supported_authentications_mask & (1 << i) != 0:
                    auths.append(Utils.to_text(SSH1.AUTHS[i]))
            return auths

        def write(self, wbuf: 'WriteBuf') -> None:
            wbuf.write(self.cookie)
            wbuf.write_int(self.server_key_bits)
            wbuf.write_mpint1(self.server_key_public_exponent)
            wbuf.write_mpint1(self.server_key_public_modulus)
            wbuf.write_int(self.host_key_bits)
            wbuf.write_mpint1(self.host_key_public_exponent)
            wbuf.write_mpint1(self.host_key_public_modulus)
            wbuf.write_int(self.protocol_flags)
            wbuf.write_int(self.supported_ciphers_mask)
            wbuf.write_int(self.supported_authentications_mask)

        @property
        def payload(self) -> bytes:
            wbuf = WriteBuf()
            self.write(wbuf)
            return wbuf.write_flush()

        @classmethod
        def parse(cls, payload: bytes) -> 'SSH1.PublicKeyMessage':
            buf = ReadBuf(payload)
            cookie = buf.read(8)
            server_key_bits = buf.read_int()
            server_key_exponent = buf.read_mpint1()
            server_key_modulus = buf.read_mpint1()
            skey = (server_key_bits, server_key_exponent, server_key_modulus)
            host_key_bits = buf.read_int()
            host_key_exponent = buf.read_mpint1()
            host_key_modulus = buf.read_mpint1()
            hkey = (host_key_bits, host_key_exponent, host_key_modulus)
            pflags = buf.read_int()
            cmask = buf.read_int()
            amask = buf.read_int()
            pkm = cls(cookie, skey, hkey, pflags, cmask, amask)
            return pkm


class SSH2:  # pylint: disable=too-few-public-methods
    class KexDB:  # pylint: disable=too-few-public-methods
        WARN_OPENSSH74_UNSAFE = 'disabled (in client) since OpenSSH 7.4, unsafe algorithm'
        WARN_OPENSSH72_LEGACY = 'disabled (in client) since OpenSSH 7.2, legacy algorithm'
        FAIL_OPENSSH70_LEGACY = 'removed since OpenSSH 7.0, legacy algorithm'
        FAIL_OPENSSH70_WEAK = 'removed (in server) and disabled (in client) since OpenSSH 7.0, weak algorithm'
        FAIL_OPENSSH70_LOGJAM = 'disabled (in client) since OpenSSH 7.0, logjam attack'
        INFO_OPENSSH69_CHACHA = 'default cipher since OpenSSH 6.9.'
        FAIL_OPENSSH67_UNSAFE = 'removed (in server) since OpenSSH 6.7, unsafe algorithm'
        FAIL_OPENSSH61_REMOVE = 'removed since OpenSSH 6.1, removed from specification'
        FAIL_OPENSSH31_REMOVE = 'removed since OpenSSH 3.1'
        FAIL_DBEAR67_DISABLED = 'disabled since Dropbear SSH 2015.67'
        FAIL_DBEAR53_DISABLED = 'disabled since Dropbear SSH 0.53'
        FAIL_DEPRECATED_CIPHER = 'deprecated cipher'
        FAIL_WEAK_CIPHER = 'using weak cipher'
        FAIL_WEAK_ALGORITHM = 'using weak/obsolete algorithm'
        FAIL_PLAINTEXT = 'no encryption/integrity'
        FAIL_DEPRECATED_MAC = 'deprecated MAC'
        FAIL_1024BIT_MODULUS = 'using small 1024-bit modulus'
        FAIL_UNPROVEN = 'using unproven algorithm'
        WARN_CURVES_WEAK = 'using weak elliptic curves'
        WARN_RNDSIG_KEY = 'using weak random number generator could reveal the key'
        WARN_HASH_WEAK = 'using weak hashing algorithm'
        WARN_CIPHER_MODE = 'using weak cipher mode'
        WARN_BLOCK_SIZE = 'using small 64-bit block size'
        WARN_CIPHER_WEAK = 'using weak cipher'
        WARN_ENCRYPT_AND_MAC = 'using encrypt-and-MAC mode'
        WARN_TAG_SIZE = 'using small 64-bit tag size'
        WARN_TAG_SIZE_96 = 'using small 96-bit tag size'
        WARN_EXPERIMENTAL = 'using experimental algorithm'
        WARN_OBSOLETE = 'using obsolete algorithm'
        WARN_UNTRUSTED = 'using untrusted algorithm'

        ALGORITHMS = {
            # Format: 'algorithm_name': [['version_first_appeared_in'], [reason_for_failure1, reason_for_failure2, ...], [warning1, warning2, ...]]
            'kex': {
                'diffie-hellman-group1-sha1': [['2.3.0,d0.28,l10.2', '6.6', '6.9'], [FAIL_1024BIT_MODULUS, FAIL_OPENSSH67_UNSAFE, FAIL_OPENSSH70_LOGJAM], [WARN_HASH_WEAK]],
                'gss-group1-sha1-toWM5Slw5Ew8Mqkay+al2g==': [[], [FAIL_1024BIT_MODULUS, FAIL_OPENSSH67_UNSAFE, FAIL_OPENSSH70_LOGJAM], [WARN_HASH_WEAK]],
                'gss-gex-sha1-toWM5Slw5Ew8Mqkay+al2g==': [[], [], [WARN_HASH_WEAK]],
                'gss-gex-sha1-': [[], [], [WARN_HASH_WEAK]],
                'gss-group1-sha1-': [[], [FAIL_1024BIT_MODULUS], [WARN_HASH_WEAK]],
                'gss-group14-sha1-': [[], [], [WARN_HASH_WEAK]],
                'gss-group14-sha1-toWM5Slw5Ew8Mqkay+al2g==': [[], [], [WARN_HASH_WEAK]],
                'gss-group14-sha256-': [[]],
                'gss-group14-sha256-toWM5Slw5Ew8Mqkay+al2g==': [[]],
                'gss-group15-sha512-': [[]],
                'gss-group15-sha512-toWM5Slw5Ew8Mqkay+al2g==': [[]],
                'gss-group16-sha512-': [[]],
                'gss-nistp256-sha256-': [[], [WARN_CURVES_WEAK]],
                'gss-curve25519-sha256-': [[]],
                'diffie-hellman-group1-sha256': [[], [FAIL_1024BIT_MODULUS]],
                'diffie-hellman-group14-sha1': [['3.9,d0.53,l10.6.0'], [], [WARN_HASH_WEAK]],
                'diffie-hellman-group14-sha256': [['7.3,d2016.73']],
                'diffie-hellman-group14-sha256@ssh.com': [[]],
                'diffie-hellman-group15-sha256': [[]],
                'diffie-hellman-group15-sha256@ssh.com': [[]],
                'diffie-hellman-group15-sha384@ssh.com': [[]],
                'diffie-hellman-group15-sha512': [[]],
                'diffie-hellman-group16-sha256': [[]],
                'diffie-hellman-group16-sha384@ssh.com': [[]],
                'diffie-hellman-group16-sha512': [['7.3,d2016.73']],
                'diffie-hellman-group16-sha512@ssh.com': [[]],
                'diffie-hellman-group17-sha512': [[]],
                'diffie-hellman-group18-sha512': [['7.3']],
                'diffie-hellman-group18-sha512@ssh.com': [[]],
                'diffie-hellman-group-exchange-sha1': [['2.3.0', '6.6', None], [FAIL_OPENSSH67_UNSAFE], [WARN_HASH_WEAK]],
                'diffie-hellman-group-exchange-sha256': [['4.4']],
                'diffie-hellman-group-exchange-sha256@ssh.com': [[]],
                'diffie-hellman-group-exchange-sha512@ssh.com': [[]],
                'ecdh-sha2-curve25519': [[], []],
                'ecdh-sha2-nistb233': [[], [WARN_CURVES_WEAK]],
                'ecdh-sha2-nistb409': [[], [WARN_CURVES_WEAK]],
                'ecdh-sha2-nistk163': [[], [WARN_CURVES_WEAK]],
                'ecdh-sha2-nistk233': [[], [WARN_CURVES_WEAK]],
                'ecdh-sha2-nistk283': [[], [WARN_CURVES_WEAK]],
                'ecdh-sha2-nistk409': [[], [WARN_CURVES_WEAK]],
                'ecdh-sha2-nistp192': [[], [WARN_CURVES_WEAK]],
                'ecdh-sha2-nistp224': [[], [WARN_CURVES_WEAK]],
                'ecdh-sha2-nistp256': [['5.7,d2013.62,l10.6.0'], [WARN_CURVES_WEAK]],
                'ecdh-sha2-nistp384': [['5.7,d2013.62'], [WARN_CURVES_WEAK]],
                'ecdh-sha2-nistp521': [['5.7,d2013.62'], [WARN_CURVES_WEAK]],
                'ecdh-sha2-nistt571': [[], [WARN_CURVES_WEAK]],
                'ecdh-sha2-1.3.132.0.10': [[]],  # ECDH over secp256k1 (i.e.: the Bitcoin curve)
                'curve25519-sha256@libssh.org': [['6.5,d2013.62,l10.6.0']],
                'curve25519-sha256': [['7.4,d2018.76']],
                'curve448-sha512': [[]],
                'kexguess2@matt.ucc.asn.au': [['d2013.57']],
                'rsa1024-sha1': [[], [FAIL_1024BIT_MODULUS], [WARN_HASH_WEAK]],
                'rsa2048-sha256': [[]],
                'sntrup4591761x25519-sha512@tinyssh.org': [['8.0'], [], [WARN_EXPERIMENTAL]],
                'kexAlgoCurve25519SHA256': [[]],
                'Curve25519SHA256': [[]],
                'ext-info-c': [[]],  # Extension negotiation (RFC 8308)
                'ext-info-s': [[]],  # Extension negotiation (RFC 8308)
            },
            'key': {
                'ssh-rsa1': [[], [FAIL_WEAK_ALGORITHM]],
                'rsa-sha2-256': [['7.2']],
                'rsa-sha2-512': [['7.2']],
                'ssh-ed25519': [['6.5,l10.7.0']],
                'ssh-ed25519-cert-v01@openssh.com': [['6.5']],
                'ssh-rsa': [['2.5.0,d0.28,l10.2'], [WARN_HASH_WEAK]],
                'ssh-dss': [['2.1.0,d0.28,l10.2', '6.9'], [FAIL_1024BIT_MODULUS, FAIL_OPENSSH70_WEAK], [WARN_RNDSIG_KEY]],
                'ecdsa-sha2-nistp256': [['5.7,d2013.62,l10.6.4'], [WARN_CURVES_WEAK], [WARN_RNDSIG_KEY]],
                'ecdsa-sha2-nistp384': [['5.7,d2013.62,l10.6.4'], [WARN_CURVES_WEAK], [WARN_RNDSIG_KEY]],
                'ecdsa-sha2-nistp521': [['5.7,d2013.62,l10.6.4'], [WARN_CURVES_WEAK], [WARN_RNDSIG_KEY]],
                'ecdsa-sha2-1.3.132.0.10': [[], [], [WARN_RNDSIG_KEY]],  # ECDSA over secp256k1 (i.e.: the Bitcoin curve)
                'x509v3-sign-dss': [[], [FAIL_1024BIT_MODULUS, FAIL_OPENSSH70_WEAK], [WARN_RNDSIG_KEY]],
                'x509v3-sign-rsa': [[], [], [WARN_HASH_WEAK]],
                'x509v3-sign-rsa-sha256@ssh.com': [[]],
                'x509v3-ssh-dss': [[], [FAIL_1024BIT_MODULUS, FAIL_OPENSSH70_WEAK], [WARN_RNDSIG_KEY]],
                'x509v3-ssh-rsa': [[], [], [WARN_HASH_WEAK]],
                'ssh-rsa-cert-v00@openssh.com': [['5.4', '6.9'], [FAIL_OPENSSH70_LEGACY], []],
                'ssh-dss-cert-v00@openssh.com': [['5.4', '6.9'], [FAIL_1024BIT_MODULUS, FAIL_OPENSSH70_LEGACY], [WARN_RNDSIG_KEY]],
                'ssh-rsa-cert-v01@openssh.com': [['5.6']],
                'ssh-dss-cert-v01@openssh.com': [['5.6', '6.9'], [FAIL_1024BIT_MODULUS, FAIL_OPENSSH70_WEAK], [WARN_RNDSIG_KEY]],
                'ecdsa-sha2-nistp256-cert-v01@openssh.com': [['5.7'], [WARN_CURVES_WEAK], [WARN_RNDSIG_KEY]],
                'ecdsa-sha2-nistp384-cert-v01@openssh.com': [['5.7'], [WARN_CURVES_WEAK], [WARN_RNDSIG_KEY]],
                'ecdsa-sha2-nistp521-cert-v01@openssh.com': [['5.7'], [WARN_CURVES_WEAK], [WARN_RNDSIG_KEY]],
                'rsa-sha2-256-cert-v01@openssh.com': [['7.8']],
                'rsa-sha2-512-cert-v01@openssh.com': [['7.8']],
                'ssh-rsa-sha256@ssh.com': [[]],
                'ssh-dss-sha256@ssh.com': [[], [FAIL_1024BIT_MODULUS]],
                'sk-ecdsa-sha2-nistp256-cert-v01@openssh.com': [['8.2'], [WARN_CURVES_WEAK], [WARN_RNDSIG_KEY]],
                'sk-ecdsa-sha2-nistp256@openssh.com': [['8.2'], [WARN_CURVES_WEAK], [WARN_RNDSIG_KEY]],
                'sk-ssh-ed25519-cert-v01@openssh.com': [['8.2']],
                'sk-ssh-ed25519@openssh.com': [['8.2']],
                'ssh-gost2001': [[], [], [WARN_UNTRUSTED]],
                'ssh-gost2012-256': [[], [], [WARN_UNTRUSTED]],
                'ssh-gost2012-512': [[], [], [WARN_UNTRUSTED]],
                'spi-sign-rsa': [[]],
                'ssh-ed448': [[]],
                'x509v3-ecdsa-sha2-nistp256': [[], [WARN_CURVES_WEAK]],
                'x509v3-ecdsa-sha2-nistp384': [[], [WARN_CURVES_WEAK]],
                'x509v3-ecdsa-sha2-nistp521': [[], [WARN_CURVES_WEAK]],
                'x509v3-rsa2048-sha256': [[]],
            },
            'enc': {
                'none': [['1.2.2,d2013.56,l10.2'], [FAIL_PLAINTEXT]],
                'des': [[], [FAIL_WEAK_CIPHER], [WARN_CIPHER_MODE, WARN_BLOCK_SIZE]],
                'des-cbc': [[], [FAIL_WEAK_CIPHER], [WARN_CIPHER_MODE, WARN_BLOCK_SIZE]],
                'des-cbc@ssh.com': [[], [FAIL_WEAK_CIPHER], [WARN_CIPHER_MODE, WARN_BLOCK_SIZE]],
                'des-cbc-ssh1': [[], [FAIL_WEAK_CIPHER], [WARN_CIPHER_MODE, WARN_BLOCK_SIZE]],
                '3des': [[], [FAIL_OPENSSH67_UNSAFE], [WARN_OPENSSH74_UNSAFE, WARN_CIPHER_WEAK, WARN_CIPHER_MODE, WARN_BLOCK_SIZE]],
                '3des-cbc': [['1.2.2,d0.28,l10.2', '6.6', None], [FAIL_OPENSSH67_UNSAFE], [WARN_OPENSSH74_UNSAFE, WARN_CIPHER_WEAK, WARN_CIPHER_MODE, WARN_BLOCK_SIZE]],
                '3des-ctr': [['d0.52'], [FAIL_WEAK_CIPHER]],
                'blowfish': [[], [FAIL_WEAK_ALGORITHM], [WARN_BLOCK_SIZE]],
                'blowfish-cbc': [['1.2.2,d0.28,l10.2', '6.6,d0.52', '7.1,d0.52'], [FAIL_OPENSSH67_UNSAFE, FAIL_DBEAR53_DISABLED], [WARN_OPENSSH72_LEGACY, WARN_CIPHER_MODE, WARN_BLOCK_SIZE]],
                'blowfish-ctr': [[], [FAIL_OPENSSH67_UNSAFE, FAIL_DBEAR53_DISABLED], [WARN_OPENSSH72_LEGACY, WARN_CIPHER_MODE, WARN_BLOCK_SIZE]],
                'twofish-cbc': [['d0.28', 'd2014.66'], [FAIL_DBEAR67_DISABLED], [WARN_CIPHER_MODE]],
                'twofish128-cbc': [['d0.47', 'd2014.66'], [FAIL_DBEAR67_DISABLED], [WARN_CIPHER_MODE]],
                'twofish192-cbc': [[], [], [WARN_CIPHER_MODE]],
                'twofish256-cbc': [['d0.47', 'd2014.66'], [FAIL_DBEAR67_DISABLED], [WARN_CIPHER_MODE]],
                'twofish-ctr': [[]],
                'twofish128-ctr': [['d2015.68']],
                'twofish192-ctr': [[]],
                'twofish256-ctr': [['d2015.68']],
                'serpent128-cbc': [[], [FAIL_DEPRECATED_CIPHER], [WARN_CIPHER_MODE]],
                'serpent192-cbc': [[], [FAIL_DEPRECATED_CIPHER], [WARN_CIPHER_MODE]],
                'serpent256-cbc': [[], [FAIL_DEPRECATED_CIPHER], [WARN_CIPHER_MODE]],
                'serpent128-ctr': [[], [FAIL_DEPRECATED_CIPHER]],
                'serpent192-ctr': [[], [FAIL_DEPRECATED_CIPHER]],
                'serpent256-ctr': [[], [FAIL_DEPRECATED_CIPHER]],
                'idea-cbc': [[], [FAIL_DEPRECATED_CIPHER], [WARN_CIPHER_MODE]],
                'idea-ctr': [[], [FAIL_DEPRECATED_CIPHER]],
                'cast128-ctr': [[], [FAIL_DEPRECATED_CIPHER]],
                'cast128-cbc': [['2.1.0', '6.6', '7.1'], [FAIL_OPENSSH67_UNSAFE], [WARN_OPENSSH72_LEGACY, WARN_CIPHER_MODE, WARN_BLOCK_SIZE]],
                'arcfour': [['2.1.0', '6.6', '7.1'], [FAIL_OPENSSH67_UNSAFE], [WARN_OPENSSH72_LEGACY, WARN_CIPHER_WEAK]],
                'arcfour128': [['4.2', '6.6', '7.1'], [FAIL_OPENSSH67_UNSAFE], [WARN_OPENSSH72_LEGACY, WARN_CIPHER_WEAK]],
                'arcfour256': [['4.2', '6.6', '7.1'], [FAIL_OPENSSH67_UNSAFE], [WARN_OPENSSH72_LEGACY, WARN_CIPHER_WEAK]],
                'aes128-cbc': [['2.3.0,d0.28,l10.2', '6.6', None], [FAIL_OPENSSH67_UNSAFE], [WARN_CIPHER_MODE]],
                'aes192-cbc': [['2.3.0,l10.2', '6.6', None], [FAIL_OPENSSH67_UNSAFE], [WARN_CIPHER_MODE]],
                'aes256-cbc': [['2.3.0,d0.47,l10.2', '6.6', None], [FAIL_OPENSSH67_UNSAFE], [WARN_CIPHER_MODE]],
                'rijndael128-cbc': [['2.3.0', '3.0.2'], [FAIL_OPENSSH31_REMOVE], [WARN_CIPHER_MODE]],
                'rijndael192-cbc': [['2.3.0', '3.0.2'], [FAIL_OPENSSH31_REMOVE], [WARN_CIPHER_MODE]],
                'rijndael256-cbc': [['2.3.0', '3.0.2'], [FAIL_OPENSSH31_REMOVE], [WARN_CIPHER_MODE]],
                'rijndael-cbc@lysator.liu.se': [['2.3.0', '6.6', '7.1'], [FAIL_OPENSSH67_UNSAFE], [WARN_OPENSSH72_LEGACY, WARN_CIPHER_MODE]],
                'aes128-ctr': [['3.7,d0.52,l10.4.1']],
                'aes192-ctr': [['3.7,l10.4.1']],
                'aes256-ctr': [['3.7,d0.52,l10.4.1']],
                'aes128-gcm': [[]],
                'aes256-gcm': [[]],
                'AEAD_AES_128_GCM': [[]],
                'AEAD_AES_256_GCM': [[]],
                'aes128-gcm@openssh.com': [['6.2']],
                'aes256-gcm@openssh.com': [['6.2']],
                'chacha20-poly1305': [[], [], [], [INFO_OPENSSH69_CHACHA]],
                'chacha20-poly1305@openssh.com': [['6.5'], [], [], [INFO_OPENSSH69_CHACHA]],
                'camellia128-cbc': [[], [], [WARN_CIPHER_MODE]],
                'camellia128-ctr': [[]],
                'camellia192-cbc': [[], [], [WARN_CIPHER_MODE]],
                'camellia192-ctr': [[]],
                'camellia256-cbc': [[], [], [WARN_CIPHER_MODE]],
                'camellia256-ctr': [[]],
                'crypticore128@ssh.com': [[], [FAIL_UNPROVEN]],
                'seed-cbc@ssh.com': [[], [], [WARN_OBSOLETE, WARN_CIPHER_MODE]],
            },
            'mac': {
                'none': [['d2013.56'], [FAIL_PLAINTEXT]],
                'hmac-sha1': [['2.1.0,d0.28,l10.2'], [], [WARN_ENCRYPT_AND_MAC, WARN_HASH_WEAK]],
                'hmac-sha1-96': [['2.5.0,d0.47', '6.6', '7.1'], [FAIL_OPENSSH67_UNSAFE], [WARN_OPENSSH72_LEGACY, WARN_ENCRYPT_AND_MAC, WARN_HASH_WEAK]],
                'hmac-sha2-56': [[], [], [WARN_TAG_SIZE, WARN_ENCRYPT_AND_MAC]],
                'hmac-sha2-224': [[], [], [WARN_TAG_SIZE, WARN_ENCRYPT_AND_MAC]],
                'hmac-sha2-256': [['5.9,d2013.56,l10.7.0'], [], [WARN_ENCRYPT_AND_MAC]],
                'hmac-sha2-256-96': [['5.9', '6.0'], [FAIL_OPENSSH61_REMOVE], [WARN_ENCRYPT_AND_MAC]],
                'hmac-sha2-384': [[], [], [WARN_ENCRYPT_AND_MAC]],
                'hmac-sha2-512': [['5.9,d2013.56,l10.7.0'], [], [WARN_ENCRYPT_AND_MAC]],
                'hmac-sha2-512-96': [['5.9', '6.0'], [FAIL_OPENSSH61_REMOVE], [WARN_ENCRYPT_AND_MAC]],
                'hmac-sha3-224': [[], [], [WARN_ENCRYPT_AND_MAC]],
                'hmac-sha3-256': [[], [], [WARN_ENCRYPT_AND_MAC]],
                'hmac-sha3-384': [[], [], [WARN_ENCRYPT_AND_MAC]],
                'hmac-sha3-512': [[], [], [WARN_ENCRYPT_AND_MAC]],
                'hmac-sha256': [[], [], [WARN_ENCRYPT_AND_MAC]],
                'hmac-sha256-96@ssh.com': [[], [], [WARN_ENCRYPT_AND_MAC, WARN_TAG_SIZE]],
                'hmac-sha256@ssh.com': [[], [], [WARN_ENCRYPT_AND_MAC]],
                'hmac-sha512': [[], [], [WARN_ENCRYPT_AND_MAC]],
                'hmac-sha512@ssh.com': [[], [], [WARN_ENCRYPT_AND_MAC]],
                'hmac-md5': [['2.1.0,d0.28', '6.6', '7.1'], [FAIL_OPENSSH67_UNSAFE], [WARN_OPENSSH72_LEGACY, WARN_ENCRYPT_AND_MAC, WARN_HASH_WEAK]],
                'hmac-md5-96': [['2.5.0', '6.6', '7.1'], [FAIL_OPENSSH67_UNSAFE], [WARN_OPENSSH72_LEGACY, WARN_ENCRYPT_AND_MAC, WARN_HASH_WEAK]],
                'hmac-ripemd': [[], [FAIL_DEPRECATED_MAC], [WARN_OPENSSH72_LEGACY, WARN_ENCRYPT_AND_MAC]],
                'hmac-ripemd160': [['2.5.0', '6.6', '7.1'], [FAIL_OPENSSH67_UNSAFE], [WARN_OPENSSH72_LEGACY, WARN_ENCRYPT_AND_MAC]],
                'hmac-ripemd160@openssh.com': [['2.1.0', '6.6', '7.1'], [FAIL_OPENSSH67_UNSAFE], [WARN_OPENSSH72_LEGACY, WARN_ENCRYPT_AND_MAC]],
                'umac-64@openssh.com': [['4.7'], [], [WARN_ENCRYPT_AND_MAC, WARN_TAG_SIZE]],
                'umac-128@openssh.com': [['6.2'], [], [WARN_ENCRYPT_AND_MAC]],
                'hmac-sha1-etm@openssh.com': [['6.2'], [], [WARN_HASH_WEAK]],
                'hmac-sha1-96-etm@openssh.com': [['6.2', '6.6', None], [FAIL_OPENSSH67_UNSAFE], [WARN_HASH_WEAK]],
                'hmac-sha2-256-96-etm@openssh.com': [[], [], [WARN_TAG_SIZE_96]],  # Despite the @openssh.com tag, it doesn't appear that this was ever shipped with OpenSSH; it is only implemented in AsyncSSH (?).
                'hmac-sha2-512-96-etm@openssh.com': [[], [], [WARN_TAG_SIZE_96]],  # Despite the @openssh.com tag, it doesn't appear that this was ever shipped with OpenSSH; it is only implemented in AsyncSSH (?).
                'hmac-sha2-256-etm@openssh.com': [['6.2']],
                'hmac-sha2-512-etm@openssh.com': [['6.2']],
                'hmac-md5-etm@openssh.com': [['6.2', '6.6', '7.1'], [FAIL_OPENSSH67_UNSAFE], [WARN_OPENSSH72_LEGACY, WARN_HASH_WEAK]],
                'hmac-md5-96-etm@openssh.com': [['6.2', '6.6', '7.1'], [FAIL_OPENSSH67_UNSAFE], [WARN_OPENSSH72_LEGACY, WARN_HASH_WEAK]],
                'hmac-ripemd160-etm@openssh.com': [['6.2', '6.6', '7.1'], [FAIL_OPENSSH67_UNSAFE], [WARN_OPENSSH72_LEGACY]],
                'umac-32@openssh.com': [[], [], [WARN_ENCRYPT_AND_MAC, WARN_TAG_SIZE]],  # Despite having the @openssh.com suffix, this may never have shipped with OpenSSH (!).
                'umac-64-etm@openssh.com': [['6.2'], [], [WARN_TAG_SIZE]],
                'umac-96@openssh.com': [[], [], [WARN_ENCRYPT_AND_MAC]],  # Despite having the @openssh.com suffix, this may never have shipped with OpenSSH (!).
                'umac-128-etm@openssh.com': [['6.2']],
                'aes128-gcm': [[]],
                'aes256-gcm': [[]],
                'chacha20-poly1305@openssh.com': [[]],  # Despite the @openssh.com tag, this was never shipped as a MAC in OpenSSH (only as a cipher); it is only implemented as a MAC in Syncplify.
                'crypticore-mac@ssh.com': [[], [FAIL_UNPROVEN]],
            }
        }  # type: Dict[str, Dict[str, List[List[Optional[str]]]]]

    class KexParty:
        def __init__(self, enc: List[str], mac: List[str], compression: List[str], languages: List[str]) -> None:
            self.__enc = enc
            self.__mac = mac
            self.__compression = compression
            self.__languages = languages

        @property
        def encryption(self) -> List[str]:
            return self.__enc

        @property
        def mac(self) -> List[str]:
            return self.__mac

        @property
        def compression(self) -> List[str]:
            return self.__compression

        @property
        def languages(self) -> List[str]:
            return self.__languages

    class Kex:
        def __init__(self, cookie: bytes, kex_algs: List[str], key_algs: List[str], cli: 'SSH2.KexParty', srv: 'SSH2.KexParty', follows: bool, unused: int = 0) -> None:
            self.__cookie = cookie
            self.__kex_algs = kex_algs
            self.__key_algs = key_algs
            self.__client = cli
            self.__server = srv
            self.__follows = follows
            self.__unused = unused

            self.__rsa_key_sizes = {}  # type: Dict[str, Tuple[int, int]]
            self.__dh_modulus_sizes = {}  # type: Dict[str, Tuple[int, int]]
            self.__host_keys = {}  # type: Dict[str, bytes]

        @property
        def cookie(self) -> bytes:
            return self.__cookie

        @property
        def kex_algorithms(self) -> List[str]:
            return self.__kex_algs

        @property
        def key_algorithms(self) -> List[str]:
            return self.__key_algs

        # client_to_server
        @property
        def client(self) -> 'SSH2.KexParty':
            return self.__client

        # server_to_client
        @property
        def server(self) -> 'SSH2.KexParty':
            return self.__server

        @property
        def follows(self) -> bool:
            return self.__follows

        @property
        def unused(self) -> int:
            return self.__unused

        def set_rsa_key_size(self, rsa_type: str, hostkey_size: int, ca_size: int = -1) -> None:
            self.__rsa_key_sizes[rsa_type] = (hostkey_size, ca_size)

        def rsa_key_sizes(self) -> Dict[str, Tuple[int, int]]:
            return self.__rsa_key_sizes

        def set_dh_modulus_size(self, gex_alg: str, modulus_size: int) -> None:
            self.__dh_modulus_sizes[gex_alg] = (modulus_size, -1)

        def dh_modulus_sizes(self) -> Dict[str, Tuple[int, int]]:
            return self.__dh_modulus_sizes

        def set_host_key(self, key_type: str, hostkey: bytes) -> None:
            self.__host_keys[key_type] = hostkey

        def host_keys(self) -> Dict[str, bytes]:
            return self.__host_keys

        def write(self, wbuf: 'WriteBuf') -> None:
            wbuf.write(self.cookie)
            wbuf.write_list(self.kex_algorithms)
            wbuf.write_list(self.key_algorithms)
            wbuf.write_list(self.client.encryption)
            wbuf.write_list(self.server.encryption)
            wbuf.write_list(self.client.mac)
            wbuf.write_list(self.server.mac)
            wbuf.write_list(self.client.compression)
            wbuf.write_list(self.server.compression)
            wbuf.write_list(self.client.languages)
            wbuf.write_list(self.server.languages)
            wbuf.write_bool(self.follows)
            wbuf.write_int(self.__unused)

        @property
        def payload(self) -> bytes:
            wbuf = WriteBuf()
            self.write(wbuf)
            return wbuf.write_flush()

        @classmethod
        def parse(cls, payload: bytes) -> 'SSH2.Kex':
            buf = ReadBuf(payload)
            cookie = buf.read(16)
            kex_algs = buf.read_list()
            key_algs = buf.read_list()
            cli_enc = buf.read_list()
            srv_enc = buf.read_list()
            cli_mac = buf.read_list()
            srv_mac = buf.read_list()
            cli_compression = buf.read_list()
            srv_compression = buf.read_list()
            cli_languages = buf.read_list()
            srv_languages = buf.read_list()
            follows = buf.read_bool()
            unused = buf.read_int()
            cli = SSH2.KexParty(cli_enc, cli_mac, cli_compression, cli_languages)
            srv = SSH2.KexParty(srv_enc, srv_mac, srv_compression, srv_languages)
            kex = cls(cookie, kex_algs, key_algs, cli, srv, follows, unused)
            return kex

    # Obtains host keys, checks their size, and derives their fingerprints.
    class HostKeyTest:
        # Tracks the RSA host key types.  As of this writing, testing one in this family yields valid results for the rest.
        RSA_FAMILY = ['ssh-rsa', 'rsa-sha2-256', 'rsa-sha2-512']

        # Dict holding the host key types we should extract & parse.  'cert' is True to denote that a host key type handles certificates (thus requires additional parsing).  'variable_key_len' is True for host key types that can have variable sizes (True only for RSA types, as the rest are of fixed-size).  After the host key type is fully parsed, the key 'parsed' is added with a value of True.
        HOST_KEY_TYPES = {
            'ssh-rsa':      {'cert': False, 'variable_key_len': True},
            'rsa-sha2-256': {'cert': False, 'variable_key_len': True},
            'rsa-sha2-512': {'cert': False, 'variable_key_len': True},

            'ssh-rsa-cert-v01@openssh.com':     {'cert': True, 'variable_key_len': True},

            'ssh-ed25519':                      {'cert': False, 'variable_key_len': False},
            'ssh-ed25519-cert-v01@openssh.com': {'cert': True, 'variable_key_len': False},
        }

        @staticmethod
        def run(s: 'SSH.Socket', server_kex: 'SSH2.Kex') -> None:
            KEX_TO_DHGROUP = {
                'diffie-hellman-group1-sha1': KexGroup1,
                'diffie-hellman-group14-sha1': KexGroup14_SHA1,
                'diffie-hellman-group14-sha256': KexGroup14_SHA256,
                'curve25519-sha256': KexCurve25519_SHA256,
                'curve25519-sha256@libssh.org': KexCurve25519_SHA256,
                'diffie-hellman-group16-sha512': KexGroup16_SHA512,
                'diffie-hellman-group18-sha512': KexGroup18_SHA512,
                'diffie-hellman-group-exchange-sha1': KexGroupExchange_SHA1,
                'diffie-hellman-group-exchange-sha256': KexGroupExchange_SHA256,
                'ecdh-sha2-nistp256': KexNISTP256,
                'ecdh-sha2-nistp384': KexNISTP384,
                'ecdh-sha2-nistp521': KexNISTP521,
                # 'kexguess2@matt.ucc.asn.au': ???
            }

            # Pick the first kex algorithm that the server supports, which we
            # happen to support as well.
            kex_str = None
            kex_group = None
            for server_kex_alg in server_kex.kex_algorithms:
                if server_kex_alg in KEX_TO_DHGROUP:
                    kex_str = server_kex_alg
                    kex_group = KEX_TO_DHGROUP[kex_str]()
                    break

            if kex_str is not None and kex_group is not None:
                SSH2.HostKeyTest.perform_test(s, server_kex, kex_str, kex_group, SSH2.HostKeyTest.HOST_KEY_TYPES)

        @staticmethod
        def perform_test(s: 'SSH.Socket', server_kex: 'SSH2.Kex', kex_str: str, kex_group: 'KexDH', host_key_types: Dict[str, Dict[str, bool]]) -> None:
            hostkey_modulus_size = 0
            ca_modulus_size = 0

            # If the connection still exists, close it so we can test
            # using a clean slate (otherwise it may exist in a non-testable
            # state).
            if s.is_connected():
                s.close()

            # For each host key type...
            for host_key_type in host_key_types:
                # Skip those already handled (i.e.: those in the RSA family, as testing one tests them all).
                if 'parsed' in host_key_types[host_key_type] and host_key_types[host_key_type]['parsed']:
                    continue

                # If this host key type is supported by the server, we test it.
                if host_key_type in server_kex.key_algorithms:
                    cert = host_key_types[host_key_type]['cert']
                    variable_key_len = host_key_types[host_key_type]['variable_key_len']

                    # If the connection is closed, re-open it and get the kex again.
                    if not s.is_connected():
                        err = s.connect()
                        if err is not None:
                            return

                        _, _, err = s.get_banner()
                        if err is not None:
                            s.close()
                            return

                        # Parse the server's initial KEX.
                        packet_type = 0  # pylint: disable=unused-variable
                        packet_type, payload = s.read_packet()
                        SSH2.Kex.parse(payload)

                    # Send the server our KEXINIT message, using only our
                    # selected kex and host key type.  Send the server's own
                    # list of ciphers and MACs back to it (this doesn't
                    # matter, really).
                    client_kex = SSH2.Kex(os.urandom(16), [kex_str], [host_key_type], server_kex.client, server_kex.server, False, 0)

                    s.write_byte(SSH.Protocol.MSG_KEXINIT)
                    client_kex.write(s)
                    s.send_packet()

                    # Do the initial DH exchange.  The server responds back
                    # with the host key and its length.  Bingo.  We also get back the host key fingerprint.
                    kex_group.send_init(s)
                    host_key = kex_group.recv_reply(s, variable_key_len)
                    if host_key is not None:
                        server_kex.set_host_key(host_key_type, host_key)

                    hostkey_modulus_size = kex_group.get_hostkey_size()
                    ca_modulus_size = kex_group.get_ca_size()

                    # Close the socket, as the connection has
                    # been put in a state that later tests can't use.
                    s.close()

                    # If the host key modulus or CA modulus was successfully parsed, check to see that its a safe size.
                    if hostkey_modulus_size > 0 or ca_modulus_size > 0:
                        # Set the hostkey size for all RSA key types since 'ssh-rsa',
                        # 'rsa-sha2-256', etc. are all using the same host key.
                        # Note, however, that this may change in the future.
                        if cert is False and host_key_type in SSH2.HostKeyTest.RSA_FAMILY:
                            for rsa_type in SSH2.HostKeyTest.RSA_FAMILY:
                                server_kex.set_rsa_key_size(rsa_type, hostkey_modulus_size)
                        elif cert is True:
                            server_kex.set_rsa_key_size(host_key_type, hostkey_modulus_size, ca_modulus_size)

                        # Keys smaller than 2048 result in a failure.  Update the database accordingly.
                        if (cert is False) and (hostkey_modulus_size < 2048):
                            for rsa_type in SSH2.HostKeyTest.RSA_FAMILY:
                                alg_list = SSH2.KexDB.ALGORITHMS['key'][rsa_type]
                                alg_list.append(['using small %d-bit modulus' % hostkey_modulus_size])
                        elif (cert is True) and ((hostkey_modulus_size < 2048) or (ca_modulus_size > 0 and ca_modulus_size < 2048)):  # pylint: disable=chained-comparison
                            alg_list = SSH2.KexDB.ALGORITHMS['key'][host_key_type]
                            min_modulus = min(hostkey_modulus_size, ca_modulus_size)
                            min_modulus = min_modulus if min_modulus > 0 else max(hostkey_modulus_size, ca_modulus_size)
                            alg_list.append(['using small %d-bit modulus' % min_modulus])

                    # If this host key type is in the RSA family, then mark them all as parsed (since results in one are valid for them all).
                    if host_key_type in SSH2.HostKeyTest.RSA_FAMILY:
                        for rsa_type in SSH2.HostKeyTest.RSA_FAMILY:
                            host_key_types[rsa_type]['parsed'] = True
                    else:
                        host_key_types[host_key_type]['parsed'] = True

    # Performs DH group exchanges to find what moduli are supported, and checks
    # their size.
    class GEXTest:

        # Creates a new connection to the server.  Returns True on success, or False.
        @staticmethod
        def reconnect(s: 'SSH.Socket', gex_alg: str) -> bool:
            if s.is_connected():
                return True

            err = s.connect()
            if err is not None:
                return False

            unused = None  # pylint: disable=unused-variable
            unused2 = None  # pylint: disable=unused-variable
            unused, unused2, err = s.get_banner()
            if err is not None:
                s.close()
                return False

            # Parse the server's initial KEX.
            packet_type = 0  # pylint: disable=unused-variable
            packet_type, payload = s.read_packet(2)
            kex = SSH2.Kex.parse(payload)

            # Send our KEX using the specified group-exchange and most of the
            # server's own values.
            client_kex = SSH2.Kex(os.urandom(16), [gex_alg], kex.key_algorithms, kex.client, kex.server, False, 0)
            s.write_byte(SSH.Protocol.MSG_KEXINIT)
            client_kex.write(s)
            s.send_packet()
            return True

        # Runs the DH moduli test against the specified target.
        @staticmethod
        def run(s: 'SSH.Socket', kex: 'SSH2.Kex') -> None:
            GEX_ALGS = {
                'diffie-hellman-group-exchange-sha1': KexGroupExchange_SHA1,
                'diffie-hellman-group-exchange-sha256': KexGroupExchange_SHA256,
            }

            # The previous RSA tests put the server in a state we can't
            # test.  So we need a new connection to start with a clean
            # slate.
            if s.is_connected():
                s.close()

            # Check if the server supports any of the group-exchange
            # algorithms.  If so, test each one.
            for gex_alg in GEX_ALGS:
                if gex_alg in kex.kex_algorithms:

                    if SSH2.GEXTest.reconnect(s, gex_alg) is False:
                        break

                    kex_group = GEX_ALGS[gex_alg]()
                    smallest_modulus = -1

                    # First try a range of weak sizes.
                    try:
                        kex_group.send_init_gex(s, 512, 1024, 1536)
                        kex_group.recv_reply(s, False)

                        # Its been observed that servers will return a group
                        # larger than the requested max.  So just because we
                        # got here, doesn't mean the server is vulnerable...
                        smallest_modulus = kex_group.get_dh_modulus_size()

                    except Exception:
                        pass
                    finally:
                        s.close()

                    # Try an array of specific modulus sizes... one at a time.
                    reconnect_failed = False
                    for bits in [512, 768, 1024, 1536, 2048, 3072, 4096]:

                        # If we found one modulus size already, but we're about
                        # to test a larger one, don't bother.
                        if bits >= smallest_modulus > 0:
                            break

                        if SSH2.GEXTest.reconnect(s, gex_alg) is False:
                            reconnect_failed = True
                            break

                        try:
                            kex_group.send_init_gex(s, bits, bits, bits)
                            kex_group.recv_reply(s, False)
                            smallest_modulus = kex_group.get_dh_modulus_size()
                        except Exception:
                            # import traceback
                            # print(traceback.format_exc())
                            pass
                        finally:
                            # The server is in a state that is not re-testable,
                            # so there's nothing else to do with this open
                            # connection.
                            s.close()

                    if smallest_modulus > 0:
                        kex.set_dh_modulus_size(gex_alg, smallest_modulus)

                        # We flag moduli smaller than 2048 as a failure.
                        if smallest_modulus < 2048:
                            text = 'using small %d-bit modulus' % smallest_modulus
                            lst = SSH2.KexDB.ALGORITHMS['kex'][gex_alg]
                            # For 'diffie-hellman-group-exchange-sha256', add
                            # a failure reason.
                            if len(lst) == 1:
                                lst.append([text])
                            # For 'diffie-hellman-group-exchange-sha1', delete
                            # the existing failure reason (which is vague), and
                            # insert our own.
                            else:
                                del lst[1]
                                lst.insert(1, [text])

                    if reconnect_failed:
                        break


class SSH:  # pylint: disable=too-few-public-methods
    class Protocol:  # pylint: disable=too-few-public-methods
        SMSG_PUBLIC_KEY = 2
        MSG_DEBUG = 4
        MSG_KEXINIT = 20
        MSG_NEWKEYS = 21
        MSG_KEXDH_INIT = 30
        MSG_KEXDH_REPLY = 31
        MSG_KEXDH_GEX_REQUEST = 34
        MSG_KEXDH_GEX_GROUP = 31
        MSG_KEXDH_GEX_INIT = 32
        MSG_KEXDH_GEX_REPLY = 33

    class Product:  # pylint: disable=too-few-public-methods
        OpenSSH = 'OpenSSH'
        DropbearSSH = 'Dropbear SSH'
        LibSSH = 'libssh'
        TinySSH = 'TinySSH'
        PuTTY = 'PuTTY'

    class Software:
        def __init__(self, vendor: Optional[str], product: str, version: str, patch: Optional[str], os_version: Optional[str]) -> None:
            self.__vendor = vendor
            self.__product = product
            self.__version = version
            self.__patch = patch
            self.__os = os_version

        @property
        def vendor(self) -> Optional[str]:
            return self.__vendor

        @property
        def product(self) -> str:
            return self.__product

        @property
        def version(self) -> str:
            return self.__version

        @property
        def patch(self) -> Optional[str]:
            return self.__patch

        @property
        def os(self) -> Optional[str]:
            return self.__os

        def compare_version(self, other: Union[None, 'SSH.Software', str]) -> int:
            # pylint: disable=too-many-branches
            if other is None:
                return 1
            if isinstance(other, SSH.Software):
                other = '{}{}'.format(other.version, other.patch or '')
            else:
                other = str(other)
            mx = re.match(r'^([\d\.]+\d+)(.*)$', other)
            if mx is not None:
                oversion, opatch = mx.group(1), mx.group(2).strip()
            else:
                oversion, opatch = other, ''
            if self.version < oversion:
                return -1
            elif self.version > oversion:
                return 1
            spatch = self.patch or ''
            if self.product == SSH.Product.DropbearSSH:
                if not re.match(r'^test\d.*$', opatch):
                    opatch = 'z{}'.format(opatch)
                if not re.match(r'^test\d.*$', spatch):
                    spatch = 'z{}'.format(spatch)
            elif self.product == SSH.Product.OpenSSH:
                mx1 = re.match(r'^p\d(.*)', opatch)
                mx2 = re.match(r'^p\d(.*)', spatch)
                if not (bool(mx1) and bool(mx2)):
                    if mx1 is not None:
                        opatch = mx1.group(1)
                    if mx2 is not None:
                        spatch = mx2.group(1)
            if spatch < opatch:
                return -1
            elif spatch > opatch:
                return 1
            return 0

        def between_versions(self, vfrom: str, vtill: str) -> bool:
            if bool(vfrom) and self.compare_version(vfrom) < 0:
                return False
            if bool(vtill) and self.compare_version(vtill) > 0:
                return False
            return True

        def display(self, full: bool = True) -> str:
            r = '{} '.format(self.vendor) if bool(self.vendor) else ''
            r += self.product
            if bool(self.version):
                r += ' {}'.format(self.version)
            if full:
                patch = self.patch or ''
                if self.product == SSH.Product.OpenSSH:
                    mx = re.match(r'^(p\d)(.*)$', patch)
                    if mx is not None:
                        r += mx.group(1)
                        patch = mx.group(2).strip()
                if bool(patch):
                    r += ' ({})'.format(patch)
                if bool(self.os):
                    r += ' running on {}'.format(self.os)
            return r

        def __str__(self) -> str:
            return self.display()

        def __repr__(self) -> str:
            r = 'vendor={}, '.format(self.vendor) if bool(self.vendor) else ''
            r += 'product={}'.format(self.product)
            if bool(self.version):
                r += ', version={}'.format(self.version)
            if bool(self.patch):
                r += ', patch={}'.format(self.patch)
            if bool(self.os):
                r += ', os={}'.format(self.os)
            return '<{}({})>'.format(self.__class__.__name__, r)

        @staticmethod
        def _fix_patch(patch: str) -> Optional[str]:
            return re.sub(r'^[-_\.]+', '', patch) or None

        @staticmethod
        def _fix_date(d: Optional[str]) -> Optional[str]:
            if d is not None and len(d) == 8:
                return '{}-{}-{}'.format(d[:4], d[4:6], d[6:8])
            else:
                return None

        @classmethod
        def _extract_os_version(cls, c: Optional[str]) -> Optional[str]:
            if c is None:
                return None
            mx = re.match(r'^NetBSD(?:_Secure_Shell)?(?:[\s-]+(\d{8})(.*))?$', c)
            if mx is not None:
                d = cls._fix_date(mx.group(1))
                return 'NetBSD' if d is None else 'NetBSD ({})'.format(d)
            mx = re.match(r'^FreeBSD(?:\slocalisations)?[\s-]+(\d{8})(.*)$', c)
            if not bool(mx):
                mx = re.match(r'^[^@]+@FreeBSD\.org[\s-]+(\d{8})(.*)$', c)
            if mx is not None:
                d = cls._fix_date(mx.group(1))
                return 'FreeBSD' if d is None else 'FreeBSD ({})'.format(d)
            w = ['RemotelyAnywhere', 'DesktopAuthority', 'RemoteSupportManager']
            for win_soft in w:
                mx = re.match(r'^in ' + win_soft + r' ([\d\.]+\d)$', c)
                if mx is not None:
                    ver = mx.group(1)
                    return 'Microsoft Windows ({} {})'.format(win_soft, ver)
            generic = ['NetBSD', 'FreeBSD']
            for g in generic:
                if c.startswith(g) or c.endswith(g):
                    return g
            return None

        @classmethod
        def parse(cls, banner: 'SSH.Banner') -> Optional['SSH.Software']:
            # pylint: disable=too-many-return-statements
            software = str(banner.software)
            mx = re.match(r'^dropbear_([\d\.]+\d+)(.*)', software)
            v = None  # type: Optional[str]
            if mx is not None:
                patch = cls._fix_patch(mx.group(2))
                v, p = 'Matt Johnston', SSH.Product.DropbearSSH
                v = None
                return cls(v, p, mx.group(1), patch, None)
            mx = re.match(r'^OpenSSH[_\.-]+([\d\.]+\d+)(.*)', software)
            if mx is not None:
                patch = cls._fix_patch(mx.group(2))
                v, p = 'OpenBSD', SSH.Product.OpenSSH
                v = None
                os_version = cls._extract_os_version(banner.comments)
                return cls(v, p, mx.group(1), patch, os_version)
            mx = re.match(r'^libssh-([\d\.]+\d+)(.*)', software)
            if mx is not None:
                patch = cls._fix_patch(mx.group(2))
                v, p = None, SSH.Product.LibSSH
                os_version = cls._extract_os_version(banner.comments)
                return cls(v, p, mx.group(1), patch, os_version)
            mx = re.match(r'^libssh_([\d\.]+\d+)(.*)', software)
            if mx is not None:
                patch = cls._fix_patch(mx.group(2))
                v, p = None, SSH.Product.LibSSH
                os_version = cls._extract_os_version(banner.comments)
                return cls(v, p, mx.group(1), patch, os_version)
            mx = re.match(r'^RomSShell_([\d\.]+\d+)(.*)', software)
            if mx is not None:
                patch = cls._fix_patch(mx.group(2))
                v, p = 'Allegro Software', 'RomSShell'
                return cls(v, p, mx.group(1), patch, None)
            mx = re.match(r'^mpSSH_([\d\.]+\d+)', software)
            if mx is not None:
                v, p = 'HP', 'iLO (Integrated Lights-Out) sshd'
                return cls(v, p, mx.group(1), None, None)
            mx = re.match(r'^Cisco-([\d\.]+\d+)', software)
            if mx is not None:
                v, p = 'Cisco', 'IOS/PIX sshd'
                return cls(v, p, mx.group(1), None, None)
            mx = re.match(r'^tinyssh_(.*)', software)
            if mx is not None:
                return cls(None, SSH.Product.TinySSH, mx.group(1), None, None)
            mx = re.match(r'^PuTTY_Release_(.*)', software)
            if mx:
                return cls(None, SSH.Product.PuTTY, mx.group(1), None, None)
            return None

    class Banner:
        _RXP, _RXR = r'SSH-\d\.\s*?\d+', r'(-\s*([^\s]*)(?:\s+(.*))?)?'
        RX_PROTOCOL = re.compile(re.sub(r'\\d(\+?)', r'(\\d\g<1>)', _RXP))
        RX_BANNER = re.compile(r'^({0}(?:(?:-{0})*)){1}$'.format(_RXP, _RXR))

        def __init__(self, protocol: Tuple[int, int], software: Optional[str], comments: Optional[str], valid_ascii: bool) -> None:
            self.__protocol = protocol
            self.__software = software
            self.__comments = comments
            self.__valid_ascii = valid_ascii

        @property
        def protocol(self) -> Tuple[int, int]:
            return self.__protocol

        @property
        def software(self) -> Optional[str]:
            return self.__software

        @property
        def comments(self) -> Optional[str]:
            return self.__comments

        @property
        def valid_ascii(self) -> bool:
            return self.__valid_ascii

        def __str__(self) -> str:
            r = 'SSH-{}.{}'.format(self.protocol[0], self.protocol[1])
            if self.software is not None:
                r += '-{}'.format(self.software)
            if bool(self.comments):
                r += ' {}'.format(self.comments)
            return r

        def __repr__(self) -> str:
            p = '{}.{}'.format(self.protocol[0], self.protocol[1])
            r = 'protocol={}'.format(p)
            if self.software is not None:
                r += ', software={}'.format(self.software)
            if bool(self.comments):
                r += ', comments={}'.format(self.comments)
            return '<{}({})>'.format(self.__class__.__name__, r)

        @classmethod
        def parse(cls, banner: str) -> Optional['SSH.Banner']:
            valid_ascii = Utils.is_print_ascii(banner)
            ascii_banner = Utils.to_print_ascii(banner)
            mx = cls.RX_BANNER.match(ascii_banner)
            if mx is None:
                return None
            protocol = min(re.findall(cls.RX_PROTOCOL, mx.group(1)))
            protocol = (int(protocol[0]), int(protocol[1]))
            software = (mx.group(3) or '').strip() or None
            if software is None and (mx.group(2) or '').startswith('-'):
                software = ''
            comments = (mx.group(4) or '').strip() or None
            if comments is not None:
                comments = re.sub(r'\s+', ' ', comments)
            return cls(protocol, software, comments, valid_ascii)

    class Fingerprint:
        def __init__(self, fpd: bytes) -> None:
            self.__fpd = fpd

        @property
        def md5(self) -> str:
            h = hashlib.md5(self.__fpd).hexdigest()
            r = u':'.join(h[i:i + 2] for i in range(0, len(h), 2))
            return u'MD5:{}'.format(r)

        @property
        def sha256(self) -> str:
            h = base64.b64encode(hashlib.sha256(self.__fpd).digest())
            r = h.decode('ascii').rstrip('=')
            return u'SHA256:{}'.format(r)

    class Algorithm:
        class Timeframe:
            def __init__(self) -> None:
                self.__storage = {}  # type: Dict[str, List[Optional[str]]]

            def __contains__(self, product: str) -> bool:
                return product in self.__storage

            def __getitem__(self, product):  # type: (str) -> Sequence[Optional[str]]
                return tuple(self.__storage.get(product, [None] * 4))

            def __str__(self) -> str:
                return self.__storage.__str__()

            def __repr__(self) -> str:
                return self.__str__()

            def get_from(self, product: str, for_server: bool = True) -> Optional[str]:
                return self[product][0 if bool(for_server) else 2]

            def get_till(self, product: str, for_server: bool = True) -> Optional[str]:
                return self[product][1 if bool(for_server) else 3]

            def _update(self, versions: Optional[str], pos: int) -> None:
                ssh_versions = {}  # type: Dict[str, str]
                for_srv, for_cli = pos < 2, pos > 1
                for v in (versions or '').split(','):
                    ssh_prod, ssh_ver, is_cli = SSH.Algorithm.get_ssh_version(v)
                    if not ssh_ver or (is_cli and for_srv) or (not is_cli and for_cli and ssh_prod in ssh_versions):
                        continue
                    ssh_versions[ssh_prod] = ssh_ver
                for ssh_product, ssh_version in ssh_versions.items():
                    if ssh_product not in self.__storage:
                        self.__storage[ssh_product] = [None] * 4
                    prev = self[ssh_product][pos]
                    if (prev is None or (prev < ssh_version and pos % 2 == 0) or (prev > ssh_version and pos % 2 == 1)):
                        self.__storage[ssh_product][pos] = ssh_version

            def update(self, versions: List[Optional[str]], for_server: Optional[bool] = None) -> 'SSH.Algorithm.Timeframe':
                for_cli = for_server is None or for_server is False
                for_srv = for_server is None or for_server is True
                vlen = len(versions)
                for i in range(min(3, vlen)):
                    if for_srv and i < 2:
                        self._update(versions[i], i)
                    if for_cli and (i % 2 == 0 or vlen == 2):
                        self._update(versions[i], 3 - 0**i)
                return self

        @staticmethod
        def get_ssh_version(version_desc: str) -> Tuple[str, str, bool]:
            is_client = version_desc.endswith('C')
            if is_client:
                version_desc = version_desc[:-1]
            if version_desc.startswith('d'):
                return SSH.Product.DropbearSSH, version_desc[1:], is_client
            elif version_desc.startswith('l1'):
                return SSH.Product.LibSSH, version_desc[2:], is_client
            else:
                return SSH.Product.OpenSSH, version_desc, is_client

        @classmethod
        def get_since_text(cls, versions: List[Optional[str]]) -> Optional[str]:
            tv = []
            if len(versions) == 0 or versions[0] is None:
                return None
            for v in versions[0].split(','):
                ssh_prod, ssh_ver, is_cli = cls.get_ssh_version(v)
                if not ssh_ver:
                    continue
                if ssh_prod in [SSH.Product.LibSSH]:
                    continue
                if is_cli:
                    ssh_ver = '{} (client only)'.format(ssh_ver)
                tv.append('{} {}'.format(ssh_prod, ssh_ver))
            if len(tv) == 0:
                return None
            return 'available since ' + ', '.join(tv).rstrip(', ')

    class Algorithms:
        def __init__(self, pkm: Optional[SSH1.PublicKeyMessage], kex: Optional[SSH2.Kex]) -> None:
            self.__ssh1kex = pkm
            self.__ssh2kex = kex

        @property
        def ssh1kex(self) -> Optional[SSH1.PublicKeyMessage]:
            return self.__ssh1kex

        @property
        def ssh2kex(self) -> Optional[SSH2.Kex]:
            return self.__ssh2kex

        @property
        def ssh1(self) -> Optional['SSH.Algorithms.Item']:
            if self.ssh1kex is None:
                return None
            item = SSH.Algorithms.Item(1, SSH1.KexDB.ALGORITHMS)
            item.add('key', [u'ssh-rsa1'])
            item.add('enc', self.ssh1kex.supported_ciphers)
            item.add('aut', self.ssh1kex.supported_authentications)
            return item

        @property
        def ssh2(self) -> Optional['SSH.Algorithms.Item']:
            if self.ssh2kex is None:
                return None
            item = SSH.Algorithms.Item(2, SSH2.KexDB.ALGORITHMS)
            item.add('kex', self.ssh2kex.kex_algorithms)
            item.add('key', self.ssh2kex.key_algorithms)
            item.add('enc', self.ssh2kex.server.encryption)
            item.add('mac', self.ssh2kex.server.mac)
            return item

        @property
        def values(self) -> Iterable['SSH.Algorithms.Item']:
            for item in [self.ssh1, self.ssh2]:
                if item is not None:
                    yield item

        @property
        def maxlen(self) -> int:
            def _ml(items: Sequence[str]) -> int:
                return max(len(i) for i in items)
            maxlen = 0
            if self.ssh1kex is not None:
                maxlen = max(_ml(self.ssh1kex.supported_ciphers),
                             _ml(self.ssh1kex.supported_authentications),
                             maxlen)
            if self.ssh2kex is not None:
                maxlen = max(_ml(self.ssh2kex.kex_algorithms),
                             _ml(self.ssh2kex.key_algorithms),
                             _ml(self.ssh2kex.server.encryption),
                             _ml(self.ssh2kex.server.mac),
                             maxlen)
            return maxlen

        def get_ssh_timeframe(self, for_server: Optional[bool] = None) -> 'SSH.Algorithm.Timeframe':
            timeframe = SSH.Algorithm.Timeframe()
            for alg_pair in self.values:
                alg_db = alg_pair.db
                for alg_type, alg_list in alg_pair.items():
                    for alg_name in alg_list:
                        alg_name_native = Utils.to_text(alg_name)
                        alg_desc = alg_db[alg_type].get(alg_name_native)
                        if alg_desc is None:
                            continue
                        versions = alg_desc[0]
                        timeframe.update(versions, for_server)
            return timeframe

        def get_recommendations(self, software: Optional['SSH.Software'], for_server: bool = True) -> Tuple[Optional['SSH.Software'], Dict[int, Dict[str, Dict[str, Dict[str, int]]]]]:
            # pylint: disable=too-many-locals,too-many-statements
            vproducts = [SSH.Product.OpenSSH,
                         SSH.Product.DropbearSSH,
                         SSH.Product.LibSSH,
                         SSH.Product.TinySSH]
            # Set to True if server is not one of vproducts, above.
            unknown_software = False
            if software is not None:
                if software.product not in vproducts:
                    unknown_software = True

            # The code below is commented out because it would try to guess what the server is,
            # usually resulting in wild & incorrect recommendations.
            # if software is None:
            #     ssh_timeframe = self.get_ssh_timeframe(for_server)
            #     for product in vproducts:
            #         if product not in ssh_timeframe:
            #             continue
            #         version = ssh_timeframe.get_from(product, for_server)
            #         if version is not None:
            #             software = SSH.Software(None, product, version, None, None)
            #             break
            rec = {}  # type: Dict[int, Dict[str, Dict[str, Dict[str, int]]]]
            if software is None:
                unknown_software = True
            for alg_pair in self.values:
                sshv, alg_db = alg_pair.sshv, alg_pair.db
                rec[sshv] = {}
                for alg_type, alg_list in alg_pair.items():
                    if alg_type == 'aut':
                        continue
                    rec[sshv][alg_type] = {'add': {}, 'del': {}, 'chg': {}}
                    for n, alg_desc in alg_db[alg_type].items():
                        versions = alg_desc[0]
                        empty_version = False
                        if len(versions) == 0 or versions[0] is None:
                            empty_version = True
                        else:
                            matches = False
                            if unknown_software:
                                matches = True
                            for v in versions[0].split(','):
                                ssh_prefix, ssh_version, is_cli = SSH.Algorithm.get_ssh_version(v)
                                if not ssh_version:
                                    continue
                                if (software is not None) and (ssh_prefix != software.product):
                                    continue
                                if is_cli and for_server:
                                    continue
                                if (software is not None) and (software.compare_version(ssh_version) < 0):
                                    continue
                                matches = True
                                break
                            if not matches:
                                continue
                        adl, faults = len(alg_desc), 0
                        for i in range(1, 3):
                            if not adl > i:
                                continue
                            fc = len(alg_desc[i])
                            if fc > 0:
                                faults += pow(10, 2 - i) * fc
                        if n not in alg_list:
                            # Don't recommend certificate or token types; these will only appear in the server's list if they are fully configured & functional on the server.
                            if faults > 0 or (alg_type == 'key' and (('-cert-' in n) or (n.startswith('sk-')))) or empty_version:
                                continue
                            rec[sshv][alg_type]['add'][n] = 0
                        else:
                            if faults == 0:
                                continue
                            if n in ['diffie-hellman-group-exchange-sha256', 'rsa-sha2-256', 'rsa-sha2-512', 'ssh-rsa-cert-v01@openssh.com']:
                                rec[sshv][alg_type]['chg'][n] = faults
                            else:
                                rec[sshv][alg_type]['del'][n] = faults
                    # If we are working with unknown software, drop all add recommendations, because we don't know if they're valid.
                    if unknown_software:
                        rec[sshv][alg_type]['add'] = {}
                    add_count = len(rec[sshv][alg_type]['add'])
                    del_count = len(rec[sshv][alg_type]['del'])
                    chg_count = len(rec[sshv][alg_type]['chg'])
                    new_alg_count = len(alg_list) + add_count - del_count
                    if new_alg_count < 1 and del_count > 0:
                        mf = min(rec[sshv][alg_type]['del'].values())
                        new_del = {}
                        for k, cf in rec[sshv][alg_type]['del'].items():
                            if cf != mf:
                                new_del[k] = cf
                        if del_count != len(new_del):
                            rec[sshv][alg_type]['del'] = new_del
                            new_alg_count += del_count - len(new_del)
                    if new_alg_count < 1:
                        del rec[sshv][alg_type]
                    else:
                        if add_count == 0:
                            del rec[sshv][alg_type]['add']
                        if del_count == 0:
                            del rec[sshv][alg_type]['del']
                        if chg_count == 0:
                            del rec[sshv][alg_type]['chg']
                        if len(rec[sshv][alg_type]) == 0:
                            del rec[sshv][alg_type]
                if len(rec[sshv]) == 0:
                    del rec[sshv]
            return software, rec

        class Item:
            def __init__(self, sshv: int, db: Dict[str, Dict[str, List[List[Optional[str]]]]]) -> None:
                self.__sshv = sshv
                self.__db = db
                self.__storage = {}  # type: Dict[str, List[str]]

            @property
            def sshv(self) -> int:
                return self.__sshv

            @property
            def db(self) -> Dict[str, Dict[str, List[List[Optional[str]]]]]:
                return self.__db

            def add(self, key: str, value: List[str]) -> None:
                self.__storage[key] = value

            def items(self) -> Iterable[Tuple[str, List[str]]]:
                return self.__storage.items()

    class Security:  # pylint: disable=too-few-public-methods
        # Format: [starting_vuln_version, last_vuln_version, affected, CVE_ID, CVSSv2, description]
        #   affected: 1 = server, 2 = client, 4 = local
        #   Example:  if it affects servers, both remote & local, then affected
        #             = 1.  If it affects servers, but is a local issue only,
        #             then affected = 1 + 4 = 5.
        CVE = {
            'Dropbear SSH': [
                ['0.0', '2018.76', 1, 'CVE-2018-15599', 5.0, 'remote users may enumerate users on the system'],
                ['0.0', '2017.74', 5, 'CVE-2017-9079', 4.7, 'local users can read certain files as root'],
                ['0.0', '2017.74', 5, 'CVE-2017-9078', 9.3, 'local users may elevate privileges to root under certain conditions'],
                ['0.0', '2016.73', 5, 'CVE-2016-7409', 2.1, 'local users can read process memory under limited conditions'],
                ['0.0', '2016.73', 1, 'CVE-2016-7408', 6.5, 'remote users can execute arbitrary code'],
                ['0.0', '2016.73', 5, 'CVE-2016-7407', 10.0, 'local users can execute arbitrary code'],
                ['0.0', '2016.73', 1, 'CVE-2016-7406', 10.0, 'remote users can execute arbitrary code'],
                ['0.44', '2015.71', 1, 'CVE-2016-3116', 5.5, 'bypass command restrictions via xauth command injection'],
                ['0.28', '2013.58', 1, 'CVE-2013-4434', 5.0, 'discover valid usernames through different time delays'],
                ['0.28', '2013.58', 1, 'CVE-2013-4421', 5.0, 'cause DoS via a compressed packet (memory consumption)'],
                ['0.52', '2011.54', 1, 'CVE-2012-0920', 7.1, 'execute arbitrary code or bypass command restrictions'],
                ['0.40', '0.48.1',  1, 'CVE-2007-1099', 7.5, 'conduct a MitM attack (no warning for hostkey mismatch)'],
                ['0.28', '0.47',    1, 'CVE-2006-1206', 7.5, 'cause DoS via large number of connections (slot exhaustion)'],
                ['0.39', '0.47',    1, 'CVE-2006-0225', 4.6, 'execute arbitrary commands via scp with crafted filenames'],
                ['0.28', '0.46',    1, 'CVE-2005-4178', 6.5, 'execute arbitrary code via buffer overflow vulnerability'],
                ['0.28', '0.42',    1, 'CVE-2004-2486', 7.5, 'execute arbitrary code via DSS verification code']],
            'libssh': [
                ['0.6.4',   '0.6.4',  1, 'CVE-2018-10933', 6.4, 'authentication bypass'],
                ['0.7.0',   '0.7.5',  1, 'CVE-2018-10933', 6.4, 'authentication bypass'],
                ['0.8.0',   '0.8.3',  1, 'CVE-2018-10933', 6.4, 'authentication bypass'],
                ['0.1',   '0.7.2',  1, 'CVE-2016-0739', 4.3, 'conduct a MitM attack (weakness in DH key generation)'],
                ['0.5.1', '0.6.4',  1, 'CVE-2015-3146', 5.0, 'cause DoS via kex packets (null pointer dereference)'],
                ['0.5.1', '0.6.3',  1, 'CVE-2014-8132', 5.0, 'cause DoS via kex init packet (dangling pointer)'],
                ['0.4.7', '0.6.2',  1, 'CVE-2014-0017', 1.9, 'leak data via PRNG state reuse on forking servers'],
                ['0.4.7', '0.5.3',  1, 'CVE-2013-0176', 4.3, 'cause DoS via kex packet (null pointer dereference)'],
                ['0.4.7', '0.5.2',  1, 'CVE-2012-6063', 7.5, 'cause DoS or execute arbitrary code via sftp (double free)'],
                ['0.4.7', '0.5.2',  1, 'CVE-2012-4562', 7.5, 'cause DoS or execute arbitrary code (overflow check)'],
                ['0.4.7', '0.5.2',  1, 'CVE-2012-4561', 5.0, 'cause DoS via unspecified vectors (invalid pointer)'],
                ['0.4.7', '0.5.2',  1, 'CVE-2012-4560', 7.5, 'cause DoS or execute arbitrary code (buffer overflow)'],
                ['0.4.7', '0.5.2',  1, 'CVE-2012-4559', 6.8, 'cause DoS or execute arbitrary code (double free)']],
            'OpenSSH': [
                ['7.2',     '7.2p2',   1, 'CVE-2016-6515',  7.8, 'cause DoS via long password string (crypt CPU consumption)'],
                ['1.2.2',   '7.2',     1, 'CVE-2016-3115',  5.5, 'bypass command restrictions via crafted X11 forwarding data'],
                ['5.4',     '7.1',     1, 'CVE-2016-1907',  5.0, 'cause DoS via crafted network traffic (out of bounds read)'],
                ['5.4',     '7.1p1',   2, 'CVE-2016-0778',  4.6, 'cause DoS via requesting many forwardings (heap based buffer overflow)'],
                ['5.0',     '7.1p1',   2, 'CVE-2016-0777',  4.0, 'leak data via allowing transfer of entire buffer'],
                ['6.0',     '7.2p2',   5, 'CVE-2015-8325',  7.2, 'privilege escalation via triggering crafted environment'],
                ['6.8',     '6.9',     5, 'CVE-2015-6565',  7.2, 'cause DoS via writing to a device (terminal disruption)'],
                ['5.0',     '6.9',     5, 'CVE-2015-6564',  6.9, 'privilege escalation via leveraging sshd uid'],
                ['5.0',     '6.9',     5, 'CVE-2015-6563',  1.9, 'conduct impersonation attack'],
                ['6.9p1',   '6.9p1',   1, 'CVE-2015-5600',  8.5, 'cause Dos or aid in conduct brute force attack (CPU consumption)'],
                ['6.0',     '6.6',     1, 'CVE-2015-5352',  4.3, 'bypass access restrictions via a specific connection'],
                ['6.0',     '6.6',     2, 'CVE-2014-2653',  5.8, 'bypass SSHFP DNS RR check via unacceptable host certificate'],
                ['5.0',     '6.5',     1, 'CVE-2014-2532',  5.8, 'bypass environment restrictions via specific string before wildcard'],
                ['1.2',     '6.4',     1, 'CVE-2014-1692',  7.5, 'cause DoS via triggering error condition (memory corruption)'],
                ['6.2',     '6.3',     1, 'CVE-2013-4548',  6.0, 'bypass command restrictions via crafted packet data'],
                ['1.2',     '5.6',     1, 'CVE-2012-0814',  3.5, 'leak data via debug messages'],
                ['1.2',     '5.8',     1, 'CVE-2011-5000',  3.5, 'cause DoS via large value in certain length field (memory consumption)'],
                ['5.6',     '5.7',     2, 'CVE-2011-0539',  5.0, 'leak data or conduct hash collision attack'],
                ['1.2',     '6.1',     1, 'CVE-2010-5107',  5.0, 'cause DoS via large number of connections (slot exhaustion)'],
                ['1.2',     '5.8',     1, 'CVE-2010-4755',  4.0, 'cause DoS via crafted glob expression (CPU and memory consumption)'],
                ['1.2',     '5.6',     1, 'CVE-2010-4478',  7.5, 'bypass authentication check via crafted values'],
                ['4.3',     '4.8',     1, 'CVE-2009-2904',  6.9, 'privilege escalation via hard links to setuid programs'],
                ['4.0',     '5.1',     1, 'CVE-2008-5161',  2.6, 'recover plaintext data from ciphertext'],
                ['1.2',     '4.6',     1, 'CVE-2008-4109',  5.0, 'cause DoS via multiple login attempts (slot exhaustion)'],
                ['1.2',     '4.8',     1, 'CVE-2008-1657',  6.5, 'bypass command restrictions via modifying session file'],
                ['1.2.2',   '4.9',     1, 'CVE-2008-1483',  6.9, 'hijack forwarded X11 connections'],
                ['4.0',     '4.6',     1, 'CVE-2007-4752',  7.5, 'privilege escalation via causing an X client to be trusted'],
                ['4.3p2',   '4.3p2',   1, 'CVE-2007-3102',  4.3, 'allow attacker to write random data to audit log'],
                ['1.2',     '4.6',     1, 'CVE-2007-2243',  5.0, 'discover valid usernames through different responses'],
                ['4.4',     '4.4',     1, 'CVE-2006-5794',  7.5, 'bypass authentication'],
                ['4.1',     '4.1p1',   1, 'CVE-2006-5229',  2.6, 'discover valid usernames through different time delays'],
                ['1.2',     '4.3p2',   1, 'CVE-2006-5052',  5.0, 'discover valid usernames through different responses'],
                ['1.2',     '4.3p2',   1, 'CVE-2006-5051',  9.3, 'cause DoS or execute arbitrary code (double free)'],
                ['4.5',     '4.5',     1, 'CVE-2006-4925',  5.0, 'cause DoS via invalid protocol sequence (crash)'],
                ['1.2',     '4.3p2',   1, 'CVE-2006-4924',  7.8, 'cause DoS via crafted packet (CPU consumption)'],
                ['3.8.1p1', '3.8.1p1', 1, 'CVE-2006-0883',  5.0, 'cause DoS via connecting multiple times (client connection refusal)'],
                ['3.0',     '4.2p1',   1, 'CVE-2006-0225',  4.6, 'execute arbitrary code'],
                ['2.1',     '4.1p1',   1, 'CVE-2005-2798',  5.0, 'leak data about authentication credentials'],
                ['3.5',     '3.5p1',   1, 'CVE-2004-2760',  6.8, 'leak data through different connection states'],
                ['2.3',     '3.7.1p2', 1, 'CVE-2004-2069',  5.0, 'cause DoS via large number of connections (slot exhaustion)'],
                ['3.0',     '3.4p1',   1, 'CVE-2004-0175',  4.3, 'leak data through directoy traversal'],
                ['1.2',     '3.9p1',   1, 'CVE-2003-1562',  7.6, 'leak data about authentication credentials'],
                ['3.1p1',   '3.7.1p1', 1, 'CVE-2003-0787',  7.5, 'privilege escalation via modifying stack'],
                ['3.1p1',   '3.7.1p1', 1, 'CVE-2003-0786', 10.0, 'privilege escalation via bypassing authentication'],
                ['1.0',     '3.7.1',   1, 'CVE-2003-0695',  7.5, 'cause DoS or execute arbitrary code'],
                ['1.0',     '3.7',     1, 'CVE-2003-0693', 10.0, 'execute arbitrary code'],
                ['3.0',     '3.6.1p2', 1, 'CVE-2003-0386',  7.5, 'bypass address restrictions for connection'],
                ['3.1p1',   '3.6.1p1', 1, 'CVE-2003-0190',  5.0, 'discover valid usernames through different time delays'],
                ['3.2.2',   '3.2.2',   1, 'CVE-2002-0765',  7.5, 'bypass authentication'],
                ['1.2.2',   '3.3p1',   1, 'CVE-2002-0640', 10.0, 'execute arbitrary code'],
                ['1.2.2',   '3.3p1',   1, 'CVE-2002-0639', 10.0, 'execute arbitrary code'],
                ['2.1',     '3.2',     1, 'CVE-2002-0575',  7.5, 'privilege escalation'],
                ['2.1',     '3.0.2p1', 2, 'CVE-2002-0083', 10.0, 'privilege escalation'],
                ['3.0',     '3.0p1',   1, 'CVE-2001-1507',  7.5, 'bypass authentication'],
                ['1.2.3',   '3.0.1p1', 5, 'CVE-2001-0872',  7.2, 'privilege escalation via crafted environment variables'],
                ['1.2.3',   '2.1.1',   1, 'CVE-2001-0361',  4.0, 'recover plaintext from ciphertext'],
                ['1.2',     '2.1',     1, 'CVE-2000-0525', 10.0, 'execute arbitrary code (improper privileges)']],
            'PuTTY': [
                ['0.54', '0.73', 2, 'CVE-2020-XXXX', 5.0, 'out of bounds memory read'],
                ['0.0', '0.72', 2, 'CVE-2019-17069', 5.0, 'potential DOS by remote SSHv1 server'],
                ['0.71', '0.72', 2, 'CVE-2019-17068', 5.0, 'xterm bracketed paste mode command injection'],
                ['0.52', '0.72', 2, 'CVE-2019-17067', 7.5, 'port rebinding weakness in port forward tunnel handling'],
                ['0.0', '0.71', 2, 'CVE-2019-XXXX', 5.0, 'undefined vulnerability in obsolete SSHv1 protocol handling'],
                ['0.0', '0.71', 6, 'CVE-2019-XXXX', 5.0, 'local privilege escalation in Pageant'],
                ['0.0', '0.70', 2, 'CVE-2019-9898', 7.5, 'potential recycling of random numbers'],
                ['0.0', '0.70', 2, 'CVE-2019-9897', 5.0, 'multiple denial-of-service issues from writing to the terminal'],
                ['0.0', '0.70', 6, 'CVE-2019-9896', 4.6, 'local application hijacking through malicious Windows help file'],
                ['0.0', '0.70', 2, 'CVE-2019-9894', 6.4, 'buffer overflow in RSA key exchange'],
                ['0.0', '0.69', 6, 'CVE-2016-6167', 4.4, 'local application hijacking through untrusted DLL loading'],
                ['0.0', '0.67', 2, 'CVE-2017-6542', 7.5, 'buffer overflow in UNIX client that can result in privilege escalation or denial-of-service'],
                ['0.0', '0.66', 2, 'CVE-2016-2563', 7.5, 'buffer overflow in SCP command-line utility'],
                ['0.0', '0.65', 2, 'CVE-2015-5309', 4.3, 'integer overflow in terminal-handling code'],
            ]
        }  # type: Dict[str, List[List[Any]]]
        TXT = {
            'Dropbear SSH': [
                ['0.28', '0.34', 1, 'remote root exploit', 'remote format string buffer overflow exploit (exploit-db#387)']],
            'libssh': [
                ['0.3.3', '0.3.3', 1, 'null pointer check', 'missing null pointer check in "crypt_set_algorithms_server"'],
                ['0.3.3', '0.3.3', 1, 'integer overflow',   'integer overflow in "buffer_get_data"'],
                ['0.3.3', '0.3.3', 3, 'heap overflow',      'heap overflow in "packet_decrypt"']]
        }  # type: Dict[str, List[List[Any]]]

    class Socket(ReadBuf, WriteBuf):
        class InsufficientReadException(Exception):
            pass

        SM_BANNER_SENT = 1

        def __init__(self, host: Optional[str], port: int, ipvo: Optional[Sequence[int]] = None, timeout: Union[int, float] = 5, timeout_set: bool = False) -> None:
            super(SSH.Socket, self).__init__()
            self.__sock = None  # type: Optional[socket.socket]
            self.__sock_map = {}  # type: Dict[int, socket.socket]
            self.__block_size = 8
            self.__state = 0
            self.__header = []  # type: List[str]
            self.__banner = None  # type: Optional[SSH.Banner]
            if host is None:
                raise ValueError('undefined host')
            nport = Utils.parse_int(port)
            if nport < 1 or nport > 65535:
                raise ValueError('invalid port: {}'.format(port))
            self.__host = host
            self.__port = nport
            if ipvo is not None:
                self.__ipvo = ipvo
            else:
                self.__ipvo = ()
            self.__timeout = timeout
            self.__timeout_set = timeout_set
            self.client_host = None  # type: Optional[str]
            self.client_port = None

        def _resolve(self, ipvo: Sequence[int]) -> Iterable[Tuple[int, Tuple[Any, ...]]]:
            ipvo = tuple([x for x in Utils.unique_seq(ipvo) if x in (4, 6)])
            ipvo_len = len(ipvo)
            prefer_ipvo = ipvo_len > 0
            prefer_ipv4 = prefer_ipvo and ipvo[0] == 4
            if ipvo_len == 1:
                family = socket.AF_INET if ipvo[0] == 4 else socket.AF_INET6
            else:
                family = socket.AF_UNSPEC
            try:
                stype = socket.SOCK_STREAM
                r = socket.getaddrinfo(self.__host, self.__port, family, stype)
                if prefer_ipvo:
                    r = sorted(r, key=lambda x: x[0], reverse=not prefer_ipv4)
                check = any(stype == rline[2] for rline in r)
                for af, socktype, _proto, _canonname, addr in r:
                    if not check or socktype == socket.SOCK_STREAM:
                        yield af, addr
            except socket.error as e:
                Output().fail('[exception] {}'.format(e))
                sys.exit(exitcodes.CONNECTION_ERROR)

        # Listens on a server socket and accepts one connection (used for
        # auditing client connections).
        def listen_and_accept(self) -> None:

            try:
                # Socket to listen on all IPv4 addresses.
                s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
                s.bind(('0.0.0.0', self.__port))
                s.listen()
                self.__sock_map[s.fileno()] = s
            except Exception:
                print("Warning: failed to listen on any IPv4 interfaces.")

            try:
                # Socket to listen on all IPv6 addresses.
                s = socket.socket(socket.AF_INET6, socket.SOCK_STREAM)
                s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
                s.setsockopt(socket.IPPROTO_IPV6, socket.IPV6_V6ONLY, 1)
                s.bind(('::', self.__port))
                s.listen()
                self.__sock_map[s.fileno()] = s
            except Exception:
                print("Warning: failed to listen on any IPv6 interfaces.")

            # If we failed to listen on any interfaces, terminate.
            if len(self.__sock_map.keys()) == 0:
                print("Error: failed to listen on any IPv4 and IPv6 interfaces!")
                sys.exit(exitcodes.CONNECTION_ERROR)

            # Wait for an incoming connection.  If a timeout was explicitly
            # set by the user, terminate when it elapses.
            fds = None
            time_elapsed = 0.0
            interval = 1.0
            while True:
                # Wait for a connection on either socket.
                fds = select.select(self.__sock_map.keys(), [], [], interval)
                time_elapsed += interval

                # We have incoming data on at least one of the sockets.
                if len(fds[0]) > 0:
                    break

                if self.__timeout_set and time_elapsed >= self.__timeout:
                    print("Timeout elapsed.  Terminating...")
                    sys.exit(exitcodes.CONNECTION_ERROR)

            # Accept the connection.
            c, addr = self.__sock_map[fds[0][0]].accept()
            self.client_host = addr[0]
            self.client_port = addr[1]
            c.settimeout(self.__timeout)
            self.__sock = c

        def connect(self) -> Optional[str]:
            '''Returns None on success, or an error string.'''
            err = None
            for af, addr in self._resolve(self.__ipvo):
                s = None
                try:
                    s = socket.socket(af, socket.SOCK_STREAM)
                    s.settimeout(self.__timeout)
                    s.connect(addr)
                    self.__sock = s
                    return None
                except socket.error as e:
                    err = e
                    self._close_socket(s)
            if err is None:
                errm = 'host {} has no DNS records'.format(self.__host)
            else:
                errt = (self.__host, self.__port, err)
                errm = 'cannot connect to {} port {}: {}'.format(*errt)
            return '[exception] {}'.format(errm)

        def get_banner(self, sshv: int = 2) -> Tuple[Optional['SSH.Banner'], List[str], Optional[str]]:
            if self.__sock is None:
                return self.__banner, self.__header, 'not connected'
            if self.__banner is not None:
                return self.__banner, self.__header, None

            banner = SSH_HEADER.format('1.5' if sshv == 1 else '2.0')
            if self.__state < self.SM_BANNER_SENT:
                self.send_banner(banner)

            s = 0
            e = None
            while s >= 0:
                s, e = self.recv()
                if s < 0:
                    continue
                while self.unread_len > 0:
                    line = self.read_line()
                    if len(line.strip()) == 0:
                        continue
                    self.__banner = SSH.Banner.parse(line)
                    if self.__banner is not None:
                        return self.__banner, self.__header, None
                    self.__header.append(line)

            return self.__banner, self.__header, e

        def recv(self, size: int = 2048) -> Tuple[int, Optional[str]]:
            if self.__sock is None:
                return -1, 'not connected'
            try:
                data = self.__sock.recv(size)
            except socket.timeout:
                return -1, 'timed out'
            except socket.error as e:
                if e.args[0] in (errno.EAGAIN, errno.EWOULDBLOCK):
                    return 0, 'retry'
                return -1, str(e.args[-1])
            if len(data) == 0:
                return -1, None
            pos = self._buf.tell()
            self._buf.seek(0, 2)
            self._buf.write(data)
            self._len += len(data)
            self._buf.seek(pos, 0)
            return len(data), None

        def send(self, data: bytes) -> Tuple[int, Optional[str]]:
            if self.__sock is None:
                return -1, 'not connected'
            try:
                self.__sock.send(data)
                return 0, None
            except socket.error as e:
                return -1, str(e.args[-1])

        def send_algorithms(self) -> None:
            '''Sends the list of supported host keys, key exchanges, ciphers, and MACs.  Emulates OpenSSH v8.2.'''

            key_exchanges = ['curve25519-sha256', 'curve25519-sha256@libssh.org', 'ecdh-sha2-nistp256', 'ecdh-sha2-nistp384', 'ecdh-sha2-nistp521', 'diffie-hellman-group-exchange-sha256', 'diffie-hellman-group16-sha512', 'diffie-hellman-group18-sha512', 'diffie-hellman-group14-sha256']
            hostkeys = ['rsa-sha2-512', 'rsa-sha2-256', 'ssh-rsa', 'ecdsa-sha2-nistp256', 'ssh-ed25519']
            ciphers = ['chacha20-poly1305@openssh.com', 'aes128-ctr', 'aes192-ctr', 'aes256-ctr', 'aes128-gcm@openssh.com', 'aes256-gcm@openssh.com']
            macs = ['umac-64-etm@openssh.com', 'umac-128-etm@openssh.com', 'hmac-sha2-256-etm@openssh.com', 'hmac-sha2-512-etm@openssh.com', 'hmac-sha1-etm@openssh.com', 'umac-64@openssh.com', 'umac-128@openssh.com', 'hmac-sha2-256', 'hmac-sha2-512', 'hmac-sha1']
            compressions = ['none', 'zlib@openssh.com']
            languages = ['']

            kexparty = SSH2.KexParty(ciphers, macs, compressions, languages)
            kex = SSH2.Kex(os.urandom(16), key_exchanges, hostkeys, kexparty, kexparty, False, 0)

            self.write_byte(SSH.Protocol.MSG_KEXINIT)
            kex.write(self)
            self.send_packet()

        def send_banner(self, banner: str) -> None:
            self.send(banner.encode() + b'\r\n')
            if self.__state < self.SM_BANNER_SENT:
                self.__state = self.SM_BANNER_SENT

        def ensure_read(self, size: int) -> None:
            while self.unread_len < size:
                s, e = self.recv()
                if s < 0:
                    raise SSH.Socket.InsufficientReadException(e)

        def read_packet(self, sshv: int = 2) -> Tuple[int, bytes]:
            try:
                header = WriteBuf()
                self.ensure_read(4)
                packet_length = self.read_int()
                header.write_int(packet_length)
                # XXX: validate length
                if sshv == 1:
                    padding_length = 8 - packet_length % 8
                    self.ensure_read(padding_length)
                    padding = self.read(padding_length)
                    header.write(padding)
                    payload_length = packet_length
                    check_size = padding_length + payload_length
                else:
                    self.ensure_read(1)
                    padding_length = self.read_byte()
                    header.write_byte(padding_length)
                    payload_length = packet_length - padding_length - 1
                    check_size = 4 + 1 + payload_length + padding_length
                if check_size % self.__block_size != 0:
                    Output().fail('[exception] invalid ssh packet (block size)')
                    sys.exit(exitcodes.CONNECTION_ERROR)
                self.ensure_read(payload_length)
                if sshv == 1:
                    payload = self.read(payload_length - 4)
                    header.write(payload)
                    crc = self.read_int()
                    header.write_int(crc)
                else:
                    payload = self.read(payload_length)
                    header.write(payload)
                packet_type = ord(payload[0:1])
                if sshv == 1:
                    rcrc = SSH1.crc32(padding + payload)
                    if crc != rcrc:
                        Output().fail('[exception] packet checksum CRC32 mismatch.')
                        sys.exit(exitcodes.CONNECTION_ERROR)
                else:
                    self.ensure_read(padding_length)
                    padding = self.read(padding_length)
                payload = payload[1:]
                return packet_type, payload
            except SSH.Socket.InsufficientReadException as ex:
                if ex.args[0] is None:
                    header.write(self.read(self.unread_len))
                    e = header.write_flush().strip()
                else:
                    e = ex.args[0].encode('utf-8')
                return -1, e

        def send_packet(self) -> Tuple[int, Optional[str]]:
            payload = self.write_flush()
            padding = -(len(payload) + 5) % 8
            if padding < 4:
                padding += 8
            plen = len(payload) + padding + 1
            pad_bytes = b'\x00' * padding
            data = struct.pack('>Ib', plen, padding) + payload + pad_bytes
            return self.send(data)

        def is_connected(self) -> bool:
            """Returns true if this Socket is connected, False otherwise."""
            return self.__sock is not None

        def close(self) -> None:
            self.__cleanup()
            self.reset()
            self.__state = 0
            self.__header = []
            self.__banner = None

        def _close_socket(self, s: Optional[socket.socket]) -> None:  # pylint: disable=no-self-use
            try:
                if s is not None:
                    s.shutdown(socket.SHUT_RDWR)
                    s.close()  # pragma: nocover
            except Exception:
                pass

        def __del__(self) -> None:
            self.__cleanup()

        def __cleanup(self) -> None:
            self._close_socket(self.__sock)
            for fd in self.__sock_map:
                self._close_socket(self.__sock_map[fd])
            self.__sock = None


class KexDH:  # pragma: nocover
    def __init__(self, kex_name: str, hash_alg: str, g: int, p: int) -> None:
        self.__kex_name = kex_name
        self.__hash_alg = hash_alg
        self.__g = 0
        self.__p = 0
        self.__q = 0
        self.__x = 0
        self.__e = 0
        self.set_params(g, p)

        self.__ed25519_pubkey = None  # type: Optional[bytes]
        self.__hostkey_type = None  # type: Optional[bytes]
        self.__hostkey_e = 0
        self.__hostkey_n = 0
        self.__hostkey_n_len = 0  # Length of the host key modulus.
        self.__ca_n_len = 0  # Length of the CA key modulus (if hostkey is a cert).

    def set_params(self, g: int, p: int) -> None:
        self.__g = g
        self.__p = p
        self.__q = (self.__p - 1) // 2
        self.__x = 0
        self.__e = 0

    def send_init(self, s: SSH.Socket, init_msg: int = SSH.Protocol.MSG_KEXDH_INIT) -> None:
        r = random.SystemRandom()
        self.__x = r.randrange(2, self.__q)
        self.__e = pow(self.__g, self.__x, self.__p)
        s.write_byte(init_msg)
        s.write_mpint2(self.__e)
        s.send_packet()

    # Parse a KEXDH_REPLY or KEXDH_GEX_REPLY message from the server.  This
    # contains the host key, among other things.  Function returns the host
    # key blob (from which the fingerprint can be calculated).
    def recv_reply(self, s: 'SSH.Socket', parse_host_key_size: bool = True) -> Optional[bytes]:
        packet_type, payload = s.read_packet(2)

        # Skip any & all MSG_DEBUG messages.
        while packet_type == SSH.Protocol.MSG_DEBUG:
            packet_type, payload = s.read_packet(2)

        if packet_type != -1 and packet_type not in [SSH.Protocol.MSG_KEXDH_REPLY, SSH.Protocol.MSG_KEXDH_GEX_REPLY]:  # pylint: disable=no-else-raise
            # TODO: change Exception to something more specific.
            raise Exception('Expected MSG_KEXDH_REPLY (%d) or MSG_KEXDH_GEX_REPLY (%d), but got %d instead.' % (SSH.Protocol.MSG_KEXDH_REPLY, SSH.Protocol.MSG_KEXDH_GEX_REPLY, packet_type))
        elif packet_type == -1:
            # A connection error occurred.  We can't parse anything, so just
            # return.  The host key modulus (and perhaps certificate modulus)
            # will remain at length 0.
            return None

        hostkey_len = 0  # pylint: disable=unused-variable
        hostkey_type_len = hostkey_e_len = 0  # pylint: disable=unused-variable
        key_id_len = principles_len = 0  # pylint: disable=unused-variable
        critical_options_len = extensions_len = 0  # pylint: disable=unused-variable
        nonce_len = ca_key_len = ca_key_type_len = 0  # pylint: disable=unused-variable
        ca_key_len = ca_key_type_len = ca_key_e_len = 0  # pylint: disable=unused-variable

        key_id = principles = None  # pylint: disable=unused-variable
        critical_options = extensions = None  # pylint: disable=unused-variable
        nonce = ca_key = ca_key_type = None  # pylint: disable=unused-variable
        ca_key_e = ca_key_n = None  # pylint: disable=unused-variable

        # Get the host key blob, F, and signature.
        ptr = 0
        hostkey, hostkey_len, ptr = KexDH.__get_bytes(payload, ptr)

        # If we are not supposed to parse the host key size (i.e.: it is a type that is of fixed size such as ed25519), then stop here.
        if not parse_host_key_size:
            return hostkey

        _, _, ptr = KexDH.__get_bytes(payload, ptr)
        _, _, ptr = KexDH.__get_bytes(payload, ptr)

        # Now pick apart the host key blob.
        # Get the host key type (i.e.: 'ssh-rsa', 'ssh-ed25519', etc).
        ptr = 0
        self.__hostkey_type, hostkey_type_len, ptr = KexDH.__get_bytes(hostkey, ptr)

        # If this is an RSA certificate, skip over the nonce.
        if self.__hostkey_type.startswith(b'ssh-rsa-cert-v0'):
            nonce, nonce_len, ptr = KexDH.__get_bytes(hostkey, ptr)

        # The public key exponent.
        hostkey_e, hostkey_e_len, ptr = KexDH.__get_bytes(hostkey, ptr)
        self.__hostkey_e = int(binascii.hexlify(hostkey_e), 16)

        # Here is the modulus size & actual modulus of the host key public key.
        hostkey_n, self.__hostkey_n_len, ptr = KexDH.__get_bytes(hostkey, ptr)
        self.__hostkey_n = int(binascii.hexlify(hostkey_n), 16)

        # If this is an RSA certificate, continue parsing to extract the CA
        # key.
        if self.__hostkey_type.startswith(b'ssh-rsa-cert-v0'):
            # Skip over the serial number.
            ptr += 8

            # Get the certificate type.
            cert_type = int(binascii.hexlify(hostkey[ptr:ptr + 4]), 16)
            ptr += 4

            # Only SSH2_CERT_TYPE_HOST (2) makes sense in this context.
            if cert_type == 2:

                # Skip the key ID (this is the serial number of the
                # certificate).
                key_id, key_id_len, ptr = KexDH.__get_bytes(hostkey, ptr)

                # The principles, which are... I don't know what.
                principles, principles_len, ptr = KexDH.__get_bytes(hostkey, ptr)

                # Skip over the timestamp that this certificate is valid after.
                ptr += 8

                # Skip over the timestamp that this certificate is valid before.
                ptr += 8

                # TODO: validate the principles, and time range.

                # The critical options.
                critical_options, critical_options_len, ptr = KexDH.__get_bytes(hostkey, ptr)

                # Certificate extensions.
                extensions, extensions_len, ptr = KexDH.__get_bytes(hostkey, ptr)

                # Another nonce.
                nonce, nonce_len, ptr = KexDH.__get_bytes(hostkey, ptr)

                # Finally, we get to the CA key.
                ca_key, ca_key_len, ptr = KexDH.__get_bytes(hostkey, ptr)

                # Last in the host key blob is the CA signature.  It isn't
                # interesting to us, so we won't bother parsing any further.
                # The CA key has the modulus, however...
                ptr = 0

                # 'ssh-rsa', 'rsa-sha2-256', etc.
                ca_key_type, ca_key_type_len, ptr = KexDH.__get_bytes(ca_key, ptr)

                # CA's public key exponent.
                ca_key_e, ca_key_e_len, ptr = KexDH.__get_bytes(ca_key, ptr)

                # CA's modulus.  Bingo.
                ca_key_n, self.__ca_n_len, ptr = KexDH.__get_bytes(ca_key, ptr)

        return hostkey

    @staticmethod
    def __get_bytes(buf: bytes, ptr: int) -> Tuple[bytes, int, int]:
        num_bytes = struct.unpack('>I', buf[ptr:ptr + 4])[0]
        ptr += 4
        return buf[ptr:ptr + num_bytes], num_bytes, ptr + num_bytes

    # Converts a modulus length in bytes to its size in bits, after some
    # possible adjustments.
    @staticmethod
    def __adjust_key_size(size: int) -> int:
        size = size * 8
        # Actual keys are observed to be about 8 bits bigger than expected
        # (i.e.: 1024-bit keys have a 1032-bit modulus).  Check if this is
        # the case, and subtract 8 if so.  This simply improves readability
        # in the UI.
        if (size >> 3) % 2 != 0:
            size = size - 8
        return size

    # Returns the size of the hostkey, in bits.
    def get_hostkey_size(self) -> int:
        return KexDH.__adjust_key_size(self.__hostkey_n_len)

    # Returns the size of the CA key, in bits.
    def get_ca_size(self) -> int:
        return KexDH.__adjust_key_size(self.__ca_n_len)

    # Returns the size of the DH modulus, in bits.
    def get_dh_modulus_size(self) -> int:
        # -2 to account for the '0b' prefix in the string.
        return len(bin(self.__p)) - 2


class KexGroup1(KexDH):  # pragma: nocover
    def __init__(self) -> None:
        # rfc2409: second oakley group
        p = int('ffffffffffffffffc90fdaa22168c234c4c6628b80dc1cd129024e088a67cc74020bbea63b139b22514a08798e3404ddef9519b3cd3a431b302b0a6df25f14374fe1356d6d51c245e485b576625e7ec6f44c42e9a637ed6b0bff5cb6f406b7edee386bfb5a899fa5ae9f24117c4b1fe649286651ece65381ffffffffffffffff', 16)
        super(KexGroup1, self).__init__('KexGroup1', 'sha1', 2, p)


class KexGroup14(KexDH):  # pragma: nocover
    def __init__(self, hash_alg: str) -> None:
        # rfc3526: 2048-bit modp group
        p = int('ffffffffffffffffc90fdaa22168c234c4c6628b80dc1cd129024e088a67cc74020bbea63b139b22514a08798e3404ddef9519b3cd3a431b302b0a6df25f14374fe1356d6d51c245e485b576625e7ec6f44c42e9a637ed6b0bff5cb6f406b7edee386bfb5a899fa5ae9f24117c4b1fe649286651ece45b3dc2007cb8a163bf0598da48361c55d39a69163fa8fd24cf5f83655d23dca3ad961c62f356208552bb9ed529077096966d670c354e4abc9804f1746c08ca18217c32905e462e36ce3be39e772c180e86039b2783a2ec07a28fb5c55df06f4c52c9de2bcbf6955817183995497cea956ae515d2261898fa051015728e5a8aacaa68ffffffffffffffff', 16)
        super(KexGroup14, self).__init__('KexGroup14', hash_alg, 2, p)


class KexGroup14_SHA1(KexGroup14):
    def __init__(self) -> None:
        super(KexGroup14_SHA1, self).__init__('sha1')


class KexGroup14_SHA256(KexGroup14):
    def __init__(self) -> None:
        super(KexGroup14_SHA256, self).__init__('sha256')


class KexGroup16_SHA512(KexDH):
    def __init__(self) -> None:
        # rfc3526: 4096-bit modp group
        p = int('ffffffffffffffffc90fdaa22168c234c4c6628b80dc1cd129024e088a67cc74020bbea63b139b22514a08798e3404ddef9519b3cd3a431b302b0a6df25f14374fe1356d6d51c245e485b576625e7ec6f44c42e9a637ed6b0bff5cb6f406b7edee386bfb5a899fa5ae9f24117c4b1fe649286651ece45b3dc2007cb8a163bf0598da48361c55d39a69163fa8fd24cf5f83655d23dca3ad961c62f356208552bb9ed529077096966d670c354e4abc9804f1746c08ca18217c32905e462e36ce3be39e772c180e86039b2783a2ec07a28fb5c55df06f4c52c9de2bcbf6955817183995497cea956ae515d2261898fa051015728e5a8aaac42dad33170d04507a33a85521abdf1cba64ecfb850458dbef0a8aea71575d060c7db3970f85a6e1e4c7abf5ae8cdb0933d71e8c94e04a25619dcee3d2261ad2ee6bf12ffa06d98a0864d87602733ec86a64521f2b18177b200cbbe117577a615d6c770988c0bad946e208e24fa074e5ab3143db5bfce0fd108e4b82d120a92108011a723c12a787e6d788719a10bdba5b2699c327186af4e23c1a946834b6150bda2583e9ca2ad44ce8dbbbc2db04de8ef92e8efc141fbecaa6287c59474e6bc05d99b2964fa090c3a2233ba186515be7ed1f612970cee2d7afb81bdd762170481cd0069127d5b05aa993b4ea988d8fddc186ffb7dc90a6c08f4df435c934063199ffffffffffffffff', 16)
        super(KexGroup16_SHA512, self).__init__('KexGroup16_SHA512', 'sha512', 2, p)


class KexGroup18_SHA512(KexDH):
    def __init__(self) -> None:
        # rfc3526: 8192-bit modp group
        p = int('ffffffffffffffffc90fdaa22168c234c4c6628b80dc1cd129024e088a67cc74020bbea63b139b22514a08798e3404ddef9519b3cd3a431b302b0a6df25f14374fe1356d6d51c245e485b576625e7ec6f44c42e9a637ed6b0bff5cb6f406b7edee386bfb5a899fa5ae9f24117c4b1fe649286651ece45b3dc2007cb8a163bf0598da48361c55d39a69163fa8fd24cf5f83655d23dca3ad961c62f356208552bb9ed529077096966d670c354e4abc9804f1746c08ca18217c32905e462e36ce3be39e772c180e86039b2783a2ec07a28fb5c55df06f4c52c9de2bcbf6955817183995497cea956ae515d2261898fa051015728e5a8aaac42dad33170d04507a33a85521abdf1cba64ecfb850458dbef0a8aea71575d060c7db3970f85a6e1e4c7abf5ae8cdb0933d71e8c94e04a25619dcee3d2261ad2ee6bf12ffa06d98a0864d87602733ec86a64521f2b18177b200cbbe117577a615d6c770988c0bad946e208e24fa074e5ab3143db5bfce0fd108e4b82d120a92108011a723c12a787e6d788719a10bdba5b2699c327186af4e23c1a946834b6150bda2583e9ca2ad44ce8dbbbc2db04de8ef92e8efc141fbecaa6287c59474e6bc05d99b2964fa090c3a2233ba186515be7ed1f612970cee2d7afb81bdd762170481cd0069127d5b05aa993b4ea988d8fddc186ffb7dc90a6c08f4df435c93402849236c3fab4d27c7026c1d4dcb2602646dec9751e763dba37bdf8ff9406ad9e530ee5db382f413001aeb06a53ed9027d831179727b0865a8918da3edbebcf9b14ed44ce6cbaced4bb1bdb7f1447e6cc254b332051512bd7af426fb8f401378cd2bf5983ca01c64b92ecf032ea15d1721d03f482d7ce6e74fef6d55e702f46980c82b5a84031900b1c9e59e7c97fbec7e8f323a97a7e36cc88be0f1d45b7ff585ac54bd407b22b4154aacc8f6d7ebf48e1d814cc5ed20f8037e0a79715eef29be32806a1d58bb7c5da76f550aa3d8a1fbff0eb19ccb1a313d55cda56c9ec2ef29632387fe8d76e3c0468043e8f663f4860ee12bf2d5b0b7474d6e694f91e6dbe115974a3926f12fee5e438777cb6a932df8cd8bec4d073b931ba3bc832b68d9dd300741fa7bf8afc47ed2576f6936ba424663aab639c5ae4f5683423b4742bf1c978238f16cbe39d652de3fdb8befc848ad922222e04a4037c0713eb57a81a23f0c73473fc646cea306b4bcbc8862f8385ddfa9d4b7fa2c087e879683303ed5bdd3a062b3cf5b3a278a66d2a13f83f44f82ddf310ee074ab6a364597e899a0255dc164f31cc50846851df9ab48195ded7ea1b1d510bd7ee74d73faf36bc31ecfa268359046f4eb879f924009438b481c6cd7889a002ed5ee382bc9190da6fc026e479558e4475677e9aa9e3050e2765694dfc81f56e880b96e7160c980dd98edd3dfffffffffffffffff', 16)
        super(KexGroup18_SHA512, self).__init__('KexGroup18_SHA512', 'sha512', 2, p)


class KexCurve25519_SHA256(KexDH):
    def __init__(self) -> None:
        super(KexCurve25519_SHA256, self).__init__('KexCurve25519_SHA256', 'sha256', 0, 0)

    # To start an ED25519 kex, we simply send a random 256-bit number as the
    # public key.
    def send_init(self, s: 'SSH.Socket', init_msg: int = SSH.Protocol.MSG_KEXDH_INIT) -> None:
        self.__ed25519_pubkey = os.urandom(32)
        s.write_byte(init_msg)
        s.write_string(self.__ed25519_pubkey)
        s.send_packet()


class KexNISTP256(KexDH):
    def __init__(self) -> None:
        super(KexNISTP256, self).__init__('KexNISTP256', 'sha256', 0, 0)

    # Because the server checks that the value sent here is valid (i.e.: it lies
    # on the curve, among other things), we would have to write a lot of code
    # or import an elliptic curve library in order to randomly generate a
    # valid elliptic point each time.  Hence, we will simply send a static
    # value, which is enough for us to extract the server's host key.
    def send_init(self, s: 'SSH.Socket', init_msg: int = SSH.Protocol.MSG_KEXDH_INIT) -> None:
        s.write_byte(init_msg)
        s.write_string(b'\x04\x0b\x60\x44\x9f\x8a\x11\x9e\xc7\x81\x0c\xa9\x98\xfc\xb7\x90\xaa\x6b\x26\x8c\x12\x4a\xc0\x09\xbb\xdf\xc4\x2c\x4c\x2c\x99\xb6\xe1\x71\xa0\xd4\xb3\x62\x47\x74\xb3\x39\x0c\xf2\x88\x4a\x84\x6b\x3b\x15\x77\xa5\x77\xd2\xa9\xc9\x94\xf9\xd5\x66\x19\xcd\x02\x34\xd1')
        s.send_packet()


class KexNISTP384(KexDH):
    def __init__(self) -> None:
        super(KexNISTP384, self).__init__('KexNISTP384', 'sha256', 0, 0)

    # See comment for KexNISTP256.send_init().
    def send_init(self, s: 'SSH.Socket', init_msg: int = SSH.Protocol.MSG_KEXDH_INIT) -> None:
        s.write_byte(init_msg)
        s.write_string(b'\x04\xe2\x9b\x84\xce\xa1\x39\x50\xfe\x1e\xa3\x18\x70\x1c\xe2\x7a\xe4\xb5\x6f\xdf\x93\x9f\xd4\xf4\x08\xcc\x9b\x02\x10\xa4\xca\x77\x9c\x2e\x51\x44\x1d\x50\x7a\x65\x4e\x7e\x2f\x10\x2d\x2d\x4a\x32\xc9\x8e\x18\x75\x90\x6c\x19\x10\xda\xcc\xa8\xe9\xf4\xc4\x3a\x53\x80\x35\xf4\x97\x9c\x04\x16\xf9\x5a\xdc\xcc\x05\x94\x29\xfa\xc4\xd6\x87\x4e\x13\x21\xdb\x3d\x12\xac\xbd\x20\x3b\x60\xff\xe6\x58\x42')
        s.send_packet()


class KexNISTP521(KexDH):
    def __init__(self) -> None:
        super(KexNISTP521, self).__init__('KexNISTP521', 'sha256', 0, 0)

    # See comment for KexNISTP256.send_init().
    def send_init(self, s: 'SSH.Socket', init_msg: int = SSH.Protocol.MSG_KEXDH_INIT) -> None:
        s.write_byte(init_msg)
        s.write_string(b'\x04\x01\x02\x90\x29\xe9\x8f\xa8\x04\xaf\x1c\x00\xf9\xc6\x29\xc0\x39\x74\x8e\xea\x47\x7e\x7c\xf7\x15\x6e\x43\x3b\x59\x13\x53\x43\xb0\xae\x0b\xe7\xe6\x7c\x55\x73\x52\xa5\x2a\xc1\x42\xde\xfc\xf4\x1f\x8b\x5a\x8d\xfa\xcd\x0a\x65\x77\xa8\xce\x68\xd2\xc6\x26\xb5\x3f\xee\x4b\x01\x7b\xd2\x96\x23\x69\x53\xc7\x01\xe1\x0d\x39\xe9\x87\x49\x3b\xc8\xec\xda\x0c\xf9\xca\xad\x89\x42\x36\x6f\x93\x78\x78\x31\x55\x51\x09\x51\xc0\x96\xd7\xea\x61\xbf\xc2\x44\x08\x80\x43\xed\xc6\xbb\xfb\x94\xbd\xf8\xdf\x2b\xd8\x0b\x2e\x29\x1b\x8c\xc4\x8a\x04\x2d\x3a')
        s.send_packet()


class KexGroupExchange(KexDH):
    def __init__(self, classname: str, hash_alg: str) -> None:
        super(KexGroupExchange, self).__init__(classname, hash_alg, 0, 0)

    def send_init(self, s: 'SSH.Socket', init_msg: int = SSH.Protocol.MSG_KEXDH_GEX_REQUEST) -> None:
        self.send_init_gex(s)

    # The group exchange starts with sending a message to the server with
    # the minimum, maximum, and preferred number of bits are for the DH group.
    # The server responds with a generator and prime modulus that matches that,
    # then the handshake continues on like a normal DH handshake (except the
    # SSH message types differ).
    def send_init_gex(self, s: 'SSH.Socket', minbits: int = 1024, prefbits: int = 2048, maxbits: int = 8192) -> None:

        # Send the initial group exchange request.  Tell the server what range
        # of modulus sizes we will accept, along with our preference.
        s.write_byte(SSH.Protocol.MSG_KEXDH_GEX_REQUEST)
        s.write_int(minbits)
        s.write_int(prefbits)
        s.write_int(maxbits)
        s.send_packet()

        packet_type, payload = s.read_packet(2)
        if (packet_type != SSH.Protocol.MSG_KEXDH_GEX_GROUP) and (packet_type != SSH.Protocol.MSG_DEBUG):  # pylint: disable=consider-using-in
            # TODO: replace with a better exception type.
            raise Exception('Expected MSG_KEXDH_GEX_REPLY (%d), but got %d instead.' % (SSH.Protocol.MSG_KEXDH_GEX_REPLY, packet_type))

        # Skip any & all MSG_DEBUG messages.
        while packet_type == SSH.Protocol.MSG_DEBUG:
            packet_type, payload = s.read_packet(2)

        # Parse the modulus (p) and generator (g) values from the server.
        ptr = 0
        p_len = struct.unpack('>I', payload[ptr:ptr + 4])[0]
        ptr += 4

        p = int(binascii.hexlify(payload[ptr:ptr + p_len]), 16)
        ptr += p_len

        g_len = struct.unpack('>I', payload[ptr:ptr + 4])[0]
        ptr += 4

        g = int(binascii.hexlify(payload[ptr:ptr + g_len]), 16)
        ptr += g_len

        # Now that we got the generator and modulus, perform the DH exchange
        # like usual.
        super(KexGroupExchange, self).set_params(g, p)
        super(KexGroupExchange, self).send_init(s, SSH.Protocol.MSG_KEXDH_GEX_INIT)


class KexGroupExchange_SHA1(KexGroupExchange):
    def __init__(self) -> None:
        super(KexGroupExchange_SHA1, self).__init__('KexGroupExchange_SHA1', 'sha1')


class KexGroupExchange_SHA256(KexGroupExchange):
    def __init__(self) -> None:
        super(KexGroupExchange_SHA256, self).__init__('KexGroupExchange_SHA256', 'sha256')
