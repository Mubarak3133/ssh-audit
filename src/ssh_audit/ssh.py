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
import hashlib
import re

# pylint: disable=unused-import
from typing import Dict, List, Set, Sequence, Tuple, Iterable  # noqa: F401
from typing import Callable, Optional, Union, Any  # noqa: F401

from ssh_audit.ssh1_kexdb import SSH1_KexDB
from ssh_audit.ssh1_publickeymessage import SSH1_PublicKeyMessage
from ssh_audit.ssh2_kex import SSH2_Kex
from ssh_audit.ssh2_kexdb import SSH2_KexDB
from ssh_audit.ssh_banner import SSH_Banner
from ssh_audit.utils import Utils


class SSH:  # pylint: disable=too-few-public-methods
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
        def parse(cls, banner: 'SSH_Banner') -> Optional['SSH.Software']:
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
        def __init__(self, pkm: Optional[SSH1_PublicKeyMessage], kex: Optional[SSH2_Kex]) -> None:
            self.__ssh1kex = pkm
            self.__ssh2kex = kex

        @property
        def ssh1kex(self) -> Optional[SSH1_PublicKeyMessage]:
            return self.__ssh1kex

        @property
        def ssh2kex(self) -> Optional[SSH2_Kex]:
            return self.__ssh2kex

        @property
        def ssh1(self) -> Optional['SSH.Algorithms.Item']:
            if self.ssh1kex is None:
                return None
            item = SSH.Algorithms.Item(1, SSH1_KexDB.ALGORITHMS)
            item.add('key', [u'ssh-rsa1'])
            item.add('enc', self.ssh1kex.supported_ciphers)
            item.add('aut', self.ssh1kex.supported_authentications)
            return item

        @property
        def ssh2(self) -> Optional['SSH.Algorithms.Item']:
            if self.ssh2kex is None:
                return None
            item = SSH.Algorithms.Item(2, SSH2_KexDB.ALGORITHMS)
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
