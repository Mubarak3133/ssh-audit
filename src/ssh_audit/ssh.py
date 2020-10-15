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
import re

# pylint: disable=unused-import
from typing import Dict, List, Set, Sequence, Tuple, Iterable  # noqa: F401
from typing import Callable, Optional, Union, Any  # noqa: F401

from ssh_audit.banner import Banner
from ssh_audit.product import Product
from ssh_audit.ssh1_kexdb import SSH1_KexDB
from ssh_audit.ssh1_publickeymessage import SSH1_PublicKeyMessage
from ssh_audit.ssh2_kex import SSH2_Kex
from ssh_audit.ssh2_kexdb import SSH2_KexDB
from ssh_audit.utils import Utils


class SSH:  # pylint: disable=too-few-public-methods
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
            if self.product == Product.DropbearSSH:
                if not re.match(r'^test\d.*$', opatch):
                    opatch = 'z{}'.format(opatch)
                if not re.match(r'^test\d.*$', spatch):
                    spatch = 'z{}'.format(spatch)
            elif self.product == Product.OpenSSH:
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
                if self.product == Product.OpenSSH:
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
        def parse(cls, banner: 'Banner') -> Optional['SSH.Software']:
            # pylint: disable=too-many-return-statements
            software = str(banner.software)
            mx = re.match(r'^dropbear_([\d\.]+\d+)(.*)', software)
            v = None  # type: Optional[str]
            if mx is not None:
                patch = cls._fix_patch(mx.group(2))
                v, p = 'Matt Johnston', Product.DropbearSSH
                v = None
                return cls(v, p, mx.group(1), patch, None)
            mx = re.match(r'^OpenSSH[_\.-]+([\d\.]+\d+)(.*)', software)
            if mx is not None:
                patch = cls._fix_patch(mx.group(2))
                v, p = 'OpenBSD', Product.OpenSSH
                v = None
                os_version = cls._extract_os_version(banner.comments)
                return cls(v, p, mx.group(1), patch, os_version)
            mx = re.match(r'^libssh-([\d\.]+\d+)(.*)', software)
            if mx is not None:
                patch = cls._fix_patch(mx.group(2))
                v, p = None, Product.LibSSH
                os_version = cls._extract_os_version(banner.comments)
                return cls(v, p, mx.group(1), patch, os_version)
            mx = re.match(r'^libssh_([\d\.]+\d+)(.*)', software)
            if mx is not None:
                patch = cls._fix_patch(mx.group(2))
                v, p = None, Product.LibSSH
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
                return cls(None, Product.TinySSH, mx.group(1), None, None)
            mx = re.match(r'^PuTTY_Release_(.*)', software)
            if mx:
                return cls(None, Product.PuTTY, mx.group(1), None, None)
            return None


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
                return Product.DropbearSSH, version_desc[1:], is_client
            elif version_desc.startswith('l1'):
                return Product.LibSSH, version_desc[2:], is_client
            else:
                return Product.OpenSSH, version_desc, is_client

        @classmethod
        def get_since_text(cls, versions: List[Optional[str]]) -> Optional[str]:
            tv = []
            if len(versions) == 0 or versions[0] is None:
                return None
            for v in versions[0].split(','):
                ssh_prod, ssh_ver, is_cli = cls.get_ssh_version(v)
                if not ssh_ver:
                    continue
                if ssh_prod in [Product.LibSSH]:
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
            vproducts = [Product.OpenSSH,
                         Product.DropbearSSH,
                         Product.LibSSH,
                         Product.TinySSH]
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
