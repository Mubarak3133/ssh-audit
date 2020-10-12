"""
   The MIT License (MIT)

   Copyright (C) 2020 Joe Testa (jtesta@positronsecurity.com)

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
from typing import Dict, List, Tuple
from typing import Optional, Any


# Validates policy files and performs policy testing
class Policy:

    def __init__(self, policy_file: Optional[str] = None, policy_data: Optional[str] = None) -> None:
        self._name = None  # type: Optional[str]
        self._version = None  # type: Optional[str]
        self._banner = None  # type: Optional[str]
        self._compressions = None  # type: Optional[List[str]]
        self._host_keys = None  # type: Optional[List[str]]
        self._optional_host_keys = None  # type: Optional[List[str]]
        self._kex = None  # type: Optional[List[str]]
        self._ciphers = None  # type: Optional[List[str]]
        self._macs = None  # type: Optional[List[str]]
        self._hostkey_sizes = None  # type: Optional[Dict[str, int]]
        self._cakey_sizes = None  # type: Optional[Dict[str, int]]
        self._dh_modulus_sizes = None  # type: Optional[Dict[str, int]]
        self._server_policy = True

        if (policy_file is None) and (policy_data is None):
            raise RuntimeError('policy_file and policy_data must not both be None.')
        elif (policy_file is not None) and (policy_data is not None):
            raise RuntimeError('policy_file and policy_data must not both be specified.')

        if policy_file is not None:
            with open(policy_file, "r") as f:
                policy_data = f.read()

        lines = []
        if policy_data is not None:
            lines = policy_data.split("\n")

        for line in lines:
            line = line.strip()
            if (len(line) == 0) or line.startswith('#'):
                continue

            key = None
            val = None
            try:
                key, val = line.split('=')
            except ValueError:
                raise ValueError("could not parse line: %s" % line)

            key = key.strip()
            val = val.strip()

            if key not in ['name', 'version', 'banner', 'compressions', 'host keys', 'optional host keys', 'key exchanges', 'ciphers', 'macs', 'client policy'] and not key.startswith('hostkey_size_') and not key.startswith('cakey_size_') and not key.startswith('dh_modulus_size_'):
                raise ValueError("invalid field found in policy: %s" % line)

            if key in ['name', 'banner']:

                # If the banner value is blank, set it to "" so that the code below handles it.
                if len(val) < 2:
                    val = "\"\""

                if (val[0] != '"') or (val[-1] != '"'):
                    raise ValueError('the value for the %s field must be enclosed in quotes: %s' % (key, val))

                # Remove the surrounding quotes, and unescape quotes & newlines.
                val = val[1:-1]. replace("\\\"", "\"").replace("\\n", "\n")

                if key == 'name':
                    self._name = val
                elif key == 'banner':
                    self._banner = val
            elif key == 'version':
                self._version = val
            elif key in ['compressions', 'host keys', 'optional host keys', 'key exchanges', 'ciphers', 'macs']:
                try:
                    algs = val.split(',')
                except ValueError:
                    # If the value has no commas, then set the algorithm list to just the value.
                    algs = [val]

                # Strip whitespace in each algorithm name.
                algs = [alg.strip() for alg in algs]

                if key == 'compressions':
                    self._compressions = algs
                elif key == 'host keys':
                    self._host_keys = algs
                elif key == 'optional host keys':
                    self._optional_host_keys = algs
                elif key == 'key exchanges':
                    self._kex = algs
                elif key == 'ciphers':
                    self._ciphers = algs
                elif key == 'macs':
                    self._macs = algs
            elif key.startswith('hostkey_size_'):
                hostkey_type = key[13:]
                if self._hostkey_sizes is None:
                    self._hostkey_sizes = {}
                self._hostkey_sizes[hostkey_type] = int(val)
            elif key.startswith('cakey_size_'):
                cakey_type = key[11:]
                if self._cakey_sizes is None:
                    self._cakey_sizes = {}
                self._cakey_sizes[cakey_type] = int(val)
            elif key.startswith('dh_modulus_size_'):
                dh_modulus_type = key[16:]
                if self._dh_modulus_sizes is None:
                    self._dh_modulus_sizes = {}
                self._dh_modulus_sizes[dh_modulus_type] = int(val)
            elif key.startswith('client policy') and val.lower() == 'true':
                self._server_policy = False


        if self._name is None:
            raise ValueError('The policy does not have a name field.')
        if self._version is None:
            raise ValueError('The policy does not have a version field.')


    @staticmethod
    def _append_error(errors: List[Any], mismatched_field: str, expected_required: Optional[List[str]], expected_optional: Optional[List[str]], actual: List[str]) -> None:
        if expected_required is None:
            expected_required = ['']
        if expected_optional is None:
            expected_optional = ['']
        errors.append({'mismatched_field': mismatched_field, 'expected_required': expected_required, 'expected_optional': expected_optional, 'actual': actual})


    @staticmethod
    def create(source: Optional[str], banner: Optional['SSH.Banner'], kex: Optional['SSH2.Kex'], client_audit: bool) -> str:
        '''Creates a policy based on a server configuration.  Returns a string.'''

        today = date.today().strftime('%Y/%m/%d')
        compressions = None
        host_keys = None
        kex_algs = None
        ciphers = None
        macs = None
        rsa_hostkey_sizes_str = ''
        rsa_cakey_sizes_str = ''
        dh_modulus_sizes_str = ''
        client_policy_str = ''

        if client_audit:
            client_policy_str = "\n# Set to true to signify this is a policy for clients, not servers.\nclient policy = true\n"

        if kex is not None:
            if kex.server.compression is not None:
                compressions = ', '.join(kex.server.compression)
            if kex.key_algorithms is not None:
                host_keys = ', '.join(kex.key_algorithms)
            if kex.kex_algorithms is not None:
                kex_algs = ', '.join(kex.kex_algorithms)
            if kex.server.encryption is not None:
                ciphers = ', '.join(kex.server.encryption)
            if kex.server.mac is not None:
                macs = ', '.join(kex.server.mac)
            if kex.rsa_key_sizes():
                rsa_key_sizes_dict = kex.rsa_key_sizes()
                for host_key_type in sorted(rsa_key_sizes_dict):
                    hostkey_size, cakey_size = rsa_key_sizes_dict[host_key_type]

                    rsa_hostkey_sizes_str = "%shostkey_size_%s = %d\n" % (rsa_hostkey_sizes_str, host_key_type, hostkey_size)
                    if cakey_size != -1:
                        rsa_cakey_sizes_str = "%scakey_size_%s = %d\n" % (rsa_cakey_sizes_str, host_key_type, cakey_size)

                if len(rsa_hostkey_sizes_str) > 0:
                    rsa_hostkey_sizes_str = "\n# RSA host key sizes.\n%s" % rsa_hostkey_sizes_str
                if len(rsa_cakey_sizes_str) > 0:
                    rsa_cakey_sizes_str = "\n# RSA CA key sizes.\n%s" % rsa_cakey_sizes_str
            if kex.dh_modulus_sizes():
                dh_modulus_sizes_dict = kex.dh_modulus_sizes()
                for gex_type in sorted(dh_modulus_sizes_dict):
                    modulus_size, _ = dh_modulus_sizes_dict[gex_type]
                    dh_modulus_sizes_str = "%sdh_modulus_size_%s = %d\n" % (dh_modulus_sizes_str, gex_type, modulus_size)
                if len(dh_modulus_sizes_str) > 0:
                    dh_modulus_sizes_str = "\n# Group exchange DH modulus sizes.\n%s" % dh_modulus_sizes_str


        policy_data = '''#
# Custom policy based on %s (created on %s)
#
%s
# The name of this policy (displayed in the output during scans).  Must be in quotes.
name = "Custom Policy (based on %s on %s)"

# The version of this policy (displayed in the output during scans).  Not parsed, and may be any value, including strings.
version = 1

# The banner that must match exactly.  Commented out to ignore banners, since minor variability in the banner is sometimes normal.
# banner = "%s"

# The compression options that must match exactly (order matters).  Commented out to ignore by default.
# compressions = %s
%s%s%s
# The host key types that must match exactly (order matters).
host keys = %s

# Host key types that may optionally appear.
#optional host keys = ssh-ed25519-cert-v01@openssh.com,sk-ssh-ed25519@openssh.com,sk-ssh-ed25519-cert-v01@openssh.com,rsa-sha2-256-cert-v01@openssh.com,rsa-sha2-512-cert-v01@openssh.com

# The key exchange algorithms that must match exactly (order matters).
key exchanges = %s

# The ciphers that must match exactly (order matters).
ciphers = %s

# The MACs that must match exactly (order matters).
macs = %s
''' % (source, today, client_policy_str, source, today, banner, compressions, rsa_hostkey_sizes_str, rsa_cakey_sizes_str, dh_modulus_sizes_str, host_keys, kex_algs, ciphers, macs)

        return policy_data


    def evaluate(self, banner: Optional['SSH.Banner'], kex: Optional['SSH2.Kex']) -> Tuple[bool, List[Dict[str, str]], str]:
        '''Evaluates a server configuration against this policy.  Returns a tuple of a boolean (True if server adheres to policy) and an array of strings that holds error messages.'''

        ret = True
        errors = []  # type: List[Any]

        banner_str = str(banner)
        if (self._banner is not None) and (banner_str != self._banner):
            ret = False
            self._append_error(errors, 'Banner', [self._banner], None, [banner_str])

        # All subsequent tests require a valid kex, so end here if we don't have one.
        if kex is None:
            return ret, errors, self._get_error_str(errors)

        if (self._compressions is not None) and (kex.server.compression != self._compressions):
            ret = False
            self._append_error(errors, 'Compression', self._compressions, None, kex.server.compression)

        # If a list of optional host keys was given in the policy, remove any of its entries from the list retrieved from the server.  This allows us to do an exact comparison with the expected list below.
        pruned_host_keys = kex.key_algorithms
        if self._optional_host_keys is not None:
            pruned_host_keys = [x for x in kex.key_algorithms if x not in self._optional_host_keys]

        if (self._host_keys is not None) and (pruned_host_keys != self._host_keys):
            ret = False
            self._append_error(errors, 'Host keys', self._host_keys, self._optional_host_keys, kex.key_algorithms)

        if self._hostkey_sizes is not None:
            hostkey_types = list(self._hostkey_sizes.keys())
            hostkey_types.sort()  # Sorted to make testing output repeatable.
            for hostkey_type in hostkey_types:
                expected_hostkey_size = self._hostkey_sizes[hostkey_type]
                if hostkey_type in kex.rsa_key_sizes():
                    actual_hostkey_size, actual_cakey_size = kex.rsa_key_sizes()[hostkey_type]
                    if actual_hostkey_size != expected_hostkey_size:
                        ret = False
                        self._append_error(errors, 'RSA host key (%s) sizes' % hostkey_type, [str(expected_hostkey_size)], None, [str(actual_hostkey_size)])

        if self._cakey_sizes is not None:
            hostkey_types = list(self._cakey_sizes.keys())
            hostkey_types.sort()  # Sorted to make testing output repeatable.
            for hostkey_type in hostkey_types:
                expected_cakey_size = self._cakey_sizes[hostkey_type]
                if hostkey_type in kex.rsa_key_sizes():
                    actual_hostkey_size, actual_cakey_size = kex.rsa_key_sizes()[hostkey_type]
                    if actual_cakey_size != expected_cakey_size:
                        ret = False
                        self._append_error(errors, 'RSA CA key (%s) sizes' % hostkey_type, [str(expected_cakey_size)], None, [str(actual_cakey_size)])

        if kex.kex_algorithms != self._kex:
            ret = False
            self._append_error(errors, 'Key exchanges', self._kex, None, kex.kex_algorithms)

        if (self._ciphers is not None) and (kex.server.encryption != self._ciphers):
            ret = False
            self._append_error(errors, 'Ciphers', self._ciphers, None, kex.server.encryption)

        if (self._macs is not None) and (kex.server.mac != self._macs):
            ret = False
            self._append_error(errors, 'MACs', self._macs, None, kex.server.mac)

        if self._dh_modulus_sizes is not None:
            dh_modulus_types = list(self._dh_modulus_sizes.keys())
            dh_modulus_types.sort()  # Sorted to make testing output repeatable.
            for dh_modulus_type in dh_modulus_types:
                expected_dh_modulus_size = self._dh_modulus_sizes[dh_modulus_type]
                if dh_modulus_type in kex.dh_modulus_sizes():
                    actual_dh_modulus_size, _ = kex.dh_modulus_sizes()[dh_modulus_type]
                    if expected_dh_modulus_size != actual_dh_modulus_size:
                        ret = False
                        self._append_error(errors, 'Group exchange (%s) modulus sizes' % dh_modulus_type, [str(expected_dh_modulus_size)], None, [str(actual_dh_modulus_size)])

        return ret, errors, self._get_error_str(errors)


    @staticmethod
    def _get_error_str(errors: List[Any]) -> str:
        '''Transforms an error struct to a flat string of error messages.'''

        error_list = []
        for e in errors:
            e_str = "%s did not match. " % e['mismatched_field']
            if ('expected_optional' in e) and (e['expected_optional'] != ['']):
                e_str += "Expected (required): %s; Expected (optional): %s" % (Policy._normalize_error_field(e['expected_required']), Policy._normalize_error_field(e['expected_optional']))
            else:
                e_str += "Expected: %s" % Policy._normalize_error_field(e['expected_required'])
            e_str += "; Actual: %s" % Policy._normalize_error_field(e['actual'])
            error_list.append(e_str)

        error_list.sort()  # To ensure repeatable results for testing.

        error_str = ''
        if len(error_list) > 0:
            error_str = "  * %s" % '\n  * '.join(error_list)

        return error_str


    def get_name_and_version(self) -> str:
        '''Returns a string of this Policy's name and version.'''
        return '%s (version %s)' % (self._name, self._version)


    def is_server_policy(self) -> bool:
        '''Returns True if this is a server policy, or False if this is a client policy.'''
        return self._server_policy


    @staticmethod
    def _normalize_error_field(field: List[str]) -> Any:
        '''If field is an array with a string parsable as an integer, return that integer.  Otherwise, return the field unmodified.'''
        if len(field) == 1:
            try:
                return int(field[0])
            except ValueError:
                return field
        else:
            return field


    def __str__(self) -> str:
        undefined = '{undefined}'

        name = undefined
        version = undefined
        banner = undefined
        compressions_str = undefined
        host_keys_str = undefined
        kex_str = undefined
        ciphers_str = undefined
        macs_str = undefined

        if self._name is not None:
            name = '[%s]' % self._name
        if self._version is not None:
            version = '[%s]' % self._version
        if self._banner is not None:
            banner = '[%s]' % self._banner

        if self._compressions is not None:
            compressions_str = ', '.join(self._compressions)
        if self._host_keys is not None:
            host_keys_str = ', '.join(self._host_keys)
        if self._kex is not None:
            kex_str = ', '.join(self._kex)
        if self._ciphers is not None:
            ciphers_str = ', '.join(self._ciphers)
        if self._macs is not None:
            macs_str = ', '.join(self._macs)

        return "Name: %s\nVersion: %s\nBanner: %s\nCompressions: %s\nHost Keys: %s\nKey Exchanges: %s\nCiphers: %s\nMACs: %s" % (name, version, banner, compressions_str, host_keys_str, kex_str, ciphers_str, macs_str)
