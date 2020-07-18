import binascii
import itertools


# MSB and LSB utility functions
def LSB(n):
    return n & 0xff
def MSB(n):
    return (n >> 24) & 0xff

# This is the modular inverse of 13477581 mod 2**32
# It is used in state-recovery
TI = 3645876429

# generate the CRC tables
# kinda messy but this is what you get
CRCINVTAB = [-1] * 256
CRCTAB = [-1] * 256

def crcc(b, i):
    temp = int.from_bytes(b, 'big') ^ i
    for j in range(8):
        if temp & 1:
            temp = (temp >> 1) ^ 0xEDB88320
        else:
            temp >>= 1

    return temp

for i in range(256):
    temp = crcc(b'\x00',i)
    CRCTAB[i] = temp
    CRCINVTAB[MSB(temp)] = (temp << 8) ^ i


# perform crc32
def crc32(buf, crc):
    for k in buf:
        crc = ((crc >> 8) & 0xffffff) ^ CRCTAB[LSB(crc ^ k)]
    return crc

# perform crc32 but inverse
def crc32inv(buf, crc):
    for k in buf[::-1]:
        crc = (crc << 8) ^ CRCINVTAB[MSB(crc)] ^ k
    return crc


# main cipher class!
class ZipCrypto:
    # initialise the cipher
    # the values s0, s1 and s2 shouldn't be touched in normal operation but when we're executing an
    # attack we need this functionality so we can start the cipher in the state we want
    def __init__(self, key, s0=0x12345678, s1=0x23456789, s2=0x34567890):
        self.key0 = s0
        self.key1 = s1
        self.key2 = s2
        
        self.process_keys(key)

        # keep track of the key if needed
        self.master_key = key

    # perform the initialisation rounds and mixing in keys
    def process_keys(self, key):
        for i in range(len(key)):
            self.update_keys(key[i])

    def update_keys(self, char):
        # update state for keys 0,1,2. We don't calculate key3 here because it isn't needed unless we
        # are encrypting or decrypting
        self.key0 = crc32(bytes([char]), self.key0)
        self.key1 = (self.key1 + LSB(self.key0)) & 0xffffffff
        self.key1 = (self.key1 * 134775813 + 1) & 0xffffffff
        self.key2 = crc32(bytes([MSB(self.key1)]), self.key2)

    # self-explanitory
    def get_keys(self):
        return (self.key0, self.key1, self.key2)

    def set_keys(self, k0, k1, k2):
        self.key0, self.key1, self.key2 = k0, k1, k2

    # encrypt with the stream cipher. We calculate k3 here only
    def encrypt(self, pt):
        out = b''
        for c in pt:
            # calculate k3
            temp = (self.key2 & 0xffff) | 3
            k3 = LSB((temp * (temp ^ 1)) >> 8)

            # xor with current character
            Ci = bytes([c ^ self.key])
            out += Ci

            # advance stream
            self.update_keys(c)    

        return out

    # alias for encrypt. xor is self-inverse so we don't need separate functions
    def decrypt(self, ct):
        return self.encrypt(ct)


###### ATTACK FUNCTIONS ######


# given an internal state k0, k1, k2 and a ciphertext byte yielded from encryption
# at this point in the keystream, will return the previous state, as well as the plaintext
# byte decrypted from c
def rewind_state(k0, k1, k2, c):
    # reverse the k2 operation
    r2 = crc32inv(bytes([MSB(k1)]), k2)
    # reverse the k1 operation
    r1 = (((k1 - 1) * TI) - LSB(k0)) % (1 << 32)

    # calculate p, finding k3 in the process
    temp = (r2 | 3) & 0xffff
    r3 = LSB((temp * (temp ^ 1)) >> 8)
    p = c ^ r3

    # reverse the k0 operation
    r0 = crc32inv(bytes([p]), k0)
    return r0, r1, r2, p


# given an internal state k0, k1, k2 and ciphertext which represents all encryption up until that point,
# will recursively rewind the state until it reaches the "internal key" which is independent of the plaintext
# and can be used for decryption

# NOTE: to decrypt with an internal key (k0, k1, k2), use:

#    cipher = ZipCrypto(b'', k0, k1, k2)

# and then the cipher as normal
def reconstruct_key(k0, k1, k2, ct):
    c0, c1, c2 = k0, k1, k2

    for c in reversed(ct):
        c0, c1, c2, p = rewind_state(c0, c1, c2, c)

    return c0, c1, c2


# Reconstructs the last four bytes of the password from the key
# This exploits the linearity of the crc32 hash. Consider a crc32 hash 't', which
# has been constructed from hashing 'abcd' - that is to say, beginning with the initial
# state S, applying the hash of 'a', then 'b', then 'c', then 'd'. We can say then that:
#
# t = crc32('abcd', S) = crc32('d', crc32('abc', S))
#
# We denote this state s = crc32('abc', 0)
#
# The linearity property can be stated as follows:
#
# crc32inv('\x00', t) ^ s = '\x00' ^ 'd'
# => crc32inv('\x00', t) ^ s = 'd'
#
# Thus, if we know two crc states, s and t, which are a single byte away from each other, we
# can trivially determine that byte.
#
# As a crc state is 4 bytes long, we can recursively apply this same principle to reconstruct up to 4 bytes
# from the difference of two hashes, as we know what the start state is (the start state of the cipher)

def reconstruct_four_bytes(k0, start=0x12345678):
    # set the temporary value to the hash to reverse
    t = k0

    # if the hash == the start, it has not been updated
    if k0 == start:
        return b''

    # try for length between 1 and 4
    for i in range(1, 5):
        # yield candiate
        t = crc32inv(b'\x00', t)
        # XOR with the start state, and check if it matches with up to the number of
        # bytes we've already checked - if the length is less than 4, then it will leave
        # some state bytes unchanged
        if (t ^ start) >> (8 * i) == 0:
            # return if it does
            return (t ^ start).to_bytes(i, 'little')

    # this should never happen
    assert False, "Error in key location"


# From section 3.6 of the original paper describing the KPA, we can use MSB checking to fairly efficiently
# extend the reconstruction from 4 to 5/6 bytes.
def reconstruct_six_bytes(k0, k1, k2, s0=0x12345678, s1=0x23456789 , s2=0x34567890):
    # calculate the states 1 before what we have (not k0 yet)
    k1_0 = (((k1 - 1) * TI) - LSB(k0)) % (1 << 32)
    k2_0 = crc32inv(bytes([MSB(k1)]), k2)
    # we can go even further on k2, calculate 2 before
    k2_n1 = crc32inv(bytes([MSB(k1_0)]), k2_0)

    # we can now reconstruct the MSBS of all<= 6 bytes that k1 cycles through until the cipher init
    # completes, as we have 2, and there are 4 that are hashed with the initial state of k2 to get the
    # first used state of k2, so we can invert that hash
    k1_bytes = reconstruct_four_bytes(k2_n1, s2) + bytes([MSB(k1_0)]) + bytes([MSB(k1)])

    # begin reconstructing the password
    pw = b''

    # guess the first byte. there may be better ways to do this but the computational cost is
    # fairly minimal
    for j in range(256):
        # calculate the state of k0 after the first pw byte addition
        kk0 = crc32(bytes([j]), s0)
        # calculate what the MSB of k1 would be. If it matches, we good.
        if MSB((((s1 + LSB(kk0)) * 134775813) + 1) % (1 << 32)) == k1_bytes[0]:
            pw += bytes([j])
            break

    # save the current password state
    cc = ZipCrypto(pw, s0, s1, s2)
    state = cc.get_keys()
    
    # continue to guess the next bytes until we get to more than 6 characters or we find a key
    # that works.
    for i in range(1, 6):
        for j in range(256):
            # update the theorical key0
            kk0 = crc32(bytes([j]), state[0])
            # check whether they next key1 MSB would match
            if MSB((((state[1] + LSB(kk0)) * 134775813) + 1) % (1 << 32)) == k1_bytes[i]:
                # append to the current password
                pw += bytes([j])
                
                # instantiate the cipher
                cc = ZipCrypto(pw, s0, s1, s2)
                # check whether the entirety of the keys match
                if cc.get_keys() == (k0, k1, k2):
                    # we're done
                    return (pw)

                # update the state otherwise
                state = cc.get_keys()
                break

    # this CAN happen, if the key doesn't have an equivalent in <= 6 chars
    assert False, "Key not found!"


# finally, we can extend the procedure to arbitrary lengths by bruteforcing every possible
# prefix in front of 6 characters and then performing the 6-charcter algorithm
def recover_pw(k0, k1, k2, known=b''):
    # is it less than 6 bytes?
    try:
        return reconstruct_six_bytes(k0, k1, k2)
    except:
        pass

    # list of possible bytes. we can restrict this if we want
    chars = [bytes([x]) for x in range(256)]

    # if we are given some known characters, we'll want to try it without any prefixing first just in case
    s = 1 if known == "" else 0

    # we're unlikely to need a guess_length of more than 6 before a valid password is found, as the total
    # cipher state is only 12 bytes. However, we'll go up to 2^64 just in case you want to run the program
    # for ~2 years
    for guess_length in range(s, 9):
        for p in itertools.product(chars, repeat=guess_length):
            # produce a guess
            guessed = known + b''.join(p)
            # get the state that comes from that guess:
            # this is slow im almost certain
            cc = ZipCrypto(guessed)
            try:
                # try and reconstruct
                return guessed + reconstruct_six_bytes(k0, k1, k2, *cc.get_keys())
            except:
                continue

    # it will take some time to get here    
    return False
            

# USAGE
# instatiate the cipher with
#   zc = ZipCrypto(b'your password')

# encrypt/decrypt with
#   zc.encrypt(msg)
#   zc.decrypt(ct)

# NOTE: reinstatiate every time you want to use the
# same key to encyrpt or decrypt as the stream needs to be
# reset



# Recover a password from an internal key:
#   pw = recover_pw(k0,k1,k2)
# Optionally, if you know some bytes at the start:
#   pw = recover_pw(k0,k1,k2,b'known bytes')        
    
