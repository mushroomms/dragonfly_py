#!/usr/bin/env python3

#"""
#Implements the Dragonfly (SAE) handshake.

#Instead of using a client (STA) and a access point (AP), we
#just programmatically create a peer to peer network of two participiants.
#Either party may initiate the SAE protocol, either party can be the client and server.

#In a mesh scenario, where two APs (two equals) are trying to establish a connection
#between each other and each one could have the role of supplicant or authenticator.

#SAE is build upon the Dragonfly Key Exchange, which is described in https://tools.ietf.org/html/rfc7664.

#https://stackoverflow.com/questions/31074172/elliptic-curve-point-addition-over-a-finite-field-in-python

# THIS FILE IS RESPONSIBLE FOR THE EXCHANGE OF PUBLIC (CLOUD) KEYS BETWEEN KEYGEN AND CLOUD NODES
#"""
import time
import hashlib
import random
import logging
import socket
import re, uuid
import os, random, struct
from collections import namedtuple
from optparse import *
import asn1tools
import sys
import math
from hwcounter import Timer, count, count_end

# Print the help message
help_message = """
This script takes two command-line arguments:
1. <server_port>: The port number to listen for dragonfly initiation.
2. <peer_name>: The name of the peer machine.

Example usage:
python3 dragonfly_ap.py 8080 client1

Make sure to provide both arguments when running the script.
"""

# Check if the correct number of arguments is provided
if len(sys.argv) != 3:
    print("Usage: python3 dragonfly_ap.py <server_port> <peer_name>")
    print(help_message)
    sys.exit(1)

server_port:str = sys.argv[1]
server_name:str = sys.argv[2]

#Compile asn1 file for server_key
asn1_file = asn1tools.compile_files('declaration.asn')

#create tcp/ip socket
sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)

#retrieve local hostname
local_hostname = socket.gethostname()

#get fully qualified hostname
local_fqdn = socket.getfqdn()

#get the according ip address
ip_address = "192.168.10.1"

#output hostname, domain name, ip address
print ("[SOCK] Working on %s (%s) with %s" % (local_hostname, local_fqdn, ip_address))

#bind socket to port
server_address = ('192.168.10.1', int(server_port))

print ("[SOCK] Starting up on %s port %s" % server_address)
print ("[SOCK] Listening for %s machine" % server_name)
sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
sock.bind(server_address)

logger = logging.getLogger('dragonfly')
logger.setLevel(logging.INFO)

# create file handler which logs even debug messages
fh = logging.FileHandler('dragonfly.log')
fh.setLevel(logging.DEBUG)

# create console handler with a higher log level
ch = logging.StreamHandler()
ch.setLevel(logging.DEBUG)

# create formatter and add it to the handlers
formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
ch.setFormatter(formatter)
fh.setFormatter(formatter)

# add the handlers to logger
logger.addHandler(ch)
logger.addHandler(fh)

Point = namedtuple("Point", "x y")
# The point at infinity (origin for the group law).
O = 'Origin'

def lsb(x):
    binary = bin(x).lstrip('0b')
    return binary[0]

def legendre(a, p):
    return pow(a, (p - 1) // 2, p)

def tonelli_shanks(n, p):
    """
    # https://rosettacode.org/wiki/Tonelli-Shanks_algorithm#Python
    """
    assert legendre(n, p) == 1, "not a square (mod p)"
    q = p - 1
    s = 0
    while q % 2 == 0:
        q //= 2
        s += 1
    if s == 1:
        return pow(n, (p + 1) // 4, p)
    for z in range(2, p):
        if p - 1 == legendre(z, p):
            break
    c = pow(z, q, p)
    r = pow(n, (q + 1) // 2, p)
    t = pow(n, q, p)
    m = s
    t2 = 0
    while (t - 1) % p != 0:
        t2 = (t * t) % p
        for i in range(1, m):
            if (t2 - 1) % p == 0:
                break
            t2 = (t2 * t2) % p
        b = pow(c, 1 << (m - i - 1), p)
        r = (r * b) % p
        c = (b * b) % p
        t = (t * c) % p
        m = i
    return r

class Curve():
    """
    Mathematical operations on a Elliptic Curve.

    A lot of code taken from:
    https://stackoverflow.com/questions/31074172/elliptic-curve-point-addition-over-a-finite-field-in-python
    """

    def __init__(self, a, b, p):
        self.a = a
        self.b = b
        self.p = p

    def curve_equation(self, x):
        """
        We currently use the elliptic curve
        NIST P-384
        """
        return (pow(x, 3) + (self.a * x) + self.b) % self.p

    def is_quadratic_residue(self, x):
        """
        https://en.wikipedia.org/wiki/Euler%27s_criterion
        Computes Legendre Symbol.
        """
        return pow(x, (self.p-1) // 2, self.p) == 1

    def valid(self, P):
        """
        Determine whether we have a valid representation of a point
        on our curve.  We assume that the x and y coordinates
        are always reduced modulo p, so that we can compare
        two points for equality with a simple ==.
        """
        if P == O:
            return True
        else:
            return (
                (P.y**2 - (P.x**3 + self.a*P.x + self.b)) % self.p == 0 and
                0 <= P.x < self.p and 0 <= P.y < self.p)

    def inv_mod_p(self, x):
        """
        Compute an inverse for x modulo p, assuming that x
        is not divisible by p.
        """
        if x % self.p == 0:
            raise ZeroDivisionError("Impossible inverse")
        return pow(x, self.p-2, self.p)

    def ec_inv(self, P):
        """
        Inverse of the point P on the elliptic curve y^2 = x^3 + ax + b.
        """
        if P == O:
            return P
        return Point(P.x, (-P.y) % self.p)

    def ec_add(self, P, Q):
        """
        Sum of the points P and Q on the elliptic curve y^2 = x^3 + ax + b.
        https://stackoverflow.com/questions/31074172/elliptic-curve-point-addition-over-a-finite-field-in-python
        """
        if not (self.valid(P) and self.valid(Q)):
            raise ValueError("Invalid inputs")

        # Deal with the special cases where either P, Q, or P + Q is
        # the origin.
        if P == O:
            result = Q
        elif Q == O:
            result = P
        elif Q == self.ec_inv(P):
            result = O
        else:
            # Cases not involving the origin.
            if P == Q:
                dydx = (3 * P.x**2 + self.a) * self.inv_mod_p(2 * P.y)
            else:
                dydx = (Q.y - P.y) * self.inv_mod_p(Q.x - P.x)
            x = (dydx**2 - P.x - Q.x) % self.p
            y = (dydx * (P.x - x) - P.y) % self.p
            result = Point(x, y)

        # The above computations *should* have given us another point
        # on the curve.
        assert self.valid(result)
        return result

    def double_add_algorithm(self, scalar, P):
        """
        Double-and-Add Algorithm for Point Multiplication
        Input: A scalar in the range 0-p and a point on the elliptic curve P
        https://stackoverflow.com/questions/31074172/elliptic-curve-point-addition-over-a-finite-field-in-python
        """
        assert self.valid(P)

        b = bin(scalar).lstrip('0b')
        T = P
        for i in b[1:]:
            T = self.ec_add(T, T)
            if i == '1':
                T = self.ec_add(T, P)

        assert self.valid(T)
        return T

class Peer:
    """
    Implements https://wlan1nde.wordpress.com/2018/09/14/wpa3-improving-your-wlan-security/
    Take a ECC curve from here: https://safecurves.cr.yp.to/

    Example: NIST P-384
    y^2 = x^3-3x+27580193559959705877849011840389048093056905856361568521428707301988689241309860865136260764883745107765439761230575
    modulo p = 2^384 - 2^128 - 2^96 + 2^32 - 1
    2000 NIST; also in SEC 2 and NSA Suite B

    See here: https://www.rfc-editor.org/rfc/rfc5639.txt

   Curve-ID: brainpoolP256r1
      p =
      A9FB57DBA1EEA9BC3E660A909D838D726E3BF623D52620282013481D1F6E5377
      A =
      7D5A0975FC2C3057EEF67530417AFFE7FB8055C126DC5C6CE94A4B44F330B5D9
      B =
      26DC5C6CE94A4B44F330B5D9BBD77CBF958416295CF7E1CE6BCCDC18FF8C07B6
      x =
      8BD2AEB9CB7E57CB2C4B482FFC81B7AFB9DE27E1E3BD23C23A4453BD9ACE3262
      y =
      547EF835C3DAC4FD97F8461A14611DC9C27745132DED8E545C1D54C72F046997
      q =
      A9FB57DBA1EEA9BC3E660A909D838D718C397AA3B561A6F7901E0E82974856A7
      h = 1
    """

    def __init__(self, password, mac_address, name):
        self.name = name
        self.password = password
        self.mac_address = mac_address

        # Try out Curve-ID: brainpoolP256t1
        self.p = int('A9FB57DBA1EEA9BC3E660A909D838D726E3BF623D52620282013481D1F6E5377', 16)
        self.a = int('7D5A0975FC2C3057EEF67530417AFFE7FB8055C126DC5C6CE94A4B44F330B5D9', 16)
        self.b = int('26DC5C6CE94A4B44F330B5D9BBD77CBF958416295CF7E1CE6BCCDC18FF8C07B6', 16)
        self.q = int('A9FB57DBA1EEA9BC3E660A909D838D718C397AA3B561A6F7901E0E82974856A7', 16)
        self.curve = Curve(self.a, self.b, self.p)

        # A toy curve
        # self.a, self.b, self.p = 2, 2, 17
        # self.q = 19
        # self.curve = Curve(self.a, self.b, self.p)

    def initiate(self, other_mac, k=40):
        """
        See algorithm in https://tools.ietf.org/html/rfc7664
        in section 3.2.1
        """
        self.other_mac = other_mac
        found = 0
        num_valid_points = 0
        counter = 1
        n = self.p.bit_length() + 64

        while counter <= k:
            base = self.compute_hashed_password(counter)
            temp = self.key_derivation_function(n, base, 'Dragonfly Hunting And Pecking')
            seed = (temp % (self.p - 1)) + 1
            val = self.curve.curve_equation(seed)
            if self.curve.is_quadratic_residue(val):
                if num_valid_points < 5:
                    x = seed
                    save = base
                    found = 1
                    num_valid_points += 1
                    print('[DRGN] Got point after {} iterations'.format(counter))

            counter = counter + 1

        if found == 0:
            logger.error('[DRGN] No valid point found after {} iterations'.format(k))
        elif found == 1:
            # https://crypto.stackexchange.com/questions/6777/how-to-calculate-y-value-from-yy-mod-prime-efficiently
            # https://rosettacode.org/wiki/Tonelli-Shanks_algorithm
            y = tonelli_shanks(self.curve.curve_equation(x), self.p)

            PE = Point(x, y)

            # check valid point
            assert self.curve.curve_equation(x) == pow(y, 2, self.p)

            print('[DRGN] Using {}-th valid Point={}'.format(num_valid_points, PE))
            print('[DRGN] Point is on curve: {}'.format(self.curve.valid(PE)))

            self.PE = PE
            assert self.curve.valid(self.PE)

    def commit_exchange(self):
        """
        This is basically Diffie Hellman Key Exchange (or in our case ECCDH)

        In the Commit Exchange, both sides commit to a single guess of the
        password.  The peers generate a scalar and an element, exchange them
        with each other, and process the other's scalar and element to
        generate a common and shared secret.

        If we go back to elliptic curves over the real numbers, there is a nice geometric
        interpretation for the ECDLP: given a starting point P, we compute 2P, 3P, . . .,
        d P = T , effectively hopping back and forth on the elliptic curve. We then publish
        the starting point P (a public parameter) and the final point T (the public key). In
        order to break the cryptosystem, an attacker has to figure out how often we “jumped”
        on the elliptic curve. The number of hops is the secret d, the private key.
        """
        # seed the PBG before picking a new random number
        # random.seed(time.process_time())

        # None or no argument seeds from current time or from an operating
        # system specific randomness source if available.
        random.seed()

        # Otherwise, each party chooses two random numbers, private and mask
        self.private = random.randrange(1, self.p)
        self.mask = random.randrange(1, self.p)

        # print('[DRGN] Private={}'.format(self.private))
        # print('[DRGN] Mask={}'.format(self.mask))

        # These two secrets and the Password Element are then used to construct
        # the scalar and element:

        # what is q?
        # o  A point, G, on the elliptic curve, which serves as a generator for
        #    the ECC group.  G is chosen such that its order, with respect to
        #    elliptic curve addition, is a sufficiently large prime.
        #
        # o  A prime, q, which is the order of G, and thus is also the size of
        #    the cryptographic subgroup that is generated by G.

        # https://math.stackexchange.com/questions/331329/is-it-possible-to-compute-order-of-a-point-over-elliptic-curve
        # In the elliptic Curve cryptography, it is said that the order of base point
        # should be a prime number, and order of a point P is defined as k, where kP=O.

        # Theorem 9.2.1 The points on an elliptic curve together with O
        # have cyclic subgroups. Under certain conditions all points on an
        # elliptic curve form a cyclic group.
        # For this specific curve the group order is a prime and, according to Theo-
        # rem 8.2.4, every element is primitive.

        # Question: What is the order of our PE?
        # the order must be p, since p is a prime

        self.scalar = (self.private + self.mask) % self.q

        # If the scalar is less than two (2), the private and mask MUST be
        # thrown away and new values generated.  Once a valid scalar and
        # Element are generated, the mask is no longer needed and MUST be
        # irretrievably destroyed.
        if self.scalar < 2:
            raise ValueError('[DRGN] Scalar is {}, regenerating...'.format(self.scalar))

        P = self.curve.double_add_algorithm(self.mask, self.PE)

        # get the inverse of res
        # −P = (x_p , p − y_p ).
        self.element = self.curve.ec_inv(P)

        assert self.curve.valid(self.element)

        # The peers exchange their scalar and Element and check the peer's
        # scalar and Element, deemed peer-scalar and Peer-Element.  If the peer
        # has sent an identical scalar and Element -- i.e., if scalar equals
        # peer-scalar and Element equals Peer-Element -- it is sign of a
        # reflection attack, and the exchange MUST be aborted.  If the values
        # differ, peer-scalar and Peer-Element must be validated.

        print('[DRGN] Sending scalar and element to the Peer!')
        print('[DRGN] Scalar={}'.format(self.scalar))
        print('[DRGN] Element={}'.format(self.element))

        return self.scalar, self.element

    def compute_shared_secret(self, peer_element, peer_scalar, peer_mac):
        """
        ss = F(scalar-op(private,
                         element-op(peer-Element,
                                    scalar-op(peer-scalar, PE))))

        AP1: K = private(AP1) • (scal(AP2) • P(x, y) ◊ new_point(AP2))
               = private(AP1) • private(AP2) • P(x, y)
        AP2: K = private(AP2) • (scal(AP1) • P(x, y) ◊ new_point(AP1))
               = private(AP2) • private(AP1) • P(x, y)

        A shared secret element is computed using one’s rand and
        the other peer’s element and scalar:
        Alice: K = rand A • (scal B • PW + elemB )
        Bob: K = rand B • (scal A • PW + elemA )

        Since scal(APx) • P(x, y) is another point, the scalar multiplied point
        of e.g. scal(AP1) • P(x, y) is added to the new_point(AP2) and afterwards
        multiplied by private(AP1).
        """
        self.peer_element = peer_element
        self.peer_scalar = peer_scalar
        self.peer_mac = peer_mac
        
        print("[DRGN] Validating Scalar and Element...")
        assert self.curve.valid(self.peer_element)

        # If both the peer-scalar and Peer-Element are
        # valid, they are used with the Password Element to derive a shared
        # secret, ss:

        if self.peer_element == self.element and self.peer_scalar == self.scalar:
            print("[ALERT] Sign of reflection attack! Dragonfly key exchange aborted")
            sys.exit(0)

        Z = self.curve.double_add_algorithm(self.peer_scalar, self.PE)
        ZZ = self.curve.ec_add(self.peer_element, Z)
        K = self.curve.double_add_algorithm(self.private, ZZ)

        self.k = K[0]

        print('[DRGN] [{}] Shared Secret = {}'.format(self.name, self.k))

        own_message = '{}{}{}{}{}{}'.format(self.k , self.scalar , self.peer_scalar , self.element[0] , self.peer_element[0] , self.mac_address).encode()

        H = hashlib.sha256()
        H.update(own_message)
        self.token = H.hexdigest()

        return self.token

    def confirm_exchange(self, peer_token):
        """
            In the Confirm Exchange, both sides confirm that they derived the
            same secret, and therefore, are in possession of the same password.
        """
        peer_message = '{}{}{}{}{}{}'.format(self.k , self.peer_scalar , self.scalar , self.peer_element[0] , self.element[0] , self.peer_mac).encode()
        H = hashlib.sha256()
        H.update(peer_message)
        self.peer_token_computed = H.hexdigest()

        print('[DRGN] [{}] Computed Token from Peer={}'.format(self.name, self.peer_token_computed))
        print('[DRGN] [{}] Received Token from Peer={}'.format(self.name, peer_token))

        # Pairwise Master Key” (PMK)
        # compute PMK = H(k | scal(AP1) + scal(AP2) mod q)
        pmk_message = '{}{}'.format(self.k, (self.scalar + self.peer_scalar) % self.q).encode()
        #H = hashlib.sha256()
        #H.update(pmk_message)
        self.PMK = hashlib.sha256(pmk_message).digest()

        print('[DRGN] [{}] Pairwise Master Key(PMK)={}'.format(self.name, self.PMK))
        return self.PMK

    def key_derivation_function(self, n, base, seed):
        """
        B.5.1 Per-Message Secret Number Generation Using Extra Random Bits

        Key derivation function from Section B.5.1 of [FIPS186-4]

        The key derivation function, KDF, is used to produce a
        bitstream whose length is equal to the length of the prime from the
        group's domain parameter set plus the constant sixty-four (64) to
        derive a temporary value, and the temporary value is modularly
        reduced to produce a seed.
        """
        combined_seed = '{}{}'.format(base, seed).encode()

        # base and seed concatenated are the input to the RGB
        random.seed(combined_seed)

        # Obtain a string of N+64 returned_bits from an RBG with a security strength of
        # requested_security_strength or more.

        randbits = random.getrandbits(n)
        binary_repr = format(randbits, '0{}b'.format(n))

        assert len(binary_repr) == n

        logger.debug('Rand={}'.format(binary_repr))

        # Convert returned_bits to the non-negative integer c (see Appendix C.2.1).
        C = 0
        for i in range(n):
            if int(binary_repr[i]) == 1:
                C += pow(2, n-i)

        logger.debug('C={}'.format(C))

        #k = (C % (n - 1)) + 1

        k = C

        logger.debug('k={}'.format(k))

        return k

    def compute_hashed_password(self, counter):
        maxm = max(self.mac_address, self.other_mac)
        minm = min(self.mac_address, self.other_mac)
        message = '{}{}{}{}'.format(maxm, minm, self.password, counter).encode()
        logger.debug('Message to hash is: {}'.format(message))
        H = hashlib.sha256()
        H.update(message)
        digest = H.digest()
        return digest
'''
BLOCK_SIZE = 16
pad = lambda s: bytes(s + (BLOCK_SIZE - len(s) % BLOCK_SIZE) * chr(BLOCK_SIZE - len(s) %     BLOCK_SIZE), 'utf-8')
unpad = lambda s: s[:-ord(s[-1:])]
 

def encrypt(raw, PMK):
        raw = pad(raw)
        iv = Random.new().read(AES.block_size)
        cipher = AES.new(PMK, AES.MODE_CBC, iv)
        return base64.b64encode(iv + cipher.encrypt(raw))
'''

def handshake():
    print()
    print("========= Dragonfly Key Exchange ==========") 
    #Own MAC address
    own_mac = (':'.join(re.findall('..', '%012x' % uuid.getnode())))

    # Listening for connection
    sock.listen(1)
    connection, client_address = sock.accept()
    
    print ("[SOCK] Connecting from", client_address)
    raw_other_mac = connection.recv(1024)
    receive_mac_address = time.time() # Time receive MAC address

    #decode BER and get MAC address
    other_decode_mac = asn1_file.decode('DataMac', raw_other_mac)
    other_mac = other_decode_mac.get('data')

    #Encode MAC address with BER and send MAC address to peer
    own_mac_BER = asn1_file.encode('DataMac', {'data': own_mac})
    connection.send(own_mac_BER)
    time_taken_mac_address = (time.time() - receive_mac_address) * 1000 # Time taken to send MAC address

    print ("[DRGN] Own MAC Address:",own_mac)
    print ("[DRGN] Peer MAC Address:",other_mac)

    print('[DRGN] Starting hunting and pecking to derive PE...')
    ap = Peer('abc1238', own_mac, 'AP')

    start_initiate = time.time() #start time of initiate
    process_initiate_start_time = time.process_time() #start cpu time of initiate
    start_initiate_cpucycle = count()
    ap.initiate(other_mac)
    initiate_cpucycle = count_end() - start_initiate_cpucycle
    initiate_wall_time = (time.time() - start_initiate) * 1000 #final time for initiate wall
    initiate_cpu_time = (time.process_time() - process_initiate_start_time) * 1000 #final time for initiate cpu

    print()
    print("========== Dragonfly Commit Exchange ==========")

    start_commit = time.time() #start commit wall time 
    process_commit_start = time.process_time() #start commit cpu time 
    start_commit_cpucycle = count()
    scalar_ap, element_ap = ap.commit_exchange()
    commit_cpucycle = count_end() - start_commit_cpucycle
    commit_cpu_time = (time.process_time() - process_commit_start) * 1000 #final commit cpu time
    commit_wall_time = (time.time() - start_commit) * 1000 #final commit wall time

    #Scalar / element BER encoded received and decoded
    print('[DRGN] Scalar and Element Received from STA')
    scalar_element_ap_encoded= connection.recv(1024)
    receive_scalar_element = time.time() # Time when scalar & element is received

    scalar_element_ap_decoded = asn1_file.decode('DataScalarElement', scalar_element_ap_encoded)
    scalar_element_ap = scalar_element_ap_decoded.get('data')

    #BER encode scalar_ap / element_ap 
    scalar_complete = ("\n".join([str(scalar_ap), str(element_ap)]))
    scalar_element_BER = asn1_file.encode('DataScalarElement',{'data': scalar_complete})

    #Send Scalar / element ap data
    connection.sendall(scalar_element_BER)
    time_scalar_element = (time.time() - receive_scalar_element) * 1000 # Time taken to send scalar & element

    # scalar_element_ap = connection.recv(1024).decode()
    data = scalar_element_ap.split('\n')
    # print (data[0])
    # print (data[1])
    scalar_sta = data[0]
    element_sta = data[1]
    print ('[DRGN] STA Scalar:',scalar_sta)
    print ('[DRGN] STA Elemenet:',element_sta)

    print('[DRGN] Computing shared secret...\n')
    namedtuple_element_sta = eval(element_sta)

    start_compute = time.time()
    process_start_compute = time.process_time()
    start_compute_cpucycle = count()
    ap_token = ap.compute_shared_secret(namedtuple_element_sta, int(scalar_sta), other_mac)
    compute_cpucycle = count_end() - start_compute_cpucycle
    compute_wall_time = (time.time() - start_compute) * 1000 #final compute wall time 
    compute_cpu_time = (time.process_time() - process_start_compute) * 1000 #final compute cpu time

    print()
    print("========== Dragonfly Confirm Exchange ==========")    

    # Received BER encoded STA token and decode it
    staToken_encoded = connection.recv(1024)
    receive_token = time.time()
    staToken_decoded = asn1_file.decode('DataStaAp', staToken_encoded)
    sta_token = staToken_decoded.get('data')

    print('[DRGN] Received STA token:', sta_token)

    # Encode ap_token to be BER and send to peer
    apToken_encoded = asn1_file.encode('DataStaAp',{'data':ap_token})
    connection.send(apToken_encoded)
    time_taken_token = (time.time() - receive_token) * 1000 # Time taken to send token
    print("[DRGN] AP Token is being sent over:", ap_token)

    start_confirm = time.time()
    process_start_confirm = time.process_time()
    start_confirm_cpucycle = count()
    PMK_Key = ap.confirm_exchange(sta_token)
    confirm_cpucycle = count_end() - start_confirm_cpucycle
    confirm_wall_time = time.time() - start_confirm #final confirm wall time 
    confirm_cpu_time = time.process_time() - process_start_confirm #final confirm cpu time

    total_wall_time = initiate_wall_time + commit_wall_time + compute_wall_time + confirm_wall_time
    total_cpu_time = initiate_cpu_time + commit_cpu_time + compute_cpu_time + confirm_cpu_time
    total_cpucycle = initiate_cpucycle + commit_cpucycle + compute_cpucycle + confirm_cpucycle

    # Writing PMK.key into file
    pmk_filename = server_name + "_pmk.key"
    f = open(pmk_filename, "wb")
    f.write(PMK_Key)
    f.close()

    print("\n[STA] Time taken to send MAC address:", time_taken_mac_address, "ms")
    print("[STA] Time taken to send Scalar & Element:", time_scalar_element, "ms")
    print("[STA] Time taken to send token:", time_taken_token, "ms")

    print("\n[STA] WALL TIME for Dragonfly Key Exchange: " + str(total_wall_time) + " ms")
    print("[STA] CPU TIME for Dragonfly Key Exhcange: " + str(total_cpu_time) + " ms")
    print("[STA] CPU Cycles for Dragonfly Exchange: " + str(total_cpucycle))

    print()
    os.system("md5sum " + pmk_filename)    
    print()         

if __name__ == '__main__':
    handshake()
    sock.close()
