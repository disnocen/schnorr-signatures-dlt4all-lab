from typing import Tuple, Optional, Any
import hashlib
import binascii


p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

# Points are tuples of X and Y coordinates and the point at infinity is
# represented by the None keyword.
G = (0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798, 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8)

Point = Tuple[int, int]

# This implementation can be sped up by storing the midstate after hashing
# tag_hash instead of rehashing it all the time.
def tagged_hash(tag: str, msg: bytes) -> bytes:
    tag_hash = hashlib.sha256(tag.encode()).digest()
    return hashlib.sha256(tag_hash + tag_hash + msg).digest()

def is_infinity(P: Optional[Point]) -> bool:
    return P is None

def x(P: Point) -> int:
    return P[0]

def y(P: Point) -> int:
    return P[1]

def point_add(P1: Optional[Point], P2: Optional[Point]) -> Optional[Point]:
    if P1 is None:
        return P2
    if P2 is None:
        return P1
    if (x(P1) == x(P2)) and (y(P1) != y(P2)):
        return None
    if P1 == P2:
        lam = (3 * x(P1) * x(P1) * pow(2 * y(P1), p - 2, p)) % p
    else:
        lam = ((y(P2) - y(P1)) * pow(x(P2) - x(P1), p - 2, p)) % p
    x3 = (lam * lam - x(P1) - x(P2)) % p
    return (x3, (lam * (x(P1) - x3) - y(P1)) % p)

def point_mul(P: Optional[Point], n: int) -> Optional[Point]:
    R = None
    for i in range(256):
        if (n >> i) & 1:
            R = point_add(R, P)
        P = point_add(P, P)
    return R

def bytes_from_int(x: int) -> bytes:
    return x.to_bytes(32, byteorder="big")

def bytes_from_point(P: Point) -> bytes:
    return bytes_from_int(x(P))

def xor_bytes(b0: bytes, b1: bytes) -> bytes:
    return bytes(x ^ y for (x, y) in zip(b0, b1))

def lift_x_square_y(b: bytes) -> Optional[Point]:
    x = int_from_bytes(b)
    if x >= p:
        return None
    y_sq = (pow(x, 3, p) + 7) % p
    y = pow(y_sq, (p + 1) // 4, p)
    if pow(y, 2, p) != y_sq:
        return None
    return (x, y)

def lift_x_even_y(b: bytes) -> Optional[Point]:
    P = lift_x_square_y(b)
    if P is None:
        return None
    else:
        return (x(P), y(P) if y(P) % 2 == 0 else p - y(P))

def int_from_bytes(b: bytes) -> int:
    return int.from_bytes(b, byteorder="big")

def x_int_from_point(P: bytes) -> int:
    return int_from_bytes(P, byteorder="big")

def hash_sha256(b: bytes) -> bytes:
    return hashlib.sha256(b).digest()

def is_square(x: int) -> bool:
    return int(pow(x, (p - 1) // 2, p)) == 1

def has_square_y(P: Optional[Point]) -> bool:
    infinity = is_infinity(P)
    if infinity: return False
    assert P is not None
    return is_square(y(P))

def has_even_y(P: Point) -> bool:
    return y(P) % 2 == 0

def pubkey_gen(seckey: bytes) -> bytes:
    d0 = int_from_bytes(seckey)
    if not (1 <= d0 <= n - 1):
        raise ValueError('The secret key must be an integer in the range 1..n-1.')
    P = point_mul(G, d0)
    assert P is not None
    return P
    #return bytes_from_point(P)

def aggregate_pubkey_gen(pubkey1: Point, pubkey2: Point) -> bytes:
    return bytes_from_point(point_add(pubkey1, pubkey2))

def schnorr_sign(msg: bytes, seckey: bytes, aux_rand: bytes) -> bytes:
    if len(msg) != 32:
        raise ValueError('The message must be a 32-byte array.')
    d0 = int_from_bytes(seckey)
    if not (1 <= d0 <= n - 1):
        raise ValueError('The secret key must be an integer in the range 1..n-1.')
    if len(aux_rand) != 32:
        raise ValueError('aux_rand must be 32 bytes instead of %i.' % len(aux_rand))
    P = point_mul(G, d0)
    assert P is not None
    d = d0 if has_even_y(P) else n - d0
    t = xor_bytes(bytes_from_int(d), tagged_hash("BIP340/aux", aux_rand))
    k0 = int_from_bytes(tagged_hash("BIP340/nonce", t + bytes_from_point(P) + msg)) % n
    if k0 == 0:
        raise RuntimeError('Failure. This happens only with negligible probability.')
    R = point_mul(G, k0)
    assert R is not None
    k = n - k0 if not has_square_y(R) else k0
    e = int_from_bytes(tagged_hash("BIP340/challenge", bytes_from_point(R) + bytes_from_point(P) + msg)) % n
    sig = (R, (k + e * d) % n)
    print(sig)
    if not aggregate_schnorr_verify(msg, bytes_from_point(P), sig):
        raise RuntimeError('The created signature does not pass verification.')
    return sig

def aggregate_schnorr_sign(sig1,sig2):
    R=point_add(sig1[0],sig2[0])
    S=(sig1[1]+sig2[1])%n
    return (R,S)

def aggregate_schnorr_verify(msg: bytes, pubkey: bytes, sig) -> bool:
    if len(msg) != 32:
        raise ValueError('The message must be a 32-byte array.')
    if len(pubkey) != 32:
        raise ValueError('The public key must be a 32-byte array.')
    # if len(sig) != 64:
        # raise ValueError('The signature must be a 64-byte array.')
    P = lift_x_even_y(pubkey)
    r = x(sig[0])
    s = sig[1]
    if (P is None) or (r >= p) or (s >= n):
        return False
    e = int_from_bytes(tagged_hash("BIP340/challenge", bytes_from_int(r) + pubkey + msg)) % n
    R = point_add(point_mul(G, s), point_mul(P, n - e))
    if (R is None) or (not has_square_y(R)) or (x(R) != r):
        return False
    return True

# def aggregate_schnorr_verify(msg: bytes, pubkey: bytes, sig: bytes) -> bool:
    # if len(msg) != 32:
        # raise ValueError('The message must be a 32-byte array.')
    # if len(pubkey) != 32:
        # raise ValueError('The public key must be a 32-byte array.')
    # if len(sig) != 128:
        # raise ValueError('The signature must be a 64-byte array.')
    # P = lift_x_even_y(pubkey)
# 
    # r1 = int_from_bytes(sig[0:32])
    # s1 = int_from_bytes(sig[32:64])
    # r2 = int_from_bytes(sig[64:96])
    # s2 = int_from_bytes(sig[96:128])
    # 
    # ragg=(r1+r2) % p
    # sagg=(s1+s2) % n
# 
    # e = int_from_bytes(tagged_hash("BIP340/challenge", bytes_from_int(ragg) + pubkey + msg)) % n
    # R = point_add(point_mul(G, sagg), point_mul(P, n - e))
    # if (R is None) or (not has_square_y(R)) or (x(R) != ragg):
        # return False
    # return True
# 
# 
# 
# 
# 
