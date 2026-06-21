-- | Principle 2 · Distinction — the cryptographic interface.
--
-- This module is the ONE place the system trusts cryptography.  It
-- realises the abstract @Crypto@ interface from the Agda model
-- (@Sanctum.P2_Distinction@): a digest and an *asymmetric*, publicly
-- verifiable signature scheme.
--
-- ⚠  DEMO PARAMETERS.  The digest is an FNV-style hash and the signature
--    is a textbook Schnorr scheme over a small fixed prime.  This is
--    self-contained and dependency-free so the project builds and runs
--    offline, and it is genuinely asymmetric (verification needs only the
--    public key).  For production, swap the prime for a real group
--    (Ed25519) and the digest for BLAKE2b/SHA-256.  Nothing else changes:
--    the protocol proofs assume only this interface.
module Sanctum.Crypto
  ( Hash(..)
  , Identity(..)
  , SecretKey(..)
  , Sig(..)
  , digestBytes
  , digestText
  , hashConcat
  , Domain(..)
  , tagged
  , attestationDigest
  , reconfigDigest
  , zeroHash
  , keypair
  , sign
  , verify
  ) where

import           Data.Bits          (xor, (.&.))
import qualified Data.ByteString    as BS
import           Data.ByteString    (ByteString)
import           Data.Word          (Word64, Word8)
import qualified Data.Text          as T
import           Data.Text          (Text)
import           Data.Text.Encoding (encodeUtf8)

----------------------------------------------------------------------
-- Digests
----------------------------------------------------------------------

-- | A digest.  Modelled in Agda as @Hash = ℕ@.
newtype Hash = Hash { unHash :: Word64 } deriving (Eq, Ord)

instance Show Hash where show (Hash w) = "#" ++ show w

-- | The hash of the void: parent of genesis (Agda 'zeroHash').
zeroHash :: Hash
zeroHash = Hash 0

-- FNV-1a 64-bit (DEMO digest — not collision-resistant).
fnv1a :: ByteString -> Word64
fnv1a = BS.foldl' step 0xcbf29ce484222325
  where step h b = (h `xor` fromIntegral b) * 0x100000001b3

-- | Digest of an opaque octet string.
digestBytes :: ByteString -> Hash
digestBytes = Hash . fnv1a

-- | Digest of UTF-8 text (documents are hashed this way in the demo).
digestText :: Text -> Hash
digestText = digestBytes . encodeUtf8

-- Little-endian 8-byte encoding, shared by every field-commitment below.
le64 :: Integral a => a -> [Word8]
le64 w = [ fromIntegral ((toInteger w `div` (256 ^ i)) .&. 0xff) | i <- [0..7::Int] ]

-- | Combine several words into one digest.
hashConcat :: [Word64] -> Hash
hashConcat = digestBytes . BS.pack . concatMap le64

-- | Commitment domains.  Every structured commitment leads with a distinct
--   domain code, so a value in one domain can never be reinterpreted as a
--   value in another (structural domain separation — closes leaf/node and
--   cross-commitment confusion by construction, not by luck).
data Domain = DLeaf | DNode | DRoot | DHeader | DReconfig | DCharter
  deriving (Eq, Show, Enum)

-- | A domain-tagged commitment: @tagged d xs = H(code d ‖ xs)@.
tagged :: Domain -> [Word64] -> Hash
tagged d xs = hashConcat (fromIntegral (fromEnum d) : xs)

-- | The digest an attestation's signature must cover: author ‖ fact ‖ time.
--   (Lives here, next to 'hashConcat', because it is cryptographic
--   commitment logic — not a data type.)
attestationDigest :: Identity -> Hash -> Integer -> Hash
attestationDigest author factHash t =
  tagged DLeaf [ fromIntegral (unIdentity author), unHash factHash, fromIntegral t ]

-- | The digest a reconfiguration certificate must cover.  It binds BOTH
--   the source context (current members + current epoch) and the target
--   (proposed members + target epoch + proposed fault budget), so a
--   signature authorising one reconfiguration cannot be replayed against
--   a different current set, a different epoch, or a parallel fork.
reconfigDigest
  :: [Identity]  -- ^ current members (source binding)
  -> Int         -- ^ current epoch  (source binding)
  -> [Identity]  -- ^ proposed members
  -> Int         -- ^ target epoch
  -> Int         -- ^ proposed fault budget
  -> Hash
reconfigDigest current fromEpoch proposed toEpoch fault =
  tagged DReconfig
       ( fromIntegral (length current) : map (fromIntegral . unIdentity) current
      -- length-prefix separates the two variable-length member runs
      ++ fromIntegral (length proposed) : map (fromIntegral . unIdentity) proposed
      ++ [fromIntegral fromEpoch, fromIntegral toEpoch, fromIntegral fault])

----------------------------------------------------------------------
-- Signatures: textbook Schnorr over a small fixed prime (DEMO).
----------------------------------------------------------------------

-- A 61-bit prime and a generator.  Toy size; replace with a real group.
prime :: Integer
prime = 2305843009213693951    -- 2^61 - 1 (a Mersenne prime)

gen :: Integer
gen = 37

order :: Integer
order = prime - 1              -- exponent modulus

-- | Public identity = g^sk mod p.
newtype Identity = Identity { unIdentity :: Integer } deriving (Eq, Ord)
instance Show Identity where show (Identity x) = "id:" ++ show (x `mod` 100000)

-- | Secret key (an exponent).
newtype SecretKey = SecretKey Integer deriving (Eq, Ord, Show)

-- | Schnorr signature (challenge, response).
data Sig = Sig !Integer !Integer deriving (Eq, Ord)
instance Show Sig where show (Sig e _) = "sig:" ++ show (e `mod` 100000)

modexp :: Integer -> Integer -> Integer -> Integer
modexp _ 0 _ = 1
modexp b e m
  | even e    = let h = modexp b (e `div` 2) m in (h * h) `mod` m
  | otherwise = (b `mod` m) * modexp b (e - 1) m `mod` m

-- | Deterministic keypair from a seed.
keypair :: Word64 -> (Identity, SecretKey)
keypair seed =
  let sk = 1 + (toInteger (fnv1a (encodeUtf8 (T.pack (show seed)))) `mod` (order - 1))
  in (Identity (modexp gen sk prime), SecretKey sk)

hOf :: [Integer] -> Integer
hOf xs = toInteger (fnv1a (BS.pack (concatMap le64 xs))) `mod` order

-- | Sign a digest with a secret key (deterministic-nonce Schnorr).
sign :: SecretKey -> Hash -> Sig
sign (SecretKey sk) (Hash h) =
  let m  = toInteger h
      k  = 1 + (hOf [sk, m, 0xdead] `mod` (order - 1))
      r  = modexp gen k prime
      e  = hOf [r, m]
      s  = (k + e * sk) `mod` order
  in Sig e s
{-# INLINE sign #-}

-- | Verify a signature with only the public identity.
--   Checks H(g^s · pk^(-e) ‖ m) == e.
verify :: Identity -> Hash -> Sig -> Bool
verify (Identity pk) (Hash h) (Sig e s) =
  let m    = toInteger h
      gpe  = modexp gen s prime
      pke  = modexp pk ((order - e) `mod` order) prime   -- pk^(-e)
      r'   = (gpe * pke) `mod` prime
  in hOf [r', m] == e
