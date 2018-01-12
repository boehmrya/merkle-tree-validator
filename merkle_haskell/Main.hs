import qualified Crypto.Hash as H
import qualified Data.ByteString.Char8 as C
import System.Environment
import Data.List.Split
import Data.List
import Data.Char

{- a Digest is a value returned by the hash function (for the curious, see
   here: https://hackage.haskell.org/package/cryptonite-0.24/docs/Crypto-Hash-Algorithms.html) -}
--type Digest = H.Digest H.Blake2b_160

type Digest = H.Digest H.MD5

data MerkleTree = Leaf Digest | Node Digest MerkleTree MerkleTree
  deriving Show

label :: MerkleTree -> Digest
label (Leaf x) = x
label (Node x l r) = x


{- compute a Digest from a String by first converting the String to a ByteString
   and then calling Crypto.Hash's hash function, which gives a different result
   depending on the expected type, which here is the particular Digest type
   defined above (Crypto.Hash.Algorithms has many more Digest types). -}
hash :: String -> Digest
hash s = H.hash (C.pack s)

combineHash :: Digest -> Digest -> Digest
combineHash x y = hash (show x ++ show y)

{- we will assume that the length of the input list is a power of two,
   so we will build a full binary tree (this ensures that some computations
   with paths come out nicely below) -}

buildMerkle :: [String] -> MerkleTree
buildMerkle ss = if (length ss == 1) then Leaf (hash (head (sort(ss))))
      else Node (combineHash (label (buildMerkle (fst (splitAt ((length (sort(ss))) `div` 2) (sort(ss)) )))) (label (buildMerkle (snd (splitAt ((length (sort(ss))) `div` 2) (sort(ss))))))) 
      (buildMerkle (fst (splitAt ((length ss) `div` 2) (sort(ss))))) 
      (buildMerkle (snd (splitAt ((length ss) `div` 2) (sort(ss)))))

-- False means left subtree, True means right subtree
type Path = [Bool]

{- a MerklePatth is a list of (d,b,d') where starting
   from the root of the Merkle tree, the current node has digest d,
   which is computed by combineHash from the digest for the 
   left node (if b is False) or the right node (if b is True),
   together with d'. -}
type MerklePathh = [(Digest,Bool,Digest)]

{- a MerklePath is a MerklePathh plus the Digest for the Leaf that you reach by following
   the MerklePathh in the Merkle tree. -} 
type MerklePath = (MerklePathh, Digest)


getMerklePath :: MerkleTree -> Path -> MerklePathh -> MerklePath
getMerklePath (Leaf x) p m = (m, x)
getMerklePath (Node x l r) p m = if ((head p) == True) then (getMerklePath r (tail p) (m ++ [(x, head p, label l)]))
   else (getMerklePath l (tail p) (m ++ [(x, head p, label r)]))


-- helper function for checkInclusion
-- convert the leaf digest to a tuple to help with checkInclusion
leafDigestToTuple :: Digest -> MerklePathh
leafDigestToTuple d = [(d, True, d)]

-- helper function for checkInclusion
-- add leaf tuple to the merkle path list to help with checkInclusion
-- finally return the reversed list (so we can easily recurse)
leafMerkleTestList :: MerklePath -> MerklePathh
leafMerkleTestList (p,d) = reverse ( concat[p, leafDigestToTuple d] )

-- gets the first element of a tuple
getThird :: (Digest, Bool, Digest) -> Digest
getThird (_, _, c) = c

-- gets the third element of a tuple
getFirst :: (Digest, Bool, Digest) -> Digest
getFirst (a, _, _) = a

-- gets the second element of a tuple
getSecond :: (Digest, Bool, Digest) -> Bool
getSecond (_, a, _) = a

-- checks consecutive hashes using combineHash function
-- provides validation for checkInclusion function
-- helper for checkInclusion
checkTwoHashes :: MerklePathh -> Bool
checkTwoHashes m = (combineHash (getFirst (head (take 2 m))) (getThird (last (take 2 m)))) == (getFirst (last (take 2 m)))

-- uses checkTwoHashes function to recursively check all hashes in the path
-- helper for checkInclusion function
checkHashesPath :: MerklePathh -> Bool
checkHashesPath m = if length m <= 2 then checkTwoHashes m
   else checkTwoHashes (tail m)

-- uses checkTwoHashes function to recursively check all hashes in the path
checkPath :: MerklePath -> Bool
checkPath (p,d) = checkHashesPath ( leafMerkleTestList (p,d) )

-- final check if path is merkle path is included
checkInclusion :: Digest {- root hash -} -> MerklePath -> Bool
checkInclusion root (p,d) = (checkPath (p,d) && ((getFirst (last (leafMerkleTestList (p,d)))) == root))


-- helper function for successor Path
type Bit = Int

boolToInt :: Bool -> Bit
boolToInt b = if b == True then 1 else 0

pathToNums :: Path -> [Bit]
pathToNums p = reverse (map boolToInt p)

bin2int :: [Bit] -> Int
bin2int bits = sum [w*b | (w,b) <- zip weights bits]
   where weights = iterate (*2) 1

successorPath :: Path -> Path -> Bool
successorPath p1 p2 = abs ((bin2int (pathToNums p1)) - (bin2int (pathToNums p2))) == 1

getPath :: MerklePath -> Path -> Path
getPath (m,d) p = if (length m) == 0 then p
   else getPath ((tail m), d) (p ++ [(getSecond (head m))])


checkExclusion :: Digest {- root hash -} ->
                  String {- string to prove is excluded -} ->
                  String {- an included string -} ->
                  String {- another included string, which comes right
                            after the first included string in the sorted leaves of the tree -} ->
                  MerklePath {- proof of inclusion for first included string -} ->
                  MerklePath {- proof of inclusion for second included string -} ->
                  Bool
checkExclusion d s1 s2 s3 mp1 mp2 = if (((checkInclusion d mp1 == True) && (checkInclusion d mp2 == True)) && 
   (successorPath (getPath mp1 []) (getPath mp2 [])) && (s3 > s2))  then True else False



sampleSet = splitOn " " "white coral bells upon a silver stalk ."
sampleHashes = map (\ s -> (s , hash s)) sampleSet

sampleTree = buildMerkle sampleSet
sampleTreeRootHash = label sampleTree
p1 = [True, False, True]
p2 = [True, False, False]

-- exclusion should succeed with these paths
samplePath1 = getMerklePath sampleTree [True, False, True] []
samplePath2 = getMerklePath sampleTree [True, False, False] []
test1 = checkExclusion sampleTreeRootHash "bread" "bells" "coral" samplePath1 samplePath2


{- exclusion should fail with these paths (the string "bread" is not in the Merkle tree, but
   these paths are not the ones needed to show this -}
samplePath1b = getMerklePath sampleTree [True, False, True] []
samplePath2b = getMerklePath sampleTree [False, False, False] []
test2 = checkExclusion sampleTreeRootHash "bread" "bells" "white" samplePath1b samplePath2b


digest1 = hash "bread"
digest2 = hash "bread"
combinedDig = combineHash digest1 digest2

boolToString :: Bool -> String
boolToString b = if (b == True) then "True" else "False"


main :: IO ()
main = do
   print("Test 1: " ++ (boolToString test1))
   print("Test 2: " ++ (boolToString test2))



