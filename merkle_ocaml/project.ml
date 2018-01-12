open Digest;;
open List;;
open String;;


type merkleTree = 
	| Leaf of Digest.t 
	| Node of Digest.t * merkleTree * merkleTree;;


let label (m : merkleTree) : Digest.t =
	match m with
	| Leaf x -> x
	| Node (x, l, r) -> x;;


let hash (s : string) : Digest.t =
  Digest.string s;;


let combineHash (d1: Digest.t) (d2: Digest.t) : Digest.t =
  hash ((Digest.to_hex d1) ^ (Digest.to_hex d2));;


(*
let combineHash (d1: Digest.t) (d2: Digest.t) : Digest.t =
  hash (d1 ^ d1);;
*)
let splitAt (lst: string list) (n: int) : string list * string list =
    let rec aux i acc = function
      | [] -> List.rev acc, []
      | h :: t as l -> if i = 0 then List.rev acc, l
                       else aux (i-1) (h :: acc) t  in
    aux n [] lst;;


(* helper for buildMerkle *)
let fst (a,_) = a;;


(* helper for buildMerkle *)
let snd (_,a) = a;;


let rec buildMerkle (ss : string list) : merkleTree  =
	if ((List.length ss) == 1) then (Leaf (hash (List.hd (List.sort compare ss)))) 
	else Node ((combineHash (label (buildMerkle (fst (splitAt (List.sort compare ss) ((List.length (List.sort compare ss)) / 2))))) (label (buildMerkle (snd (splitAt (List.sort compare ss) ((List.length (List.sort compare ss)) / 2)))))), 
		(buildMerkle (fst (splitAt (List.sort compare ss) ((List.length (List.sort compare ss)) / 2)))), 
		(buildMerkle (snd (splitAt (List.sort compare ss) ((List.length (List.sort compare ss)) / 2)))));;


type path = bool list;;


type merkleElement = (Digest.t * bool * Digest.t);;


type merklePathh = merkleElement list;;


type merklePath = (merklePathh * Digest.t);;


let rec getMerklePath (mt : merkleTree) (p : path) (mh : merklePathh) : merklePath =
	match mt with
	| Leaf x -> (mh, x)
	| Node (x, l, r) -> if ((List.hd p) == true) then (getMerklePath r (List.tl p) (mh @ [(x, List.hd p, label l)]))
	else (getMerklePath l (List.tl p) (mh @ [(x, List.hd p, label r)]));;


(*
helper function for checkInclusion
convert the leaf digest to a tuple to help with checkInclusion
*)
let leafDigestToTuple (d : Digest.t) : merklePathh = [(d, true, d)];;


(*
helper function for checkInclusion
add leaf tuple to the merkle path list to help with checkInclusion
finally return the reversed list (so we can easily recurse)
*)
let leafMerkleTestList ((p,d) : merklePath) : merklePathh = List.rev ( p @ (leafDigestToTuple d) );;


(* gets the third element of a 3-tuple *)
(*
let getFirst ((a : Digest.t), (b : bool), (c : Digest.t)) : Digest.t = a;;
*)
let getFirst ((a,b,c) : merkleElement) : Digest.t = a;;


(* gets the second element of a 3-tuple *)
let getSecond ((a : Digest.t), (b : bool), (c : Digest.t)) : bool = b;;


(* gets the third element of a 3-tuple *)
(* let getThird ((a : Digest.t), (b : bool), (c : Digest.t)) : Digest.t = c;; *)
let getThird ((a,b,c) : merkleElement) : Digest.t = c;;


(* returns the first n elements of a list *)
let rec take (k: int) (xs: merklePathh) : merklePathh = match k with
    | 0 -> []
    | k -> match xs with
           | [] -> failwith "take"
           | y::ys -> y :: (take (k - 1) ys)


(* returns the last element of a list *)
let last (m: merklePathh) = List.hd (List.rev m);;


(* 
Takes merklepathh and returns a bool, checks consecutive hashes using combineHash function,
provides validation for checkInclusion function helper for checkInclusion
*)
let checkTwoHashes (m : merklePathh) : bool = if (compare (Digest.to_hex (combineHash (getFirst (List.hd (take 2 m))) (getThird (last (take 2 m))))) (Digest.to_hex (getFirst (last (take 2 m))))) == 0 then true else false;;


(*
uses checkTwoHashes function to recursively check all hashes in the path, helper for checkInclusion function
*)
let checkHashesPath (m : merklePathh) : bool = if List.length m <= 2 then checkTwoHashes m else checkTwoHashes (List.tl m);;


(* uses checkTwoHashes function to recursively check all hashes in the path *)
let checkPath ((p,d) : merklePath) : bool = checkHashesPath ( leafMerkleTestList (p,d) );;


(* final check if path is merkle path is included *)
let checkInclusion (root : Digest.t) ((p,d) : merklePath) : bool = (checkPath (p,d) && ((getFirst (last (leafMerkleTestList (p,d)))) == root));;


type bit = int;;


let boolToInt (b : bool) : bit = if b == true then 1 else 0;;


let intBitToString (i : int) : string = if i == 1 then "1" else "0";;


let pathToNums (p : path) : bit list = (List.map boolToInt p);;


let bin2int (bits : bit list) : int = int_of_string ("0b" ^ (String.concat "" (List.map intBitToString bits)));;


let successorPath (p1 : path) (p2 : path) : bool = abs ((bin2int (pathToNums p1)) - (bin2int (pathToNums p2))) == 1;;


let rec getPath ((m,d) : merklePath) (p : path) : path = if (List.length m) == 0 then p else getPath ((List.tl m), d) (p @ [(getSecond (List.hd m))]);;


let checkExclusion (d : Digest.t) (s1 : string) (s2 : string) (s3 : string) (mp1 : merklePath) (mp2 : merklePath) : bool = if (((checkInclusion d mp1 == true) && (checkInclusion d mp2 == true)) && 
   (successorPath (getPath mp1 []) (getPath mp2 [])) && (s3 > s2) && (s1 > s2) && (s3 > s1)) then true else false;;


let sampleSet = ["white"; "coral"; "bells"; "upon"; "a"; "silver"; "stalk"; "."];;
let sampleHashes = List.map (fun s -> (s , hash s)) sampleSet;;


let sampleTree = buildMerkle sampleSet;;
let sampleTreeRootHash = label sampleTree;; 
let hexRootHash = Digest.to_hex sampleTreeRootHash;;


(* exclusion should succeed with these paths *)
let samplePath1 = getMerklePath sampleTree [true; false; true] [];;
let samplePath2 = getMerklePath sampleTree [true; false; false] [];;
let test1 = checkExclusion sampleTreeRootHash "bread" "bells" "coral" samplePath1 samplePath2;;


(*
exclusion should fail with these paths (the string "bread" is not in the Merkle tree, but
these paths are not the ones needed to show this
*)
let samplePath1b = getMerklePath sampleTree [true; false; true] [];;
let samplePath2b = getMerklePath sampleTree [false; false; false] [];;
let test2 = checkExclusion sampleTreeRootHash "bread" "bells" "white" samplePath1b samplePath2b;;


let boolToString (b : bool) : string = if (b == true) then "True" else "False";;

print_string ("Test1: " ^ (boolToString test1) ^ "\n");;
print_string ("Test2: " ^ (boolToString test2) ^ "\n");;


