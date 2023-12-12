module Util

import Data.Fuel
import Data.List1
import Data.SortedMap
import Data.Vect
import System.File
import public Data.String

%default total

--------------------------------------------------------------------------------
-- Numeric utilities
--------------------------------------------------------------------------------

export
fastNatDiv : Nat -> Nat -> Nat
fastNatDiv x y = cast $ cast {to = Integer} x `div` cast y

export
fastNatMod : Nat -> Nat -> Nat
fastNatMod x y = cast $ cast {to = Integer} x `mod` cast y

export
fastGCD : Nat -> Nat -> Nat
fastGCD a 0 = a
fastGCD 0 b = b
fastGCD a b = let r := a `fastNatMod` b in fastGCD b $ assert_smaller b r

export
fastLCM : Nat -> Nat -> Nat
fastLCM a b = (a * b) `fastNatDiv` fastGCD a b

--------------------------------------------------------------------------------
-- Map Utilities
--------------------------------------------------------------------------------

export
insertWith : Ord k => (v -> v -> v) -> k -> v -> SortedMap k v -> SortedMap k v
insertWith f key val m =
  case lookup key m of
    Nothing => insert key val m
    Just v  => insert key (f v val) m

export
fromListWith : Ord k => (v -> v -> v) -> List (k,v) -> SortedMap k v
fromListWith f = foldl (\m,(key,val) => insertWith f key val m) empty

export
zipWithIndex : List a -> List (Nat,a)
zipWithIndex = go [<] 0
  where
    go : SnocList (Nat,a) -> Nat -> List a -> List (Nat,a)
    go sx k []        = sx <>> []
    go sx k (x :: xs) = go (sx :< (k,x)) (S k) xs

--------------------------------------------------------------------------------
-- Parsing Utilities
--------------------------------------------------------------------------------

export
trimSplit : Char -> String -> List String
trimSplit c = map trim . forget . split (c ==)

export %inline
commaSep : String -> List String
commaSep = trimSplit ','

export %inline
colonSep1 : String -> Either String (Vect 2 String)
colonSep1 s =
  let [a,b] := trimSplit ':' s | _ => Left "Invalid: \{s}"
   in Right [a,b]

export %inline
prefixWord : String -> String -> Either String String
prefixWord pre s =
  let [p,x] := words s | _ => Left "Invalid: \{s}"
   in if pre == p then Right x else Left "Invalid: \{s}"

--------------------------------------------------------------------------------
-- IO Utilities
--------------------------------------------------------------------------------

export
lines : String -> IO (List String)
lines file =
  let path := "resources/\{file}.txt"
   in do
     Right (_,ls) <- readFilePage 0 (limit 1_000_000) path
       | Left err => putStrLn "Error when reading \{path}: \{show err}" $> []
     pure (filter ("" /=) $ map trim ls)

export covering
text : String -> IO String
text file =
  let path := "resources/\{file}.txt"
   in do
     Right s <- readFile path
       | Left err => putStrLn "Error when reading \{path}: \{show err}" $> ""
     pure s
