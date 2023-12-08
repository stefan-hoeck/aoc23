module Util

import Data.Fuel
import Data.List1
import Data.SortedMap
import public Data.String
import System.File

%default total

gcd' : (a,b : Integer) -> Integer
gcd' a 0 = a
gcd' a b = let r := a `mod` b in gcd' b $ assert_smaller b r

export
gcd : Nat -> Nat -> Nat
gcd a b = cast $ gcd' (cast $ max a b) (cast $ min a b)

export
lcm : Nat -> Nat -> Nat
lcm a b = cast $ (cast {to = Integer} a * cast b) `div` cast (gcd a b)

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

export
trimSplit : Char -> String -> List String
trimSplit c = map trim . forget . split (c ==)

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
