module Day13

import Data.List
import Data.List1
import Data.Maybe
import Util
import Derive.Prelude

%language ElabReflection
%default total

data Dir = H | V

%runElab derive "Dir" [Show,Eq,Ord]

halfLength : List a -> Nat -> Nat
halfLength xs n =
  let l := length xs in if fastNatMod l 2 == 0 then fastNatDiv l 2 + n else 0

refl' : List (List Char) -> Nat
refl' xs@(_::t) = if xs == reverse xs then halfLength xs 0 else refl' t
refl' []        = 0

refl : Nat -> List (List Char) -> Nat
refl n xs@(_::t) = if xs == reverse xs then halfLength xs n else refl (S n) t
refl _ []        = 0

mirror : ((Dir,Nat) -> Bool) -> List (List Char) -> Maybe (Dir,Nat)
mirror valid hs =
  let ts := transpose hs
      vs := [ (H, refl 0 hs * 100)
            , (H, refl' (reverse hs) * 100)
            , (V, refl 0 ts)
            , (V, refl' (reverse ts))
            ]
   in List.find valid vs

fixSmudgeLine : List Char -> List (List Char)
fixSmudgeLine []          = []
fixSmudgeLine ('#' :: xs) = ('.' :: xs) :: map ('#' ::) (fixSmudgeLine xs)
fixSmudgeLine (x   :: xs) = map (x ::) (fixSmudgeLine xs)

fixSmudgeLines : List (List Char) -> List (List (List Char))
fixSmudgeLines []        = []
fixSmudgeLines (x :: xs) =
  map (::xs) (fixSmudgeLine x) ++ map (x::) (fixSmudgeLines xs)

gt0 : (Dir,Nat) -> Bool
gt0 = (> 0) . snd

valid : (Dir,Nat) -> (Dir,Nat) -> Bool
valid x y = gt0 y && x /= y

solve2 : List (List Char) -> List Nat
solve2 ts =
  let s1 := fromMaybe (H, 0) $ mirror ((> 0) . snd) ts
   in mapMaybe (map snd . mirror (valid s1)) $ fixSmudgeLines ts

export
main : IO ()
main = do
  bs <- forget . split ([] ==) . map unpack . String.lines <$> text "day13"

  putStrLn "day 13 part 1: \{show . sum $ mapMaybe (map snd . mirror gt0) bs}"
  putStrLn "day 13 part 2: \{show . sum $ bs >>= solve2}"
