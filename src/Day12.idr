module Day12

import Data.SortedMap
import Data.Vect
import Util

%default total

-- memoize intermediate results to avoid exponential growth
0 Memo : Type
Memo = SortedMap (Nat,Nat) Nat

solveM : {k,m : _} -> Memo -> Vect k Char -> Vect m Nat -> (Memo, Nat)

-- not memoized version of solve. must only be invoked from `solveM`
solve : {k,m : _} -> Memo -> Vect k Char -> Vect m Nat -> (Memo, Nat)

dropNat : {k,m : _} -> Memo -> Vect k Char -> Vect m Nat -> Nat -> (Memo, Nat)
-- make sure we have a separator after a sequence of damaged springs
dropNat q ('#'::cs) ys 0     = (q,0)
dropNat q (_  ::cs) ys 0     = solveM q cs ys
dropNat q []   []      0     = (q,1)

dropNat q ('.'::cs) ys (S j) = (q,0)
dropNat q (_  ::cs) ys (S j) = dropNat q cs ys j
dropNat q []        ys _     = (q,0)

solveM q cs ys =
  let Nothing := lookup (k,m) q | Just v => (q,v)
      (q2,v)  := solve q cs ys
   in (insert (k,m) v q2, v)

solve q ('.'::cs) ys          = solveM q cs ys
solve q ('#'::cs) (S y :: ys) = dropNat q cs ys y
solve q ('?'::cs) (S y :: ys) =
  let (q2,r1) := dropNat q cs ys y        -- spring could be damaged
      (q3,r2) := solveM q2 cs (S y :: ys) -- or operational
   in (q3,r1+r2)
solve q ('?'::cs) ys          = solveM q cs ys
solve q []        []          = (q,1)
solve q _         _           = (q,0)

solve1 : String -> Nat
solve1 s =
  let [a,b] := words s | _ => 0
   in snd $ solveM empty (fromList $ unpack a) (map cast (fromList $ commaSep b))

solve2 : String -> Nat
solve2 s =
  let [a,b] := words s | _ => 0
      aa    := List.intersperse "?" (replicate 5 a)
      bb    := List.intersperse "," (replicate 5 b)
   in solve1 (concat $ aa ++ " " :: bb)

example : String

export
main : IO ()
main = do
  -- ls <- pure (String.lines example)
  ls <- lines "day12"
  putStrLn "day 12 part 1: \{show . sum $ map solve1 ls}"
  putStrLn "day 12 part 2: \{show . sum $ map solve2 ls}"

example =
  """
  ???.### 1,1,3
  .??..??...?##. 1,1,3
  ?#?#?#?#?#?#?#? 1,3,1,6
  ????.#...#... 4,1,1
  ????.######..#####. 1,6,5
  ?###???????? 3,2,1
  """
