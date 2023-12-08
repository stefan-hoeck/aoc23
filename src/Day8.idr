||| ...x..xx.....x|..x...x.x.x..x
||| ..x..xx....x|..x...x.x..
||| ..x..xx....x..|x...x.x....
module Day8

import Data.SortedMap
import Data.Stream
import Util
import Derive.Prelude

%language ElabReflection

data LR = L | R

%inline lr : LR -> (a,a) -> a
lr L = fst
lr R = snd

0 Map : Type
Map = SortedMap String (String,String)

next : LR -> Map -> String -> String
next x m s = maybe s (lr x) $ lookup s m

follow : Nat -> Stream LR -> String -> Map -> Nat
follow k _       "ZZZ" _ = k
follow k (y::ys) s     m = follow (S k) ys (next y m s) m

endsOnZ : String -> Bool
endsOnZ s = case unpack s of [_,_,'Z'] => True; _ => False

endsOnA : String -> Bool
endsOnA s = case unpack s of [_,_,'A'] => True; _ => False

-- this works under the (possibly wrong) assumption that the
-- periodic reoccurance of a string ending on `Z` is regular:
-- there is only one such string in the period, and the period's
-- length is the same as the first position of the string ending
-- on Z. This simplifies the task at hand quite a bit, and we
-- only have to compute the lowest common multiple of all the
-- periods.
period :
     SnocList Nat
  -> (cache : SortedMap (Nat,String) Nat)
  -> (m     : Map)
  -> (cur   : Stream (Nat,LR))
  -> (pos   : Nat)
  -> (s     : String)
  -> Maybe Nat
period sn cache m ((p,y)::ys) pos s =
  case lookup (p, s) cache of
    Just pre =>
      case sn of
        [<v] => if v == (pos `minus` pre) then Just v else Nothing
        _    => Nothing
    Nothing  =>
     let sn2 := if endsOnZ s then sn :< pos else sn
         c2  := insert (p,s) pos cache
       in period sn2 c2 m ys (S pos) (next y m s)

toLR : Char -> LR
toLR 'L' = L
toLR _   = R

pair : String -> (String,(String,String))
pair s =
  let [a,"=",b,c] := words s | _ => ("",("",""))
   in (a,(strSubstr 1 3 b, strSubstr 0 3 c))

solve : List String -> Map -> (l : List (Nat,LR)) -> (0 _ : NonEmpty l) => Nat
solve vs m l = foldl Util.lcm 1 $ mapMaybe (period [<] empty m (cycle l) 0) vs

export covering
main : IO ()
main = do
  h::t       <- lines "day8" | [] => putStrLn "empty input"
  lrs@(_::_) <- pure (zipWithIndex $ map toLR (unpack h))
    | [] => putStrLn "empty directions"
  m          <- pure (SortedMap.fromList $ map pair t)
  let s1 := solve ["AAA"] m lrs
      s2 := solve (filter endsOnA $ keys m) m lrs
  putStrLn "day  8 part 1: \{show s1}"
  putStrLn "day  8 part 2: \{show s2}"
