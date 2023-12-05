module AOC23.Day5

import AOC23.Util
import Data.List
import Data.Maybe
import Data.Nat

record Mapping where
  constructor M
  src : Nat
  dst : Nat
  len : Nat

check : Mapping -> Maybe Mapping
check m = if m.len == 0 then Nothing else Just m

drop : Nat -> Mapping -> Mapping
drop n (M s d l) = M (s+n) (d+n) (l `minus` n)

splitAt : Nat -> Mapping -> (Mapping,Maybe Mapping)
splitAt n m =
  ( M m.src m.dst (min m.len n)
  , check $ M (m.src+n) (m.dst+n) (m.len `minus` n)
  )

splitMappings : (src,dst : List Mapping) -> List Mapping
splitMappings s@(x :: xs) d@(y::ys) =
  case compare x.dst y.src of
    LT =>
      let (pre,rem) := splitAt (y.src `minus` x.dst) x
       in pre :: splitMappings (toList rem ++ xs) d
    EQ => case compare x.len y.len of 
      LT => M x.src y.dst x.len :: splitMappings xs (drop x.len y :: ys)
      EQ => M x.src y.dst x.len :: splitMappings xs ys
      GT => M x.src y.dst y.len :: splitMappings (drop y.len x :: xs) ys
    GT =>
      let (_,Just m) := splitAt (x.dst `minus` y.src) y | _ => splitMappings s ys
       in splitMappings s (m::ys)
splitMappings xs          _        = xs

0 Almanac : Type
Almanac = List Mapping

mapping : String -> Mapping
mapping s =
  let [dst,src,len] := cast <$> words s | _ => M 0 0 0
   in M src dst len

merge : List Mapping -> List Mapping -> List Mapping
merge sl ms = splitMappings (sortBy (comparing dst) sl) (sortBy (comparing src) ms)

almanac : List Mapping -> SnocList Mapping -> List String -> Almanac
almanac alm sx (""::_::t) = almanac (merge alm (sx <>> [])) [<] t
almanac alm sx (h::t)     = almanac alm (sx :< mapping h) t
almanac alm sx []         = merge alm (sx <>> [])

read : List String -> Almanac
read (sds::""::_::t) =
  let ("seeds:"::ss) := words sds | _ => []
   in almanac (map ((\x => M x x 1) . cast) ss) [<] t
read _ = []

p2Init : SnocList Mapping -> List String -> List Mapping
p2Init sx (s :: l :: xs) = p2Init (sx :< M (cast s) (cast s) (cast l)) xs
p2Init sx _ = sx <>> []

read2 : List String -> Almanac
read2 (sds::""::_::t) =
  let ("seeds:"::ss) := words sds | _ => []
   in almanac (p2Init [<] ss) [<] t
read2 _ = []

part1 : List String -> Nat
part1 = foldl min 0xffff_ffff_ffff . map dst . read

part2 : List String -> Nat
part2 = foldl min 0xffff_ffff_ffff . map dst . read2

covering
main : IO ()
main = do
  ls <- lines <$> text "day5"
  printLn (part1 ls)
  printLn (part2 ls)
