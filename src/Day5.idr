module Day5

import Util
import Data.List
import Data.Maybe
import Data.Nat

%default total

record Mapping where
  constructor M
  src : Nat
  dst : Nat
  len : Nat

data Rem : Type where
  Fst  : Mapping -> Rem
  None : Rem
  Lst  : Mapping -> Rem

check : Mapping -> Maybe Mapping
check m = if m.len == 0 then Nothing else Just m

drop : Nat -> Mapping -> Mapping
drop n (M s d l) = M (s+n) (d+n) (l `minus` n)

break : Nat -> Mapping -> (Mapping,Maybe Mapping)
break n m = (M m.src m.dst n, check $ drop n m)

splitEq : Mapping -> Mapping -> (Mapping, Rem)
splitEq x y =
  case compare x.len y.len of 
    LT => (M x.src y.dst x.len, Lst $ drop x.len y)
    EQ => (M x.src y.dst x.len, None)
    GT => (M x.src y.dst y.len, Fst $ drop y.len x)

splitMapping : Mapping -> Mapping -> (List Mapping, Rem)
splitMapping x y =
  case compare x.dst y.src of
    LT => case break (y.src `minus` x.dst) x of
      (pre, Just pst) => let (x,rem) := splitEq pst y in ([pre,x],rem)
      (pre, Nothing)  => ([pre], Lst y)
    EQ => mapFst pure $ splitEq x y
    GT => case break (x.dst `minus` y.src) y of
      (_,Just pst) => let (x,rem) := splitEq x pst in ([x],rem)
      (_,Nothing)  => ([], Fst x)

splitCur : Mapping -> List Mapping -> (List Mapping, List Mapping)
splitCur x []        = ([x],[])
splitCur x (y :: ys) =
  case splitMapping x y of
    (ms, Fst x') => mapFst (ms ++) (splitCur x' ys)
    (ms, None)   => (ms, ys)
    (ms, Lst y') => (ms, y'::ys)

splitMappings : (src,dst : List Mapping) -> List Mapping
splitMappings xs        [] = xs
splitMappings []        _  = []
splitMappings (x :: xs) ys =
  let (as,bs) := splitCur x ys in as ++ splitMappings xs bs

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
