module Day5b

import Control.Monad.State
import Derive.Prelude
import Util

%default total
%language ElabReflection

record Val (t : String) where
  constructor V
  val : Nat

%inline (-) : Val t -> Val t -> Val "len"
V x - V y = V $ x `minus` y

%inline (+) : Val "len" -> Val t -> Val t
(+) (V v) (V y) = V (v + y)

data Evt = SE | DE | SS | DS

%runElab derive "Evt" [Show,Eq,Ord]

0 ETag : Evt -> (s,d : String) -> String
ETag SS s d = s
ETag SE s d = s
ETag DS s d = d
ETag DE s d = d

record Event (src,sh,dst : String) where
  constructor E
  val : Val sh
  evt : Evt
  res : Val (ETag evt src dst)

%inline pair : Event s x d -> (Nat,Evt)
pair e = (e.val.val, e.evt)

record Mapping (s,d : String) where
  constructor M
  src : Val s
  dst : Val d
  len : Val "len"

data ST : (src,sh,dst : String) -> Type where
  Src  : Val s -> Val x -> ST s x d          -- a source range has started
  Dst  : Val x -> Val d -> ST s x d          -- a destination range has started
  Both : Val s -> Val x -> Val d -> ST s x d -- ranges currently overlap
  None : ST s x d                            -- no range at the current position

next : Event s x d -> ST s x d -> (ST s x d,Mapping s d)
next (E v SE r) (Src s d)    = (None,             M s (V d.val) $ v-d)
next (E v DS r) (Src s d)    = (Both (v-d+s) v r, M s (V d.val) $ v-d)
next (E v SE r) (Both s x d) = (Dst v (v-x+d),    M s d $ v-x)
next (E v DE r) (Both s x d) = (Src (v-x+s) v,    M s d $ v-x)
next (E v SS r) (Dst s d)    = (Both r v (v-s+d), M (V 0) (V 0) (V 0))
next (E v SS r) None         = (Src r v,          M (V 0) (V 0) (V 0))
next (E v DS r) None         = (Dst v r,          M (V 0) (V 0) (V 0))
next _          _            = (None,             M (V 0) (V 0) (V 0))

fromIn : Mapping s x -> List (Event s x d)
fromIn (M s d l) = [E d SS s, E (l+d) SE (l+s)]

mrg : List (Mapping s x) -> List (Event s x d) -> List (Mapping s d)
mrg i o =
     filter (\x => x.len.val > 0)
   . evalState {stateType = ST s x d} None
   . traverse (state . next)
   . sortBy (comparing pair)
   $ (i >>= fromIn) ++ o 

events : String -> List (Event s x "location")
events s =
  let [d,s,l] := cast <$> words s | _ => []
   in [E (V s) DS (V d), E (V $ s+l) DE (V $ d+l)]

solve : {x : _} -> List (Mapping "seed" x) -> List (List String) -> String
solve xs ((h::t) :: ys) = solve (mrg xs $ t >>= events) ys
solve xs _ = "best \{x}: \{show $ foldl min 0xffff_ffff (map (val . dst) xs)}"

p1Init : List String -> List (Mapping "seed" "seed")
p1Init = map ((\x => M (V x) (V x) (V 1)) . cast)

p2Init : List String -> List (Mapping "seed" "seed")
p2Init (s::l::xs) = M (V $ cast s) (V $ cast s) (V $ cast l) :: p2Init xs
p2Init _          = []

export
main : IO ()
main = do
  h::""::_::t  <- String.lines <$> text "day5" | _ => putStrLn "Invalid input"
  "seeds:"::ss <- pure (words h)               | _ => putStrLn "Invalid input"
  putStrLn "day  5 part 1: \{solve (p1Init ss) (forget $ split (""==) t)}"
  putStrLn "day  5 part 2: \{solve (p2Init ss) (forget $ split (""==) t)}"
