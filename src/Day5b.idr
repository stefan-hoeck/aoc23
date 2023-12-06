||| The startegy of solving this (especially part 2) is to
||| align the source-destination ranges in the almanac and
||| find overlapping and non-overlapping regions to get the
||| final mappings from seeds to locations.
|||
||| For this, we generate a list of "events" on the shared axis
||| betweeen a two adjacent mappings, and write a stateful
||| traversal of this list of events, thus generating a new list
||| of mappings.
|||
||| For instance, if we have
||| 
|||   seed-to-soil map:
|||   50 98 2
|||   52 50 48
|||   
|||   soil-to-fertilizer map:
|||   0  15 37
|||   37 52 2
|||   39 0  15
|||
||| this generates the following sequence of events, sorted by the
||| values on the shared axis of the two adjacent mappings ("soil" in
||| this case)
|||
|||   "seed"                 98 50                                       98
|||   src                    x--x----------------------------------------x
|||   "soil"  0      15      50 52 54                                    100
|||   dst     x------x----------x--x
|||   "fert"  39     0       35 37 39
|||
||| An `x` marks an event (the beginning or ending of a range on the
||| given axis). By traversing the events from left to right, we get
||| the following new mappings from seed to fertilizer:
|||
|||   35 98 2
|||   37 50 2
|||   54 52 46
|||
||| The strategy is thus to create a sorted list of events on the
||| shared axes between adjacent sets of mappings and
||| traverse those events to generate
||| a new list of mapping ranges combining the two original lists of
||| mappings. We use a simple state machine for this plus a bit of help
||| from the type system to avoid we mix up the values on the different
||| axes.
module Day5b

import Control.Monad.State
import Derive.Prelude
import Util

%default total
%language ElabReflection

||| A tagged value on one of the range axes
record Val (t : String) where
  constructor V
  val : Nat

Cast String (Val t) where cast = V . cast

||| We use "len" as a tag for distances on one of the axes.
%inline (-) : Val t -> Val t -> Val "len"
V x - V y = V $ x `minus` y

||| We can increase the value on an axis by a `V "len"`
%inline (+) : Val "len" -> Val t -> Val t
(+) (V v) (V y) = V (v + y)

||| Event type: source end, destination end, source start, destination start
||| Note: Ending events must come before starting events to avoid
||| zero length overlaps.
data Evt = SE | DE | SS | DS

%runElab derive "Evt" [Show,Eq,Ord]

||| Tag used for the second value in an event
0 ETag : Evt -> (s,d : String) -> String
ETag SS s d = s
ETag SE s d = s
ETag DS s d = d
ETag DE s d = d

||| An event on the shared axis of source and destination.
||| `val` is the value on the shared axis when an event happens
||| (a range starts or ends), `evt` is the event in question,
||| and `res` (result) is the second value associated with an event.
||| In case of an event related to a source range, `res` is of type
||| `Val S` otherwise of type `Val D`.
record Event (src,sh,dst : String) where
  constructor E
  val : Val sh
  evt : Evt
  res : Val (ETag evt src dst)

-- used for sorting events by their value on the shared axis and event types
%inline pair : Event s x d -> (Nat,Evt)
pair e = (e.val.val, e.evt)

||| A range of mappings from a source axis to values on a destination axis.
record Mapping (s,d : String) where
  constructor M
  src : Val s
  dst : Val d
  len : Val "len"

||| State of our state machine. See `next`, where we update the
||| state and compute new `Mapping`s based on the current state
||| and the events on the shared axis.
data ST : (src,sh,dst : String) -> Type where
  Src  : Val s -> Val x -> ST s x d          -- a source range has started
  Dst  : Val x -> Val d -> ST s x d          -- a destination range has started
  Both : Val s -> Val x -> Val d -> ST s x d -- ranges currently overlap
  None : ST s x d                            -- no range at the current position

-- compute the new state and mapping from the current state and event.
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

-- Merge the current mappings with the events from the next set
-- of mappings.
mrg : List (Mapping s x) -> List (Event s x d) -> List (Mapping s d)
mrg i o =
     filter (\x => x.len.val > 0)
   . evalState {stateType = ST s x d} None
   . traverse (state . next)
   . sortBy (comparing pair)
   $ (i >>= fromIn) ++ o 

--------------------------------------------------------------------------------
-- Parser and `main` function
--------------------------------------------------------------------------------

events : (0 d : String) -> String -> List (Event s x d)
events _ s =
  let [d,s,l] := cast <$> words s | _ => []
   in [E (V s) DS (V d), E (V $ s+l) DE (V $ d+l)]

dest : String -> String
dest s =
  let [h,_]      := words s         | _ => s
      [_,"to",d] := trimSplit '-' h | _ => s
   in d

solve : {x : _} -> List (Mapping "seed" x) -> List (List String) -> String
solve xs ((h::t) :: ys) = solve (mrg xs $ t >>= events (dest h)) ys
solve xs _ = "best \{x}: \{show $ foldl min 0xffff_ffff (map (val . dst) xs)}"

p1Init : List String -> List (Mapping "seed" "seed")
p1Init = map ((\x => M x x $ V 1) . cast)

p2Init : List String -> List (Mapping "seed" "seed")
p2Init (s::l::xs) = M (cast s) (cast s) (cast l) :: p2Init xs
p2Init _          = []

main : IO ()
main = do
  h::""::_::t  <- String.lines <$> text "day5" | _ => putStrLn "Invalid input"
  "seeds:"::ss <- pure (words h)               | _ => putStrLn "Invalid input"
  putStrLn (solve (p1Init ss) (forget $ split (""==) t))
  putStrLn (solve (p2Init ss) (forget $ split (""==) t))
