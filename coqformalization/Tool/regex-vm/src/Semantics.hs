module Semantics where

import qualified Prelude

__ :: any
__ = Prelude.error "Logical or arity value used"

false_rect :: a1
false_rect =
  Prelude.error "absurd case"

false_rec :: a1
false_rec =
  false_rect

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect _ f _ =
  f

eq_rec :: a1 -> a2 -> a1 -> a2
eq_rec =
  eq_rect

eq_rec_r :: a1 -> a2 -> a1 -> a2
eq_rec_r =
  eq_rec

app :: (([]) a1) -> (([]) a1) -> ([]) a1
app l m =
  case l of {
   ([]) -> m;
   (:) a l1 -> (:) a (app l1 m)}

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
data SigT a p =
   ExistT a p

acc_rect :: (a1 -> () -> (a1 -> () -> a2) -> a2) -> a1 -> a2
acc_rect f x =
  f x __ (\y _ -> acc_rect f y)

well_founded_induction_type :: (a1 -> (a1 -> () -> a2) -> a2) -> a1 -> a2
well_founded_induction_type x a =
  acc_rect (\x0 _ x1 -> x x0 x1) a

well_founded_induction :: (a1 -> (a1 -> () -> a2) -> a2) -> a1 -> a2
well_founded_induction =
  well_founded_induction_type

append :: Prelude.String -> Prelude.String -> Prelude.String
append s1 s2 =
  case s1 of {
   ([]) -> s2;
   (:) c s1' -> (:) c (append s1' s2)}

data Regex =
   Empty
 | Eps
 | Chr Prelude.Char
 | Cat Regex Regex
 | Choice Regex Regex
 | Star Regex

type Input = SigT Regex Prelude.String

mk_input :: Regex -> Prelude.String -> Input
mk_input e s =
  ExistT e s

data Bit =
   O
 | I

type Code = ([]) Bit

null :: Regex -> Prelude.Bool
null e =
  case e of {
   Empty -> Prelude.False;
   Chr _ -> Prelude.False;
   Cat e1 e2 ->
    case null e1 of {
     Prelude.True -> null e2;
     Prelude.False -> Prelude.False};
   Choice e1 e2 ->
    case null e1 of {
     Prelude.True -> Prelude.True;
     Prelude.False -> null e2};
   _ -> Prelude.True}

empty :: Regex -> Prelude.Bool
empty e =
  case e of {
   Eps -> Prelude.True;
   Cat e1 e2 ->
    case empty e1 of {
     Prelude.True -> empty e2;
     Prelude.False -> Prelude.False};
   Choice e1 e2 ->
    case empty e1 of {
     Prelude.True -> empty e2;
     Prelude.False -> Prelude.False};
   Star e1 -> empty e1;
   _ -> Prelude.False}

unprob :: Regex -> Regex
unprob e =
  case e of {
   Cat e2 e3 -> Cat (unprob e2) (unprob e3);
   Choice e2 e3 -> Choice (unprob e2) (unprob e3);
   Star e2 ->
    case null e2 of {
     Prelude.True ->
      case empty e2 of {
       Prelude.True -> Eps;
       Prelude.False -> Star
        (let {
          unprob_rec e3 =
            case e3 of {
             Cat e1 e4 ->
              case null e1 of {
               Prelude.True ->
                case empty e1 of {
                 Prelude.True ->
                  case null e4 of {
                   Prelude.True -> unprob_rec e4;
                   Prelude.False -> unprob e4};
                 Prelude.False ->
                  case null e4 of {
                   Prelude.True ->
                    case empty e4 of {
                     Prelude.True -> unprob_rec e1;
                     Prelude.False -> Choice (unprob_rec e1) (unprob_rec e4)};
                   Prelude.False ->
                    case empty e4 of {
                     Prelude.True -> unprob_rec e1;
                     Prelude.False -> Choice (unprob_rec e1) (unprob e4)}}};
               Prelude.False ->
                case empty e1 of {
                 Prelude.True ->
                  case null e4 of {
                   Prelude.True -> unprob_rec e4;
                   Prelude.False -> unprob e4};
                 Prelude.False ->
                  case empty e4 of {
                   Prelude.True -> unprob e1;
                   Prelude.False -> Choice (unprob e1) (unprob_rec e4)}}};
             Choice e1 e4 ->
              case null e1 of {
               Prelude.True ->
                case empty e1 of {
                 Prelude.True ->
                  case null e4 of {
                   Prelude.True -> unprob_rec e4;
                   Prelude.False -> unprob e4};
                 Prelude.False ->
                  case null e4 of {
                   Prelude.True ->
                    case empty e4 of {
                     Prelude.True -> unprob_rec e1;
                     Prelude.False -> Choice (unprob_rec e1) (unprob_rec e4)};
                   Prelude.False ->
                    case empty e4 of {
                     Prelude.True -> unprob_rec e1;
                     Prelude.False -> Choice (unprob_rec e1) (unprob e4)}}};
               Prelude.False ->
                case empty e1 of {
                 Prelude.True ->
                  case null e4 of {
                   Prelude.True -> unprob_rec e4;
                   Prelude.False -> unprob e4};
                 Prelude.False ->
                  case empty e4 of {
                   Prelude.True -> unprob e1;
                   Prelude.False -> Choice (unprob e1) (unprob_rec e4)}}};
             Star e1 ->
              case null e1 of {
               Prelude.True -> unprob_rec e1;
               Prelude.False -> unprob e1};
             _ -> false_rec}}
         in unprob_rec e2)};
     Prelude.False -> Star (unprob e2)};
   x -> x}

data Output =
   Ok Prelude.String Prelude.String Code
 | Error

type Greedy_interp_type = () -> ((,) Prelude.Int Output)

greedy_interp_F :: Input -> (Input -> () -> Greedy_interp_type) ->
                   ((,) Prelude.Int Output)
greedy_interp_F p x =
  case p of {
   ExistT e s ->
    case e of {
     Empty -> (,) 0 Error;
     Eps -> (,) (Prelude.succ 0) (Ok ([]) s ([]));
     Chr a ->
      case s of {
       ([]) -> (,) (Prelude.succ (Prelude.succ 0)) Error;
       (:) a' s' ->
        let {s0 = (Prelude.==) a a'} in
        case s0 of {
         Prelude.True ->
          eq_rec_r a' (\_ _ -> (,) (Prelude.succ (Prelude.succ 0)) (Ok ((:)
            a' ([])) s' ([]))) a x __;
         Prelude.False -> (,) (Prelude.succ (Prelude.succ 0)) Error}};
     Cat e1 e2 ->
      let {iH1 = x (mk_input e1 s) __ __} in
      case iH1 of {
       (,) n1 o1 ->
        case o1 of {
         Ok c1 r1 bs1 ->
          let {iH2 = x (mk_input e2 r1) __ __} in
          case iH2 of {
           (,) n2 o2 ->
            case o2 of {
             Ok c2 r2 bs2 -> (,)
              ((Prelude.+) ((Prelude.+) (Prelude.succ 0) n1) n2) (Ok
              (append c1 c2) r2 (app bs1 bs2));
             Error -> (,) ((Prelude.+) ((Prelude.+) (Prelude.succ 0) n1) n2)
              Error}};
         Error -> (,) ((Prelude.+) (Prelude.succ 0) n1) Error}};
     Choice e1 e2 ->
      let {iH1 = x (mk_input e1 s) __ __} in
      case iH1 of {
       (,) n1 o1 ->
        case o1 of {
         Ok c1 r1 bs1 -> (,) ((Prelude.+) (Prelude.succ 0) n1) (Ok c1 r1 ((:)
          O bs1));
         Error ->
          let {iH2 = x (mk_input e2 s) __ __} in
          case iH2 of {
           (,) n2 o2 ->
            case o2 of {
             Ok c2 r2 bs2 -> (,)
              ((Prelude.+) ((Prelude.+) (Prelude.succ 0) n1) n2) (Ok c2 r2
              ((:) I bs2));
             Error -> (,) ((Prelude.+) ((Prelude.+) (Prelude.succ 0) n1) n2)
              Error}}}};
     Star e0 ->
      let {iHe = x (mk_input e0 s) __ __} in
      case iHe of {
       (,) ne oe ->
        case oe of {
         Ok ce re bse ->
          case ce of {
           ([]) -> false_rec;
           (:) a' s' ->
            eq_rec_r (append ((:) a' s') re)
              (let {iH = eq_rec s x (append ((:) a' s') re)} in
               let {iHes = iH (mk_input (Star e0) re) __ __} in
               case iHes of {
                (,) nes oes ->
                 case oes of {
                  Ok ces res bses -> (,)
                   ((Prelude.+) ((Prelude.+) (Prelude.succ 0) ne) nes) (Ok
                   (append ((:) a' s') ces) res ((:) O (app bse bses)));
                  Error -> false_rec}}) s};
         Error -> (,) ((Prelude.+) (Prelude.succ 0) ne) (Ok ([]) s ((:) I
          ([])))}}}}

greedy_interp :: Regex -> Prelude.String -> ((,) Prelude.Int Output)
greedy_interp e s =
  well_founded_induction (\x x0 _ -> greedy_interp_F x x0) (mk_input e s) __

type Interp_type = Prelude.Maybe Code

interp :: Regex -> Prelude.String -> Interp_type
interp e s =
  let {hu = unprob e} in
  let {hr = greedy_interp hu s} in
  case hr of {
   (,) _ o ->
    case o of {
     Ok _ _ bs -> Prelude.Just bs;
     Error -> Prelude.Nothing}}

