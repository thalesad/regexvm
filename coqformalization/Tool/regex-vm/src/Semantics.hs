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

data Maybe a p =
   Unknown
 | Found a p

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

data Result0 =
   Result Code Prelude.String Prelude.String

bitcode :: Result0 -> Code
bitcode r =
  case r of {
   Result bitcode0 _ _ -> bitcode0}

consumed :: Result0 -> Prelude.String
consumed r =
  case r of {
   Result _ consumed0 _ -> consumed0}

remaining :: Result0 -> Prelude.String
remaining r =
  case r of {
   Result _ _ remaining0 -> remaining0}

type Valid_result = Maybe Result0 ()

type Interp_type = () -> Valid_result

interp_F :: Input -> (Input -> () -> Interp_type) -> Valid_result
interp_F p x =
  case p of {
   ExistT e s ->
    case e of {
     Empty -> Unknown;
     Eps -> Found (Result ([]) ([]) s) __;
     Chr a' ->
      case s of {
       ([]) -> Unknown;
       (:) a s1 ->
        case (Prelude.==) a a' of {
         Prelude.True -> Found (Result ([]) ((:) a' ([])) s1) __;
         Prelude.False -> Unknown}};
     Cat e1 e2 ->
      case x (mk_input e1 s) __ __ of {
       Unknown -> Unknown;
       Found r1 _ ->
        case x (mk_input e2 (remaining r1)) __ __ of {
         Unknown -> Unknown;
         Found r2 _ -> Found (Result (app (bitcode r1) (bitcode r2))
          (append (consumed r1) (consumed r2)) (remaining r2)) __}};
     Choice e1 e2 ->
      case x (mk_input e1 s) __ __ of {
       Unknown ->
        case x (mk_input e2 s) __ __ of {
         Unknown -> Unknown;
         Found r1 _ -> Found (Result ((:) I (bitcode r1)) (consumed r1)
          (remaining r1)) __};
       Found r1 _ -> Found (Result ((:) O (bitcode r1)) (consumed r1)
        (remaining r1)) __};
     Star e1 ->
      case s of {
       ([]) -> Found (Result ((:) I ([])) ([]) ([])) __;
       (:) _ _ ->
        case x (mk_input e1 s) __ __ of {
         Unknown -> Found (Result ((:) I ([])) ([]) s) __;
         Found r1 _ ->
          case (Prelude.==) (remaining r1) ([]) of {
           Prelude.True -> Found (Result ((:) O
            (app (bitcode r1) ((:) I ([])))) (consumed r1) ([])) __;
           Prelude.False ->
            case x (mk_input (Star e1) (remaining r1)) __ __ of {
             Unknown -> Found (Result ((:) O (app (bitcode r1) ((:) I ([]))))
              (consumed r1) (remaining r1)) __;
             Found r2 _ -> Found (Result ((:) O
              (app (bitcode r1) (bitcode r2)))
              (append (consumed r1) (consumed r2)) (remaining r2)) __}}}}}}

interp' :: Input -> Valid_result
interp' p =
  well_founded_induction (\x x0 _ -> interp_F x x0) p __

interp :: Regex -> Prelude.String -> Maybe Result0 ()
interp e s =
  let {j = unprob e} in
  let {j0 = interp' (mk_input j s)} in
  case j0 of {
   Unknown -> Unknown;
   Found r _ -> Found r __}

