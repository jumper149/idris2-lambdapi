module Main

import Generics.Derive

%language ElabReflection

mutual
  data TermUp = Ann TermDown Typ
              | Bound Nat
              | Free BoundName
              | At TermUp TermDown

  data TermDown = Infer TermUp
                | Lam TermDown

  data Typ = TFree BoundName
           | Fun Typ Typ

  data BoundName = Global String
                 | Local Nat
                 | Quote Nat

  data Value = VLam (Value -> Value)
             | VNeutral Neutral

  data Neutral = NFree BoundName
               | NApp Neutral Value

%runElab deriveMutual
  [ ("TermUp"   , [ Eq, Generic, Meta, Ord, Show ])
  , ("TermDown" , [ Eq, Generic, Meta, Ord, Show ])
  , ("Typ"      , [ Eq, Generic, Meta, Ord, Show ])
  , ("BoundName", [ Eq, Generic, Meta, Ord, Show ])
  ]

vfree : BoundName -> Value
vfree = VNeutral . NFree

vapp : (v : Value) ->
       (v' : Value) ->
       Value
vapp (VLam f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)

mutual
  evalUp : (term : TermUp) ->
           {n : Nat} ->
           (env : Vect n Value) ->
           Value
  evalUp (Ann e _) env = evalDown e env
  evalUp (Bound i) env = case natToFin i n of
    Nothing => ?lookupListErr
    Just i' => index i' env
  evalUp (Free x) env = vfree x
  evalUp (At e e') env = vapp (evalUp e env) (evalDown e' env)

  evalDown : (term : TermDown) ->
             {n : Nat} ->
             (env : Vect n Value) ->
             Value
  evalDown (Infer i) env = evalUp i env
  evalDown (Lam e) env = VLam $ \ x => evalDown e $ x :: env

data Kind = Star
%runElab derive "Kind" [ Eq, Generic, Meta, Ord, Show ]

data Info = HasKind Kind
          | HasType Typ
%runElab derive "Info" [ Eq, Generic, Meta, Ord, Show ]

kindDown : (context : List (BoundName, Info)) ->
           (type : Typ) ->
           (kind : Kind) ->
           Either String ()
kindDown context (TFree x) Star = case lookup x context of
  Just (HasKind Star) => Right ()
  Just (HasType _) => Left "unexpected type"
  Nothing => Left "unknown identifier"
kindDown context (Fun k k') Star = do
  kindDown context k Star
  kindDown context k' Star

mutual
  substUp : (n : Nat) ->
            (term1 : TermUp) ->
            (term2 : TermUp) ->
            TermUp
  substUp n term1 (Ann e t) = Ann (substDown n term1 e) t
  substUp n term1 (Bound i) = if n == i then term1 else Bound i
  substUp n term1 (Free x) = Free x
  substUp n term1 (At e e') = substUp n term1 e `At` substDown n term1 e'

  substDown : (n : Nat) ->
              (term1 : TermUp) ->
              (term2 : TermDown) ->
              TermDown
  substDown n term1 (Infer e) = Infer $ substUp n term1 e
  substDown n term1 (Lam e) = Lam $ substDown (S n) term1 e

mutual
  quote : (n : Nat) ->
          (v : Value) ->
          TermDown
  quote n (VLam f) = Lam $ quote (S n) (f (vfree (Quote n)))
  quote n (VNeutral x) = Infer $ neutralQuote n x

  neutralQuote : Nat -> Neutral -> TermUp
  neutralQuote i (NFree x) = case x of
    Quote k => Bound ((i `minus` k) `minus` 1)
    _ => Free x
  neutralQuote i (NApp n v) = neutralQuote i n `At` quote i v

quote0 : Value -> TermDown
quote0 = quote 0

mutual
  typeUp : (n : Nat) ->
           (context : List (BoundName, Info)) ->
           (term : TermUp) ->
           Either String Typ
  typeUp n context (Ann e t) = do
    kindDown context t Star
    typeDown n context e t
    Right t
  typeUp n context (Bound i) = ?inferTypeErr
  typeUp n context (Free x) = case lookup x context of
    Nothing => Left "unknown identifier"
    Just (HasKind Star) => Left "unexpected kind"
    Just (HasType t) => Right t
  typeUp n context (At e e') = do
    sigma <- typeUp n context e
    case sigma of
         Fun t t' => do
           typeDown n context e' t
           Right t'
         _ => Left "illegal application"

  typeDown : (n : Nat) ->
             (context : List (BoundName, Info)) ->
             (term : TermDown) ->
             (t : Typ) ->
             Either String ()
  typeDown n context (Infer e) t = do
    t' <- typeUp n context e
    unless (t == t') $ Left "type mismatch"
  typeDown n context (Lam e) (Fun t t') =
    typeDown (S n) ((Local n, HasType t) :: context)
                   (substDown 0 (Free (Local n)) e) t'
  typeDown n context (Lam _) (TFree _) = Left "type mismatch"


typeUp0 : (context : List (BoundName, Info)) ->
          (term : TermUp) ->
          Either String Typ
typeUp0 = typeUp 0

main : IO ()
main = do
  let id' = Lam (Infer (Bound 0))
  let const' = Lam (Lam (Infer (Bound 1)))
  let tfree = \ a => TFree (Global a)
  let free = \ x => Infer (Free (Global x))
  let term1 = Ann id' (Fun (tfree "a") (tfree "a")) `At` free "y"
  let term2 = (Ann const' (Fun (Fun (tfree "b") (tfree "b"))
                          (Fun (tfree "a")
                               (Fun (tfree "b") (tfree "b"))))
                `At` id') `At` free "y"
  let env1 = [ (Global "y", HasType (tfree "a"))
             , (Global "a", HasKind Star)
             ]
  let env2 = (Global "b", HasKind Star) :: env1
  printLn $ quote0 (evalUp term1 [])
  printLn $ quote0 (evalUp term2 [])
  printLn $ typeUp0 env1 term1
  printLn $ typeUp0 env2 term2
  pure ()
