module Main

import Generics.Derive

%language ElabReflection

mutual
  data TermInferable = Ann TermCheckable TermCheckable
                     | Star
                     | Pi TermCheckable TermCheckable
                     | Bound Nat
                     | Free Reference
                     | At TermInferable TermCheckable

  data TermCheckable = Infer TermInferable
                     | Lam TermCheckable

  data Reference = Global String
                 | Local Nat
                 | Quote Nat

  data Value = VLam (Value -> Value)
             | VStar
             | VPi Value (Value -> Value)
             | VNeutral Neutral

  data Neutral = NFree Reference
               | NApp Neutral Value

%runElab deriveMutual
  [ ("TermInferable" , [ Eq, Generic, Meta, Ord, Show ])
  , ("TermCheckable", [ Eq, Generic, Meta, Ord, Show ])
  , ("Reference", [ Eq, Generic, Meta, Ord, Show ])
  ]

vfree : Reference -> Value
vfree = VNeutral . NFree

vapp : (v : Value) ->
       (v' : Value) ->
       Value
vapp (VLam f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)
vapp _ _ = ?impossibleVapp

mutual
  evalInferable : (term : TermInferable) ->
                  (env : List Value) ->
                  Value
  evalInferable (Ann e _) env = evalCheckable e env
  evalInferable Star env = VStar
  evalInferable (Pi t t') env = VPi (evalCheckable t env) (\ x => evalCheckable t' (x :: env))
  evalInferable (Bound i) env = case natToFin i (length env) of
    Nothing => ?lookupListErr
    Just i' => index' env i'
  evalInferable (Free x) env = vfree x
  evalInferable (At e e') env = vapp (evalInferable e env) (evalCheckable e' env)

  evalCheckable : (term : TermCheckable) ->
                  (env : List Value) ->
                  Value
  evalCheckable (Infer i) env = evalInferable i env
  evalCheckable (Lam e) env = VLam $ \ x => evalCheckable e $ x :: env

mutual
  substUp : (n : Nat) ->
            (term1 : TermInferable) ->
            (term2 : TermInferable) ->
            TermInferable
  substUp n term1 (Ann e t) = Ann (substDown n term1 e) (substDown n term1 t)
  substUp n term1 Star = Star
  substUp n term1 (Pi t t') = Pi (substDown n term1 t) (substDown (S n) term1 t')
  substUp n term1 (Bound i) = if n == i then term1 else Bound i
  substUp n term1 (Free x) = Free x
  substUp n term1 (At e e') = substUp n term1 e `At` substDown n term1 e'

  substDown : (n : Nat) ->
              (term1 : TermInferable) ->
              (term2 : TermCheckable) ->
              TermCheckable
  substDown n term1 (Infer e) = Infer $ substUp n term1 e
  substDown n term1 (Lam e) = Lam $ substDown (S n) term1 e

mutual
  quote : (n : Nat) ->
          (v : Value) ->
          TermCheckable
  quote n (VLam f) = Lam $ quote (S n) (f (vfree (Quote n)))
  quote n (VNeutral x) = Infer $ neutralQuote n x
  quote n VStar = Infer Star
  quote n (VPi x f) = Infer $ Pi (quote n x) (quote (S n) $ f $ vfree $ Quote n)

  neutralQuote : Nat -> Neutral -> TermInferable
  neutralQuote i (NFree x) = case x of
    Quote k => Bound ((i `minus` k) `minus` 1)
    _ => Free x
  neutralQuote i (NApp n v) = neutralQuote i n `At` quote i v

quote0 : Value -> TermCheckable
quote0 = quote 0

mutual
  typeUp : (n : Nat) ->
           (context : List (Reference, Value)) ->
           (term : TermInferable) ->
           Either String Value
  typeUp n context (Ann e p) = do
    typeDown n context p VStar
    let t = evalCheckable p []
    typeDown n context e t
    Right t
  typeUp n context Star = Right VStar
  typeUp n context (Pi p p') = do
    typeDown n context p VStar
    let t = evalCheckable p []
    typeDown (S n) ((Local n, t) :: context)
                   (substDown 0 (Free (Local n)) p') VStar
    Right VStar
  typeUp n context (Bound i) = ?inferTypeErr
  typeUp n context (Free x) = case lookup x context of
    Nothing => Left "unknown identifier"
    Just t => Right t
  typeUp n context (At e e') = do
    sigma <- typeUp n context e
    case sigma of
         VPi t t' => do
           typeDown n context e' t
           Right (t' (evalCheckable e' []))
         _ => Left "illegal application"

  typeDown : (n : Nat) ->
             (context : List (Reference, Value)) ->
             (term : TermCheckable) ->
             (t : Value) ->
             Either String ()
  typeDown n context (Infer e) t = do
    t' <- typeUp n context e
    unless (quote0 t == quote0 t') $ Left "type mismatch1"
  typeDown n context (Lam e) (VPi t t') =
    typeDown (S n) ((Local n, t) :: context)
                   (substDown 0 (Free (Local n)) e) (t' (vfree (Local n)))
  typeDown n context _ _ = Left "type mismatch2"


typeUp0 : (context : List (Reference, Value)) ->
          (term : TermInferable) ->
          Either String Value
typeUp0 = typeUp 0

main : IO ()
main = do
  let env1 = [ (Global "a", VStar)
             , (Global "b", VStar)
             ]

  let id' = Lam (Infer (Bound 0))
  let idType' = Infer (Pi (Infer Star) (Infer Star))
  let idType1' = Infer (Pi (Infer (Free (Global "a"))) (Infer (Free (Global "a"))))
  printLn $ map quote0 $ typeUp0 [] $ Ann id' idType'
  printLn $ map quote0 $ typeUp0 env1 $ Ann id' idType1'

  let const' = Lam (Lam (Infer (Bound 1)))
  let constType' = Infer (Pi (Infer Star) (Infer (Pi (Infer Star) (Infer Star))))
  let constType1' = Infer (Pi (Infer (Free (Global "a"))) (Infer (Pi (Infer (Free (Global "b"))) (Infer (Free (Global "a"))))))
  printLn $ map quote0 $ typeUp0 [] $ Ann const' constType'
  printLn $ map quote0 $ typeUp0 env1 $ Ann const' constType1'

  let idDependent = Lam (Lam (Infer (Bound 0)))
  let idDependentType =
    Infer (Pi (Infer Star)
              (Infer (Pi (Infer $ Free $ Local 0)
                         (Infer $ Free $ Local 0)
                     )
              )
          )
  printLn $ map quote0 $ typeUp0 env1 $ Ann idDependent idDependentType
  printLn $ quote0 $ evalInferable (((Ann idDependent idDependentType) `At` Infer Star) `At` Infer Star) []
  pure ()
