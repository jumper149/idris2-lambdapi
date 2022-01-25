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

  data TermCheckable = Inferred TermInferable
                     | Lambda TermCheckable

  data Reference = Global String
                 | Local Nat
                 | Quote Nat

  data Value = VLambda (Value -> Value)
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
    where vapp : (v : Value) -> (v' : Value) -> Value
          vapp (VLambda f) v = f v
          vapp (VNeutral n) v = VNeutral (NApp n v)
          vapp _ _ = ?impossibleVapp
  evalCheckable : (term : TermCheckable) ->
                  (env : List Value) ->
                  Value
  evalCheckable (Inferred i) env = evalInferable i env
  evalCheckable (Lambda e) env = VLambda $ \ x => evalCheckable e $ x :: env

mutual
  substInferable : (n : Nat) ->
                   (term1 : TermInferable) ->
                   (term2 : TermInferable) ->
                   TermInferable
  substInferable n term1 (Ann e t) = Ann (substCheckable n term1 e) (substCheckable n term1 t)
  substInferable n term1 Star = Star
  substInferable n term1 (Pi t t') = Pi (substCheckable n term1 t) (substCheckable (S n) term1 t')
  substInferable n term1 (Bound i) = if n == i then term1 else Bound i
  substInferable n term1 (Free x) = Free x
  substInferable n term1 (At e e') = substInferable n term1 e `At` substCheckable n term1 e'

  substCheckable : (n : Nat) ->
                   (term1 : TermInferable) ->
                   (term2 : TermCheckable) ->
                   TermCheckable
  substCheckable n term1 (Inferred e) = Inferred $ substInferable n term1 e
  substCheckable n term1 (Lambda e) = Lambda $ substCheckable (S n) term1 e

mutual
  quote : (n : Nat) ->
          (v : Value) ->
          TermCheckable
  quote n (VLambda f) = Lambda $ quote (S n) (f (vfree (Quote n)))
  quote n (VNeutral x) = Inferred $ neutralQuote n x
  quote n VStar = Inferred Star
  quote n (VPi x f) = Inferred $ Pi (quote n x) (quote (S n) $ f $ vfree $ Quote n)

  neutralQuote : Nat -> Neutral -> TermInferable
  neutralQuote i (NFree x) = case x of
    Quote k => Bound ((i `minus` k) `minus` 1)
    _ => Free x
  neutralQuote i (NApp n v) = neutralQuote i n `At` quote i v

quote0 : Value -> TermCheckable
quote0 = quote 0

mutual
  typeInferable : (n : Nat) ->
                  (context : List (Reference, Value)) ->
                  (term : TermInferable) ->
                  Either String Value
  typeInferable n context (Ann e p) = do
    typeCheckable n context p VStar
    let t = evalCheckable p []
    typeCheckable n context e t
    Right t
  typeInferable n context Star = Right VStar
  typeInferable n context (Pi p p') = do
    typeCheckable n context p VStar
    let t = evalCheckable p []
    typeCheckable (S n) ((Local n, t) :: context)
                   (substCheckable 0 (Free (Local n)) p') VStar
    Right VStar
  typeInferable n context (Bound i) = ?inferTypeErr
  typeInferable n context (Free x) = case lookup x context of
    Nothing => Left "unknown identifier"
    Just t => Right t
  typeInferable n context (At e e') = do
    sigma <- typeInferable n context e
    case sigma of
         VPi t t' => do
           typeCheckable n context e' t
           Right (t' (evalCheckable e' []))
         _ => Left "illegal application"

  typeCheckable : (n : Nat) ->
                  (context : List (Reference, Value)) ->
                  (term : TermCheckable) ->
                  (t : Value) ->
                  Either String ()
  typeCheckable n context (Inferred e) t = do
    t' <- typeInferable n context e
    unless (quote0 t == quote0 t') $ Left "type mismatch1"
  typeCheckable n context (Lambda e) (VPi t t') =
    typeCheckable (S n) ((Local n, t) :: context)
                   (substCheckable 0 (Free (Local n)) e) (t' (vfree (Local n)))
  typeCheckable n context _ _ = Left "type mismatch2"


typeInferable0 : (context : List (Reference, Value)) ->
                 (term : TermInferable) ->
                 Either String Value
typeInferable0 = typeInferable 0

main : IO ()
main = do
  let env1 = [ (Global "a", VStar)
             , (Global "b", VStar)
             ]

  let id' = Lambda (Inferred (Bound 0))
  let idType' = Inferred (Pi (Inferred Star) (Inferred Star))
  let idType1' = Inferred (Pi (Inferred (Free (Global "a"))) (Inferred (Free (Global "a"))))
  printLn $ map quote0 $ typeInferable0 [] $ Ann id' idType'
  printLn $ map quote0 $ typeInferable0 env1 $ Ann id' idType1'

  let const' = Lambda (Lambda (Inferred (Bound 1)))
  let constType' = Inferred (Pi (Inferred Star) (Inferred (Pi (Inferred Star) (Inferred Star))))
  let constType1' = Inferred (Pi (Inferred (Free (Global "a"))) (Inferred (Pi (Inferred (Free (Global "b"))) (Inferred (Free (Global "a"))))))
  printLn $ map quote0 $ typeInferable0 [] $ Ann const' constType'
  printLn $ map quote0 $ typeInferable0 env1 $ Ann const' constType1'

  let idDependent = Lambda (Lambda (Inferred (Bound 0)))
  let idDependentType =
    Inferred (Pi (Inferred Star)
              (Inferred (Pi (Inferred $ Free $ Local 0)
                         (Inferred $ Free $ Local 0)
                     )
              )
          )
  printLn $ map quote0 $ typeInferable0 env1 $ Ann idDependent idDependentType
  printLn $ quote0 $ evalInferable (((Ann idDependent idDependentType) `At` Inferred Star) `At` Inferred Star) []
  pure ()
