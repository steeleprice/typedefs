module Backend.Haskell

import Types
import Typedefs

import Backend
import Backend.Utils

import Text.PrettyPrint.WL
import Control.Monad.State

import Data.Vect

%default total
%access public export

||| The syntactic structure of Haskell types.
data HsType : Type where -- TODO could be interesting to index this by e.g. used variable names?
  ||| The `Void` (i.e. empty) type.
  HsVoid  :                                HsType

  ||| The `()` (i.e. unit/singleton) type.
  HsUnit  :                                HsType

  ||| The tuple type, containing two or more further types.
  HsTuple :         Vect (2 + n) HsType -> HsType

  ||| A type variable.
  HsVar   :         Name                -> HsType

  ||| A named type with zero or more other types as parameters.
  HsParam : Name -> Vect n HsType       -> HsType

||| The syntactic structure of Haskell type declarations.
data Haskell : Type where
  ||| A type synonym is a declared name (possibly with parameters) and a type.
  Synonym : Decl -> HsType                -> Haskell

  ||| An algebraic data type is a declared name (possibly with parameters)
  ||| and a number of constructors, each wrapping a Haskell type.
  ADT     : Decl -> Vect n (Name, HsType) -> Haskell

||| Render a name applied to a list of arguments exactly as written.
||| Arguments need to be previously parenthesized, if applicable.
renderApp : Name -> Vect n Doc -> Doc
renderApp name params = text (uppercase name) |+| hsep (empty :: toList params)

mutual
  ||| Render a type signature as Haskell source code.
  renderType : HsType -> Doc
  renderType HsVoid                = text "Void"
  renderType HsUnit                = text "()"
  renderType (HsTuple xs)          = tupled . toList . map (assert_total renderType) $ xs
  renderType (HsVar v)             = text (lowercase v)
  renderType (HsParam name params) = renderApp name (map guardParen params)

  ||| As `renderType`, but with enclosing top-level parentheses
  ||| if it can possibly make a semantic difference.
  guardParen : HsType -> Doc
  guardParen t@(HsParam _ []) = assert_total $ renderType t
  guardParen t@(HsParam _ _ ) = parens (assert_total $ renderType t)
  guardParen t                = assert_total $ renderType t

||| Helper function to render a top-level declaration as source code.
renderDecl : Decl -> Doc
renderDecl decl = renderApp (name decl) (map (text . lowercase) (params decl))

||| Render a type definition as Haskell source code.
renderDef : Haskell -> Doc
renderDef (Synonym decl body)  = text "type" |++| renderDecl decl
                                 |++| equals |++| renderType body
renderDef (ADT     decl cases) = text "data" |++| renderDecl decl
                                 |++| equals |++| hsep (punctuate (text " |")
                                                       (toList $ map renderConstructor cases))
  where
  renderConstructor : (Name, HsType) -> Doc
  renderConstructor (name, HsUnit)     = renderApp name []
  renderConstructor (name, HsTuple ts) = renderApp name (map guardParen ts)
  renderConstructor (name, params)     = renderApp name [guardParen params]

anonMu : Vect n (Name, a) -> Name
anonMu = concatMap (uppercase . fst)

HEnv : Nat -> Type
HEnv n = Vect n (Maybe Decl)

HsEnv : Nat -> Type
HsEnv n = Vect n (Either (m ** TDef m) Decl)


WEnv : (free : Nat) -> (n : Nat) -> Type
WEnv free n = Vect n (Either Name Decl)

--data XEnv : (free : Nat) -> (n : Nat) -> Type where
--  Nil       :                        XEnv 0        0
--  consFree  : Name -> XEnv free n -> XEnv (S free) (S n)
--  consBound : Decl -> XEnv free n -> XEnv free     (S n)
--
--map : (a -> Either Name Decl) -> Vect len a -> XEnv free len
--map _ [] = Nil
--map f (a::as) = (either consFree consBound (f a)) (map f as) 

freshWEnv : (n : Nat) -> WEnv n n -- {p=lteRefl}
freshWEnv n = map (\i => Left $ "x" ++ show (finToNat i)) range

(::) : Decl -> WEnv free n -> WEnv free (S n) -- {p=lteSuccRight p}
(::) decl e = Right decl :: e

prf : LTE n1 m1 -> LTE n2 m2 -> LTE (n1 + n2) (m1 + m2)
prf {n1=Z}   {n2=Z}                 _  _  = LTEZero
prf {n1=Z}   {n2=S _} {m1}     {m2} _  p2 = lteTransitive p2 (rewrite plusCommutative m1 m2 in lteAddRight _)
prf {n1=S _}          {m1=S _}      p1 p2 = LTESucc $ prf (fromLteSucc p1) p2

(++) : WEnv free1 n1 -> WEnv free2 n2 -> WEnv (free1 + free2) (n1 + n2) -- {p=prf p1 p2}
(++) e1 e2 = Data.Vect.(++) e1 e2

||| Filter out the entries in an `Env` that is referred to by a `TDef`.
getUsedVars : HEnv n -> (td: TDef n) -> HEnv (length (getUsedIndices td))
getUsedVars e td = map (flip index e) (fromList $ getUsedIndices td)

||| Get the free names from the environment.
getFreeVars : (e : HEnv n) -> Vect (fst (Vect.filter Maybe.isNothing e)) String
getFreeVars _ = map (\i => "x" ++ show (finToNat i)) range

||| Generate a Haskell type from a `TDef`.
makeType : Env n -> TDef n -> HsType
makeType _ T0             = HsVoid
makeType _ T1             = HsUnit
makeType e (TSum xs)      = foldr1' (\t1,t2 => HsParam "Either" [t1, t2]) (map (assert_total $ makeType e) xs)
makeType e (TProd xs)     = HsTuple $ map (assert_total $ makeType e) xs
makeType e (TVar v)       = either HsVar hsParam $ Vect.index v e
  where
  hsParam : Decl -> HsType
  hsParam (MkDecl n ps) = HsParam n (map HsVar ps)
makeType e td@(TMu cases) = HsParam (anonMu cases) . map HsVar $ getFreeVars (getUsedVars e td)
makeType e (TApp f xs)    = HsParam (name f) (map (assert_total $ makeType e) xs)

makeType' : Env n -> TNamed n -> HsType
makeType' e (TName name body) = HsParam name . map HsVar $ getFreeVars (getUsedVars e body)

--tdefToMaybeDecl : HsEnv n -> TDef n -> Either (m ** TDef m) Decl
--tdefToMaybeDecl e (TVar v)  = index v e
--tdefToMaybeDecl {n} e (TSum xs) = Left (n ** TSum (map (tdefToMaybeDecl e) xs)) 

isFree : Fin n -> Env n -> Bool
isFree ix e = isLeft $ index ix e

fff : Env n -> (Fin k, TDef n) -> Either String Decl
fff e (_,  TVar v) = index v e
fff _ (ix, _)      = Left ("y" ++ show (finToNat ix))

mutual
  ||| Generate Haskell type definitions from a `TDef`, including all of its dependencies.
  makeDefs : Env n -> TDef n -> State (List Name) (List Haskell)
  makeDefs _ T0            = pure []
  makeDefs _ T1            = pure []
  makeDefs e (TProd xs)    = map concat $ traverse (assert_total $ makeDefs e) xs
  makeDefs e (TSum xs)     = map concat $ traverse (assert_total $ makeDefs e) xs
  makeDefs _ (TVar v)      = pure []
  makeDefs e (TApp f xs) = do
      res <- assert_total $ makeDefs' (map (fff e) $ zip range xs) f
      res' <- concat <$> traverse (assert_total $ makeDefs e) xs
      pure (res ++ res')
  makeDefs e td@(TMu cases) = makeDefs' e $ TName (anonMu cases) td -- We name anonymous mus using their constructors.

  makeDefs' : Env n -> TNamed n -> State (List Name) (List Haskell)
  makeDefs' e (TName name body) = do
      st <- get
      if List.elem name st then pure []
      else do
        let decl = MkDecl name (getFreeVars $ getUsedVars e body)
        put (name :: st)
        case body of
          TMu cases => do -- Named `TMu`s are treated as ADTs.
            let newEnv = Right decl :: e
            let args = map (map (makeType newEnv)) cases
            res <- map concat $ traverse {b=List Haskell} (\(_, bdy) => assert_total $ makeDefs newEnv bdy) (toList cases)
            pure $ ADT decl args :: res
          _         => do -- All other named types are treated as synonyms.
            res <- assert_total $ makeDefs e body
            pure $ Synonym decl (makeType e body) :: res

Backend Haskell where
  generateTyDefs e td = reverse $ evalState (makeDefs e td) []
  generateCode        = renderDef
  freshEnv            = freshEnvLC

NewBackend Haskell HsType where
  msgType          = makeType []
  typedefs td      = reverse $ evalState (makeDefs (freshWEnv 0) td) []
  source type defs = vsep2 $ map renderDef $ Synonym (MkDecl "TypedefSchema" []) type :: defs 

--||| Generate type body, only useful for anonymous tdefs (i.e. without wrapping Mu/Name)
--generateType : TDef n -> Doc
--generateType {n} = renderType . makeType (freshWEnv n)--(freshEnv {lang=Haskell} n)
