module Typedefs.Backend

import Data.Vect
import Data.NEList

import Typedefs.Names
import Typedefs.Typedefs
import Typedefs.Backend.Utils

import Text.PrettyPrint.WL

%default total
%access public export


--TODO added to TParsec
Traversable NEList where
  traverse f (MkNEList x xs) = [| MkNEList (f x) (traverse f xs) |]

data ZeroOrUnbounded : (Nat -> Type) -> Bool -> Type where
  Unbounded : p n -> ZeroOrUnbounded p True
  Zero : p Z -> ZeroOrUnbounded p False

fromSigma : {p : Nat -> Type} -> (b : Bool) -> (n ** p n) -> Maybe (ZeroOrUnbounded p b)
fromSigma True  (n  **pn) = Just $ Unbounded $ pn
fromSigma False (Z  **pz) = Just $ Zero $ pz
fromSigma False (S _** _) = Nothing

||| Interface for interpreting type definitions as ASTs.
||| @def      the type representing definitions.
||| @type     the type representing types.
||| @freeVars flag controlling if type definition can have free variables.
interface ASTGen def type (freeVars : Bool) | def where
  ||| Given a list of `TNamed`, generate their corresponding type signatures.
  msgType          : ZeroOrUnbounded TNamed freeVars          -> Either CompilerError type

  ||| Generate definitions for a list of `TNamed`.
  generateTyDefs   : NEList (ZeroOrUnbounded TNamed freeVars) -> Either CompilerError (List def)

  ||| Generate serialisation and deserialisation term definitions for a
  ||| a `TNamed` and all its helper definitions.
  generateTermDefs : NEList (ZeroOrUnbounded TNamed freeVars) -> Either CompilerError (List def)

||| Interface for code generators that can generate code for type definitions and
||| type signatures independently of each other, for example Haskell and ReasonML.
||| @def  the type representing definitions.
||| @type the type representing types.
interface CodegenIndep def type | def where
  ||| Generate source code for a type signature.
  typeSource : type -> Doc

  ||| Generate source code for a type definition.
  defSource  : def -> Doc

  ||| A common preamble that code generated by `typeSource` and
  ||| `defSource` may use.
  preamble : Doc

||| Use the given backend to generate code for a list of type definitions.
generateDefs : (def : Type) -> (ASTGen def type fv, CodegenIndep def type) => NEList (n ** TNamed n) -> Maybe Doc
generateDefs {fv} def tns = 
  -- (\nel => 
  --   vsep2 $ 
  --     (preamble {def}) ::
  --     (defSource <$> 
  --      (generateTyDefs {def} nel ++ generateTermDefs {def} nel))
  -- ) 
  ?generateDefsrhs<$> (traverse (fromSigma fv) tns)

||| Use the given backend to generate code for a list of type signatures.
generateType : (def : Type) -> (ASTGen def type fv, CodegenIndep def type) => NEList (n ** TNamed n) -> Maybe Doc
generateType {fv} def tns = 
  -- (concatMap (typeSource {def} . msgType {def})) 
  ?generateTypeRhs <$> (traverse (fromSigma fv) tns)

||| Interface for code generators that need to generate code for type definitions and
||| type signatures at the same time, for example the JSON schema backend.
||| @def  the type representing type definitions.
||| @type the type representing type signatures.
interface CodegenInterdep def type where
  ||| Generate source code for a type signature and a list of helper definitions.
  sourceCode   : NEList type -> List def -> Doc

||| Use the given backend to generate code for a list of type definitions.
generate : (def : Type) -> (ASTGen def type fv, CodegenInterdep def type) => NEList (n ** TNamed n) -> Maybe Doc
generate {fv} def tns = 
  -- (\nel => 
  --   sourceCode 
  --    ((msgType {def}) <$> nel)
  --    (generateTyDefs {def} nel ++ generateTermDefs {def} nel)
  -- ) 
  ?generateRhs <$> (traverse (fromSigma fv) tns)

{-
record SpecialiseEntry where
  constructor MkSpecialiseEntry
  tdef : TDef 0
  ||| name of type used for specialisation
  targetType : String
  ||| name of function of target type generateType tdef -> targetType
  encodeFun : String
  ||| name of function of target type targetType -> generateType tdef
  decodeFun : String

||| Generate type definitions according to an *ordered* set of specialisation entries.
generateDefsSpecialised : Backend lang => Vect (S m') SpecialiseEntry -> (n : Nat) -> TDef n -> List lang
generateDefsSpecialised {lang} {m' = m'} table n td = generateTyDefs e td'
   where m : Nat
         m = S m'
         e : Env (n + m)
         e = freshEnv {lang} n ++ map (\ s => Right $ MkDecl (targetType s) []) table
         traverseTD : (n : Nat) -> (Fin m, SpecialiseEntry) -> TDef (n + m) -> TDef (n + m)
         traverseTD n (i, se) t = if t == weakenTDef (tdef se) _ (lteAddRight 0)
                                    then replace prf (TVar (fromNat (n + toNat i)))
                                    else go t
             where prf : m + n = n + m
                   prf = plusCommutative m n
                   go : TDef (n + m) -> TDef (n + m)
                   go T0 = T0
                   go T1 = T1
                   go (TSum xs)  = TSum (assert_total $ map (traverseTD n (i, se)) xs)
                   go (TProd xs) = TProd (assert_total $ map (traverseTD n (i, se)) xs)
                   go (TMu xs)   = TMu (assert_total $ map (\(c, t) => (c,traverseTD (S n) (i, se) t)) xs)
                   --go (TName name t) = TName name (traverseTD n (i, se) t)
                   go (TApp f xs) = ?goTApp
                   go x = x -- only TVar i case left
         td' : TDef (n + m)
         td' = foldl (flip (traverseTD n)) (weakenTDef td (n + m) (lteAddRight n)) (zip range table)
-}
