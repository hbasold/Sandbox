{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleContexts,
  UndecidableInstances, FlexibleInstances, TypeFamilies #-}
module FibDT where

{-
import Prelude hiding (id, (.), Functor(..))
import Control.Category
import Control.Categorical.Functor
-}

data NonEmpty a = NonEmpty {
  neHead :: a,
  neTail :: [a]
} deriving (Eq, Ord)

(|:) :: a -> [a] -> NonEmpty a
(|:) = NonEmpty

neSingle :: a -> NonEmpty a
neSingle x = x |: []

data Index = T | Compr Type deriving Show

data IndexMor
    = Id Index
    | ComprM Term
      deriving Show

data Type
    = IDT SigFunctor ReidxFunctor
    | CDT ReidxFunctor SigFunctor
    | App SigFunctor (NonEmpty Type)

instance Show Type where
    show (IDT f g) = "μ(" ++ show f ++ ", " ++ show g ++ ")"
    show (CDT g f) = "ν(" ++ show g ++ ", " ++ show f ++ ")"

newtype ReidxFunctor = RF (NonEmpty IndexMor)

instance Show ReidxFunctor where
    show (RF l) =
        if null (neTail l)
        then show (neHead l)
        else "<" ++ show (neHead l) ++ ", " ++ show (neTail l) ++ ">"

-- F : C × P_i → D
data SigFunctor
    = Const Type
    | ProjParam
    | ProjRecVar
    | Reidx IndexMor
    | Comp SigFunctor SigFunctor
    | Pair SigFunctor SigFunctor
    | Lfp SigFunctor ReidxFunctor
    | Gfp ReidxFunctor SigFunctor

instance Show SigFunctor where
    show (Const t) = "K(" ++ show t ++ ")"
    show ProjParam = "π₁"
    show ProjRecVar = "π2"
    show (Reidx u) = "(" ++ show u ++ ")*"
    show (Comp f2 f1) = "(" ++ show f2 ++ ") o (" ++ show f1 ++ ")"
    show (Pair f1 f2) = "<" ++ show f1 ++ ", " ++ show f2 ++ ">"
    show (Lfp f g) = "μ^(" ++ show f ++ ", " ++ show g ++ ")"
    show (Gfp g f) = "ν^(" ++ show g ++ ", " ++ show f ++ ")"

data Term
    = IdT Type
    | CompT Term Term
    | In Type Int
    | Out Type Int
    | Rec Type [Term]
    | Corec Type [Term]
      deriving Show

-- Examples
terminal :: Index -> Type
terminal i = CDT (RF $ Id i |: []) ProjRecVar

nat :: Type
nat = IDT (Pair (Const $ terminal T) ProjRecVar) (RF $ (Id T) |: [Id T])

z,s :: Term
z = In nat 1
s = In nat 2

streams :: SigFunctor
streams = Gfp  (RF $ (Id T) |: [Id T]) (Pair ProjParam ProjRecVar)

ones :: Term
ones =
    Corec (App streams (neSingle nat))
          [CompT s z, IdT $ terminal T]
