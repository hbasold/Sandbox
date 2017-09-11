{-# LANGUAGE
  MultiParamTypeClasses,
  FlexibleInstances,
  FlexibleContexts,
  UndecidableInstances,
  GADTs,
  FunctionalDependencies,
  RankNTypes #-}

data Empty
data New e t

class Env e where
instance Env Empty where
instance Env e => Env (New e t) where

data X0 t = V0
data Succ v t = VS v t

class Env e => Var e v t where
instance Env e => Var (New e t) (X0 t) t where
instance (Env e, Var e v t_) => Var (New e t) (Succ v t) t where

data VT v
data Sum a b
data Lfp a
data Prod a b
data Gfp a

-- | Unit type
data U = U

class Env e => Type e t
instance (Env e, Var e v U)          => Type e (VT v)
instance (Env e, Type e a, Type e b) => Type e (Sum a b)
instance (Env e, Type (New e U) a)   => Type e (Lfp a)
instance (Env e, Type e a, Type e b) => Type e (Prod a b)
instance (Env e, Type (New e U) a)   => Type e (Gfp a)

data Triv
data CSubst s x t
class (Env e, Env f) => CtxMor e f s
instance Env e => CtxMor e Empty Triv
instance (Env e, Env f, CtxMor e f s, Var (New f U) x U, Type e t) =>
    CtxMor e (New f U) (CSubst s x t)

class (Env e, 

class (Env e, Env f, CtxMor e f s, Type f a, Type e b) =>
    Subst e f s a b | a s -> b
instance (Env e, Type Empty a, Weaken e a') => Subst e Empty Triv a a'
instance (Env e, Env f,
          Var (New f U) x U,
          Type e t,
          CtxMor e f s) =>
    Subst e (New f U) (CSubst s x t) (VT x) t
{-instance (Env e, Env f,
          CtxMor e f s,
          Var (New f U) x U,
          Var f y U,
          Type e t,
          Subst e f s (VT y) t) =>
    Subst e (New f U) (CSubst s x t) (VT y) t
-}
{-
instance (Env e,
          Type (New e U) a1, Type (New e U) a2,
          Type e b,
          Var (New e U) x U,
          Type e c1, Type e c2,
          Subst e a1 b x c1, Subst e a2 b x c2) =>
    Subst e (Sum a1 a2) b x (Sum c1 c2)
instance (Env e,
          Type (New e U) a1, Type (New e U) a2,
          Type e b,
          Var (New e U) x U,
          Type e c1, Type e c2,
          Subst e a1 b x c1, Subst e a2 b x c2) =>
    Subst e (Prod a1 a2) b x (Prod c1 c2)
instance (Env e,
          Type (New (New e U) U) a,
          Type e b,
          Var (New e U) x U,
          Type (New e U) c,
          Subst e a b x c) =>
    Subst e (Lfp a) b x (Lfp c)
instance (Env e,
          Type (New (New e U) U) a,
          Type e b,
          Var (New e U) x U,
          Type (New e U) c,
          Subst e a b x c) =>
    Subst e (Gfp a) b x (Gfp c)

-}

-- | Used environments: e for term variables, s for signature variables
data Term s e t where
    V :: (Env e, Type Empty t, Var e v t) =>
         v -> Term s e t
    Sym :: (Env s, Type Empty t, Var s v t) =>
           v -> Term s e t
    Inj1 :: (Env e, Type Empty a, Type Empty b) =>
            Term s e a -> Term s e (Sum a b)
    Inj2 :: (Env e, Type Empty a, Type Empty b) =>
            Term s e b -> Term s e (Sum a b)
    In :: (Env e, Type (New Empty U) a, Subst (New Empty U) a (Lfp a) (X0 U) c) =>
          Term s e c -> Term s e (Lfp a)
    Prj1 :: (Env e, Type Empty a, Type Empty b) =>
            Term s e (Prod a b) -> Term s e a
    Prj2 :: (Env e, Type Empty a, Type Empty b) =>
            Term s e (Prod a b) -> Term s e b
    Out :: (Env e, Type (New Empty U) a, Subst Empty a (Gfp a) (X0 U) c) =>
          Term s e (Gfp a) -> Term s e c

data Body s t where
    Hole :: (Env s, Type Empty a) =>
            Term s Empty a -> Body s a
    Prod :: (Env s, Type Empty a, Type Empty b) =>
            Term s Empty a -> Term s Empty b -> Body s (Prod a b)
    Tr :: (Env s, Type (New Empty U) a, Subst Empty a (Gfp a) (X0 U) c) =>
          Term s Empty c -> Body s (Gfp a)

data Defs s where
    Empty :: Defs Empty
    Cons :: (Env s, Type Empty a, Var (New s a) v a) =>
              Defs s -> v -> Body (New s a) a -> Defs (New s a)

data Prog where
    Prog :: (Env s, Type Empty a) => Defs s -> Term s Empty a -> Prog


-- Examples --

-- Types
type OneTVar = New Empty U
type TX0 = X0 U
type TX1 = Succ TX0 U
type TX2 = Succ TX1 U

type One = Gfp (VT TX0)
type Nat = Lfp (Sum One TX0)
type List a = Lfp (Sum One (Prod a TX0))

type OneVar a = New Empty a

-- Programs
type UnitSig = OneVar One

unitDefs :: Defs UnitSig
unitDefs = Cons Empty f unitBody
    where
      f = V0 :: X0 One
      unitBody :: Body UnitSig One
      unitBody = Tr (Sym f)

unit :: Term UnitSig Empty One
unit = Sym f
    where f = V0 :: X0 One

unitP :: Prog
unitP = Prog unitDefs unit

z :: Term UnitSig Empty Nat
z = In t -- (Inj1 unit :: Term UnitSig Empty (Sum One Nat))
    where
      t :: Term UnitSig Empty (Sum One Nat)
      t = undefined
