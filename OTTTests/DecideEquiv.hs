-- | In this module, we implement a decision procedure for observational
-- equivalence of programs of a very simple language. This language allows
-- programs of finitely-indexed, inductive and coinductive type.
-- A program consists of a definition block and a term, where a definition block
-- contains definitions of the form f : A = D for some symbol f, type A and
-- a body D. A body, in turn, is either of the form { ξ ↦ t } or
-- { π₁ ↦ t₁; π₂ ↦ t₂ } for terms t, t₁, t₂. These are copattern abstractions
-- á la Abel et al.
module DecideEquiv where

import Data.Map as Map
import qualified Data.Set as Set
import Data.Set (Set)
import Control.Monad.Reader
import Control.Monad.Except

type TyVar = String
type SVar = String
type Var = String

-- | Possible types:
-- A ::= X | A + A | μX.A | A × A | νX.A
data Type = PT TyVar
          | Sum Type Type
          | Lfp TyVar Type
          | Prod Type Type
          | Gfp TyVar Type
            deriving (Eq, Ord)

-- | subst a x b substitutes a for x in b. Assumption: a is closed.
subst :: Type -> TyVar -> Type -> Type
subst a x (PT y) = if x == y then a else PT y
subst a x (Sum b1 b2) = Sum (subst a x b1) (subst a x b2)
subst a x b@(Lfp y c) = if x == y then b else (Lfp y (subst a x c))
subst a x (Prod b1 b2) = Prod (subst a x b1) (subst a x b2)
subst a x b@(Gfp y c) = if x == y then b else (Gfp y (subst a x c))

-- | Index of coproduct injections and product projections
data Idx = L | R deriving (Eq, Ord)

instance Show Idx where
    show L = "1"
    show R = "2"

-- | Allowed terms:
-- t ::= f | κ₁ t | κ₂ t | α t | π₁ t | π₂ t | ξ t
-- where f is a symbol defined in a definition block,
-- κ₁ is the first coproduct injection, α the lfp injection,
-- π₁ the first product projection and ξ the gfp projection.
data Term = Sym SVar Type
          | Inj Idx Term Type
          | In Term Type
          | Prj Idx Term Type
          | Out Term Type
            deriving (Eq, Ord)

getType :: Term -> Type
getType (Sym _ a) = a
getType (Inj _ _ a) = a
getType (In _ a) = a
getType (Prj _ _ a) = a
getType (Out _ a) = a

-- | Body D of a definition f : A = D. Note that we allow only
-- one-layer copatterns for products and gfps.
data Body = ProdAbs Term Term
          | GfpAbs Term

instance Show Body where
    show (ProdAbs t1 t2) = "{π₁ ↦ " ++ show t1 ++ "; π₂ ↦ " ++ show t2 ++ "}"
    show (GfpAbs t) = "{ξ ↦ " ++ show t ++ "}"

-- | Definition block that assigns to symbols f their type
-- and body.
type Defs = Map SVar (Type, Body)

-- | Programs are terms using symbols from a definition block.
data Prog = Prog Defs Term

------ Pretty printing ----

instance Show Type where
    showsPrec _ (PT x) = showString x
    showsPrec p (Sum a b) = showParen (p > 10) $
                            showsPrec 10 a .
                            showString " + " .
                            showsPrec 10 b
    showsPrec p (Lfp x a) = showParen (p > 0) $
                            showString "μ" .
                            showString x .
                            showString ". " .
                            showsPrec 0 a
    showsPrec p (Prod a b) = showParen (p > 10) $
                             showsPrec 11 a .
                             showString " × " .
                             showsPrec 11 b
    showsPrec p (Gfp x a) = showParen (p > 0) $
                            showString "ν" .
                            showString x .
                            showString ". " .
                            showsPrec 0 a
subscriptIdx L = "₁"
subscriptIdx R = "₂"

instance Show Term where
    showsPrec _ (Sym x _) = showString x
    showsPrec p (Inj i t _) = showParen (p > 0) $
                              showString ("κ" ++ subscriptIdx i ++ " ") .
                              showsPrec 1 t
    showsPrec p (In t _) = showParen (p > 0) $
                           showString "α " .
                           showsPrec 1 t
    showsPrec p (Prj i t _) = showParen (p > 0) $
                              showString ("π" ++ subscriptIdx i ++ " ") .
                              showsPrec 1 t
    showsPrec p (Out t _) = showParen (p > 0) $
                            showString "ξ " .
                            showsPrec 1 t

-- | Evaluation context into which we can put terms.
data EvCtx = PrjC Idx
           | OutC

-- | Bring terms into principal weak head normal form, that is,
-- into "κ₁ t", "κ₁ t" or "α t" for inductive, and into "f" for coinductive
-- types. To achieve this, we contract applications of projections.
reduce :: Defs -> Term -> Term
reduce d t@(Sym f _) = t
reduce d t@(Inj _ _ _) = t
reduce d t@(In _ _) = t
reduce d (Prj i t a) =
    let t' = reduce d t
        t'' = case t' of
                Sym f _ -> reduceSym d f (PrjC i)
                _ -> error "Could not reduce to PWHNF"
    in reduce d t''
reduce d (Out t a) =
    let t' = reduce d t
        t'' = case t' of
                Sym f _ -> reduceSym d f OutC
                _ -> error "Could not reduce to PWHNF"
    in reduce d t''

reduceSym d f (PrjC i) =
    case Map.lookup f d of
      Nothing -> error $ "Undefined symbol: " ++ f
      Just (_, b) ->
          case b of
            ProdAbs t1 t2 ->
                 case i of
                   L -> t1
                   R -> t2
            _ -> error $ "Typing error: projection applied to non-product term"
reduceSym d f OutC =
    case Map.lookup f d of
      Nothing -> error $ "Undefined symbol: " ++ f
      Just (_, b) ->
          case b of
            GfpAbs t' -> t'
            _ -> error $ "Typing error: tried to do transition from non-gfp term"

-- | Type-indexed relations on terms.
type Rel = Map Type (Set (Term, Term))

-- | Tests that we can make on programs/terms.
data Test = Top
          | Bot
          | InjT Test Test
          | InT Test
          | PrjT Idx Test
          | OutT Test

instance Show Test where
    show Top = "⊤"
    show Bot = "⟂"
    show (InjT t1 t2) = "[" ++ show t1 ++ "," ++ show t2 ++ "]"
    show (InT t) = "α⁻¹ " ++ show t
    show (PrjT i t) = "[π" ++ subscriptIdx i ++ "]" ++ " " ++ show t
    show (OutT t) = "[ξ]" ++ " " ++ show t

-- | While trying to build a bisimulation, can abort with an error or a test.
-- In the latter case, the given terms were not observationally equivalent.
data Abort = Error String
           | InEquiv Test
             deriving Show

-- | Internal monad for equivalence check.
type M a = ReaderT Defs (Either Abort) a

lookupSym :: SVar -> M Body
lookupSym f =
    do r <- asks (Map.lookup f)
       case r of
         Nothing -> throwError $ Error $ "Unknown symbol " ++ f
         Just (_, b) -> return b

-- | Once we found that two terms disagree at some point, we need to construct
-- test that witnesses this fact. While going up, we extend the found test to
-- account for the path we had to take to get to the point of disagreement.
updateTest :: (Test -> Test) -> M a -> M a
updateTest tc m =
    catchError m (\e -> case e of
                          Error s -> throwError $ Error s
                          InEquiv t -> throwError $ InEquiv $ tc t)

-- | Checks whether the given terms are already related.
inBisim :: Type -> Term -> Term -> Rel -> Bool
inBisim a t1 t2 b =
    case Map.lookup a b of
      Nothing -> False
      Just s -> Set.member (t1, t2) s

-- | Decide whether two terms t₁,t₂ : A are observationally equivalent, we
-- denote this by t₁ ~ t₂.
--
-- We assume that if t₁ and t₂ are related by b, then b is closed under term
-- derivations. For example, if t₁,t₂ : A₁ × A₂, then there are s₁,s₂ : A₁ with
-- π₁ tk ->> sk that are related by b. Analogously for the other types, details
-- are in the paper.
--
-- The procedure works as follows. Whenever we have a term in PWHNF, we check
-- whether it is already in the given relation and by assumption it is already
-- closed as bisimulation up-to convertibility.
-- Otherwise, we have three cases:
-- 1. Both terms are signature symbols. Since they are of the same type, both
--    must have a body for, say, gfps D₁ = { ξ ↦ s } and D₂ = { ξ ↦ r }.
--    Then we add (t₁,t₂) to b and check recursively  s ~ r.
--    If this fails with a test φ, then we return the test [ξ] φ, otherwise the
--    resulting bisimulation.
-- 2. Both terms are of inductive type, say a coproduct, and in WHNF "κi s₁" and
--    "κi s₂". If i /= j, then t₁ /~ t₂ and we abort with the test [⊤, ⟂] that
--    distinguishes them. Otherwise, we add (t₁, t₂) to b and continue
--    recursively to check s₁ ~ s₂.
-- 3. The terms are not in PWHNF. Then we just reduce them to PWHNF and continue
--    from there.
createBisimCand :: Term -> Term -> Rel -> M Rel
createBisimCand t1@(Sym x a) t2@(Sym y _) b0 =
    if inBisim a t1 t2 b0
    then return b0
    else do
      bx <- lookupSym x
      by <- lookupSym y
      let b0' = Map.unionWith Set.union b0 $
                Map.singleton a $ Set.singleton (t1, t2)
      case (bx, by) of
        (ProdAbs s1 s2, ProdAbs r1 r2) ->
            do b1 <- proj L $ createBisimCand s1 r1 b0'
               proj R $ createBisimCand s2 r2 b1
        (GfpAbs s, GfpAbs r) ->
            out $ createBisimCand s r b0'
        _ -> throwError $ Error $
             "Type error: " ++ show t1 ++ " vs. " ++ show t2
    where
      proj i = updateTest (PrjT i)
      out = updateTest OutT

createBisimCand t1@(Inj i r1 a) t2@(Inj j r2 _) b0 =
    if i == j
    then if inBisim a t1 t2 b0
         then return b0
         else
             let b0' = Map.unionWith Set.union b0 $
                          Map.singleton a $ Set.singleton (t1, t2)
             in inj i $ createBisimCand r1 r1 b0'
    else throwError $ InEquiv $ InjT Top Bot
    where inj i = updateTest (\t -> case i of
                                      L -> InjT t Bot
                                      R -> InjT Bot t)

createBisimCand t1@(In s1 a) t2@(In s2 _) b0 =
    if inBisim a t1 t2 b0
    then return b0
    else
        let b0' = Map.unionWith Set.union b0 $
                     Map.singleton a $ Set.singleton (t1, t2)
        in updateTest InT $ createBisimCand s1 s2 b0'

createBisimCand t1 t2 b0 =
    do d <- ask
       let t1' = reduce d t1
           t2' = reduce d t2
       createBisimCand t1' t2' b0

-- | If the given terms are observationally equivalent, then we return a
-- bisimulation up-to convertibility that relates these terms, otherwise we
-- abort with a test that distinguishes them.
bisimCand :: Defs -> Term -> Term -> Either Abort Rel
bisimCand d t1 t2 = runReaderT (createBisimCand t1 t2 Map.empty) d

-- Examples --

-- Types
oneT :: Type
oneT = Gfp "x" $ PT "x"
nat :: Type
nat = Lfp "y" $ Sum oneT (PT "y")
list :: Type -> Type
list a = Lfp "y" $ Sum oneT (Prod a (PT "y"))
stream :: Type -> Type
stream a = Gfp "z" $ Prod a (PT "z")

-- Terms & Programs
unitDefs :: Defs
unitDefs = singleton "〈〉" (oneT, GfpAbs $ Sym "〈〉" oneT)
unit :: Term
unit = Sym "〈〉" oneT
unitProg :: Prog
unitProg = Prog unitDefs unit

repNat :: Int -> Term
repNat n | n < 0 = undefined
         | n == 0 = In (Inj L unit (Sum oneT nat)) nat
         | n > 0 = In (Inj R (repNat (n-1)) (Sum oneT nat)) nat

prj :: Idx -> Term -> Term
prj L t = case getType t of
            Prod a1 _ -> Prj L t a1
            _ -> error $ "Type error: applying projection to non-product type"
prj R t = case getType t of
            Prod _ a2 -> Prj R t a2
            _ -> error $ "Type error: applying projection to non-product type"

out :: Term -> Term
out t = case getType t of
          Gfp x a -> Out t (subst (Gfp x a) x a)
          _ -> error $ "Type error: applying ξ to non-gfp type"

o1, o2, o3, z :: Term
o1 = Sym "o1" (stream nat)
o2 = Sym "o2" (stream nat)
o3 = Sym "o3" (stream nat)
z = Sym "z" (stream nat)
oDefs :: Defs
oDefs = fromList [
         ("o1", (stream nat, GfpAbs (Sym "o1Out" $ Prod nat (stream nat)))),
         ("o1Out", (stream nat, ProdAbs (repNat 1) (Sym "o1" $ stream nat))),
         ("o2", (stream nat, GfpAbs (Sym "o2Out" $ Prod nat (stream nat)))),
         ("o2Out", (stream nat, ProdAbs (repNat 1) (Sym "o3" $ stream nat))),
         ("o3", (stream nat, GfpAbs (Sym "o3Out" $ Prod nat (stream nat)))),
         ("o3Out", (stream nat, ProdAbs (repNat 1) (Sym "o2" $ stream nat))),
         ("z", (stream nat, GfpAbs (Sym "zOut" $ Prod nat (stream nat)))),
         ("zOut", (stream nat, ProdAbs (repNat 0) (Sym "z" $ stream nat)))
        ]
        `Map.union` unitDefs

s1 = out o1
s2 = out o2
r1 = prj L s1
r2 = prj L s2
u1 = prj R s1
u2 = prj R s2
zo = out z
zh = prj L zo

-- As expected:
-- bisimCand oDefs o1 o2
-- results into the correct bisimulation.
-- bisimCand oDefs o1 z
-- results into a test that distinguishes o1 and z.
