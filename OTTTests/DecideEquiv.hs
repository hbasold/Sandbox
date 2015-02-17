import Data.Map as Map
import qualified Data.Set as Set
import Data.Set (Set)
import Control.Monad.Reader
import Control.Monad.Error

type TyVar = String
type SVar = String
type Var = String

data Type = PT TyVar
          | Sum Type Type
          | Lfp TyVar Type
          | Prod Type Type
          | Gfp TyVar Type
            deriving (Show, Eq, Ord)

data Idx = L | R deriving (Eq, Ord)

instance Show Idx where
    show L = "1"
    show R = "2"

data Term = Sym SVar Type
          | Inj Idx Term Type
          | In Term Type
          | Prj Idx Term Type
          | Out Term Type
            deriving (Eq, Ord)

instance Show Term where
    show (Sym x _) = x
    show (Inj i t _) = "inj" ++ show i ++ " (" ++ show t ++ ")"
    show (In t _) = "in (" ++ show t ++ ")"
    show (Prj i t _) = "prj" ++ show i ++ " (" ++ show t ++ ")"
    show (Out t _) = "out (" ++ show t ++ ")"

data Body = ProdAbs Term Term
          | GfpAbs Term
            deriving Show

type Defs = Map SVar (Type, Body)
data Prog = Prog Defs Term

-- Bring terms into weak head normal form
data EvCtx = PrjC Idx
           | OutC

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

-- Decide whether two terms are observationally equivalent
type Rel = Map Type (Set (Term, Term))

data Test = Top
          | Bot
          | InjT Test Test
          | InT Test
          | PrjT Idx Test
          | OutT Test

instance Show Test where
    show Top = "T"
    show Bot = "F"
    show (InjT t1 t2) = "[" ++ show t1 ++ "," ++ show t2 ++ "]"
    show (InT t) = "unf " ++ show t
    show (PrjT i t) = "[" ++ show i ++ "]" ++ " " ++ show t
    show (OutT t) = "[out]" ++ " " ++ show t


data Abort = Error String
           | InEquiv Test
             deriving Show

type M a = ReaderT Defs (Either Abort) a

lookupSym :: SVar -> M Body
lookupSym f =
    do r <- asks (Map.lookup f)
       case r of
         Nothing -> throwError $ Error $ "Unknown symbol " ++ f
         Just (_, b) -> return b

updateTest :: (Test -> Test) -> M a -> M a
updateTest tc m =
    catchError m (\e -> case e of
                          Error s -> throwError $ Error s
                          InEquiv t -> throwError $ InEquiv $ tc t)

-- Monontone in the given relation
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

inBisim :: Type -> Term -> Term -> Rel -> Bool
inBisim a t1 t2 r =
    case Map.lookup a r of
      Nothing -> False
      Just s -> Set.member (t1, t2) s

bisimCand :: Defs -> Term -> Term -> Rel -> Either Abort Rel
bisimCand d t1 t2 b = runReaderT (createBisimCand t1 t2 b) d

-- Examples --

-- Types
oneT :: Type
oneT = Gfp "x" $ PT "x"
nat :: Type
nat = Lfp "y" $ Sum oneT (PT "y")
list :: Type -> Type
list a = Lfp "y" $ Sum oneT (Prod a (PT "y"))
stream :: Type -> Type
stream a = Gfp "y" $ Prod a (PT "y")

-- Terms & Programs
unitDefs :: Defs
unitDefs = singleton "f" (oneT, GfpAbs $ Sym "f" oneT)
unit :: Term
unit = Sym "f" oneT
unitProg :: Prog
unitProg = Prog unitDefs unit

repNat :: Int -> Term
repNat n | n < 0 = undefined
         | n == 0 = In (Inj L unit (Sum oneT nat)) nat
         | n > 0 = In (Inj R (repNat (n-1)) (Sum oneT nat)) nat

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

{-
s1 = Out o1 (Prod nat $ stream nat)
s2 = Out o2 (Prod nat $ stream nat)
r1 = Prj L s1 nat
r2 = Prj L s2 nat
u1 = Prj R s1 (stream nat)
u2 = Prj R s2 (stream nat)
zo = Out z (Prod nat $ stream nat)
zh = Prj L zo nat
-}

-- As expected:
-- bisimCand oDefs o1 o2 Map.empty
-- results into the correct bisimulation.
-- bisimCand oDefs o1 z Map.empty
-- results into a test.
