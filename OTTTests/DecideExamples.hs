module DecideExamples where

import Data.Map as Map

import DecideEquiv

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


-- bisimCand bsDefs bs bs does not terminate because bs is not observationally
-- normalising.
bs :: Term
bs = Sym "bs" (stream nat)
bsDefs :: Defs
bsDefs = fromList [
          ("bs", (stream nat,
                  GfpAbs (Out (Sym "bs" (stream nat)) (Prod nat (stream nat)))))
        ]

-- reduce bsDefs bs1 diverges
bs1 = Out bs (Prod nat $ stream nat)

funky :: Term
funky = Sym "funky" (stream nat)
funkyDefs :: Defs
funkyDefs = fromList [
             ("funky", (stream nat,
                        GfpAbs (out $ prj R (Sym "f" (Prod nat (stream nat))))
                       )
             ),
             ("f", (Prod nat $ stream nat,
                   ProdAbs
                   (repNat 0)
                   (prj R $ out $ prj R $ Sym "f" (Prod nat (stream nat)))
                  )
             )
            ]
-- | This would diverge to
-- ξ funky -> ξ π₂ f -> ξ π₂ ξ π₂ f -> ...
-- But reduce can detect this now in the fly.
funky1 :: Term
funky1 = out funky

f2 :: Term
f2 = prj R (Sym "f" $ Prod nat $ stream nat)
