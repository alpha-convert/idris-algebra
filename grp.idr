interface Group a where
  (<*>) : a -> a -> a
  inv : a -> a
  e : a
  lAssoc : (x <*> y) <*> z = x <*> (y <*> z)
  rAssoc : x <*> (y <*> z) = (x <*> y) <*> z
  lId : e <*> x = x
  rId : x <*> e = x
  lInv : inv x <*> x = e
  rInv : x <*> inv x = e

multEq : (Group a) => {x,y,z,w : a} -> (x = y) -> (z = w) -> (x <*> z) = (y <*> w)
multEq Refl Refl = Refl

lMultIntro : (Group a) => {x,y : a} -> (pf : x = y) -> (z : a) -> (z <*> x = z <*> y)
lMultIntro Refl _ = Refl

rMultIntro : (Group a) => {x,y : a} -> (pf : x = y) -> (z : a) -> (x <*> z = y <*> z)
rMultIntro Refl _ = Refl

lMultElim : (Group a) =>  {x,y,z : a} -> (pf : z <*> x = z <*> y) -> (x = y)
lMultElim {x = x} {y = y} {z = z} {pf = pf} =
  let lMult = lMultIntro pf (inv z) in
      let reassocd = trans lAssoc (trans lMult rAssoc) in
          let xElimd = trans (rMultIntro lInv x) lId in
          let yElimd = trans (rMultIntro lInv y) lId in
              trans (sym xElimd) (trans reassocd yElimd)

rMultElim : (Group a) =>  {x,y,z : a} -> (pf : x <*> z = y <*> z) -> (x = y)
rMultElim {x = x} {y = y} {z = z} {pf = pf} =
  let rMult = rMultIntro pf (inv z) in
      let reassocd = trans rAssoc (trans rMult lAssoc) in
          let xElimd = trans (lMultIntro rInv x) rId in
          let yElimd = trans (lMultIntro rInv y) rId in
              trans (sym xElimd) (trans reassocd yElimd)


invIsInvolution : (Group a) => {x : a} -> (inv (inv x)) = x
invIsInvolution = lMultElim $ trans rInv (sym lInv)

lDivOut : (Group a) => {x,y,z : a} -> (x <*> y = z) -> (y = (inv x) <*> z)
lDivOut Refl {y = y} = sym $ trans rAssoc (trans (rMultIntro lInv y) lId)

rDivOut : (Group a) => {x,y,z : a} -> (x <*> y = z) -> (x = z <*> (inv y))
rDivOut Refl {x = x} = sym $ trans lAssoc (trans (lMultIntro rInv x) rId)

lMultSubst : (Group a) => {x,x',y,z : a} -> (x = x') -> (x <*> y = z) -> (x' <*> y = z)
lMultSubst Refl Refl = Refl

rMultSubst : (Group a) => {x,x',y,z : a} -> (x = x') -> (y <*> x = z) -> (y <*> x' = z)
rMultSubst Refl Refl = Refl

lMultInvHelper : (Group a) => {g,g' : a} -> (inv g <*> g <*> g' = g')
lMultInvHelper = lMultSubst (sym lInv) lId

rMultInvHelper : (Group a) => {g,g' : a} -> (g <*> (g' <*> inv g') = g)
rMultInvHelper = rMultSubst (sym rInv) rId

--right multiplication to the identity implies inverse
rMultIdIsInv : (Group a) => {g,g' : a} -> (g <*> g' = Main.e) -> (g' = inv g)
rMultIdIsInv {g = g} prf = trans (sym lMultInvHelper) (trans (sym rAssoc) (trans (lMultIntro prf (inv g)) rId))

lMultIdIsInv : (Group a) => {g,g' : a} -> (g' <*> g = Main.e) -> (g' = inv g)
lMultIdIsInv {g = g} prf = trans (sym rMultInvHelper) (trans (sym lAssoc) (trans (rMultIntro prf (inv g)) lId))

lMidCancel : (Group a) => {x,y,z : a} -> (x <*> (inv y) <*> y <*> z = x <*> z)
lMidCancel {x=x} {y=y} {z=z} = let lside = rMultIntro Refl Main.e in
                                   let introY = trans (rMultSubst (sym lInv) lside) rId in
                                       rMultIntro (trans (sym rAssoc) introY) z

prodInv : (Group a) => {x,y : a} -> ((inv y) <*> (inv x) = inv (x <*> y))
prodInv {y=y} = lMultIdIsInv $ trans rAssoc $ trans lMidCancel (lInv {x=y})

data HomLaw : (a -> b) -> Type where
  MkHomLaw : (Group a, Group b) => {f : a -> b}
             -> ((x,y: a) -> (f (x <*> y) = (f x) <*> (f y)))
             -> HomLaw f


data Hom : Type -> Type -> Type where
  MkHom : (Group a,Group b) => (f : a -> b) -> HomLaw f -> Hom a b

funEq : {f : a -> b} -> {x,y : a} -> (x = y) -> (f x = f y)
funEq Refl = Refl

homUnderHom : (Group a, Group b) => {x,y : a}
  -> {f : a -> b}
  -> {g : b -> c}
  -> (fIsHom : f (x <*> y) = (f x) <*> (f y))
  -> (g (f (x <*> y)) = g (f x <*> f y))
homUnderHom fIsHom = funEq fIsHom


composeProof : (Group a, Group b, Group c) =>  (g : b -> c)
  -> (f : a -> b) 
  -> (h : a -> c) 
  -> ((z : a) -> (g (f z) = h z))
  -> (homLawG : (x : b) -> (y : b) -> g (x <*> y) = ((g x) <*> (g y))) 
  -> (homLawF : (x : a) -> (y : a) -> f (x <*> y) = ((f x) <*> (f y))) 
  -> (x : a) 
  -> (y : a) 
  -> h (x <*> y) = ((h x) <*> (h y))
composeProof g f h pf 
             homLawG 
             homLawF 
             x y = let hlgSpec = homLawG (f x) (f y) in
                       let pfSpec = pf (x <*> y) in
                               (trans (sym pfSpec) (trans p (trans hlgSpec (multEq (pf x) (pf y)))))
                               where
                                 p = homUnderHom {f=f} (homLawF x y)


composeWithProof : (g : b -> c) -> (f : a -> b) -> (h**(x : a) -> (g . f) x = h x)
composeWithProof g f = (g . f ** (\_ => Refl))

compose_hom : (Group a, Group b, Group c) => (g : Hom b c) -> (f : Hom a b) -> Hom a c
compose_hom (MkHom g (MkHomLaw homLawG)) 
            (MkHom f (MkHomLaw homLawF)) = let (h**pf) = composeWithProof g f in
                                               MkHom h (MkHomLaw {f=h} (composeProof g f h pf homLawG homLawF))
