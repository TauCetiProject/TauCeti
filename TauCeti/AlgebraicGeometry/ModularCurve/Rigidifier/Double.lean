/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ModularCurve.Simultaneous.Projections
import TauCeti.CategoryTheory.Aut.Representable

/-!
# The scheme of two rigidifications

Suppose `(𝒫, δ)` is represented by an elliptic family `V` and `δ` is relatively representable.
The relative representing scheme `δ_V` then represents `(𝒫, δ, δ)`. This file constructs the
two forgetful maps to `V`, identifies the structures they classify, and transfers properties
of `δ` to both maps. For a finite étale rigidifier the two maps are finite étale; if `𝒫` is
rigid, they jointly define a monomorphism into `V.base ×_B V.base`.

An arrow `X ⟶ V_{δ_V}` is the same as a pair of arrows `f g : X ⟶ V` classifying the same
`𝒫`-structure: such a pair lifts to `RelRepData.doubleLift f g`, and every arrow into `V_{δ_V}` is
the lift of its two projections (`RelRepData.eq_doubleLift`).

This is the geometric relation used to recover a moduli scheme from a rigidified one. The
construction does not require a group acting on the rigidifier, so it also applies to
rigidifying covers which are not Galois.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Chapter 4,
  proof of Theorem 4.7.0.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData

variable {B : Scheme.{u}} {P Q : ModuliProblem B} (D : Q.RelRepData)
  {V : EllObj B} (R : (P ⊗ Q).RepresentableBy V)

/-- The relative representing scheme of `Q` over the universal `(P, Q)`-family represents
`(P, Q, Q)`. The last `Q`-structure is the additional relative structure. -/
noncomputable def doubleRepresentableBy :
    (P ⊗ (Q ⊗ Q)).RepresentableBy (V.baseChangeFunctor.obj (D.rep V)) :=
  (D.tensorRepresentableBy R).ofIso ((β_ Q (P ⊗ Q)) ≪≫ (α_ P Q Q))

/-- The triple classified by an arrow into the scheme of two rigidifications consists of the
two structures pulled back from `V`, followed by the additional relative structure. -/
theorem doubleRepresentableBy_homEquiv {X : EllObj B}
    (f : X ⟶ V.baseChangeFunctor.obj (D.rep V)) :
    (D.doubleRepresentableBy R).homEquiv f =
      ((R.homEquiv (f ≫ V.baseChangeFunctorHom (D.rep V))).1,
        ((R.homEquiv (f ≫ V.baseChangeFunctorHom (D.rep V))).2,
          Q.map f.op (D.universal V))) := by
  rw [doubleRepresentableBy, homEquiv_ofIso, Iso.trans_hom, NatTrans.comp_app,
    types_comp_apply, associator_hom_app_apply, braiding_hom_app_apply,
    tensorRepresentableBy_homEquiv]

/-- The second projection from the scheme of two rigidifications: forget the original
`Q`-structure and retain the additional relative one. The first projection is the existing
`V.baseChangeFunctorHom (D.rep V)`. -/
noncomputable def doubleSnd : V.baseChangeFunctor.obj (D.rep V) ⟶ V :=
  R.homEquiv.symm ((P ◁ snd Q Q).app _ ((D.doubleRepresentableBy R).homEquiv (𝟙 _)))

/-- The second projection classifies the first and last structures of the universal triple.
Use `rw` with this equation: simplification changes the product in the codomain of `homEquiv`
before this left-hand side can match. -/
theorem homEquiv_doubleSnd :
    R.homEquiv (D.doubleSnd R) =
      (P ◁ snd Q Q).app _ ((D.doubleRepresentableBy R).homEquiv (𝟙 _)) :=
  R.homEquiv.apply_symm_apply _

/-- Pulling back the first and last structures of the universal triple gives the pair
classified by the composite with the second projection. -/
theorem homEquiv_comp_doubleSnd {X : EllObj B}
    (f : X ⟶ V.baseChangeFunctor.obj (D.rep V)) :
    R.homEquiv (f ≫ D.doubleSnd R) =
      (P ◁ snd Q Q).app _ ((D.doubleRepresentableBy R).homEquiv f) := by
  rw [R.homEquiv_comp, homEquiv_doubleSnd, ← NatTrans.naturality_apply,
    ← (D.doubleRepresentableBy R).homEquiv_comp, Category.comp_id]

/-- Pulling back the first two structures of the universal triple gives the pair classified by
the composite with the first projection. This is the companion of `homEquiv_comp_doubleSnd`. -/
theorem homEquiv_comp_baseChangeFunctorHom {X : EllObj B}
    (f : X ⟶ V.baseChangeFunctor.obj (D.rep V)) :
    R.homEquiv (f ≫ V.baseChangeFunctorHom (D.rep V)) =
      (P ◁ fst Q Q).app _ ((D.doubleRepresentableBy R).homEquiv f) := by
  rw [whiskerLeft_app_apply, Functor.Monoidal.fst_app_apply, doubleRepresentableBy_homEquiv]
  exact Prod.mk.eta.symm

/-- The existing base-change projection classifies the first two structures of the universal
triple. Together with `homEquiv_doubleSnd`, this identifies the two forgetful projections. -/
theorem homEquiv_baseChangeFunctorHom :
    R.homEquiv (V.baseChangeFunctorHom (D.rep V)) =
      (P ◁ fst Q Q).app _ ((D.doubleRepresentableBy R).homEquiv (𝟙 _)) := by
  simpa only [Category.id_comp] using D.homEquiv_comp_baseChangeFunctorHom R (𝟙 _)

/-- Both projections inherit properties of the rigidifying problem. In particular, if its
relative representing morphisms are finite, étale, or surjective, so is the second projection.
For the first projection this is immediate from `EllObj.baseChangeFunctorHom_base`. -/
theorem mem_doubleSnd_base {W : MorphismProperty Scheme.{u}} [W.RespectsIso]
    (h : W (D.rep V).hom) : W (D.doubleSnd R).base :=
  D.mem_base_of_forget_middle (D.doubleRepresentableBy R) R (D.doubleSnd R)
    (D.homEquiv_doubleSnd R) h

/-- If `P` is rigid, the two projections from the scheme of two rigidifications jointly define
a monomorphism to the fibre product of the scheme of one rigidification with itself. -/
theorem mono_pullback_lift_baseChangeFunctorHom_doubleSnd (hP : P.IsRigid) :
    Mono (pullback.lift (V.baseChangeFunctorHom (D.rep V)).base (D.doubleSnd R).base
      (by rw [EllObj.Hom.base_structureMap, EllObj.Hom.base_structureMap]) :
      (V.baseChangeFunctor.obj (D.rep V)).base ⟶ pullback V.structureMap V.structureMap) :=
  hP.mono_pullback_lift (R := D.doubleRepresentableBy R)
    (D.homEquiv_baseChangeFunctorHom R) (D.homEquiv_doubleSnd R)

/-! ### Two rigidifications of one `𝒫`-structure -/

/-- The arrow into the scheme of two rigidifications classifying the triple `(p, d₁, d₂)`, for
arrows `f g : X ⟶ V` classifying pairs `(p, d₁)` and `(p', d₂)`. It lifts `f` along the first
projection (`doubleLift_comp_baseChangeFunctorHom`) and, when `p = p'`, lifts `g` along the second
(`doubleLift_comp_doubleSnd`). Every arrow into the scheme of two rigidifications is of this form
(`eq_doubleLift`). -/
noncomputable def doubleLift {X : EllObj B} (f g : X ⟶ V) :
    X ⟶ V.baseChangeFunctor.obj (D.rep V) :=
  (D.doubleRepresentableBy R).homEquiv.symm
    ((R.homEquiv f).1, ((R.homEquiv f).2, (R.homEquiv g).2))

/-- The arrow `doubleLift f g` classifies the `𝒫`- and `δ`-structures classified by `f`, followed
by the `δ`-structure classified by `g`. -/
theorem doubleRepresentableBy_homEquiv_doubleLift {X : EllObj B} (f g : X ⟶ V) :
    (D.doubleRepresentableBy R).homEquiv (D.doubleLift R f g) =
      ((R.homEquiv f).1, ((R.homEquiv f).2, (R.homEquiv g).2)) :=
  (D.doubleRepresentableBy R).homEquiv.apply_symm_apply _

/-- The arrow `doubleLift f g` lifts `f` along the first projection. -/
@[reassoc (attr := simp)]
theorem doubleLift_comp_baseChangeFunctorHom {X : EllObj B} (f g : X ⟶ V) :
    D.doubleLift R f g ≫ V.baseChangeFunctorHom (D.rep V) = f :=
  R.homEquiv.injective (by
    rw [homEquiv_comp_baseChangeFunctorHom, doubleRepresentableBy_homEquiv_doubleLift]
    -- whiskering keeps the `𝒫`-structure and projects the pair of `δ`-structures to its first
    -- component; the argument is a literal tuple, so this is computed componentwise
    exact Prod.ext (Functor.Monoidal.whiskerLeft_app_apply_fst _ _)
      ((Functor.Monoidal.whiskerLeft_app_apply_snd _ _).trans (Functor.Monoidal.fst_app_apply _)))

/-- If `f` and `g` classify the same `𝒫`-structure, the arrow `doubleLift f g` lifts `g` along
the second projection. -/
@[reassoc]
theorem doubleLift_comp_doubleSnd {X : EllObj B} {f g : X ⟶ V}
    (h : (R.homEquiv f).1 = (R.homEquiv g).1) : D.doubleLift R f g ≫ D.doubleSnd R = g :=
  R.homEquiv.injective (by
    rw [homEquiv_comp_doubleSnd, doubleRepresentableBy_homEquiv_doubleLift]
    -- as above, with the second component of the pair of `δ`-structures
    exact Prod.ext ((Functor.Monoidal.whiskerLeft_app_apply_fst _ _).trans h)
      ((Functor.Monoidal.whiskerLeft_app_apply_snd _ _).trans (Functor.Monoidal.snd_app_apply _)))

/-- The two projections of an arrow into the scheme of two rigidifications classify the same
`𝒫`-structure. -/
theorem fst_homEquiv_comp_doubleSnd {X : EllObj B} (k : X ⟶ V.baseChangeFunctor.obj (D.rep V)) :
    (R.homEquiv (k ≫ D.doubleSnd R)).1 = (R.homEquiv (k ≫ V.baseChangeFunctorHom (D.rep V))).1 := by
  rw [homEquiv_comp_doubleSnd, homEquiv_comp_baseChangeFunctorHom,
    Functor.Monoidal.whiskerLeft_app_apply_fst, Functor.Monoidal.whiskerLeft_app_apply_fst]

/-- Every arrow into the scheme of two rigidifications is the lift of its two projections. -/
theorem eq_doubleLift {X : EllObj B} (k : X ⟶ V.baseChangeFunctor.obj (D.rep V)) :
    k = D.doubleLift R (k ≫ V.baseChangeFunctorHom (D.rep V)) (k ≫ D.doubleSnd R) := by
  refine (D.doubleRepresentableBy R).homEquiv.injective ?_
  rw [doubleRepresentableBy_homEquiv_doubleLift, homEquiv_comp_baseChangeFunctorHom,
    homEquiv_comp_doubleSnd]
  -- both sides are the triple classified by `k`, read componentwise
  exact Prod.ext (Functor.Monoidal.whiskerLeft_app_apply_fst _ _).symm
    (Prod.ext ((Functor.Monoidal.whiskerLeft_app_apply_snd _ _).trans
        (Functor.Monoidal.fst_app_apply _)).symm
      ((Functor.Monoidal.whiskerLeft_app_apply_snd _ _).trans
        (Functor.Monoidal.snd_app_apply _)).symm)

end TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData
