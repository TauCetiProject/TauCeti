/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ModularCurve.Simultaneous.Projections

/-!
# The scheme of two rigidifications

Suppose `(𝒫, δ)` is represented by an elliptic family `V` and `δ` is relatively representable.
The relative representing scheme `δ_V` then represents `(𝒫, δ, δ)`. This file constructs the
two forgetful maps to `V`, identifies the structures they classify, and transfers properties
of `δ` to both maps. For a finite étale rigidifier the two maps are finite étale; if `𝒫` is
rigid, they jointly define a monomorphism into `V.base ×_B V.base`.

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
  dsimp only [doubleRepresentableBy, Functor.RepresentableBy.ofIso, Equiv.trans_apply]
  rw [D.tensorRepresentableBy_homEquiv R]
  rfl

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

/-- The existing base-change projection classifies the first two structures of the universal
triple. Together with `homEquiv_doubleSnd`, this identifies the two forgetful projections. -/
theorem homEquiv_baseChangeFunctorHom :
    R.homEquiv (V.baseChangeFunctorHom (D.rep V)) =
      (P ◁ fst Q Q).app _ ((D.doubleRepresentableBy R).homEquiv (𝟙 _)) := by
  rw [doubleRepresentableBy_homEquiv]
  rw [Category.id_comp]
  -- Evaluating the cartesian projection on this explicit triple retains its first pair.
  rfl

/-- Both projections inherit properties of the rigidifying problem. In particular, if its
relative representing morphisms are finite, étale, or surjective, so is the second projection.
For the first projection this is immediate from `EllObj.baseChangeFunctorHom_base`. -/
theorem mem_doubleSnd_base {W : MorphismProperty Scheme.{u}} [W.RespectsIso]
    (h : W (D.rep V).hom) : W (D.doubleSnd R).base :=
  D.mem_base_of_forget_middle (D.doubleRepresentableBy R) R (D.doubleSnd R)
    (D.homEquiv_doubleSnd R) h

/-- If `P` is rigid, the two projections from the scheme of two rigidifications jointly define
a monomorphism to the fibre product of the scheme of one rigidification with itself. -/
theorem mono_double (hP : P.IsRigid) :
    Mono (pullback.lift (V.baseChangeFunctorHom (D.rep V)).base (D.doubleSnd R).base
      (by rw [EllObj.Hom.base_structureMap, EllObj.Hom.base_structureMap]) :
      (V.baseChangeFunctor.obj (D.rep V)).base ⟶ pullback V.structureMap V.structureMap) :=
  hP.mono_pullback_lift (R := D.doubleRepresentableBy R)
    (D.homEquiv_baseChangeFunctorHom R) (D.homEquiv_doubleSnd R)

end TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData
