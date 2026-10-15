/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PointHom.Place
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Unramified
import TauCeti.GroupTheory.Coset.Fiber

/-!
# Fibres of the class-group point map

Over a separably closed field, every fibre of a separable isogeny's point map has exactly
the degree of the isogeny many points. In particular, the point map is surjective, and its
kernel is finite with cardinality equal to the degree.

The map here is `Isogeny.toPointHom`, defined by extension and norm on ideal classes.
The point--place dictionary intertwines it with restriction of places. Complete splitting
then identifies its fibres with the finite fibres of restriction, including over infinity.
Separably closed constants suffice: the residue extensions are separable because the
isogeny is unramified, so every place above a rational place is again rational.

## Main results

* `TauCeti.Isogeny.ncard_fiber_toPointHom_eq_degree`: every point fibre has size `deg φ`.
* `TauCeti.Isogeny.finite_setOf_toPointHom_eq`: every point fibre is finite.
* `TauCeti.Isogeny.toPointHom_surjective`: a separable isogeny is surjective on points over
  a separably closed field.
* `TauCeti.Isogeny.card_ker_toPointHom_eq_degree`: the point kernel has cardinality `deg φ`.
* `TauCeti.Isogeny.finite_ker_toPointHom`: the point kernel is finite.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.10.
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] [IsSepClosed F]
  {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁ W₂) [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField]

local instance : IsIntegrallyClosed W₁.CoordinateRing := W₁.isIntegrallyClosed_coordinateRing
local instance : IsIntegrallyClosed W₂.CoordinateRing := W₂.isIntegrallyClosed_coordinateRing
local instance : IsDedekindDomain W₂.CoordinateRing :=
  W₂.isDedekindDomain_coordinateRing_of_isIntegrallyClosed

/-- Every fibre of a separable isogeny's class-group point map has cardinality equal to its
degree over a separably closed field. -/
@[simp]
theorem ncard_fiber_toPointHom_eq_degree (Q : W₂.Point) :
    {P : W₁.Point | φ.toPointHom P = Q}.ncard = φ.degree := by
  let _ := φ.fieldPullback.toRingHom.toAlgebra
  have := φ.isScalarTower_of_algebraMap_eq_fieldPullback fun _ ↦ rfl
  have := φ.finiteDimensional_functionField fun _ ↦ rfl
  let vQ := (pointEquivDegreeOnePlace W₂ Q).1
  let f := fun P : W₁.Point ↦ (pointEquivDegreeOnePlace W₁ P).1
  have hf : Function.Injective f :=
    Subtype.val_injective.comp (pointEquivDegreeOnePlace W₁).injective
  have hbij : Set.BijOn f {P | φ.toPointHom P = Q}
      {v : Place F W₁.FunctionField | v.restrict F W₂.FunctionField = vQ} := by
    refine ⟨?_, hf.injOn, ?_⟩
    · intro P hP
      rw [Set.mem_ofPred_eq, ← φ.coe_pointEquivDegreeOnePlace_toPointHom (fun _ ↦ rfl), hP]
    · intro v hv
      -- Complete splitting makes every place in this fibre rational.
      have hdeg : v.degree = 1 := by
        rw [Place.degree_eq_degree_restrict_mul_relativeDegree F W₂.FunctionField v, hv,
          (pointEquivDegreeOnePlace W₂ Q).2, one_mul]
        exact (φ.isSplitCompletely (fun _ ↦ rfl) vQ).relativeDegree_eq_one hv
      let P := (pointEquivDegreeOnePlace W₁).symm ⟨v, hdeg⟩
      have hP : f P = v := by simp [f, P]
      refine ⟨P, ?_, hP⟩
      apply (pointEquivDegreeOnePlace W₂).injective
      apply Subtype.ext
      rw [φ.coe_pointEquivDegreeOnePlace_toPointHom (fun _ ↦ rfl)]
      dsimp only [f] at hP
      rw [hP]
      exact hv
  exact hbij.ncard_eq.trans (φ.ncard_setOf_restrict_eq_degree (fun _ ↦ rfl) vQ)

/-- **Every fibre of a separable isogeny's point map is finite** over a separably closed field. -/
theorem finite_setOf_toPointHom_eq (Q : W₂.Point) : {P : W₁.Point | φ.toPointHom P = Q}.Finite :=
  Set.finite_of_ncard_ne_zero (by rw [φ.ncard_fiber_toPointHom_eq_degree Q]; exact φ.degree_ne_zero)

/-- A separable isogeny is surjective on points over a separably closed field. -/
theorem toPointHom_surjective : Function.Surjective φ.toPointHom := by
  intro Q
  exact Set.nonempty_of_ncard_ne_zero (s := {P : W₁.Point | φ.toPointHom P = Q}) (by
    rw [φ.ncard_fiber_toPointHom_eq_degree Q]
    exact φ.degree_pos.ne')

/-- The kernel of a separable isogeny's class-group point map has cardinality equal to the
degree over a separably closed field. -/
-- Simplify before `AddMonoidHom.mem_ker` rewrites membership in the kernel subtype.
@[simp↓] theorem card_ker_toPointHom_eq_degree : Nat.card φ.toPointHom.ker = φ.degree := by
  rw [← φ.ncard_fiber_toPointHom_eq_degree 0, ← Nat.card_coe_set_eq]
  exact (φ.toPointHom.card_fiber_eq_card_ker (map_zero φ.toPointHom)).symm

/-- The point kernel of a separable isogeny over a separably closed field is finite. -/
instance finite_ker_toPointHom : Finite φ.toPointHom.ker :=
  Nat.finite_of_card_ne_zero (φ.card_ker_toPointHom_eq_degree ▸ φ.degree_ne_zero)

end TauCeti.Isogeny

end
