/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PointHom.Affine
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Unramified
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InfinityPlace
import TauCeti.GroupTheory.Coset.Fiber

/-!
# Fibres of the class-group point map

For a separable isogeny over a separably closed field, the point–place dictionary identifies
the fibres of `Isogeny.toPointHom` with the fibres of restriction of places. Every place over a
rational point has degree one, since the isogeny splits that place completely. Consequently
each point fibre has cardinality equal to the degree of the isogeny. In particular, the point
map is surjective and its kernel has that cardinality.

The comparison uses the class-group computation at affine points and at infinity. The count
then follows from the fundamental identity for places and unramifiedness of separable isogenies.

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

section Restrict

variable [Algebra W₂.FunctionField W₁.FunctionField]
  (h : ∀ z, algebraMap W₂.FunctionField W₁.FunctionField z = φ.fieldPullback z)

/-- A separable isogeny sends a rational point to the point whose place lies below it. -/
private theorem toPointHom_eq_of_restrict_eq (P : W₁.Point) (Q : W₂.Point)
    (hP : haveI := φ.isScalarTower_of_algebraMap_eq_fieldPullback h
      haveI := φ.finiteDimensional_functionField h
      (W₁.pointEquivDegreeOnePlace P).1.restrict F W₂.FunctionField =
        (W₂.pointEquivDegreeOnePlace Q).1) :
    φ.toPointHom P = Q := by
  have := φ.isScalarTower_of_algebraMap_eq_fieldPullback h
  have := φ.finiteDimensional_functionField h
  have hmap : algebraMap W₂.FunctionField W₁.FunctionField = φ.fieldPullback.toRingHom :=
    RingHom.ext h
  cases P with
  | zero =>
    rw [coe_pointEquivDegreeOnePlace_zero] at hP
    have hinf : (Place.infinity W₁).restrict F W₂.FunctionField = Place.infinity W₂ := by
      rw [Place.restrict_eq_iff_isEquiv_comap, Place.valuation_infinity,
        Place.valuation_infinity, hmap]
      exact φ.isEquiv_comap_infinityPlace
    have hQ : Q = 0 := (W₂.pointEquivDegreeOnePlace).injective (Subtype.ext (by
      simpa only [Point.zero_def, coe_pointEquivDegreeOnePlace_zero] using hP.symm.trans hinf))
    simp only [← Point.zero_def, map_zero, hQ]
  | some x y hxy =>
    rw [Place.restrict_eq_iff_isEquiv_comap, coe_pointEquivDegreeOnePlace_some,
      Place.valuation_ofPrime, hmap] at hP
    cases Q with
    | zero =>
      rw [coe_pointEquivDegreeOnePlace_zero, Place.valuation_infinity] at hP
      exact φ.toPointHom_some_eq_zero_of_isEquiv_comap_infinityPlace hxy hP
    | some x' y' hxy' =>
      rw [coe_pointEquivDegreeOnePlace_some, Place.valuation_ofPrime] at hP
      exact φ.toPointHom_some_eq_some_of_isEquiv_comap_pointPlace hxy hxy' hP

/-- The point–place dictionary intertwines the point map of a separable isogeny and restriction
of places along its function-field pullback. -/
-- Not a simp lemma: the left-hand side does not determine `φ`; callers supply it and `h`.
theorem restrict_pointEquivDegreeOnePlace (P : W₁.Point) :
    haveI := φ.isScalarTower_of_algebraMap_eq_fieldPullback h
    haveI := φ.finiteDimensional_functionField h
    (W₁.pointEquivDegreeOnePlace P).1.restrict F W₂.FunctionField =
      (W₂.pointEquivDegreeOnePlace (φ.toPointHom P)).1 := by
  have := φ.isScalarTower_of_algebraMap_eq_fieldPullback h
  have := φ.finiteDimensional_functionField h
  let R := (W₁.pointEquivDegreeOnePlace P).1.restrict F W₂.FunctionField
  have := R.finiteDimensional_residueField W₂.isFunctionField
  have hdeg : R.degree = 1 := Nat.le_antisymm
    ((Place.degree_restrict_le F W₂.FunctionField _).trans
      (W₁.pointEquivDegreeOnePlace P).2.le) R.one_le_degree
  let Q := W₂.pointEquivDegreeOnePlace.symm ⟨R, hdeg⟩
  have hQ : (W₂.pointEquivDegreeOnePlace Q).1 = R :=
    congrArg Subtype.val (W₂.pointEquivDegreeOnePlace.apply_symm_apply ⟨R, hdeg⟩)
  rw [φ.toPointHom_eq_of_restrict_eq h P Q hQ.symm, hQ]

end Restrict

/-- Every fibre of a separable isogeny's point map over a separably closed field has cardinality
equal to its degree. -/
theorem ncard_fiber_toPointHom (Q : W₂.Point) :
    {P : W₁.Point | φ.toPointHom P = Q}.ncard = φ.degree := by
  let _ : Algebra W₂.FunctionField W₁.FunctionField := φ.fieldPullback.toRingHom.toAlgebra
  have h : ∀ z, algebraMap W₂.FunctionField W₁.FunctionField z = φ.fieldPullback z := fun _ ↦ rfl
  have := φ.isScalarTower_of_algebraMap_eq_fieldPullback h
  have := φ.finiteDimensional_functionField h
  rw [← φ.ncard_setOf_restrict_eq_degree h (W₂.pointEquivDegreeOnePlace Q).1]
  apply Set.BijOn.ncard_eq (f := fun P ↦ (W₁.pointEquivDegreeOnePlace P).1)
  refine ⟨?_, ?_, ?_⟩
  · intro P hP
    exact (φ.restrict_pointEquivDegreeOnePlace h P).trans
      (congrArg (fun P ↦ (W₂.pointEquivDegreeOnePlace P).1) hP)
  · intro P _ P' _ hPP'
    exact W₁.pointEquivDegreeOnePlace.injective (Subtype.ext hPP')
  · intro R hR
    have hdeg : R.degree = 1 := by
      rw [Place.degree_eq_degree_restrict_mul_relativeDegree F W₂.FunctionField R, hR,
        (W₂.pointEquivDegreeOnePlace Q).2,
        (φ.isSplitCompletely h (W₂.pointEquivDegreeOnePlace Q).1).relativeDegree_eq_one hR,
        mul_one]
    let P := W₁.pointEquivDegreeOnePlace.symm ⟨R, hdeg⟩
    have hP : (W₁.pointEquivDegreeOnePlace P).1 = R :=
      congrArg Subtype.val (W₁.pointEquivDegreeOnePlace.apply_symm_apply ⟨R, hdeg⟩)
    exact ⟨P, φ.toPointHom_eq_of_restrict_eq h P Q (hP ▸ hR), hP⟩

/-- A separable isogeny is surjective on points over a separably closed field. -/
theorem toPointHom_surjective : Function.Surjective φ.toPointHom := by
  intro Q
  have hpos : 0 < {P : W₁.Point | φ.toPointHom P = Q}.ncard := by
    rw [φ.ncard_fiber_toPointHom Q]
    exact φ.degree_pos
  exact (Set.ncard_pos (Set.finite_of_ncard_pos hpos)).mp hpos

/-- The kernel of a separable isogeny's class-group point map has cardinality equal to the
degree over a separably closed field. -/
theorem card_ker_toPointHom : Nat.card φ.toPointHom.ker = φ.degree := by
  rw [← φ.ncard_fiber_toPointHom 0, ← Nat.card_coe_set_eq]
  exact (φ.toPointHom.card_fiber_eq_card_ker (map_zero φ.toPointHom)).symm

/-- The point kernel of a separable isogeny over a separably closed field is finite. -/
instance finite_ker_toPointHom : Finite φ.toPointHom.ker :=
  Nat.finite_of_card_ne_zero (φ.card_ker_toPointHom ▸ φ.degree_ne_zero)

end TauCeti.Isogeny
