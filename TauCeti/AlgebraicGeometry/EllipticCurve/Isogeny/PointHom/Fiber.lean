/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PointHom.Affine
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.PointPlace
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InfinityPlace
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Unramified

/-!
# Fibres of the class-group point map

Over a separably closed field, every fibre of a separable isogeny's point map has exactly
the degree of the isogeny many points. In particular, the point map is surjective.

The map here is `Isogeny.toPointHom`, defined by extension and norm on ideal classes.
The point--place dictionary intertwines it with restriction of places. Complete splitting
then identifies its fibres with the finite fibres of restriction, including over infinity.
Separably closed constants suffice: the residue extensions are separable because the
isogeny is unramified, so every place above a rational place is again rational.

## Main results

* `TauCeti.Isogeny.coe_pointEquivDegreeOnePlace_toPointHom`: the point map commutes
  with restriction of places.
* `TauCeti.Isogeny.ncard_fiber_toPointHom_eq_degree`: every point fibre has size `deg φ`.
* `TauCeti.Isogeny.toPointHom_surjective`: a separable isogeny is surjective on points over
  a separably closed field.

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

/-- The class-group point map sends a point to the point under its place. -/
private theorem toPointHom_eq_of_isEquiv_comap_valuation (P : W₁.Point) (Q : W₂.Point)
    (h : (((pointEquivDegreeOnePlace W₁ P).1.valuation).comap
      (φ.fieldPullback : W₂.FunctionField →+* W₁.FunctionField)).IsEquiv
        (pointEquivDegreeOnePlace W₂ Q).1.valuation) :
    φ.toPointHom P = Q := by
  cases P with
  | zero =>
    have hinf := φ.isEquiv_comap_infinityPlace
    cases Q with
    | zero => exact map_zero φ.toPointHom
    | some x y hQ =>
      simp only [coe_pointEquivDegreeOnePlace_zero, coe_pointEquivDegreeOnePlace_some,
        Place.valuation_infinity, Place.valuation_ofPrime] at h
      exact (Place.not_isEquiv_infinityPlace_valuation (CoordinateRing.pointPlace hQ.1)
        (hinf.symm.trans h)).elim
  | some x y hP =>
    cases Q with
    | zero =>
      simp only [coe_pointEquivDegreeOnePlace_some, coe_pointEquivDegreeOnePlace_zero,
        Place.valuation_ofPrime, Place.valuation_infinity] at h
      exact φ.toPointHom_some_eq_zero_of_isEquiv_comap_infinityPlace hP h
    | some x' y' hQ =>
      simp only [coe_pointEquivDegreeOnePlace_some, Place.valuation_ofPrime] at h
      exact φ.toPointHom_some_eq_some_of_isEquiv_comap_pointPlace hP hQ h

section Restrict

variable [Algebra W₂.FunctionField W₁.FunctionField]
  (hφ : ∀ z, algebraMap W₂.FunctionField W₁.FunctionField z = φ.fieldPullback z)

/-- The place of the image of a point is the restriction of the point's place along the
isogeny's function-field pullback. -/
@[simp]
theorem coe_pointEquivDegreeOnePlace_toPointHom (P : W₁.Point) :
    haveI := φ.isScalarTower_of_algebraMap_eq_fieldPullback hφ
    haveI := φ.finiteDimensional_functionField hφ
    (pointEquivDegreeOnePlace W₂ (φ.toPointHom P)).1 =
      (pointEquivDegreeOnePlace W₁ P).1.restrict F W₂.FunctionField := by
  have := φ.isScalarTower_of_algebraMap_eq_fieldPullback hφ
  have := φ.finiteDimensional_functionField hφ
  let v := (pointEquivDegreeOnePlace W₁ P).1
  -- Restriction preserves rationality, so its place corresponds to a target point.
  have hv : (v.restrict F W₂.FunctionField).degree = 1 := by
    have hle := Place.degree_restrict_le F W₂.FunctionField v
    have hpos := (v.restrict F W₂.FunctionField).one_le_degree_of_isFunctionField
      W₂.isFunctionField
    have hdeg : v.degree = 1 := (pointEquivDegreeOnePlace W₁ P).2
    omega
  let Q := (pointEquivDegreeOnePlace W₂).symm ⟨v.restrict F W₂.FunctionField, hv⟩
  have hQ : (pointEquivDegreeOnePlace W₂ Q).1 = v.restrict F W₂.FunctionField := by
    simp [Q]
  have hmap : φ.toPointHom P = Q := by
    apply φ.toPointHom_eq_of_isEquiv_comap_valuation
    have he := (Place.restrict_eq_iff_isEquiv_comap F W₂.FunctionField v
      (pointEquivDegreeOnePlace W₂ Q).1).mp hQ.symm
    have hring : algebraMap W₂.FunctionField W₁.FunctionField =
        (φ.fieldPullback : W₂.FunctionField →+* W₁.FunctionField) := RingHom.ext hφ
    rwa [hring] at he
  rw [hmap, hQ]

end Restrict

/-- Every fibre of a separable isogeny's class-group point map has cardinality equal to its
degree over a separably closed field. -/
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

/-- A separable isogeny is surjective on points over a separably closed field. -/
theorem toPointHom_surjective : Function.Surjective φ.toPointHom := by
  intro Q
  exact Set.nonempty_of_ncard_ne_zero (s := {P : W₁.Point | φ.toPointHom P = Q}) (by
    rw [φ.ncard_fiber_toPointHom_eq_degree Q]
    exact φ.degree_pos.ne')

end TauCeti.Isogeny

end
