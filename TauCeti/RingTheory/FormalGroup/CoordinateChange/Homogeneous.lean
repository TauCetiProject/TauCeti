/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.CoordinateChange.Grading
public import TauCeti.RingTheory.FormalGroup.CoordinateChange.HopfAlgebroid
import Mathlib.Algebra.Polynomial.Laurent

/-!
# Homogeneity of the right unit and conjugation

The right unit of the strict coordinate-change Hopf algebroid preserves the Lazard grading
when its target carries the combined grading on `L[b₁, b₂, …]`. Inversion of strict
isomorphisms also preserves this grading, and hence reflects homogeneity.

The main results are `TauCeti.LazardRing.rightUnit_mem_coordinateGrading` and
`TauCeti.LazardRing.conjugation_mem_coordinateGrading_iff`. These allow the source and
target of a strict isomorphism, and its inverse, to retain their homological degrees.

The grading is recorded by a Laurent indeterminate: its square rescales the formal group
law and conjugates the universal coordinate by a homothety. Laurent polynomials permit
this homothety to be inverted; injectivity of polynomial inclusion recovers the integral
grading statements, without inverting any integer or Lazard coefficient.

## References

* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.1.
-/

public section

noncomputable section

namespace TauCeti.LazardRing

open MvPolynomial TauCeti.GradedAlgebra
open FormalCoordinate (universalStrictCoordinate coeff_succ_universalStrictCoordinate
  map_universalStrictCoordinate)

private abbrev Γ := MvPolynomial ℕ+ LazardRing

private def coordinateWeight : Γ →+* LaurentPolynomial Γ :=
  Polynomial.toLaurent.comp (toPolynomial coordinateGrading)

private def degreeUnit : (LaurentPolynomial Γ)ˣ where
  val := LaurentPolynomial.T 2
  inv := LaurentPolynomial.T (-2)
  val_inv := by rw [← LaurentPolynomial.T_add]; rfl
  inv_val := by rw [← LaurentPolynomial.T_add]; rfl

private theorem weight_source (f : LazardRing →+* Γ) :
    formalGroup.map (Polynomial.toLaurent.comp
      ((Polynomial.mapRingHom f).comp (toPolynomial grading))) =
      (formalGroup.map (LaurentPolynomial.C.comp f)).rescale degreeUnit := by
  apply FormalGroup.ext
  apply MvPowerSeries.ext
  intro d
  simp only [FormalGroup.map_toPowerSeries, FormalGroup.coeff_rescale,
    MvPowerSeries.coeff_map, RingHom.comp_apply,
    toPolynomial_of_mem (coeff_formalGroup_mem_grading d)]
  simp only [Polynomial.map_monomial, Polynomial.toLaurent_C_mul_T, degreeUnit,
    LaurentPolynomial.T_pow, Polynomial.coe_mapRingHom]
  rw [mul_comm]
  congr 2
  push_cast
  omega

private theorem weight_C :
    coordinateWeight.comp C = Polynomial.toLaurent.comp
      ((Polynomial.mapRingHom C).comp (toPolynomial grading)) := by
  let f : grading →+*ᵍ coordinateGrading :=
    { toRingHom := C, map_mem := C_mem_coordinateGrading }
  apply RingHom.ext
  intro x
  exact congrArg Polynomial.toLaurent (f.map_toPolynomial x).symm

private theorem weight_coordinate :
    FormalCoordinate.map coordinateWeight universalStrictCoordinate =
      FormalCoordinate.homothety degreeUnit⁻¹ *
        FormalCoordinate.map LaurentPolynomial.C universalStrictCoordinate *
          FormalCoordinate.homothety degreeUnit := by
  rw [map_universalStrictCoordinate, map_universalStrictCoordinate,
    FormalCoordinate.homothety_inv_mul_ofStrictCoeffs_mul_homothety]
  congr 1
  funext i
  simp only [Function.comp_apply, coordinateWeight, RingHom.comp_apply,
    toPolynomial_of_mem (X_mem_coordinateGrading i), Polynomial.toLaurent_C_mul_T,
    degreeUnit, LaurentPolynomial.T_pow]
  rw [mul_comm]
  congr 2
  push_cast
  omega

private theorem weight_rightUnit :
    coordinateWeight.comp rightUnit = Polynomial.toLaurent.comp
      ((Polynomial.mapRingHom rightUnit).comp (toPolynomial grading)) := by
  apply hom_ext
  calc
    formalGroup.map (coordinateWeight.comp rightUnit) =
        FormalCoordinate.map coordinateWeight universalStrictCoordinate •
          (formalGroup.map (LaurentPolynomial.C.comp C)).rescale degreeUnit := by
      rw [map_comp_rightUnit, weight_C, weight_source]
    _ = (FormalCoordinate.map LaurentPolynomial.C universalStrictCoordinate •
        formalGroup.map (LaurentPolynomial.C.comp C)).rescale degreeUnit := by
      rw [weight_coordinate, FormalGroup.rescale_smul]
    _ = (formalGroup.map (LaurentPolynomial.C.comp rightUnit)).rescale degreeUnit := by
      rw [map_comp_rightUnit]
    _ = _ := (weight_source rightUnit).symm

/-- The right unit preserves homological degrees, with both Lazard coefficients and
coordinate variables contributing to the combined target grading. -/
theorem rightUnit_mem_coordinateGrading {n : ℕ} {x : LazardRing} (hx : x ∈ grading n) :
    rightUnit x ∈ coordinateGrading n := by
  apply toPolynomial_eq_monomial_iff.mp
  apply Polynomial.toLaurent_injective
  have h := RingHom.congr_fun weight_rightUnit x
  simpa [coordinateWeight, toPolynomial_of_mem hx] using h

/-- The right unit also reflects homological degrees, since the graded counit retracts it. -/
@[simp]
theorem rightUnit_mem_coordinateGrading_iff {n : ℕ} {x : LazardRing} :
    rightUnit x ∈ coordinateGrading n ↔ x ∈ grading n :=
  ⟨fun hx ↦ by
    simpa only [← RingHom.comp_apply, counit_comp_rightUnit, RingHom.id_apply] using
      counit_mem_grading hx, rightUnit_mem_coordinateGrading⟩

private theorem conjugation_X_mem (i : ℕ+) :
    conjugation (X i) ∈ coordinateGrading (2 * (i : ℕ)) := by
  apply toPolynomial_eq_monomial_iff.mp
  apply Polynomial.toLaurent_injective
  have h := congrArg (fun φ : FormalCoordinate (LaurentPolynomial Γ) ↦
    PowerSeries.coeff (i + 1) φ.toPowerSeries)
    (congrArg Inv.inv weight_coordinate)
  rw [← map_inv, ← map_conjugation_universalStrictCoordinate,
    ← FormalCoordinate.map_comp] at h
  have hinv : (FormalCoordinate.homothety degreeUnit⁻¹ *
      FormalCoordinate.map LaurentPolynomial.C universalStrictCoordinate *
        FormalCoordinate.homothety degreeUnit)⁻¹ =
      FormalCoordinate.homothety degreeUnit⁻¹ *
        FormalCoordinate.map LaurentPolynomial.C universalStrictCoordinate⁻¹ *
          FormalCoordinate.homothety degreeUnit := by
    simp [mul_inv_rev, mul_assoc, ← map_inv]
  rw [hinv, FormalCoordinate.coeff_homothety_inv_mul_mul_homothety,
    ← map_conjugation_universalStrictCoordinate,
    ← FormalCoordinate.map_comp] at h
  simp only [FormalCoordinate.toPowerSeries_map, PowerSeries.coeff_map,
    RingHom.comp_apply, coeff_succ_universalStrictCoordinate] at h
  simp only [degreeUnit, Units.val_mk, Units.inv_mk, LaurentPolynomial.T_pow,
    ← LaurentPolynomial.T_add] at h
  have exponent : (-2 + ((i : ℕ) + 1 : ℕ) * 2 : ℤ) = (2 * (i : ℕ) : ℕ) := by
    push_cast
    omega
  rw [exponent, mul_comm] at h
  simpa only [coordinateWeight, RingHom.comp_apply, Polynomial.toLaurent_C_mul_T] using h

/-- Inverting a strict isomorphism preserves the combined homological grading. -/
theorem conjugation_mem_coordinateGrading {n : ℕ} {x : MvPolynomial ℕ+ LazardRing}
    (hx : x ∈ coordinateGrading n) :
    conjugation x ∈ coordinateGrading n := by
  apply (coordinateGrading_map_mem_iff coordinateGrading (.id ℕ) conjugation).mpr
    ⟨fun _ _ hy ↦ by simpa using rightUnit_mem_coordinateGrading hy, conjugation_X_mem⟩ hx

/-- Inversion of strict isomorphisms preserves and reflects homogeneity in every degree. -/
@[simp]
theorem conjugation_mem_coordinateGrading_iff {n : ℕ} {x : MvPolynomial ℕ+ LazardRing} :
    conjugation x ∈ coordinateGrading n ↔ x ∈ coordinateGrading n := by
  exact ⟨fun hx ↦ by simpa using conjugation_mem_coordinateGrading hx,
    conjugation_mem_coordinateGrading⟩

end TauCeti.LazardRing
