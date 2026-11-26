/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.CoordinateChange.Grading
public import TauCeti.RingTheory.FormalGroup.CoordinateChange.HopfAlgebroid
import TauCeti.RingTheory.PowerSeries.Coordinate.Graded

/-!
# The graded coproduct of strict coordinate changes

The composition map for strict isomorphisms of formal group laws preserves homological
degrees. Its target is the polynomial model of the tensor square, with the Lazard grading
on coefficients and degree `2i` on both families `bᵢ` and `bᵢ'`. The coproduct also reflects
homogeneity, by the left counit identity. These results retain the integral coefficient ring;
no torsion-freeness or division is required.

## References

* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.1.
-/

public section

noncomputable section

namespace TauCeti.LazardRing

open MvPolynomial
open FormalCoordinate (universalStrictCoordinate coeff_succ_universalStrictCoordinate
  map_universalStrictCoordinate)

/-- Composition of strict coordinate changes preserves the combined homological grading. -/
theorem coproduct_mem_coordinateTensorGrading {n : ℕ} {x : MvPolynomial ℕ+ LazardRing}
    (hx : x ∈ coordinateGrading n) : coproduct x ∈ coordinateTensorGrading n := by
  apply (coordinateGrading_map_mem_iff coordinateTensorGrading (.id ℕ) coproduct).mpr
    ⟨fun _ _ hx ↦ by
      simpa using C_mem_coordinateTensorGrading (C_mem_coordinateGrading hx), ?_⟩ hx
  intro i
  have h₁ : FormalCoordinate.map C universalStrictCoordinate ∈
      FormalCoordinate.gradedSubgroup coordinateTensorGrading 2 := by
    rw [map_universalStrictCoordinate, FormalCoordinate.ofStrictCoeffs_mem_gradedSubgroup]
    exact fun i ↦ C_mem_coordinateTensorGrading (X_mem_coordinateGrading i)
  have h₂ : FormalCoordinate.map (map rightUnit) universalStrictCoordinate ∈
      FormalCoordinate.gradedSubgroup coordinateTensorGrading 2 := by
    rw [map_universalStrictCoordinate, FormalCoordinate.ofStrictCoeffs_mem_gradedSubgroup]
    simp
  have h := (FormalCoordinate.mem_gradedSubgroup coordinateTensorGrading 2 _).mp
    ((FormalCoordinate.gradedSubgroup coordinateTensorGrading 2).mul_mem h₂ h₁) (i + 1)
  rw [← map_coproduct_universalStrictCoordinate, FormalCoordinate.toPowerSeries_map,
    PowerSeries.coeff_map, coeff_succ_universalStrictCoordinate] at h
  simpa using h

/-- The coproduct preserves and reflects homogeneity. -/
@[simp]
theorem coproduct_mem_coordinateTensorGrading_iff {n : ℕ} {x : MvPolynomial ℕ+ LazardRing} :
    coproduct x ∈ coordinateTensorGrading n ↔ x ∈ coordinateGrading n := by
  refine ⟨fun hx ↦ ?_, coproduct_mem_coordinateTensorGrading⟩
  have h := (coordinateTensorGrading_map_mem_iff coordinateGrading (.id ℕ)
    (pushoutLift rightUnit ⟨(C.comp counit, RingHom.id _), by
      rw [RingHom.comp_assoc, counit_comp_rightUnit, RingHom.comp_id, RingHom.id_comp]⟩)).mpr
    ⟨fun _ _ hy ↦ by simpa using C_mem_coordinateGrading (counit_mem_grading hy),
      fun _ ↦ by simp⟩ hx
  rwa [← RingHom.comp_apply, pushoutLift_counit_id_comp_coproduct, RingHom.id_apply,
    AddMonoidHom.id_apply] at h

end TauCeti.LazardRing
