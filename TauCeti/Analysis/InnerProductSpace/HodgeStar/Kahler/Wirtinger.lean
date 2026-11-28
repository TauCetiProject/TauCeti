/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Power
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.CalibratedFrame
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Complex
import TauCeti.Geometry.Symplectic.Finrank

/-!
# The Wirtinger inequality and Kähler calibrations on Hermitian vector spaces

On any finite-dimensional Hermitian vector space `E`, specializing the normalized Kähler power
`AlmostComplexStructure.kahlerPowerForm` (from
`TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Power`) to multiplication by `i`
(`AlmostComplexStructure.ofComplexModule E`) yields the all-degree Wirtinger inequality
(`TauCeti.norm_kahlerPowerForm_le`, `TauCeti.norm_kahlerPowerForm`) and the calibrated-frame
classification (`TauCeti.isCalibratedFrame_kahlerPowerForm_iff`) in terms of
`TauCeti.complexToRealFamily`.

## Main results

On finite-dimensional Hermitian vector spaces:

* `TauCeti.norm_kahlerPowerForm_le`: `‖kahlerPowerForm E r‖ ≤ 1` for every power index `r`.
* `TauCeti.norm_kahlerPowerForm`: `‖kahlerPowerForm E r‖ = 1` whenever `r ≤ finrank ℂ E`.
* `TauCeti.isCalibratedFrame_kahlerPowerForm_iff`: a `2r`-frame `v` is calibrated by
  `kahlerPowerForm E r` precisely when `v` is real-orthonormal and shares its exterior product
  with `TauCeti.complexToRealFamily u` for some complex-orthonormal family `u : Fin r → E`.

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. **148** (1982), Theorem II.6.11
  and Lemma II.6.13.
* H. Federer, *Geometric Measure Theory*, Springer (1969), §1.8.2.
* R. C. McLean, *Deformations of calibrated submanifolds*, Comm. Anal. Geom. **6** (1998),
  705–747.
-/

public section

noncomputable section

open Module exteriorPower
open scoped InnerProductSpace RealInnerProductSpace

namespace TauCeti

section HermitianWirtinger

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [InnerProductSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]

/-- The normalized `r`-th Kähler power `ωʳ / r!` (power index `r`, form degree `2 * r`) has comass
at most one for every power index `r`. -/
theorem norm_kahlerPowerForm_le (r : ℕ) : ‖kahlerPowerForm E r‖ ≤ 1 := by
  rw [kahlerPowerForm_eq_ofComplexModule]
  exact AlmostComplexStructure.norm_kahlerPowerForm_le
    AlmostComplexStructure.real_inner_ofComplexModule_ofComplexModule r

/-- **The Wirtinger inequality in every degree**: on a finite-dimensional Hermitian vector space
`E`, for every power index `r ≤ finrank ℂ E`, the normalized Kähler power `ωʳ / r!` (form degree
`2 * r`) has comass one. -/
theorem norm_kahlerPowerForm {r : ℕ} (hr : r ≤ finrank ℂ E) : ‖kahlerPowerForm E r‖ = 1 := by
  have : FiniteDimensional ℂ E := Module.Finite.of_restrictScalars_finite ℝ ℂ E
  rw [kahlerPowerForm_eq_ofComplexModule]
  refine AlmostComplexStructure.norm_kahlerPowerForm
    AlmostComplexStructure.real_inner_ofComplexModule_ofComplexModule ?_
  rw [finrank_real_eq_two_mul_finrank_complex]
  omega

/-- **Equality case of the Wirtinger inequality in every degree**: a `2r`-frame `v` in a
finite-dimensional Hermitian vector space `E` is calibrated by `ωʳ / r!` precisely when `v` is
real-orthonormal and shares its exterior product with `TauCeti.complexToRealFamily u` for some
complex-orthonormal family `u : Fin r → E`. -/
theorem isCalibratedFrame_kahlerPowerForm_iff {r : ℕ} (v : Fin (2 * r) → E) :
    (kahlerPowerForm E r).IsCalibratedFrame v ↔
      Orthonormal ℝ v ∧ ∃ u : Fin r → E, Orthonormal ℂ u ∧
        ιMulti ℝ (2 * r) v = ιMulti ℝ (2 * r) (complexToRealFamily u) := by
  rw [kahlerPowerForm_eq_ofComplexModule,
    AlmostComplexStructure.isCalibratedFrame_kahlerPowerForm_iff
      AlmostComplexStructure.real_inner_ofComplexModule_ofComplexModule]
  refine and_congr_right fun _ ↦ ⟨?_, ?_⟩
  · rintro ⟨u, hu, hJu, hι⟩
    have huC : Orthonormal ℂ u :=
      (hu.complex_iff_forall_real_inner_I_smul_eq_zero).2 fun i j ↦ by
        simpa [AlmostComplexStructure.ofComplexModule_apply] using hJu i j
    have hframe : (AlmostComplexStructure.ofComplexModule E).complexRealFrame u =
        complexToRealFamily u := by
      ext i
      obtain ⟨⟨j, k⟩, rfl⟩ := (complexRealIndexEquiv r).surjective i
      fin_cases k <;> simp
    exact ⟨u, huC, by rwa [hframe] at hι⟩
  · rintro ⟨u, hu, hι⟩
    have huR : Orthonormal ℝ u := hu.real
    refine ⟨u, huR, fun i j ↦ ?_, ?_⟩
    · simpa [AlmostComplexStructure.ofComplexModule_apply] using
        (huR.complex_iff_forall_real_inner_I_smul_eq_zero).1 hu i j
    · convert hι using 2
      ext i
      obtain ⟨⟨j, k⟩, rfl⟩ := (complexRealIndexEquiv r).surjective i
      fin_cases k <;> simp

end HermitianWirtinger

end TauCeti
