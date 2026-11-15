/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Additivity

/-!
# Vector dependence and restriction of diagonal spectral measures

Let `P` be a projection-valued measure on `X` acting on a complex Hilbert space `H`. To each vector
`ξ : H`, `P` attaches the finite positive measure `P.diag ξ` whose value on a measurable set `B` is
`‖P.proj B hB ξ‖ₑ ^ 2`.

This file records how `P.diag ξ` varies with `ξ` and interacts with spectral projections:

* `P.diag 0 = 0`, `P.diag (-ξ) = P.diag ξ`, and `P.diag (c • ξ) = (‖c‖₊ ^ 2) • P.diag ξ`;
* `P.diag (ξ + η) ≤ 2 • P.diag ξ + 2 • P.diag η`, the parallelogram upper bound that makes
  second-moment conditions against `P.diag` closed under addition;
* `P.diag (P.proj B hB ξ) = (P.diag ξ).restrict B`, identifying the diagonal measure of a projected
  vector with the restriction of the original diagonal measure.

## References

* G. Teschl, *Mathematical Methods in Quantum Mechanics*, AMS GSM 99, 2009, Section 3.1.
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Springer GTM 265, 2012,
  Section 4.1.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace TauCeti.ProjValMeasure

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The diagonal spectral measure of the zero vector is the zero measure. -/
@[simp]
theorem diag_zero (P : ProjValMeasure X H) : P.diag 0 = 0 := by
  ext B hB
  simp [← P.enorm_sq_proj_apply B hB 0]

/-- Negating a vector leaves its diagonal spectral measure unchanged. -/
@[simp]
theorem diag_neg (P : ProjValMeasure X H) (ξ : H) : P.diag (-ξ) = P.diag ξ := by
  ext B hB
  rw [← P.enorm_sq_proj_apply B hB (-ξ), ← P.enorm_sq_proj_apply B hB ξ, map_neg, eNorm_neg]

/-- Scaling a vector by `c` scales its diagonal spectral measure by `‖c‖₊ ^ 2`. -/
theorem diag_smul (P : ProjValMeasure X H) (c : ℂ) (ξ : H) :
    P.diag (c • ξ) = (‖c‖₊ ^ 2) • P.diag ξ := by
  ext B hB
  rw [smul_apply, ← P.enorm_sq_proj_apply B hB (c • ξ), ← P.enorm_sq_proj_apply B hB ξ,
    map_smul, eNorm_smul, mul_pow, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_pow,
    eNorm_eq_nnNorm]

/-- Subadditivity of diagonal spectral measures up to a factor of `2`:
`P.diag (ξ + η) ≤ 2 • P.diag ξ + 2 • P.diag η`. -/
theorem diag_add_le (P : ProjValMeasure X H) (ξ η : H) :
    P.diag (ξ + η) ≤ 2 • P.diag ξ + 2 • P.diag η := by
  rw [Measure.le_iff]
  intro B hB
  let u := P.proj B hB ξ
  let v := P.proj B hB η
  have hreal : ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
    nlinarith [norm_add_le u v, norm_nonneg (u + v), sq_nonneg (‖u‖ - ‖v‖)]
  have henorm : ‖u + v‖ₑ ^ 2 ≤ 2 * ‖u‖ₑ ^ 2 + 2 * ‖v‖ₑ ^ 2 := by
    have h := ENNReal.ofReal_le_ofReal hreal
    rwa [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_pow (norm_nonneg _),
      ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm, ofReal_norm, ofReal_norm] at h
  calc (P.diag (ξ + η)) B
      = ‖u + v‖ₑ ^ 2 := by
          rw [← P.enorm_sq_proj_apply B hB (ξ + η), map_add]
    _ ≤ 2 * ‖u‖ₑ ^ 2 + 2 * ‖v‖ₑ ^ 2 := henorm
    _ = (2 • P.diag ξ + 2 • P.diag η) B := by
          simp [u, v, P.enorm_sq_proj_apply B hB]

/-- Subadditivity of diagonal spectral measures on differences:
`P.diag (ξ - η) ≤ 2 • P.diag ξ + 2 • P.diag η`. -/
theorem diag_sub_le (P : ProjValMeasure X H) (ξ η : H) :
    P.diag (ξ - η) ≤ 2 • P.diag ξ + 2 • P.diag η := by
  rw [sub_eq_add_neg, ← P.diag_neg η]
  exact P.diag_add_le ξ (-η)

/-- Projecting a vector onto a measurable set `B` restricts its diagonal spectral measure to `B`. -/
@[simp]
theorem diag_proj (P : ProjValMeasure X H) (B : Set X) (hB : MeasurableSet B) (ξ : H) :
    P.diag (P.proj B hB ξ) = (P.diag ξ).restrict B := by
  ext C hC
  rw [Measure.restrict_apply hC, ← P.enorm_sq_proj_apply C hC,
    ← P.enorm_sq_proj_apply (C ∩ B) (hC.inter hB), ← ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.mul_def, P.proj_inter]

end TauCeti.ProjValMeasure
