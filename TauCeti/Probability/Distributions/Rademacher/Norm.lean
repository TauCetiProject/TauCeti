/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Rademacher.Basic
public import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# The Rademacher convexity inequality

For a finite family of vectors `v i` and pairwise independent Rademacher signs `ε i`,
each `‖v j‖` is bounded by the expected norm of `∑ i, ε i • v i`. Thus the same
expectation bounds the maximum of the vector norms. This estimate compares random
signed sums with their largest summand, as needed in lower bounds for mean norms
of finite-dimensional spaces.

Only pairwise independence is needed: testing the signed sum against a norming
functional and multiplying by `ε j` recovers `‖v j‖` in expectation. No completeness,
separability, or finite-dimensionality assumption on the vector space is required.
Real scalar multiplication also covers complex normed spaces by restriction of scalars.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §13.3.
-/

public section

open MeasureTheory ProbabilityTheory TauCeti.Probability
open scoped BigOperators

namespace Finset

variable {Ω ι E : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ε : ι → Ω → ℝ}

/-- A finite Rademacher sum of fixed vectors is integrable, even in an incomplete space. -/
theorem integrable_sum_smul_rademacher (s : Finset ι) (v : ι → E)
    (hε : ∀ i ∈ s, HasLaw (ε i) rademacherMeasure P) :
    Integrable (fun ω ↦ ∑ i ∈ s, ε i ω • v i) P := by
  exact integrable_finsetSum s fun i hi ↦
    (hε i hi).integrable_comp (integrable_rademacherMeasure fun t ↦ t • v i)

/-- **Rademacher convexity inequality.** Every summand's norm is bounded by the expected
norm of the signed sum. Pairwise independence of the Rademacher signs suffices. -/
theorem norm_le_integral_norm_sum_smul_rademacher (s : Finset ι) (v : ι → E)
    (hε : ∀ i ∈ s, HasLaw (ε i) rademacherMeasure P)
    (hind : (s : Set ι).Pairwise fun i j ↦ IndepFun (ε i) (ε j) P) {j : ι} (hj : j ∈ s) :
    ‖v j‖ ≤ ∫ ω, ‖∑ i ∈ s, ε i ω • v i‖ ∂P := by
  classical
  let : IsProbabilityMeasure P := (hε j hj).isProbabilityMeasure
  have habs (i : ι) (hi : i ∈ s) : ∀ᵐ ω ∂P, |ε i ω| = 1 := by
    apply ((hε i hi).ae_iff (by fun_prop : Measurable fun t : ℝ ↦ |t| = 1)).2
    simp [rademacherMeasure_eq]
  have hint (i : ι) (hi : i ∈ s) : Integrable (fun ω ↦ ε j ω * ε i ω) P := by
    refine ⟨((hε j hj).aemeasurable.mul (hε i hi).aemeasurable).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := 1) ?_⟩
    filter_upwards [habs j hj, habs i hi] with ω hjω hiω
    simp [Real.norm_eq_abs, hjω, hiω]
  have hmoment (i : ι) (hi : i ∈ s) :
      (∫ ω, ε j ω * ε i ω ∂P) = if i = j then 1 else 0 := by
    by_cases hij : i = j
    · subst i
      have hsquare : (fun ω ↦ ε j ω * ε j ω) =ᵐ[P] fun _ ↦ (1 : ℝ) := by
        filter_upwards [habs j hj] with ω hω
        nlinarith [sq_abs (ε j ω)]
      simp [integral_congr_ae hsquare]
    · rw [(hind hj hi (Ne.symm hij)).integral_fun_mul_eq_mul_integral
        (hε j hj).aemeasurable.aestronglyMeasurable (hε i hi).aemeasurable.aestronglyMeasurable,
        (hε j hj).integral_eq, (hε i hi).integral_eq, integral_id_rademacherMeasure]
      simp [hij]
  obtain ⟨f, hf, hfv⟩ := exists_dual_vector'' ℝ (v j)
  have heval : (∫ ω, ε j ω * f (∑ i ∈ s, ε i ω • v i) ∂P) = ‖v j‖ := by
    simp_rw [map_sum, map_smul, smul_eq_mul, Finset.mul_sum, ← mul_assoc]
    rw [integral_finsetSum s (fun i hi ↦ (hint i hi).mul_const (f (v i)))]
    simp only [integral_mul_const]
    rw [Finset.sum_congr rfl (fun i hi ↦ congrArg (· * f (v i)) (hmoment i hi))]
    simpa [hj] using hfv
  rw [← heval]
  refine integral_mono_ae
    (by simpa only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum, ← mul_assoc] using
      integrable_finsetSum s (fun i hi ↦ (hint i hi).mul_const (f (v i))))
    (integrable_sum_smul_rademacher s v hε).norm ?_
  filter_upwards [habs j hj] with ω hω
  calc
    _ ≤ |ε j ω * f (∑ i ∈ s, ε i ω • v i)| := le_abs_self _
    _ = ‖f (∑ i ∈ s, ε i ω • v i)‖ := by rw [abs_mul, hω, one_mul, Real.norm_eq_abs]
    _ ≤ ‖∑ i ∈ s, ε i ω • v i‖ := (f.le_opNorm _).trans (by
      exact mul_le_of_le_one_left (norm_nonneg _) hf)

/-- The largest norm in a nonempty finite family is bounded by the expected norm of its
Rademacher sum. -/
theorem sup'_norm_le_integral_norm_sum_smul_rademacher (s : Finset ι) (hs : s.Nonempty)
    (v : ι → E) (hε : ∀ i ∈ s, HasLaw (ε i) rademacherMeasure P)
    (hind : (s : Set ι).Pairwise fun i j ↦ IndepFun (ε i) (ε j) P) :
    s.sup' hs (fun i ↦ ‖v i‖) ≤ ∫ ω, ‖∑ i ∈ s, ε i ω • v i‖ ∂P := by
  exact (Finset.sup'_le_iff hs _).2 fun j hj ↦
    norm_le_integral_norm_sum_smul_rademacher s v hε hind hj

end Finset
