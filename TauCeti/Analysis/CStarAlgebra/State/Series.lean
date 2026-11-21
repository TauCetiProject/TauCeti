/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
public import TauCeti.Analysis.Normed.Operator.PositiveContinuousLinearMap
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Analysis.CStarAlgebra.State.Spectrum

/-!
# Norm-convergent series of positive functionals and faithful states on C⋆-algebras

On a possibly nonunital complex C⋆-algebra, positivity turns unconditional operator-norm
convergence of a family `f : ι → (A →P[ℂ] ℂ)` into absolute convergence: `f` is summable in
operator norm if and only if its norms `‖f i‖` are summable
(`PositiveContinuousLinearMap.summable_toContinuousLinearMap_iff`), and the operator norm is
unconditionally additive over arbitrary index sets (`PositiveContinuousLinearMap.opNorm_tsum`).
The lower bound comes from evaluating finite partial sums along the increasing approximate unit
`CStarAlgebra.increasingApproximateUnit A`.

Combining `PositiveContinuousLinearMap.tsum` with norm-attaining states along a countable dense
sequence in the positive cone yields a faithful norm-one positive functional on every separable
nontrivial complex C⋆-algebra (`TauCeti.CStarAlgebra.exists_faithful_positiveContinuousLinearMap`).

## Main declarations

* `PositiveContinuousLinearMap.summable_toContinuousLinearMap_iff`: summability of positive
  functionals in the dual norm is equivalent to summability of their norms.
* `PositiveContinuousLinearMap.hasSum_opNorm_tsum`, `PositiveContinuousLinearMap.opNorm_tsum`:
  `‖tsum f‖ = ∑' i, ‖f i‖`, unconditionally.
* `TauCeti.CStarAlgebra.exists_faithful_positiveContinuousLinearMap`: every separable nontrivial
  C⋆-algebra admits a norm-one positive functional strictly positive on nonzero positive elements.

## References

* J. Peterson, *Notes on Operator Algebras*, Propositions 4.1.4–4.1.5 and Corollary 4.1.7.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Section 3.4.
-/

public section

noncomputable section

open Filter Topology
open scoped CStarAlgebra ComplexOrder

namespace PositiveContinuousLinearMap

variable {ι A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private theorem sum_opNorm_le_opNorm_tsum {f : ι → A →P[ℂ] ℂ}
    (hf : Summable fun i => (f i : A →L[ℂ] ℂ)) (s : Finset ι) :
    ∑ i ∈ s, ‖(f i : A →L[ℂ] ℂ)‖ ≤ ‖(tsum f : A →L[ℂ] ℂ)‖ := by
  have hl := CStarAlgebra.increasingApproximateUnit A
  have := hl.neBot
  have hlim_lhs : Tendsto (fun e => ∑ i ∈ s, (f i e).re) (CStarAlgebra.approximateUnit A)
      (𝓝 (∑ i ∈ s, ‖(f i : A →L[ℂ] ℂ)‖)) := by
    refine tendsto_finsetSum s fun i _ => ?_
    simpa only [Function.comp_def, Complex.ofReal_re] using
      (Complex.continuous_re.tendsto _).comp ((f i).tendsto_nhds_opNorm hl)
  have hlim_rhs : Tendsto (fun e => (tsum f e).re) (CStarAlgebra.approximateUnit A)
      (𝓝 ‖(tsum f : A →L[ℂ] ℂ)‖) := by
    simpa only [Function.comp_def, Complex.ofReal_re] using
      (Complex.continuous_re.tendsto _).comp ((tsum f).tendsto_nhds_opNorm hl)
  refine le_of_tendsto_of_tendsto hlim_lhs hlim_rhs ?_
  filter_upwards [hl.eventually_nonneg] with e he
  have hre : HasSum (fun i => (f i e).re) (tsum f e).re :=
    Complex.reCLM.hasSum (hasSum_tsum_apply hf e)
  simpa only [← hre.tsum_eq] using
    hre.summable.sum_le_tsum s fun i _ => (Complex.le_def.1 ((f i).map_nonneg he)).1

/-- A family of positive continuous linear functionals on a C⋆-algebra is summable in operator
norm if and only if its operator norms are summable. -/
theorem summable_toContinuousLinearMap_iff (f : ι → A →P[ℂ] ℂ) :
    Summable (fun i => (f i : A →L[ℂ] ℂ)) ↔ Summable (fun i => ‖(f i : A →L[ℂ] ℂ)‖) :=
  ⟨fun hf => summable_of_sum_le (fun _ => norm_nonneg _) (sum_opNorm_le_opNorm_tsum hf),
    Summable.of_norm⟩

/-- For a summable family of positive continuous linear functionals on a C⋆-algebra, the operator
norms sum to the operator norm of the sum. -/
theorem hasSum_opNorm_tsum {f : ι → A →P[ℂ] ℂ} (hf : Summable fun i => (f i : A →L[ℂ] ℂ)) :
    HasSum (fun i => ‖(f i : A →L[ℂ] ℂ)‖) ‖(tsum f : A →L[ℂ] ℂ)‖ := by
  have hnorm : Summable fun i => ‖(f i : A →L[ℂ] ℂ)‖ :=
    (summable_toContinuousLinearMap_iff f).1 hf
  have hge : ∑' i, ‖(f i : A →L[ℂ] ℂ)‖ ≤ ‖(tsum f : A →L[ℂ] ℂ)‖ :=
    hnorm.tsum_le_of_sum_le (sum_opNorm_le_opNorm_tsum hf)
  have hle : ‖(tsum f : A →L[ℂ] ℂ)‖ ≤ ∑' i, ‖(f i : A →L[ℂ] ℂ)‖ := by
    rw [toContinuousLinearMap_tsum]
    exact norm_tsum_le_tsum_norm hnorm
  simpa only [le_antisymm hle hge] using hnorm.hasSum

/-- **Additivity of the norm on series of positive functionals.** The operator norm of `tsum f` is
unconditionally the sum of the operator norms of the summands. -/
theorem opNorm_tsum (f : ι → A →P[ℂ] ℂ) :
    ‖(tsum f : A →L[ℂ] ℂ)‖ = ∑' i, ‖(f i : A →L[ℂ] ℂ)‖ := by
  by_cases hf : Summable fun i => (f i : A →L[ℂ] ℂ)
  · exact (hasSum_opNorm_tsum hf).tsum_eq.symm
  · have hnot : ¬ Summable fun i => ‖(f i : A →L[ℂ] ℂ)‖ :=
      mt (summable_toContinuousLinearMap_iff f).2 hf
    rw [tsum_eq_zero_of_not_summable hf, toContinuousLinearMap_zero, norm_zero,
      _root_.tsum_eq_zero_of_not_summable hnot]

end PositiveContinuousLinearMap

namespace TauCeti.CStarAlgebra

/-- Every separable nontrivial complex C⋆-algebra admits a norm-one positive continuous linear
functional that is strictly positive on every nonzero nonnegative element. -/
theorem exists_faithful_positiveContinuousLinearMap {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [TopologicalSpace.SeparableSpace A] [Nontrivial A] :
    ∃ ψ : A →P[ℂ] ℂ, ‖(ψ : A →L[ℂ] ℂ)‖ = 1 ∧ ∀ a : A, 0 ≤ a → a ≠ 0 → 0 < ψ a := by
  have : Nonempty {x : A | 0 ≤ x} := ⟨⟨0, le_rfl⟩⟩
  obtain ⟨b, hb⟩ := TopologicalSpace.exists_dense_seq {x : A | 0 ≤ x}
  choose φ hφ_norm hφ_val _ using fun n : ℕ =>
    exists_positiveContinuousLinearMap_apply_mul_self_eq_norm_sq (b n).prop
  let w : ℕ → ℝ := fun n => (1 : ℝ) / 2 / 2 ^ n
  have hw_nonneg (n : ℕ) : 0 ≤ w n := by positivity
  let f : ℕ → A →P[ℂ] ℂ := fun n =>
    PositiveContinuousLinearMap.mk₀ ((w n : ℂ) • (φ n : A →L[ℂ] ℂ)) fun x hx =>
      mul_nonneg (Complex.le_def.2 ⟨hw_nonneg n, rfl⟩) ((φ n).map_nonneg hx)
  have hf_norm (n : ℕ) : ‖(f n : A →L[ℂ] ℂ)‖ = w n := by
    simp [f, norm_smul, Real.norm_of_nonneg (hw_nonneg n), hφ_norm n]
  have hf_sum : Summable fun n => (f n : A →L[ℂ] ℂ) :=
    (PositiveContinuousLinearMap.summable_toContinuousLinearMap_iff f).2 <| by
      simpa only [hf_norm] using summable_geometric_two' (1 : ℝ)
  refine ⟨PositiveContinuousLinearMap.tsum f, ?_, ?_⟩
  · rw [PositiveContinuousLinearMap.opNorm_tsum]
    simpa only [hf_norm] using tsum_geometric_two' (1 : ℝ)
  · intro a ha ha0
    refine lt_of_le_of_ne ((PositiveContinuousLinearMap.tsum f).map_nonneg ha) (Ne.symm ?_)
    intro h0
    have hpos : 0 < ‖a‖ / 2 := half_pos (norm_pos_iff.2 ha0)
    obtain ⟨n, hn⟩ := Metric.denseRange_iff.1 hb ⟨a, ha⟩ (‖a‖ / 2) hpos
    have hdist : ‖(b n : A) - a‖ < ‖a‖ / 2 := by
      simpa only [Subtype.dist_eq, dist_eq_norm, norm_sub_rev] using hn
    have hfn0 : f n a = 0 :=
      (PositiveContinuousLinearMap.tsum_apply_eq_zero_iff hf_sum ha).1 h0 n
    have hφn0 : φ n a = 0 := by
      have hwn : (w n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
      simpa [f, hwn] using hfn0
    have hnorm_le : ‖(b n : A)‖ ≤ ‖(b n : A) - a‖ := by
      have h1 := (φ n : A →L[ℂ] ℂ).le_opNorm ((b n : A) - a)
      rw [hφ_norm n, one_mul, PositiveContinuousLinearMap.coe_toContinuousLinearMap, map_sub,
        hφ_val n, hφn0, sub_zero, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)] at h1
      exact h1
    have htri : ‖a‖ ≤ ‖(b n : A)‖ + ‖(b n : A) - a‖ := by
      simpa only [norm_sub_rev] using norm_le_norm_add_norm_sub' a (b n : A)
    linarith

end TauCeti.CStarAlgebra
