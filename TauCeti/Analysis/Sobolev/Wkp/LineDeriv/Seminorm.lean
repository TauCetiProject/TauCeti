/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.LineDeriv.Contraction
public import TauCeti.Analysis.Sobolev.Wkp.Seminorm
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Sobolev seminorms and iterated directional derivatives

The top Sobolev seminorm and the sum of the `Lᵖ` norms of its scalar components in an
orthonormal basis control one another. The comparison allows estimates on scalar
directional derivatives to be used for the full weak derivative. Taking any number of
directional derivatives also bounds each remaining seminorm by the corresponding
higher seminorm of the original function times the product of the direction norms.
Both estimates include `p = ∞`.

The use of scalar components for polynomial approximation follows Brenner and Scott,
*The Mathematical Theory of Finite Element Methods*, 3rd ed., §4.3.
-/

public section

namespace TauCeti.Wkp

open MeasureTheory TopologicalSpace
open scoped ENNReal

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {Ω : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {ι : Type*} [Fintype ι]

/-- The top Sobolev seminorm is bounded by the sum of the `Lᵖ` norms of all iterated
directional derivatives of that order along a finite orthonormal basis. -/
theorem norm_iteratedGradient_le_sum_norm_iteratedLineDerivZeroL (j : ℕ)
    (b : OrthonormalBasis ι ℝ E) (u : Wkp μ Ω p (j + 1)) :
    ‖iteratedGradient j u‖ ≤
      ∑ r : Fin (j + 1) → ι, ‖iteratedLineDerivZeroL (j + 1) (b ∘ r) u‖ := by
  let D (r : Fin (j + 1) → ι) : Lp ℝ p (μ.restrict Ω) :=
    iteratedLineDerivZeroL (j + 1) (b ∘ r) u
  have hD (r : Fin (j + 1) → ι) :
      ∀ᵐ x ∂μ.restrict Ω,
        D r x = IteratedGradient.evalTupleL j (b ∘ r) (iteratedGradient j u x) := by
    have hrev : ((b ∘ r) ∘ Fin.revPerm) ∘ Fin.rev = b ∘ r :=
      funext fun i ↦ congrArg (b ∘ r) (Fin.rev_rev i)
    simpa only [D, iteratedLineDerivZeroL_comp_perm, hrev] using
      iteratedLineDerivZeroL_succ_ae j ((b ∘ r) ∘ Fin.revPerm) u
  calc
    ‖iteratedGradient j u‖ ≤ ‖∑ r, Lp.normLp (D r)‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun r ↦ Lp.normLp (D r)),
        ae_all_iff.2 (fun r ↦ Lp.coeFn_normLp (D r)), ae_all_iff.2 hD] with x hsum hnorm hx
      simp only [hsum, hnorm, hx]
      exact (IteratedGradient.norm_le_sum_norm_evalTupleL_apply_orthonormalBasis j
        (iteratedGradient j u x) b).trans (Real.le_norm_self _)
    _ ≤ ∑ r, ‖D r‖ := by simpa only [Lp.norm_normLp] using norm_sum_le _ (fun r ↦ Lp.normLp (D r))

/-- For an orthonormal basis of size `n`, the sum of the `Lᵖ` norms of all order-`(j + 1)`
directional components is at most `n ^ (j + 1)` times the top Sobolev seminorm. -/
theorem sum_norm_iteratedLineDerivZeroL_le (j : ℕ) (b : OrthonormalBasis ι ℝ E)
    (u : Wkp μ Ω p (j + 1)) :
    ∑ r : Fin (j + 1) → ι, ‖iteratedLineDerivZeroL (j + 1) (b ∘ r) u‖ ≤
      (Fintype.card ι : ℝ) ^ (j + 1) * ‖iteratedGradient j u‖ := by
  calc
    _ ≤ ∑ _r : Fin (j + 1) → ι, ‖iteratedGradient j u‖ := by
      refine Finset.sum_le_sum fun r _ ↦
        (norm_iteratedLineDerivZeroL_succ_apply_le j (b ∘ r) u).trans_eq ?_
      simp [Function.comp_apply, b.orthonormal.1]
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]

/-- After differentiating along `j` directions, the order-`i` Sobolev seminorm is at most
the order-`(i + j)` seminorm of the original function times the product of the direction norms. -/
theorem seminorm_iteratedLineDerivL_le {i k : ℕ} (hi : i ≤ k) :
    ∀ (j : ℕ) (m : Fin j → E) (u : Wkp μ Ω p (k + j)),
      seminorm k i hi (iteratedLineDerivL k j m u) ≤
        (∏ r, ‖m r‖) * seminorm (k + j) (i + j) (Nat.add_le_add_right hi j) u
  | 0, m, u => by simp
  | j + 1, m, u => by
      rw [iteratedLineDerivL_succ, ContinuousLinearMap.comp_apply, Fin.prod_univ_succ]
      refine (seminorm_iteratedLineDerivL_le hi j (Fin.tail m) _).trans ?_
      refine (mul_le_mul_of_nonneg_left (seminorm_lineDerivL_le (m 0) (Nat.add_le_add_right hi j) u)
        (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)).trans_eq ?_
      simp only [Fin.tail_def]
      ac_rfl

end TauCeti.Wkp
