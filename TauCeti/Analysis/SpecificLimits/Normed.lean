/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
# Geometric series in seminormed rings and normed fields

The norms of the powers of an element in the open unit ball form a summable series, even when
the seminorm is not normalized. The same holds after multiplication by bounded coefficients.
Completeness then gives summability in the ring itself.

Over a normed field, the evaluations below specialize Mathlib's binomial geometric-series
formula to linear and quadratic coefficients, without requiring completeness or an ultrametric
norm. Finite products of geometric series converge unconditionally over all exponent vectors,
giving the product Cauchy kernel expansion.
-/

public section

namespace TauCeti

/-- The norms of the powers of an element in the open unit ball are summable in a seminormed
ring, without requiring a normalized seminorm. -/
theorem summable_norm_pow_of_norm_lt_one {K : Type*} [SeminormedRing K]
    {q : K} (hq : ‖q‖ < 1) : Summable (fun n : ℕ ↦ ‖q ^ n‖) := by
  -- The positive-degree estimate does not require any bound on the seminorm of one.
  rw [← summable_nat_add_iff 1]
  exact Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun n ↦ norm_pow_le' q n.succ_pos)
    ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg q) hq))

/-- A geometric series with bounded coefficients is absolutely summable in a seminormed ring
when the parameter belongs to the open unit ball. -/
theorem summable_norm_mul_pow_of_norm_le {K : Type*} [SeminormedRing K]
    {b : ℕ → K} {C : ℝ} (hb : ∀ n, ‖b n‖ ≤ C) {q : K} (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ ↦ ‖b n * q ^ n‖) := by
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
    ((summable_norm_pow_of_norm_lt_one hq).mul_left C)
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hb n) (norm_nonneg _))

/-- A geometric series with bounded coefficients is summable in a complete seminormed ring
when the parameter belongs to the open unit ball. -/
theorem summable_mul_pow_of_norm_le {K : Type*} [SeminormedRing K] [CompleteSpace K]
    {b : ℕ → K} {C : ℝ} (hb : ∀ n, ‖b n‖ ≤ C) {q : K} (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ ↦ b n * q ^ n) :=
  (summable_norm_mul_pow_of_norm_le hb hq).of_norm

variable {K : Type*} [NormedField K]

/-- The geometric series with coefficient and exponent both shifted by one. -/
theorem tsum_natCast_succ_mul_pow_succ (r : K) (hr : ‖r‖ < 1) :
    (∑' d : ℕ, ((d + 1 : ℕ) : K) * r ^ (d + 1)) = r / (1 - r) ^ 2 := by
  calc
    _ = r * ∑' d : ℕ, (((d + 1).choose 1 : ℕ) : K) * r ^ d := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro d
      simp only [Nat.choose_one_right, pow_succ]
      ring
    _ = _ := by rw [tsum_choose_mul_geometric_of_norm_lt_one 1 hr]; ring

/-- The shifted geometric series weighted by `choose (d + 1) 2`. -/
theorem tsum_choose_two_mul_pow_succ (r : K) (hr : ‖r‖ < 1) :
    (∑' d : ℕ, (((d + 1).choose 2 : ℕ) : K) * r ^ (d + 1)) = r ^ 2 / (1 - r) ^ 3 := by
  have ht : Summable (fun d : ℕ ↦ (((d + 1 + 1).choose 2 : ℕ) : K) * r ^ (d + 1 + 1)) := by
    refine ((hasSum_choose_mul_geometric_of_norm_lt_one 2 hr).summable.mul_right (r ^ 2)).congr ?_
    intro d
    rw [Nat.add_assoc, pow_add]
    ring
  rw [tsum_eq_zero_add' (f := fun d : ℕ ↦ (((d + 1).choose 2 : ℕ) : K) * r ^ (d + 1)) ht]
  simp only [Nat.choose_eq_zero_of_lt (by decide : 1 < 2), Nat.cast_zero, zero_mul, zero_add]
  calc
    _ = r ^ 2 * ∑' d : ℕ, (((d + 2).choose 2 : ℕ) : K) * r ^ d := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro d
      rw [Nat.add_assoc, pow_add]
      ring
    _ = _ := by rw [tsum_choose_mul_geometric_of_norm_lt_one 2 hr]; ring

/-- The shifted geometric series weighted by `-choose (d + 2) 2`. -/
theorem tsum_neg_choose_two_mul_pow_succ (r : K) (hr : ‖r‖ < 1) :
    (∑' d : ℕ, -((((d + 1 + 1).choose 2 : ℕ) : K)) * r ^ (d + 1)) =
      -r / (1 - r) ^ 3 := by
  calc
    _ = -r * ∑' d : ℕ, (((d + 2).choose 2 : ℕ) : K) * r ^ d := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro d
      rw [Nat.add_assoc, pow_succ]
      ring
    _ = _ := by rw [tsum_choose_mul_geometric_of_norm_lt_one 2 hr]; ring

/-- The product of finitely many geometric series, indexed by all exponent vectors.
The index type may be empty. -/
theorem hasSum_prod_geometric_of_norm_lt_one {𝕜 ι : Type*} [NormedField 𝕜]
    [Fintype ι] {r : ι → 𝕜} (hr : ∀ i, ‖r i‖ < 1) :
    HasSum (fun α : ι → ℕ ↦ ∏ i, r i ^ α i) (∏ i, (1 - r i)⁻¹) := by
  classical
  -- First obtain the nonnegative majorant needed for absolute summability.
  have hnonneg : ∀ n (q : Fin n → ℝ), (∀ i, 0 ≤ q i) → (∀ i, q i < 1) →
      Summable (fun α : Fin n → ℕ ↦ ∏ i, q i ^ α i) := by
    intro n
    induction n with
    | zero => intro q _ _; exact (hasSum_fintype _).summable
    | succ n ih =>
      intro q hq hq'
      apply (Fin.consEquiv (fun _ : Fin (n + 1) ↦ ℕ)).summable_iff.mp
      simpa only [Function.comp_def, Fin.consEquiv_apply, Fin.prod_univ_succ,
        Fin.cons_zero, Fin.cons_succ] using
        (summable_geometric_of_lt_one (hq 0) (hq' 0)).mul_of_nonneg
          (ih (fun i ↦ q i.succ) (fun i ↦ hq i.succ) (fun i ↦ hq' i.succ))
          (fun k ↦ pow_nonneg (hq 0) k)
          (fun α ↦ Finset.prod_nonneg fun i _ ↦ pow_nonneg (hq i.succ) (α i))
  -- Multiply the geometric sums one coordinate at a time.
  have hfin : ∀ n (q : Fin n → 𝕜), (∀ i, ‖q i‖ < 1) →
      HasSum (fun α : Fin n → ℕ ↦ ∏ i, q i ^ α i) (∏ i, (1 - q i)⁻¹) := by
    intro n
    induction n with
    | zero => intro q _; simp
    | succ n ih =>
      intro q hq
      have h₀ := hasSum_geometric_of_norm_lt_one (hq 0)
      have ht := ih (fun i ↦ q i.succ) (fun i ↦ hq i.succ)
      have hn₀ : Summable (fun k : ℕ ↦ ‖q 0 ^ k‖) := by
        simpa only [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) (hq 0)
      have hnt : Summable (fun α : Fin n → ℕ ↦ ‖∏ i, q i.succ ^ α i‖) := by
        simpa only [norm_prod, norm_pow] using
          hnonneg n (fun i ↦ ‖q i.succ‖) (fun i ↦ norm_nonneg _) (fun i ↦ hq i.succ)
      have hm : Summable (fun a : ℕ × (Fin n → ℕ) ↦
          q 0 ^ a.1 * ∏ i, q i.succ ^ a.2 i) :=
        summable_mul_of_summable_norm'
          (f := fun k : ℕ ↦ q 0 ^ k) (g := fun α : Fin n → ℕ ↦ ∏ i, q i.succ ^ α i)
          hn₀ h₀.summable hnt ht.summable
      have hmul := h₀.mul ht hm
      apply (Fin.consEquiv (fun _ : Fin (n + 1) ↦ ℕ)).hasSum_iff.mp
      simpa only [Function.comp_def, Fin.consEquiv_apply, Fin.prod_univ_succ,
        Fin.cons_zero, Fin.cons_succ] using
        hmul
  -- Reindex the result from finite tuples to the requested finite index type.
  let e := Fintype.equivFin ι
  have hp (α : ι → ℕ) : (∏ i, r i ^ α i) = ∏ j, r (e.symm j) ^ α (e.symm j) :=
    Fintype.prod_equiv e _ _ (fun i ↦ by simp)
  have hc : (∏ i, (1 - r i)⁻¹) = ∏ j, (1 - r (e.symm j))⁻¹ :=
    Fintype.prod_equiv e _ _ (fun i ↦ by simp)
  rw [hc]
  apply (Equiv.piCongrLeft (fun _ : Fin (Fintype.card ι) ↦ ℕ) e).symm.hasSum_iff.mp
  simpa only [Function.comp_def, hp, Equiv.piCongrLeft_symm_apply,
    Equiv.apply_symm_apply] using hfin (Fintype.card ι) (fun j ↦ r (e.symm j))
      (fun j ↦ hr (e.symm j))

/-- A finite product of shifted reciprocal kernels expands into geometric series whenever
in each coordinate the displacement has smaller norm than the denominator. -/
theorem hasSum_prod_geometric_div {𝕜 ι : Type*} [NormedField 𝕜] [Fintype ι]
    {z w : ι → 𝕜} (hw : ∀ i, ‖w i‖ < ‖z i‖) :
    HasSum (fun α : ι → ℕ ↦ ∏ i, (w i / z i) ^ α i / z i)
      (∏ i, (z i - w i)⁻¹) := by
  have hne (i) : z i ≠ 0 := norm_ne_zero_iff.mp
    ((norm_nonneg _).trans_lt (hw i)).ne'
  have hg := hasSum_prod_geometric_of_norm_lt_one (r := fun i ↦ w i / z i)
    (fun i ↦ by rw [norm_div]; exact (div_lt_one (norm_pos_iff.mpr (hne i))).mpr (hw i))
  have heq (i) : (1 - w i / z i)⁻¹ / z i = (z i - w i)⁻¹ := by
    field_simp [hne i]
  convert hg.mul_right (∏ i, (z i)⁻¹) using 1
  · ext α
    simp only [← Finset.prod_mul_distrib, div_eq_mul_inv]
  · simp only [← Finset.prod_mul_distrib, ← div_eq_mul_inv, heq]

end TauCeti

end
