/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TreeWalk.Leading
public import TauCeti.Data.Nat.Factorial.Basic
public import TauCeti.Probability.RandomMatrix.MomentBounds

/-!
# Leading trace words and expected even moments of Wigner matrices

In a leading cyclic word `w : Fin (2 * m) → Fin n` — a closed walk of length `2 * m` with no
singleton unordered edge that visits `m + 1` vertices — pairing each discovery step of
`TreeWalk.cyclicPath w` with its reverse (`integral_prod_wignerMatrix_apply_leading`) reduces the
expected product of Wigner entries along `w` to the product of the second absolute moments at its
`m` discovery steps. Since each discovery step reads an off-diagonal entry whose squared norm has
expectation `n⁻¹ s`, every leading word contributes `((n : ℂ)⁻¹ * s) ^ m` whenever the off-diagonal
coordinates in the `n × n` corner have common second absolute moment `s`
(`integral_prod_wignerMatrix_apply_leading_of_integral_norm_sq_eq`).

Summing over the `catalan m * n.descFactorial (m + 1)` leading cyclic words and combining with the
nonleading trace-word bound from `TauCeti.Probability.RandomMatrix.MomentBounds` and the
falling-factorial collision estimate `n ^ (m + 1) - n.descFactorial (m + 1) ≤ ((m + 1).choose 2) *
n ^ m` gives an explicit `O(n⁻¹)` finite-`n` bound on the distance between the expected normalized
even trace `n⁻¹ E[tr(Hₙ ^ (2 * m))]` and `s ^ m * catalan m`, valid for every `m : ℕ` (including
`m = 0`) and without assuming identically distributed entries.

## Main results

* `TauCeti.sum_integral_prod_wignerMatrix_leading` and
  `TauCeti.norm_inv_mul_sum_integral_prod_wignerMatrix_leading_sub_le`: for `m ≠ 0`, the sum of
  expected Wigner entry products over all leading cyclic words of length `2 * m` is
  `(catalan m * n.descFactorial (m + 1)) * ((n : ℂ)⁻¹ * s) ^ m`, so its `n⁻¹`-normalized value lies
  within `s ^ m * catalan m * (m + 1).choose 2 / n` of `s ^ m * catalan m`.
* `TauCeti.norm_inv_mul_integral_trace_pow_two_mul_wignerMatrix_sub_le`: quantitative `O(n⁻¹)`
  bound between `n⁻¹ E[tr(Hₙ ^ (2 * m))]` and `s ^ m * catalan m`.
* `TauCeti.tendsto_inv_mul_integral_trace_pow_two_mul_wignerMatrix`: `n⁻¹ E[tr(Hₙ ^ (2 * m))]`
  converges to `s ^ m * catalan m` as `n → ∞`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3, Lemma 2.1.6.
-/

public section

open MeasureTheory ProbabilityTheory Matrix Finset Filter
open scoped Topology

namespace TauCeti

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ξ : StrictUpper → Ω → ℂ}
  {η : ℕ → Ω → ℝ}

/-- For `m ≠ 0`, the sum of expected Wigner entry products over all leading cyclic words of length
`2 * m` is `(catalan m * n.descFactorial (m + 1)) * ((n : ℂ)⁻¹ * s) ^ m` whenever the strictly
upper coordinates in the `n × n` corner are independent and have common second absolute moment
`s`. -/
theorem sum_integral_prod_wignerMatrix_leading {m n : ℕ} (hm : m ≠ 0) {s : ℝ}
    (hξ : ∀ ij : StrictUpper, ij.1.2 < n → AEStronglyMeasurable (fun ω ↦ ‖ξ ij ω‖ ^ 2) P)
    (hξindep : iIndepFun (fun ij : {ij : StrictUpper // ij.1.2 < n} ↦ ξ ij.1) P)
    (hξsq : ∀ ij : StrictUpper, ij.1.2 < n → ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = s) :
    (∑ w : Fin (2 * m) → Fin n with
      (∀ t, ∃ r ≠ t, s(w r, w (finRotate (2 * m) r)) = s(w t, w (finRotate (2 * m) t))) ∧
        #(univ.image w) = m + 1,
      ∫ ω, ∏ t, wignerMatrix ξ η n ω (w t) (w (finRotate (2 * m) t)) ∂P) =
      (catalan m * n.descFactorial (m + 1) : ℕ) * ((n : ℂ)⁻¹ * s) ^ m := by
  rw [sum_congr rfl fun w hw ↦
    integral_prod_wignerMatrix_apply_leading_of_integral_norm_sq_eq hξ hξindep hξsq w
      (mem_filter.mp hw).2.1 (mem_filter.mp hw).2.2,
    sum_const, nsmul_eq_mul, TreeWalk.card_filter_leading_cyclic_word hm, Fintype.card_fin]

/-- For `m ≠ 0` and `n ≠ 0`, normalizing the leading Wigner trace-word sum by `n⁻¹` approximates
`s ^ m * catalan m` up to the vertex-collision error `s ^ m * catalan m * (m + 1).choose 2 / n`
whenever `0 ≤ s` and the strictly upper coordinates in the `n × n` corner are independent with
common second absolute moment `s`. Neither centering nor any assumption on the diagonal entries is
needed. -/
theorem norm_inv_mul_sum_integral_prod_wignerMatrix_leading_sub_le {m n : ℕ} (hm : m ≠ 0)
    (hn : n ≠ 0) {s : ℝ} (hs : 0 ≤ s)
    (hξ : ∀ ij : StrictUpper, ij.1.2 < n → AEStronglyMeasurable (fun ω ↦ ‖ξ ij ω‖ ^ 2) P)
    (hξindep : iIndepFun (fun ij : {ij : StrictUpper // ij.1.2 < n} ↦ ξ ij.1) P)
    (hξsq : ∀ ij : StrictUpper, ij.1.2 < n → ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = s) :
    ‖(n : ℂ)⁻¹ * (∑ w : Fin (2 * m) → Fin n with
        (∀ t, ∃ r ≠ t, s(w r, w (finRotate (2 * m) r)) = s(w t, w (finRotate (2 * m) t))) ∧
          #(univ.image w) = m + 1,
        ∫ ω, ∏ t, wignerMatrix ξ η n ω (w t) (w (finRotate (2 * m) t)) ∂P) -
      (s : ℂ) ^ m * catalan m‖ ≤
      s ^ m * catalan m * (m + 1).choose 2 / n := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hdesc_le : (n.descFactorial (m + 1) : ℝ) ≤ (n : ℝ) ^ (m + 1) := by
    exact_mod_cast Nat.descFactorial_le_pow n (m + 1)
  have hpow_sub : (n : ℝ) ^ (m + 1) - n.descFactorial (m + 1) ≤
      ((m + 1).choose 2 : ℝ) * (n : ℝ) ^ m := by
    have hcast : (n : ℝ) ^ (m + 1) ≤
        (n.descFactorial (m + 1) : ℝ) + ((m + 1).choose 2 : ℝ) * (n : ℝ) ^ m := by
      exact_mod_cast Nat.pow_succ_le_descFactorial_succ_add n m
    linarith
  have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hexpr : (n : ℂ)⁻¹ * (∑ w : Fin (2 * m) → Fin n with
        (∀ t, ∃ r ≠ t, s(w r, w (finRotate (2 * m) r)) = s(w t, w (finRotate (2 * m) t))) ∧
          #(univ.image w) = m + 1,
        ∫ ω, ∏ t, wignerMatrix ξ η n ω (w t) (w (finRotate (2 * m) t)) ∂P) -
      (s : ℂ) ^ m * catalan m =
      (((s ^ m * catalan m * ((n.descFactorial (m + 1) : ℝ) - (n : ℝ) ^ (m + 1)) /
        (n : ℝ) ^ (m + 1)) : ℝ) : ℂ) := by
    rw [sum_integral_prod_wignerMatrix_leading hm hξ hξindep hξsq, mul_pow, inv_pow]
    push_cast
    field_simp [hnc]
    ring
  rw [hexpr, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul,
    abs_of_nonneg (mul_nonneg (pow_nonneg hs m) (Nat.cast_nonneg _)),
    abs_of_pos (pow_pos hn_pos (m + 1)), abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hdesc_le)]
  calc s ^ m * catalan m * ((n : ℝ) ^ (m + 1) - n.descFactorial (m + 1)) / (n : ℝ) ^ (m + 1)
      ≤ s ^ m * catalan m * (((m + 1).choose 2 : ℝ) * (n : ℝ) ^ m) / ((n : ℝ) ^ m * n) := by
        rw [pow_succ (n : ℝ) m]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow_sub (by positivity)) (by positivity)
    _ = s ^ m * catalan m * (m + 1).choose 2 / n := by
        have hnm : (n : ℝ) ^ m ≠ 0 := (pow_pos hn_pos m).ne'
        field_simp [hnm, hn_pos.ne']

/-- **Quantitative expected even-moment bound for Wigner matrices.** For independent centered
entries in the `n × n` corner whose `2m`th absolute moments are uniformly bounded by `B` and whose
strictly upper entries have common second absolute moment `s ≥ 0`, the normalized expected `2m`th
trace of the `n × n` Wigner matrix (`n ≠ 0`) lies within
`((m ^ (2 * m) * B + s ^ m * catalan m * (m + 1).choose 2) / n)` of `s ^ m * catalan m`. All
`m : ℕ` (including `m = 0`) are covered, and identical distribution is not required. -/
theorem norm_inv_mul_integral_trace_pow_two_mul_wignerMatrix_sub_le {m n : ℕ} (hn : n ≠ 0)
    {B s : ℝ} (hs : 0 ≤ s)
    (hindep : iIndepFun
      (fun r : {ij : StrictUpper // ij.1.2 < n} ⊕ {i : ℕ // i < n} ↦
        Sum.elim (fun ij ↦ ξ ij.1) (fun i ω ↦ (η i.1 ω : ℂ)) r) P)
    (hξzero : ∀ ij : StrictUpper, ij.1.2 < n → ∫ ω, ξ ij ω ∂P = 0)
    (hηzero : ∀ i < n, ∫ ω, η i ω ∂P = 0)
    (hξp : ∀ ij : StrictUpper, ij.1.2 < n → MemLp (ξ ij) (2 * m : ℕ) P)
    (hηp : ∀ i < n, MemLp (η i) (2 * m : ℕ) P)
    (hξ : ∀ ij : StrictUpper, ij.1.2 < n → ∫ ω, ‖ξ ij ω‖ ^ (2 * m) ∂P ≤ B)
    (hη : ∀ i < n, ∫ ω, ‖η i ω‖ ^ (2 * m) ∂P ≤ B)
    (hξsq : ∀ ij : StrictUpper, ij.1.2 < n → ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = s) :
    ‖(n : ℂ)⁻¹ * (∫ ω, (wignerMatrix ξ η n ω ^ (2 * m)).trace ∂P) -
      (s : ℂ) ^ m * catalan m‖ ≤
      ((m : ℝ) ^ (2 * m) * B + s ^ m * catalan m * (m + 1).choose 2) / n := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have hB : 0 ≤ B :=
    (integral_nonneg fun _ ↦ by positivity).trans (hη 0 (Nat.pos_of_ne_zero hn))
  rcases eq_or_ne m 0 with rfl | hm
  · have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    simp only [Nat.mul_zero, pow_zero, Matrix.trace_one, Fintype.card_fin, integral_const,
      probReal_univ, one_smul, inv_mul_cancel₀ hnc, catalan_zero, Nat.cast_one, mul_one, sub_self,
      norm_zero, Nat.cast_zero, one_mul, zero_add, Nat.choose_succ_self, add_zero]
    exact div_nonneg hB (Nat.cast_nonneg n)
  · classical
    let L : ℂ := ∑ w : Fin (2 * m) → Fin n with
      (∀ t, ∃ r ≠ t, s(w r, w (finRotate (2 * m) r)) = s(w t, w (finRotate (2 * m) t))) ∧
        #(univ.image w) = m + 1,
      ∫ ω, ∏ t, wignerMatrix ξ η n ω (w t) (w (finRotate (2 * m) t)) ∂P
    have h2m : 2 * m ≠ 0 := Nat.mul_ne_zero (by decide) hm
    have hrem : ‖(n : ℂ)⁻¹ * ((∫ ω, (wignerMatrix ξ η n ω ^ (2 * m)).trace ∂P) - L)‖ ≤
        (m : ℝ) ^ (2 * m) * B / n := by
      have hrem' := norm_inv_mul_integral_trace_pow_two_mul_wignerMatrix_sub_sum_le (n := n)
        (ξ := fun ij ↦ if ij.1.2 < n then ξ ij else 0)
        (η := fun i ↦ if i < n then η i else 0)
        (iIndepFun_sumElim_ofReal_ite_lt hindep)
        (fun ij ↦ by by_cases h : ij.1.2 < n <;> simp [h, hξzero])
        (fun i ↦ by by_cases h : i < n <;> simp [h, hηzero])
        hm
        (fun ij ↦ by
          by_cases h : ij.1.2 < n
          · simpa [h] using hξp ij h
          · simp [h, MemLp.zero])
        (fun i ↦ by
          by_cases h : i < n
          · simpa [h] using hηp i h
          · simp [h, MemLp.zero])
        (fun ij ↦ by
          by_cases h : ij.1.2 < n
          · simpa [h] using hξ ij h
          · simpa [h, zero_pow h2m] using hB)
        (fun i ↦ by
          by_cases h : i < n
          · simpa [h] using hη i h
          · simpa [h, zero_pow h2m] using hB)
      simpa only [wignerMatrix_ite_lt] using hrem'
    have hlead : ‖(n : ℂ)⁻¹ * L - (s : ℂ) ^ m * catalan m‖ ≤
        s ^ m * catalan m * (m + 1).choose 2 / n :=
      norm_inv_mul_sum_integral_prod_wignerMatrix_leading_sub_le hm hn hs
        (fun ij hij ↦
          (continuous_norm.pow 2).comp_aestronglyMeasurable (hξp ij hij).aestronglyMeasurable)
        (iIndepFun.precomp (g := Sum.inl) Sum.inl_injective hindep) hξsq
    have hsplit : (n : ℂ)⁻¹ * (∫ ω, (wignerMatrix ξ η n ω ^ (2 * m)).trace ∂P) -
        (s : ℂ) ^ m * catalan m =
        (n : ℂ)⁻¹ * ((∫ ω, (wignerMatrix ξ η n ω ^ (2 * m)).trace ∂P) - L) +
          ((n : ℂ)⁻¹ * L - (s : ℂ) ^ m * catalan m) := by
      ring
    rw [hsplit]
    calc ‖(n : ℂ)⁻¹ * ((∫ ω, (wignerMatrix ξ η n ω ^ (2 * m)).trace ∂P) - L) +
            ((n : ℂ)⁻¹ * L - (s : ℂ) ^ m * catalan m)‖
        ≤ ‖(n : ℂ)⁻¹ * ((∫ ω, (wignerMatrix ξ η n ω ^ (2 * m)).trace ∂P) - L)‖ +
            ‖(n : ℂ)⁻¹ * L - (s : ℂ) ^ m * catalan m‖ := norm_add_le _ _
      _ ≤ (m : ℝ) ^ (2 * m) * B / n + s ^ m * catalan m * (m + 1).choose 2 / n :=
          add_le_add hrem hlead
      _ = ((m : ℝ) ^ (2 * m) * B + s ^ m * catalan m * (m + 1).choose 2) / n :=
          (add_div _ _ _).symm

/-- **Expected even Wigner trace moments converge to Catalan numbers.** Under independent centered
entries with uniformly bounded `2m`th absolute moments and common off-diagonal second absolute
moment `s`, `n⁻¹ E[tr(Hₙ ^ (2 * m))]` tends to `s ^ m * catalan m` as `n → ∞` (for every `m : ℕ`).
-/
theorem tendsto_inv_mul_integral_trace_pow_two_mul_wignerMatrix {m : ℕ} {B s : ℝ}
    (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦ Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
    (hξzero : ∀ ij, ∫ ω, ξ ij ω ∂P = 0) (hηzero : ∀ i, ∫ ω, η i ω ∂P = 0)
    (hξp : ∀ ij, MemLp (ξ ij) (2 * m : ℕ) P) (hηp : ∀ i, MemLp (η i) (2 * m : ℕ) P)
    (hξ : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ (2 * m) ∂P ≤ B)
    (hη : ∀ i, ∫ ω, ‖η i ω‖ ^ (2 * m) ∂P ≤ B)
    (hξsq : ∀ ij, ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = s) :
    Tendsto (fun n : ℕ ↦ (n : ℂ)⁻¹ * ∫ ω, (wignerMatrix ξ η n ω ^ (2 * m)).trace ∂P)
      atTop (𝓝 ((s : ℂ) ^ m * catalan m)) := by
  have hs : 0 ≤ s := by
    rw [← hξsq ⟨(0, 1), Nat.zero_lt_one⟩]
    exact integral_nonneg fun _ ↦ sq_nonneg _
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ ↦
      ((m : ℝ) ^ (2 * m) * B + s ^ m * catalan m * (m + 1).choose 2) / n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact norm_inv_mul_integral_trace_pow_two_mul_wignerMatrix_sub_le hn hs
    ((iIndepFun.precomp
        (Sum.map_injective.mpr ⟨Subtype.val_injective, Subtype.val_injective⟩) hindep).congr
      fun r ↦ .of_forall fun _ ↦ by rcases r with ij | i <;> rfl)
    (fun ij _ ↦ hξzero ij) (fun i _ ↦ hηzero i)
    (fun ij _ ↦ hξp ij) (fun i _ ↦ hηp i)
    (fun ij _ ↦ hξ ij) (fun i _ ↦ hη i) (fun ij _ ↦ hξsq ij)

end TauCeti
