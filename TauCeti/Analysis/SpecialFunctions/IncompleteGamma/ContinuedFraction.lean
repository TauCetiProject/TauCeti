/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.ContinuedFractions.ReductionOfOrder
public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Lower
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Kummer.Contiguous
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Kummer.Limit
import TauCeti.Analysis.Asymptotics.Sum.Divergence

/-!
# The continued fraction of Tricomi's incomplete Gamma function

For every complex parameter `a ∉ {-1, -2, …}` (that is, `∀ k : ℕ, a + 1 ≠ -k`) and every `z : ℂ`,
the continued fraction DLMF 8.9.1 with head `0`, partial denominators `b₁ = 1`,
`bₙ = a + n - 1` (`n ≥ 2`), and partial numerators `a₁ = 1`, `a₂ = -z`,
`a_{2k} = -(a + k - 1) z` (`k ≥ 2`), `a_{2k + 1} = k z` (`k ≥ 1`) converges to
`Γ(a + 1) e^z γ*(a, z)`.

Following Gautschi (1967), the file introduces the explicit Kummer sequence
`f(n) = tricomiContFractSol a z n` solving the three-term recurrence
`y(n + 1) = bₙ y(n) + aₙ y(n - 1)` (`n ≥ 1`), normalized by `f(0) = 1` and expressed through
Mathlib's regularized Kummer function `𝐌(⌈n / 2⌉, a + n, z) = regularizedHGFun {⌈n / 2⌉} {a + n} z`
so that `-f(1) = Γ(a + 1) 𝐌(1, a + 1, z) = Γ(a + 1) e^z γ*(a, z)`. At `z = 0`, all partial
numerators from `a₂` onward vanish and every convergent from index `1` onward equals
`1 = Γ(a + 1) γ*(a, 0)`. For `z ≠ 0`, `f` has the large-index asymptotic
`Γ(a + m) f(m) / ((-1)^m (a₁ ⋯ aₘ) Γ(a + 1)) → e^{z / 2}`, so `f` is eventually nonzero and its
reduction-of-order partial sums `∑_{m = N}^{n - 1} (-1)^m (a₁ ⋯ aₘ) / (f(m) f(m + 1))` diverge in
norm, giving eventual nonvanishing of the continuant denominators and convergence of the
continued fraction via `TauCeti.tendsto_convs_contFrac_of_tendsto_norm_sum`.

## Main definitions

* `Complex.tricomiContFractNum a z` — the 1-indexed partial numerators of DLMF 8.9.1.
* `Complex.tricomiContFractDen a` — the 1-indexed partial denominators of DLMF 8.9.1.
* `Complex.tricomiContFract a z` — the `GenContFract ℂ` of DLMF 8.9.1, defined through
  `TauCeti.contFrac`.
* `Complex.tricomiContFractSol a z` — the explicit Kummer solution of the recurrence with
  `f(0) = 1`.

## Main results

* `Complex.tricomiContFract_zero_right_convs` — at `z = 0`, the convergents equal `1` for every
  `n ≥ 1` when `a + 1 ∉ -ℕ`.
* `Complex.tricomiContFractSol_recurrence` — `tricomiContFractSol a z` satisfies the three-term
  recurrence `f(n + 1) = bₙ f(n) + aₙ f(n - 1)` for `n ≥ 1` when `a + 1 ∉ -ℕ`.
* `Complex.tendsto_Gamma_mul_tricomiContFractSol_div` — Gautschi's large-index asymptotic
  `Γ(a + m) f(m) / ((-1)^m (a₁ ⋯ aₘ) Γ(a + 1)) → e^{z / 2}` for `a + 1 ∉ -ℕ` and `z ≠ 0`.
* `Complex.eventually_tricomiContFractSol_ne_zero` — `tricomiContFractSol a z n ≠ 0` eventually
  when `a + 1 ∉ -ℕ` and `z ≠ 0`.
* `Complex.tendsto_norm_sum_tricomiContFractSol_atTop` — the reduction-of-order partial sums of
  `tricomiContFractSol a z` tend to infinity in norm when `a + 1 ∉ -ℕ` and `z ≠ 0`.
* `Complex.tendsto_convs_tricomiContFract` — DLMF 8.9.1: for `a + 1 ∉ -ℕ` and every `z : ℂ`,
  `(tricomiContFract a z).dens n` is eventually nonzero and `(tricomiContFract a z).convs`
  converges to `Γ(a + 1) e^z γ*(a, z)`.
* `Complex.tendsto_convs_tricomiContFract_lowerIncompleteGamma` — the `γ(a, z)` form of DLMF 8.9.1
  for `a ∉ -ℕ` and `z ≠ 0`, with limit `a z^{-a} e^z γ(a, z)`.

## References

* *NIST Digital Library of Mathematical Functions*, [§8.9](https://dlmf.nist.gov/8.9).
* W. Gautschi, *Computational aspects of three-term recurrence relations*, SIAM Rev. 9 (1967),
  24–82, §1 and §5.
-/

public section

noncomputable section

open Filter Finset Polynomial
open scoped Nat Topology

namespace Complex

/-! ### Partial numerators, partial denominators, and the continued fraction -/

/-- The 1-indexed partial numerators `aₙ` of the continued fraction DLMF 8.9.1 for Tricomi's
incomplete Gamma function: `a₁ = 1`, `a₂ = -z`, `a_{2k} = -(a + k - 1) z` for `k ≥ 2`, and
`a_{2k + 1} = k z` for `k ≥ 1` (with `a₀ = 0`). -/
def tricomiContFractNum (a z : ℂ) : ℕ → ℂ
  | 0 => 0
  | 1 => 1
  | 2 => -z
  | n + 3 =>
    if Even (n + 3) then -(a + (((n + 3) / 2 : ℕ) : ℂ) - 1) * z
    else (((n + 3) / 2 : ℕ) : ℂ) * z

/-- At index `0`, the 1-indexed sequence `tricomiContFractNum` takes the padding value `0`. -/
@[simp]
theorem tricomiContFractNum_zero (a z : ℂ) : tricomiContFractNum a z 0 = 0 := (rfl)

/-- The first partial numerator `a₁` of DLMF 8.9.1 is `1`. -/
@[simp]
theorem tricomiContFractNum_one (a z : ℂ) : tricomiContFractNum a z 1 = 1 := (rfl)

/-- The second partial numerator `a₂` of DLMF 8.9.1 is `-z`. -/
@[simp]
theorem tricomiContFractNum_two (a z : ℂ) : tricomiContFractNum a z 2 = -z := (rfl)

/-- Unfolding `tricomiContFractNum` at `n + 3`. -/
theorem tricomiContFractNum_add_three (a z : ℂ) (n : ℕ) :
    tricomiContFractNum a z (n + 3) =
      if Even (n + 3) then -(a + (((n + 3) / 2 : ℕ) : ℂ) - 1) * z
      else (((n + 3) / 2 : ℕ) : ℂ) * z := (rfl)

/-- For `k ≥ 2`, the even partial numerator `a_{2k}` of DLMF 8.9.1 is `-(a + k - 1) z`. -/
theorem tricomiContFractNum_two_mul (a z : ℂ) {k : ℕ} (hk : 2 ≤ k) :
    tricomiContFractNum a z (2 * k) = -(a + k - 1) * z := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have heq : 2 * (2 + m) = (2 * m + 1) + 3 := by omega
  have heven : Even ((2 * m + 1) + 3) := ⟨m + 2, by omega⟩
  have hdiv : ((2 * m + 1) + 3) / 2 = 2 + m := by omega
  rw [heq, tricomiContFractNum]
  simp [heven, hdiv]

/-- For `k ≥ 1`, the odd partial numerator `a_{2k + 1}` of DLMF 8.9.1 is `k z`. -/
theorem tricomiContFractNum_two_mul_add_one (a z : ℂ) {k : ℕ} (hk : 1 ≤ k) :
    tricomiContFractNum a z (2 * k + 1) = k * z := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have heq : 2 * (1 + m) + 1 = 2 * m + 3 := by omega
  have hodd : ¬Even (2 * m + 3) := by
    rw [Nat.not_even_iff_odd]
    exact ⟨m + 1, by omega⟩
  have hdiv : (2 * m + 3) / 2 = 1 + m := by omega
  rw [heq, tricomiContFractNum]
  simp [hodd, hdiv]

/-- At `z = 0`, every partial numerator of DLMF 8.9.1 from index `2` onward vanishes. -/
theorem tricomiContFractNum_zero_right (a : ℂ) {n : ℕ} (hn : 2 ≤ n) :
    tricomiContFractNum a 0 n = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  cases m with
  | zero => simp
  | succ m =>
    have heq : 2 + (m + 1) = m + 3 := by omega
    rw [heq, tricomiContFractNum]
    split_ifs <;> simp

/-- When `a + 1 ∉ -ℕ` and `z ≠ 0`, every partial numerator `aₙ` (`n ≥ 1`) of DLMF 8.9.1 is
nonzero. -/
theorem tricomiContFractNum_ne_zero {a z : ℂ} (ha : ∀ k : ℕ, a + 1 ≠ -k) (hz : z ≠ 0)
    {n : ℕ} (hn : 1 ≤ n) : tricomiContFractNum a z n ≠ 0 := by
  rcases eq_or_lt_of_le hn with rfl | hn1
  · simp
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hn1) with rfl | hn2
  · simpa using hz
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [tricomiContFractNum_two_mul a z (by omega)]
    refine mul_ne_zero (neg_ne_zero.2 fun h => ?_) hz
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    exact ha m (by push_cast at h ⊢; linear_combination h)
  · rw [tricomiContFractNum_two_mul_add_one a z (by omega)]
    exact mul_ne_zero (Nat.cast_ne_zero.2 (by omega)) hz

private theorem prod_Icc_tricomiContFractNum_ne_zero {a z : ℂ} (ha : ∀ k : ℕ, a + 1 ≠ -k)
    (hz : z ≠ 0) (m : ℕ) : (∏ j ∈ Icc 1 m, tricomiContFractNum a z j) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ hj =>
    tricomiContFractNum_ne_zero ha hz (Finset.mem_Icc.1 hj).1

private theorem neg_one_pow_mul_prod_Icc_tricomiContFractNum_ne_zero {a z : ℂ}
    (ha : ∀ k : ℕ, a + 1 ≠ -k) (hz : z ≠ 0) (m : ℕ) :
    (-1 : ℂ) ^ m * (∏ j ∈ Icc 1 m, tricomiContFractNum a z j) ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (by norm_num)) (prod_Icc_tricomiContFractNum_ne_zero ha hz m)

/-- The 1-indexed partial denominators `bₙ` of the continued fraction DLMF 8.9.1 for Tricomi's
incomplete Gamma function: `b₁ = 1` and `bₙ = a + n - 1` for `n ≥ 2` (with `b₀ = 0`). -/
def tricomiContFractDen (a : ℂ) : ℕ → ℂ
  | 0 => 0
  | 1 => 1
  | n + 2 => a + (n + 2 : ℕ) - 1

/-- At index `0`, the 1-indexed sequence `tricomiContFractDen` takes the padding value `0`. -/
@[simp]
theorem tricomiContFractDen_zero (a : ℂ) : tricomiContFractDen a 0 = 0 := (rfl)

/-- The first partial denominator `b₁` of DLMF 8.9.1 is `1`. -/
@[simp]
theorem tricomiContFractDen_one (a : ℂ) : tricomiContFractDen a 1 = 1 := (rfl)

/-- For every `n : ℕ`, the partial denominator `b_{n + 2}` of DLMF 8.9.1 is `a + n + 1`. -/
@[simp]
theorem tricomiContFractDen_add_two (a : ℂ) (n : ℕ) :
    tricomiContFractDen a (n + 2) = a + n + 1 := by
  rw [tricomiContFractDen]
  push_cast
  ring

/-- For `n ≥ 2`, the partial denominator `bₙ` of DLMF 8.9.1 is `a + n - 1`. -/
theorem tricomiContFractDen_of_two_le (a : ℂ) {n : ℕ} (hn : 2 ≤ n) :
    tricomiContFractDen a n = a + n - 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [add_comm 2 m, tricomiContFractDen_add_two]
  push_cast
  ring

/-- The generalized continued fraction of DLMF 8.9.1 for `Γ(a + 1) e^z γ*(a, z)`, with head `0`,
partial numerators `tricomiContFractNum a z`, and partial denominators `tricomiContFractDen a`. -/
def tricomiContFract (a z : ℂ) : GenContFract ℂ :=
  TauCeti.contFrac (tricomiContFractNum a z) (tricomiContFractDen a)

/-- Unfolding `tricomiContFract` to `TauCeti.contFrac`. -/
theorem tricomiContFract_def (a z : ℂ) :
    tricomiContFract a z =
      TauCeti.contFrac (tricomiContFractNum a z) (tricomiContFractDen a) := (rfl)

/-- The head term of `tricomiContFract a z` is `0`. -/
@[simp]
theorem tricomiContFract_h (a z : ℂ) : (tricomiContFract a z).h = 0 :=
  TauCeti.contFrac_h _ _

/-- The `n`-th 0-indexed pair of `tricomiContFract a z` consists of `a_{n + 1}` and `b_{n + 1}`. -/
@[simp]
theorem tricomiContFract_s_get? (a z : ℂ) (n : ℕ) :
    (tricomiContFract a z).s.get? n =
      some ⟨tricomiContFractNum a z (n + 1), tricomiContFractDen a (n + 1)⟩ :=
  TauCeti.contFrac_s_get? _ _ n

/-- The infinite continued fraction `tricomiContFract a z` never terminates in `Stream'.Seq`. -/
@[simp]
theorem not_terminatedAt_tricomiContFract (a z : ℂ) (n : ℕ) :
    ¬(tricomiContFract a z).TerminatedAt n :=
  TauCeti.not_terminatedAt_contFrac _ _ n

/-! ### Exact evaluation at `z = 0` -/

/-- At `z = 0`, the `n`-th continuant pair (`n ≥ 1`) of `tricomiContFract a 0` has both entries
equal to the rising factorial `(a + 1)_{n - 1}`. -/
theorem tricomiContFract_zero_right_conts (a : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    (tricomiContFract a 0).conts n =
      ⟨(ascPochhammer ℂ (n - 1)).eval (a + 1), (ascPochhammer ℂ (n - 1)).eval (a + 1)⟩ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  rw [add_comm 1 k, add_tsub_cancel_right]
  induction k using Nat.twoStepInduction with
  | zero =>
    rw [zero_add, GenContFract.first_cont_eq (tricomiContFract_s_get? a 0 0)]
    simp
  | one =>
    have h1 : (tricomiContFract a 0).conts 1 = ⟨1, 1⟩ := by
      rw [GenContFract.first_cont_eq (tricomiContFract_s_get? a 0 0)]
      simp
    rw [GenContFract.conts_recurrence (tricomiContFract_s_get? a 0 1) rfl h1]
    simp
  | more k ih0 ih1 =>
    have hk : k + 2 + 1 = (k + 1) + 2 := by omega
    rw [hk, GenContFract.conts_recurrence (tricomiContFract_s_get? a 0 (k + 1 + 1)) ih0 ih1,
      tricomiContFractNum_zero_right a (by omega), tricomiContFractDen_add_two, zero_mul, add_zero,
      ascPochhammer_succ_eval (n := k + 1)]
    congr 1 <;> (push_cast; ring)

/-- At `z = 0`, the `n`-th continuant numerator (`n ≥ 1`) of `tricomiContFract a 0` is the rising
factorial `(a + 1)_{n - 1}`. -/
theorem tricomiContFract_zero_right_nums (a : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    (tricomiContFract a 0).nums n = (ascPochhammer ℂ (n - 1)).eval (a + 1) := by
  rw [GenContFract.num_eq_conts_a, tricomiContFract_zero_right_conts a hn]

/-- At `z = 0`, the `n`-th continuant denominator (`n ≥ 1`) of `tricomiContFract a 0` is the rising
factorial `(a + 1)_{n - 1}`. -/
theorem tricomiContFract_zero_right_dens (a : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    (tricomiContFract a 0).dens n = (ascPochhammer ℂ (n - 1)).eval (a + 1) := by
  rw [GenContFract.den_eq_conts_b, tricomiContFract_zero_right_conts a hn]

/-- When `a + 1 ∉ -ℕ`, every convergent denominator of `tricomiContFract a 0` is nonzero. -/
theorem tricomiContFract_zero_right_dens_ne_zero {a : ℂ} (ha : ∀ k : ℕ, a + 1 ≠ -k) (n : ℕ) :
    (tricomiContFract a 0).dens n ≠ 0 := by
  rcases n with _ | k
  · simp
  · rw [tricomiContFract_zero_right_dens a (Nat.succ_pos k), Nat.succ_sub_one, ne_eq,
      ascPochhammer_eval_eq_zero_iff]
    rintro ⟨m, _, hm⟩
    exact ha m (by linear_combination hm)

/-- At `z = 0`, every convergent of `tricomiContFract a 0` from index `1` onward equals `1` when
`a + 1 ∉ -ℕ`. -/
theorem tricomiContFract_zero_right_convs {a : ℂ} (ha : ∀ k : ℕ, a + 1 ≠ -k) {n : ℕ} (hn : 1 ≤ n) :
    (tricomiContFract a 0).convs n = 1 := by
  have hd := tricomiContFract_zero_right_dens_ne_zero ha n
  rw [GenContFract.conv_eq_num_div_den, tricomiContFract_zero_right_nums a hn,
    ← tricomiContFract_zero_right_dens a hn, div_self hd]

/-- At `z = 0` and `a + 1 ∉ -ℕ`, the `n`-th convergent (`n ≥ 1`) of `tricomiContFract a 0` equals
`Γ(a + 1) γ*(a, 0)`. -/
theorem tricomiContFract_zero_right_convs_eq_Gamma_mul {a : ℂ} (ha : ∀ k : ℕ, a + 1 ≠ -k) {n : ℕ}
    (hn : 1 ≤ n) :
    (tricomiContFract a 0).convs n = Gamma (a + 1) * tricomiIncompleteGamma a 0 := by
  rw [tricomiContFract_zero_right_convs ha hn, tricomiIncompleteGamma_zero_right,
    mul_inv_cancel₀ (Gamma_ne_zero ha)]

/-! ### The explicit Kummer solution and its three-term recurrence -/

/-- The explicit Kummer sequence solving the three-term recurrence of `tricomiContFract a z`:
`f(0) = 1`, and for `n ≥ 1`,
`f(n) = (-1)^{⌈n / 2⌉} Γ(a + 1) z^{n - 1} dₙ 𝐌(⌈n / 2⌉, a + n, z)`
with `d₁ = 1`, `d_{2k} = (a + 1)_{k - 1} (k - 1)!`, and `d_{2k + 1} = (a + 1)_{k - 1} k!`. -/
def tricomiContFractSol (a z : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 =>
    (-1 : ℂ) ^ ((n + 2) / 2) * Gamma (a + 1) * z ^ n *
      ((ascPochhammer ℂ ((n - 1) / 2)).eval (a + 1) * ((n / 2)! : ℂ)) *
      regularizedHGFun {(((n + 2) / 2 : ℕ) : ℂ)} {a + (n + 1 : ℕ)} z

/-- Normalization of `tricomiContFractSol` at `0`: `f(0) = 1`. -/
@[simp]
theorem tricomiContFractSol_zero (a z : ℂ) : tricomiContFractSol a z 0 = 1 := (rfl)

/-- Unfolding `tricomiContFractSol` at `n + 1` in terms of `regularizedHGFun`. -/
theorem tricomiContFractSol_succ (a z : ℂ) (n : ℕ) :
    tricomiContFractSol a z (n + 1) =
      (-1 : ℂ) ^ ((n + 2) / 2) * Gamma (a + 1) * z ^ n *
        ((ascPochhammer ℂ ((n - 1) / 2)).eval (a + 1) * ((n / 2)! : ℂ)) *
        regularizedHGFun {(((n + 2) / 2 : ℕ) : ℂ)} {a + (n + 1 : ℕ)} z := (rfl)

/-- Value of `tricomiContFractSol` at `1`: `f(1) = -Γ(a + 1) 𝐌(1, a + 1, z)`. -/
@[simp]
theorem tricomiContFractSol_one (a z : ℂ) :
    tricomiContFractSol a z 1 = -Gamma (a + 1) * regularizedHGFun {1} {a + 1} z := by
  simp [tricomiContFractSol]

/-- Explicit form of `tricomiContFractSol` at positive even indices `2k` (`k ≥ 1`). -/
theorem tricomiContFractSol_two_mul (a z : ℂ) {k : ℕ} (hk : 1 ≤ k) :
    tricomiContFractSol a z (2 * k) =
      (-1) ^ k * Gamma (a + 1) * z ^ (2 * k - 1) *
        ((ascPochhammer ℂ (k - 1)).eval (a + 1) * ((k - 1)! : ℂ)) *
        regularizedHGFun {(k : ℂ)} {a + (2 * k : ℕ)} z := by
  rcases k with _ | m
  · omega
  · rw [Nat.mul_succ, tricomiContFractSol_succ, Nat.add_sub_assoc (by decide : 1 ≤ 2)]
    simp only [Nat.add_sub_cancel, Nat.add_assoc, Nat.reduceAdd, Nat.reduceSub,
      Nat.mul_add_div (by decide : 0 < 2), Nat.mul_div_right _ (by decide : 0 < 2),
      Nat.reduceDiv, add_zero]

/-- Explicit form of `tricomiContFractSol` at odd indices `2k + 1` (`k ≥ 1`). -/
theorem tricomiContFractSol_two_mul_add_one (a z : ℂ) {k : ℕ} (hk : 1 ≤ k) :
    tricomiContFractSol a z (2 * k + 1) =
      (-1) ^ (k + 1) * Gamma (a + 1) * z ^ (2 * k) *
        ((ascPochhammer ℂ (k - 1)).eval (a + 1) * (k ! : ℂ)) *
        regularizedHGFun {(k + 1 : ℂ)} {a + (2 * k + 1 : ℕ)} z := by
  rcases k with _ | m
  · omega
  · rw [tricomiContFractSol_succ, Nat.mul_succ, ← Nat.cast_add_one (m + 1),
      Nat.add_sub_assoc (by decide : 1 ≤ 2)]
    simp only [Nat.add_sub_cancel, Nat.add_assoc, Nat.reduceAdd, Nat.reduceSub,
      Nat.mul_add_div (by decide : 0 < 2), Nat.reduceDiv, add_zero]

/-- Value of `-tricomiContFractSol` at `1` in terms of `tricomiIncompleteGamma`:
`-f(1) = Γ(a + 1) e^z γ*(a, z)`. -/
theorem neg_tricomiContFractSol_one (a z : ℂ) :
    -tricomiContFractSol a z 1 = Gamma (a + 1) * cexp z * tricomiIncompleteGamma a z := by
  rw [tricomiContFractSol_one, tricomiIncompleteGamma_def, mul_assoc, ← mul_assoc (cexp z),
    ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
  ring

private theorem neg_one_pow_mul_prod_tricomiContFractNum (a z : ℂ) (n : ℕ) :
    (-1 : ℂ) ^ (n + 1) * (∏ j ∈ Icc 1 (n + 1), tricomiContFractNum a z j) =
      (-1 : ℂ) ^ ((n + 2) / 2) * z ^ n *
        ((ascPochhammer ℂ ((n - 1) / 2)).eval (a + 1) * ((n / 2)! : ℂ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcomm :
        (-1 : ℂ) ^ (n + 1) * -1 *
            ((∏ k ∈ Icc 1 (n + 1), tricomiContFractNum a z k) * tricomiContFractNum a z (n + 2)) =
          -tricomiContFractNum a z (n + 2) *
            ((-1 : ℂ) ^ (n + 1) * ∏ k ∈ Icc 1 (n + 1), tricomiContFractNum a z k) := by ring
    rw [pow_succ (-1 : ℂ) (n + 1), prod_Icc_succ_top (by omega), hcomm, ih]
    cases n with
    | zero => simp
    | succ r =>
      rcases Nat.even_or_odd' r with ⟨q, rfl | rfl⟩
      · have hidx : 2 * (q + 1) + 1 = 2 * q + 1 + 2 := by omega
        have hnum : tricomiContFractNum a z (2 * q + 1 + 2) = (q + 1 : ℂ) * z := by
          rw [← hidx, tricomiContFractNum_two_mul_add_one a z (Nat.succ_pos q), Nat.cast_add_one]
        rw [hnum]
        simp only [Nat.add_sub_cancel]
        simp only [Nat.add_assoc, Nat.reduceAdd, Nat.mul_add_div (by decide : 0 < 2),
          Nat.mul_div_right _ (by decide : 0 < 2), Nat.reduceDiv, add_zero, Nat.factorial_succ]
        push_cast
        ring
      · have hidx : 2 * (q + 2) = 2 * q + 1 + 1 + 2 := by omega
        have hnum : tricomiContFractNum a z (2 * q + 1 + 1 + 2) = -(a + 1 + q) * z := by
          rw [← hidx, tricomiContFractNum_two_mul a z (by omega)]
          push_cast
          ring
        rw [hnum]
        simp only [Nat.add_sub_cancel]
        simp only [Nat.add_assoc, Nat.reduceAdd, Nat.mul_add_div (by decide : 0 < 2),
          Nat.reduceDiv, add_zero, ascPochhammer_succ_eval]
        ring

/-- For `m ≥ 1`, `tricomiContFractSol a z m` factors as the signed numerator product times
`Γ(a + 1) 𝐌(⌈m / 2⌉, a + m, z)`:
`f(m) = (-1)^m (∏_{j = 1}^m aⱼ) Γ(a + 1) 𝐌(⌈m / 2⌉, a + m, z)`. -/
theorem tricomiContFractSol_eq_prod_mul (a z : ℂ) {m : ℕ} (hm : 1 ≤ m) :
    tricomiContFractSol a z m =
      ((-1 : ℂ) ^ m * ∏ j ∈ Icc 1 m, tricomiContFractNum a z j) *
        Gamma (a + 1) * regularizedHGFun {(((m + 1) / 2 : ℕ) : ℂ)} {a + m} z := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [add_comm 1 n, neg_one_pow_mul_prod_tricomiContFractNum, tricomiContFractSol]
  have hdiv : (n + 1 + 1) / 2 = (n + 2) / 2 := by omega
  rw [hdiv]
  ring

private theorem regularizedHGFun_tricomi_rel_of_two_le (a z : ℂ) {n : ℕ} (hm : 2 ≤ n) :
    regularizedHGFun {(((n - 1 + 1) / 2 : ℕ) : ℂ)} {a + (n - 1 : ℕ)} z -
        (a + n - 1) * regularizedHGFun {(((n + 1) / 2 : ℕ) : ℂ)} {a + n} z =
      tricomiContFractNum a z (n + 1) *
        regularizedHGFun {(((n + 1 + 1) / 2 : ℕ) : ℂ)} {a + (n + 1 : ℕ)} z := by
  have hn1 : 1 ≤ n := by omega
  have hn_cast : a + ((n - 1 : ℕ) : ℂ) = a + n - 1 := by
    rw [Nat.cast_sub hn1, Nat.cast_one]
    ring
  have hn_succ : a + ((n + 1 : ℕ) : ℂ) = a + n + 1 := by push_cast; ring
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have hk : 1 ≤ k := by omega
    have hnum := tricomiContFractNum_two_mul_add_one a z hk
    have h1 : (2 * k - 1 + 1) / 2 = k := by omega
    have h2 : (2 * k + 1) / 2 = k := by omega
    have h3 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    have hM := regularizedHGFun_singleton_sub_mul (k : ℂ) (a + (2 * k : ℕ) - 1) z
    have hb1 : a + (2 * k : ℕ) - 1 + 1 = a + (2 * k : ℕ) := by ring
    have hb2 : a + (2 * k : ℕ) - 1 + 2 = a + (2 * k : ℕ) + 1 := by ring
    rw [hnum, h1, h2, h3, hn_cast, hn_succ]
    rw [hb1, hb2] at hM
    push_cast at hM ⊢
    linear_combination hM
  · have hidx : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
    have hnum : tricomiContFractNum a z (2 * k + 1 + 1) = -(a + k) * z := by
      rw [← hidx, tricomiContFractNum_two_mul a z (by omega)]
      push_cast
      ring
    have h1 : (2 * k + 1 - 1 + 1) / 2 = k := by omega
    have h2 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    have h3 : (2 * k + 1 + 1 + 1) / 2 = k + 1 := by omega
    have hM := regularizedHGFun_singleton_sub_mul_add_one_left (k : ℂ) (a + (2 * k + 1 : ℕ) - 1) z
    have hb1 : a + (2 * k + 1 : ℕ) - 1 + 1 = a + (2 * k + 1 : ℕ) := by ring
    have hb2 : a + (2 * k + 1 : ℕ) - 1 + 2 = a + (2 * k + 1 : ℕ) + 1 := by ring
    have hab : (k : ℂ) - (a + (2 * k + 1 : ℕ) - 1) = -(a + k) := by push_cast; ring
    rw [hnum, h1, h2, h3, hn_cast, hn_succ]
    rw [hb1, hb2, hab] at hM
    push_cast at hM ⊢
    linear_combination hM

/-- When `a + 1 ∉ -ℕ`, `tricomiContFractSol a z` solves the three-term recurrence
`f(n + 1) = bₙ f(n) + aₙ f(n - 1)` for every `n ≥ 1`. -/
theorem tricomiContFractSol_recurrence {a : ℂ} (ha : ∀ k : ℕ, a + 1 ≠ -k) (z : ℂ) {n : ℕ}
    (hn : 1 ≤ n) :
    tricomiContFractSol a z (n + 1) =
      tricomiContFractDen a n * tricomiContFractSol a z n +
        tricomiContFractNum a z n * tricomiContFractSol a z (n - 1) := by
  rcases eq_or_lt_of_le hn with rfl | hn1
  · have h2 : tricomiContFractSol a z 2 = -Gamma (a + 1) * z * regularizedHGFun {1} {a + 2} z := by
      have ha2_nat : a + ((2 * 1 : ℕ) : ℂ) = a + 2 := by norm_num
      rw [tricomiContFractSol_two_mul a z le_rfl, ha2_nat]
      simp
    have hM := regularizedHGFun_one_singleton_eq_inv_Gamma_add_mul (a + 1) z
    have hG := mul_inv_cancel₀ (Gamma_ne_zero ha)
    have ha2 : a + 1 + 1 = a + 2 := by ring
    rw [ha2] at hM
    rw [h2, tricomiContFractDen_one, tricomiContFractNum_one, tricomiContFractSol_one,
      tricomiContFractSol_zero]
    linear_combination Gamma (a + 1) * hM + hG
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    let P : ℕ → ℂ := fun k => (-1 : ℂ) ^ k * ∏ j ∈ Icc 1 k, tricomiContFractNum a z j
    have hP (k : ℕ) : (-1 : ℂ) ^ k * (∏ j ∈ Icc 1 k, tricomiContFractNum a z j) = P k := rfl
    have hP_step (k : ℕ) : P (k + 1) = -tricomiContFractNum a z (k + 1) * P k := by
      simp only [P, pow_succ, prod_Icc_succ_top (Nat.le_add_left 1 k)]
      ring
    have hm_sub : m + 2 - 1 = m + 1 := by omega
    have hrel := regularizedHGFun_tricomi_rel_of_two_le a z (Nat.le_add_left 2 m)
    rw [hm_sub] at hrel ⊢
    rw [tricomiContFractSol_eq_prod_mul a z (Nat.le_add_left 1 (m + 2)),
      tricomiContFractSol_eq_prod_mul a z hn,
      tricomiContFractSol_eq_prod_mul a z (Nat.le_add_left 1 m),
      tricomiContFractDen_of_two_le a (Nat.le_add_left 2 m),
      hP (m + 2 + 1), hP (m + 2), hP (m + 1), hP_step (m + 2), hP_step (m + 1)]
    linear_combination -tricomiContFractNum a z (m + 2) * P (m + 1) * Gamma (a + 1) * hrel

/-! ### Large-index asymptotic nonvanishing and reduction-of-order divergence -/

/-- Gautschi's large-index asymptotic normalization of `tricomiContFractSol`: when `a + 1 ∉ -ℕ`
and `z ≠ 0`, dividing `Γ(a + m) f(m)` by `(-1)^m (a₁ ⋯ aₘ) Γ(a + 1)` converges to `e^{z / 2}` as
`m → ∞`. -/
theorem tendsto_Gamma_mul_tricomiContFractSol_div {a z : ℂ} (ha : ∀ k : ℕ, a + 1 ≠ -k)
    (hz : z ≠ 0) :
    Tendsto (fun m : ℕ =>
      Gamma (a + m) * tricomiContFractSol a z m /
        (((-1 : ℂ) ^ m * ∏ j ∈ Icc 1 m, tricomiContFractNum a z j) * Gamma (a + 1)))
      atTop (𝓝 (cexp (z / 2))) := by
  have heven : Tendsto (fun k : ℕ =>
      Gamma (a + (2 * k : ℕ)) * regularizedHGFun {(((2 * k + 1) / 2 : ℕ) : ℂ)} {a + (2 * k : ℕ)} z)
      atTop (𝓝 (cexp (z / 2))) := by
    refine (tendsto_Gamma_mul_regularizedHGFun_nhds_exp_div_two a z).congr fun k => ?_
    have hdiv : (2 * k + 1) / 2 = k := by omega
    have hadd : 2 * (k : ℂ) + a = a + (2 * k : ℕ) := by push_cast; ring
    rw [hdiv, hadd]
  have hodd : Tendsto (fun k : ℕ =>
      Gamma (a + (2 * k + 1 : ℕ)) *
        regularizedHGFun {(((2 * k + 1 + 1) / 2 : ℕ) : ℂ)} {a + (2 * k + 1 : ℕ)} z)
      atTop (𝓝 (cexp (z / 2))) := by
    refine ((tendsto_Gamma_mul_regularizedHGFun_nhds_exp_div_two (a - 1) z).comp
      (tendsto_add_atTop_nat 1)).congr fun k => ?_
    simp only [Function.comp_apply]
    have hdiv : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    have hadd : 2 * ((k + 1 : ℕ) : ℂ) + (a - 1) = a + (2 * k + 1 : ℕ) := by push_cast; ring
    rw [hdiv, hadd]
  have hM : Tendsto (fun m : ℕ =>
      Gamma (a + m) * regularizedHGFun {(((m + 1) / 2 : ℕ) : ℂ)} {a + m} z)
      atTop (𝓝 (cexp (z / 2))) :=
    tendsto_iff_eventually.2 fun _ hp =>
      Filter.Eventually.atTop_of_arithmetic (n := 2) (by decide) fun r hr =>
        match r, hr with
        | 0, _ => by simpa only [add_zero] using heven.eventually hp
        | 1, _ => hodd.eventually hp
        | _ + 2, hr => by omega
  refine hM.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hP_ne := prod_Icc_tricomiContFractNum_ne_zero ha hz m
  have hG_ne : Gamma (a + 1) ≠ 0 := Gamma_ne_zero ha
  rw [tricomiContFractSol_eq_prod_mul a z hm]
  field_simp

/-- For `a + 1 ∉ -ℕ` and `z ≠ 0`, `tricomiContFractSol a z n` is eventually nonzero. -/
theorem eventually_tricomiContFractSol_ne_zero {a z : ℂ} (ha : ∀ k : ℕ, a + 1 ≠ -k) (hz : z ≠ 0) :
    ∀ᶠ n in atTop, tricomiContFractSol a z n ≠ 0 := by
  filter_upwards [(tendsto_Gamma_mul_tricomiContFractSol_div ha hz).eventually_ne
    (Complex.exp_ne_zero _)] with m hm h0
  simp [h0] at hm

private theorem tricomiContFract_term_ratio_eq {a z : ℂ} (ha : ∀ k : ℕ, a + 1 ≠ -k) (hz : z ≠ 0)
    {m : ℕ} (hm1 : 1 ≤ m) (hfm : tricomiContFractSol a z m ≠ 0)
    (hfm1 : tricomiContFractSol a z (m + 1) ≠ 0) (hfm2 : tricomiContFractSol a z (m + 2) ≠ 0) :
    ((-1) ^ (m + 1) * (∏ j ∈ Icc 1 (m + 1), tricomiContFractNum a z j) /
        (tricomiContFractSol a z (m + 1) * tricomiContFractSol a z (m + 2))) /
      ((-1) ^ m * (∏ j ∈ Icc 1 m, tricomiContFractNum a z j) /
        (tricomiContFractSol a z m * tricomiContFractSol a z (m + 1))) =
      -((a + m) * (a + m + 1) / tricomiContFractNum a z (m + 2)) *
        ((Gamma (a + m) * tricomiContFractSol a z m /
            (((-1 : ℂ) ^ m * ∏ j ∈ Icc 1 m, tricomiContFractNum a z j) * Gamma (a + 1))) /
          (Gamma (a + (m + 2 : ℕ)) * tricomiContFractSol a z (m + 2) /
            (((-1 : ℂ) ^ (m + 2) * ∏ j ∈ Icc 1 (m + 2), tricomiContFractNum a z j) *
              Gamma (a + 1)))) := by
  have hPm := neg_one_pow_mul_prod_Icc_tricomiContFractNum_ne_zero ha hz m
  have ha_m1 : tricomiContFractNum a z (m + 1) ≠ 0 := tricomiContFractNum_ne_zero ha hz (by omega)
  have ha_m2 : tricomiContFractNum a z (m + 2) ≠ 0 := tricomiContFractNum_ne_zero ha hz (by omega)
  have hG1 : Gamma (a + 1) ≠ 0 := Gamma_ne_zero ha
  have ham_ne : a + m ≠ 0 := fun h => by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hm1
    exact ha r (by push_cast at h ⊢; linear_combination h)
  have ham1_ne : a + m + 1 ≠ 0 := fun h => by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hm1
    exact ha (r + 1) (by push_cast at h ⊢; linear_combination h)
  have hGm : Gamma (a + m) ≠ 0 := Gamma_ne_zero fun k hk => by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hm1
    exact ha (r + k) (by push_cast at hk ⊢; linear_combination hk)
  have hGm2 : Gamma (a + (m + 2 : ℕ)) = (a + m + 1) * (a + m) * Gamma (a + m) := by
    have hs1 : a + (m + 2 : ℕ) = (a + m + 1) + 1 := by push_cast; ring
    have hs0 : a + m + 1 = (a + m) + 1 := by ring
    rw [hs1, Gamma_add_one _ ham1_ne, hs0, Gamma_add_one _ ham_ne, ← hs0]
    ring
  have hP1 : (-1 : ℂ) ^ (m + 1) * (∏ j ∈ Icc 1 (m + 1), tricomiContFractNum a z j) =
      -tricomiContFractNum a z (m + 1) *
        ((-1 : ℂ) ^ m * ∏ j ∈ Icc 1 m, tricomiContFractNum a z j) := by
    rw [pow_succ, prod_Icc_succ_top (by omega)]
    ring
  have hP2 : (-1 : ℂ) ^ (m + 2) * (∏ j ∈ Icc 1 (m + 2), tricomiContFractNum a z j) =
      tricomiContFractNum a z (m + 1) * tricomiContFractNum a z (m + 2) *
        ((-1 : ℂ) ^ m * ∏ j ∈ Icc 1 m, tricomiContFractNum a z j) := by
    have hm2_eq : m + 2 = (m + 1) + 1 := by omega
    rw [hm2_eq, pow_succ, prod_Icc_succ_top (by omega)]
    linear_combination -tricomiContFractNum a z (m + 2) * hP1
  rw [hP1, hP2, hGm2]
  field_simp

private theorem norm_tricomiContFractNum_add_two_le (a z : ℂ) (m : ℕ) :
    ‖tricomiContFractNum a z (m + 2)‖ ≤ (‖a‖ + m + 2) * ‖z‖ := by
  rcases eq_or_ne m 0 with rfl | hm0
  · simp only [zero_add, tricomiContFractNum_two, norm_neg, Nat.cast_zero, add_zero]
    nlinarith [norm_nonneg a, norm_nonneg z]
  · rcases Nat.even_or_odd' (m + 2) with ⟨k, hk | hk⟩
    · rw [hk, tricomiContFractNum_two_mul a z (by omega), norm_mul, norm_neg]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg z)
      have hk1 : k + 1 ≤ m + 2 := by omega
      have hk1R : (k : ℝ) + 1 ≤ (m : ℝ) + 2 := by exact_mod_cast hk1
      calc ‖a + (k : ℂ) - 1‖ ≤ ‖a + (k : ℂ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ ≤ ‖a‖ + ‖(k : ℂ)‖ + 1 := by rw [norm_one]; gcongr; exact norm_add_le _ _
        _ = ‖a‖ + k + 1 := by rw [norm_natCast]
        _ ≤ ‖a‖ + m + 2 := by linarith
    · rw [hk, tricomiContFractNum_two_mul_add_one a z (by omega), norm_mul, norm_natCast]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg z)
      have hkle : k ≤ m + 2 := by omega
      have hkleR : (k : ℝ) ≤ (m : ℝ) + 2 := by exact_mod_cast hkle
      linarith [norm_nonneg a]

private theorem six_le_norm_mul_div_tricomiContFractNum {a z : ℂ} (ha : ∀ k : ℕ, a + 1 ≠ -k)
    (hz : z ≠ 0) {m : ℕ} (hmR : 3 * ‖a‖ + 12 * ‖z‖ + 4 ≤ (m : ℝ)) :
    6 ≤ ‖(a + m) * (a + m + 1) / tricomiContFractNum a z (m + 2)‖ := by
  have ha_m2 : tricomiContFractNum a z (m + 2) ≠ 0 := tricomiContFractNum_ne_zero ha hz (by omega)
  have ham_ge : (m : ℝ) - ‖a‖ ≤ ‖a + m‖ := by
    have htri := norm_sub_norm_le (m : ℂ) (-a)
    rw [sub_neg_eq_add, add_comm (m : ℂ) a, norm_natCast, norm_neg] at htri
    exact htri
  have ham1_ge : (m : ℝ) - ‖a‖ ≤ ‖a + m + 1‖ := by
    have htri := norm_sub_norm_le ((m : ℂ) + 1) (-a)
    have hcast : ‖(m : ℂ) + 1‖ = (m : ℝ) + 1 := by
      rw [← Nat.cast_add_one, norm_natCast, Nat.cast_add_one]
    have hadd : (m : ℂ) + 1 + a = a + m + 1 := by ring
    rw [sub_neg_eq_add, hadd, hcast, norm_neg] at htri
    linarith
  rw [norm_div, norm_mul, le_div_iff₀ (norm_pos_iff.2 ha_m2)]
  calc 6 * ‖tricomiContFractNum a z (m + 2)‖
      ≤ 6 * ((‖a‖ + m + 2) * ‖z‖) := by gcongr; exact norm_tricomiContFractNum_add_two_le a z m
    _ ≤ ((m : ℝ) - ‖a‖) * ((m : ℝ) - ‖a‖) := by
        have h1 : 6 * ‖z‖ ≤ ((m : ℝ) - ‖a‖) / 2 := by linarith [norm_nonneg a]
        have h2 : ‖a‖ + (m : ℝ) + 2 ≤ 2 * ((m : ℝ) - ‖a‖) := by linarith [norm_nonneg z]
        nlinarith [norm_nonneg a, norm_nonneg z]
    _ ≤ ‖a + m‖ * ‖a + m + 1‖ := by
        have h0 : 0 ≤ (m : ℝ) - ‖a‖ := by linarith [norm_nonneg a, norm_nonneg z]
        gcongr

private theorem eventually_three_mul_norm_le_tricomiTerm {a z : ℂ} (ha : ∀ k : ℕ, a + 1 ≠ -k)
    (hz : z ≠ 0) :
    ∀ᶠ m in atTop,
      3 * ‖(-1) ^ m * (∏ j ∈ Icc 1 m, tricomiContFractNum a z j) /
          (tricomiContFractSol a z m * tricomiContFractSol a z (m + 1))‖ ≤
        ‖(-1) ^ (m + 1) * (∏ j ∈ Icc 1 (m + 1), tricomiContFractNum a z j) /
          (tricomiContFractSol a z (m + 1) * tricomiContFractSol a z (m + 2))‖ := by
  let L : ℕ → ℂ := fun m =>
    Gamma (a + m) * tricomiContFractSol a z m /
      (((-1 : ℂ) ^ m * ∏ j ∈ Icc 1 m, tricomiContFractNum a z j) * Gamma (a + 1))
  have hL : Tendsto L atTop (𝓝 (cexp (z / 2))) := tendsto_Gamma_mul_tricomiContFractSol_div ha hz
  have hLratio : Tendsto (fun m => ‖L m / L (m + 2)‖) atTop (𝓝 1) := by
    have hexp : cexp (z / 2) ≠ 0 := Complex.exp_ne_zero _
    have hdiv := hL.div (hL.comp (tendsto_add_atTop_nat 2)) hexp
    rw [div_self hexp] at hdiv
    simpa only [norm_one, Pi.div_apply, Function.comp_apply] using hdiv.norm
  have hLhalf : ∀ᶠ m in atTop, (1 / 2 : ℝ) ≤ ‖L m / L (m + 2)‖ :=
    hLratio.eventually (le_mem_nhds (by norm_num))
  have hbig : ∀ᶠ m : ℕ in atTop, 3 * ‖a‖ + 12 * ‖z‖ + 4 ≤ (m : ℝ) :=
    tendsto_natCast_atTop_atTop (R := ℝ) |>.eventually_ge_atTop (3 * ‖a‖ + 12 * ‖z‖ + 4)
  have hfne := eventually_tricomiContFractSol_ne_zero ha hz
  filter_upwards [hLhalf, hbig, eventually_ge_atTop 1, hfne,
    (tendsto_add_atTop_nat 1).eventually hfne,
    (tendsto_add_atTop_nat 2).eventually hfne] with m hLh hmR hm1 hfm hfm1 hfm2
  have hPm := neg_one_pow_mul_prod_Icc_tricomiContFractNum_ne_zero ha hz m
  have hTm_ne : (-1) ^ m * (∏ j ∈ Icc 1 m, tricomiContFractNum a z j) /
      (tricomiContFractSol a z m * tricomiContFractSol a z (m + 1)) ≠ 0 :=
    div_ne_zero hPm (mul_ne_zero hfm hfm1)
  have hrat_ge := six_le_norm_mul_div_tricomiContFractNum ha hz hmR
  have hratio_ge : 3 ≤ ‖((-1) ^ (m + 1) * (∏ j ∈ Icc 1 (m + 1), tricomiContFractNum a z j) /
        (tricomiContFractSol a z (m + 1) * tricomiContFractSol a z (m + 2))) /
      ((-1) ^ m * (∏ j ∈ Icc 1 m, tricomiContFractNum a z j) /
        (tricomiContFractSol a z m * tricomiContFractSol a z (m + 1)))‖ := by
    rw [tricomiContFract_term_ratio_eq ha hz hm1 hfm hfm1 hfm2, norm_mul, norm_neg]
    calc (3 : ℝ) = 6 * (1 / 2) := by norm_num
      _ ≤ ‖(a + m) * (a + m + 1) / tricomiContFractNum a z (m + 2)‖ * ‖L m / L (m + 2)‖ := by
          gcongr
  rwa [norm_div, le_div_iff₀ (norm_pos_iff.2 hTm_ne)] at hratio_ge

/-- For `a + 1 ∉ -ℕ`, `z ≠ 0`, and any starting index `N : ℕ`, the reduction-of-order partial sums
`∑_{m = N}^{n - 1} (-1)^m (a₁ ⋯ aₘ) / (f(m) f(m + 1))` of `f = tricomiContFractSol a z` tend to
infinity in norm. -/
theorem tendsto_norm_sum_tricomiContFractSol_atTop {a z : ℂ} (ha : ∀ k : ℕ, a + 1 ≠ -k)
    (hz : z ≠ 0) (N : ℕ) :
    Tendsto (fun n => ‖∑ m ∈ Ico N n,
      (-1) ^ m * (∏ j ∈ Icc 1 m, tricomiContFractNum a z j) /
        (tricomiContFractSol a z m * tricomiContFractSol a z (m + 1))‖) atTop atTop := by
  refine TauCeti.tendsto_norm_sum_Ico_atTop_of_mul_norm_le (c := 3) (by norm_num)
    (eventually_three_mul_norm_le_tricomiTerm ha hz) (Eventually.frequently ?_) N
  have hfne := eventually_tricomiContFractSol_ne_zero ha hz
  filter_upwards [hfne, (tendsto_add_atTop_nat 1).eventually hfne] with m hfm hfm1
  exact norm_pos_iff.2 <| div_ne_zero
    (neg_one_pow_mul_prod_Icc_tricomiContFractNum_ne_zero ha hz m) (mul_ne_zero hfm hfm1)

/-! ### Convergence of DLMF 8.9.1 -/

/-- **DLMF 8.9.1**: for every `a ∉ {-1, -2, …}` (`∀ k : ℕ, a + 1 ≠ -k`) and every `z : ℂ`, the
continued fraction `tricomiContFract a z` has eventually nonzero denominators and its convergents
tend to `Γ(a + 1) e^z γ*(a, z)`. -/
theorem tendsto_convs_tricomiContFract {a : ℂ} (ha : ∀ k : ℕ, a + 1 ≠ -k) (z : ℂ) :
    (∀ᶠ n in atTop, (tricomiContFract a z).dens n ≠ 0) ∧
      Tendsto (tricomiContFract a z).convs atTop
        (𝓝 (Gamma (a + 1) * cexp z * tricomiIncompleteGamma a z)) := by
  rcases eq_or_ne z 0 with rfl | hz
  · refine ⟨Eventually.of_forall (tricomiContFract_zero_right_dens_ne_zero ha), ?_⟩
    rw [Complex.exp_zero, mul_one]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (tricomiContFract_zero_right_convs_eq_Gamma_mul ha hn).symm
  · have hconv := TauCeti.tendsto_convs_contFrac_of_tendsto_norm_sum
      (fun _ hn => tricomiContFractSol_recurrence ha z hn)
      (by simp : tricomiContFractSol a z 0 ≠ 0)
      (eventually_tricomiContFractSol_ne_zero ha hz)
      (tendsto_norm_sum_tricomiContFractSol_atTop ha hz 0)
    rwa [← tricomiContFract_def, tricomiContFractSol_zero, div_one,
      neg_tricomiContFractSol_one] at hconv

/-- At `a = 0`, the continued fraction `tricomiContFract 0 z` converges to `e^z` for every
`z : ℂ`. -/
theorem tendsto_convs_tricomiContFract_zero_left (z : ℂ) :
    (∀ᶠ n in atTop, (tricomiContFract 0 z).dens n ≠ 0) ∧
      Tendsto (tricomiContFract 0 z).convs atTop (𝓝 (cexp z)) := by
  have ha : ∀ k : ℕ, (0 : ℂ) + 1 ≠ -k := fun k hk =>
    Nat.cast_add_one_ne_zero (R := ℂ) k (by linear_combination hk)
  simpa using tendsto_convs_tricomiContFract ha z

/-- **DLMF 8.9.1** in terms of the lower incomplete Gamma function `γ(a, z)`: for `a ∉ -ℕ` and
`z ≠ 0`, the convergents of `tricomiContFract a z` tend to `a z^{-a} e^z γ(a, z)`. -/
theorem tendsto_convs_tricomiContFract_lowerIncompleteGamma {a z : ℂ} (ha : ∀ k : ℕ, a ≠ -k)
    (hz : z ≠ 0) :
    (∀ᶠ n in atTop, (tricomiContFract a z).dens n ≠ 0) ∧
      Tendsto (tricomiContFract a z).convs atTop
        (𝓝 (a * z ^ (-a) * cexp z * lowerIncompleteGamma a z)) := by
  have ha1 : ∀ k : ℕ, a + 1 ≠ -k := fun k hk =>
    ha (k + 1) (by push_cast; linear_combination hk)
  have ha0 : a ≠ 0 := by simpa using ha 0
  have hza : z ^ a ≠ 0 := by
    rw [cpow_def_of_ne_zero hz]
    exact Complex.exp_ne_zero _
  have heq : Gamma (a + 1) * cexp z * tricomiIncompleteGamma a z =
      a * z ^ (-a) * cexp z * lowerIncompleteGamma a z := by
    rw [lowerIncompleteGamma_def, regularizedGamma_def, Gamma_add_one a ha0, cpow_neg]
    calc a * Gamma a * cexp z * tricomiIncompleteGamma a z
        = a * Gamma a * ((z ^ a)⁻¹ * z ^ a) * cexp z * tricomiIncompleteGamma a z := by
            rw [inv_mul_cancel₀ hza, mul_one]
      _ = a * (z ^ a)⁻¹ * cexp z * (Gamma a * (z ^ a * tricomiIncompleteGamma a z)) := by ring
  simpa only [heq] using tendsto_convs_tricomiContFract ha1 z

end Complex
