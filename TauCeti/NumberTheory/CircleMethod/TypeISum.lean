/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Harmonic.Bounds
public import TauCeti.NumberTheory.CircleMethod.AdditiveCharacter
public import TauCeti.NumberTheory.Harmonic.Basic

/-!
# Type I sums for additive twists

For `α` close to a reduced fraction, `|α - a / q| ≤ q⁻²` with `gcd(a, q) = 1`, this file proves
the type I bound of the circle method:

`∑_{m=1}^M min(X / m, 1 / ‖mα‖) ≤ 16 (X / q + M + q) log (2Mq)`
(`TauCeti.sum_min_inv_distInt_le`).

It is the estimate behind the minor-arc bounds for exponential sums: after summing over `n` a
geometric sum `∑_{n ≤ X / m} e(mnα)` is at most `min(X / m, 1 / (2‖mα‖))`, so a type I sum
`∑_{m ≤ M} ∑_{n ≤ X / m} a(m) e(mnα)` with bounded coefficients is controlled by the left side.

The proof is the standard counting of the points `mα` modulo `1`.

* `TauCeti.sum_min_inv_distInt_le_of_separated`: if the pairwise differences of finitely many
  points `x i` are at distance at least `δ` from the integers, then
  `∑ min(Y, 1 / ‖x i‖) ≤ 2Y + (2 / δ) H_K` with `K = ⌊1 / (2δ)⌋` and `H_K` the harmonic number,
  because each window `‖x‖ ∈ [nδ, (n + 1)δ)` holds at most two of the points, one on each side of
  the nearest integer.
* `TauCeti.one_div_two_mul_le_distInt_intCast_mul`: if `|α - a / q| ≤ q⁻²` with `gcd(a, q) = 1`,
  then `‖dα‖ ≥ 1 / (2q)` for every integer `d ≠ 0` with `2|d| ≤ q`. So in a block of `q / 2 + 1`
  consecutive integers `m` the points `mα` are `1 / (2q)`-separated.

Splitting `1 ≤ m ≤ M` into such blocks, the block of `m ≥ jq / 2` contributes at most
`4X / (jq) + 4q H_q`, and the first block contributes `O(q log q)` because there `‖mα‖ ≥ 1 / (2q)`.

As in `TauCeti.norm_sum_expTwoPiI_le`, the minimum `min(X / m, 1 / ‖mα‖)` takes the value `X / m`
when `‖mα‖ = 0`: with Lean's `1 / 0 = 0` the minimum would be `0` there.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., GTM 74, Springer, 2000, Chapter 25.
* R. C. Vaughan, *The Hardy–Littlewood Method*, 2nd ed., Cambridge Tracts in Mathematics 125,
  1997, Lemma 2.2.
-/

public section

noncomputable section

namespace TauCeti

/-! ### Separated points -/

/-- In the window `‖x‖ ∈ [nδ, (n + 1)δ)` with `n ≥ 1`, `min(Y, 1 / ‖x‖) ≤ 1 / (nδ)`; in the
window `n = 0` it is at most `Y`. -/
private theorem ite_min_inv_distInt_le_ite_floor (x : ℝ) {δ : ℝ} (hδ : 0 < δ) (Y : ℝ) :
    (if distInt x = 0 then Y else min Y (distInt x)⁻¹) ≤
      if ⌊distInt x / δ⌋₊ = 0 then Y else ((⌊distInt x / δ⌋₊ : ℝ) * δ)⁻¹ := by
  split_ifs with h0 hn hn
  · exact le_rfl
  · exact absurd (by simp [h0]) hn
  · exact min_le_left _ _
  · have hle : (⌊distInt x / δ⌋₊ : ℝ) * δ ≤ distInt x :=
      (le_div_iff₀ hδ).1 (Nat.floor_le (div_nonneg (distInt_nonneg _) hδ.le))
    have hpos : 0 < (⌊distInt x / δ⌋₊ : ℝ) * δ :=
      mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) hδ
    exact (min_le_right _ _).trans (inv_anti₀ hpos hle)

/-- If the pairwise differences of the points `x i` are at distance at least `δ` from the
integers, each window `‖x i‖ ∈ [kδ, (k + 1)δ)` holds at most two of them, one on each side of the
nearest integer. -/
private theorem card_filter_floor_distInt_div_eq_le_two {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ distInt (x i - x j)) (k : ℕ) :
    (s.filter fun i ↦ ⌊distInt (x i) / δ⌋₊ = k).card ≤ 2 := by
  refine (Finset.card_le_card_of_injOn (fun i ↦ decide (0 ≤ x i - round (x i)))
    (fun _ _ ↦ Finset.mem_coe.2 (Finset.mem_univ _)) ?_).trans_eq
    (Finset.card_univ.trans Fintype.card_bool)
  intro i hi j hj hij
  by_contra hne
  rw [Finset.mem_coe, Finset.mem_filter] at hi hj
  -- With `r = x - round x`, so `|r| = ‖x‖`: both `|r i|` and `|r j|` lie in `[kδ, (k + 1)δ)`.
  have key : ∀ t, ⌊distInt (x t) / δ⌋₊ = k →
      (k : ℝ) * δ ≤ |x t - round (x t)| ∧ |x t - round (x t)| < k * δ + δ := fun t ht ↦ by
    have h1 := Nat.floor_le (div_nonneg (distInt_nonneg (x t)) hδ.le)
    have h2 := Nat.lt_floor_add_one (distInt (x t) / δ)
    rw [ht, le_div_iff₀ hδ] at h1
    rw [ht, div_lt_iff₀ hδ, add_mul, one_mul] at h2
    rw [distInt_def] at h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨h1, h2⟩ := key i hi.2
  obtain ⟨h3, h4⟩ := key j hj.2
  have hs : 0 ≤ x i - round (x i) ↔ 0 ≤ x j - round (x j) := by simpa using hij
  -- On the same side of the nearest integer, they differ by less than `δ`.
  have hlt : |(x i - round (x i)) - (x j - round (x j))| < δ := by
    rw [abs_sub_lt_iff]
    rcases le_or_gt 0 (x i - round (x i)) with hr | hr
    · rw [abs_of_nonneg hr] at h1 h2
      rw [abs_of_nonneg (hs.1 hr)] at h3 h4
      constructor <;> linarith
    · rw [abs_of_neg hr] at h1 h2
      rw [abs_of_neg (lt_of_not_ge (mt hs.2 hr.not_ge))] at h3 h4
      constructor <;> linarith
  have hle := distInt_le_abs_sub_intCast (x i - x j) (round (x i) - round (x j))
  push_cast at hle
  exact (hsep i hi.1 j hj.1 hne).not_gt (hle.trans_lt (by convert hlt using 2; ring))

/-- **Separated points.** If the pairwise differences of the points `x i`, `i ∈ s`, are at
distance at least `δ > 0` from the integers, then
`∑_{i ∈ s} min(Y, 1 / ‖x i‖) ≤ 2Y + (2 / δ) H_K` with `K = ⌊1 / (2δ)⌋` and `H_K` the harmonic
number, the minimum taking the value `Y` when `‖x i‖ = 0`. -/
theorem sum_min_inv_distInt_le_of_separated {ι : Type*} (s : Finset ι) (x : ι → ℝ) {δ Y : ℝ}
    (hδ : 0 < δ) (hY : 0 ≤ Y) (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ distInt (x i - x j)) :
    ∑ i ∈ s, (if distInt (x i) = 0 then Y else min Y (distInt (x i))⁻¹) ≤
      2 * Y + 2 / δ * harmonic ⌊(2 * δ)⁻¹⌋₊ := by
  set K := ⌊(2 * δ)⁻¹⌋₊
  -- Sort the points by their window `n i`; a term in the window `k` is at most `b k`.
  set n : ι → ℕ := fun i ↦ ⌊distInt (x i) / δ⌋₊
  set b : ℕ → ℝ := fun k ↦ if k = 0 then Y else ((k : ℝ) * δ)⁻¹ with hb
  have hb0 : ∀ k, 0 ≤ b k := fun k ↦ by
    simp only [hb]
    split_ifs
    exacts [hY, by positivity]
  have hmaps : ∀ i ∈ s, n i ∈ Finset.range (K + 1) := fun i _ ↦ by
    rw [Finset.mem_range, Nat.lt_succ_iff]
    refine Nat.floor_le_floor ?_
    rw [div_le_iff₀ hδ, mul_inv, mul_assoc, inv_mul_cancel₀ hδ.ne', mul_one]
    exact (distInt_le_half _).trans_eq (one_div 2)
  calc ∑ i ∈ s, (if distInt (x i) = 0 then Y else min Y (distInt (x i))⁻¹)
      = ∑ k ∈ Finset.range (K + 1), ∑ i ∈ s with n i = k,
          (if distInt (x i) = 0 then Y else min Y (distInt (x i))⁻¹) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ k ∈ Finset.range (K + 1), 2 * b k := by
        gcongr with k
        calc _ ≤ ∑ i ∈ s with n i = k, b k := Finset.sum_le_sum fun i hi ↦
              (Finset.mem_filter.1 hi).2 ▸ ite_min_inv_distInt_le_ite_floor (x i) hδ Y
          _ = (s.filter fun i ↦ n i = k).card * b k := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ 2 * b k := mul_le_mul_of_nonneg_right
              (by exact_mod_cast card_filter_floor_distInt_div_eq_le_two s x hδ hsep k) (hb0 k)
    _ = 2 * Y + 2 / δ * harmonic K := by
        rw [Finset.sum_range_succ', add_comm]
        simp only [hb, cast_harmonic_eq_sum_range, Finset.mul_sum, Nat.succ_ne_zero, ↓reduceIte]
        congr 1
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        field_simp

/-! ### Separation from a rational approximation -/

/-- If `|α - a / q| ≤ q⁻²` with `gcd(a, q) = 1`, then `‖dα‖ ≥ 1 / (2q)` for every integer
`d ≠ 0` with `2|d| ≤ q`. -/
theorem one_div_two_mul_le_distInt_intCast_mul {α : ℝ} {a : ℤ} {q : ℕ} (ha : Int.gcd a q = 1)
    (hα : |α - a / q| ≤ 1 / (q : ℝ) ^ 2) {d : ℤ} (hd : d ≠ 0) (hdq : 2 * |d| ≤ q) :
    1 / (2 * (q : ℝ)) ≤ distInt (d * α) := by
  have hd1 : 1 ≤ |d| := Int.one_le_abs hd
  have hq : (0 : ℝ) < q := by exact_mod_cast (show (0 : ℤ) < q by omega)
  -- `q ∤ da`, since `q` is coprime to `a` and `0 < |d| < q`.
  have hndvd : ¬(q : ℤ) ∣ d * a := fun h ↦ by
    have hcop : IsCoprime (q : ℤ) a := (Int.isCoprime_iff_gcd_eq_one.2 ha).symm
    exact hd (Int.eq_zero_of_abs_lt_dvd (hcop.dvd_of_dvd_mul_right h) (by omega))
  have h1 := one_div_le_distInt_intCast_div hndvd
  have h2 := distInt_add_le (d * α) ((d * a : ℤ) / q - d * α)
  have h3 := distInt_le_abs ((d * a : ℤ) / q - d * α)
  have h4 : |((d * a : ℤ) : ℝ) / q - d * α| ≤ 1 / (2 * q) := by
    have hdq' : 2 * |(d : ℝ)| ≤ q := by exact_mod_cast hdq
    rw [show ((d * a : ℤ) : ℝ) / q - d * α = -(d * (α - a / q)) by push_cast; ring, abs_neg,
      abs_mul]
    calc |(d : ℝ)| * |α - a / q| ≤ q / 2 * (1 / (q : ℝ) ^ 2) := by
          gcongr
          linarith
      _ = 1 / (2 * q) := by field_simp
  rw [add_sub_cancel] at h2
  have : 1 / (q : ℝ) = 1 / (2 * q) + 1 / (2 * q) := by field_simp; norm_num
  linarith

/-! ### The type I bound -/

/-- In a block of `q / 2 + 1` consecutive integers, the points `mα` are `1 / (2q)`-separated. -/
private theorem one_div_two_mul_le_distInt_sub_of_div_eq {α : ℝ} {a : ℤ} {q : ℕ}
    (ha : Int.gcd a q = 1) (hα : |α - a / q| ≤ 1 / (q : ℝ) ^ 2) {m m' : ℕ}
    (hmm' : m / (q / 2 + 1) = m' / (q / 2 + 1)) (hne : m ≠ m') :
    1 / (2 * (q : ℝ)) ≤ distInt (m * α - m' * α) := by
  have hL : 0 < q / 2 + 1 := Nat.succ_pos _
  have h1 := Nat.div_mul_le_self m (q / 2 + 1)
  have h2 := Nat.lt_div_mul_add (a := m) hL
  have h3 := Nat.div_mul_le_self m' (q / 2 + 1)
  have h4 := Nat.lt_div_mul_add (a := m') hL
  rw [hmm'] at h1 h2
  generalize m' / (q / 2 + 1) * (q / 2 + 1) = t at h1 h2 h3 h4
  have := one_div_two_mul_le_distInt_intCast_mul ha hα (d := (m : ℤ) - m') (by omega) (by
    rcases abs_cases ((m : ℤ) - m') with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega)
  convert this using 2
  push_cast
  ring

/-- Raising the cap `Y` raises `min(Y, 1 / ‖x‖)`. -/
private theorem ite_min_inv_distInt_le_of_le {x Y Y' : ℝ} (h : Y ≤ Y') :
    (if distInt x = 0 then Y else min Y (distInt x)⁻¹) ≤
      if distInt x = 0 then Y' else min Y' (distInt x)⁻¹ := by
  split_ifs
  exacts [h, min_le_min_right _ h]

/-- The terms of a block, each with the cap `Y`, sum to at most `2Y + 4q H_q`. -/
private theorem sum_block_le {α : ℝ} {a : ℤ} {q : ℕ} (hq : 0 < q) (ha : Int.gcd a q = 1)
    (hα : |α - a / q| ≤ 1 / (q : ℝ) ^ 2) (s : Finset ℕ) (j : ℕ)
    (hs : ∀ m ∈ s, m / (q / 2 + 1) = j) {Y : ℝ} (hY : 0 ≤ Y) (g : ℕ → ℝ)
    (hg : ∀ m ∈ s, g m ≤ if distInt (m * α) = 0 then Y else min Y (distInt (m * α))⁻¹) :
    ∑ m ∈ s, g m ≤ 2 * Y + 4 * q * harmonic q := by
  have hsep : ∀ m ∈ s, ∀ m' ∈ s, m ≠ m' → 1 / (2 * (q : ℝ)) ≤ distInt (m * α - m' * α) :=
    fun m hm m' hm' hne ↦ one_div_two_mul_le_distInt_sub_of_div_eq ha hα
      ((hs m hm).trans (hs m' hm').symm) hne
  have h := sum_min_inv_distInt_le_of_separated s (fun m : ℕ ↦ (m : ℝ) * α) (by positivity) hY hsep
  rw [show (2 * (1 / (2 * (q : ℝ))))⁻¹ = q by field_simp, Nat.floor_natCast,
    show 2 / (1 / (2 * (q : ℝ))) = 4 * q by field_simp; norm_num] at h
  exact (Finset.sum_le_sum hg).trans h

/-- The first block, `1 ≤ m < q / 2 + 1`: there `‖mα‖ ≥ 1 / (2q)`, so each term is at most `2q`
whatever `X`. -/
private theorem sum_filter_div_eq_zero_le {α : ℝ} {a : ℤ} {q : ℕ} (hq : 0 < q)
    (ha : Int.gcd a q = 1) (hα : |α - a / q| ≤ 1 / (q : ℝ) ^ 2) (M : ℕ) (X : ℝ) :
    ∑ m ∈ Finset.Icc 1 M with m / (q / 2 + 1) = 0,
        (if distInt (m * α) = 0 then X / m else min (X / m) (distInt (m * α))⁻¹) ≤
      2 * (2 * q) + 4 * q * harmonic q := by
  refine sum_block_le hq ha hα _ 0 (fun m hm ↦ (Finset.mem_filter.1 hm).2) (by positivity) _ ?_
  intro m hm
  obtain ⟨hm, hm0⟩ := Finset.mem_filter.1 hm
  have hm1 := (Finset.mem_Icc.1 hm).1
  have hmL : m < q / 2 + 1 := (Nat.div_eq_zero_iff_lt (Nat.succ_pos _)).1 hm0
  have hsep := one_div_two_mul_le_distInt_intCast_mul ha hα (d := m) (by omega) (by
    rw [Nat.abs_cast]; omega)
  push_cast at hsep
  have hpos : 0 < distInt (m * α) := lt_of_lt_of_le (by positivity) hsep
  have hinv : (distInt (m * α))⁻¹ ≤ 2 * q := by
    rw [inv_le_comm₀ hpos (by positivity)]
    simpa using hsep
  simp only [hpos.ne', ↓reduceIte, min_eq_right hinv]
  exact min_le_right _ _

/-- The block `j + 1`: there `m ≥ (j + 1) L` with `L = q / 2 + 1`, so each term has the cap
`X / ((j + 1) L)`. -/
private theorem sum_filter_div_eq_succ_le {α : ℝ} {a : ℤ} {q : ℕ} (hq : 0 < q)
    (ha : Int.gcd a q = 1) (hα : |α - a / q| ≤ 1 / (q : ℝ) ^ 2) (M : ℕ) {X : ℝ} (hX : 0 ≤ X)
    (j : ℕ) :
    ∑ m ∈ Finset.Icc 1 M with m / (q / 2 + 1) = j + 1,
        (if distInt (m * α) = 0 then X / m else min (X / m) (distInt (m * α))⁻¹) ≤
      2 * (X / ((j + 1 : ℕ) * (q / 2 + 1 : ℕ))) + 4 * q * harmonic q := by
  refine sum_block_le hq ha hα _ (j + 1) (fun m hm ↦ (Finset.mem_filter.1 hm).2)
    (by positivity) _ fun m hm ↦ ite_min_inv_distInt_le_of_le ?_
  have hjm : (j + 1) * (q / 2 + 1) ≤ m :=
    (Finset.mem_filter.1 hm).2 ▸ Nat.div_mul_le_self m (q / 2 + 1)
  gcongr
  exact_mod_cast hjm

/-- Summing the block bounds: with `L = q / 2 + 1` and `J = M / L` blocks after the first,
`∑_{j < J} 2X / ((j + 1) L) + J · 4q H_q + (4q + 4q H_q) ≤ 16 (X / q + M + q) log (2Mq)`. -/
private theorem sum_block_bounds_le {q M : ℕ} (hq : 0 < q) (hM : 0 < M) {X : ℝ} (hX : 0 ≤ X) :
    ∑ j ∈ Finset.range (M / (q / 2 + 1)),
        (2 * (X / ((j + 1 : ℕ) * (q / 2 + 1 : ℕ))) + 4 * q * harmonic q) +
        (2 * (2 * q) + 4 * q * harmonic q) ≤
      16 * (X / q + M + q) * Real.log (2 * M * q) := by
  set L := q / 2 + 1
  set J := M / L
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hharm : ∑ j ∈ Finset.range J, 2 * (X / ((j + 1 : ℕ) * L)) = 2 * X / L * harmonic J := by
    simp only [cast_harmonic_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    field_simp
  rw [hharm]
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqL : (q : ℝ) ≤ 2 * L := by exact_mod_cast (show q ≤ 2 * L by omega)
  have hJL : (J : ℝ) * L ≤ M := by exact_mod_cast Nat.div_mul_le_self M L
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.succ_pos (q / 2)
  -- With `Λ = 1 + log (Mq)`: `H_J ≤ Λ`, `H_q ≤ Λ` and `Λ ≤ 2 log (2Mq)`.
  set Λ := 1 + Real.log (M * q)
  have hlogMq : 0 ≤ Real.log (M * q) := Real.log_nonneg (by nlinarith)
  have hHJ : (harmonic J : ℝ) ≤ Λ := by
    refine (harmonic_le_one_add_log J).trans ?_
    rcases Nat.eq_zero_or_pos J with hJ0 | hJ0
    · simp only [hJ0, Nat.cast_zero, Real.log_zero]; linarith
    · have : (J : ℝ) ≤ M * q := by
        have : (J : ℝ) ≤ M := by exact_mod_cast Nat.div_le_self M L
        nlinarith
      linarith [Real.log_le_log (by exact_mod_cast hJ0) this]
  have hHq : (harmonic q : ℝ) ≤ Λ := by
    linarith [harmonic_le_one_add_log q, Real.log_le_log hq' (show (q : ℝ) ≤ M * q by nlinarith)]
  have hΛ2 : Λ ≤ 2 * Real.log (2 * M * q) := by
    rw [mul_assoc, Real.log_mul two_ne_zero (by positivity)]
    linarith [Real.one_sub_inv_le_log_of_pos (two_pos (α := ℝ))]
  have hXL : 2 * X / L ≤ 4 * X / q := by
    rw [div_le_div_iff₀ hL hq']
    nlinarith
  have e1 : 2 * X / L * harmonic J ≤ 4 * X / q * Λ :=
    mul_le_mul hXL hHJ ((Real.log_nonneg (by simp)).trans (log_add_one_le_harmonic J))
      (by positivity)
  have e2 : (J : ℝ) * (4 * q * harmonic q) ≤ 8 * M * Λ := by
    calc (J : ℝ) * (4 * q * harmonic q) = J * (4 * q) * harmonic q := by ring
      _ ≤ 8 * M * Λ :=
        mul_le_mul (by nlinarith) hHq
          ((Real.log_nonneg (by simp)).trans (log_add_one_le_harmonic q)) (by positivity)
  have e3 : 2 * (2 * (q : ℝ)) + 4 * q * harmonic q ≤ 8 * q * Λ := by nlinarith
  have hXq : 0 ≤ X / q * Λ := mul_nonneg (by positivity) (by linarith)
  calc 2 * X / L * harmonic J + J * (4 * q * harmonic q) + (2 * (2 * q) + 4 * q * harmonic q)
      ≤ 8 * (X / q + M + q) * Λ := by
        have : 4 * X / q * Λ = 4 * (X / q * Λ) := by ring
        nlinarith
    _ ≤ 8 * (X / q + M + q) * (2 * Real.log (2 * M * q)) := by gcongr
    _ = 16 * (X / q + M + q) * Real.log (2 * M * q) := by ring

/-- **The type I bound.** If `|α - a / q| ≤ q⁻²` with `q ≥ 1` and `gcd(a, q) = 1`, then for every
`M` and `X ≥ 0`,
`∑_{m=1}^M min(X / m, 1 / ‖mα‖) ≤ 16 (X / q + M + q) log (2Mq)`,
the minimum taking the value `X / m` when `‖mα‖ = 0`. -/
theorem sum_min_inv_distInt_le {α : ℝ} {a : ℤ} {q : ℕ} (hq : 0 < q) (ha : Int.gcd a q = 1)
    (hα : |α - a / q| ≤ 1 / (q : ℝ) ^ 2) (M : ℕ) {X : ℝ} (hX : 0 ≤ X) :
    ∑ m ∈ Finset.Icc 1 M,
        (if distInt (m * α) = 0 then X / m else min (X / m) (distInt (m * α))⁻¹) ≤
      16 * (X / q + M + q) * Real.log (2 * M * q) := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  -- Split `1 ≤ m ≤ M` into the blocks `m / (q / 2 + 1) = j`, `j ≤ M / (q / 2 + 1)`.
  have hmaps : ∀ m ∈ Finset.Icc 1 M, m / (q / 2 + 1) ∈ Finset.range (M / (q / 2 + 1) + 1) :=
    fun m hm ↦
      Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.div_le_div_right (Finset.mem_Icc.1 hm).2))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.sum_range_succ']
  exact (add_le_add (Finset.sum_le_sum fun j _ ↦ sum_filter_div_eq_succ_le hq ha hα M hX j)
    (sum_filter_div_eq_zero_le hq ha hα M X)).trans (sum_block_bounds_le hq hM hX)

/-! ### Checks -/

/-- At `α = 0` every `‖mα‖` vanishes, so the sum is `X H_M`; the term `X / q` of
`sum_min_inv_distInt_le` pays for it at `q = 1`. -/
example (M : ℕ) (X : ℝ) :
    ∑ m ∈ Finset.Icc 1 M,
        (if distInt (m * 0) = 0 then X / m else min (X / m) (distInt (m * 0))⁻¹) =
      X * harmonic M := by
  simp [harmonic_eq_sum_Icc, Finset.mul_sum, div_eq_mul_inv]

end TauCeti
