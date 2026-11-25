/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.NumberTheory.LSeries.Basic
public import TauCeti.NumberTheory.LSeries.InghamExponent
import Mathlib.Analysis.Complex.ExponentialBounds
import TauCeti.Analysis.Calculus.BumpFunction.Multiplicative
import TauCeti.NumberTheory.LSeries.LogBoundedCoeff
import TauCeti.NumberTheory.LSeries.SmoothedSum.ContourEstimate

/-!
# Ingham's transfer theorem

Let `η` be a zero-free width: continuous and nonincreasing on `[3, ∞)`, with
`η(t) ≥ a₀ (log t)^{-A}` there for some `a₀ > 0`. Let `‖a(n)‖ ≤ B log(n + 1)` and let the L-series
of `a` agree on `Re s > 1` with `G(s) + r/(s - 1)`, where `G` is holomorphic on a set containing
the region `R_η = {s : 1 - η(|Im s| + 3) ≤ Re s}` and `‖G(s)‖ ≤ C₀ log(|Im s| + 3)^{B'}` on
`R_η`. Then there are `c > 0` and `C'` with

`‖∑_{n ≤ x} a(n) - r x‖ ≤ C' x exp(-c ω_η(x))` for every `x ≥ 3`,

where `ω_η` is the Ingham exponent `TauCeti.inghamExponent`. For `η(t) = c₀ / log t` the error is
the classical `x exp(-c √(log x))`.

The proof first replaces `η` by `min η (1/2)`, which is at least `κ η` for a constant
`κ ∈ (0, 1]`, so that `ω_η` changes by at most the factor `κ` (`TauCeti.mul_inghamExponent_le`).
It then smooths the sum with the cutoff `χ_ε = smoothCutoff ν ε` of a fixed smooth bump `ν`.
At the height `T` of `TauCeti.exists_rpow_eq_and_inghamExponent_le`, the rectangle
`[1 - η(T + 3), 1 + 1/log x] ×ℂ [-T, T]` lies in `R_η`, and
`TauCeti.LSeries.norm_tsum_mul_smoothCutoff_sub_residue_le_of_norm_le_mul_log` bounds the smoothed
sum minus `r · 𝓜χ_ε(1) · x`. With `ε = T^{-1/2}`, the comparison with the sharp sum, the distance
from `𝓜χ_ε(1)` to `1` and the contour bound are each `O(x (log x)^k T^{-1/2})`, and
`T^{-1/2} ≤ 2 exp(-ω_η(x)/4)`; the powers of `log x` are absorbed by
`TauCeti.exists_log_pow_mul_exp_neg_inghamExponent_le`. For `x` too small to choose `T`, the
trivial bound `(B log(x + 1) + ‖r‖) x` suffices. For `η ≤ 1/2` the constant is `c = 1/8`.

## Main results

* `TauCeti.LSeries.norm_sum_sub_mul_le_of_zeroFreeRegion`: Ingham's transfer theorem.

## References

* A. E. Ingham, *The Distribution of Prime Numbers*, Cambridge Tracts 30 (1932), Chapter II.
* D. J. Platt, T. S. Trudgian, *The error term in the prime number theorem*, Math. Comp. 90
  (2021), §1.
* H. L. Montgomery, R. C. Vaughan, *Multiplicative Number Theory I*, Chapter 6.
* A. Kontorovich, T. Tao et al., *PrimeNumberTheoremAnd* blueprint, Theorem 4.6.1,
  <https://github.com/AlexKontorovich/PrimeNumberTheoremAnd>. The lemma `GenStrengthPNT` in the
  Tau Ceti fork <https://github.com/TauCetiProject/PrimeNumberTheoremAnd>, file
  `PrimeNumberTheoremAnd/MediumPNT.lean` at revision `2e6b7fe`, proves this theorem for `-ζ'/ζ`
  and `η(t) = A₀ / log^{n₁} t`; the proof here follows its route.
-/

public section

open Set Complex
open scoped Real

namespace TauCeti.LSeries

/-- A lower bound `η(t) ≥ a₀ (log t)^{-A}` on `[3, ∞)` with `a₀ > 0` makes `η` positive there. -/
private lemma pos_of_mul_log_rpow_neg_le {η : ℝ → ℝ} {a₀ A : ℝ} (ha₀ : 0 < a₀)
    (hηlow : ∀ t, 3 ≤ t → a₀ * Real.log t ^ (-A) ≤ η t) {t : ℝ} (ht : 3 ≤ t) : 0 < η t :=
  (mul_pos ha₀ (Real.rpow_pos_of_pos (Real.log_pos (by linarith)) _)).trans_le (hηlow t ht)

/-- If `η` is nonincreasing on `[3, ∞)`, the rectangle `[1 - η(T + 3), σ] ×ℂ [-T, T]` lies in
the region `1 - η(|Im s| + 3) ≤ Re s`. -/
private lemma le_re_of_mem_reProdIm {η : ℝ → ℝ} (hηa : AntitoneOn η (Ici 3)) {T σ : ℝ} {s : ℂ}
    (hs : s ∈ Icc (1 - η (T + 3)) σ ×ℂ Icc (-T) T) : 1 - η (|s.im| + 3) ≤ s.re := by
  obtain ⟨⟨hre, -⟩, him⟩ := mem_reProdIm.1 hs
  have h0 := abs_nonneg s.im
  have h := hηa (mem_Ici.2 (by linarith)) (mem_Ici.2 (by linarith [him.1, him.2]))
    (by linarith [abs_le.2 him] : |s.im| + 3 ≤ T + 3)
  linarith

/-- A bound `‖mellin χ_ε s‖ ≤ C / (|s| (1 + ε|s|))` at `ε = 1`, `s = 1` forces `C ≥ 0`. -/
private lemma nonneg_of_norm_mellin_smoothCutoff_le {ν : ℝ → ℝ} {C : ℝ}
    (hC : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 →
      ‖mellin (fun x ↦ (smoothCutoff ν ε x : ℂ)) s‖ ≤ C / (‖s‖ * (1 + ε * ‖s‖))) : 0 ≤ C := by
  have h := hC 1 one_pos le_rfl 1 (by norm_num) (by norm_num)
  rw [norm_one, one_mul, mul_one] at h
  exact (div_nonneg_iff.1 ((norm_nonneg _).trans h)).elim (·.1) fun h' ↦ absurd h'.2 (by norm_num)

/-- The arithmetic of the contour terms at `ε = 1/s`, `T = s²` and `x = us`: the bound of
`TauCeti.LSeries.norm_tsum_mul_smoothCutoff_sub_residue_le_of_norm_le_mul_log` is at most
`(16eBC + 4WC + 3eWC) u L² P`. Here `K = M + ‖r‖/η` is at most `W P` with `P ≥ 1`, the logarithm
`l` on the left edge is at most `L = log x ≥ 1`, and `v = 1/log x + η` is at most `3/2`. -/
private lemma contour_terms_le {B C K W P L u s x v l : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hK0 : 0 ≤ K) (hK : K ≤ W * P) (hP : 1 ≤ P) (hL : 1 ≤ L) (hs : 1 ≤ s) (hu : 0 ≤ u)
    (hv : v ≤ 3 / 2) (hl : l ≤ L) (hxu : x = u * s) :
    1 / (2 * π) * (2 * (8 * B * L ^ 2 * C * (Real.exp 1 * x)) / (s⁻¹ * s ^ 2) +
        4 * (K * C * (u / s)) * l + 2 * (v * (K * C) * (Real.exp 1 * x) / (s⁻¹ * (s ^ 2) ^ 2))) ≤
    (16 * Real.exp 1 * B * C + 4 * W * C + 3 * Real.exp 1 * W * C) * u * (L ^ 2 * P) := by
  subst hxu
  have hW : 0 ≤ W := by nlinarith [hK0.trans hK]
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  generalize Real.exp 1 = e at *
  -- the tails, the left edge and the horizontal edges, using `u / s ≤ u` and `u / s² ≤ u`
  have t1 : 2 * (8 * B * L ^ 2 * C * (e * (u * s))) / (s⁻¹ * s ^ 2) ≤
      16 * e * B * C * (u * (L ^ 2 * P)) := by
    rw [show 2 * (8 * B * L ^ 2 * C * (e * (u * s))) / (s⁻¹ * s ^ 2) =
      16 * e * B * C * (u * L ^ 2) by field_simp; ring]
    gcongr
    exact le_mul_of_one_le_right (by positivity) hP
  have t2 : 4 * (K * C * (u / s)) * l ≤ 4 * W * C * (u * (L ^ 2 * P)) := by
    have h1 : K * C * (u / s) * l ≤ K * C * (u / s) * L :=
      mul_le_mul_of_nonneg_left hl (by positivity)
    have h2 : K * C * (u / s) * L ≤ W * P * C * u * L := by
      gcongr
      exact div_le_self hu hs
    have h3 : W * C * u * (L * P) ≤ W * C * u * (L ^ 2 * P) :=
      mul_le_mul_of_nonneg_left (by gcongr; nlinarith) (by positivity)
    linarith
  have t3 : 2 * (v * (K * C) * (e * (u * s)) / (s⁻¹ * (s ^ 2) ^ 2)) ≤
      3 * e * W * C * (u * (L ^ 2 * P)) := by
    rw [show 2 * (v * (K * C) * (e * (u * s)) / (s⁻¹ * (s ^ 2) ^ 2)) =
      2 * (v * (K * C * e * (u / s ^ 2))) by field_simp]
    have hKCu : K * C * e * (u / s ^ 2) ≤ W * P * C * e * u := by
      gcongr
      exact div_le_self hu (one_le_pow₀ hs)
    have h0 : 0 ≤ 3 * e * W * C * u * P := by positivity
    calc 2 * (v * (K * C * e * (u / s ^ 2))) ≤ 2 * (3 / 2 * (W * P * C * e * u)) := by
          gcongr 2 * ?_
          exact (mul_le_mul_of_nonneg_right hv (by positivity)).trans
            (mul_le_mul_of_nonneg_left hKCu (by norm_num))
      _ = 3 * e * W * C * u * P := by ring
      _ ≤ 3 * e * W * C * (u * (L ^ 2 * P)) := by nlinarith [mul_nonneg h0 (sub_nonneg.2 hL2)]
  have hπ : 1 / (2 * π) ≤ 1 := by rw [div_le_one (by positivity)]; linarith [Real.two_le_pi]
  have hQ : 0 ≤ (16 * e * B * C + 4 * W * C + 3 * e * W * C) * u * (L ^ 2 * P) := by positivity
  calc _ ≤ 1 / (2 * π) * ((16 * e * B * C + 4 * W * C + 3 * e * W * C) * u * (L ^ 2 * P)) := by
        gcongr
        linarith
    _ ≤ _ := mul_le_of_le_one_left hQ hπ

/-- The comparison with the sharp sum, `3B (2εx + 1) L`, and the main term `R · 2 log 2 · ε · x`
at `ε = 1/s` and `x = us` are together at most `(9B + 2R) u L² P`, for `u, s, L, P ≥ 1`. -/
private lemma sharp_and_main_terms_le {B R P L u s x : ℝ} (hB : 0 ≤ B) (hR : 0 ≤ R) (hP : 1 ≤ P)
    (hL : 1 ≤ L) (hs : 1 ≤ s) (hu : 1 ≤ u) (hxu : x = u * s) :
    3 * B * (2 * s⁻¹ * x + 1) * L + R * (2 * Real.log 2 * s⁻¹) * x ≤
      (9 * B + 2 * R) * u * (L ^ 2 * P) := by
  subst hxu
  have hLP : 1 ≤ L ^ 2 * P := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL) hP
  have hLLP : L ≤ L ^ 2 * P := by nlinarith
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  rw [show 3 * B * (2 * s⁻¹ * (u * s) + 1) * L + R * (2 * Real.log 2 * s⁻¹) * (u * s) =
    3 * B * ((2 * u + 1) * L) + 2 * Real.log 2 * (R * u) by field_simp]
  nlinarith [mul_nonneg (mul_nonneg hB (zero_le_one.trans hL)) (sub_nonneg.2 hu),
    mul_nonneg (mul_nonneg hB (by linarith : (0 : ℝ) ≤ u)) (sub_nonneg.2 hLLP),
    mul_nonneg (mul_nonneg hR (by linarith : (0 : ℝ) ≤ u)) (sub_nonneg.2 hLP),
    mul_nonneg (mul_nonneg hR (by linarith : (0 : ℝ) ≤ u)) (sub_nonneg.2 hlog2)]

/-- **The estimate at a given height.** Let `ν` be a `C¹` bump with the uniform Mellin bound `C`
on the strip `1/2 ≤ Re s ≤ 2`, let `‖a(n)‖ ≤ B log(n + 1)`, let `T ≥ 3`, `0 < η ≤ 1/2`,
`x^η = T` and `T² ≤ x`. If `G` is holomorphic and bounded by `M` on the rectangle
`[1 - η, 1 + 1/log x] ×ℂ [-T, T]`, `L(a, s) = G(s) + r/(s - 1)` on `Re s = 1 + 1/log x`, and
`M + ‖r‖/η ≤ W P` with `P ≥ 1`, then `‖∑_{n ≤ x} a(n) - r x‖ ≤ D (x / √T) (log x)² P`. -/
private lemma norm_sum_sub_mul_le_of_height {ν : ℝ → ℝ} (hν : ContDiffOn ℝ 1 ν (Ioi 0))
    (hν0 : ∀ x > 0, 0 ≤ ν x) (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc (1 / 2) 2)
    (hνm : ∫ x in Ioi 0, ν x / x = 1) {C : ℝ}
    (hC : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 →
      ‖mellin (fun x ↦ (smoothCutoff ν ε x : ℂ)) s‖ ≤ C / (‖s‖ * (1 + ε * ‖s‖)))
    {a : ℕ → ℂ} {B : ℝ} (ha : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ B * Real.log (n + 1)) {G : ℂ → ℂ}
    {r : ℂ} {x η T M W P : ℝ} (hT : 3 ≤ T) (hη : 0 < η) (hη2 : η ≤ 1 / 2) (hxT : x ^ η = T)
    (hTx : T ^ 2 ≤ x) (hG : DifferentiableOn ℂ G (Icc (1 - η) (1 + (Real.log x)⁻¹) ×ℂ Icc (-T) T))
    (hGb : ∀ s ∈ Icc (1 - η) (1 + (Real.log x)⁻¹) ×ℂ Icc (-T) T, ‖G s‖ ≤ M)
    (hL : ∀ s : ℂ, s.re = 1 + (Real.log x)⁻¹ → LSeries a s = G s + r / (s - 1))
    (hK : M + ‖r‖ / η ≤ W * P) (hP : 1 ≤ P) :
    ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n - r * x‖ ≤
      (16 * Real.exp 1 * B * C + 4 * W * C + 3 * Real.exp 1 * W * C + 9 * B + 2 * ‖r‖) *
        (x / √T) * (Real.log x ^ 2 * P) := by
  obtain ⟨s, hs0, rfl⟩ : ∃ s, 0 ≤ s ∧ T = s ^ 2 := ⟨√T, Real.sqrt_nonneg T, by
    rw [Real.sq_sqrt (by linarith)]⟩
  rw [Real.sqrt_sq hs0]
  have hs : 1 ≤ s := by nlinarith
  have hx0 : 0 < x := by nlinarith
  have hL1 : 1 ≤ Real.log x :=
    (Real.le_log_iff_exp_le hx0).2 (by nlinarith [Real.exp_one_lt_d9])
  have hlog : (Real.log x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL1
  have hε : 0 < s⁻¹ := by positivity
  have hε1 : s⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs
  have h1mem : (1 : ℂ) ∈ Icc (1 - η) (1 + (Real.log x)⁻¹) ×ℂ Icc (-s ^ 2) (s ^ 2) := by
    refine mem_reProdIm.2 ⟨?_, ?_⟩ <;> simp only [one_re, one_im, mem_Icc]
    · constructor <;> linarith [inv_pos.2 (zero_lt_one.trans_le hL1)]
    · constructor <;> nlinarith
  have hM : 0 ≤ M := (norm_nonneg _).trans (hGb 1 h1mem)
  have h1 := norm_tsum_mul_smoothCutoff_sub_residue_le_of_norm_le_mul_log ha hν hνs hε
    (by nlinarith) hη (by linarith) (by nlinarith) hG.continuousOn
    (hG.mono fun z hz ↦ ⟨Ioo_subset_Icc_self hz.1, Ioo_subset_Icc_self hz.2⟩) hGb hL
    fun z hz1 hz2 ↦ hC s⁻¹ hε hε1 z (by linarith) (by linarith)
  have h2 := TauCeti.norm_sum_sub_tsum_mul_smoothCutoff_le ha hν0 hνs hνm hε hε1 (X := x)
    (by nlinarith)
  have h3 := TauCeti.norm_mellin_smoothCutoff_one_sub_one_le hν0 hνs hνm hε hε1
  have hu : 1 ≤ x / s := by rw [le_div_iff₀ (by linarith)]; nlinarith
  have hy : x ^ (1 - η) = x / s / s := by
    rw [Real.rpow_sub hx0, Real.rpow_one, hxT, div_div, sq]
  have hl : Real.log (1 + s ^ 2 / (1 - η)) ≤ Real.log x := by
    have h1η : 0 < 1 - η := by linarith
    refine Real.log_le_log (by positivity) ?_
    have : s ^ 2 / (1 - η) ≤ 2 * s ^ 2 := by rw [div_le_iff₀ h1η]; nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hT (by positivity : (0 : ℝ) ≤ s ^ 2)]
  have h4 := contour_terms_le (nonneg_of_norm_le_mul_log ha)
    (nonneg_of_norm_mellin_smoothCutoff_le hC) (by positivity) hK hP hL1 hs (u := x / s)
    (v := (Real.log x)⁻¹ + η) (by linarith) (by linarith) hl (by field_simp)
  have h5 := sharp_and_main_terms_le (nonneg_of_norm_le_mul_log ha) (norm_nonneg r) hP hL1 hs hu
    (x := x) (by field_simp)
  rw [hy] at h1
  have hIcc : Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ := Finset.Icc_add_one_left_eq_Ioc 0 _
  set m := mellin (fun y ↦ (smoothCutoff ν s⁻¹ y : ℂ)) 1
  have hdec : ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n - r * x =
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n - ∑' n : ℕ, a n * smoothCutoff ν s⁻¹ (n / x)) +
      (∑' n : ℕ, a n * smoothCutoff ν s⁻¹ (n / x) - r * m * x) + r * (m - 1) * x := by
    rw [hIcc]; ring
  have h6 : ‖r * (m - 1) * x‖ ≤ ‖r‖ * (2 * Real.log 2 * s⁻¹) * x := by
    rw [norm_mul, norm_mul, Complex.norm_of_nonneg hx0.le]
    gcongr
  rw [hdec]
  exact norm_add₃_le.trans (by linarith)

/-- If `ω ≤ 2 log T + log 2`, then the saving `T^{-1/2}` is at most `2 exp(-ω/4)`. -/
private lemma inv_sqrt_le_two_mul_exp {T ω : ℝ} (hT : 0 < T)
    (hω : ω ≤ 2 * Real.log T + Real.log 2) : (√T)⁻¹ ≤ 2 * Real.exp (-(1 / 4) * ω) := calc
  (√T)⁻¹ = Real.exp (-(Real.log T / 2)) := by
    rw [Real.exp_neg, ← Real.log_sqrt hT.le, Real.exp_log (Real.sqrt_pos.2 hT)]
  _ ≤ Real.exp (Real.log 2 + -(1 / 4) * ω) :=
    Real.exp_le_exp.2 (by linarith [Real.log_nonneg one_le_two])
  _ = 2 * Real.exp (-(1 / 4) * ω) := by rw [Real.exp_add, Real.exp_log two_pos]

/-- On the rectangle `[1 - η(T + 3), σ] ×ℂ [-T, T]` with `T + 3 ≤ x`, a bound
`‖G(s)‖ ≤ C₀ log(|Im s| + 3)^{B'}` on the region `1 - η(|Im s| + 3) ≤ Re s` gives
`‖G(s)‖ ≤ |C₀| (log x)^N` for every natural `N ≥ |B'|`. -/
private lemma norm_le_of_mem_reProdIm {η : ℝ → ℝ} (hηa : AntitoneOn η (Ici 3)) {G : ℂ → ℂ}
    {C₀ B' : ℝ}
    (hGb : ∀ s : ℂ, 1 - η (|s.im| + 3) ≤ s.re → ‖G s‖ ≤ C₀ * Real.log (|s.im| + 3) ^ B')
    {N : ℕ} (hB'N : |B'| ≤ N) {T σ x : ℝ} (hTx : T + 3 ≤ x) {s : ℂ}
    (hs : s ∈ Icc (1 - η (T + 3)) σ ×ℂ Icc (-T) T) : ‖G s‖ ≤ |C₀| * Real.log x ^ N := by
  have him := abs_le.2 (mem_reProdIm.1 hs).2
  have h0 := abs_nonneg s.im
  have h1 : 1 ≤ Real.log (|s.im| + 3) :=
    (Real.le_log_iff_exp_le (by linarith)).2 (by linarith [Real.exp_one_lt_d9])
  have h2 : Real.log (|s.im| + 3) ≤ Real.log x := Real.log_le_log (by linarith) (by linarith)
  calc ‖G s‖ ≤ C₀ * Real.log (|s.im| + 3) ^ B' := hGb s (le_re_of_mem_reProdIm hηa hs)
    _ ≤ |C₀| * Real.log (|s.im| + 3) ^ B' :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ ≤ |C₀| * Real.log (|s.im| + 3) ^ (N : ℝ) := by
        gcongr
        exact (le_abs_self _).trans hB'N
    _ ≤ |C₀| * Real.log x ^ N := by
        rw [Real.rpow_natCast]
        gcongr

/-- If `a₀ l^{-A} ≤ η` with `a₀, η > 0`, `l ≥ 1` and `l^A ≤ P`, then
`c P + R/η ≤ (c + R/a₀) P` for `R ≥ 0`: the pole term `‖r‖/η` on the edges is absorbed in the
factor `P` that bounds `G`. -/
private lemma add_div_le_of_mul_rpow_neg_le (c : ℝ) {R a₀ η l A P : ℝ} (hR : 0 ≤ R) (ha₀ : 0 < a₀)
    (hη : 0 < η) (hl : 1 ≤ l) (hlP : l ^ A ≤ P) (hlow : a₀ * l ^ (-A) ≤ η) :
    c * P + R / η ≤ (c + R / a₀) * P := by
  rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, div_le_iff₀ (by positivity)] at hlow
  have h1 : a₀ ≤ η * P := hlow.trans (mul_le_mul_of_nonneg_left hlP hη.le)
  have h2 : R / η ≤ R / a₀ * P := by
    rw [div_mul_eq_mul_div, le_div_iff₀ ha₀, div_mul_eq_mul_div, div_le_iff₀ hη]
    nlinarith
  linarith

/-- **The large-`x` case.** Under the hypotheses of the transfer theorem, let `ν` be a `C¹` bump
with the uniform Mellin bound `C` on the strip `1/2 ≤ Re s ≤ 2`, let `N ≥ |B'|` and `N ≥ A` be
natural, and let `(log x)^{N+2} exp(-ω_η(x)/8) ≤ D'` for `x ≥ 1`. If `x ≥ 1` and
`log 3 ≤ η(6) log x`, then `‖∑_{n ≤ x} a(n) - r x‖ ≤ 2 D D' x exp(-ω_η(x)/8)`. -/
private lemma norm_sum_sub_mul_le_of_log_three_le {ν : ℝ → ℝ} (hν : ContDiffOn ℝ 1 ν (Ioi 0))
    (hν0 : ∀ x > 0, 0 ≤ ν x) (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc (1 / 2) 2)
    (hνm : ∫ x in Ioi 0, ν x / x = 1) {C : ℝ}
    (hC : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 →
      ‖mellin (fun x ↦ (smoothCutoff ν ε x : ℂ)) s‖ ≤ C / (‖s‖ * (1 + ε * ‖s‖)))
    {η : ℝ → ℝ} (hηc : ContinuousOn η (Ici 3)) (hηa : AntitoneOn η (Ici 3))
    (hηhalf : ∀ t, 3 ≤ t → η t ≤ 1 / 2) {a₀ A : ℝ} (ha₀ : 0 < a₀)
    (hηlow : ∀ t, 3 ≤ t → a₀ * Real.log t ^ (-A) ≤ η t) {a : ℕ → ℂ} {B : ℝ}
    (ha : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ B * Real.log (n + 1)) {r : ℂ} {U : Set ℂ}
    (hRU : {s : ℂ | 1 - η (|s.im| + 3) ≤ s.re} ⊆ U) {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G U)
    (hLG : ∀ s : ℂ, 1 < s.re → LSeries a s = G s + r / (s - 1)) {C₀ B' : ℝ}
    (hGb : ∀ s : ℂ, 1 - η (|s.im| + 3) ≤ s.re → ‖G s‖ ≤ C₀ * Real.log (|s.im| + 3) ^ B')
    {N : ℕ} (hB'N : |B'| ≤ N) (hAN : A ≤ N) {D' : ℝ}
    (hD' : ∀ x, 1 ≤ x → Real.log x ^ (N + 2) * Real.exp (-(1 / 8) * inghamExponent η x) ≤ D')
    {x : ℝ} (hx : 1 ≤ x) (h6 : Real.log 3 ≤ η 6 * Real.log x) :
    ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n - r * x‖ ≤
      2 * (16 * Real.exp 1 * B * C + 4 * (|C₀| + ‖r‖ / a₀) * C +
        3 * Real.exp 1 * (|C₀| + ‖r‖ / a₀) * C + 9 * B + 2 * ‖r‖) * D' * x *
      Real.exp (-(1 / 8) * inghamExponent η x) := by
  obtain ⟨T, hT, hxT, hω⟩ := exists_rpow_eq_and_inghamExponent_le hηc hηa hx h6
  have hT3 : (3 : ℝ) ≤ T + 3 := by linarith
  have hηT := pos_of_mul_log_rpow_neg_le ha₀ hηlow hT3
  have hTx : T ^ 2 ≤ x := by
    rw [← hxT, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    simpa using Real.rpow_le_rpow_of_exponent_le hx
      (by push_cast; linarith [hηhalf _ hT3] : η (T + 3) * ((2 : ℕ) : ℝ) ≤ 1)
  have hTL : Real.log (T + 3) ≤ Real.log x := Real.log_le_log (by linarith) (by nlinarith)
  have hL1 : 1 ≤ Real.log (T + 3) :=
    (Real.le_log_iff_exp_le (by linarith)).2 (by linarith [Real.exp_one_lt_d9])
  have hK := add_div_le_of_mul_rpow_neg_le |C₀| (norm_nonneg r) ha₀ hηT hL1
    (P := Real.log x ^ N)
    ((Real.rpow_le_rpow_of_exponent_le hL1 hAN).trans (by rw [Real.rpow_natCast]; gcongr))
    (hηlow _ hT3)
  have h := norm_sum_sub_mul_le_of_height hν hν0 hνs hνm hC ha hT hηT (hηhalf _ hT3)
    hxT hTx (hG.mono fun s hs ↦ hRU (le_re_of_mem_reProdIm hηa hs))
    (fun s hs ↦ norm_le_of_mem_reProdIm hηa hGb hB'N (by nlinarith) hs)
    (fun s hs ↦ hLG s (by rw [hs]; linarith [inv_pos.2 (zero_lt_one.trans_le (hL1.trans hTL))]))
    hK (one_le_pow₀ (hL1.trans hTL))
  -- `x / √T ≤ 2 x exp(-ω/4)`, and `(log x)^{N+2} exp(-ω/8) ≤ D'` absorbs the logarithms
  have hsq : x / √T ≤ 2 * x * (Real.exp (-(1 / 8) * inghamExponent η x) *
      Real.exp (-(1 / 8) * inghamExponent η x)) := by
    rw [← Real.exp_add, div_eq_mul_inv, show -(1 / 8) * inghamExponent η x +
      -(1 / 8) * inghamExponent η x = -(1 / 4) * inghamExponent η x by ring]
    exact (mul_le_mul_of_nonneg_left (inv_sqrt_le_two_mul_exp (by linarith) hω)
      (by linarith)).trans_eq (by ring)
  obtain ⟨D, hD⟩ : ∃ D, D = 16 * Real.exp 1 * B * C + 4 * (|C₀| + ‖r‖ / a₀) * C +
      3 * Real.exp 1 * (|C₀| + ‖r‖ / a₀) * C + 9 * B + 2 * ‖r‖ := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by
    have := nonneg_of_norm_le_mul_log ha
    have := nonneg_of_norm_mellin_smoothCutoff_le hC
    rw [hD]
    positivity
  rw [← hD, ← pow_add, add_comm 2 N] at h
  obtain ⟨e, he⟩ : ∃ e, e = Real.exp (-(1 / 8) * inghamExponent η x) := ⟨_, rfl⟩
  have he0 : 0 < e := he ▸ Real.exp_pos _
  rw [← hD, ← he]
  rw [← he] at hsq
  calc _ ≤ D * (2 * x * (e * e)) * Real.log x ^ (N + 2) := h.trans (by
        gcongr
        exact pow_nonneg (Real.log_nonneg hx) _)
    _ = 2 * D * x * e * (Real.log x ^ (N + 2) * e) := by ring
    _ ≤ 2 * D * x * e * D' := by
        gcongr
        exact he ▸ hD' x hx
    _ = 2 * D * D' * x * e := by ring

/-- **The small-`x` case.** If `‖a(n)‖ ≤ B log(n + 1)`, `0 < η ≤ 1/2` on `[3, ∞)`, `x ≥ 1` and
`η(6) log x < log 3`, then `‖∑_{n ≤ x} a(n) - r x‖ ≤ E x exp(-ω_η(x)/8)` with a constant `E`
depending only on `B`, `‖r‖` and `Λ = log 3 / η(6)`: the trivial bound `(B log(x + 1) + ‖r‖) x`
holds, and `log x < Λ` bounds both `log(x + 1)` and `ω_η(x)`. -/
private lemma norm_sum_sub_mul_le_of_lt_log_three {η : ℝ → ℝ} (hηpos : ∀ t, 3 ≤ t → 0 < η t)
    (hηhalf : ∀ t, 3 ≤ t → η t ≤ 1 / 2) {a : ℕ → ℂ} {B : ℝ}
    (ha : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ B * Real.log (n + 1)) (r : ℂ) {x : ℝ} (hx : 1 ≤ x)
    (h6 : ¬Real.log 3 ≤ η 6 * Real.log x) :
    ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n - r * x‖ ≤ (B * (Real.log 3 / η 6 + 1) + ‖r‖) *
      Real.exp (1 / 8 * (Real.log 3 / η 6 / 2 + Real.log 3)) * x *
      Real.exp (-(1 / 8) * inghamExponent η x) := by
  have hB := nonneg_of_norm_le_mul_log ha
  have hx0 : 0 ≤ x := by linarith
  have hL0 := Real.log_nonneg hx
  have hΛ : Real.log x < Real.log 3 / η 6 := by
    rw [lt_div_iff₀ (hηpos 6 (by norm_num))]
    linarith
  have hsum : ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n‖ ≤ ⌊x⌋₊ * (B * Real.log (x + 1)) := by
    have hn (n : ℕ) (hn : n ∈ Finset.Icc 1 ⌊x⌋₊) : ‖a n‖ ≤ B * Real.log (x + 1) := by
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn
      have : (n : ℝ) ≤ x := (Nat.cast_le.2 h2).trans (Nat.floor_le hx0)
      exact (ha n h1).trans
        (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by linarith)) hB)
    simpa using norm_sum_le_of_le _ hn
  -- `log(x + 1) ≤ log(e x) = 1 + log x`, and `ω_η(x) ≤ η(3) log x + log 3`
  have hlog : Real.log (x + 1) ≤ Real.log 3 / η 6 + 1 := by
    have := Real.log_le_log (by positivity) (by nlinarith [Real.add_one_le_exp 1] :
      x + 1 ≤ Real.exp 1 * x)
    rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp] at this
    linarith
  have hω : inghamExponent η x ≤ Real.log 3 / η 6 / 2 + Real.log 3 :=
    (inghamExponent_le (fun t ht ↦ (hηpos t ht).le) hx le_rfl).trans
      (by nlinarith [hηhalf 3 le_rfl])
  have hexp : 1 ≤ Real.exp (1 / 8 * (Real.log 3 / η 6 / 2 + Real.log 3)) *
      Real.exp (-(1 / 8) * inghamExponent η x) := by
    rw [← Real.exp_add, Real.one_le_exp_iff]
    linarith
  calc _ ≤ ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n‖ + ‖r * x‖ := norm_sub_le _ _
    _ ≤ (B * (Real.log 3 / η 6 + 1) + ‖r‖) * x := by
        rw [norm_mul, Complex.norm_of_nonneg hx0]
        nlinarith [Nat.floor_le hx0, mul_le_mul_of_nonneg_left hlog hB,
          mul_nonneg hB (Real.log_nonneg (by linarith : (1 : ℝ) ≤ x + 1))]
    _ ≤ (B * (Real.log 3 / η 6 + 1) + ‖r‖) * x * (Real.exp (1 / 8 *
          (Real.log 3 / η 6 / 2 + Real.log 3)) * Real.exp (-(1 / 8) * inghamExponent η x)) :=
        le_mul_of_one_le_right (mul_nonneg (add_nonneg (mul_nonneg hB (by linarith))
          (norm_nonneg r)) hx0) hexp
    _ = _ := by ring

/-- **The transfer theorem for `η ≤ 1/2`**, with `c = 1/8`. -/
private lemma norm_sum_sub_mul_le_of_zeroFreeRegion_of_le_half {η : ℝ → ℝ}
    (hηc : ContinuousOn η (Ici 3)) (hηa : AntitoneOn η (Ici 3))
    (hηhalf : ∀ t, 3 ≤ t → η t ≤ 1 / 2) {a₀ A : ℝ} (ha₀ : 0 < a₀)
    (hηlow : ∀ t, 3 ≤ t → a₀ * Real.log t ^ (-A) ≤ η t) {a : ℕ → ℂ} {B : ℝ}
    (ha : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ B * Real.log (n + 1)) {r : ℂ} {U : Set ℂ}
    (hRU : {s : ℂ | 1 - η (|s.im| + 3) ≤ s.re} ⊆ U) {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G U)
    (hLG : ∀ s : ℂ, 1 < s.re → LSeries a s = G s + r / (s - 1)) {C₀ B' : ℝ}
    (hGb : ∀ s : ℂ, 1 - η (|s.im| + 3) ≤ s.re → ‖G s‖ ≤ C₀ * Real.log (|s.im| + 3) ^ B') :
    ∃ c > 0, ∃ C' : ℝ, ∀ x : ℝ, 3 ≤ x →
      ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n - r * x‖ ≤ C' * x * Real.exp (-c * inghamExponent η x) := by
  obtain ⟨ν, hνd, hν0, hνs, hνm, -⟩ := exists_smooth_symmetric_bump one_lt_two
  have hνs' : Function.support ν ∩ Ioi 0 ⊆ Icc (1 / 2) 2 := fun y hy ↦ by
    simpa only [one_div] using hνs hy.1
  have hν1 : ContDiffOn ℝ 1 ν (Ioi 0) := (hνd.of_le (by exact_mod_cast le_top)).contDiffOn
  obtain ⟨C, hC⟩ := exists_norm_mellin_smoothCutoff_le (k := 1) hν1 hνs' (σ₁ := 1 / 2) (σ₂ := 2)
    (by norm_num)
  simp only [pow_one] at hC
  have hN := Nat.le_ceil (max |B'| A)
  obtain ⟨D', hD'⟩ := exists_log_pow_mul_exp_neg_inghamExponent_le ha₀ (c := 1 / 8)
    (by norm_num) hηlow (⌈max |B'| A⌉₊ + 2)
  obtain ⟨D, hD⟩ : ∃ D, D = 16 * Real.exp 1 * B * C + 4 * (|C₀| + ‖r‖ / a₀) * C +
      3 * Real.exp 1 * (|C₀| + ‖r‖ / a₀) * C + 9 * B + 2 * ‖r‖ := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = (B * (Real.log 3 / η 6 + 1) + ‖r‖) *
      Real.exp (1 / 8 * (Real.log 3 / η 6 / 2 + Real.log 3)) := ⟨_, rfl⟩
  refine ⟨1 / 8, by norm_num, max (2 * D * D') E, fun x hx ↦ ?_⟩
  have hx1 : 1 ≤ x := by linarith
  by_cases h6 : Real.log 3 ≤ η 6 * Real.log x
  · refine (norm_sum_sub_mul_le_of_log_three_le hν1 (fun y _ ↦ hν0 y) hνs' hνm hC hηc hηa
      hηhalf ha₀ hηlow ha hRU hG hLG hGb ((le_max_left _ _).trans hN)
      ((le_max_right _ _).trans hN) hD' hx1 h6).trans ?_
    rw [← hD]
    gcongr
    exact le_max_left _ _
  · refine (norm_sum_sub_mul_le_of_lt_log_three
    (fun _ ↦ pos_of_mul_log_rpow_neg_le ha₀ hηlow) hηhalf ha r hx1 h6).trans ?_
    rw [← hE]
    gcongr
    exact le_max_right _ _


/-- For `t ≥ 3`, `a₀ (log t)^{-A} ≤ η(t)` gives
`min a₀ (1/2) · (log t)^{-max A 0} ≤ min (η t) (1/2)`, since `log t ≥ 1`. -/
private lemma mul_log_rpow_neg_le_min {η : ℝ → ℝ} {a₀ A : ℝ} (ha₀ : 0 < a₀)
    (hηlow : ∀ t, 3 ≤ t → a₀ * Real.log t ^ (-A) ≤ η t) {t : ℝ} (ht : 3 ≤ t) :
    min a₀ (1 / 2) * Real.log t ^ (-max A 0) ≤ min (η t) (1 / 2) := by
  have hl : 1 ≤ Real.log t :=
    (Real.le_log_iff_exp_le (by linarith)).2 (by linarith [Real.exp_one_lt_d9])
  have h0 : 0 ≤ Real.log t ^ (-max A 0) := Real.rpow_nonneg (by linarith) _
  refine le_min ((mul_le_mul (min_le_left _ _) (Real.rpow_le_rpow_of_exponent_le hl
    (neg_le_neg (le_max_left _ _))) h0 ha₀.le).trans (hηlow t ht)) ?_
  exact (mul_le_of_le_one_right (le_min ha₀.le one_half_pos.le)
    (Real.rpow_le_one_of_one_le_of_nonpos hl (neg_nonpos.2 (le_max_right _ _)))).trans
    (min_le_right _ _)

/-- **Ingham's transfer theorem.** Let `η` be continuous and nonincreasing on `[3, ∞)` with
`η(t) ≥ a₀ (log t)^{-A}` there, `a₀ > 0`. Let `‖a(n)‖ ≤ B log(n + 1)` for `n ≥ 1`, let `U` contain
`R_η = {s : 1 - η(|Im s| + 3) ≤ Re s}`, and let `G` be holomorphic on `U` with
`L(a, s) = G(s) + r/(s - 1)` for `Re s > 1` and `‖G(s)‖ ≤ C₀ log(|Im s| + 3)^{B'}` on `R_η`. Then
there are `c > 0` and `C'` with `‖∑_{n ≤ x} a(n) - r x‖ ≤ C' x exp(-c ω_η(x))` for every `x ≥ 3`,
where `ω_η` is the Ingham exponent `TauCeti.inghamExponent`. -/
theorem norm_sum_sub_mul_le_of_zeroFreeRegion {η : ℝ → ℝ} (hηc : ContinuousOn η (Ici 3))
    (hηa : AntitoneOn η (Ici 3)) {a₀ A : ℝ} (ha₀ : 0 < a₀)
    (hηlow : ∀ t, 3 ≤ t → a₀ * Real.log t ^ (-A) ≤ η t) {a : ℕ → ℂ} {B : ℝ}
    (ha : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ B * Real.log (n + 1)) {r : ℂ} {U : Set ℂ}
    (hRU : {s : ℂ | 1 - η (|s.im| + 3) ≤ s.re} ⊆ U) {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G U)
    (hLG : ∀ s : ℂ, 1 < s.re → LSeries a s = G s + r / (s - 1)) {C₀ B' : ℝ}
    (hGb : ∀ s : ℂ, 1 - η (|s.im| + 3) ≤ s.re → ‖G s‖ ≤ C₀ * Real.log (|s.im| + 3) ^ B') :
    ∃ c > 0, ∃ C' : ℝ, ∀ x : ℝ, 3 ≤ x →
      ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n - r * x‖ ≤ C' * x * Real.exp (-c * inghamExponent η x) := by
  -- apply the case `η ≤ 1/2` to `min η (1/2)`, whose region lies inside `R_η`
  have hsub : {s : ℂ | 1 - min (η (|s.im| + 3)) (1 / 2) ≤ s.re} ⊆
      {s : ℂ | 1 - η (|s.im| + 3) ≤ s.re} :=
    ofPred_subset_ofPred.2 fun _ hs ↦ (sub_le_sub_left (min_le_left _ _) 1).trans hs
  obtain ⟨c, hc, C', hC'⟩ := norm_sum_sub_mul_le_of_zeroFreeRegion_of_le_half
    (η := fun t ↦ min (η t) (1 / 2)) (hηc.inf continuousOn_const)
    (fun _ hs _ ht hst ↦ min_le_min_right _ (hηa hs ht hst)) (fun _ _ ↦ min_le_right _ _)
    (lt_min ha₀ one_half_pos) (fun _ ↦ mul_log_rpow_neg_le_min ha₀ hηlow) ha (hsub.trans hRU) hG
    hLG fun s hs ↦ hGb s (hsub hs)
  -- `min η (1/2) ≥ κ η` with `κ = min 1 (1 / (2 η(3)))`, since `η ≤ η(3)`
  have hη3 := pos_of_mul_log_rpow_neg_le ha₀ hηlow le_rfl
  have hκ : 0 < min 1 (1 / (2 * η 3)) := lt_min one_pos (by positivity)
  have hle (t : ℝ) (ht : 3 ≤ t) : min 1 (1 / (2 * η 3)) * η t ≤ min (η t) (1 / 2) := by
    have hηt := (pos_of_mul_log_rpow_neg_le ha₀ hηlow ht).le
    refine le_min (mul_le_of_le_one_left hηt (min_le_left _ _)) ?_
    calc min 1 (1 / (2 * η 3)) * η t ≤ 1 / (2 * η 3) * η 3 :=
          mul_le_mul (min_le_right _ _) (hηa (mem_Ici.2 le_rfl) (mem_Ici.2 ht) ht) hηt
            (by positivity)
      _ = 1 / 2 := by field_simp
  refine ⟨c * min 1 (1 / (2 * η 3)), mul_pos hc hκ, max C' 0, fun x hx ↦ (hC' x hx).trans ?_⟩
  have hω := mul_inghamExponent_le hκ.le (min_le_left _ _)
    (fun t ht ↦ (pos_of_mul_log_rpow_neg_le ha₀ hηlow ht).le) hle (by linarith : (1 : ℝ) ≤ x)
  calc _ ≤ max C' 0 * x * Real.exp (-c * inghamExponent (fun t ↦ min (η t) (1 / 2)) x) := by
        gcongr
        exact le_max_left _ _
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
        linarith [mul_le_mul_of_nonneg_left hω hc.le]

end TauCeti.LSeries
