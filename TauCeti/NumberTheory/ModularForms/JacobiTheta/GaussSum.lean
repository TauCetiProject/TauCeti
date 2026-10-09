/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import TauCeti.NumberTheory.ModularForms.JacobiTheta.OneVariable
import TauCeti.Topology.Algebra.InfiniteSum.NatInt

/-!
# The quadratic Gauss sum, from the Jacobi theta function

For every natural number `N`, Gauss's evaluation of the quadratic Gauss sum is

```text
∑_{r = 0}^{N - 1} e^{2πi r² / N} = (1 + i) / 2 · (1 + (-i)^N) · √N,
```

that is `√N`, `0`, `i√N` or `(1 + i)√N` according as `N ≡ 1, 2, 3, 0 (mod 4)` (for `N = 0`
both sides vanish). Mathlib's
`gaussSum_sq` determines the square of a quadratic Gauss sum, so only its sign is new here, and
the sign is genuinely archimedean: it depends on the choice of `e^{2πi/N}` among the primitive
`N`-th roots of unity.

The proof compares two asymptotic expansions of the Jacobi theta function
`θ(τ) = ∑_n e^{πi n² τ}` (Mathlib's `jacobiTheta`) as `τ` tends to the cusp `2/N`, along the
curve `τ = -1 / (iY - N/2)`, `Y → 0⁺`. Splitting `n` into residue classes modulo `N` and applying
the functional equation `jacobiTheta₂_functional_equation` to each class expresses `θ(τ)` through
the Gauss sum; splitting `n` by parity and applying the functional equation to
`θ(-1/τ) = θ(iY - N/2)` expresses it through `θ(iY)` and `θ(4iY)`. The square roots of the two
functional equations combine to the constant `(1 + i)√N` exactly, so the two expansions give an
identity for every `Y > 0`. As `Y → 0⁺` the theta arguments in this identity, `i/Y`, `i/(4Y)` and
the transformed arguments `1/(2N) + i/(4Y)` of the residue-class series, all tend to `i∞`, so
their theta values tend to `1` (`θ(τ) → 1` as `im τ → ∞`), and the identity becomes the
evaluation. This is the classical theta-function route of Landsberg and Schaar.

## Main results

* `TauCeti.sum_range_cexp_two_pi_I_sq_div`: Gauss's evaluation of the quadratic Gauss sum.

## References

* C. F. Gauss, *Summatio quarumdam serierum singularium* (1811).
* H. Rademacher, *Topics in Analytic Number Theory*, Chapter 9 (the Landsberg–Schaar relation).
* B. C. Berndt, R. J. Evans and K. S. Williams, *Gauss and Jacobi Sums*, Chapter 1.
-/

public section

open Complex Filter Topology
open scoped Real

namespace TauCeti

/-- Adding an integer multiple of `2πi` does not change `cexp`. -/
private theorem cexp_add_int_mul_two_pi_I (x : ℂ) (k : ℤ) :
    cexp (x + k * (2 * π * I)) = cexp x := by
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Splitting `θ(2/N + δ)` into the residue classes of `n` modulo `N`: on the class of `r` the
factor `e^{πi n² · 2/N}` is the constant `e^{2πi r²/N}`, and the remaining shifted theta series
in `T = N²δ` is transformed by the functional equation. -/
private theorem jacobiTheta_two_div_add (N : ℕ) [NeZero N] {δ : ℂ} (hδ : 0 < δ.im) :
    jacobiTheta (2 / N + δ) = 1 / (-I * (N ^ 2 * δ)) ^ (1 / 2 : ℂ) *
      ∑ r : Fin N, cexp (2 * π * I * (r : ℕ) ^ 2 / N) *
        jacobiTheta₂ ((r : ℕ) / N) (-1 / (N ^ 2 * δ)) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hδ0 : δ ≠ 0 := fun h ↦ by simp [h] at hδ
  set T : ℂ := N ^ 2 * δ with hT
  have hT0 : T ≠ 0 := mul_ne_zero (pow_ne_zero 2 hN) hδ0
  have hτ : 0 < (2 / (N : ℂ) + δ).im := by
    rw [add_im, ← ofReal_natCast, ← ofReal_ofNat, ← ofReal_div, ofReal_im, zero_add]
    exact hδ
  rw [jacobiTheta_eq_jacobiTheta₂, jacobiTheta₂,
    tsum_int_eq_sum_fin_tsum ((summable_jacobiTheta₂_term_iff _ _).2 hτ) N, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  set a : ℂ := (r : ℕ) / N with ha
  -- Each residue class is a shifted theta series in `T`, to which the functional equation applies.
  have hterm (q : ℤ) : jacobiTheta₂_term (q * N + (r : ℕ)) 0 (2 / N + δ) =
      cexp (2 * π * I * (r : ℕ) ^ 2 / N) * cexp (π * I * T * a ^ 2) *
        jacobiTheta₂_term q (T * a) T := by
    rw [jacobiTheta₂_term, jacobiTheta₂_term, ← Complex.exp_add, ← Complex.exp_add,
      ← cexp_add_int_mul_two_pi_I _ (-(q ^ 2 * N + 2 * q * (r : ℕ)))]
    congr 1
    rw [hT, ha]
    push_cast
    field_simp
    ring
  rw [tsum_congr hterm, tsum_mul_left, ← jacobiTheta₂, jacobiTheta₂_functional_equation,
    mul_div_cancel_left₀ _ hT0]
  have hcancel : cexp (π * I * T * a ^ 2) * cexp (-π * I * (T * a) ^ 2 / T) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    field_simp
    ring
  linear_combination (1 / (-I * T) ^ (1 / 2 : ℂ) * cexp (2 * π * I * (r : ℕ) ^ 2 / N) *
    jacobiTheta₂ a (-1 / T)) * hcancel

/-- The principal square root of `w ^ 2` is `w` when `w` lies in the right half-plane. -/
private theorem cpow_one_div_two_eq_of_sq {w z : ℂ} (h : w ^ 2 = z) (hw : 0 < w.re) :
    z ^ (1 / 2 : ℂ) = w := by
  rw [← h, one_div]
  exact sq_cpow_two_inv hw

/-- The two expansions of `θ(τ)` at `τ = -1 / (iY - N/2)`, equated. The square roots arising
from the two functional equations combine to the constant `(1 + i)√N`. -/
private theorem sum_mul_jacobiTheta₂_eq (N : ℕ) [NeZero N] {Y : ℝ} (hY : 0 < Y) :
    ∑ r : Fin N, cexp (2 * π * I * (r : ℕ) ^ 2 / N) *
        jacobiTheta₂ ((r : ℕ) / N) (1 / (2 * N) + I / (4 * Y)) =
      √N * (1 + I) * (cexp (-π * I * N / 2) * jacobiTheta (I / Y) +
        (1 - cexp (-π * I * N / 2)) / 2 * jacobiTheta (I / (4 * Y))) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
  have hY0 : (Y : ℂ) ≠ 0 := ofReal_ne_zero.2 hY.ne'
  -- Proof structure: with `u = Y + iN/2` and `s = √u`, take `τ = i/u`. The first expansion
  -- (`jacobiTheta_two_div_add`) writes `θ(τ)` through the Gauss sum with the factor
  -- `1 / √(-iN²(τ - 2/N)) = s / ((1 + i)√(NY))`; the second (the functional equation at `τ`,
  -- then `jacobiTheta_sub_natCast_div_two` and `jacobiTheta_I_mul`) writes it as
  -- `s · θ(iY - N/2)`. Both square roots are identified by squaring.
  set u : ℂ := Y + I * (N / 2) with hu
  have hure : u.re = Y := by simp [hu]
  have huim : u.im = N / 2 := by simp [hu]
  have hu0 : u ≠ 0 := fun h ↦ hY.ne' (by rw [← hure, h, zero_re])
  set s : ℂ := u ^ (2⁻¹ : ℂ) with hs
  have hs2 : s ^ 2 = u := cpow_ofNat_inv_pow u 2
  have hsre : 0 < s.re := by
    rw [hs, cpow_inv_two_re, hure]
    exact Real.sqrt_pos.2 (by positivity)
  have hsim : 0 ≤ s.im := by
    rw [hs, cpow_inv_two_im_eq_sqrt (by rw [huim]; positivity)]
    exact Real.sqrt_nonneg _
  have hs0 : s ≠ 0 := fun h ↦ by simp [h] at hsre
  have hnormSq : 0 < normSq s := normSq_pos.2 hs0
  -- The point `τ = i / u` has `-1 / τ = iY - N/2`, and `τ - 2/N` scaled by `N²` is `-2NY / u`.
  set τ : ℂ := I / u with hτ
  have hτim : 0 < τ.im := by
    rw [hτ, div_im]
    simp only [I_im, I_re, one_mul, zero_mul, zero_div, sub_zero, hure]
    exact div_pos hY (normSq_pos.2 hu0)
  have hδim : 0 < (τ - 2 / N).im := by
    rw [sub_im, ← ofReal_natCast, ← ofReal_ofNat, ← ofReal_div, ofReal_im, sub_zero]
    exact hτim
  have hT : (N : ℂ) ^ 2 * (τ - 2 / N) = -(2 * N * Y) / u := by
    rw [hτ, eq_div_iff hu0]
    field_simp
    rw [hu]
    ring
  have hTinv : -1 / ((N : ℂ) ^ 2 * (τ - 2 / N)) = 1 / (2 * N) + I / (4 * Y) := by
    rw [hT, hu]
    field_simp
    ring
  have hsqrtT : (-I * ((N : ℂ) ^ 2 * (τ - 2 / N))) ^ (1 / 2 : ℂ) = (1 + I) * √(N * Y) * s⁻¹ := by
    refine cpow_one_div_two_eq_of_sq ?_ ?_
    · rw [mul_pow, mul_pow, inv_pow, hs2, ← ofReal_pow, Real.sq_sqrt (by positivity), hT]
      field_simp
      ring_nf
      rw [I_sq]
      push_cast
      ring
    · rw [mul_comm (1 + I), mul_assoc, re_ofReal_mul]
      refine mul_pos (Real.sqrt_pos.2 (by positivity)) ?_
      have : ((1 + I) * s⁻¹).re = (s.re + s.im) / normSq s := by
        simp only [mul_re, add_re, add_im, one_re, one_im, I_re, I_im, inv_re, inv_im]
        ring
      rw [this]
      positivity
  have hsqrtτ : (-I * τ) ^ (1 / 2 : ℂ) = s⁻¹ := by
    refine cpow_one_div_two_eq_of_sq ?_ ?_
    · rw [inv_pow, hs2, hτ]
      field_simp
      rw [I_sq, neg_neg]
    · rw [inv_re]
      exact div_pos hsre hnormSq
  -- The first expansion.
  have hA := jacobiTheta_two_div_add N hδim
  rw [add_sub_cancel, hTinv, hsqrtT] at hA
  -- The second expansion.
  have hF : jacobiTheta τ = s * jacobiTheta (I * Y - N / 2) := by
    rw [jacobiTheta_eq_jacobiTheta₂, jacobiTheta₂_functional_equation, hsqrtτ,
      jacobiTheta_eq_jacobiTheta₂]
    have : -1 / τ = I * Y - N / 2 := by
      rw [hτ, hu]
      field_simp
      ring_nf
      rw [I_sq]
      ring
    simp [this]
  have hB := jacobiTheta_sub_natCast_div_two N (τ := I * Y) (by simpa using hY)
  have hC1 := jacobiTheta_I_mul hY
  have hC4' : jacobiTheta (I * (4 * Y)) = jacobiTheta (I / (4 * Y)) / (2 * √Y) := by
    have h4 : √(4 * Y) = 2 * √Y := by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have h := jacobiTheta_I_mul (y := 4 * Y) (by positivity)
    rw [h4] at h
    push_cast at h
    exact h
  rw [show (4 : ℂ) * (I * Y) = I * (4 * Y) by ring, hC4', hC1] at hB
  have hI : (1 + I) ≠ 0 := fun h ↦ by simpa using congrArg re h
  have hsN : ((√N : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 hNpos).ne'
  have hsY : ((√Y : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 hY).ne'
  rw [Real.sqrt_mul hNpos.le, ofReal_mul, hF, hB] at hA
  -- What remains is an identity of rational functions in these atoms.
  generalize cexp (-π * I * N / 2) = ω at hA ⊢
  generalize jacobiTheta (I / Y) = A at hA ⊢
  generalize jacobiTheta (I / (4 * Y)) = B at hA ⊢
  generalize ∑ r : Fin N, cexp (2 * π * I * (r : ℕ) ^ 2 / N) *
    jacobiTheta₂ ((r : ℕ) / N) (1 / (2 * N) + I / (4 * Y)) = S at hA ⊢
  field_simp at hA
  linear_combination -hA / 2

/-- As `Y → 0⁺`, the point `i / (cY)` tends to `i∞`. -/
private theorem tendsto_I_div_nhdsGT_zero (c : ℝ) (hc : 0 < c) :
    Tendsto (fun Y : ℝ ↦ I / (c * Y)) (𝓝[>] 0) (comap im atTop) := by
  refine tendsto_comap_iff.2 ?_
  have : (fun Y : ℝ ↦ (I / (c * Y)).im) = fun Y ↦ c⁻¹ * Y⁻¹ := by
    ext Y
    rw [← ofReal_mul, div_ofReal_im, I_im, one_div, mul_inv]
  rw [Function.comp_def, this]
  exact tendsto_inv_nhdsGT_zero.const_mul_atTop (inv_pos.2 hc)

/-- **Gauss's evaluation of the quadratic Gauss sum**: for every natural number `N`,
`∑_{r < N} e^{2πi r²/N} = (1 + i)/2 · (1 + (-i)^N) · √N`. -/
theorem sum_range_cexp_two_pi_I_sq_div (N : ℕ) :
    ∑ r ∈ Finset.range N, cexp (2 * π * I * r ^ 2 / N) = (1 + I) / 2 * (1 + (-I) ^ N) * √N := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp
  have : NeZero N := ⟨hN⟩
  set ω : ℂ := cexp (-π * I * N / 2) with hω
  have hω' : ω = (-I) ^ N := by
    rw [hω, ← exp_neg_pi_div_two_mul_I, ← Complex.exp_nat_mul]
    ring_nf
  -- Let `Y → 0⁺` in the exact identity `sum_mul_jacobiTheta₂_eq`.
  have hθ (c : ℝ) (hc : 0 < c) :
      Tendsto (fun Y : ℝ ↦ jacobiTheta (I / (c * Y))) (𝓝[>] 0) (𝓝 1) :=
    tendsto_jacobiTheta_comap_im_atTop.comp (tendsto_I_div_nhdsGT_zero c hc)
  have hR : Tendsto (fun Y : ℝ ↦ √N * (1 + I) * (ω * jacobiTheta (I / Y) +
      (1 - ω) / 2 * jacobiTheta (I / (4 * Y)))) (𝓝[>] 0)
      (𝓝 (√N * (1 + I) * (ω * 1 + (1 - ω) / 2 * 1))) := by
    have h1 := hθ 1 one_pos
    simp only [ofReal_one, one_mul] at h1
    have h4 := hθ 4 (by norm_num)
    push_cast at h4
    exact ((h1.const_mul ω).add (h4.const_mul _)).const_mul _
  have hL : Tendsto (fun Y : ℝ ↦ ∑ r : Fin N, cexp (2 * π * I * (r : ℕ) ^ 2 / N) *
      jacobiTheta₂ ((r : ℕ) / N) (1 / (2 * N) + I / (4 * Y))) (𝓝[>] 0)
      (𝓝 (∑ r : Fin N, cexp (2 * π * I * (r : ℕ) ^ 2 / N) * 1)) := by
    refine tendsto_finsetSum _ fun r _ ↦ (Tendsto.const_mul _ ?_)
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim := (tendsto_iff_norm_sub_tendsto_zero.1 (hθ 4 (by norm_num)))
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with Y (hY : 0 < Y)
    have him : (1 / (2 * (N : ℂ)) + I / (4 * Y)).im = 1 / (4 * Y) := by
      rw [add_im, ← ofReal_natCast, ← ofReal_ofNat, ← ofReal_mul, ← ofReal_one, ← ofReal_div,
        ofReal_im, zero_add, ← ofReal_ofNat, ← ofReal_mul, div_ofReal_im, I_im]
    refine (norm_jacobiTheta₂_sub_one_le (by simp) (by rw [him]; positivity)).trans_eq ?_
    rw [him]
    congr 3
    push_cast
    field_simp
  have heq := tendsto_nhds_unique (hL.congr' (eventually_nhdsWithin_of_forall (s := Set.Ioi 0)
    fun _ hY ↦ sum_mul_jacobiTheta₂_eq N hY)) hR
  rw [← Fin.sum_univ_eq_sum_range (fun r ↦ cexp (2 * π * I * r ^ 2 / N))]
  simp only [mul_one] at heq
  rw [heq, ← hω']
  ring

end TauCeti
