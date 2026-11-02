/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import TauCeti.NumberTheory.ModularForms.SiegelFunction.Bounds
public import TauCeti.NumberTheory.ModularForms.SiegelFunction.JInvariant

/-!
# Recovering the discriminant from the six singular values of `j`

In Heegner's and Stark's proof of the class number one theorem, the remaining branch ends with the
value of the cube root `γ₂` of `j` at the CM point `τ_D` of an imaginary quadratic field of
discriminant `D` being one of `0, -32, -96, -960, -5280, -640320`
(`TauCeti.mem_image_intCast_of_tschirnhausPolynomial_X_pow_four_eq`). Then `j(τ_D) = γ₂(τ_D)³` is
the cube of one of these integers, and this file recovers `D` from that value. The CM point has
imaginary part `√|D| / 2`, and the six values belong to `|D| = 3, 11, 19, 43, 67, 163`.

The argument is a rigorous enclosure of the `q`-expansion of `j` at `i∞`, with an explicit tail.
Write `q = e^{2π i τ}` and `A = |q| = e^{-2π Im τ}`. The twelfth power of the Siegel function
`g₀ = g_{(0, 1/2)}` is `x = 4096 q ∏_{n ≥ 1} (1 + qⁿ)²⁴`
(`siegelFunction_zero_half_pow_twelve`), and the product is within `A / (1 - 2A)` of `1`, so
`|x| = 4096 A (1 + O(A))` (`norm_siegelFunction_zero_half_pow_twelve_le`,
`le_norm_siegelFunction_zero_half_pow_twelve`). Weber's cubic `(x + 16)³ = j x`
(`siegelFunction_zero_half_pow_twelve_add_sixteen_pow_three`) and `j = v³` give
`|x + 16|³ = |v|³ |x|`. For `Im τ = √n / 2` with `n ≥ 3` this pins down `A = e^{-π √n}` to within
a few percent:

* if `n` is larger than the expected value, `|x|` is so small that `|v|³ |x| < (16 - |x|)³`;
* if `n` is smaller (but at least `3`), `|x|` lies in an interval on which the concave function
  `|v|³ t - (16 + t)³` is positive at both ends.

Certified rational bounds on `π`, `e`, square roots and the exponential series turn both cases
into exact rational inequalities. The closest call is `n = 163` against `n = 162`, where the
two sides differ by about half a percent.

## Main results

* `TauCeti.ModularForm.mk_mem_of_j_eq_intCast_pow_three`: if `Im τ = √n / 2` with `n ≥ 3` and
  `j(τ) = v³` with `v ∈ {0, -32, -96, -960, -5280, -640320}`, then `(n, v)` is one of
  `(3, 0), (11, -32), (19, -96), (43, -960), (67, -5280), (163, -640320)`.
* `TauCeti.ModularForm.mem_of_j_eq_intCast_pow_three`: in particular
  `n ∈ {3, 11, 19, 43, 67, 163}`.

## References

* H. M. Stark, *On the “gap” in a theorem of Heegner*, J. Number Theory 1 (1969), 16–27.
* D. A. Cox, *Primes of the Form x² + ny²*, §12 (Weber's functions and the singular values of
  `γ₂`).
-/

public section

open Complex
open UpperHalfPlane hiding I
open scoped Real

namespace TauCeti.ModularForm

/-! ### Weber's cubic in norms -/

/-- If `j(τ) = v³`, then Weber's cubic gives `|g₀¹² + 16|³ = |v|³ |g₀¹²|`. -/
private theorem norm_siegelFunction_zero_half_pow_twelve_add_sixteen_pow_three {τ : ℍ} {v : ℂ}
    (hj : j τ = v ^ 3) :
    ‖siegelFunction ![0, 1 / 2] τ ^ 12 + 16‖ ^ 3 =
      ‖v‖ ^ 3 * ‖siegelFunction ![0, 1 / 2] τ ^ 12‖ := by
  have h := congrArg norm (siegelFunction_zero_half_pow_twelve_add_sixteen_pow_three τ)
  rwa [hj, norm_pow, norm_mul, norm_pow] at h

/-! ### Excluding imaginary parts that are too large or too small -/

/-- If `j(τ) = v³` and `|q| ≤ α` with `T = 4096 α U` so small that `|v|³ T < (16 - T)³`, there is
no such `τ`. Here `U` bounds the product factor `|∏_{n ≥ 1} (1 + qⁿ)|²⁴` through `|q| ≤ α'`. -/
private theorem false_of_norm_le {τ : ℍ} {v : ℂ} (hj : j τ = v ^ 3) {α α' U : ℝ}
    (hq : ‖cexp (2 * π * I * τ)‖ ≤ α) (hα' : 2 * α' < 1) (hq' : ‖cexp (2 * π * I * τ)‖ ≤ α')
    (hU : (1 + α' / (1 - 2 * α')) ^ 24 ≤ U) (hT : 4096 * α * U ≤ 16)
    (hcert : ‖v‖ ^ 3 * (4096 * α * U) < (16 - 4096 * α * U) ^ 3) : False := by
  set A := ‖cexp (2 * π * I * τ)‖
  have hA : 0 ≤ A := norm_nonneg _
  have hU₀ : 0 ≤ U := (by positivity : (0 : ℝ) ≤ (1 + α' / (1 - 2 * α')) ^ 24).trans hU
  have hQ₀ : 0 ≤ A / (1 - 2 * A) := div_nonneg hA (by linarith)
  have hQ := div_le_div₀ (hA.trans hq') hq' (by linarith) (by linarith : 1 - 2 * α' ≤ 1 - 2 * A)
  have hP : (1 + A / (1 - 2 * A)) ^ 24 ≤ U := le_trans (by gcongr) hU
  have hx : ‖siegelFunction ![0, 1 / 2] τ ^ 12‖ ≤ 4096 * A * U :=
    (norm_siegelFunction_zero_half_pow_twelve_le τ.im_pos (by linarith)).trans (by gcongr)
  set t := ‖siegelFunction ![0, 1 / 2] τ ^ 12‖
  have ht : t ≤ 4096 * α * U := hx.trans (by gcongr)
  -- `16 - t ≤ |x + 16|`.
  have hlow : 16 - t ≤ ‖siegelFunction ![0, 1 / 2] τ ^ 12 + 16‖ := by
    have := norm_sub_norm_le (16 : ℂ) (-(siegelFunction ![0, 1 / 2] τ ^ 12))
    rw [sub_neg_eq_add, add_comm, norm_neg, Complex.norm_ofNat] at this
    linarith
  have h := norm_siegelFunction_zero_half_pow_twelve_add_sixteen_pow_three hj
  have h₁ : (16 - 4096 * α * U) ^ 3 ≤ (16 - t) ^ 3 := by gcongr
  have h₂ : (16 - t) ^ 3 ≤ ‖siegelFunction ![0, 1 / 2] τ ^ 12 + 16‖ ^ 3 := by
    gcongr
    linarith
  have h₃ : ‖v‖ ^ 3 * t ≤ ‖v‖ ^ 3 * (4096 * α * U) := by gcongr
  linarith

/-- If `j(τ) = v³` and `β ≤ |q| ≤ α`, where `|v|³ t > (16 + t)³` at both ends of the resulting
interval `[4096 β L, 4096 α U]` for `|g₀¹²|`, there is no such `τ`. -/
private theorem false_of_le_norm {τ : ℍ} {v : ℂ} (hj : j τ = v ^ 3) {α β L U : ℝ}
    (hα : 3 * α < 1) (hq : ‖cexp (2 * π * I * τ)‖ ≤ α) (hβ : β ≤ ‖cexp (2 * π * I * τ)‖)
    (hβ₀ : 0 ≤ β) (hU : (1 + α / (1 - 2 * α)) ^ 24 ≤ U) (hL : L ≤ (1 - α / (1 - 2 * α)) ^ 24)
    (hL₀ : 0 ≤ L) (hcerta : (16 + 4096 * β * L) ^ 3 < ‖v‖ ^ 3 * (4096 * β * L))
    (hcertb : (16 + 4096 * α * U) ^ 3 < ‖v‖ ^ 3 * (4096 * α * U)) : False := by
  set A := ‖cexp (2 * π * I * τ)‖
  have hA : 0 ≤ A := norm_nonneg _
  have hU₀ : 0 ≤ U := (by positivity : (0 : ℝ) ≤ (1 + α / (1 - 2 * α)) ^ 24).trans hU
  have hε : 0 ≤ 1 - α / (1 - 2 * α) := by
    rw [sub_nonneg, div_le_one (by linarith)]
    linarith
  have hα₀ : 0 ≤ α := hA.trans hq
  have hQ₀ : 0 ≤ A / (1 - 2 * A) := div_nonneg hA (by linarith)
  have hQ := div_le_div₀ hα₀ hq (by linarith) (by linarith : 1 - 2 * α ≤ 1 - 2 * A)
  have hP : (1 + A / (1 - 2 * A)) ^ 24 ≤ U := le_trans (by gcongr) hU
  have hP' : L ≤ (1 - A / (1 - 2 * A)) ^ 24 := hL.trans (by gcongr)
  have hlo := le_norm_siegelFunction_zero_half_pow_twelve τ.im_pos (by linarith)
  have hhi := norm_siegelFunction_zero_half_pow_twelve_le τ.im_pos (by linarith)
  set t := ‖siegelFunction ![0, 1 / 2] τ ^ 12‖
  have ha : 4096 * β * L ≤ t := le_trans (by gcongr) hlo
  have hb : t ≤ 4096 * α * U := hhi.trans (by gcongr)
  -- The convex function `(16 + t)³ - |v|³ t` is negative at both ends of `[4096 β L, 4096 α U]`.
  have hf : ConvexOn ℝ (Set.Ici 0) fun t : ℝ ↦ (16 + t) ^ 3 - ‖v‖ ^ 3 * t := by
    refine ((((convexOn_pow 3).translate_right 16).subset (fun t ht ↦ ?_) (convex_Ici 0)).sub
      ((LinearMap.mul ℝ ℝ (‖v‖ ^ 3)).concaveOn (convex_Ici 0))).congr fun t _ ↦ ?_
    · rw [Set.mem_Ici] at ht
      rw [Set.mem_preimage, Set.mem_Ici]
      linarith
    · simp only [Pi.sub_apply, Function.comp_apply, LinearMap.mul_apply']
  have hmax := hf.le_max_of_mem_Icc (by positivity : (0 : ℝ) ≤ 4096 * β * L)
    (by positivity : (0 : ℝ) ≤ 4096 * α * U) ⟨ha, hb⟩
  have hlt : (16 + t) ^ 3 < ‖v‖ ^ 3 * t := by
    rw [le_max_iff] at hmax
    rcases hmax with h | h <;> linarith
  -- `|x + 16| ≤ 16 + t`.
  have hup : ‖siegelFunction ![0, 1 / 2] τ ^ 12 + 16‖ ≤ 16 + t := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_ofNat, add_comm]
  have h := norm_siegelFunction_zero_half_pow_twelve_add_sixteen_pow_three hj
  have h₁ : ‖siegelFunction ![0, 1 / 2] τ ^ 12 + 16‖ ^ 3 ≤ (16 + t) ^ 3 := by gcongr
  linarith

/-! ### Certified bounds for `e^{-π √m}` -/

/-- `e^{-x} ≤ (e₋ᵏ ∑_{i < 6} cⁱ / i!)⁻¹` for `k + c ≤ x` and `c ≥ 0`, with `e₋ = 2.7182818283`. -/
private theorem exp_neg_le_of_le {x c : ℝ} (k : ℕ) (hc : 0 ≤ c) (hx : k + c ≤ x) :
    Real.exp (-x) ≤ (2.7182818283 ^ k * ∑ i ∈ Finset.range 6, c ^ i / i.factorial)⁻¹ := by
  have hS : 0 < ∑ i ∈ Finset.range 6, c ^ i / i.factorial := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    positivity
  calc Real.exp (-x) ≤ Real.exp (-(k + c)) := Real.exp_le_exp.2 (by linarith)
    _ = (Real.exp 1 ^ k * Real.exp c)⁻¹ := by
      rw [Real.exp_neg, Real.exp_add, ← Real.exp_nat_mul, mul_one]
    _ ≤ _ := inv_anti₀ (by positivity) (mul_le_mul (pow_le_pow_left₀ (by norm_num)
      Real.exp_one_gt_d9.le k) (Real.sum_le_exp_of_nonneg hc 6) hS.le (by positivity))

/-- `(∑_{i < 6} dⁱ / i!) / e₊ᵏ ≤ e^{-x}` for `x ≤ k - d` and `d ≥ 0`, with `e₊ = 2.7182818286`. -/
private theorem le_exp_neg_of_le {x d : ℝ} (k : ℕ) (hd : 0 ≤ d) (hx : x ≤ k - d) :
    (∑ i ∈ Finset.range 6, d ^ i / i.factorial) / 2.7182818286 ^ k ≤ Real.exp (-x) := by
  calc (∑ i ∈ Finset.range 6, d ^ i / i.factorial) / 2.7182818286 ^ k
      ≤ Real.exp d / Real.exp 1 ^ k := by
        gcongr
        · exact Real.sum_le_exp_of_nonneg hd 6
        · exact Real.exp_one_lt_d9.le
    _ = Real.exp (-(k - d)) := by
      rw [← Real.exp_nat_mul, mul_one, ← Real.exp_sub]
      ring_nf
    _ ≤ Real.exp (-x) := Real.exp_le_exp.2 (by linarith)

/-- An upper bound for `e^{-π √m}` from a lower bound `s ≤ √m`. -/
private theorem exp_neg_pi_mul_sqrt_le {m s c α : ℝ} (k : ℕ) (hs₀ : 0 ≤ s) (hs : s ^ 2 ≤ m)
    (hc : 0 ≤ c) (hk : k + c ≤ 3.141592 * s)
    (hα : (2.7182818283 ^ k * ∑ i ∈ Finset.range 6, c ^ i / i.factorial)⁻¹ ≤ α) :
    Real.exp (-(π * √m)) ≤ α := by
  have h₁ : s ≤ √m := by simpa [Real.sqrt_sq hs₀] using Real.sqrt_le_sqrt hs
  have h₂ : 3.141592 * s ≤ π * √m := mul_le_mul Real.pi_gt_d6.le h₁ hs₀ Real.pi_pos.le
  exact (exp_neg_le_of_le k hc (hk.trans h₂)).trans hα

/-- A lower bound for `e^{-π √m}` from an upper bound `√m ≤ s`. -/
private theorem le_exp_neg_pi_mul_sqrt {m s d β : ℝ} (k : ℕ) (hs₀ : 0 ≤ s) (hs : m ≤ s ^ 2)
    (hd : 0 ≤ d) (hk : 3.141593 * s ≤ k - d)
    (hβ : β ≤ (∑ i ∈ Finset.range 6, d ^ i / i.factorial) / 2.7182818286 ^ k) :
    β ≤ Real.exp (-(π * √m)) := by
  have h₁ : √m ≤ s := by simpa [Real.sqrt_sq hs₀] using Real.sqrt_le_sqrt hs
  have h₂ : π * √m ≤ 3.141593 * s :=
    mul_le_mul Real.pi_lt_d6.le h₁ (Real.sqrt_nonneg _) (by norm_num)
  exact hβ.trans (le_exp_neg_of_le k hd (h₂.trans hk))

/-! ### The imaginary part from the value of `j` -/

/-- `|q| = e^{-π √n}` when `Im τ = √n / 2`. -/
private theorem norm_exp_two_pi_I_eq {τ : ℍ} {n : ℕ} (hτ : τ.im = √n / 2) :
    ‖cexp (2 * π * I * τ)‖ = Real.exp (-(π * √n)) := by
  rw [TauCeti.UpperHalfPlane.norm_exp_two_pi_I_mul, UpperHalfPlane.coe_im, hτ]
  ring_nf

/-- `e^{-π √m} ≤ |q|` when `Im τ = √n / 2` and `n ≤ m`. -/
private theorem le_norm_exp_two_pi_I {τ : ℍ} {n m : ℕ} (hτ : τ.im = √n / 2) (h : n ≤ m) :
    Real.exp (-(π * √m)) ≤ ‖cexp (2 * π * I * τ)‖ := by
  rw [norm_exp_two_pi_I_eq hτ, Real.exp_le_exp, neg_le_neg_iff]
  gcongr

/-- For `Im τ ≥ √3 / 2`, `|q| ≤ 0.00434`. -/
private theorem norm_exp_two_pi_I_le_of_three_le {τ : ℍ} {n : ℕ} (hτ : τ.im = √n / 2)
    (hn : 3 ≤ n) : ‖cexp (2 * π * I * τ)‖ ≤ 0.00434 :=
  ((UpperHalfPlane.norm_exp_two_pi_I_mul_le (t := √3 / 2)
      (by rw [UpperHalfPlane.coe_im, hτ]; gcongr; exact_mod_cast hn)).trans_eq
    (by ring_nf)).trans <| exp_neg_pi_mul_sqrt_le (s := 1.73205) (c := 0.4413) 5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- If `j(τ) = v³` with `Im τ = √n / 2` and the certificate at `√(m + 1)` holds, then `n ≤ m`. -/
private theorem le_of_j_eq_pow_three {τ : ℍ} {n m m' : ℕ} {v : ℂ} (hτ : τ.im = √n / 2)
    (hj : j τ = v ^ 3) (hm : m + 1 = m') {α : ℝ} (hα : Real.exp (-(π * √m')) ≤ α)
    (hα₀ : α ≤ 0.002)
    (hcert : ‖v‖ ^ 3 * (4096 * α * 1.05) < (16 - 4096 * α * 1.05) ^ 3) : n ≤ m := by
  by_contra! h
  have hq := ((UpperHalfPlane.norm_exp_two_pi_I_mul_le (t := √m' / 2)
      (by rw [UpperHalfPlane.coe_im, hτ]; gcongr; exact_mod_cast (by omega : m' ≤ n))).trans_eq
    (by ring_nf)).trans hα
  exact false_of_norm_le hj hq (α' := 0.002) (by norm_num) (hq.trans hα₀) (by norm_num)
    (by linarith) hcert

/-- If `j(τ) = v³` with `Im τ = √n / 2`, `n ≥ 3`, and the certificates at `√(m - 1)` and at `√3`
hold, then `m ≤ n`. -/
private theorem le_of_j_eq_pow_three' {τ : ℍ} {n m m' : ℕ} {v : ℂ} (hτ : τ.im = √n / 2)
    (hn : 3 ≤ n) (hj : j τ = v ^ 3) (hm : m' + 1 = m) {β : ℝ}
    (hβ : β ≤ Real.exp (-(π * √m'))) (hβ₀ : 0 ≤ β)
    (hcerta : (16 + 4096 * β * 0.89) ^ 3 < ‖v‖ ^ 3 * (4096 * β * 0.89))
    (hcertb : (16 + 4096 * 0.00434 * 1.111) ^ 3 < ‖v‖ ^ 3 * (4096 * 0.00434 * 1.111)) :
    m ≤ n := by
  by_contra! h
  exact false_of_le_norm hj (by norm_num) (norm_exp_two_pi_I_le_of_three_le hτ hn)
    (hβ.trans (le_norm_exp_two_pi_I hτ (by omega))) hβ₀ (by norm_num) (by norm_num) (by norm_num)
    hcerta hcertb

/-- **Recovering the discriminant from a singular value of `j`.** Let `τ` be a point of the upper
half-plane with `Im τ = √n / 2` for a natural number `n ≥ 3`, such as the CM point of an imaginary
quadratic field of discriminant `-n`. If `j(τ) = v³` with `v ∈ {0, -32, -96, -960, -5280, -640320}`,
then `(n, v)` is one of `(3, 0), (11, -32), (19, -96), (43, -960), (67, -5280), (163, -640320)`. -/
theorem mk_mem_of_j_eq_intCast_pow_three {τ : ℍ} {n : ℕ} (hn : 3 ≤ n) (hτ : τ.im = √n / 2)
    {v : ℤ} (hv : v ∈ ({0, -32, -96, -960, -5280, -640320} : Finset ℤ))
    (hj : j τ = (v : ℂ) ^ 3) :
    (n, v) ∈ ({(3, 0), (11, -32), (19, -96), (43, -960), (67, -5280), (163, -640320)} :
      Finset (ℕ × ℤ)) := by
  have hnorm : ‖(v : ℂ)‖ = |(v : ℝ)| := Complex.norm_intCast v
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · -- `v = 0`: `n = 3`.
    have h₁ := le_of_j_eq_pow_three (m := 3) (m' := 4) (α := 1.88e-3) hτ hj rfl
      (exp_neg_pi_mul_sqrt_le (s := 2) (c := 0.2831) 6 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by rw [hnorm]; norm_num)
    obtain rfl : n = 3 := by omega
    simp
  · -- `v = -32`: `n = 11`.
    have h₁ := le_of_j_eq_pow_three (m := 11) (m' := 12) (α := 1.89e-5) hτ hj rfl
      (exp_neg_pi_mul_sqrt_le (s := 3.464101) (c := 0.8827) 10 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by rw [hnorm]; norm_num)
    have h₂ := le_of_j_eq_pow_three' (m := 11) (m' := 10) (β := 4.84e-5) hτ hn hj rfl
      (le_exp_neg_pi_mul_sqrt (s := 3.162278) (d := 0.0654) 10 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by rw [hnorm]; norm_num) (by rw [hnorm]; norm_num)
    obtain rfl : n = 11 := by omega
    simp
  · -- `v = -96`: `n = 19`.
    have h₁ := le_of_j_eq_pow_three (m := 19) (m' := 20) (α := 7.92e-7) hτ hj rfl
      (exp_neg_pi_mul_sqrt_le (s := 4.472135) (c := 0.0496) 14 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by rw [hnorm]; norm_num)
    have h₂ := le_of_j_eq_pow_three' (m := 19) (m' := 18) (β := 1.62e-6) hτ hn hj rfl
      (le_exp_neg_pi_mul_sqrt (s := 4.242641) (d := 0.6713) 14 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by rw [hnorm]; norm_num) (by rw [hnorm]; norm_num)
    obtain rfl : n = 19 := by omega
    simp
  · -- `v = -960`: `n = 43`.
    have h₁ := le_of_j_eq_pow_three (m := 43) (m' := 44) (α := 8.92e-10) hτ hj rfl
      (exp_neg_pi_mul_sqrt_le (s := 6.633249) (c := 0.8389) 20 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by rw [hnorm]; norm_num)
    have h₂ := le_of_j_eq_pow_three' (m := 43) (m' := 42) (β := 1.43e-9) hτ hn hj rfl
      (le_exp_neg_pi_mul_sqrt (s := 6.480741) (d := 0.6401) 21 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by rw [hnorm]; norm_num) (by rw [hnorm]; norm_num)
    obtain rfl : n = 43 := by omega
    simp
  · -- `v = -5280`: `n = 67`.
    have h₁ := le_of_j_eq_pow_three (m := 67) (m' := 68) (α := 5.62e-12) hτ hj rfl
      (exp_neg_pi_mul_sqrt_le (s := 8.246211) (c := 0.9062) 25 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by rw [hnorm]; norm_num)
    have h₂ := le_of_j_eq_pow_three' (m := 67) (m' := 66) (β := 8.23e-12) hτ hn hj rfl
      (le_exp_neg_pi_mul_sqrt (s := 8.124039) (d := 0.4775) 26 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by rw [hnorm]; norm_num) (by rw [hnorm]; norm_num)
    obtain rfl : n = 67 := by omega
    simp
  · -- `v = -640320`: `n = 163`.
    have h₁ := le_of_j_eq_pow_three (m := 163) (m' := 164) (α := 3.38e-18) hτ hj rfl
      (exp_neg_pi_mul_sqrt_le (s := 12.806248) (c := 0.232) 40 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by rw [hnorm]; norm_num)
    have h₂ := le_of_j_eq_pow_three' (m := 163) (m' := 162) (β := 4.30e-18) hτ hn hj rfl
      (le_exp_neg_pi_mul_sqrt (s := 12.727923) (d := 0.014) 40 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by rw [hnorm]; norm_num) (by rw [hnorm]; norm_num)
    obtain rfl : n = 163 := by omega
    simp

/-- **The six singular values of `j` determine the discriminant.** If `Im τ = √n / 2` with `n ≥ 3`
and `j(τ) = v³` with `v ∈ {0, -32, -96, -960, -5280, -640320}`, then
`n ∈ {3, 11, 19, 43, 67, 163}`. -/
theorem mem_of_j_eq_intCast_pow_three {τ : ℍ} {n : ℕ} (hn : 3 ≤ n) (hτ : τ.im = √n / 2)
    {v : ℤ} (hv : v ∈ ({0, -32, -96, -960, -5280, -640320} : Finset ℤ))
    (hj : j τ = (v : ℂ) ^ 3) : n ∈ ({3, 11, 19, 43, 67, 163} : Finset ℕ) := by
  have h := mk_mem_of_j_eq_intCast_pow_three hn hτ hv hj
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h ⊢
  omega

end TauCeti.ModularForm
