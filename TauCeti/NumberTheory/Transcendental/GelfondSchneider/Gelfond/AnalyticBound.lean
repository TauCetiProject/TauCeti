/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Schwarz
public import TauCeti.NumberTheory.Transcendental.GelfondSchneider.Gelfond.Auxiliary

/-!
# The analytic upper bound for the value of Gelfond's auxiliary function

Let `λ, β ∈ ℂ`, let `m ≥ 1` and let `q ^ 2 ≤ 2 m n` (in the application `q ^ 2 = 2 m n`).
Gelfond's auxiliary function is

`R(z) = ∑_{a, b = 1}^{q} η_{ab} exp ((a + b β) λ z)`,

whose coefficients are produced by Siegel's lemma with `|η_{ab}| ≤ c ^ n n ^ ((n + 1) / 2)`
(`RingHom.exists_gelfond_auxiliary`). Suppose that `R` vanishes to order `r ≥ n` at each of the
points `1, …, m`. This file proves that the derivative of order `r` at any of these points `t₀`
is small:

`|R⁽ʳ⁾(t₀)| ≤ c₃ ^ r r ^ (((3 - m) r + 1) / 2)`

for a constant `c₃` depending only on `λ`, `β`, `m` and `c`. This is the analytic half of the
final contradiction in Gelfond's proof of the Gelfond–Schneider theorem: when `r` is the order of
the first nonvanishing derivative (`RingHom.exists_iteratedDeriv_gelfond_auxiliary_ne_zero`), the
value is `R⁽ʳ⁾(t₀) = λ ^ r σ ρ` for a nonzero algebraic number `ρ`, and Liouville's lower bound
`|σ ρ| ≥ c₂ ^ (-r) r ^ (-(h - 1) (r + 1))` (`TauCeti.exists_one_le_pow_mul_norm_gelfond_value`)
contradicts the upper bound below once `m = 2 h + 2` and `r` is large.

**Proof.** Apply Schwarz's lemma for the first nonvanishing derivative
(`TauCeti.norm_iteratedDeriv_le_mul_prod_div_pow`) on the disc of radius `T = 3 m √r` centred at
`0`, with the `m` zeros `1, …, m` of order `r`. On the circle,
`|R| ≤ q ^ 2 A exp (q (1 + |β|) |λ| T)`, where `A` bounds the coefficients; since `q √r ≤ 2 m r`
this is `O(1) ^ r r ^ ((r + 1) / 2)`.
The zero `t₀` contributes `r! / (T - t₀) ^ r ≤ r ^ r / √r ^ r`, and each of the other `m - 1`
zeros a factor `(|t₀ - t| / (T - t)) ^ r ≤ √r ^ (-r)`. Altogether
`|R⁽ʳ⁾(t₀)| ≤ O(1) ^ r r ^ (r + (r + 1) / 2 - m r / 2)`.

## Main results

* `TauCeti.exists_norm_iteratedDeriv_gelfond_auxiliary_le`: the bound above for `R⁽ʳ⁾(t₀)`, with
  complex coefficients `η_{ab}`.
* `RingHom.exists_norm_gelfond_value_le`: the algebraic form. For a ring homomorphism `σ` to `ℂ`
  with `σ α = exp λ`, `σ γ = exp (σ β λ)` and `λ ≠ 0`, if the values
  `y_k(t) = ∑_{a, b} η_{ab} (a + b β) ^ k α ^ (a t) γ ^ (b t)` vanish for `k < r` and `1 ≤ t ≤ m`,
  then `|σ y_r(t₀)| ≤ c₃ ^ r r ^ (((3 - m) r + 1) / 2)`.

## References

* M. Karatarakis and F. Wiedijk, *A formalization of the Gelfond–Schneider theorem*,
  arXiv:2603.24823 (2026), §3.
* K. Soundararajan (notes by I. Petrow), *Transcendental number theory*, Stanford Math 249A
  course notes (2011).
-/

public section

open Finset Metric

namespace TauCeti

/-- The bound for Gelfond's auxiliary function on a disc: if `‖η_{ab}‖ ≤ A` and `‖w‖ ≤ T`, then
`‖R w‖ ≤ q ^ 2 A exp (q (1 + ‖β‖) ‖λ‖ T)`. -/
private theorem norm_gelfond_auxiliary_le (l β : ℂ) {q : ℕ} {η : Fin q → Fin q → ℂ} {A T : ℝ}
    (hη : ∀ a b, ‖η a b‖ ≤ A) {w : ℂ} (hw : ‖w‖ ≤ T) :
    ‖∑ a, ∑ b, η a b * Complex.exp ((((a + 1 : ℕ) : ℂ) + (b + 1 : ℕ) * β) * l * w)‖ ≤
      (q * q : ℕ) * (A * Real.exp (q * (1 + ‖β‖) * ‖l‖ * T)) := by
  have hterm (a b : Fin q) :
      ‖η a b * Complex.exp ((((a + 1 : ℕ) : ℂ) + (b + 1 : ℕ) * β) * l * w)‖ ≤
        A * Real.exp (q * (1 + ‖β‖) * ‖l‖ * T) := by
    rw [norm_mul, Complex.norm_exp]
    have hA : 0 ≤ A := (norm_nonneg _).trans (hη a b)
    refine mul_le_mul (hη a b) (Real.exp_le_exp.2 ((Complex.re_le_norm _).trans ?_))
      (Real.exp_pos _).le hA
    have ha : ((a + 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast a.is_lt
    have hb : ((b + 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast b.is_lt
    have hθ : ‖((a + 1 : ℕ) : ℂ) + (b + 1 : ℕ) * β‖ ≤ q * (1 + ‖β‖) :=
      calc ‖((a + 1 : ℕ) : ℂ) + (b + 1 : ℕ) * β‖
          ≤ ((a + 1 : ℕ) : ℝ) + (b + 1 : ℕ) * ‖β‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, Complex.norm_natCast, Complex.norm_natCast]
        _ ≤ q + q * ‖β‖ := by gcongr
        _ = q * (1 + ‖β‖) := by ring
    rw [norm_mul, norm_mul]
    gcongr
  calc ‖∑ a, ∑ b, η a b * Complex.exp ((((a + 1 : ℕ) : ℂ) + (b + 1 : ℕ) * β) * l * w)‖
      ≤ ∑ a : Fin q, ∑ b : Fin q, A * Real.exp (q * (1 + ‖β‖) * ‖l‖ * T) :=
        (norm_sum_le _ _).trans (sum_le_sum fun a _ ↦ (norm_sum_le _ _).trans
          (sum_le_sum fun b _ ↦ hterm a b))
    _ = (q * q : ℕ) * (A * Real.exp (q * (1 + ‖β‖) * ‖l‖ * T)) := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- On the disc of radius `3 m √r`, Gelfond's auxiliary function with
`‖η_{ab}‖ ≤ c ^ n n ^ ((n + 1) / 2)`, `q ^ 2 ≤ 2 m n` and `1 ≤ n ≤ r` is bounded by
`2 m r c' ^ r √r ^ (r + 1) E ^ r`, where `c' = max 1 |c|` and
`E = exp ((1 + ‖β‖) ‖λ‖ 6 m ^ 2)`. -/
private theorem norm_gelfond_auxiliary_le_sqrt (l β : ℂ) (c : ℝ) {m n q r : ℕ}
    {η : Fin q → Fin q → ℂ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hq : q ^ 2 ≤ 2 * m * n) (hnr : n ≤ r)
    (hη : ∀ a b, ‖η a b‖ ≤ c ^ n * (n : ℝ) ^ (((n : ℝ) + 1) / 2)) {w : ℂ}
    (hw : ‖w‖ ≤ 3 * m * √(r : ℝ)) :
    ‖∑ a, ∑ b, η a b * Complex.exp ((((a + 1 : ℕ) : ℂ) + (b + 1 : ℕ) * β) * l * w)‖ ≤
      2 * m * r * (max 1 |c| ^ r * √(r : ℝ) ^ (r + 1) *
        Real.exp ((1 + ‖β‖) * ‖l‖ * (6 * m ^ 2)) ^ r) := by
  set S := √(r : ℝ)
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hn.trans hnr
  have hr₀ : (0 : ℝ) ≤ r := by linarith
  have hS : 1 ≤ S := Real.one_le_sqrt.mpr hr'
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hc' : 1 ≤ max 1 |c| := le_max_left _ _
  -- `q ^ 2 ≤ 2 m r` and `q √r ≤ 2 m r`.
  have hq' : ((q * q : ℕ) : ℝ) ≤ 2 * m * r := by
    rw [← sq]
    calc ((q ^ 2 : ℕ) : ℝ) ≤ ((2 * m * n : ℕ) : ℝ) := by exact_mod_cast hq
      _ ≤ 2 * m * r := by push_cast; gcongr
  have hqS : (q : ℝ) * S ≤ 2 * m * r := by
    have hq'' : (q : ℝ) ^ 2 ≤ 2 * m * r := by rw [sq]; exact_mod_cast hq'
    refine (mul_self_le_mul_self_iff (by positivity) (by positivity)).mpr ?_
    have e : (q : ℝ) * S * ((q : ℝ) * S) = (q : ℝ) ^ 2 * r := by
      rw [← Real.mul_self_sqrt hr₀]
      ring
    rw [e]
    nlinarith
  -- The coefficients: `c ^ n n ^ ((n + 1) / 2) ≤ c' ^ r √r ^ (r + 1)`.
  have hA : c ^ n * (n : ℝ) ^ (((n : ℝ) + 1) / 2) ≤ max 1 |c| ^ r * S ^ (r + 1) := by
    have hnr' : (n : ℝ) ≤ r := by exact_mod_cast hnr
    have hSr : S ^ (r + 1) = (r : ℝ) ^ (((r : ℝ) + 1) / 2) := by
      rw [Real.rpow_div_two_eq_sqrt _ hr₀]
      norm_cast
    rw [hSr]
    refine mul_le_mul ?_ ((Real.rpow_le_rpow (by positivity) hnr' (by positivity)).trans
      (Real.rpow_le_rpow_of_exponent_le hr' (by linarith))) (by positivity) (by positivity)
    calc c ^ n ≤ |c| ^ n := (le_abs_self _).trans (abs_pow c n).le
      _ ≤ max 1 |c| ^ n := pow_le_pow_left₀ (abs_nonneg c) (le_max_right _ _) n
      _ ≤ max 1 |c| ^ r := pow_le_pow_right₀ hc' hnr
  -- The exponential: `q (1 + ‖β‖) ‖λ‖ 3 m √r ≤ r (1 + ‖β‖) ‖λ‖ 6 m ^ 2`.
  have hexp : Real.exp (q * (1 + ‖β‖) * ‖l‖ * (3 * m * S)) ≤
      Real.exp ((1 + ‖β‖) * ‖l‖ * (6 * m ^ 2)) ^ r := by
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.2 ?_
    have hβl : 0 ≤ (1 + ‖β‖) * ‖l‖ := by positivity
    calc (q : ℝ) * (1 + ‖β‖) * ‖l‖ * (3 * m * S) = (1 + ‖β‖) * ‖l‖ * (3 * m * (q * S)) := by
          ring
      _ ≤ (1 + ‖β‖) * ‖l‖ * (3 * m * (2 * m * r)) := by gcongr
      _ = r * ((1 + ‖β‖) * ‖l‖ * (6 * m ^ 2)) := by ring
  refine (norm_gelfond_auxiliary_le l β (fun a b ↦ (hη a b).trans hA) hw).trans ?_
  gcongr

/-- The natural numbers `1, …, m`, viewed in `ℂ`, have norm at most `m`. -/
private theorem norm_le_of_mem_image_Icc {m : ℕ} {x : ℂ}
    (hx : x ∈ (Icc 1 m).image fun t : ℕ ↦ (t : ℂ)) : ‖x‖ ≤ m := by
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hx
  rw [Complex.norm_natCast]
  exact_mod_cast (mem_Icc.mp ht).2

/-- The zeros `1, …, m` other than `t₀` contribute a product of factors
`(|t₀ - x| / (3 m S - |x|)) ^ r`, each at most `S⁻¹ ^ r` when `1 ≤ S`. -/
private theorem prod_erase_norm_sub_div_pow_le {m r t₀ : ℕ} {S : ℝ} (hS : 1 ≤ S)
    (ht₀ : t₀ ∈ Icc 1 m) :
    ∏ x ∈ ((Icc 1 m).image fun t : ℕ ↦ (t : ℂ)).erase (t₀ : ℂ),
        (‖(t₀ : ℂ) - x‖ / (3 * m * S - ‖x‖)) ^ r ≤ S⁻¹ ^ (r * (m - 1)) := by
  have hS₀ : 0 < S := by linarith
  set s : Finset ℂ := (Icc 1 m).image fun t : ℕ ↦ (t : ℂ)
  set T := 3 * m * S
  have hm' : (1 : ℝ) ≤ m := by
    exact_mod_cast (mem_Icc.mp ht₀).1.trans (mem_Icc.mp ht₀).2
  have hsm (x : ℂ) (hx : x ∈ s) : ‖x‖ ≤ m := norm_le_of_mem_image_Icc hx
  have hTx (x : ℂ) (hx : x ∈ s) : 2 * m * S ≤ T - ‖x‖ := by
    have := hsm x hx
    nlinarith
  have ht₀s : (t₀ : ℂ) ∈ s := mem_image.mpr ⟨t₀, ht₀, rfl⟩
  -- Each zero other than `t₀` contributes at most `S⁻¹ ^ r`.
  have hnonneg (x : ℂ) (hx : x ∈ s.erase (t₀ : ℂ)) :
      0 ≤ (‖(t₀ : ℂ) - x‖ / (T - ‖x‖)) ^ r := by
    have := hTx x (mem_of_mem_erase hx)
    exact pow_nonneg (div_nonneg (norm_nonneg _) (by nlinarith)) r
  have hfactor (x : ℂ) (hx : x ∈ s.erase (t₀ : ℂ)) :
      (‖(t₀ : ℂ) - x‖ / (T - ‖x‖)) ^ r ≤ S⁻¹ ^ r := by
    have hTx := hTx x (mem_of_mem_erase hx)
    have hx' := hsm x (mem_of_mem_erase hx)
    have ht₀' := hsm _ ht₀s
    refine pow_le_pow_left₀ (div_nonneg (norm_nonneg _) (by nlinarith)) ?_ r
    rw [div_le_iff₀ (by nlinarith), inv_mul_eq_div, le_div_iff₀ hS₀]
    calc ‖(t₀ : ℂ) - x‖ * S ≤ 2 * m * S := by
          gcongr
          linarith [norm_sub_le (t₀ : ℂ) x]
      _ ≤ T - ‖x‖ := hTx
  have hcard : (s.erase (t₀ : ℂ)).card = m - 1 := by
    rw [card_erase_of_mem ht₀s, card_image_of_injective _ Nat.cast_injective, Nat.card_Icc,
      Nat.add_sub_cancel]
  refine (prod_le_prod₀ hnonneg hfactor).trans_eq ?_
  rw [prod_const, hcard, ← pow_mul]

/-- Schwarz's lemma at the zeros `1, …, m`: if `f` is entire, bounded by `M` on the circle of
radius `3 m √r`, and vanishes to order `r ≥ 1` at each of the points `1, …, m`, then
`‖f⁽ʳ⁾(t₀)‖ √r ^ (m r) ≤ r! M` for every `1 ≤ t₀ ≤ m`. The zero `t₀` contributes the factor
`r! / (3 m √r - t₀) ^ r ≤ r! / √r ^ r`, and each of the other `m - 1` zeros `t` a factor
`(|t₀ - t| / (3 m √r - t)) ^ r ≤ √r ^ (-r)`. -/
private theorem norm_iteratedDeriv_mul_sqrt_pow_le {f : ℂ → ℂ} (hf : ∀ z, AnalyticAt ℂ f z)
    {m r t₀ : ℕ} {M : ℝ} (hr : 1 ≤ r)
    (hzero : ∀ k < r, ∀ t ∈ Icc 1 m, iteratedDeriv k f t = 0) (ht₀ : t₀ ∈ Icc 1 m)
    (hM : ∀ w ∈ sphere (0 : ℂ) (3 * m * √(r : ℝ)), ‖f w‖ ≤ M) :
    ‖iteratedDeriv r f t₀‖ * √(r : ℝ) ^ (m * r) ≤ r.factorial * M := by
  set S := √(r : ℝ)
  have hS : 1 ≤ S := Real.one_le_sqrt.mpr (by exact_mod_cast hr)
  have hS₀ : 0 < S := by linarith
  set T := 3 * m * S
  have hm : 1 ≤ m := (mem_Icc.mp ht₀).1.trans (mem_Icc.mp ht₀).2
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  -- The `m` zeros `1, …, m` of order `r` lie in the disc, at distance at least `2 m S` from
  -- the circle.
  set s : Finset ℂ := (Icc 1 m).image fun t : ℕ ↦ (t : ℂ)
  have hk : ∀ x ∈ s, (((fun _ ↦ r) x : ℕ) : ℕ∞) ≤ analyticOrderAt f x := by
    simp only [s, mem_image]
    rintro _ ⟨t, ht, rfl⟩
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf _)).mpr
      fun k hk ↦ hzero k hk t ht
  have hs : (s : Set ℂ) ⊆ ball 0 T := fun x hx ↦ by
    rw [mem_ball, dist_zero_right]
    exact (norm_le_of_mem_image_Icc hx).trans_lt (by nlinarith)
  have ht₀s : (t₀ : ℂ) ∈ s := mem_image.mpr ⟨t₀, ht₀, rfl⟩
  have hmain := norm_iteratedDeriv_le_mul_prod_div_pow (fun z _ ↦ hf z) hk hs hM ht₀s
  simp only [sub_zero] at hmain
  -- Each zero other than `t₀` contributes at most `S⁻¹ ^ r`.
  have hprod := prod_erase_norm_sub_div_pow_le (m := m) (r := r) (t₀ := t₀) hS ht₀
  have hTt₀ : S ≤ T - ‖(t₀ : ℂ)‖ := by
    have := norm_le_of_mem_image_Icc ht₀s
    nlinarith
  have hM₀ : 0 ≤ M := (norm_nonneg _).trans (hM T (by
    rw [mem_sphere_zero_iff_norm, Complex.norm_real, Real.norm_of_nonneg (by positivity)]))
  have h₁ : ‖iteratedDeriv r f t₀‖ ≤ r.factorial * M / S ^ r * S⁻¹ ^ (r * (m - 1)) := by
    refine hmain.trans ((mul_le_mul_of_nonneg_left hprod
      (div_nonneg (by positivity) (pow_nonneg (by linarith) _))).trans ?_)
    gcongr
  obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le' hm
  simp only [Nat.add_sub_cancel] at h₁
  calc ‖iteratedDeriv r f t₀‖ * S ^ ((m' + 1) * r)
      ≤ r.factorial * M / S ^ r * S⁻¹ ^ (r * m') * (S ^ r * S ^ (r * m')) := by
        rw [← pow_add, show r + r * m' = (m' + 1) * r by ring]
        gcongr
    _ = r.factorial * M := by
        rw [inv_pow]
        field_simp

/-- The arithmetic of Gelfond's upper bound: if `D √r ^ (m r) ≤ r! 2 m r c' ^ r √r ^ (r + 1) E ^ r`
with `m, r ≥ 1` and `c', E ≥ 1`, then `D ≤ (4 (m + 1) c' E) ^ r r ^ (((3 - m) r + 1) / 2)`, using
`r! ≤ r ^ r = √r ^ (2 r)` and `2 m r ≤ (4 (m + 1)) ^ r`. -/
private theorem le_pow_mul_rpow_of_mul_sqrt_pow_le {D c' E : ℝ} {m r : ℕ} (hm : 1 ≤ m)
    (hr : 1 ≤ r) (hD : D * √(r : ℝ) ^ (m * r) ≤
      r.factorial * (2 * m * r * (c' ^ r * √(r : ℝ) ^ (r + 1) * E ^ r)))
    (hc' : 1 ≤ c') (hE : 1 ≤ E) :
    D ≤ (4 * (m + 1) * c' * E) ^ r * (r : ℝ) ^ (((3 - m : ℝ) * r + 1) / 2) := by
  set S := √(r : ℝ)
  have hr₀ : (0 : ℝ) < r := by exact_mod_cast hr
  have hS₀ : 0 < S := Real.sqrt_pos.mpr hr₀
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hfact : (r.factorial : ℝ) ≤ S ^ (2 * r) := by
    rw [pow_mul, sq, Real.mul_self_sqrt hr₀.le]
    exact_mod_cast r.factorial_le_pow
  have h2mr : 2 * (m : ℝ) * r ≤ (4 * (m + 1)) ^ r := by
    have h₁ : (r : ℝ) ≤ 2 ^ r := by exact_mod_cast r.lt_two_pow_self.le
    have h₂ : 2 * (m : ℝ) ≤ (2 * (m + 1)) ^ r :=
      (by linarith : 2 * (m : ℝ) ≤ 2 * (m + 1)).trans (le_self_pow₀ (by linarith) (by omega))
    calc 2 * (m : ℝ) * r ≤ (2 * (m + 1)) ^ r * 2 ^ r :=
          mul_le_mul h₂ h₁ (by positivity) (by positivity)
      _ = (4 * (m + 1)) ^ r := by rw [← mul_pow]; ring
  have hfinal : D * S ^ (m * r) ≤ (4 * (m + 1) * c' * E) ^ r * S ^ (3 * r + 1) := by
    refine hD.trans ?_
    calc (r.factorial : ℝ) * (2 * m * r * (c' ^ r * S ^ (r + 1) * E ^ r))
        ≤ S ^ (2 * r) * ((4 * (m + 1)) ^ r * (c' ^ r * S ^ (r + 1) * E ^ r)) := by
          gcongr
      _ = (4 * (m + 1) * c' * E) ^ r * S ^ (3 * r + 1) := by
          simp only [mul_pow]
          ring
  -- `S ^ (3 r + 1) / S ^ (m r) = r ^ (((3 - m) r + 1) / 2)`.
  have hpow (N : ℕ) : S ^ N = (r : ℝ) ^ ((N : ℝ) / 2) := by
    rw [Real.rpow_div_two_eq_sqrt _ hr₀.le, Real.rpow_natCast]
  have hrpow : (r : ℝ) ^ (((3 - m : ℝ) * r + 1) / 2) = S ^ (3 * r + 1) / S ^ (m * r) := by
    rw [hpow, hpow, ← Real.rpow_sub hr₀]
    congr 1
    push_cast
    ring
  rw [hrpow, mul_div_assoc', le_div_iff₀ (by positivity)]
  exact hfinal

/-- **The analytic upper bound for Gelfond's auxiliary function** (Karatarakis–Wiedijk, §3).
Let `λ, β ∈ ℂ`, `m ∈ ℕ` and `c ∈ ℝ`. There is `c₃ ≥ 1` with the following property. Let `n ≥ 1`,
`q ^ 2 ≤ 2 m n` and `r ≥ n`, let `η_{ab} ∈ ℂ`, `a, b < q`, satisfy
`‖η_{ab}‖ ≤ c ^ n n ^ ((n + 1) / 2)`, and suppose that
`R(z) = ∑_{a, b} η_{ab} exp (((a + 1) + (b + 1) β) λ z)` vanishes to order `r` at each of the
points `1, …, m`. Then `‖R⁽ʳ⁾(t₀)‖ ≤ c₃ ^ r r ^ (((3 - m) r + 1) / 2)` for every `1 ≤ t₀ ≤ m`. -/
theorem exists_norm_iteratedDeriv_gelfond_auxiliary_le (l β : ℂ) (m : ℕ) (c : ℝ) :
    ∃ c₃ : ℝ, 1 ≤ c₃ ∧ ∀ (n q r t₀ : ℕ) (η : Fin q → Fin q → ℂ), 1 ≤ n → q ^ 2 ≤ 2 * m * n →
      n ≤ r → t₀ ∈ Icc 1 m → (∀ a b, ‖η a b‖ ≤ c ^ n * (n : ℝ) ^ (((n : ℝ) + 1) / 2)) →
      (∀ k < r, ∀ t ∈ Icc 1 m, iteratedDeriv k (fun z ↦ ∑ a, ∑ b, η a b *
        Complex.exp ((((a + 1 : ℕ) : ℂ) + (b + 1 : ℕ) * β) * l * z)) t = 0) →
      ‖iteratedDeriv r (fun z ↦ ∑ a, ∑ b, η a b *
        Complex.exp ((((a + 1 : ℕ) : ℂ) + (b + 1 : ℕ) * β) * l * z)) t₀‖ ≤
        c₃ ^ r * (r : ℝ) ^ (((3 - m : ℝ) * r + 1) / 2) := by
  have hc' : 1 ≤ max 1 |c| := le_max_left _ _
  have hE : 1 ≤ Real.exp ((1 + ‖β‖) * ‖l‖ * (6 * m ^ 2)) := Real.one_le_exp (by positivity)
  refine ⟨4 * (m + 1) * max 1 |c| * Real.exp ((1 + ‖β‖) * ‖l‖ * (6 * m ^ 2)), ?_,
    fun n q r t₀ η hn hq hnr ht₀ hη hzero ↦ ?_⟩
  · have h4 : (1 : ℝ) ≤ 4 * (m + 1) := by linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h4 hc') hE
  have hm : 1 ≤ m := (mem_Icc.mp ht₀).1.trans (mem_Icc.mp ht₀).2
  refine le_pow_mul_rpow_of_mul_sqrt_pow_le hm (hn.trans hnr) ?_ hc' hE
  refine norm_iteratedDeriv_mul_sqrt_pow_le (fun z ↦ by fun_prop) (hn.trans hnr) hzero ht₀
    fun w hw ↦ norm_gelfond_auxiliary_le_sqrt l β c hm hn hq hnr hη ?_
  exact (mem_sphere_zero_iff_norm.mp hw).le

end TauCeti

namespace RingHom

/-- **The analytic upper bound for Gelfond's values** (Karatarakis–Wiedijk, §3). Let `R` be a
ring with a ring homomorphism `σ : R →+* ℂ`, let `λ ≠ 0`, and let `α, β, γ ∈ R` with
`σ α = exp λ` and `σ γ = exp (σ β λ)`. For `m ∈ ℕ` and `c ∈ ℝ` there is `c₃ ≥ 1` with the
following property. Let `n ≥ 1`, `q ^ 2 ≤ 2 m n`, `r ≥ n` and `1 ≤ t₀ ≤ m`, and let
`η_{ab} ∈ R`, `a, b < q`, satisfy `‖σ η_{ab}‖ ≤ c ^ n n ^ ((n + 1) / 2)`. If
`y_k(t) = ∑_{a, b} η_{ab} ((a + 1) + (b + 1) β) ^ k α ^ ((a + 1) t) γ ^ ((b + 1) t)` vanishes for
all `k < r` and `1 ≤ t ≤ m`, then `‖σ y_r(t₀)‖ ≤ c₃ ^ r r ^ (((3 - m) r + 1) / 2)`. -/
theorem exists_norm_gelfond_value_le {R : Type*} [Ring R] (σ : R →+* ℂ) {l : ℂ} (hl : l ≠ 0)
    {α β γ : R} (hα : σ α = Complex.exp l) (hγ : σ γ = Complex.exp (σ β * l)) (m : ℕ) (c : ℝ) :
    ∃ c₃ : ℝ, 1 ≤ c₃ ∧ ∀ (n q r t₀ : ℕ) (η : Fin q → Fin q → R), 1 ≤ n → q ^ 2 ≤ 2 * m * n →
      n ≤ r → t₀ ∈ Icc 1 m →
      (∀ a b, ‖σ (η a b)‖ ≤ c ^ n * (n : ℝ) ^ (((n : ℝ) + 1) / 2)) →
      (∀ k < r, ∀ t ∈ Icc 1 m, ∑ a, ∑ b, η a b *
        (((a + 1 : ℕ) : R) + (b + 1 : ℕ) * β) ^ k *
          (α ^ ((a + 1 : ℕ) * t) * γ ^ ((b + 1 : ℕ) * t)) = 0) →
      ‖σ (∑ a, ∑ b, η a b * (((a + 1 : ℕ) : R) + (b + 1 : ℕ) * β) ^ r *
        (α ^ ((a + 1 : ℕ) * t₀) * γ ^ ((b + 1 : ℕ) * t₀)))‖ ≤
        c₃ ^ r * (r : ℝ) ^ (((3 - m : ℝ) * r + 1) / 2) := by
  obtain ⟨c₃, hc₃, h⟩ := TauCeti.exists_norm_iteratedDeriv_gelfond_auxiliary_le l (σ β) m c
  set L := max 1 ‖l‖⁻¹
  refine ⟨L * c₃, one_le_mul_of_one_le_of_one_le (le_max_left _ _) hc₃,
    fun n q r t₀ η hn hq hnr ht₀ hη hzero ↦ ?_⟩
  have hR := h n q r t₀ (fun a b ↦ σ (η a b)) hn hq hnr ht₀ hη fun k hk t ht ↦ by
    rw [σ.iteratedDeriv_gelfond_auxiliary_natCast hα hγ, hzero k hk t ht, map_zero, mul_zero]
  rw [σ.iteratedDeriv_gelfond_auxiliary_natCast hα hγ, norm_mul, norm_pow] at hR
  -- Dividing by `‖λ‖ ^ r` costs the factor `‖λ‖⁻¹ ^ r ≤ L ^ r`.
  have hl' : 0 < ‖l‖ := norm_pos_iff.mpr hl
  calc ‖σ _‖ = ‖l‖⁻¹ ^ r * (‖l‖ ^ r * ‖σ _‖) := by
        rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hl'.ne', one_pow, one_mul]
    _ ≤ L ^ r * (c₃ ^ r * (r : ℝ) ^ (((3 - m : ℝ) * r + 1) / 2)) := by
        gcongr
        exact le_max_right _ _
    _ = (L * c₃) ^ r * (r : ℝ) ^ (((3 - m : ℝ) * r + 1) / 2) := by
        rw [mul_pow, mul_assoc]

end RingHom
