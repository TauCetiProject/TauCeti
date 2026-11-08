/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.RingTheory.Algebraic.Basic

import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import TauCeti.NumberTheory.Transcendental.GelfondSchneider.Gelfond.AnalyticBound
import TauCeti.NumberTheory.Transcendental.GelfondSchneider.Gelfond.Value

/-!
# The Gelfond–Schneider theorem for complex numbers

This file proves the Gelfond–Schneider theorem in its complex form: if `λ ≠ 0` is a complex number
with `exp λ` algebraic and `β` is an algebraic number that is not rational, then `exp (β λ)` is
transcendental (`TauCeti.transcendental_exp_mul`). In particular, for algebraic `α ≠ 0, 1` and
algebraic irrational `β`, every value `exp (β log α)` of `α ^ β` is transcendental; for the
principal branch `α ^ β` this is `TauCeti.transcendental_cpow`.

The proof is Gelfond's. Suppose that `γ = exp (β λ)` is algebraic and let `K = ℚ(exp λ, β, γ)`,
a number field of degree `h` embedded in `ℂ` by `σ`, and put `m = 2 h + 2`. For `q ^ 2 = 2 m n`,
Siegel's lemma gives algebraic integers `η_{ab}`, not all zero, of house at most
`c ^ n n ^ ((n + 1) / 2)`, such that the values
`y_k(t) = ∑_{a, b} η_{ab} ((a + 1) + (b + 1) β) ^ k (exp λ) ^ ((a + 1) t) γ ^ ((b + 1) t)` vanish
for `k < n` and `1 ≤ t ≤ m` (`TauCeti.exists_gelfond_auxiliary_algebraic`). Let `r` be the first
order with `ρ = y_r(t₀) ≠ 0` for some `1 ≤ t₀ ≤ m` (`TauCeti.exists_gelfond_value_ne_zero`), so
that `r ≥ n`. Then

* `1 ≤ c₂ ^ r r ^ ((h - 1) r) |σ ρ|` by Liouville's inequality
  (`TauCeti.exists_one_le_pow_mul_norm_gelfond_value`);
* `|σ ρ| ≤ c₃ ^ r r ^ (((3 - m) r + 1) / 2)` by Schwarz's lemma
  (`RingHom.exists_norm_gelfond_value_le`).

Since `m = 2 h + 2`, together they give `1 ≤ (c₂ c₃) ^ r r ^ ((1 - r) / 2)`, which fails once `n`,
and hence `r`, is large.

## Main results

* `TauCeti.transcendental_exp_mul`: the Gelfond–Schneider theorem for an arbitrary nonzero
  logarithm `λ` of an algebraic number.
* `TauCeti.transcendental_cpow`: the Gelfond–Schneider theorem for `Complex.cpow`.

## References

* M. Karatarakis and F. Wiedijk, *A formalization of the Gelfond–Schneider theorem*,
  arXiv:2603.24823 (2026), §3.
* K. Soundararajan (notes by I. Petrow), *Transcendental number theory*, Stanford Math 249A
  course notes (2011).
-/

public section

open Finset Module NumberField

namespace TauCeti

/-- For `C ≥ 0` and every large natural number `r`, `C ^ r r ^ ((1 - r) / 2) < 1`: writing
`s = √r`, the left side is `s (C / s) ^ r ≤ s 2 ^ (-r)` as soon as `s ≥ 2 C`. -/
private theorem exists_pow_mul_rpow_lt_one {C : ℝ} (hC : 0 ≤ C) :
    ∃ N : ℕ, ∀ r : ℕ, N ≤ r → C ^ r * (r : ℝ) ^ ((1 - (r : ℝ)) / 2) < 1 := by
  refine ⟨⌈4 * C ^ 2⌉₊ + 1, fun r hr ↦ ?_⟩
  have hr₁ : (1 : ℝ) ≤ r := by exact_mod_cast (Nat.le_add_left 1 _).trans hr
  have hr₀ : (0 : ℝ) < r := zero_lt_one.trans_le hr₁
  have hCr : 4 * C ^ 2 ≤ r :=
    (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_succ _).trans hr)
  set s := Real.sqrt r
  have hs₀ : 0 < s := Real.sqrt_pos.2 hr₀
  have hsr : s ≤ r := Real.sqrt_le_self_iff.2 (Or.inr hr₁)
  -- `2 C ≤ s`, since `(2 C) ^ 2 ≤ r`.
  have hCs : 2 * C ≤ s := Real.le_sqrt_of_sq_le (by nlinarith)
  -- `r ^ ((1 - r) / 2) = s / s ^ r`.
  have hrs : (r : ℝ) ^ ((1 - (r : ℝ)) / 2) = s / s ^ r := by
    rw [show (1 - (r : ℝ)) / 2 = 1 / 2 * (1 - r) by ring, Real.rpow_mul hr₀.le,
      ← Real.sqrt_eq_rpow, Real.rpow_sub hs₀, Real.rpow_one, Real.rpow_natCast]
  have hCs' : C / s ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hs₀ two_pos]
    linarith
  calc C ^ r * (r : ℝ) ^ ((1 - (r : ℝ)) / 2) = s * (C / s) ^ r := by
        rw [hrs, div_pow]
        field_simp
    _ ≤ s * (1 / 2) ^ r := by gcongr
    _ = s / 2 ^ r := by rw [one_div, inv_pow, div_eq_mul_inv]
    _ < 1 := by
        rw [div_lt_one (by positivity)]
        exact hsr.trans_lt (by exact_mod_cast Nat.lt_two_pow_self)

/-- **Gelfond's contradiction.** No number field `K` with an embedding `σ : K →+* ℂ` contains
elements `α, β, γ` with `β` irrational, `σ α = exp λ` and `σ γ = exp (σ β λ)` for some `λ ≠ 0`. -/
private theorem gelfond_false {K : Type*} [Field K] [NumberField K] (σ : K →+* ℂ) {l : ℂ}
    (hl : l ≠ 0) {α β γ : K} (hα : σ α = Complex.exp l) (hγ : σ γ = Complex.exp (σ β * l))
    (hβ : ∀ r : ℚ, (r : K) ≠ β) : False := by
  set h := finrank ℚ K
  have hh : 1 ≤ h := finrank_pos
  set m := 2 * h + 2
  have hm : 1 ≤ m := by omega
  have hα₀ : α ≠ 0 := fun h ↦ Complex.exp_ne_zero l (by rw [← hα, h, map_zero])
  have hγ₀ : γ ≠ 0 := fun h ↦ Complex.exp_ne_zero (σ β * l) (by rw [← hγ, h, map_zero])
  obtain ⟨c, -, haux⟩ := exists_gelfond_auxiliary_algebraic α β γ hm
  obtain ⟨c₂, hc₂, hlow⟩ := exists_one_le_pow_mul_norm_gelfond_value α β γ m c
  obtain ⟨c₃, hc₃, hup⟩ := σ.exists_norm_gelfond_value_le hl hα hγ m c
  obtain ⟨N, hN⟩ := exists_pow_mul_rpow_lt_one
    (mul_nonneg (zero_le_one.trans hc₂) (zero_le_one.trans hc₃))
  -- Take `n = 2 m (N + 1) ^ 2 ≥ N` and `q = 2 m (N + 1)`, so that `q ^ 2 = 2 m n`.
  set n := 2 * m * (N + 1) ^ 2
  have hNn : N ≤ n := by
    calc N ≤ (N + 1) ^ 2 := (Nat.le_succ N).trans (Nat.le_self_pow two_ne_zero _)
      _ ≤ n := Nat.le_mul_of_pos_left _ (by omega)
  have hn : 1 ≤ n := Nat.mul_pos (by omega) (by positivity)
  have hq : (2 * m * (N + 1)) ^ 2 = 2 * m * n := by ring
  obtain ⟨η, hη, hηle, hzero⟩ := haux n _ hn hq
  have hη' : (fun a b ↦ (η a b : K)) ≠ 0 := fun h ↦
    hη (funext₂ fun a b ↦ RingOfIntegers.coe_eq_zero_iff.1 (congr_fun₂ h a b))
  -- The first order `r` at which some value `ρ = y_r(t₀)` is nonzero; `r ≥ n` since the values of
  -- lower order vanish.
  obtain ⟨r, -, t₀, ht₀, hzero', hρ⟩ :=
    exists_gelfond_value_ne_zero hα₀ hγ₀ hβ hη' (T := Icc 1 m) ⟨1, mem_Icc.2 ⟨le_rfl, hm⟩⟩
  have hnr : n ≤ r := by
    by_contra! hrn
    exact hρ (hzero r hrn t₀ ht₀)
  have hr₀ : (0 : ℝ) < r := by exact_mod_cast hn.trans hnr
  have hL := hlow σ n _ r t₀ η hq hnr (mem_Icc.1 ht₀).2 hηle hρ
  have hU := hup n _ r t₀ (fun a b ↦ (η a b : K)) hn hq.le hnr ht₀
    (fun a b ↦ (norm_embedding_le_house _ σ).trans (hηle a b)) hzero'
  -- With `m = 2 h + 2`, the exponents of `r` add up to `(1 - r) / 2`.
  have hexp : (((h - 1) * r : ℕ) : ℝ) + ((3 - m : ℝ) * r + 1) / 2 = (1 - (r : ℝ)) / 2 := by
    simp only [m]
    push_cast [hh]
    ring
  refine (hN r (hNn.trans hnr)).not_ge ?_
  calc (1 : ℝ) ≤ c₂ ^ r * (r : ℝ) ^ ((h - 1) * r) * ‖σ (∑ a, ∑ b, (η a b : K) *
        (((a + 1 : ℕ) : K) + (b + 1 : ℕ) * β) ^ r *
          (α ^ ((a + 1 : ℕ) * t₀) * γ ^ ((b + 1 : ℕ) * t₀)))‖ := hL
    _ ≤ c₂ ^ r * (r : ℝ) ^ ((h - 1) * r) * (c₃ ^ r * (r : ℝ) ^ (((3 - m : ℝ) * r + 1) / 2)) := by
        gcongr
    _ = (c₂ * c₃) ^ r * (r : ℝ) ^ ((1 - (r : ℝ)) / 2) := by
        rw [← hexp, Real.rpow_add hr₀, Real.rpow_natCast, mul_pow]
        ring

/-- **The Gelfond–Schneider theorem** (Karatarakis–Wiedijk, §3). Let `λ ≠ 0` be a complex number
such that `exp λ` is algebraic, and let `β` be an algebraic number that is not rational. Then
`exp (β λ)` is transcendental. -/
theorem transcendental_exp_mul {l β : ℂ} (hl : l ≠ 0) (hα : IsAlgebraic ℚ (Complex.exp l))
    (hβ : IsAlgebraic ℚ β) (hirr : ∀ q : ℚ, β ≠ q) :
    Transcendental ℚ (Complex.exp (β * l)) := by
  intro hγ
  -- The number field `K = ℚ(exp λ, β, exp (β λ)) ⊂ ℂ`, with its inclusion `σ` into `ℂ`.
  set K := IntermediateField.adjoin ℚ ({Complex.exp l, β, Complex.exp (β * l)} : Set ℂ)
  have : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_adjoin <| by
    rintro x (rfl | rfl | rfl)
    exacts [hα.isIntegral, hβ.isIntegral, hγ.isIntegral]
  have : NumberField K := { }
  let α' : K := ⟨Complex.exp l, IntermediateField.subset_adjoin _ _ (by simp)⟩
  let β' : K := ⟨β, IntermediateField.subset_adjoin _ _ (by simp)⟩
  let γ' : K := ⟨Complex.exp (β * l), IntermediateField.subset_adjoin _ _ (by simp)⟩
  refine gelfond_false K.val.toRingHom hl (α := α') (β := β') (γ := γ') rfl rfl fun q hq ↦
    hirr q ?_
  simpa [β'] using congrArg Subtype.val hq.symm

/-- **The Gelfond–Schneider theorem for `Complex.cpow`.** If `α ≠ 0, 1` and `β` are algebraic
numbers and `β` is not rational, then the principal value `α ^ β = exp (β log α)` is
transcendental. -/
theorem transcendental_cpow {α β : ℂ} (hα : IsAlgebraic ℚ α) (h0 : α ≠ 0) (h1 : α ≠ 1)
    (hβ : IsAlgebraic ℚ β) (hirr : ∀ q : ℚ, β ≠ q) : Transcendental ℚ (α ^ β) := by
  have hl : Complex.log α ≠ 0 := fun h ↦ h1 (by rw [← Complex.exp_log h0, h, Complex.exp_zero])
  rw [Complex.cpow_def_of_ne_zero h0, mul_comm]
  exact transcendental_exp_mul hl (by rwa [Complex.exp_log h0]) hβ hirr

end TauCeti
