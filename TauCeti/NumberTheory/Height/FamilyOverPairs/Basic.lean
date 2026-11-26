/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Padics.Complex
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Heights of families of complex numbers over all places

A *pair* `ι` (`TauCeti.PrimePadicIso`) is a prime `ℓ = ℓ(ι)` with a ring isomorphism
`ι : ℂ ≃+* PadicAlgCl ℓ` onto an algebraic closure of `ℚ_[ℓ]`, which carries the norm extending
`|·|_ℓ`. It serves only to read off an `ℓ`-adic size `‖ι z‖` of a complex number `z`.

A family `y = (y_ι)` of complex numbers indexed by the pairs has *height at most `c`*
(`TauCeti.PrimePadicIso.HeightLe y c`) if there are a multiplier `H ∈ ℂ^×`, a real `α` and exponents
`h_ℓ ≥ 0`, one for each prime `ℓ`, with `|σ(H)| ≤ e^α` for every field automorphism `σ` of `ℂ`,
`|ι(H y_ι)| ≤ ℓ(ι)^{h_{ℓ(ι)}}` for every pair `ι`, and `α + ∑_{ℓ ∈ S} h_ℓ log ℓ ≤ c` for every
finite set `S` of primes. Only this upper bound is defined.

## Main definitions

* `TauCeti.PrimePadicIso`: a prime `ℓ` with a ring isomorphism `ℂ ≃+* PadicAlgCl ℓ`.
* `TauCeti.PrimePadicIso.HeightLe y c`: the family `y` has height at most `c`.

## Main results

* `TauCeti.PrimePadicIso.norm_rpow_ratCast_eq_one`: a real power `N ^ e`, with `e ∈ ℚ` and `N`
  prime to `ℓ(ι)`, has `|ι(N ^ e)| = 1`.
* `TauCeti.PrimePadicIso.HeightLe.mono`: the bound survives raising `c` and shrinking each
  `|ι(y_ι)|`.
* `TauCeti.PrimePadicIso.HeightLe.rpow_mul`: multiplying each `y_ι` by a real power `N_ι ^ e_ι`,
  with `e_ι ∈ ℚ` and `N_ι` prime to `ℓ(ι)`, keeps the bound.
* `TauCeti.PrimePadicIso.HeightLe.of_mul_le`: a bound `|ι(H y_ι)| ≤ e^{e_{ℓ(ι)}}` with real
  exponents of any sign gives a height bound.
* `TauCeti.PrimePadicIso.HeightLe.inv_const`: the constant family `H⁻¹` has height at most `c`
  when `|σ(H)| ≤ e^c` for every `σ`; `TauCeti.PrimePadicIso.heightLe_one`,
  `TauCeti.PrimePadicIso.heightLe_zero`: the constant families `1` and `0` have heights at most
  `0` and at most any `c`.
* `TauCeti.PrimePadicIso.HeightLe.mul`, `TauCeti.PrimePadicIso.HeightLe.prod`,
  `TauCeti.PrimePadicIso.HeightLe.pow`: heights add under products.

The product formula for a rational number over the primes below a bound, which goes with this
calculus, is `Rat.log_abs_add_sum_log_padicNorm_eq_zero`.

## References

* The folder `grh` of https://github.com/lsernau/grh-lean at commit
  72fead102f663d5c7a407964a13dc0cf9d977207 (`New.PrimePadicIso`, `New.HeightLe`,
  `New.HeightLe.mono`, `New.HeightLe.rpow_mul`, `New.HeightLe.of_mul_le`,
  `New.HeightLe.inv_const`, `New.HeightLe.mul`, `New.HeightLe.prod`, `New.HeightLe.pow`).
-/

public section

open Finset

namespace TauCeti

/-- A *pair*: a prime `ℓ` together with a ring isomorphism `ℂ ≃+* PadicAlgCl ℓ` onto an
algebraic closure of `ℚ_[ℓ]`, normed by the extension of the `ℓ`-adic norm. -/
structure PrimePadicIso where
  /-- The prime `ℓ(ι)` of the pair. -/
  prime : ℕ
  /-- The prime `ℓ(ι)` is prime. -/
  [fact_prime : Fact prime.Prime]
  /-- The ring isomorphism `ℂ ≃+* PadicAlgCl ℓ` of the pair. -/
  iso : ℂ ≃+* PadicAlgCl prime

attribute [instance] PrimePadicIso.fact_prime

namespace PrimePadicIso

/-- A family `y = (y_ι)` of complex numbers indexed by the pairs has *height at most `c`* if there
are `H ≠ 0`, `α ∈ ℝ` and `h_ℓ ≥ 0` for the primes `ℓ` with `|σ(H)| ≤ e^α` for every
automorphism `σ` of `ℂ`, `|ι(H y_ι)| ≤ ℓ(ι)^{h_{ℓ(ι)}}` for every pair `ι`, and
`α + ∑_{ℓ ∈ S} h_ℓ log ℓ ≤ c` for every finite set `S` of primes. -/
def HeightLe (y : PrimePadicIso → ℂ) (c : ℝ) : Prop :=
  ∃ H : ℂ, H ≠ 0 ∧ ∃ α : ℝ, ∃ h : ℕ → ℝ, (∀ ℓ : ℕ, ℓ.Prime → 0 ≤ h ℓ) ∧
    (∀ σ : ℂ ≃+* ℂ, ‖σ H‖ ≤ Real.exp α) ∧
    (∀ ι : PrimePadicIso, ‖ι.iso (H * y ι)‖ ≤ (ι.prime : ℝ) ^ h ι.prime) ∧
    ∀ S : Finset ℕ, (∀ ℓ ∈ S, ℓ.Prime) → α + ∑ ℓ ∈ S, h ℓ * Real.log ℓ ≤ c

/-- Unfolding `HeightLe`. -/
theorem heightLe_iff {y : PrimePadicIso → ℂ} {c : ℝ} :
    HeightLe y c ↔ ∃ H : ℂ, H ≠ 0 ∧ ∃ α : ℝ, ∃ h : ℕ → ℝ, (∀ ℓ : ℕ, ℓ.Prime → 0 ≤ h ℓ) ∧
      (∀ σ : ℂ ≃+* ℂ, ‖σ H‖ ≤ Real.exp α) ∧
      (∀ ι : PrimePadicIso, ‖ι.iso (H * y ι)‖ ≤ (ι.prime : ℝ) ^ h ι.prime) ∧
      ∀ S : Finset ℕ, (∀ ℓ ∈ S, ℓ.Prime) → α + ∑ ℓ ∈ S, h ℓ * Real.log ℓ ≤ c :=
  Iff.rfl

variable {y y' : PrimePadicIso → ℂ} {c c' : ℝ}

/-- A height bound survives raising the bound and replacing each `y_ι` by a `y'_ι` with
`|ι(y'_ι)| ≤ |ι(y_ι)|`. -/
theorem HeightLe.mono (hy : HeightLe y c) (hc : c ≤ c')
    (hle : ∀ ι : PrimePadicIso, ‖ι.iso (y' ι)‖ ≤ ‖ι.iso (y ι)‖) : HeightLe y' c' := by
  obtain ⟨H, hH, α, h, h0, hσ, hι, hS⟩ := hy
  refine ⟨H, hH, α, h, h0, hσ, fun ι ↦ ?_, fun S hS' ↦ (hS S hS').trans hc⟩
  calc ‖ι.iso (H * y' ι)‖ = ‖ι.iso H‖ * ‖ι.iso (y' ι)‖ := by rw [map_mul, norm_mul]
    _ ≤ ‖ι.iso H‖ * ‖ι.iso (y ι)‖ := by gcongr; exact hle ι
    _ = ‖ι.iso (H * y ι)‖ := by rw [map_mul, norm_mul]
    _ ≤ _ := hι ι

/-- The image of a positive integer prime to `ℓ` has norm `1` in `PadicAlgCl ℓ`. -/
theorem norm_natCast_eq_one (ι : PrimePadicIso) {N : ℕ} (hN : ι.prime.Coprime N) :
    ‖ι.iso (N : ℂ)‖ = 1 := by
  rw [map_natCast, ← map_natCast (algebraMap ℚ_[ι.prime] (PadicAlgCl ι.prime)),
    PadicAlgCl.norm_extends, Padic.norm_natCast_eq_one_iff]
  exact hN

/-- The image of a real power `N ^ e`, with `e ∈ ℚ` and `N` prime to `ℓ`, has norm `1` in
`PadicAlgCl ℓ`: its `e.den`-th power is `N ^ e.num`. -/
theorem norm_rpow_ratCast_eq_one (ι : PrimePadicIso) {N : ℕ} (hN : ι.prime.Coprime N) (e : ℚ) :
    ‖ι.iso (((N : ℝ) ^ (e : ℝ) : ℝ) : ℂ)‖ = 1 := by
  have hpow : ((N : ℝ) ^ (e : ℝ)) ^ e.den = (N : ℝ) ^ e.num := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg N), ← Real.rpow_intCast]
    congr 1
    exact_mod_cast e.mul_den_eq_num
  have hC : (((N : ℝ) ^ (e : ℝ) : ℝ) : ℂ) ^ e.den = (N : ℂ) ^ e.num := by
    rw [← Complex.ofReal_pow, hpow, Complex.ofReal_zpow, Complex.ofReal_natCast]
  have h := congrArg (fun z ↦ ‖ι.iso z‖) hC
  simp only [map_pow, map_zpow₀, norm_pow, norm_zpow, norm_natCast_eq_one ι hN, one_zpow] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) e.den_ne_zero).1 h

/-- Multiplying each `y_ι` by a real power `N_ι ^ e_ι`, with `e_ι ∈ ℚ` and `N_ι` prime to
`ℓ(ι)` (so `N_ι > 0`), keeps a height bound. -/
theorem HeightLe.rpow_mul (hy : HeightLe y c) (N : PrimePadicIso → ℕ) (e : PrimePadicIso → ℚ)
    (hN : ∀ ι : PrimePadicIso, ι.prime.Coprime (N ι)) :
    HeightLe (fun ι ↦ (((N ι : ℝ) ^ (e ι : ℝ) : ℝ) : ℂ) * y ι) c :=
  hy.mono le_rfl fun ι ↦ by rw [map_mul, norm_mul, norm_rpow_ratCast_eq_one ι (hN ι), one_mul]

/-- A height bound from bounds `|ι(H y_ι)| ≤ e^{e_{ℓ(ι)}}` with real exponents `e_ℓ` of any sign:
if `H ≠ 0`, `|σ(H)| ≤ e^α` for every `σ` and `α + ∑_{ℓ ∈ S} e_ℓ ≤ c` for every finite set `S` of
primes, then `y` has height at most `c`. -/
theorem HeightLe.of_mul_le {H : ℂ} (hH : H ≠ 0) {α : ℝ}
    (hσ : ∀ σ : ℂ ≃+* ℂ, ‖σ H‖ ≤ Real.exp α) (e : ℕ → ℝ)
    (hι : ∀ ι : PrimePadicIso, ‖ι.iso (H * y ι)‖ ≤ Real.exp (e ι.prime))
    (hS : ∀ S : Finset ℕ, (∀ ℓ ∈ S, ℓ.Prime) → α + ∑ ℓ ∈ S, e ℓ ≤ c) : HeightLe y c := by
  refine ⟨H, hH, α, fun ℓ ↦ max (e ℓ) 0 / Real.log ℓ, fun ℓ hℓ ↦ ?_, hσ, fun ι ↦ ?_,
    fun S hS' ↦ ?_⟩
  · exact div_nonneg (le_max_right _ _) (Real.log_nonneg (by exact_mod_cast hℓ.one_lt.le))
  · -- `ℓ ^ (t / log ℓ) = ℓ ^ logb ℓ (e ^ t) = e ^ t` for `t = max (e ℓ) 0`
    have hℓ := ι.fact_prime.out
    beta_reduce
    rw [← Real.log_exp (max (e ι.prime) 0), Real.log_div_log,
      Real.rpow_logb (by exact_mod_cast hℓ.pos) (by exact_mod_cast hℓ.ne_one) (Real.exp_pos _)]
    exact (hι ι).trans (Real.exp_le_exp.2 (le_max_left _ _))
  · have hsum : ∑ ℓ ∈ S, max (e ℓ) 0 / Real.log ℓ * Real.log ℓ = ∑ ℓ ∈ S with 0 ≤ e ℓ, e ℓ := by
      rw [sum_filter]
      refine sum_congr rfl fun ℓ hℓ ↦ ?_
      have hlog : Real.log ℓ ≠ 0 :=
        (Real.log_pos (by exact_mod_cast (hS' ℓ hℓ).one_lt)).ne'
      rw [div_mul_cancel₀ _ hlog]
      split_ifs with he
      · exact max_eq_left he
      · exact max_eq_right (not_le.1 he).le
    rw [hsum]
    exact hS _ fun ℓ hℓ ↦ hS' ℓ (mem_filter.1 hℓ).1

/-- The constant family `0` has height at most `c` for every `c`: take for the multiplier a
positive rational number below `e^c`. -/
theorem heightLe_zero (c : ℝ) : HeightLe 0 c := by
  obtain ⟨r, hr0, hr⟩ := exists_rat_btwn (Real.exp_pos c)
  refine ⟨r, by exact_mod_cast hr0.ne', c, 0, fun _ _ ↦ le_rfl, fun σ ↦ ?_, fun ι ↦ by simp,
    fun S _ ↦ by simp⟩
  rw [map_ratCast, Complex.norm_ratCast, abs_of_pos (by exact_mod_cast hr0)]
  exact hr.le

/-- If `|σ(H)| ≤ e^c` for every automorphism `σ` of `ℂ`, the constant family `H⁻¹` has height at
most `c`. For `H = 0` this is `heightLe_zero`. -/
theorem HeightLe.inv_const {H : ℂ} (hσ : ∀ σ : ℂ ≃+* ℂ, ‖σ H‖ ≤ Real.exp c) :
    HeightLe (fun _ ↦ H⁻¹) c := by
  rcases eq_or_ne H 0 with rfl | hH
  · rw [inv_zero]
    exact heightLe_zero c
  exact ⟨H, hH, c, 0, fun _ _ ↦ le_rfl, hσ, fun ι ↦ by simp [mul_inv_cancel₀ hH],
    fun S _ ↦ by simp⟩

/-- The constant family `1` has height at most `0`. -/
theorem heightLe_one : HeightLe 1 0 :=
  ⟨1, one_ne_zero, 0, 0, fun _ _ ↦ le_rfl, fun σ ↦ by simp, fun ι ↦ by simp, fun S _ ↦ by simp⟩

/-- Heights add: if `y` and `y'` have heights at most `c` and `c'`, the product `y y'` has height
at most `c + c'`. -/
theorem HeightLe.mul (hy : HeightLe y c) (hy' : HeightLe y' c') : HeightLe (y * y') (c + c') := by
  obtain ⟨H, hH, α, h, h0, hσ, hι, hS⟩ := hy
  obtain ⟨H', hH', α', h', h0', hσ', hι', hS'⟩ := hy'
  refine ⟨H * H', mul_ne_zero hH hH', α + α', h + h', fun ℓ hℓ ↦ ?_, fun σ ↦ ?_, fun ι ↦ ?_,
    fun S hSp ↦ ?_⟩
  · exact add_nonneg (h0 ℓ hℓ) (h0' ℓ hℓ)
  · rw [map_mul, norm_mul, Real.exp_add]
    exact mul_le_mul (hσ σ) (hσ' σ) (norm_nonneg _) (Real.exp_pos _).le
  · have hpos : (0 : ℝ) < ι.prime := by exact_mod_cast ι.fact_prime.out.pos
    rw [Pi.add_apply, Real.rpow_add hpos, Pi.mul_apply, mul_mul_mul_comm H H' (y ι) (y' ι),
      map_mul, norm_mul]
    exact mul_le_mul (hι ι) (hι' ι) (norm_nonneg _) (by positivity)
  · simp only [Pi.add_apply, add_mul, sum_add_distrib]
    linarith [hS S hSp, hS' S hSp]

/-- Heights add over finite products: if each `y i` has height at most `c i`, the product
`∏ i ∈ s, y i` has height at most `∑ i ∈ s, c i`. -/
theorem HeightLe.prod {κ : Type*} {s : Finset κ} {y : κ → PrimePadicIso → ℂ} {c : κ → ℝ}
    (hy : ∀ i ∈ s, HeightLe (y i) (c i)) : HeightLe (∏ i ∈ s, y i) (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using heightLe_one
  | insert i s hi ih =>
    rw [prod_insert hi, sum_insert hi]
    exact (hy i (mem_insert_self i s)).mul (ih fun j hj ↦ hy j (mem_insert_of_mem hj))

/-- If `y` has height at most `c`, then `y ^ n` has height at most `n c`. -/
theorem HeightLe.pow (hy : HeightLe y c) (n : ℕ) : HeightLe (y ^ n) (n * c) := by
  simpa using HeightLe.prod (s := range n) fun _ _ ↦ hy

end PrimePadicIso

end TauCeti
