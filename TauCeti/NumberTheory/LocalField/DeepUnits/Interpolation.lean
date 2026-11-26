/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.FiniteExtension.PadicNorm
public import TauCeti.NumberTheory.Padics.Exp.Polynomial
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# Valuations of interpolated sums of products of deep-unit powers

Let `K` be a finite extension of `ℚ_[p]` with absolute ramification index `e`, so that its
normalized additive valuation satisfies `v_K(p) = e`. Let `αⱼ` (`j ∈ t`) be elements of `K` with

```text
v_K(αⱼ - 1) > ρ + e / (p - 1)
```

for a real radius parameter `ρ ≥ 0`, and for a finite set `Λ` of integer exponent vectors let
`x_l = ∑ⱼ lⱼ log αⱼ`. This file bounds below the valuation of the divided derivatives

```text
Φ⁽ᵏ⁾(z) / k! = ∑_l a_l (x_l ^ k / k!) ∏ⱼ αⱼ ^ (lⱼ z)
```

at integers `z` of the auxiliary function `Φ(z) = ∑_l a_l ∏ⱼ αⱼ ^ (lⱼ z)` of the `p`-adic method of
linear forms in logarithms, when `Φ` vanishes to order `T` on Yu's grid of the integers
`0 ≤ b < N` not divisible by an auxiliary integer `q` prime to `p`, a grid of `S` points. If
`v_K(a_l) ≥ μ` for every `l`, then

```text
v_K(Φ⁽ᵏ⁾(z) / k!) ≥ k ρ + μ + (T - k) ((q - 1) e v_p(⌊N / q⌋!) + S ρ).
```

This is the normed interpolation bound `TauCeti.norm_sum_mul_prod_zpow_le_mul_norm_factorial_pow`
read through the `p`-adic norm `‖x‖ = p ^ (-v_K(x) / e)` of `TauCeti.padicNormedField`, with the
radius `c = p ^ (ρ / e)`; the ramification index enters through the valuation `e v_p(n)` of an
integer `n` in `K`. The valuation is `TauCeti.realAddValuation`, which is `⊤` at `0`, so the bound
also covers vanishing values. The logarithm is that of the given topology of `K`.

## Main results

* `TauCeti.le_realAddValuation_sum_mul_prod_zpow`: the valuation bound above.

## References

* K. Yu, *Linear forms in p-adic logarithms. II*, Compositio Math. 74 (1990), 15–113, §1.
-/

public section

open Finset NormedSpace
open scoped Nat

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {p : ℕ} [Fact p.Prime] [FinitePadicExtension K p]

/-- **Valuations of interpolated sums of products of deep-unit powers.** Let `K` be a finite
extension of `ℚ_[p]` with absolute ramification index `e`, `ρ ≥ 0` a radius parameter and `αⱼ`
(`j ∈ t`) elements with `v_K(αⱼ - 1) > ρ + e / (p - 1)`. For a finite set `Λ` of integer exponent
vectors and coefficients with `v_K(a_l) ≥ μ`, put `x_l = ∑ⱼ lⱼ log αⱼ`, and let `q` be a positive
integer prime to `p`. If `∑_l a_l x_l ^ τ ∏ⱼ αⱼ ^ (lⱼ b) = 0` for every `τ < T` and every integer
`0 ≤ b < N` not divisible by `q`, a grid of `S` points, then for every `k` and every integer `z`

```text
v_K(∑_l a_l (x_l ^ k / k!) ∏ⱼ αⱼ ^ (lⱼ z)) ≥ k ρ + μ + (T - k) ((q - 1) e v_p(⌊N / q⌋!) + S ρ).
```

Here `T - k` and `q - 1` are natural-number subtractions, truncated at zero. -/
theorem le_realAddValuation_sum_mul_prod_zpow {κ : Type*} {t : Finset κ} {α : κ → K} {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (hα : ∀ j ∈ t, ((ρ + absoluteRamificationIndex K p / (p - 1 : ℝ) : ℝ) : WithTop ℝ) <
      realAddValuation K (α j - 1))
    {Λ : Finset (κ → ℤ)} {a : (κ → ℤ) → K} {μ : ℝ}
    (ha : ∀ l ∈ Λ, (μ : WithTop ℝ) ≤ realAddValuation K (a l)) {q : ℕ} (hq : p.Coprime q)
    {N T : ℕ}
    (hzero : ∀ b < N, ¬q ∣ b → ∀ τ < T, ∑ l ∈ Λ,
      a l * (∑ j ∈ t, (l j : K) * log (α j)) ^ τ * ∏ j ∈ t, α j ^ (l j * b) = 0)
    (k : ℕ) (z : ℤ) :
    (((k * ρ + μ + (T - k : ℕ) * ((q - 1 : ℕ) * absoluteRamificationIndex K p *
        padicValNat p (N / q)! + ((range N).filter (¬q ∣ ·)).card * ρ) : ℝ)) : WithTop ℝ) ≤
      realAddValuation K (∑ l ∈ Λ, a l * ((∑ j ∈ t, (l j : K) * log (α j)) ^ k / k !) *
        ∏ j ∈ t, α j ^ (l j * z)) := by
  let _ := padicNormedField K p
  let _ := padicNormedAlgebra K p
  set e : ℝ := (absoluteRamificationIndex K p : ℝ) with he_def
  have hP : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hP1 : (p : ℝ) - 1 ≠ 0 :=
    sub_ne_zero.mpr (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt).ne'
  have he : 0 < e := Nat.cast_pos.mpr (absoluteRamificationIndex_pos K p)
  have hc : 1 ≤ (p : ℝ) ^ (ρ / e) :=
    Real.one_le_rpow (Nat.one_le_cast.mpr (Fact.out : p.Prime).one_lt.le) (div_nonneg hρ he.le)
  have hα' (j : κ) (hj : j ∈ t) :
      ‖α j - 1‖ * (p : ℝ) ^ (ρ / e) < (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹) := by
    have h := (padicNormedField_norm_lt_rpow_iff p (α j - 1) _).2 (hα j hj)
    calc ‖α j - 1‖ * (p : ℝ) ^ (ρ / e)
        < (p : ℝ) ^ (-(ρ + e / (p - 1)) / e) * (p : ℝ) ^ (ρ / e) :=
          mul_lt_mul_of_pos_right h (Real.rpow_pos_of_pos hP _)
      _ = (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹) := by
          rw [← Real.rpow_add hP]
          congr 1
          field_simp
          ring
  have ha' (l : κ → ℤ) (hl : l ∈ Λ) : ‖a l‖ ≤ (p : ℝ) ^ (-μ / e) :=
    (padicNormedField_norm_le_rpow_iff p (a l) μ).2 (ha l hl)
  have hfac : ‖(((N / q)! : ℕ) : ℤ_[p])‖ = (p : ℝ) ^ (-(padicValNat p (N / q)! : ℝ)) := by
    rw [PadicInt.norm_eq_zpow_neg_valuation (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)),
      PadicInt.valuation_natCast, ← Real.rpow_intCast, Int.cast_neg, Int.cast_natCast]
  have h := norm_sum_mul_prod_zpow_le_mul_norm_factorial_pow hc hα' (by positivity) ha' hq hzero k z
  rw [← padicNormedField_norm_le_rpow_iff p]
  refine h.trans_eq ?_
  have hpow (y : ℝ) (n : ℕ) : ((p : ℝ) ^ y) ^ n = (p : ℝ) ^ (y * n) := by
    rw [Real.rpow_mul hP.le, Real.rpow_natCast]
  rw [hfac, ← Real.rpow_neg hP.le, ← he_def]
  simp only [hpow, ← Real.rpow_sub hP, ← Real.rpow_add hP]
  congr 1
  field_simp
  ring

end TauCeti
