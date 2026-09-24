/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Complex.Basic

/-!
# Nonvanishing on the line `Re s = 1` from a 3-4-1 bound

The classical `3-4-1` argument proves that an `L`-series does not vanish on the line `Re s = 1`
in two steps. The first is arithmetic: an Euler product and the positivity of
`3 + 4 cos θ + cos 2θ` give, for real `σ > 1`,

```text
1 ≤ ‖L₀(σ) ^ 3 * L₁(σ + it) ^ 4 * L₂(σ + 2it)‖,
```

where `L₀` is the series of the trivial character, `L₁` that of a character `χ`, and `L₂` that of
`χ²`. The second step is analytic and uses no arithmetic: if `L₀` has at most a simple pole at
`1`, `L₂` stays bounded near `1 + 2it`, and `L₁` is differentiable at `1 + it` and vanishes
there, then as `σ → 1⁺` the product is `O((σ - 1)⁻³ (σ - 1)⁴) = O(σ - 1)`, contradicting the
lower bound. This file proves the second step for arbitrary functions, so that each family of
`L`-series needs to supply only its own `3-4-1` bound and its analytic inputs.

The pole condition is stated as `f₀(σ) = O((σ - 1)⁻¹)` as `σ → 1⁺`. It follows from the one-sided
residue limit `(σ - 1) f₀(σ) → r`, which is how the pole of a Dedekind zeta function is usually
available; `isBigO_inv_sub_one_of_tendsto_sub_one_mul` records that implication.

## Main results

* `TauCeti.LSeries.isBigO_inv_sub_one_of_tendsto_sub_one_mul`: a function with a finite one-sided
  residue at `1` is `O((σ - 1)⁻¹)` as `σ → 1⁺`.
* `TauCeti.LSeries.ne_zero_of_threeFourOne`: the `3-4-1` bound together with the pole bound for
  `f₀`, differentiability of `f₁` at `1 + it` and continuity of `f₂` at `1 + 2it` forces
  `f₁ (1 + it) ≠ 0`.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 4.
* The argument is the one in Mathlib's `Mathlib/NumberTheory/LSeries/Nonvanishing.lean`, by
  Michael Stoll and David Loeffler, where the private lemma
  `DirichletCharacter.LFunction_ne_zero_of_not_quadratic_or_ne_one` carries it out for Dirichlet
  `L`-functions. Here it is separated from the Dirichlet characters.
-/

public section

namespace TauCeti.LSeries

open Asymptotics Complex Filter
open scoped Topology

/-- **A simple pole is `O((σ - 1)⁻¹)`.** If `(σ - 1) f(σ)` has a limit as `σ → 1⁺`, then
`f(σ) = O((σ - 1)⁻¹)` as `σ → 1⁺`. -/
theorem isBigO_inv_sub_one_of_tendsto_sub_one_mul {f : ℝ → ℂ} {r : ℂ}
    (h : Tendsto (fun σ : ℝ ↦ ((σ : ℂ) - 1) * f σ) (𝓝[>] 1) (𝓝 r)) :
    f =O[𝓝[>] 1] fun σ : ℝ ↦ (σ - 1)⁻¹ := by
  have hinv : (fun σ : ℝ ↦ ((σ : ℂ) - 1)⁻¹) =O[𝓝[>] 1] fun σ : ℝ ↦ (σ - 1)⁻¹ :=
    isBigO_of_le _ fun σ ↦ by rw [← ofReal_one, ← ofReal_sub, ← ofReal_inv, norm_real]
  refine ((h.isBigO_one ℝ).mul hinv).congr' ?_ (by simp)
  filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
  have : (σ : ℂ) - 1 ≠ 0 := by
    rw [← ofReal_one, ← ofReal_sub, ofReal_ne_zero]
    exact sub_ne_zero.mpr hσ.ne'
  field_simp

/-- **The `3-4-1` nonvanishing criterion.** Let `f₀`, `f₁`, `f₂` be complex functions and `t` real.
Suppose that, as `σ → 1⁺` through real values,

* `1 ≤ ‖f₀(σ) ^ 3 * f₁(σ + it) ^ 4 * f₂(σ + 2it)‖` eventually;
* `f₀(σ) = O((σ - 1)⁻¹)`, so `f₀` has at most a simple pole at `1`;

and that `f₁` is complex differentiable at `1 + it` and `f₂` is continuous at `1 + 2it`. Then
`f₁ (1 + it) ≠ 0`.

The bound is the one an Euler product and `3 + 4 cos θ + cos 2θ ≥ 0` give when `f₀`, `f₁`, `f₂` are
the series of the trivial character, of a character `χ`, and of `χ²`; the analytic hypotheses are
where a continuation of these series across `Re s = 1` is used. -/
theorem ne_zero_of_threeFourOne {f₀ f₁ f₂ : ℂ → ℂ} {t : ℝ}
    (hbound : ∀ᶠ σ : ℝ in 𝓝[>] 1,
      1 ≤ ‖f₀ σ ^ 3 * f₁ (σ + I * t) ^ 4 * f₂ (σ + 2 * I * t)‖)
    (h₀ : (fun σ : ℝ ↦ f₀ σ) =O[𝓝[>] 1] fun σ : ℝ ↦ (σ - 1)⁻¹)
    (h₁ : DifferentiableAt ℂ f₁ (1 + I * t)) (h₂ : ContinuousAt f₂ (1 + 2 * I * t)) :
    f₁ (1 + I * t) ≠ 0 := by
  intro hz
  -- The horizontal line `σ ↦ σ + c` through `c + 1` tends to `c + 1` as `σ → 1⁺`.
  have hline (c : ℂ) : Tendsto (fun σ : ℝ ↦ (σ : ℂ) + c) (𝓝[>] 1) (𝓝 (1 + c)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds ?_
    exact (continuous_ofReal.add continuous_const).tendsto' (1 : ℝ) (1 + c) (by simp)
  -- Since `f₁` vanishes at `1 + it`, it is `O(σ - 1)` along the horizontal line.
  have H₁ : (fun σ : ℝ ↦ f₁ (σ + I * t)) =O[𝓝[>] 1] fun σ : ℝ ↦ σ - 1 := by
    have := h₁.isBigO_sub.comp_tendsto (hline (I * t))
    simp only [Function.comp_def, hz, sub_zero, add_sub_add_right_eq_sub] at this
    exact this.trans (isBigO_of_le _ fun σ ↦ by rw [← ofReal_one, ← ofReal_sub, norm_real])
  have H₂ : (fun σ : ℝ ↦ f₂ (σ + 2 * I * t)) =O[𝓝[>] 1] fun _ : ℝ ↦ (1 : ℝ) := by
    have := h₂.tendsto.comp (hline (2 * I * t))
    simp only [Function.comp_def] at this
    exact this.isBigO_one ℝ
  -- Hence the product is `O((σ - 1)⁻³ (σ - 1)⁴) = O(σ - 1)`, which tends to `0`.
  have H : (fun σ : ℝ ↦ f₀ σ ^ 3 * f₁ (σ + I * t) ^ 4 * f₂ (σ + 2 * I * t)) =o[𝓝[>] 1]
      fun _ : ℝ ↦ (1 : ℝ) := by
    have hlin : (fun σ : ℝ ↦ σ - 1) =o[𝓝[>] 1] fun _ : ℝ ↦ (1 : ℝ) :=
      (isLittleO_one_iff ℝ).mpr <| tendsto_nhdsWithin_of_tendsto_nhds <|
        (continuous_id.sub continuous_const).tendsto' (1 : ℝ) 0 (sub_self 1)
    refine (((h₀.pow 3).mul (H₁.pow 4)).mul H₂).trans_isLittleO (hlin.congr' ?_ .rfl)
    filter_upwards [self_mem_nhdsWithin] with σ (hσ : 1 < σ)
    have : σ - 1 ≠ 0 := sub_ne_zero.mpr hσ.ne'
    field_simp
  -- But the product is bounded below by `1`, so `1 = o(1)`, which is absurd.
  exact isLittleO_irrefl (.of_forall fun _ ↦ one_ne_zero) <|
    (IsBigO.of_bound' (by simpa using hbound)).trans_isLittleO H

end TauCeti.LSeries
