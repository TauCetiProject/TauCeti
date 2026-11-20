/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.NumberTheory.Padics.Complex
import TauCeti.NumberTheory.NumberField.House.Ultrametric
import TauCeti.NumberTheory.Padics.Basic

/-!
# Liouville's inequality in `ℂ_[p]`

The hypothesis on integers in `NumberField.one_le_pow_mul_norm_embedding_of_isUltrametricDist`
holds in `ℂ_[p]`, by `Padic.one_le_abs_mul_norm_intCast`, so Liouville's inequality applies to
every embedding of a number field into `ℂ_[p]`.

The exponent of the house is the degree `D`, not `D - 1` as at an archimedean place: for `K = ℚ`
and `x = p` the archimedean form `1 ≤ ‖σ x‖ ⌈x⌉ ^ (D - 1)` would read `1 ≤ ‖p‖ = p⁻¹` in `ℚ_[p]`.
-/

variable (p : ℕ) [Fact p.Prime]

/-- Liouville's inequality at an embedding into `ℂ_[p]`. -/
example {K : Type*} [Field K] [NumberField K] {δ a : ℕ} (hδ : δ ≠ 0) {x : K} (hx0 : x ≠ 0)
    {H : ℝ} (hint : IsIntegral ℤ ((δ : K) ^ a * x))
    (hH : NumberField.house ((δ : K) ^ a * x) ≤ H) (σ : K →+* ℂ_[p]) :
    1 ≤ H ^ Module.finrank ℚ K * ‖σ x‖ :=
  NumberField.one_le_pow_mul_norm_embedding_of_isUltrametricDist
    (fun n hn ↦ TauCeti.norm_intCast_eq_norm_padic (p := p) (K := ℂ_[p]) n ▸
      Padic.one_le_abs_mul_norm_intCast hn) hδ hx0 hint hH σ

/-- The archimedean exponent `D - 1` fails at a `p`-adic place: for `K = ℚ` and `x = p`. -/
example : ‖Rat.castHom ℚ_[p] p‖ * NumberField.house (p : ℚ) ^ (Module.finrank ℚ ℚ - 1) < 1 := by
  simpa using Padic.norm_p_lt_one (p := p)
