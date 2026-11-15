/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import TauCeti.Analysis.Analytic.ExtractZeros

/-!
# Extracting a zero of finite multiplicity from an entire function

Specializing `AnalyticOnNhd.exists_eq_sub_pow_smul` to entire functions on `ℂ` via
`Complex.analyticOnNhd_univ_iff_differentiable` factors any entire function `f : ℂ → E` of finite
analytic order `m` at `z₀` globally as `f z = (z - z₀) ^ m • g z`, where `g` is entire,
`g z₀ ≠ 0`, and `m! • g z₀ = iteratedDeriv m f z₀`. For a nonzero scalar entire function
`f : ℂ → ℂ`, every point has finite analytic order (`Differentiable.analyticOrderAt_ne_top`), giving
the scalar factorizations `Differentiable.exists_eq_sub_pow_mul` and
`Differentiable.exists_eq_pow_mul`.

## Main results

* `Differentiable.exists_eq_sub_pow_smul`: vector-valued entire zero extraction at `z₀ : ℂ`.
* `Differentiable.exists_eq_sub_pow_mul`: scalar entire zero extraction with
  `g z₀ = iteratedDeriv m f z₀ / m!`.
* `Differentiable.analyticOrderAt_ne_top`: a nonzero entire function has finite analytic order
  everywhere.
* `Differentiable.exists_eq_pow_mul`: global factorization `f z = z ^ m * g z` at the origin for
  any nonzero entire `f : ℂ → ℂ`, where `m = (analyticOrderAt f 0).toNat`.
-/

public section

/-- An entire function `f : ℂ → E` into a Banach space of finite analytic order `m` at `z₀` factors
globally on `ℂ` as `f z = (z - z₀) ^ m • g z`, where `g` is entire, `g z₀ ≠ 0`, and
`m! • g z₀ = iteratedDeriv m f z₀`. -/
theorem Differentiable.exists_eq_sub_pow_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} (hf : Differentiable ℂ f) {z₀ : ℂ} {m : ℕ}
    (hm : analyticOrderAt f z₀ = (m : ℕ∞)) :
    ∃ g : ℂ → E, Differentiable ℂ g ∧ g z₀ ≠ 0 ∧ m.factorial • g z₀ = iteratedDeriv m f z₀ ∧
      ∀ z : ℂ, f z = (z - z₀) ^ m • g z := by
  obtain ⟨g, hg, hg0, hder, hfg⟩ :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hf).exists_eq_sub_pow_smul
      (Set.mem_univ z₀) hm
  exact ⟨g, Complex.analyticOnNhd_univ_iff_differentiable.mp hg, hg0, hder, hfg⟩

/-- A scalar entire function `f : ℂ → ℂ` of finite analytic order `m` at `z₀` factors globally on
`ℂ` as `f z = (z - z₀) ^ m * g z`, with `g` entire, `g z₀ ≠ 0`, and
`g z₀ = iteratedDeriv m f z₀ / m!`. -/
theorem Differentiable.exists_eq_sub_pow_mul {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z₀ : ℂ}
    {m : ℕ} (hm : analyticOrderAt f z₀ = (m : ℕ∞)) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ g z₀ ≠ 0 ∧
      g z₀ = iteratedDeriv m f z₀ / (m.factorial : ℂ) ∧
      ∀ z : ℂ, f z = (z - z₀) ^ m * g z := by
  obtain ⟨g, hg, hg0, hder, hfg⟩ := hf.exists_eq_sub_pow_smul hm
  refine ⟨g, hg, hg0, ?_, fun z ↦ by simpa only [smul_eq_mul] using hfg z⟩
  have hfac : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  rw [← hder, nsmul_eq_mul, mul_div_cancel_left₀ _ hfac]

/-- A nonzero entire function `f : ℂ → ℂ` has finite analytic order at every point `z₀ : ℂ`. -/
theorem Differentiable.analyticOrderAt_ne_top {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf0 : f ≠ 0) (z₀ : ℂ) : analyticOrderAt f z₀ ≠ ⊤ :=
  (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z₀ (fun z ↦ hf.analyticAt z)).not.mpr hf0

/-- A nonzero entire function `f : ℂ → ℂ` factors at the origin as
`f z = z ^ (analyticOrderAt f 0).toNat * g z`, with `g` entire and `g 0 ≠ 0`. -/
theorem Differentiable.exists_eq_pow_mul {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f ≠ 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ g 0 ≠ 0 ∧
      g 0 = iteratedDeriv (analyticOrderAt f 0).toNat f 0 /
        ((analyticOrderAt f 0).toNat.factorial : ℂ) ∧
      ∀ z : ℂ, f z = z ^ (analyticOrderAt f 0).toNat * g z := by
  have htop : analyticOrderAt f 0 ≠ ⊤ := hf.analyticOrderAt_ne_top hf0 0
  obtain ⟨g, hg, hg0, hder, hfg⟩ :=
    hf.exists_eq_sub_pow_mul (z₀ := 0) (m := (analyticOrderAt f 0).toNat)
      (ENat.natCast_toNat htop).symm
  exact ⟨g, hg, hg0, hder, fun z ↦ by simpa only [sub_zero] using hfg z⟩
