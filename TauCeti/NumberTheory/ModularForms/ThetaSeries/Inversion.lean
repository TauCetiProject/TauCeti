/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.SlashActions
public import TauCeti.Analysis.Fourier.PoissonSummation
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Basic
import TauCeti.Analysis.Distribution.SchwartzSpace.Gaussian

/-!
# The inversion law of theta series

Let `L` be a full lattice in a real inner product space `E` of dimension `n`, with dual lattice
`L^∨`. This file proves the behaviour of the theta series of `L` and of its translates under the
inversion `S : τ ↦ -1/τ` of the upper half-plane.

The input is the Fourier transform of the Gaussian `x ↦ exp (π i τ ‖x‖²)`, for `τ ∈ ℍ`:

`𝓕 (x ↦ exp (π i τ ‖x‖²)) y = (τ / i) ^ (-n/2) * exp (π i (-1/τ) ‖y‖²)`,

which is `UpperHalfPlane.fourier_gaussian`, Mathlib's `fourier_gaussian_innerProductSpace` at
`b = -π i τ`. The power is a complex power with the principal branch; `τ / i = -iτ` has positive
real part, so there is no ambiguity. In even dimension `n = 2k` it is the honest integer power
`((-i)^k τ^k)⁻¹` (`UpperHalfPlane.fourier_gaussian_of_finrank_eq_two_mul`).

Poisson summation over `L` (`SchwartzMap.tsum_eq_tsum_dual_fourier`), applied to this Gaussian at
the point `-1/τ` and translated by `v : E`, gives the **inversion law at a general translate**

`θ_{v+L}(-1/τ) = (covolume L)⁻¹ (-i)^k τ^k ∑_{m ∈ L^∨} exp (2πi ⟪v, m⟫) exp (π i ‖m‖² τ)`

in dimension `n = 2k`, and at `v = 0` the **scalar inversion law**

`Θ_L(-1/τ) = (covolume L)⁻¹ (-i)^k τ^k Θ_{L^∨}(τ)`,

that is `Θ_L ∣[k] S = (-i)^k (covolume L)⁻¹ Θ_{L^∨}`. No integrality of `L` is needed. Applied
twice, with `(L^∨)^∨ = L` and `covolume L^∨ = (covolume L)⁻¹`, it returns `(-1)^k Θ_L`, which is
the action of `S² = -1` in weight `k`, as it must be. Together with the translation law of an even
lattice, this is what makes the theta series of an even unimodular lattice a modular form of level
one.

## Main statements

* `ZLattice.thetaCoset_S_smul`: the inversion law at a general translate.
* `ZLattice.thetaSeries_S_smul`, `ZLattice.thetaSeries_slash_S`: the scalar inversion law.
* `ZLattice.thetaSeries_slash_S_sq`: applied twice, the inversion law gives the action
  `(-1)^k` of `S² = -1` in weight `k`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Ch. VII §6.
* W. Ebeling, *Lattices and Codes*, Ch. 3.
-/

public section

open Complex Module
open scoped Real RealInnerProductSpace FourierTransform ModularForm SchwartzMap UpperHalfPlane

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-- The automorphy factor of the inversion law: `((-i)^k (-1/τ)^k)⁻¹ = (-i)^k τ^k`. -/
private theorem inv_neg_I_pow_mul_S_smul_pow (k : ℕ) (τ : ℍ) :
    ((-I) ^ k * ((ModularGroup.S • τ : ℍ) : ℂ) ^ k)⁻¹ = (-I) ^ k * (τ : ℂ) ^ k := by
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, ← mul_pow, ← mul_pow, ← inv_pow]
  congr 1
  field_simp
  rw [I_sq]
  ring

/-- The **inversion law at a general translate**: for a full lattice `L` in a real inner product
space of dimension `2k` and `v : E`,
`θ_{v+L}(-1/τ) = (covolume L)⁻¹ (-i)^k τ^k ∑_{m ∈ L^∨} exp (2πi ⟪v, m⟫) exp (π i ‖m‖² τ)`. -/
theorem thetaCoset_S_smul {k : ℕ} (hn : finrank ℝ E = 2 * k) (v : E) (τ : ℍ) :
    thetaCoset L v (ModularGroup.S • τ) =
      (covolume L : ℂ)⁻¹ * (-I) ^ k * (τ : ℂ) ^ k *
        ∑' m : dual L,
          cexp (2 * π * I * ⟪v, (m : E)⟫) * cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * τ) := by
  -- Poisson summation for the Gaussian `x ↦ exp (π i σ ‖x‖²)` at `σ = -1/τ`, translated by `v`.
  have hσ : -1 / ((ModularGroup.S • τ : ℍ) : ℂ) = τ := by
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk]
    field_simp
  have hpoisson := (SchwartzMap.gaussian _ (ModularGroup.S • τ).re_neg_pi_mul_I_mul_pos :
      𝓢(E, ℂ)).tsum_eq_tsum_dual_fourier L v
  simp only [SchwartzMap.coe_gaussian_neg_pi_mul_I_mul, ← thetaCoset_apply] at hpoisson
  have hterm (m : dual L) :
      𝓕 (fun x : E ↦ cexp (π * I * (‖x‖ ^ 2 : ℝ) * (ModularGroup.S • τ : ℍ))) m *
          cexp (2 * π * I * ⟪v, (m : E)⟫) =
        (-I) ^ k * (τ : ℂ) ^ k *
          (cexp (2 * π * I * ⟪v, (m : E)⟫) * cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * τ)) := by
    rw [UpperHalfPlane.fourier_gaussian_of_finrank_eq_two_mul hn, hσ,
      inv_neg_I_pow_mul_S_smul_pow]
    ring
  rw [hpoisson, tsum_congr hterm, tsum_mul_left]
  ring

/-- The **scalar inversion law**: for a full lattice `L` in a real inner product space of
dimension `2k`, `Θ_L(-1/τ) = (covolume L)⁻¹ (-i)^k τ^k Θ_{L^∨}(τ)`. -/
theorem thetaSeries_S_smul {k : ℕ} (hn : finrank ℝ E = 2 * k) (τ : ℍ) :
    thetaSeries L (ModularGroup.S • τ) =
      (covolume L : ℂ)⁻¹ * (-I) ^ k * (τ : ℂ) ^ k * thetaSeries (dual L) τ := by
  rw [← thetaCoset_zero L, thetaCoset_S_smul L hn, thetaSeries_apply]
  simp

/-- The **scalar inversion law** in slash form: for a full lattice `L` in a real inner product
space of dimension `2k`, `Θ_L ∣[k] S = (-i)^k (covolume L)⁻¹ Θ_{L^∨}`. -/
theorem thetaSeries_slash_S {k : ℕ} (hn : finrank ℝ E = 2 * k) :
    thetaSeries L ∣[(k : ℤ)] ModularGroup.S =
      ((-I) ^ k * (covolume L : ℂ)⁻¹) • thetaSeries (dual L) := by
  ext τ
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  rw [ModularForm.SL_slash_apply, ModularGroup.denom_S, thetaSeries_S_smul L hn, Pi.smul_apply,
    smul_eq_mul, zpow_neg, zpow_natCast]
  field_simp


/-- **Consistency of the inversion law with `S² = -1`**: applying `thetaSeries_slash_S` twice,
with `(L^∨)^∨ = L` and `covolume L^∨ = (covolume L)⁻¹`, gives `Θ_L ∣[k] S² = (-1)^k Θ_L` for a
full lattice `L` in a real inner product space of dimension `2k`. This is the action of
`S² = -1` in weight `k`, which is not trivial when `k` is odd. -/
theorem thetaSeries_slash_S_sq {k : ℕ} (hn : finrank ℝ E = 2 * k) :
    thetaSeries L ∣[(k : ℤ)] (ModularGroup.S ^ 2) = ((-1 : ℂ) ^ k) • thetaSeries L := by
  have hc : (covolume L : ℂ) ≠ 0 := by exact_mod_cast (covolume_pos L MeasureTheory.volume).ne'
  rw [sq, SlashAction.slash_mul, thetaSeries_slash_S L hn, ModularForm.SL_smul_slash,
    thetaSeries_slash_S (dual L) hn, dual_dual, covolume_dual, smul_smul]
  congr 1
  push_cast
  field_simp
  rw [← pow_mul, mul_comm, pow_mul, neg_sq, I_sq]

end ZLattice
