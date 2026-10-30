/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.SlashActions
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.FiniteFourier
import TauCeti.Analysis.Fourier.PoissonSummation
import TauCeti.Analysis.SpecialFunctions.Gaussian.Schwartz

/-!
# The inversion law of theta series

Let `L` be a full lattice in a real inner product space `E` of even dimension `n = 2k`, with dual
lattice `L^∨`. Poisson summation over `L`, applied to the Gaussian `x ↦ exp (π i (-1/τ) ‖x‖²)`,
whose Fourier transform is `(-i)^k τ^k exp (π i τ ‖y‖²)`, gives the behaviour of theta series
under the inversion `S : τ ↦ -1/τ`:

* at a general translate `v : E`,
  `θ_{v+L}(-1/τ) = (covol L)⁻¹ (-i)^k τ^k ∑_{m ∈ L^∨} e(⟪v, m⟫) exp (π i ‖m‖² τ)`,
  with `e(x) = exp (2 π i x)`;
* at `v = 0`, `Θ_L(-1/τ) = (covol L)⁻¹ (-i)^k τ^k Θ_{L^∨}(τ)`, that is
  `Θ_L ∣[k] S = (-i)^k (covol L)⁻¹ Θ_{L^∨}` in weight `k`;
* for integral `L` and `γ ∈ L^∨`, splitting the dual sum into the cosets of `L` gives the
  vector-valued law `θ_γ(-1/τ) = (covol L)⁻¹ (-i)^k τ^k ∑_{δ ∈ L^∨/L} e(b_L(γ, δ)) θ_δ(τ)`.

No integrality is needed for the first two statements. The phase `e(+⟪v, m⟫)` is the one produced
by Poisson summation with Mathlib's Fourier transform; since `θ_δ = θ_{-δ}`, the vector-valued law
also holds with the opposite phase (`ZLattice.IsIntegral.sum_discriminantPairingChar_neg`).

## Main statements

* `ZLattice.thetaCoset_S_smul`: the inversion law at a general translate.
* `ZLattice.thetaSeries_S_smul`, `ZLattice.thetaSeries_slash_S`: the scalar inversion law.
* `ZLattice.IsIntegral.thetaCoset_S_smul`: the vector-valued inversion law.

## References

* J.-P. Serre, *A Course in Arithmetic*, Ch. VII §6.
* W. Ebeling, *Lattices and Codes*, §3.2.
-/

public section

open Complex Module
open UpperHalfPlane (modular_S_smul)
open scoped Real RealInnerProductSpace FourierTransform ModularForm UpperHalfPlane

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  {k : ℕ}

/-- **The inversion law of theta series at a general translate**: if `dim E = 2k`, then for every
`v : E` and `τ ∈ ℍ`,
`θ_{v+L}(-1/τ) = (covol L)⁻¹ (-i)^k τ^k ∑_{m ∈ L^∨} e(⟪v, m⟫) exp (π i ‖m‖² τ)`. -/
theorem thetaCoset_S_smul (hk : finrank ℝ E = 2 * k) (v : E) (τ : ℍ) :
    thetaCoset L v (ModularGroup.S • τ) = (covolume L : ℂ)⁻¹ * ((-I) ^ k * (τ : ℂ) ^ k) *
      ∑' m : dual L, cexp (2 * π * I * ⟪v, (m : E)⟫) *
        cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * τ) := by
  generalize hσ : ModularGroup.S • τ = σ
  have hστ : (σ : ℂ) = -(τ : ℂ)⁻¹ := by
    rw [← hσ, modular_S_smul]
    simp [inv_neg]
  have hb : 0 < (-(π * I * (σ : ℂ))).re := by simpa using mul_pos Real.pi_pos σ.im_pos
  -- The theta series at `σ` is the periodization of the Schwartz Gaussian `exp (π i σ ‖x‖²)`.
  have hg : (TauCeti.gaussianSchwartzMap hb : E → ℂ) =
      fun x : E ↦ cexp (π * I * (‖x‖ ^ 2 : ℝ) * σ) := by
    ext x
    rw [TauCeti.gaussianSchwartzMap_apply]
    push_cast
    ring_nf
  -- Its Fourier transform is `(-i)^k τ^k exp (π i τ ‖y‖²)`, since `-1/σ = τ`.
  have hF (m : E) : 𝓕 (TauCeti.gaussianSchwartzMap hb : E → ℂ) m =
      ((-I) ^ k * (τ : ℂ) ^ k) * cexp (π * I * (‖m‖ ^ 2 : ℝ) * τ) := by
    have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
    rw [hg, TauCeti.fourier_cexp_pi_mul_I_mul_norm_sq_mul_of_finrank_eq hk σ.im_pos, hστ]
    congr 1
    · rw [← mul_pow, ← mul_pow, ← inv_pow]
      congr 1
      field_simp
      ring_nf
      simp [I_sq]
    · congr 1
      field_simp
  calc thetaCoset L v σ = ∑' ℓ : L, (TauCeti.gaussianSchwartzMap hb : E → ℂ) (v + ℓ) := by
        rw [thetaCoset_apply, hg]
    _ = (covolume L : ℂ)⁻¹ * ∑' m : dual L, ((-I) ^ k * (τ : ℂ) ^ k) *
          (cexp (2 * π * I * ⟪v, (m : E)⟫) * cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * τ)) := by
        rw [SchwartzMap.tsum_eq_tsum_dual_fourier]
        congr 1
        exact tsum_congr fun m ↦ by rw [hF]; ring
    _ = _ := by rw [tsum_mul_left, ← mul_assoc]

/-- **The inversion law of theta series**: if `dim E = 2k`, then for `τ ∈ ℍ`,
`Θ_L(-1/τ) = (covol L)⁻¹ (-i)^k τ^k Θ_{L^∨}(τ)`. -/
theorem thetaSeries_S_smul (hk : finrank ℝ E = 2 * k) (τ : ℍ) :
    thetaSeries L (ModularGroup.S • τ) =
      (covolume L : ℂ)⁻¹ * ((-I) ^ k * (τ : ℂ) ^ k) * thetaSeries (dual L) τ := by
  rw [← thetaCoset_zero, thetaCoset_S_smul L hk, thetaSeries_apply]
  simp

/-- **The inversion law of theta series in slash form**: if `dim E = 2k`, then in weight `k`,
`Θ_L ∣[k] S = (-i)^k (covol L)⁻¹ Θ_{L^∨}`. -/
theorem thetaSeries_slash_S (hk : finrank ℝ E = 2 * k) :
    thetaSeries L ∣[(k : ℤ)] ModularGroup.S =
      ((-I) ^ k * (covolume L : ℂ)⁻¹) • thetaSeries (dual L) := by
  ext τ
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  rw [ModularForm.SL_slash_apply, thetaSeries_S_smul L hk, ModularGroup.denom_S, Pi.smul_apply,
    smul_eq_mul, zpow_neg, zpow_natCast]
  field_simp

namespace IsIntegral

variable {L}

/-- **The vector-valued inversion law of coset theta series**: if `L` is integral and
`dim E = 2k`, then for `γ ∈ L^∨` and `τ ∈ ℍ`,
`θ_{γ+L}(-1/τ) = (covol L)⁻¹ (-i)^k τ^k ∑_{δ ∈ L^∨/L} e(b_L(γ, δ)) θ_{δ+L}(τ)`, a finite sum
over the discriminant group. -/
theorem thetaCoset_S_smul (hL : IsIntegral L) [Fintype (DiscriminantGroup L)]
    (hk : finrank ℝ E = 2 * k) (γ : dual L) (τ : ℍ) :
    thetaCoset L γ (ModularGroup.S • τ) = (covolume L : ℂ)⁻¹ * ((-I) ^ k * (τ : ℂ) ^ k) *
      ∑ δ : DiscriminantGroup L,
        hL.discriminantPairingChar (Submodule.Quotient.mk γ) δ * thetaCosetClass L δ τ := by
  rw [ZLattice.thetaCoset_S_smul L hk, ← hL.tsum_exp_inner_mul_thetaTerm γ τ]

end IsIntegral

end ZLattice
