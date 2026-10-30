/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.DiscriminantCharacter
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.DiscriminantGroup

/-!
# The finite Fourier sum of coset theta series

For an integral full lattice `L`, the character `exp (2πi ⟪γ, m⟫)` of the dual lattice, with
`γ ∈ L^∨`, is constant on cosets modulo `L`. It is the exponential of the discriminant pairing
of the rational model, transported through `ZLattice.ratModelDiscriminantGroupEquiv`.

This file identifies the absolutely convergent character-weighted theta sum over `L^∨` with
`∑ δ : A_L, e(b_L(γ, δ)) θ_δ`. This is the finite sum occurring in the vector-valued inversion
law. The pairing and its descent are taken from `IntegralLattice.discriminantPairing`; no new
bilinear form on the discriminant group is introduced. Integrality suffices for this splitting,
with no evenness or parity restriction on the rank.

The normalization of the finite sum is also recorded: the inverse covolume is the inverse
square root of the determinant, and, for integral lattices, of the discriminant group's order.

## References

* W. Ebeling, *Lattices and Codes*, 3rd ed., Chapter 2.
-/

public section

open Complex
open scoped Real RealInnerProductSpace UpperHalfPlane

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]

namespace IsIntegral

/-- The character-weighted theta sum over the dual lattice is absolutely convergent. -/
theorem summable_norm_discriminantPairingChar_mul_thetaTerm (hL : IsIntegral L)
    (γ : DiscriminantGroup L) (τ : ℍ) :
    Summable fun m : dual L ↦ ‖hL.discriminantPairingChar γ (Submodule.Quotient.mk m) *
      cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * τ)‖ := by
  simpa only [norm_mul, norm_discriminantPairingChar, one_mul] using
    (summable_thetaSeries (dual L) τ).norm

/-- Splitting the character-weighted theta sum over `L^∨` into cosets of `L` gives the finite
Fourier sum of the coset theta series on the discriminant group. -/
theorem tsum_discriminantPairingChar_mul_thetaTerm (hL : IsIntegral L)
    [Fintype (DiscriminantGroup L)] (γ : DiscriminantGroup L) (τ : ℍ) :
    (∑' m : dual L, hL.discriminantPairingChar γ (Submodule.Quotient.mk m) *
      cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * τ)) =
        ∑ δ : DiscriminantGroup L, hL.discriminantPairingChar γ δ * thetaCosetClass L δ τ := by
  let f : dual L → DiscriminantGroup L := Submodule.Quotient.mk
  let F := fun m : dual L ↦ hL.discriminantPairingChar γ (Submodule.Quotient.mk m) *
    cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * τ)
  have hsum : Summable F := (hL.summable_norm_discriminantPairingChar_mul_thetaTerm γ τ).of_norm
  have hfiber (δ : DiscriminantGroup L) :
      ∑' m : (f ⁻¹' {δ} : Set (dual L)), F m =
        hL.discriminantPairingChar γ δ * thetaCosetClass L δ τ := by
    have hchar (m : (f ⁻¹' {δ} : Set (dual L))) :
        hL.discriminantPairingChar γ (Submodule.Quotient.mk (m : dual L)) =
          hL.discriminantPairingChar γ δ :=
      congrArg (hL.discriminantPairingChar γ) m.2
    simp_rw [F, hchar]
    rw [tsum_mul_left, tsum_thetaTerm_fiber (dual L) (isIntegral_iff_le_dual.mp hL),
      ← thetaCosetClass_mk, Submodule.Quotient.mk_out]
  have h := hsum.hasSum.tsum_fiberwise f
  rw [funext hfiber] at h
  simpa only [tsum_fintype] using h.tsum_eq.symm

/-- In representative notation, the weighted dual theta sum is the finite sum with coefficients
`e(b_L(γ, δ))`. -/
theorem tsum_exp_inner_mul_thetaTerm (hL : IsIntegral L) [Fintype (DiscriminantGroup L)]
    (γ : dual L) (τ : ℍ) :
    (∑' m : dual L, cexp (2 * π * I * (⟪(γ : E), (m : E)⟫ : ℝ)) *
      cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * τ)) =
        ∑ δ : DiscriminantGroup L,
          hL.discriminantPairingChar (Submodule.Quotient.mk γ) δ * thetaCosetClass L δ τ := by
  simpa only [discriminantPairingChar_mk_mk] using
    hL.tsum_discriminantPairingChar_mul_thetaTerm (Submodule.Quotient.mk γ) τ

/-- Negating the phase in the finite Fourier sum leaves it unchanged, since the coset theta
series at `δ` and `-δ` agree. -/
theorem sum_discriminantPairingChar_neg (hL : IsIntegral L) [Fintype (DiscriminantGroup L)]
    (γ : DiscriminantGroup L) (τ : ℍ) :
    (∑ δ : DiscriminantGroup L, hL.discriminantPairingChar γ (-δ) * thetaCosetClass L δ τ) =
      ∑ δ : DiscriminantGroup L, hL.discriminantPairingChar γ δ * thetaCosetClass L δ τ := by
  classical
  simpa only [Equiv.neg_apply, thetaCosetClass_neg] using
    Equiv.sum_comp (Equiv.neg (DiscriminantGroup L))
      (fun δ ↦ hL.discriminantPairingChar γ δ * thetaCosetClass L δ τ)

end IsIntegral

end ZLattice
