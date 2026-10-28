/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.RationalModel
public import TauCeti.Analysis.SpecialFunctions.Complex.Circle
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

/-- The complex additive character `δ ↦ e(b_L(γ, δ))` of the discriminant group, obtained from
its rational-model discriminant pairing. -/
noncomputable def discriminantPairingChar (hL : IsIntegral L) (γ : DiscriminantGroup L) :
    AddChar (DiscriminantGroup L) ℂ :=
  TauCeti.expCircle.compAddMonoidHom
    (((ratModel hL).discriminantPairing (ratModelDiscriminantGroupEquiv hL γ)).toAddMonoidHom.comp
      (ratModelDiscriminantGroupEquiv hL).toAddMonoidHom)

/-- The discriminant character is the exponential of the existing rational discriminant
pairing, transported through the bridge. -/
theorem discriminantPairingChar_apply (hL : IsIntegral L) (γ δ : DiscriminantGroup L) :
    hL.discriminantPairingChar γ δ = TauCeti.expCircle
      ((ratModel hL).discriminantPairing (ratModelDiscriminantGroupEquiv hL γ)
        (ratModelDiscriminantGroupEquiv hL δ)) := (rfl)

/-- On representatives in the dual lattice the character is `exp (2πi ⟪x, y⟫)`. -/
@[simp]
theorem discriminantPairingChar_mk_mk (hL : IsIntegral L) (x y : dual L) :
    hL.discriminantPairingChar (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      cexp (2 * π * I * (⟪(x : E), (y : E)⟫ : ℝ)) := by
  rw [discriminantPairingChar_apply, ratModelDiscriminantGroupEquiv_mk,
    ratModelDiscriminantGroupEquiv_mk, TauCeti.IntegralLattice.discriminantPairing_mk,
    TauCeti.expCircle_coe, ← ratModel_form_ratModelDualEquiv_cast hL x y, Complex.ofReal_ratCast]

/-- The discriminant pairing character is symmetric in its two class arguments. -/
theorem discriminantPairingChar_comm (hL : IsIntegral L) (γ δ : DiscriminantGroup L) :
    hL.discriminantPairingChar γ δ = hL.discriminantPairingChar δ γ := by
  simp only [discriminantPairingChar_apply, TauCeti.IntegralLattice.discriminantPairing_comm]

/-- The zero class gives the trivial character. -/
@[simp]
theorem discriminantPairingChar_zero (hL : IsIntegral L) : hL.discriminantPairingChar 0 = 0 := by
  ext δ
  rw [discriminantPairingChar_comm]
  simp

/-- Every value of the discriminant pairing character has norm one. -/
@[simp]
theorem norm_discriminantPairingChar (hL : IsIntegral L) (γ δ : DiscriminantGroup L) :
    ‖hL.discriminantPairingChar γ δ‖ = 1 := by
  rw [discriminantPairingChar_apply, TauCeti.norm_expCircle]

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
  let f := (L.submoduleOf (dual L)).mkQ.toAddMonoidHom
  let F := fun m : dual L ↦ hL.discriminantPairingChar γ (Submodule.Quotient.mk m) *
    cexp (π * I * (‖(m : E)‖ ^ 2 : ℝ) * τ)
  have hsum : Summable F := (hL.summable_norm_discriminantPairingChar_mul_thetaTerm γ τ).of_norm
  have hfiber (δ : DiscriminantGroup L) :
      ∑' m : (f ⁻¹' {δ} : Set (dual L)), F m =
        hL.discriminantPairingChar γ δ * thetaCosetClass L δ τ := by
    let y : dual L := Quotient.out δ
    have hy : f y = δ := Submodule.Quotient.mk_out δ
    let e := (f.fiberEquivKer y).symm
    have hker (x : dual L) : x ∈ L.submoduleOf (dual L) ↔ x ∈ f.ker := by simp [f]
    let eL := (Submodule.submoduleOfEquivOfLe (isIntegral_iff_le_dual.mp hL)).toEquiv.symm
    let e' : L ≃ (f ⁻¹' {δ} : Set (dual L)) :=
      ((eL.trans (Equiv.subtypeEquivRight hker)).trans e).trans
        (Set.equivOfEq (by rw [hy]))
    -- The inverse of the submodule-of equivalence only inserts the proof of membership in L^∨.
    have heL (v : L) :
        (((Submodule.submoduleOfEquivOfLe (isIntegral_iff_le_dual.mp hL)).symm v : dual L) : E) =
          v := rfl
    have he (v : L) : ((e' v : dual L) : E) = (y : E) + v := by
      simp [e', e, eL, AddMonoidHom.fiberEquivKer_symm_apply, heL]
    have hθ : thetaCosetClass L δ τ = thetaCoset L (y : E) τ := by
      simpa only [y, Submodule.Quotient.mk_out] using congrFun (thetaCosetClass_mk L y) τ
    rw [← e'.tsum_eq, hθ, thetaCoset_apply, ← tsum_mul_left]
    apply tsum_congr
    intro v
    have hv : Submodule.Quotient.mk (e' v : dual L) = δ := (e' v).2
    simp only [F, hv, he]
  have h := hsum.hasSum.tsum_fiberwise f
  rw [funext hfiber] at h
  simpa only [tsum_fintype] using h.tsum_eq.symm

/-- In representative notation, the weighted dual theta sum is the finite sum with coefficients
`e(b_L(γ, δ))`. The positive sign agrees with Mathlib's Fourier transform convention. -/
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
