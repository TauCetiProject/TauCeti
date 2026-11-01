/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.RationalModel
public import TauCeti.Analysis.SpecialFunctions.Complex.Circle

/-!
# Complex characters of the discriminant pairing

For an integral full lattice `L`, this file transports
`IntegralLattice.discriminantPairing` through `ZLattice.ratModelDiscriminantGroupEquiv` and
composes it with `TauCeti.expCircle`. The resulting `ZLattice.IsIntegral.discriminantPairingChar`
is the complex additive character `δ ↦ e(b_L(γ, δ))` of the discriminant group. On representatives
`x, y ∈ L^∨`, its value is `exp (2πi ⟪x, y⟫)`. It is symmetric in the two classes and has norm one.
These characters give the coefficients in finite Fourier sums indexed by the discriminant group.

## References

* W. Ebeling, *Lattices and Codes*, 3rd ed., Chapter 2.
-/

public section

open Complex
open scoped Real RealInnerProductSpace

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

end IsIntegral

end ZLattice
