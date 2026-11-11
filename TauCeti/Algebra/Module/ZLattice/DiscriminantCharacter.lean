/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Level
public import TauCeti.Analysis.SpecialFunctions.Complex.Circle.Basic

/-!
# Complex characters of the discriminant form

For an integral full lattice `L`, this file transports `IntegralLattice.discriminantPairing`
through `ZLattice.ratModelDiscriminantGroupEquiv` and composes it with `TauCeti.expCircle`. The
resulting `ZLattice.IsIntegral.discriminantPairingChar` is the complex additive character
`δ ↦ e(b_L(γ, δ))` of the discriminant group `A_L = L^∨ ⧸ L`. On representatives `x, y ∈ L^∨`,
its value is `exp (2πi ⟪x, y⟫)`. It is symmetric and additive in the two classes and has norm one.

When `L` is moreover even, transporting `IntegralLattice.discriminantQuadraticMap` through the same
equivalence and composing with `TauCeti.expCircle` gives
`ZLattice.IsEven.discriminantQuadraticChar`, the complex quadratic phase `γ ↦ e(q_L(γ))` on `A_L`.
On a representative `x ∈ L^∨`, its value is `exp (πi ‖x‖²)`. It satisfies the quadratic refinement
law `e(q_L(γ + δ)) = e(q_L(γ)) e(q_L(δ)) e(b_L(γ, δ))`, is even (`e(q_L(-γ)) = e(q_L(γ))`), scales
by `n²` in the exponent on scalar multiples `n • γ`, has `level L` as the least positive exponent
killing all of its values, and gives the eigenvalue by which the modular translation `T : τ ↦ τ + 1`
acts on the coset theta series `θ_γ`.

## Main definitions

* `ZLattice.IsIntegral.discriminantPairingChar`: the additive character `δ ↦ e(b_L(γ, δ))` of
  `DiscriminantGroup L` for an integral full lattice `L`.
* `ZLattice.IsEven.discriminantQuadraticChar`: the quadratic phase `γ ↦ e(q_L(γ))` on
  `DiscriminantGroup L` for an even full lattice `L`.

## Main statements

* `ZLattice.IsIntegral.discriminantPairingChar_mk_mk`: on `x, y ∈ L^∨`,
  `e(b_L(x, y)) = exp (2πi ⟪x, y⟫)`.
* `ZLattice.IsEven.discriminantQuadraticChar_mk`: on `x ∈ L^∨`, `e(q_L(x)) = exp (πi ‖x‖²)`.
* `ZLattice.IsEven.discriminantQuadraticChar_add`:
  `e(q_L(γ + δ)) = e(q_L(γ)) e(q_L(δ)) e(b_L(γ, δ))`.
* `ZLattice.IsEven.discriminantQuadraticChar_nsmul`,
  `ZLattice.IsEven.discriminantQuadraticChar_zsmul`: `e(q_L(n • γ)) = e(q_L(γ))^(n²)`.
* `ZLattice.IsEven.discriminantQuadraticChar_pow_eq_one_iff`: `e(q_L(γ))^n = 1` if and only if
  `n • q_L(γ) = 0`.
* `ZLattice.IsEven.level_dvd_iff_discriminantQuadraticChar_pow_eq_one`,
  `ZLattice.IsEven.discriminantQuadraticChar_pow_level`: `level L ∣ N` if and only if
  `e(q_L(γ))^N = 1` for every `γ : DiscriminantGroup L`.
* `ZLattice.IsEven.cexp_two_pi_mul_I_div_eq_discriminantQuadraticChar_iff`:
  `exp (2πi m / N) = e(q_L(γ))` if and only if `m mod N` maps to `q_L(γ)` under
  `ZMod.toRatAddCircle N`.

## References

* W. Ebeling, *Lattices and Codes*, 3rd ed., Chapter 2.
-/

public section

open Complex ComplexConjugate
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

/-- Addition in the first class argument multiplies the corresponding characters. -/
@[simp]
theorem discriminantPairingChar_add_left (hL : IsIntegral L) (γ δ : DiscriminantGroup L) :
    hL.discriminantPairingChar (γ + δ) =
      hL.discriminantPairingChar γ + hL.discriminantPairingChar δ := by
  ext ε
  rw [AddChar.add_apply, hL.discriminantPairingChar_comm, AddChar.map_add_eq_mul,
    hL.discriminantPairingChar_comm ε γ, hL.discriminantPairingChar_comm ε δ]

/-- Negation in the first class argument negates the corresponding character. -/
@[simp]
theorem discriminantPairingChar_neg_left (hL : IsIntegral L) (γ : DiscriminantGroup L) :
    hL.discriminantPairingChar (-γ) = -hL.discriminantPairingChar γ := by
  ext δ
  simp [discriminantPairingChar_apply]

/-- Every value of the discriminant pairing character has norm one. -/
@[simp]
theorem norm_discriminantPairingChar (hL : IsIntegral L) (γ δ : DiscriminantGroup L) :
    ‖hL.discriminantPairingChar γ δ‖ = 1 := by
  rw [discriminantPairingChar_apply, TauCeti.norm_expCircle]

end IsIntegral

namespace IsEven

/-- The complex quadratic phase `γ ↦ e(q_L(γ))` on the discriminant group of an even full lattice,
obtained by composing `TauCeti.expCircle` with the discriminant quadratic map of its rational
model. -/
noncomputable def discriminantQuadraticChar (hL : IsEven L) (γ : DiscriminantGroup L) : ℂ :=
  TauCeti.expCircle ((ratModel hL.isIntegral).discriminantQuadraticMap
    ((isEven_ratModel_iff hL.isIntegral).mpr hL)
    (ratModelDiscriminantGroupEquiv hL.isIntegral γ))

/-- `discriminantQuadraticChar` is the exponential of the rational-model discriminant quadratic map,
transported across `ratModelDiscriminantGroupEquiv`. -/
theorem discriminantQuadraticChar_apply (hL : IsEven L) (γ : DiscriminantGroup L) :
    hL.discriminantQuadraticChar γ = TauCeti.expCircle
      ((ratModel hL.isIntegral).discriminantQuadraticMap
        ((isEven_ratModel_iff hL.isIntegral).mpr hL)
        (ratModelDiscriminantGroupEquiv hL.isIntegral γ)) := (rfl)

/-- On a representative `x ∈ L^∨`, the quadratic phase `e(q_L(x + L))` is `exp (πi ‖x‖²)`. -/
@[simp]
theorem discriminantQuadraticChar_mk (hL : IsEven L) (x : dual L) :
    hL.discriminantQuadraticChar (Submodule.Quotient.mk x) =
      cexp (π * I * (‖(x : E)‖ ^ 2 : ℝ)) := by
  rw [discriminantQuadraticChar_apply, ratModelDiscriminantGroupEquiv_mk,
    TauCeti.IntegralLattice.discriminantQuadraticMap_mk, TauCeti.expCircle_coe, Rat.cast_div,
    Rat.cast_ofNat, ← Complex.ofReal_ratCast, ratModel_form_ratModelDualEquiv_cast,
    real_inner_self_eq_norm_sq]
  congr 1
  ring

/-- At the zero class of `L^∨ ⧸ L`, the quadratic phase is `1`. -/
@[simp]
theorem discriminantQuadraticChar_zero (hL : IsEven L) :
    hL.discriminantQuadraticChar 0 = 1 := by
  simp [discriminantQuadraticChar_apply]

/-- The quadratic phase is even on the discriminant group: `e(q_L(-γ)) = e(q_L(γ))`. -/
@[simp]
theorem discriminantQuadraticChar_neg (hL : IsEven L) (γ : DiscriminantGroup L) :
    hL.discriminantQuadraticChar (-γ) = hL.discriminantQuadraticChar γ := by
  simp [discriminantQuadraticChar_apply]

/-- **Quadratic refinement.** On the discriminant group of an even full lattice,
`e(q_L(γ + δ)) = e(q_L(γ)) e(q_L(δ)) e(b_L(γ, δ))`. -/
theorem discriminantQuadraticChar_add (hL : IsEven L) (γ δ : DiscriminantGroup L) :
    hL.discriminantQuadraticChar (γ + δ) =
      hL.discriminantQuadraticChar γ * hL.discriminantQuadraticChar δ *
        hL.isIntegral.discriminantPairingChar γ δ := by
  rw [discriminantQuadraticChar_apply, map_add,
    QuadraticMap.map_add ⇑((ratModel hL.isIntegral).discriminantQuadraticMap
      ((isEven_ratModel_iff hL.isIntegral).mpr hL)),
    TauCeti.IntegralLattice.polar_discriminantQuadraticMap, AddChar.map_add_eq_mul,
    AddChar.map_add_eq_mul, ← discriminantQuadraticChar_apply, ← discriminantQuadraticChar_apply,
    ← IsIntegral.discriminantPairingChar_apply]

/-- On differences in the discriminant group,
`e(q_L(γ - δ)) = e(q_L(γ)) e(q_L(δ)) e(b_L(γ, -δ))`. -/
theorem discriminantQuadraticChar_sub (hL : IsEven L) (γ δ : DiscriminantGroup L) :
    hL.discriminantQuadraticChar (γ - δ) =
      hL.discriminantQuadraticChar γ * hL.discriminantQuadraticChar δ *
        hL.isIntegral.discriminantPairingChar γ (-δ) := by
  rw [sub_eq_add_neg, discriminantQuadraticChar_add, discriminantQuadraticChar_neg]

/-- Scaling a discriminant class by `n : ℕ` raises its quadratic phase to the `n²`-th power. -/
theorem discriminantQuadraticChar_nsmul (hL : IsEven L) (n : ℕ) (γ : DiscriminantGroup L) :
    hL.discriminantQuadraticChar (n • γ) = hL.discriminantQuadraticChar γ ^ (n ^ 2) := by
  rw [discriminantQuadraticChar_apply, map_nsmul, QuadraticMap.map_smul_of_tower, ← sq,
    AddChar.map_nsmul_eq_pow, ← discriminantQuadraticChar_apply]

/-- Scaling a discriminant class by `n : ℤ` raises its quadratic phase to the `n²`-th power. -/
theorem discriminantQuadraticChar_zsmul (hL : IsEven L) (n : ℤ) (γ : DiscriminantGroup L) :
    hL.discriminantQuadraticChar (n • γ) = hL.discriminantQuadraticChar γ ^ (n ^ 2) := by
  rcases Int.natAbs_eq n with h | h <;>
    (conv_lhs => rw [h]) <;>
    simp only [natCast_zsmul, neg_smul, discriminantQuadraticChar_neg,
      discriminantQuadraticChar_nsmul, ← zpow_natCast, Nat.cast_pow, Int.natAbs_sq]

/-- Every value of the discriminant quadratic phase has norm one. -/
@[simp]
theorem norm_discriminantQuadraticChar (hL : IsEven L) (γ : DiscriminantGroup L) :
    ‖hL.discriminantQuadraticChar γ‖ = 1 := by
  rw [discriminantQuadraticChar_apply, TauCeti.norm_expCircle]

/-- Every value of the discriminant quadratic phase is nonzero. -/
theorem discriminantQuadraticChar_ne_zero (hL : IsEven L) (γ : DiscriminantGroup L) :
    hL.discriminantQuadraticChar γ ≠ 0 :=
  norm_ne_zero_iff.mp (by simp)

/-- Complex conjugation inverts the discriminant quadratic phase. -/
@[simp]
theorem conj_discriminantQuadraticChar (hL : IsEven L) (γ : DiscriminantGroup L) :
    conj (hL.discriminantQuadraticChar γ) = (hL.discriminantQuadraticChar γ)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [discriminantQuadraticChar_apply, ← TauCeti.expCircle_neg, ← AddChar.map_add_eq_mul,
    add_neg_cancel, AddChar.map_zero_eq_one]

/-- `e(q_L(γ)) = 1` if and only if `q_L(γ) = 0` in `ℚ/ℤ`. -/
theorem discriminantQuadraticChar_eq_one_iff (hL : IsEven L) (γ : DiscriminantGroup L) :
    hL.discriminantQuadraticChar γ = 1 ↔
      (ratModel hL.isIntegral).discriminantQuadraticMap
        ((isEven_ratModel_iff hL.isIntegral).mpr hL)
        (ratModelDiscriminantGroupEquiv hL.isIntegral γ) = 0 :=
  TauCeti.expCircle_eq_one_iff

/-- `e(q_L(γ))^n = 1` if and only if `n` annihilates `q_L(γ)` in `ℚ/ℤ`. -/
theorem discriminantQuadraticChar_pow_eq_one_iff (hL : IsEven L) (γ : DiscriminantGroup L)
    (n : ℕ) :
    hL.discriminantQuadraticChar γ ^ n = 1 ↔
      n • (ratModel hL.isIntegral).discriminantQuadraticMap
        ((isEven_ratModel_iff hL.isIntegral).mpr hL)
        (ratModelDiscriminantGroupEquiv hL.isIntegral γ) = 0 := by
  rw [discriminantQuadraticChar_apply, ← AddChar.map_nsmul_eq_pow, TauCeti.expCircle_eq_one_iff]

/-- For an even full lattice `L`, `level L ∣ N` if and only if `e(q_L(γ)) ^ N = 1` for every
`γ : DiscriminantGroup L`. -/
theorem level_dvd_iff_discriminantQuadraticChar_pow_eq_one (hL : IsEven L) {N : ℕ} :
    level L ∣ N ↔ ∀ γ : DiscriminantGroup L, hL.discriminantQuadraticChar γ ^ N = 1 := by
  simp_rw [hL.level_dvd_iff_discriminantQuadraticMap, hL.discriminantQuadraticChar_pow_eq_one_iff]

/-- The `level L`-th power of every discriminant quadratic phase `e(q_L(γ))` is `1`. -/
@[simp]
theorem discriminantQuadraticChar_pow_level (hL : IsEven L) (γ : DiscriminantGroup L) :
    hL.discriminantQuadraticChar γ ^ level L = 1 :=
  hL.level_dvd_iff_discriminantQuadraticChar_pow_eq_one.mp dvd_rfl γ

/-- The complex phase `exp (2πi m / N)` agrees with `e(q_L(γ))` exactly when the residue of `m`
modulo `N` maps to `q_L(γ)` under `ZMod.toRatAddCircle N`. -/
theorem cexp_two_pi_mul_I_div_eq_discriminantQuadraticChar_iff (hL : IsEven L)
    (γ : DiscriminantGroup L) (N : ℕ) (m : ℤ) :
    cexp (2 * π * I * ((m : ℝ) / N)) = hL.discriminantQuadraticChar γ ↔
      ZMod.toRatAddCircle N (m : ZMod N) =
        (ratModel hL.isIntegral).discriminantQuadraticMap
          ((isEven_ratModel_iff hL.isIntegral).mpr hL)
          (ratModelDiscriminantGroupEquiv hL.isIntegral γ) := by
  have hcast : cexp (2 * π * I * ((m : ℝ) / N)) =
      TauCeti.expCircle (ZMod.toRatAddCircle N (m : ZMod N)) := by
    rw [ZMod.toRatAddCircle_intCast, TauCeti.expCircle_coe]
    push_cast
    rfl
  rw [hcast, discriminantQuadraticChar_apply,
    (AddChar.injective_iff.2 fun _ ↦ TauCeti.expCircle_eq_one_iff.mp).eq_iff]

end IsEven

end ZLattice
