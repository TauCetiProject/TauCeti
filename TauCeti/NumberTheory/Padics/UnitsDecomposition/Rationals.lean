/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.NumberTheory.LocalField.Padic
public import TauCeti.NumberTheory.LocalField.Units.Decomposition
public import TauCeti.NumberTheory.Padics.UnitsCharacter.Basic

/-!
# Canonical splitting of `ℚ_pˣ`

Using the canonical uniformizer `p` (`TauCeti.padicPrimeUnit p`), the multiplicative group
`ℚ_[p]ˣ` splits topologically as `Multiplicative ℤ × ℤ_[p]ˣ` via
`x ↦ (v_p(x), x · p^{-v_p(x)})` (`TauCeti.padicUnitsEquivIntProd p`), with inverse
`(n, u) ↦ p ^ n * u`. This specializes the local-field splitting `TauCeti.unitsEquivIntProd`
and identifies `unitFiltration ℚ_[p] 0` with `ℤ_[p]ˣ` via
`TauCeti.unitFiltrationZeroEquivIntegerUnits`.

## Main definitions

* `TauCeti.unitFiltrationZeroPadicEquiv`: the topological group isomorphism
  `unitFiltration ℚ_[p] 0 ≃ₜ* ℤ_[p]ˣ`, specializing `TauCeti.unitFiltrationZeroEquivIntegerUnits`.
* `TauCeti.padicUnitsEquivIntProd`: the canonical splitting
  `ℚ_[p]ˣ ≃ₜ* Multiplicative ℤ × ℤ_[p]ˣ`, specializing `TauCeti.unitsEquivIntProd`.

## Main results

* `TauCeti.padicUnitsEquivIntProd_apply_snd`: the `ℤ_[p]ˣ`-component of `padicUnitsEquivIntProd p`
  is `TauCeti.padicUnitPart p`.
* `TauCeti.padicUnitsEquivIntProd_eq_of_decomposition`: if `x = p ^ k * w` with `w ∈ ℤ_[p]ˣ`, then
  `padicUnitsEquivIntProd p x = (.ofAdd k, w)`.
-/

public section

noncomputable section

open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

section Splitting

variable (p : ℕ) [Fact p.Prime]

/-- Underlying algebraic isomorphism `U(ℚ_[p], 0) ≃* ℤ_[p]ˣ`. -/
private def unitFiltrationZeroPadicMulEquiv : unitFiltration ℚ_[p] 0 ≃* ℤ_[p]ˣ :=
  (unitFiltrationZeroEquivIntegerUnits (K := ℚ_[p])).trans
    (Units.mapEquiv (_root_.Padic.integerRingEquiv p).toMulEquiv)

private theorem unitFiltrationZeroPadicMulEquiv_apply (u : unitFiltration ℚ_[p] 0) :
    unitFiltrationZeroPadicMulEquiv p u =
      Units.mapEquiv (_root_.Padic.integerRingEquiv p).toMulEquiv
        (unitFiltrationZeroEquivIntegerUnits (K := ℚ_[p]) u) :=
  MulEquiv.trans_apply _ _ u

private theorem unitFiltrationZeroPadicMulEquiv_symm_apply (u : ℤ_[p]ˣ) :
    (unitFiltrationZeroPadicMulEquiv p).symm u =
      ⟨padicIntUnitsInclusion p u, padicIntUnitsInclusion_mem_unitFiltration_zero u⟩ :=
  Subtype.ext <| Units.ext <| by
    rw [unitFiltrationZeroPadicMulEquiv, MulEquiv.symm_trans_apply, Units.mapEquiv_symm,
      coe_unitFiltrationZeroEquivIntegerUnits_symm, Units.coe_mapEquiv,
      coe_padicIntUnitsInclusion_apply]
    exact _root_.Padic.coe_integerRingEquiv_symm_apply p (u : ℤ_[p])

/-- The depth-zero unit filtration `U(ℚ_[p], 0)` is topologically isomorphic to `ℤ_[p]ˣ`,
specializing and refining `TauCeti.unitFiltrationZeroEquivIntegerUnits` along
`Padic.integerRingEquiv`. -/
def unitFiltrationZeroPadicEquiv : unitFiltration ℚ_[p] 0 ≃ₜ* ℤ_[p]ˣ :=
  let e := unitFiltrationZeroPadicMulEquiv p
  have hinv : Continuous e.symm :=
    ((padicIntUnitsInclusion p).continuous.subtype_mk _).congr fun u ↦
      (unitFiltrationZeroPadicMulEquiv_symm_apply p u).symm
  ContinuousMulEquiv.mk e (hinv.continuous_symm_of_equiv_compact_to_t2 (f := e.symm.toEquiv)) hinv

private theorem unitFiltrationZeroPadicEquiv_apply (u : unitFiltration ℚ_[p] 0) :
    unitFiltrationZeroPadicEquiv p u = unitFiltrationZeroPadicMulEquiv p u :=
  (rfl)

/-- `unitFiltrationZeroPadicEquiv p` preserves the underlying `p`-adic number. -/
@[simp]
theorem coe_unitFiltrationZeroPadicEquiv_apply (u : unitFiltration ℚ_[p] 0) :
    ((unitFiltrationZeroPadicEquiv p u : ℤ_[p]) : ℚ_[p]) = ((u : ℚ_[p]ˣ) : ℚ_[p]) := by
  rw [unitFiltrationZeroPadicEquiv_apply, unitFiltrationZeroPadicMulEquiv_apply, Units.coe_mapEquiv]
  exact (_root_.Padic.coe_integerRingEquiv_apply p _).trans
    (coe_unitFiltrationZeroEquivIntegerUnits u)

/-- The inverse of `unitFiltrationZeroPadicEquiv p` is `padicIntUnitsInclusion p` into
`U(ℚ_[p], 0)`. -/
@[simp]
theorem coe_unitFiltrationZeroPadicEquiv_symm_apply (u : ℤ_[p]ˣ) :
    ((unitFiltrationZeroPadicEquiv p).symm u : ℚ_[p]ˣ) = padicIntUnitsInclusion p u :=
  congrArg Subtype.val (unitFiltrationZeroPadicMulEquiv_symm_apply p u)

/-- Topological product equivalence transferring the second factor from `U(ℚ_[p], 0)` to
`ℤ_[p]ˣ`. -/
private def prodUnitFiltrationEquiv :
    Multiplicative ℤ × unitFiltration ℚ_[p] 0 ≃ₜ* Multiplicative ℤ × ℤ_[p]ˣ where
  toMulEquiv := MulEquiv.prodCongr (MulEquiv.refl (Multiplicative ℤ))
    (unitFiltrationZeroPadicEquiv p).toMulEquiv
  continuous_toFun := continuous_fst.prodMk
    ((unitFiltrationZeroPadicEquiv p).continuous.comp continuous_snd)
  continuous_invFun := continuous_fst.prodMk
    ((unitFiltrationZeroPadicEquiv p).symm.continuous.comp continuous_snd)

private theorem prodUnitFiltrationEquiv_apply (z : Multiplicative ℤ × unitFiltration ℚ_[p] 0) :
    prodUnitFiltrationEquiv p z = (z.1, unitFiltrationZeroPadicEquiv p z.2) :=
  (rfl)

private theorem prodUnitFiltrationEquiv_symm_apply (z : Multiplicative ℤ × ℤ_[p]ˣ) :
    (prodUnitFiltrationEquiv p).symm z = (z.1, (unitFiltrationZeroPadicEquiv p).symm z.2) :=
  (rfl)

/-- **The canonical splitting `ℚ_[p]ˣ ≃ₜ* Multiplicative ℤ × ℤ_[p]ˣ`.** It specializes
`TauCeti.unitsEquivIntProd` at `p`, sending `x` to `(v_p(x), x · p^{-v_p(x)})`, with inverse
`(n, u) ↦ p ^ n * u`. -/
def padicUnitsEquivIntProd : ℚ_[p]ˣ ≃ₜ* Multiplicative ℤ × ℤ_[p]ˣ :=
  (unitsEquivIntProd ℚ_[p] (padicPrimeUnit p) (normalizedValuation_padicPrimeUnit p)).trans
    (prodUnitFiltrationEquiv p)

/-- The `ℤ`-component of `padicUnitsEquivIntProd p` is the `p`-adic valuation. -/
@[simp]
theorem padicUnitsEquivIntProd_apply_fst (x : ℚ_[p]ˣ) :
    (padicUnitsEquivIntProd p x).1 = .ofAdd (x : ℚ_[p]).valuation :=
  Multiplicative.toAdd.injective <| by
    rw [padicUnitsEquivIntProd, ContinuousMulEquiv.trans_apply, prodUnitFiltrationEquiv_apply]
    simp

/-- The `ℤ_[p]ˣ`-component of `padicUnitsEquivIntProd p` has underlying `p`-adic number
`x · p ^ (-v_p(x))`. -/
theorem coe_padicUnitsEquivIntProd_apply_snd (x : ℚ_[p]ˣ) :
    (((padicUnitsEquivIntProd p x).2 : ℤ_[p]) : ℚ_[p]) =
      (x : ℚ_[p]) * (p : ℚ_[p]) ^ (-(x : ℚ_[p]).valuation) := by
  rw [padicUnitsEquivIntProd, ContinuousMulEquiv.trans_apply, prodUnitFiltrationEquiv_apply]
  simp

/-- The `ℤ_[p]ˣ`-component of `padicUnitsEquivIntProd p` is `TauCeti.padicUnitPart p`. -/
@[simp]
theorem padicUnitsEquivIntProd_apply_snd (x : ℚ_[p]ˣ) :
    (padicUnitsEquivIntProd p x).2 = padicUnitPart p x :=
  Units.ext <| PadicInt.ext <| by
    rw [coe_padicUnitsEquivIntProd_apply_snd, coe_padicUnitPart_apply]

/-- The inverse of `padicUnitsEquivIntProd p` sends `(n, u)` to `p ^ n * u`. -/
@[simp]
theorem padicUnitsEquivIntProd_symm_apply (z : Multiplicative ℤ × ℤ_[p]ˣ) :
    (padicUnitsEquivIntProd p).symm z =
      padicPrimeUnit p ^ z.1.toAdd * padicIntUnitsInclusion p z.2 := by
  rw [padicUnitsEquivIntProd, ContinuousMulEquiv.symm_trans_apply,
    prodUnitFiltrationEquiv_symm_apply]
  simp

/-- If `x : ℚ_[p]ˣ` factors as `p ^ k * w` with `w ∈ ℤ_[p]ˣ`, then
`padicUnitsEquivIntProd p x = (.ofAdd k, w)`. -/
theorem padicUnitsEquivIntProd_eq_of_decomposition (x : ℚ_[p]ˣ) (k : ℤ) (w : ℤ_[p]ˣ)
    (hx : (x : ℚ_[p]) = (p : ℚ_[p]) ^ k * ((w : ℤ_[p]) : ℚ_[p])) :
    padicUnitsEquivIntProd p x = (.ofAdd k, w) := by
  rw [← (padicUnitsEquivIntProd p).apply_symm_apply (.ofAdd k, w)]
  congr 1
  apply Units.ext
  simpa [padicUnitsEquivIntProd_symm_apply] using hx

/-- `padicUnitsEquivIntProd p` sends `p` to `(1, 1)`. -/
@[simp]
theorem padicUnitsEquivIntProd_padicPrimeUnit :
    padicUnitsEquivIntProd p (padicPrimeUnit p) = (.ofAdd 1, 1) := by
  rw [← (padicUnitsEquivIntProd p).apply_symm_apply (.ofAdd 1, 1)]
  simp

/-- `padicUnitsEquivIntProd p` sends a unit `u ∈ ℤ_[p]ˣ` to `(0, u)`. -/
@[simp]
theorem padicUnitsEquivIntProd_padicIntUnitsInclusion (u : ℤ_[p]ˣ) :
    padicUnitsEquivIntProd p (padicIntUnitsInclusion p u) = (1, u) := by
  rw [← (padicUnitsEquivIntProd p).apply_symm_apply (1, u)]
  simp

end Splitting

end TauCeti
