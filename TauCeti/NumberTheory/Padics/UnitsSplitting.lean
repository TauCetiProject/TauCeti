/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.NumberTheory.LocalField.Padic
public import TauCeti.NumberTheory.LocalField.UnitsDecomposition
public import TauCeti.NumberTheory.Padics.UnitsCharacter

/-!
# Canonical splitting of `ℚ_pˣ`

Using the canonical uniformizer `p` (`TauCeti.padicPrimeUnit p`), the multiplicative group
`ℚ_[p]ˣ` splits topologically as `Multiplicative ℤ × ℤ_[p]ˣ` via
`x ↦ (v_p(x), x · p^{-v_p(x)})` (`TauCeti.padicUnitsEquivIntProd p`), with inverse
`(n, u) ↦ p ^ n * u`.

## Main definitions

* `TauCeti.unitFiltrationZeroPadicEquiv`: the topological group isomorphism
  `unitFiltration ℚ_[p] 0 ≃ₜ* ℤ_[p]ˣ`.
* `TauCeti.padicUnitsEquivIntProd`: the canonical splitting
  `ℚ_[p]ˣ ≃ₜ* Multiplicative ℤ × ℤ_[p]ˣ`.

## Main results

* `TauCeti.padicUnitsEquivIntProd_apply_snd`: the `ℤ_[p]ˣ`-component of `padicUnitsEquivIntProd p`
  is `TauCeti.padicUnitPart p`.
* `TauCeti.padicUnitsEquivIntProd_eq_of_decomposition`: if `x = p ^ k * w` with `w ∈ ℤ_[p]ˣ`, then
  `padicUnitsEquivIntProd p x = (.ofAdd k, w)`.
* `TauCeti.eq_padicPrimeUnit_zpow_mul_padicUnitPart`: every `x : ℚ_[p]ˣ` factors as
  `p ^ v_p(x) * u` with `u = padicUnitPart p x`.
-/

public section

noncomputable section

open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

section Splitting

variable (p : ℕ) [Fact p.Prime]

/-- `padicIntUnitsInclusion p` is injective. -/
theorem padicIntUnitsInclusion_injective : Function.Injective (padicIntUnitsInclusion p) :=
  fun _ _ h ↦ Units.ext <| PadicInt.ext <| by
    simpa [coe_padicIntUnitsInclusion_apply] using congrArg (fun x : ℚ_[p]ˣ ↦ (x : ℚ_[p])) h

/-- Every unit of `ℤ_[p]` has valuation zero in `ℚ_[p]`. -/
theorem valuation_padicIntUnitsInclusion (u : ℤ_[p]ˣ) :
    ((padicIntUnitsInclusion p u : ℚ_[p]).valuation) = 0 := by
  rw [← _root_.Padic.toAdd_normalizedValuation_eq_valuation,
    _root_.Padic.toAdd_normalizedValuation_eq_zero_of_coe_eq (coe_padicIntUnitsInclusion_apply u)]

/-- Every unit of `ℤ_[p]` has normalized valuation `1` in `ℚ_[p]`. -/
@[simp]
theorem normalizedValuation_padicIntUnitsInclusion (u : ℤ_[p]ˣ) :
    normalizedValuation ℚ_[p] (padicIntUnitsInclusion p u) = 1 :=
  Multiplicative.toAdd.injective <| by
    rw [_root_.Padic.toAdd_normalizedValuation_eq_zero_of_coe_eq
      (coe_padicIntUnitsInclusion_apply u), toAdd_one]

/-- Every unit of `ℤ_[p]` lies in the depth-zero unit filtration `U(ℚ_[p], 0)`. -/
theorem padicIntUnitsInclusion_mem_unitFiltration_zero (u : ℤ_[p]ˣ) :
    padicIntUnitsInclusion p u ∈ unitFiltration ℚ_[p] 0 := by
  rw [← ker_normalizedValuation, MonoidHom.mem_ker, normalizedValuation_padicIntUnitsInclusion]

/-- Underlying algebraic isomorphism `U(ℚ_[p], 0) ≃* ℤ_[p]ˣ`. -/
private def unitFiltrationZeroPadicMulEquiv : unitFiltration ℚ_[p] 0 ≃* ℤ_[p]ˣ :=
  (unitFiltrationZeroEquivIntegerUnits (K := ℚ_[p])).trans
    (Units.mapEquiv (_root_.Padic.integerRingEquiv p).toMulEquiv)

private theorem unitFiltrationZeroPadicMulEquiv_symm_apply (u : ℤ_[p]ˣ) :
    (unitFiltrationZeroPadicMulEquiv p).symm u =
      ⟨padicIntUnitsInclusion p u, padicIntUnitsInclusion_mem_unitFiltration_zero p u⟩ :=
  Subtype.ext <| Units.ext <| by
    -- Unfold the composition defining `unitFiltrationZeroPadicMulEquiv` on the inverse direction.
    change (((unitFiltrationZeroEquivIntegerUnits (K := ℚ_[p])).symm
      (Units.map (_root_.Padic.integerRingEquiv p).symm.toMonoidHom u) :
        unitFiltration ℚ_[p] 0) : ℚ_[p]ˣ) = (padicIntUnitsInclusion p u : ℚ_[p])
    rw [coe_unitFiltrationZeroEquivIntegerUnits_symm, coe_padicIntUnitsInclusion_apply]
    exact _root_.Padic.coe_integerRingEquiv_symm_apply p (u : ℤ_[p])

/-- The depth-zero unit filtration `U(ℚ_[p], 0)` is topologically isomorphic to `ℤ_[p]ˣ`. -/
def unitFiltrationZeroPadicEquiv : unitFiltration ℚ_[p] 0 ≃ₜ* ℤ_[p]ˣ :=
  let e := unitFiltrationZeroPadicMulEquiv p
  have hinv : Continuous e.symm :=
    ((padicIntUnitsInclusion p).continuous.subtype_mk _).congr fun u ↦
      (unitFiltrationZeroPadicMulEquiv_symm_apply p u).symm
  ContinuousMulEquiv.mk e (hinv.continuous_symm_of_equiv_compact_to_t2 (f := e.symm.toEquiv)) hinv

/-- `unitFiltrationZeroPadicEquiv p` preserves the underlying `p`-adic number. -/
@[simp]
theorem coe_unitFiltrationZeroPadicEquiv_apply (u : unitFiltration ℚ_[p] 0) :
    ((unitFiltrationZeroPadicEquiv p u : ℤ_[p]) : ℚ_[p]) = ((u : ℚ_[p]ˣ) : ℚ_[p]) := by
  -- Unfold `unitFiltrationZeroPadicEquiv` into
  -- `integerRingEquiv ∘ unitFiltrationZeroEquivIntegerUnits`.
  change ((_root_.Padic.integerRingEquiv p
    (unitFiltrationZeroEquivIntegerUnits (K := ℚ_[p]) u : 𝒪[ℚ_[p]]) : ℤ_[p]) : ℚ_[p]) = _
  rw [_root_.Padic.coe_integerRingEquiv_apply, coe_unitFiltrationZeroEquivIntegerUnits]

/-- The inverse of `unitFiltrationZeroPadicEquiv p` is `padicIntUnitsInclusion p` into
`U(ℚ_[p], 0)`. -/
@[simp]
theorem coe_unitFiltrationZeroPadicEquiv_symm_apply (u : ℤ_[p]ˣ) :
    ((unitFiltrationZeroPadicEquiv p).symm u : ℚ_[p]ˣ) = padicIntUnitsInclusion p u :=
  congrArg Subtype.val (unitFiltrationZeroPadicMulEquiv_symm_apply p u)

/-- **The canonical splitting `ℚ_[p]ˣ ≃ₜ* Multiplicative ℤ × ℤ_[p]ˣ`.** It sends
`x` to `(v_p(x), x · p^{-v_p(x)})`, with inverse `(n, u) ↦ p ^ n * u`. -/
def padicUnitsEquivIntProd : ℚ_[p]ˣ ≃ₜ* Multiplicative ℤ × ℤ_[p]ˣ :=
  let e₁ := unitsEquivIntProd ℚ_[p] (padicPrimeUnit p) (normalizedValuation_padicPrimeUnit p)
  let e₂ := unitFiltrationZeroPadicEquiv p
  e₁.trans
    { toMulEquiv := MulEquiv.prodCongr (MulEquiv.refl (Multiplicative ℤ)) e₂.toMulEquiv
      continuous_toFun := continuous_fst.prodMk (e₂.continuous.comp continuous_snd)
      continuous_invFun := continuous_fst.prodMk (e₂.symm.continuous.comp continuous_snd) }

/-- The `ℤ`-component of `padicUnitsEquivIntProd p` is the `p`-adic valuation. -/
@[simp]
theorem padicUnitsEquivIntProd_apply_fst (x : ℚ_[p]ˣ) :
    (padicUnitsEquivIntProd p x).1 = .ofAdd (x : ℚ_[p]).valuation :=
  Multiplicative.toAdd.injective <| by
    -- Project onto the first factor of the composite equivalence `padicUnitsEquivIntProd`.
    change (unitsEquivIntProd ℚ_[p] (padicPrimeUnit p)
      (normalizedValuation_padicPrimeUnit p) x).1.toAdd = _
    simp

/-- The `ℤ_[p]ˣ`-component of `padicUnitsEquivIntProd p` has underlying `p`-adic number
`x · p ^ (-v_p(x))`. -/
theorem coe_padicUnitsEquivIntProd_apply_snd (x : ℚ_[p]ˣ) :
    (((padicUnitsEquivIntProd p x).2 : ℤ_[p]) : ℚ_[p]) =
      (x : ℚ_[p]) * (p : ℚ_[p]) ^ (-(x : ℚ_[p]).valuation) := by
  -- Project onto the second factor of the composite equivalence `padicUnitsEquivIntProd`.
  change ((unitFiltrationZeroPadicEquiv p (unitsEquivIntProd ℚ_[p] (padicPrimeUnit p)
    (normalizedValuation_padicPrimeUnit p) x).2 : ℤ_[p]) : ℚ_[p]) = _
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
  -- Unfold the inverse of the composite equivalence `padicUnitsEquivIntProd`.
  change (unitsEquivIntProd ℚ_[p] (padicPrimeUnit p)
    (normalizedValuation_padicPrimeUnit p)).symm
    (z.1, (unitFiltrationZeroPadicEquiv p).symm z.2) = _
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

/-- Every `x : ℚ_[p]ˣ` factors as `p ^ v_p(x) * u` with `u = padicUnitPart p x`. -/
theorem eq_padicPrimeUnit_zpow_mul_padicUnitPart (x : ℚ_[p]ˣ) :
    x = padicPrimeUnit p ^ (x : ℚ_[p]).valuation *
      padicIntUnitsInclusion p (padicUnitPart p x) :=
  Units.ext <| by simpa using coe_eq_zpow_valuation_mul_padicUnitPart x

end Splitting

end TauCeti
