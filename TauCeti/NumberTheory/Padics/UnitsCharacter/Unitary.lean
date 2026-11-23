/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.UnitsCharacter.Coefficients
public import TauCeti.Topology.Algebra.ValuativeRel.ContinuousRingHom
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic

/-!
# Unitary continuous characters of `ℚ_pˣ`

A continuous character `δ : ℚ_[p]ˣ →ₜ* Lˣ` with values in a valuated field `L` is **unitary**
(`TauCeti.PadicUnitsChar.IsUnitary`) when `valuation L (δ (padicPrimeUnit p) : L) = 1`. When `L`
is a nonarchimedean local field, every continuous character automatically maps `ℤ_[p]ˣ` into
units of valuation `1` (`TauCeti.PadicUnitsChar.valuation_apply_padicIntUnitsInclusion_eq_one`),
so `δ` is unitary if and only if `valuation L (δ x : L) = 1` for all `x ∈ ℚ_[p]ˣ`
(`TauCeti.PadicUnitsChar.isUnitary_iff_forall_valuation_eq_one`).

On the other hand, the algebra-map character `padicAlgebraMapChar p L h` into any nonarchimedean
local field `L` equipped with a continuous `ℚ_[p]`-algebra structure is not unitary
(`TauCeti.not_isUnitary_padicAlgebraMapChar`), because `valuation L (p : L) < 1`.

## Main definitions

* `TauCeti.PadicUnitsChar.IsUnitary`: unitarity predicate
  `valuation L (δ (padicPrimeUnit p) : L) = 1`.

## Main results

* `TauCeti.PadicUnitsChar.isUnitary_iff_valuation_padicPrimeUnit_eq_one`,
  `TauCeti.PadicUnitsChar.isUnitary_one`, `TauCeti.PadicUnitsChar.isUnitary_mul`,
  `TauCeti.PadicUnitsChar.isUnitary_inv`: basic properties of unitary characters.
* `TauCeti.PadicUnitsChar.valuation_apply_padicIntUnitsInclusion_eq_one`: `δ(ℤ_[p]ˣ)` has
  valuation `1` in any nonarchimedean local field.
* `TauCeti.PadicUnitsChar.isUnitary_iff_forall_valuation_eq_one`: characterization of unitarity on
  all of `ℚ_[p]ˣ`.
* `TauCeti.not_isUnitary_padicAlgebraMapChar`: `x ↦ algebraMap ℚ_[p] L x` is not unitary.
-/

public section

noncomputable section

open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

section UnitaryBasic

variable {p : ℕ} [Fact p.Prime]
variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]

/-- A continuous character `δ : ℚ_[p]ˣ →ₜ* Lˣ` with values in a valuated field `L` is
**unitary** if `v_L(δ(p)) = 1`. When `L` is a nonarchimedean local field, `δ(ℤ_[p]ˣ)`
automatically lies in `U(L, 0)`, so this is equivalent to `v_L(δ(x)) = 1` for all `x ∈ ℚ_[p]ˣ`
(`isUnitary_iff_forall_valuation_eq_one`). -/
def PadicUnitsChar.IsUnitary (δ : PadicUnitsChar p L) : Prop :=
  valuation L (δ (padicPrimeUnit p) : L) = 1

/-- Unfolding `δ.IsUnitary` as `valuation L (δ (padicPrimeUnit p) : L) = 1`. -/
theorem PadicUnitsChar.isUnitary_iff_valuation_padicPrimeUnit_eq_one (δ : PadicUnitsChar p L) :
    δ.IsUnitary ↔ valuation L (δ (padicPrimeUnit p) : L) = 1 :=
  Iff.rfl

/-- The trivial character is unitary. -/
@[simp]
theorem PadicUnitsChar.isUnitary_one : (1 : PadicUnitsChar p L).IsUnitary := by
  simp [IsUnitary]

/-- The product of two unitary characters is unitary. -/
theorem PadicUnitsChar.isUnitary_mul [ContinuousMul L] {δ₁ δ₂ : PadicUnitsChar p L}
    (h₁ : δ₁.IsUnitary) (h₂ : δ₂.IsUnitary) : (δ₁ * δ₂).IsUnitary := by
  simp only [IsUnitary, ContinuousMonoidHom.mul_apply, Units.val_mul, map_mul]
  rw [h₁, h₂, mul_one]

/-- The inverse of a unitary character is unitary. -/
theorem PadicUnitsChar.isUnitary_inv [ContinuousMul L] {δ : PadicUnitsChar p L}
    (h : δ.IsUnitary) : δ⁻¹.IsUnitary := by
  have hmul : valuation L (δ (padicPrimeUnit p) : L) *
      valuation L ((δ⁻¹ (padicPrimeUnit p) : Lˣ) : L) = 1 := by
    rw [← map_mul]
    have : (δ (padicPrimeUnit p) : L) * ((δ⁻¹ (padicPrimeUnit p) : Lˣ) : L) = 1 :=
      Units.mul_inv _
    rw [this, map_one]
  rw [PadicUnitsChar.IsUnitary] at h ⊢
  rwa [h, one_mul] at hmul

end UnitaryBasic

section UnitaryLocalField

variable {p : ℕ} [Fact p.Prime]
variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]

/-- Every continuous character `δ : ℚ_[p]ˣ →ₜ* Lˣ` into a nonarchimedean local field `L` sends
all of `ℤ_[p]ˣ` into units of valuation `1`. -/
@[simp]
theorem PadicUnitsChar.valuation_apply_padicIntUnitsInclusion_eq_one (δ : PadicUnitsChar p L)
    (u : ℤ_[p]ˣ) :
    valuation L (δ (padicIntUnitsInclusion p u) : L) = 1 := by
  let f : ℤ_[p]ˣ →ₜ* Multiplicative ℤ :=
    ⟨(normalizedValuation L).comp δ.toWeight.toMonoidHom,
      (continuous_normalizedValuation L).comp δ.toWeight.continuous⟩
  have hf : f = 1 := ContinuousMonoidHom.eq_one_of_isMulTorsionFree f
  have hval : normalizedValuation L (δ (padicIntUnitsInclusion p u)) = 1 := by
    simpa [f, PadicUnitsChar.toWeight_apply] using DFunLike.congr_fun hf u
  exact (normalizedValuation_eq_one_iff _).mp hval

/-- `δ : ℚ_[p]ˣ →ₜ* Lˣ` is unitary if and only if every value `δ(x)` has valuation `1` in `L`. -/
theorem PadicUnitsChar.isUnitary_iff_forall_valuation_eq_one (δ : PadicUnitsChar p L) :
    δ.IsUnitary ↔ ∀ x : ℚ_[p]ˣ, valuation L (δ x : L) = 1 := by
  refine ⟨fun h x ↦ ?_, fun h ↦ h (padicPrimeUnit p)⟩
  rw [eq_padicPrimeUnit_zpow_mul_padicUnitPart p x, map_mul, map_zpow, Units.val_mul,
    Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, h, one_zpow, one_mul,
    δ.valuation_apply_padicIntUnitsInclusion_eq_one]

/-- The character `x ↦ algebraMap ℚ_[p] L x` into any nonarchimedean local field `L` with a
continuous `ℚ_[p]`-algebra structure (including `ℚ_[p]` itself and its finite extensions) is not
unitary, because `v_L(p) < 1`. -/
theorem not_isUnitary_padicAlgebraMapChar (p : ℕ) [Fact p.Prime] (L : Type*) [Field L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra ℚ_[p] L]
    (h : Continuous (algebraMap ℚ_[p] L)) :
    ¬ (padicAlgebraMapChar p L h).IsUnitary := by
  rw [PadicUnitsChar.IsUnitary, coe_padicAlgebraMapChar_padicPrimeUnit]
  have : ValuativeExtension ℚ_[p] L := ValuativeExtension.of_continuous_algebraMap h
  have hlt : valuation L (p : L) < 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] L) p, ValuativeExtension.valuation_algebraMap_lt_one_iff]
    exact Valuation.integer.v_irreducible_lt_one (TauCeti.Padic.irreducible_natCast_self p)
  exact hlt.ne

end UnitaryLocalField

end TauCeti
