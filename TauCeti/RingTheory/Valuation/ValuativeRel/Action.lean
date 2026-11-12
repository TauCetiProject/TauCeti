/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Action.Invariant
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Topology.Algebra.Valued.ValuativeRel
import TauCeti.RingTheory.DiscreteValuationRing.Uniformizer

/-!
# Group actions preserving the valuation of a valued field

A group acting on a field `L` with a valuative relation and preserving the integer ring `𝒪[L]`
preserves the valuation of every element, as soon as `𝒪[L]` is a discrete valuation ring: the
action carries irreducible elements of `𝒪[L]` to irreducible elements, which are associated to
them, and units have valuation one.

## Main results

* `TauCeti.coe_smul_integer`: the action on `𝒪[L]` read in `L`.
* `TauCeti.valuation_smul`: the action preserves the valuation of every element of `L`.
-/

public section
noncomputable section

open ValuativeRel

namespace TauCeti

section ValuationSMul

variable {L : Type*} [Field L] [ValuativeRel L]
variable {G : Type*} [Group G] [MulSemiringAction G L] [IsInvariantSubring G 𝒪[L]]

/-- The image of an integer of `L` under the action, read in `L`. This is `map_smul` for the
equivariant inclusion `IsInvariantSubring.subtypeHom`. -/
@[simp]
theorem coe_smul_integer (σ : G) (y : 𝒪[L]) : ((σ • y : 𝒪[L]) : L) = σ • (y : L) :=
  map_smul (IsInvariantSubring.subtypeHom G 𝒪[L]) σ y

variable [IsDiscreteValuationRing 𝒪[L]] in
/-- The action preserves the valuation of every integer of `L`. -/
private theorem valuation_smul_integer (σ : G) (x : 𝒪[L]) :
    valuation L (σ • (x : L)) = valuation L (x : L) := by
  have hirr (π : 𝒪[L]) (hπ : Irreducible π) :
      valuation L (σ • (π : L)) = valuation L (π : L) := by
    have hσπ : Irreducible (σ • π) := hπ.map (MulSemiringAction.toRingAut G 𝒪[L] σ)
    obtain ⟨u, hu⟩ : ∃ u : 𝒪[L]ˣ, σ • π * (u : 𝒪[L]) = π :=
      ⟨uniformizerChangeUnit (σ • π) π hσπ hπ, mul_uniformizerChangeUnit (σ • π) π hσπ hπ⟩
    have h := congrArg (fun y : 𝒪[L] ↦ valuation L (y : L)) hu
    have hu1 : valuation L ((u : 𝒪[L]) : L) = 1 :=
      (Valuation.integer.integers (valuation L)).valuation_unit u
    simpa [hu1, coe_smul_integer] using h
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  rcases eq_or_ne x 0 with rfl | h0
  · simp
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hπ
  have hu : valuation L ((σ • (u : 𝒪[L]) : 𝒪[L]) : L) = 1 :=
    (Valuation.integer.integers (valuation L)).one_of_isUnit
      (u.isUnit.map (MulSemiringAction.toRingAut G 𝒪[L] σ))
  have hu' : valuation L ((u : 𝒪[L]) : L) = 1 :=
    (Valuation.integer.integers (valuation L)).valuation_unit u
  rw [← coe_smul_integer, smul_mul', smul_pow']
  simp only [Subring.coe_mul, Subring.coe_pow, map_mul, map_pow, hu, hu', one_mul]
  rw [coe_smul_integer, hirr π hπ]

variable [IsDiscreteValuationRing 𝒪[L]] in
/-- The action preserves the valuation of every element of `L`. -/
@[simp]
theorem valuation_smul (σ : G) (x : L) : valuation L (σ • x) = valuation L x := by
  by_cases hx : valuation L x ≤ 1
  · exact valuation_smul_integer σ ⟨x, hx⟩
  · have hinv : valuation L x⁻¹ ≤ 1 := by
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ (not_le.1 hx).le
    have h := valuation_smul_integer σ ⟨x⁻¹, hinv⟩
    simpa [smul_inv'', map_inv₀] using h

end ValuationSMul

end TauCeti
