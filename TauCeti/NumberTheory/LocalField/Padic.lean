/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.NormalizedValuation
public import Mathlib.NumberTheory.Padics.LocalField
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Normalization of the p-adic absolute value

The normalized absolute value on `ℚ_[p]` agrees with Mathlib's norm. The proof identifies the
canonical value group with `ℤᵐ⁰`, compares the resulting valuation with Mathlib's bundled
`Padic.mulValuation`, and computes the residue-field cardinality using `PadicInt.residueField`.

## Main results

* `toAdd_normalizedValuation_padic` identifies the additive normalized valuation with
  `Padic.valuation`.
* `natCard_residueField_padic` computes the residue-field cardinality of `ℚ_[p]`.
* `normalizedAbsoluteValue_padic` identifies the normalized absolute value with the norm on
  `ℚ_[p]`.

The Padic and residue-field constructions used here are part of Mathlib's upstream
`NumberTheory/Padics` development.
-/

public section

open ValuativeRel IsNonarchimedeanLocalField
open scoped WithZero

namespace TauCeti

variable (p : ℕ) [Fact p.Prime]

private theorem valueGroupWithZeroIsoInt_padic (x : ℚ_[p]) :
    valueGroupWithZeroIsoInt ℚ_[p] (valuation ℚ_[p] x) = Padic.mulValuation x := by
  let e := valueGroupWithZeroIsoInt ℚ_[p]
  let v := (valuation ℚ_[p]).map e.toMonoidWithZeroHom e.toOrderIso.monotone
  have hv : Function.Surjective v := e.surjective.comp valuation_surjective
  have hw : Function.Surjective (Padic.mulValuation (p := p)) := by
    intro z
    obtain ⟨q, hq⟩ := Rat.surjective_padicValuation p z
    exact ⟨q, by simpa [← Padic.comap_mulValuation_eq_padicValuation] using hq⟩
  exact DFunLike.congr_fun (Valuation.eq_of_isEquiv_of_surjective hv hw
    ((Valuation.isEquiv_map_self_of_strictMono e.toMonoidWithZeroHom e.strictMono).trans
      (ValuativeRel.isEquiv _ _))) x

/-- The additive normalized valuation on `ℚ_[p]` is Mathlib's p-adic valuation. -/
@[simp]
theorem toAdd_normalizedValuation_padic (x : ℚ_[p]ˣ) :
    (normalizedValuation ℚ_[p] x).toAdd = (x : ℚ_[p]).valuation := by
  rw [toAdd_normalizedValuation_eq_neg_log, valueGroupWithZeroIsoInt_padic]
  simp [Padic.mulValuation, x.ne_zero]

/-- The residue field of `ℚ_[p]` has cardinality `p`. -/
@[simp]
theorem natCard_residueField_padic : Nat.card 𝓀[ℚ_[p]] = p := by
  have h : 𝒪[ℚ_[p]] = PadicInt.subring p := by
    ext x
    rw [Valuation.mem_integer_iff, PadicInt.mem_subring_iff]
    rw [(ValuativeRel.isEquiv (valuation ℚ_[p]) Padic.mulValuation).le_one_iff_le_one]
    simpa using (not_congr (Padic.norm_lt_norm_iff_mulValuation_lt
      (x := (1 : ℚ_[p])) (y := x))).symm
  let e : 𝒪[ℚ_[p]] ≃+* ℤ_[p] := RingEquiv.subringCongr h
  rw [Nat.card_congr ((IsLocalRing.ResidueField.mapEquiv e).trans
    PadicInt.residueField).toEquiv, Nat.card_eq_fintype_card, ZMod.card]

/-- The normalized absolute value on `ℚ_[p]` agrees with Mathlib's norm. -/
@[simp]
theorem normalizedAbsoluteValue_padic (x : ℚ_[p]) :
    (normalizedAbsoluteValue ℚ_[p] x : ℝ) = ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [normalizedAbsoluteValue_apply_ne_zero x hx, natCard_residueField_padic,
    toAdd_normalizedValuation_padic, Padic.norm_eq_zpow_neg_valuation hx]
  simp

end TauCeti
