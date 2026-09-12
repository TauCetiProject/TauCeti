/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.NormalizedValuation
public import Mathlib.NumberTheory.Padics.LocalField

/-!
# Normalization of the p-adic absolute value

These comparison lemmas let the generic normalized-valuation API interoperate with Mathlib's
concrete p-adic norm and valuation APIs.

## Main results

* `Padic.toAdd_normalizedValuation_eq_valuation` identifies the additive normalized valuation with
  `Padic.valuation`.
* `Padic.natCard_residueField` computes the residue-field cardinality of `ℚ_[p]`.
* `Padic.normalizedAbsoluteValue_eq_nnnorm` identifies the normalized absolute value with
  Mathlib's norm on `ℚ_[p]`.

The Padic and residue-field constructions used here are part of Mathlib's upstream
`NumberTheory/Padics` development.
-/

public section

open ValuativeRel IsNonarchimedeanLocalField
open scoped WithZero

variable (p : ℕ) [Fact p.Prime]

namespace TauCeti

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

end TauCeti

namespace Padic

open TauCeti

/-- The additive normalized valuation on `ℚ_[p]` is Mathlib's p-adic valuation. -/
@[simp]
theorem toAdd_normalizedValuation_eq_valuation (x : ℚ_[p]ˣ) :
    (normalizedValuation ℚ_[p] x).toAdd = (x : ℚ_[p]).valuation := by
  rw [toAdd_normalizedValuation_eq_neg_log, TauCeti.valueGroupWithZeroIsoInt_padic]
  simp [Padic.mulValuation, x.ne_zero]

/-- The residue field of `ℚ_[p]` has cardinality `p`. -/
@[simp]
theorem natCard_residueField :
    @Fintype.card 𝓀[ℚ_[p]] (Fintype.ofFinite 𝓀[ℚ_[p]]) = p := by
  have h : 𝒪[ℚ_[p]] = PadicInt.subring p := by
    ext x
    rw [Valuation.mem_integer_iff, PadicInt.mem_subring_iff]
    rw [(ValuativeRel.isEquiv (ValuativeRel.valuation ℚ_[p]) Padic.mulValuation).le_one_iff_le_one]
    simpa using (not_congr (Padic.norm_lt_norm_iff_mulValuation_lt
      (x := (1 : ℚ_[p])) (y := x))).symm
  let e : 𝒪[ℚ_[p]] ≃+* ℤ_[p] := RingEquiv.subringCongr h
  rw [@Fintype.card_congr _ _ (Fintype.ofFinite 𝓀[ℚ_[p]]) inferInstance
    ((IsLocalRing.ResidueField.mapEquiv e).trans PadicInt.residueField).toEquiv, ZMod.card]

/-- The normalized absolute value on `ℚ_[p]` agrees with Mathlib's norm. -/
@[simp]
theorem normalizedAbsoluteValue_eq_nnnorm (x : ℚ_[p]) :
    normalizedAbsoluteValue ℚ_[p] x = ‖x‖₊ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  apply NNReal.eq
  have hcard : Nat.card 𝓀[ℚ_[p]] = p := by
    rw [@Nat.card_eq_fintype_card _ (Fintype.ofFinite 𝓀[ℚ_[p]])]
    exact natCard_residueField p
  rw [normalizedAbsoluteValue_apply_ne_zero x hx,
    hcard, toAdd_normalizedValuation_eq_valuation]
  simp only [coe_nnnorm]
  simpa using (Padic.norm_eq_zpow_neg_valuation hx).symm

end Padic
