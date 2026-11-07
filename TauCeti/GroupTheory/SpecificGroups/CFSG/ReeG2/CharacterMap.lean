/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.CharacterMap
public import TauCeti.GroupTheory.SpecificGroups.CFSG.ReeG2.Basic

/-!
# The Ree G₂ Steinberg character map

For every valid parameter of `²G₂(3^(2m+1))`, the Steinberg endomorphism of the represented
short-root carrier has the character pullback of the independently defined root-datum
Steinberg map `TauCeti.SuzukiReeIndex.datumSteinberg`. The torus is the carrier's actual
weight torus, in the same two fundamental-weight coordinates as the G₂ datum.

The torus parameters are indexed by the rank of the validated index; `weightTorus_apply`
records their identification with the carrier's two coordinates. The result compares the
existing matrix endomorphism with its root-datum counterpart, without claiming an equivalence
between the represented carrier and a canonical Chevalley–Demazure group.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §12.4.
* A.-C. Radu, *On the cohomology of the Ree groups and kernels of exceptional isogenies*,
  arXiv:2108.06291v2, §2.2, for the odd-power construction.
-/

public section

namespace TauCeti.ReeG2LieIndex

noncomputable section

variable (d : ReeG2LieIndex)

/-- The represented Ree G₂ Steinberg map pulls characters back by the native root-datum
Steinberg map, for every valid Ree parameter. The exponent is the recorded `2 * m + 1`,
not the field order `3 ^ (2 * m + 1)`. -/
theorem isCharacterMap_steinberg :
    IsCharacterMap d.weightTorus d.steinberg d.toSuzukiReeIndex.datumSteinberg.weightMap := by
  have h := G2ShortRoot.PrimeField.isCharacterMap_specialIsogeny_pow
    d.1.Closure d.1.fieldExponent
  obtain ⟨m, hm, rfl⟩ := d.exists_eq_of
  -- Both constructions use the recorded odd exponent. Compare their weight maps using
  -- the native special-isogeny square law, without unfolding the sealed datum construction.
  have hdatum : (of m hm).toSuzukiReeIndex.datumSteinberg.weightMap =
      DynkinType.g2SpecialIsogeny.weightMap ^ (of m hm).1.fieldExponent := by
    rw [SuzukiReeIndex.datumSteinberg_weightMap, (of m hm).characteristic_eq_three]
    have hp := RootPairingIsogeny.weightMap_pow_two_mul_add_one _
      DynkinType.g2SpecialIsogeny_mul_self m
    rw [RootPairingIsogeny.weightMap_pow] at hp
    simp only [toSuzukiReeIndex, SuzukiReeIndex.datumSpecialIsogeny_weightMap_reeG2,
      SuzukiReeIndex.halfExponent_reeG2, ValidLieTypeIndex.fieldExponent,
      LieTypeIndex.fieldExponent_reeG2, PNat.val_ofNat, ValidLieTypeIndex.dynkinType,
      LieTypeIndex.dynkinType_reeG2, DynkinType.rank_G2] at hp ⊢
    exact hp.symm
  rw [hdatum, steinberg_def]
  apply isCharacterMap_iff.mpr
  intro s
  rw [weightTorus_apply, weightTorus_apply]
  have hr : finCongr (of m hm).rank_eq_two = Equiv.refl (Fin 2) :=
    Equiv.ext fun i => Fin.ext rfl
  simp only [halfFrobenius_def, hr]
  -- The remaining rank-identification functions are definitionally the identity.
  exact h.map_apply s

end

end TauCeti.ReeG2LieIndex
