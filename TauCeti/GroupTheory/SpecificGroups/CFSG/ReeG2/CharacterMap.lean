/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.CharacterMap
public import TauCeti.GroupTheory.SpecificGroups.CFSG.ReeG2.Basic

/-!
# The character map of the represented Ree G₂ Steinberg endomorphism

The independently constructed signed-minor endomorphism and its odd powers act on the
short-root carrier's weight torus through the native G₂ root-datum maps. We express this
comparison in the validated index's own fundamental-weight coordinates, using the same
Bourbaki numbering as its simple root subgroups.

`TauCeti.ReeG2LieIndex.isCharacterMap_steinberg` identifies the pullback with
`TauCeti.SuzukiReeIndex.datumSteinberg.weightMap`. This is a torus compatibility theorem for
the represented carrier, not a comparison with canonical Chevalley–Demazure points.

The computation uses `TauCeti.G2ShortRoot.PrimeField.isCharacterMap_specialIsogeny_pow_odd`
and the native `TauCeti.SuzukiReeIndex.datumSteinberg_weightMap`. The odd-power convention follows
A.-C. Radu, *On the cohomology of the Ree groups and kernels of exceptional isogenies*,
arXiv:2108.06291v2, §2.2.
-/

public section

namespace TauCeti.ReeG2LieIndex

noncomputable section

variable (d : ReeG2LieIndex)

/-- The exceptional point endomorphism and the native special root-datum isogeny have the
same character pullback on the represented weight torus. -/
theorem isCharacterMap_halfFrobenius :
    IsCharacterMap d.weightTorus d.halfFrobenius
      d.toSuzukiReeIndex.datumSpecialIsogeny.weightMap := by
  obtain ⟨m, hvalid, rfl⟩ := d.exists_eq_of
  let := (of m hvalid).algebraZModThree
  rw [halfFrobenius_def, weightTorus_of]
  simp only [toSuzukiReeIndex, SuzukiReeIndex.datumSpecialIsogeny_weightMap_reeG2]
  exact G2ShortRoot.PrimeField.isCharacterMap_specialIsogeny (of m hvalid).1.Closure

/-- The represented Ree G₂ Steinberg endomorphism pulls back characters by the weight map
of the independently defined native datum Steinberg isogeny. -/
theorem isCharacterMap_steinberg :
    IsCharacterMap d.weightTorus d.steinberg
      d.toSuzukiReeIndex.datumSteinberg.weightMap := by
  obtain ⟨m, hvalid, rfl⟩ := d.exists_eq_of
  let := (of m hvalid).algebraZModThree
  rw [steinberg_def, halfFrobenius_def, SuzukiReeIndex.datumSteinberg_weightMap,
    weightTorus_of]
  simp only [toSuzukiReeIndex, SuzukiReeIndex.datumSpecialIsogeny_weightMap_reeG2,
    SuzukiReeIndex.halfExponent_reeG2, ValidLieTypeIndex.fieldExponent,
    LieTypeIndex.fieldExponent_reeG2, ValidLieTypeIndex.characteristic,
    LieTypeIndex.characteristic_reeG2]
  exact G2ShortRoot.PrimeField.isCharacterMap_specialIsogeny_pow_odd (of m hvalid).1.Closure m

end

end TauCeti.ReeG2LieIndex
