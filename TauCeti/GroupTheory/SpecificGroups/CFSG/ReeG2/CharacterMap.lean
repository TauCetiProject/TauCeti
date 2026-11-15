/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.CharacterMap
public import TauCeti.GroupTheory.SpecificGroups.CFSG.ReeG2.Basic

/-!
# The Ree G₂ exceptional and Steinberg character maps

For every valid parameter of `²G₂(3^(2m+1))`, the exceptional and Steinberg endomorphisms of the
represented short-root carrier have the character pullbacks of the independently defined
root-datum maps `TauCeti.SuzukiReeIndex.datumSpecialIsogeny` and
`TauCeti.SuzukiReeIndex.datumSteinberg`. The torus is the carrier's actual
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

private theorem weightTorus_torusPointMap_datumSpecialIsogeny
    (s : Fin d.1.rank → d.1.Closureˣ) :
    d.weightTorus (torusPointMap d.toSuzukiReeIndex.datumSpecialIsogeny.weightMap s) =
      G2ShortRoot.PrimeField.weightTorusPoints d.1.Closure
        (torusPointMap DynkinType.g2SpecialIsogeny.weightMap
          (fun i => s ((finCongr d.rank_eq_two).symm i))) := by
  obtain ⟨m, hm, rfl⟩ := d.exists_eq_of
  -- For the constructor `of`, the recorded diagram is G₂ and its rank is 2.
  -- Its inverse rank identification preserves each numbered coordinate.
  have hr (i : Fin 2) : (finCongr (of m hm).rank_eq_two).symm i = i :=
    Fin.ext rfl
  rw [weightTorus_apply]
  simp only [toSuzukiReeIndex, SuzukiReeIndex.datumSpecialIsogeny_weightMap_reeG2, hr]
  -- Both sides now apply the same G₂ torus-point map: `toSuzukiReeIndex` keeps the
  -- underlying validated index, hence its `Closure`, and the remaining rank reindexing
  -- reduces to the identity on `Fin 2` for `of m hm`.
  rfl

/-- The represented Ree G₂ half-Frobenius pulls characters back by the native exceptional
root-datum isogeny, in the validated index's fundamental-weight coordinates. -/
theorem isCharacterMap_halfFrobenius :
    IsCharacterMap d.weightTorus d.halfFrobenius
      d.toSuzukiReeIndex.datumSpecialIsogeny.weightMap := by
  apply isCharacterMap_iff.mpr
  intro s
  rw [weightTorus_torusPointMap_datumSpecialIsogeny, weightTorus_apply, halfFrobenius_def]
  exact (G2ShortRoot.PrimeField.isCharacterMap_specialIsogeny d.1.Closure).map_apply _

/-- The represented Ree G₂ Steinberg map pulls characters back by the native root-datum
Steinberg map, for every valid Ree parameter. The exponent is the recorded `2 * m + 1`,
not the field order `3 ^ (2 * m + 1)`. -/
theorem isCharacterMap_steinberg :
    IsCharacterMap d.weightTorus d.steinberg d.toSuzukiReeIndex.datumSteinberg.weightMap := by
  rw [SuzukiReeIndex.datumSteinberg_weightMap_eq_pow, steinberg_def]
  exact d.isCharacterMap_halfFrobenius.pow d.1.fieldExponent

end

end TauCeti.ReeG2LieIndex
