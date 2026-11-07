/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.CharacterMap
public import TauCeti.GroupTheory.SpecificGroups.CFSG.ReeF4.Basic
public import TauCeti.GroupTheory.SpecificGroups.CFSG.HalfFrobenius

/-!
# Character pullback of the represented Ree F₄ Steinberg map

The weight torus of the prime-field short-root carrier is reindexed by the validated index's
Bourbaki nodes. On this torus the represented half-Frobenius has the character map of the native
special root-datum isogeny. Its recorded odd power has exactly the weight map of
`SuzukiReeIndex.datumSteinberg`, with no new permutation or exponent table.

This compares the independently defined carrier and lattice maps; it does not identify the
carrier with a canonical simply connected group scheme. The carrier calculation is supplied by
`F4ShortRoot.PrimeField.isCharacterMap_specialIsogeny_pow`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10, Theorem 28.
* A.-C. Radu, *On the cohomology of the Ree groups and kernels of exceptional isogenies*,
  arXiv:2108.06291v2, §2.2, for the odd-power convention.
-/

public section

namespace TauCeti.ReeF4LieIndex

noncomputable section

variable (d : ReeF4LieIndex)

/-- The represented weight torus in the index's fundamental-weight coordinates. -/
def weightTorus : (Fin d.1.rank → d.1.Closureˣ) →* d.AmbientGroup :=
  (F4ShortRoot.PrimeField.weightTorusPoints d.1.Closure).comp
    (MonoidHom.pi fun i => Pi.evalMonoidHom _ (finCongr d.rank_eq_four.symm i))

/-- Evaluation of the indexed torus uses the rank identification and no node permutation. -/
theorem weightTorus_apply (s : Fin d.1.rank → d.1.Closureˣ) :
    d.weightTorus s = F4ShortRoot.PrimeField.weightTorusPoints d.1.Closure
      (fun i => s (finCongr d.rank_eq_four.symm i)) :=
  (rfl)

/-- The represented half-Frobenius has the native special isogeny's character pullback. -/
theorem isCharacterMap_halfFrobenius :
    IsCharacterMap d.weightTorus d.halfFrobenius
      d.toSuzukiReeIndex.datumSpecialIsogeny.weightMap := by
  have h := F4ShortRoot.PrimeField.isCharacterMap_specialIsogeny d.1.Closure
  -- The character lattice depends on the rank; eliminate the index before identifying it
  -- with the four coordinates of the represented carrier.
  obtain ⟨m, hv, rfl⟩ := d.exists_eq_of
  rw [weightTorus, halfFrobenius_def]
  simp only [toSuzukiReeIndex, SuzukiReeIndex.datumSpecialIsogeny_weightMap_reeF4]
  exact h

/-- The represented Ree F₄ Steinberg map pulls characters back by the native datum Steinberg
map, with the same odd exponent as the point-group endomorphism. -/
theorem isCharacterMap_steinberg :
    IsCharacterMap d.weightTorus d.steinberg d.toSuzukiReeIndex.datumSteinberg.weightMap := by
  have h := F4ShortRoot.PrimeField.isCharacterMap_specialIsogeny_pow
    d.1.Closure d.1.fieldExponent
  rw [d.toSuzukiReeIndex.fieldExponent_eq_two_mul_halfExponent_add_one,
    RootPairingIsogeny.weightMap_pow_two_mul_add_one _
      DynkinType.f4SpecialIsogeny_mul_self] at h
  obtain ⟨m, hv, rfl⟩ := d.exists_eq_of
  rw [weightTorus, steinberg_def, halfFrobenius_def,
    SuzukiReeIndex.datumSteinberg_weightMap]
  simp only [toSuzukiReeIndex, SuzukiReeIndex.datumSpecialIsogeny_weightMap_reeF4,
    SuzukiReeIndex.halfExponent_reeF4, ValidLieTypeIndex.fieldExponent,
    ValidLieTypeIndex.characteristic, LieTypeIndex.fieldExponent_reeF4,
    LieTypeIndex.characteristic_reeF4] at h ⊢
  exact h

end

end TauCeti.ReeF4LieIndex
