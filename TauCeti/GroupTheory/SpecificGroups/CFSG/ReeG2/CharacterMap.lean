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

/-- The native Steinberg character action, transported from the index's rank coordinates
into the carrier's two fundamental-weight coordinates. -/
theorem weightTorus_torusPointMap_datumSteinberg (s : Fin d.1.rank → d.1.Closureˣ) :
    d.weightTorus (torusPointMap d.toSuzukiReeIndex.datumSteinberg.weightMap s) =
      G2ShortRoot.PrimeField.weightTorusPoints d.1.Closure
        (torusPointMap (DynkinType.g2SpecialIsogeny.weightMap ^ d.1.fieldExponent)
          (fun i => s ((finCongr d.rank_eq_two).symm i))) := by
  obtain ⟨m, hm, rfl⟩ := d.exists_eq_of
  -- For the constructor `of`, the recorded diagram is G₂ and its rank is 2.
  -- Its inverse rank identification preserves each numbered coordinate.
  have hr (i : Fin 2) : (finCongr (of m hm).rank_eq_two).symm i = i :=
    Fin.ext rfl
  rw [weightTorus_apply, SuzukiReeIndex.datumSteinberg_weightMap_eq_pow]
  simp only [toSuzukiReeIndex, SuzukiReeIndex.datumSpecialIsogeny_weightMap_reeG2, hr]
  rfl

/-- The represented Ree G₂ Steinberg map pulls characters back by the native root-datum
Steinberg map, for every valid Ree parameter. The exponent is the recorded `2 * m + 1`,
not the field order `3 ^ (2 * m + 1)`. -/
theorem isCharacterMap_steinberg :
    IsCharacterMap d.weightTorus d.steinberg d.toSuzukiReeIndex.datumSteinberg.weightMap := by
  have h := G2ShortRoot.PrimeField.isCharacterMap_specialIsogeny_pow
    d.1.Closure d.1.fieldExponent
  apply isCharacterMap_iff.mpr
  intro s
  rw [weightTorus_torusPointMap_datumSteinberg, weightTorus_apply,
    steinberg_def, halfFrobenius_def]
  exact h.map_apply _

end

end TauCeti.ReeG2LieIndex
