/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Tits.Basic

/-!
# The Tits Steinberg equation on negative simple roots

The Tits map is the exceptional endomorphism itself, rather than a higher odd iterate. It
reverses the four negative simple roots of the characteristic-two short-root carrier, with
exponent one at long source roots and two at short source roots. This is the negative half of
the root equation needed for a pinning-preserving comparison of Steinberg maps.

The proof specializes `F4ShortRoot.PrimeField.specialIsogeny_rootSubgroupPoints` using the
numbering adapters of `Tits.Basic`, just as for the positive simple roots. The indexed negative
root maps use the existing carrier's numbered lowering subgroups.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §14.
-/

public section

namespace TauCeti.TitsLieIndex

noncomputable section

variable (d : TitsLieIndex)

/-- The Tits Steinberg map reverses negative simple roots with the indexed source-root exponent.
The separate Tits index has the exceptional parameter `m = 0`. -/
@[simp]
theorem steinberg_negativeSimpleRootSubgroup (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.steinberg (d.negativeSimpleRootSubgroup i u) =
      d.negativeSimpleRootSubgroup (d.toSuzukiReeIndex.lengthPerm i)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.toSuzukiReeIndex.exponent i)) := by
  rw [steinberg_def, negativeSimpleRootSubgroup_def,
    F4ShortRoot.PrimeField.specialIsogeny_rootSubgroupPoints, negativeSimpleRootSubgroup_def,
    finCongr_lengthPerm, ← isogenyExponent_inl_finCongr]
  simp only [F4ShortRoot.isogenyReverse, Sum.map_inr,
    F4ShortRoot.isogenyExponent_inr]

end

end TauCeti.TitsLieIndex
