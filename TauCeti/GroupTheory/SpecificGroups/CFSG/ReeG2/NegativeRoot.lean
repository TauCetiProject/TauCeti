/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.ReeG2.Basic

/-!
# Ree G₂ Steinberg equations on negative simple roots

The exceptional endomorphism and its indexed odd iterate exchange the negative simple roots of
the characteristic-three short-root carrier with the same source-root exponents as on the
positive roots. These equations supply the negative half of the pinning needed to compare
Steinberg maps by their values on signed simple root subgroups. The indexed negative root maps
use the existing carrier's numbered lowering subgroups.

The proof specializes `G2ShortRoot.PrimeField.specialIsogeny_rootSubgroupPoints` and uses
`SuzukiReeIndex.pow_fieldExponent_apply_lengthPerm` for the odd iterate, as in the positive-root
construction in `ReeG2.Basic`.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §12.4.
* A.-C. Radu, *On the cohomology of the Ree groups and kernels of exceptional isogenies*,
  arXiv:2108.06291v2, §2.2, for the odd-power construction.
-/

public section

namespace TauCeti.ReeG2LieIndex

noncomputable section

variable (d : ReeG2LieIndex)

/-- The exceptional endomorphism exchanges negative simple roots with the indexed source-root
exponent: three on the short root and one on the long root. -/
@[simp]
theorem halfFrobenius_negativeSimpleRootSubgroup (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.halfFrobenius (d.negativeSimpleRootSubgroup i u) =
      d.negativeSimpleRootSubgroup (d.toSuzukiReeIndex.lengthPerm i)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.toSuzukiReeIndex.exponent i)) := by
  obtain ⟨t, rfl⟩ := Multiplicative.ofAdd.surjective u
  rw [halfFrobenius_def, negativeSimpleRootSubgroup_def,
    G2ShortRoot.PrimeField.specialIsogeny_rootSubgroupPoints, negativeSimpleRootSubgroup_def,
    G2ShortRoot.PrimeField.specialIsogenyRootIndex_inr, finCongr_lengthPerm,
    ← specialIsogenyExponent_inl_finCongr]
  simp only [G2ShortRoot.PrimeField.specialIsogenyExponent_inr,
    G2ShortRoot.PrimeField.specialIsogenyExponent_inl, toAdd_ofAdd]

/-- The Ree Steinberg map has parameter exponent `p^m * aᵢ` on each negative simple root,
where `aᵢ` is the exceptional exponent at the source node. -/
@[simp]
theorem steinberg_negativeSimpleRootSubgroup (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.steinberg (d.negativeSimpleRootSubgroup i u) =
      d.negativeSimpleRootSubgroup (d.toSuzukiReeIndex.lengthPerm i)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^
          (d.1.characteristic ^ d.toSuzukiReeIndex.halfExponent *
            d.toSuzukiReeIndex.exponent i))) := by
  rw [steinberg_def]
  exact d.toSuzukiReeIndex.pow_fieldExponent_apply_lengthPerm
    (x := fun j t => d.negativeSimpleRootSubgroup j t)
    (fun j t => d.halfFrobenius_negativeSimpleRootSubgroup j t) i u

end

end TauCeti.ReeG2LieIndex
