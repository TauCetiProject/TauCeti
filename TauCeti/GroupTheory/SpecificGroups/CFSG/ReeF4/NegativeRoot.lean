/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.ReeF4.Basic

/-!
# Ree F₄ Steinberg equations on negative simple roots

The exceptional endomorphism and its indexed odd iterate reverse the negative simple roots of
the characteristic-two short-root carrier. The parameter exponents are attached to the source
node, exactly as for the positive simple roots. These equations supply the negative half of the
pinning needed to compare Steinberg maps by their values on signed simple root subgroups.

The indexed negative root maps use the existing carrier's numbered lowering subgroups.
The proof specializes
`F4ShortRoot.PrimeField.specialIsogeny_rootSubgroupPoints` and applies
`SuzukiReeIndex.pow_fieldExponent_apply_lengthPerm`, as in the positive-root construction in
`ReeF4.Basic`.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §14.
* A.-C. Radu, *On the cohomology of the Ree groups and kernels of exceptional isogenies*,
  arXiv:2108.06291v2, §2.2, for the odd-power construction.
-/

public section

namespace TauCeti.ReeF4LieIndex

noncomputable section

variable (d : ReeF4LieIndex)

/-- The exceptional endomorphism reverses negative simple roots with the indexed source-root
exponent: one on the long roots and two on the short roots. -/
@[simp]
theorem halfFrobenius_negativeSimpleRootSubgroup (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.halfFrobenius (d.negativeSimpleRootSubgroup i u) =
      d.negativeSimpleRootSubgroup (d.toSuzukiReeIndex.lengthPerm i)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.toSuzukiReeIndex.exponent i)) := by
  rw [halfFrobenius_def, negativeSimpleRootSubgroup_def,
    F4ShortRoot.PrimeField.specialIsogeny_rootSubgroupPoints, negativeSimpleRootSubgroup_def,
    finCongr_lengthPerm, ← isogenyExponent_inl_finCongr]
  simp only [F4ShortRoot.isogenyReverse, Sum.map_inr,
    F4ShortRoot.isogenyExponent_inr]

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

end TauCeti.ReeF4LieIndex
