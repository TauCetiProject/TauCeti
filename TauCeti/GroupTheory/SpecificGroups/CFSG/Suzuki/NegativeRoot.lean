/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Suzuki.Basic

/-!
# Suzuki endomorphisms on negative simple roots

The Suzuki half-Frobenius exchanges the negative long and short simple-root subgroups,
with source-root parameter exponents 1 and 2, respectively. Its odd power therefore has
exponents `2^m` and `2^(m+1)`. These equations complement the positive-root formulas and
allow endomorphism comparisons to retain both signs of the pinning.

The formulas use the native lowering maps `TauCeti.SpStd.rootSubgroupPoints`, with B₂ nodes
transported through `TauCeti.RankTwoBLieIndex.carrierNode`. We use the independently constructed
`TauCeti.SpStd.specialIsogeny` and the odd-power transport theorem
`TauCeti.SuzukiReeIndex.pow_fieldExponent_apply_lengthPerm`.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §14.
* A.-C. Radu, *On the cohomology of the Ree groups and kernels of exceptional isogenies*,
  arXiv:2108.06291v2, §2.2, for the odd-power construction.
-/

public section

namespace TauCeti.SuzukiLieIndex

variable (d : SuzukiLieIndex)

/-- The half-Frobenius exchanges negative simple roots by the native length permutation;
the parameter exponent is 1 on a long source root and 2 on a short source root. -/
-- Rewrite before simplification expands the node adapter inside the root-map argument.
@[simp↓] theorem halfFrobenius_rootSubgroupPoints_inr (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.halfFrobenius
        (SpStd.rootSubgroupPoints 1 (.inr (d.toRankTwoBLieIndex.carrierNode i)) d.1.Closure u) =
      SpStd.rootSubgroupPoints 1
        (.inr (d.toRankTwoBLieIndex.carrierNode
          (SuzukiReeIndex.lengthPerm d.toSuzukiReeIndex i))) d.1.Closure
        (Multiplicative.ofAdd
          (Multiplicative.toAdd u ^ SuzukiReeIndex.exponent d.toSuzukiReeIndex i)) := by
  rw [d.carrierNode_lengthPerm, d.exponent_eq_ite_carrierNode, halfFrobenius_def]
  generalize d.toRankTwoBLieIndex.carrierNode i = c
  fin_cases c
  · simpa using SpStd.specialIsogeny_rootSubgroupPoints_inr_zero d.1.Closure
      (Multiplicative.toAdd u)
  · simpa using SpStd.specialIsogeny_rootSubgroupPoints_inr_last d.1.Closure
      (Multiplicative.toAdd u)

/-- The Suzuki Steinberg map exchanges negative simple roots and raises their parameters to
`p^m * aᵢ`, where `aᵢ` is the native source-root exponent of the half-Frobenius. -/
-- As above, the indexed root-map equation precedes simplification of its node adapter.
@[simp↓] theorem steinberg_rootSubgroupPoints_inr (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.steinberg
        (SpStd.rootSubgroupPoints 1 (.inr (d.toRankTwoBLieIndex.carrierNode i)) d.1.Closure u) =
      SpStd.rootSubgroupPoints 1
        (.inr (d.toRankTwoBLieIndex.carrierNode
          (SuzukiReeIndex.lengthPerm d.toSuzukiReeIndex i))) d.1.Closure
        (Multiplicative.ofAdd
          (Multiplicative.toAdd u ^
            (d.1.characteristic ^ SuzukiReeIndex.halfExponent d.toSuzukiReeIndex *
              SuzukiReeIndex.exponent d.toSuzukiReeIndex i))) := by
  rw [steinberg_def]
  exact d.toSuzukiReeIndex.pow_fieldExponent_apply_lengthPerm
    (x := fun j t =>
      SpStd.rootSubgroupPoints 1 (.inr (d.toRankTwoBLieIndex.carrierNode j)) d.1.Closure t)
    (fun j t => d.halfFrobenius_rootSubgroupPoints_inr j t) i u

end TauCeti.SuzukiLieIndex
