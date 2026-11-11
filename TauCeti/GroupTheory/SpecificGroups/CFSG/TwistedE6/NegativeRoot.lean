/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.TwistedE6.Basic

/-!
# Negative simple roots of the twisted E₆ Steinberg map

The graph factor of `²E₆(q)` exchanges the two minuscule summands and sends each negative simple
root subgroup to the one at the selected diagram image. Composing with Frobenius gives the
Steinberg equation with additive parameter raised to `q`, the small-field parameter.

These equations complement the positive-root equations in `TwistedE6.Basic`, supplying the other
sign needed to identify a root-compatible Steinberg comparison. They use the existing lowering
maps of `E6DoubledMinuscule`, its graph-automorphism equation on signed simple roots and its
Frobenius equation; no new root maps or ambient groups are defined.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§12.2–13.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 10–11.
-/

public section

namespace TauCeti.TypeTwistedE6LieIndex

variable (d : TypeTwistedE6LieIndex) (i : Fin d.1.rank) (u : Multiplicative d.1.Closure)

/-- The doubled E₆ graph factor sends each lowering subgroup to the selected diagram image,
with no sign or change of additive parameter. -/
-- Match the indexed node before simp expands its dependent rank transport.
@[simp↓]
theorem graphAut_rootSubgroupPoints_inr :
    d.graphAut (E6DoubledMinuscule.rootSubgroupPoints (.inr (finCongr d.rank_eq_six i))
      d.1.Closure u) =
      E6DoubledMinuscule.rootSubgroupPoints
        (.inr (finCongr d.rank_eq_six (d.toGraphTwistedIndex.diagramPerm i))) d.1.Closure u := by
  rw [graphAut_def, E6DoubledMinuscule.graphAutomorphismPoints_rootSubgroupPoints,
    E6DoubledMinuscule.graphRootPerm_inr, diagramPerm_toGraphTwistedIndex]
  -- The rank transports are inverse even though their equality proofs are written separately.
  have hcast (j : Fin 6) : finCongr d.rank_eq_six (finCongr d.rank_eq_six.symm j) = j :=
    Fin.ext rfl
  rw [hcast]

/-- The `²E₆(q)` Steinberg map applies the selected diagram permutation to negative simple
roots and raises their additive parameters to the small-field order `q`. -/
@[simp↓]
theorem steinberg_rootSubgroupPoints_inr :
    d.steinberg (E6DoubledMinuscule.rootSubgroupPoints (.inr (finCongr d.rank_eq_six i))
      d.1.Closure u) =
      E6DoubledMinuscule.rootSubgroupPoints
        (.inr (finCongr d.rank_eq_six (d.toGraphTwistedIndex.diagramPerm i))) d.1.Closure
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [steinberg_def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    frobenius_def, E6DoubledMinuscule.frobenius_rootSubgroupPoints,
    ← d.1.fieldOrder_eq_characteristic_pow, graphAut_rootSubgroupPoints_inr]

end TauCeti.TypeTwistedE6LieIndex
