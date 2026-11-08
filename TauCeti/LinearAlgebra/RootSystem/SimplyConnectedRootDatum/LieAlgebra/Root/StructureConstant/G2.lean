/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.G2.RootString
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Root.StructureConstant

/-!
# Structure constants at long sums in type `G₂`

For two short roots of the pinned `G₂` datum whose sum is long, the descending root string has
length two. Thus the native integer Chevalley bracket coefficient is `±3`. This is the
coefficient-three phenomenon behind commutation of those root subgroups in characteristic three.

The root-string calculation is `g2_chainBotCoeff_eq_two_of_short_add_short_eq_long`, and the
coefficient formula is `structureConstant_eq_natCast_or_eq_neg_natCast`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 1, Theorem 1.
* R. W. Carter, *Simple Groups of Lie Type*, §4.2.
-/

public section

namespace TauCeti.DynkinType

variable {ht : G2.Valid}

/-- The bracket coefficient of two short `G₂` roots with a long sum is `±3`. -/
theorem structureConstant_G2_eq_three_or_eq_neg_three {α β γ : Fin G2.numRoots}
    (hα : g2Length α = 1) (hβ : g2Length β = 1) (hγ : g2Length γ = 3)
    (hadd : (G2.simplyConnectedRootDatum ht).root γ =
      (G2.simplyConnectedRootDatum ht).root α + (G2.simplyConnectedRootDatum ht).root β) :
    G2.structureConstant ht α β = 3 ∨ G2.structureConstant ht α β = -3 := by
  have hc : (G2.simplyConnectedRootDatum ht).chainBotCoeff α β = 2 := by
    rw [simplyConnectedRootDatum_G2]
    apply g2_chainBotCoeff_eq_two_of_short_add_short_eq_long α β γ hα hβ hγ
    rw [simplyConnectedRootDatum_G2] at hadd
    exact hadd.trans (add_comm _ _)
  have h := structureConstant_eq_natCast_or_eq_neg_natCast (t := G2) (ht := ht) ⟨γ, hadd⟩
  rw [hc] at h
  norm_num at h
  exact h

end TauCeti.DynkinType
