/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FixedSubgroup.MatrixCoordinates
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType

/-!
# Finiteness of the Lie-type groups on the classification list

Every valid Lie-type index `d` carries an ambient group `d.AmbientGroup`, a group of invertible
matrices over the algebraic closure of `𝔽_p`, with a `q`-power Frobenius `d.frobenius` raising
every matrix entry to the `q`-th power and a Steinberg endomorphism `d.steinberg`. Some positive
iterate of the Steinberg endomorphism is a positive iterate of the Frobenius:

```text
F = Frob_q                 on the nine untwisted families,
F ^ t = Frob_q ^ t         on ²Aₙ, ²Dₙ, ²E₆ (t = 2) and ³D₄ (t = 3),
F ^ 2 = Frob_q             on the Suzuki, Ree and Tits families.
```

The finite-coordinate criterion `Subgroup.finite_fixedSubgroup_of_iterate_eq_iterate` therefore
bounds the fixed points of `F` by the roots of `X ^ (q ^ k) - X` in each matrix entry, so the
fixed subgroup `d.FixedPoints` is finite. The candidate group `d.Group`, the derived subgroup of
the fixed points modulo its centre, is then finite as well. This is the finiteness of every
Lie-type group on the classification list, for every parameter the validity predicate retains,
including the Tits group and the small fields.

## Main results

* `TauCeti.ValidLieTypeIndex.finite_fixedSubgroup_of_iterate_eq_iterate_frobenius`: an
  endomorphism of the ambient group with an iterate equal to a positive iterate of the Frobenius
  has finitely many fixed points.
* `TauCeti.ValidLieTypeIndex.finite_fixedPoints`: the fixed points of the Steinberg endomorphism
  are finite.
* `TauCeti.ValidLieTypeIndex.finite`: every Lie-type candidate group is finite.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §§10–11.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §§1.17–1.18.
-/

public section

namespace TauCeti

namespace ValidLieTypeIndex

/-- **Endomorphisms with an iterate equal to a positive iterate of the Frobenius have finitely many
fixed points.** If `F ^ r = Frob_q ^ k` on the ambient group of a valid Lie-type index with
`k ≠ 0`, then every point fixed by `F` has its matrix entries among the roots of
`X ^ (q ^ k) - X`, so the fixed subgroup of `F` is finite. -/
theorem finite_fixedSubgroup_of_iterate_eq_iterate_frobenius (d : ValidLieTypeIndex)
    {F : d.AmbientGroup →* d.AmbientGroup} {r k : ℕ} (hk : k ≠ 0)
    (hF : ∀ g, (⇑F)^[r] g = (⇑d.frobenius)^[k] g) : Finite (fixedSubgroup F) := by
  -- On each constructor the Frobenius is that of the family carrier, a subgroup of `GL n` over
  -- the closure on which it raises every entry to the field order.
  obtain ⟨d, hv⟩ := d
  cases d
  · rw [frobenius_A, GraphTwistedIndex.frobenius_A] at hF
    exact Subgroup.finite_fixedSubgroup_of_iterate_eq_iterate _
      (LieTypeIndex.one_lt_fieldOrder _) hk (TypeALieIndex.coe_frobenius_apply _) hF
  · rw [frobenius_twistedA, GraphTwistedIndex.frobenius_twistedA] at hF
    exact Subgroup.finite_fixedSubgroup_of_iterate_eq_iterate _
      (LieTypeIndex.one_lt_fieldOrder _) hk (TypeALieIndex.coe_frobenius_apply _) hF
  · rw [frobenius_B, GraphTwistedIndex.frobenius_B] at hF
    exact Subgroup.finite_fixedSubgroup_of_iterate_eq_iterate _
      (LieTypeIndex.one_lt_fieldOrder _) hk (TypeBLieIndex.coe_frobenius_apply _) hF
  · rw [frobenius_C, GraphTwistedIndex.frobenius_C] at hF
    exact Subgroup.finite_fixedSubgroup_of_iterate_eq_iterate _
      (LieTypeIndex.one_lt_fieldOrder _) hk (TypeCLieIndex.coe_frobenius_apply _) hF
  · rw [frobenius_D, GraphTwistedIndex.frobenius_D] at hF
    exact Subgroup.finite_fixedSubgroup_of_iterate_eq_iterate _
      (LieTypeIndex.one_lt_fieldOrder _) hk (TypeDDiagramLieIndex.coe_frobenius_apply _) hF
  · rw [frobenius_twistedD, GraphTwistedIndex.frobenius_twistedD] at hF
    exact Subgroup.finite_fixedSubgroup_of_iterate_eq_iterate _
      (LieTypeIndex.one_lt_fieldOrder _) hk (TypeDDiagramLieIndex.coe_frobenius_apply _) hF
  · rw [frobenius_E6, GraphTwistedIndex.frobenius_E6] at hF
    exact Subgroup.finite_fixedSubgroup_of_iterate_eq_iterate _
      (LieTypeIndex.one_lt_fieldOrder _) hk (TypeE6LieIndex.coe_steinberg_apply _) hF
  · rw [frobenius_E7, GraphTwistedIndex.frobenius_E7] at hF
    exact Subgroup.finite_fixedSubgroup_of_iterate_eq_iterate _
      (LieTypeIndex.one_lt_fieldOrder _) hk (TypeE7LieIndex.coe_steinberg_apply _) hF
  · rw [frobenius_E8, GraphTwistedIndex.frobenius_E8] at hF
    exact Subgroup.finite_fixedSubgroup_of_iterate_eq_iterate _
      (LieTypeIndex.one_lt_fieldOrder _) hk (UnimodularExceptionalIndex.coe_steinberg_apply _) hF
  · rw [frobenius_F4, GraphTwistedIndex.frobenius_F4] at hF
    exact Subgroup.finite_fixedSubgroup_of_iterate_eq_iterate _
      (LieTypeIndex.one_lt_fieldOrder _) hk (UnimodularExceptionalIndex.coe_steinberg_apply _) hF
  · rw [frobenius_G2, GraphTwistedIndex.frobenius_G2] at hF
    exact Subgroup.finite_fixedSubgroup_of_iterate_eq_iterate _
      (LieTypeIndex.one_lt_fieldOrder _) hk (UnimodularExceptionalIndex.coe_steinberg_apply _) hF
  · rw [frobenius_twistedE6, GraphTwistedIndex.frobenius_twistedE6] at hF
    exact Subgroup.finite_fixedSubgroup_of_iterate_eq_iterate _
      (LieTypeIndex.one_lt_fieldOrder _) hk (TypeTwistedE6LieIndex.coe_frobenius_apply _) hF
  · rw [frobenius_trialityD4, GraphTwistedIndex.frobenius_trialityD4] at hF
    exact Subgroup.finite_fixedSubgroup_of_iterate_eq_iterate _
      (LieTypeIndex.one_lt_fieldOrder _) hk (TypeTrialityD4LieIndex.coe_frobenius_apply _) hF
  · rw [frobenius_suzuki] at hF
    exact Subgroup.finite_fixedSubgroup_of_iterate_eq_iterate _
      (LieTypeIndex.one_lt_fieldOrder _) hk (RankTwoBLieIndex.coe_frobenius_apply _) hF
  · rw [frobenius_reeG2] at hF
    exact Subgroup.finite_fixedSubgroup_of_iterate_eq_iterate _
      (LieTypeIndex.one_lt_fieldOrder _) hk (ReeG2LieIndex.coe_frobenius_apply _) hF
  · rw [frobenius_reeF4] at hF
    exact Subgroup.finite_fixedSubgroup_of_iterate_eq_iterate _
      (LieTypeIndex.one_lt_fieldOrder _) hk (ReeF4LieIndex.coe_frobenius_apply _) hF
  · rw [frobenius_tits] at hF
    exact Subgroup.finite_fixedSubgroup_of_iterate_eq_iterate _ one_lt_two hk
      (TitsLieIndex.coe_frobenius_apply _) hF

/-- **The Steinberg fixed points of every valid Lie-type index are finite.** The Steinberg
endomorphism squares to the Frobenius on the Suzuki, Ree and Tits families, and its twist-order
iterate is that iterate of the Frobenius on the ordinary and graph-twisted families. -/
instance finite_fixedPoints (d : ValidLieTypeIndex) : Finite d.FixedPoints := by
  by_cases h : d.1.UsesHalfFrobenius
  · exact d.finite_fixedSubgroup_of_iterate_eq_iterate_frobenius (r := 2) one_ne_zero
      (steinberg_steinberg_of_usesHalfFrobenius d h)
  · exact d.finite_fixedSubgroup_of_iterate_eq_iterate_frobenius
      (GraphTwistedIndex.twistOrder_pos ⟨d, h⟩).ne'
      (congrFun (iterate_steinberg_twistOrder_of_not_usesHalfFrobenius d h))

/-- **Every Lie-type group on the classification list is finite.** The candidate group of a valid
Lie-type index is the derived subgroup of the finite Steinberg fixed points modulo its centre. -/
theorem finite (d : ValidLieTypeIndex) : Finite d.Group :=
  inferInstance

end ValidLieTypeIndex

end TauCeti
