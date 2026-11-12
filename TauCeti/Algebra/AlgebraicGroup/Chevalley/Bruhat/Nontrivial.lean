/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Borel
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl
import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-!
# Simple Weyl representatives do not preserve the positive Borel

A pinned simple Weyl representative sends its positive simple-root subgroup to the
opposite root subgroup. Its conjugate can therefore belong to the positive Borel-type
subgroup only when the original root element is the identity.

For every Chevalley datum over a nontrivial commutative ring, the simple-root element with
parameter one is nonidentity and witnesses the noncontainment required by the last
Tits-system axiom. Over a field, its nontriviality follows from the Weyl projection:
if it were trivial, the Weyl word would be trivial, contradicting its simple-reflection
image. Passage to a residue field gives the result over an arbitrary nontrivial ring.
No Bruhat decomposition or generation of all scheme points is assumed.

The opposite-intersection argument is supplied by `ChevalleyDatum`'s opposite subgroups;
the Weyl-group image is supplied by `ChevalleyDatum.weylProjection_weylElement`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3.
* R. W. Carter, *Simple Groups of Lie Type*, §8.1.
-/

public section

universe v

namespace TauCeti.DynkinType.ChevalleyDatum

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

private theorem rootSubgroupPoints_simpleIndex_one_ne_one_field
    (k : Type v) [Field k] (i : Fin t.rank) :
    D.rootSubgroupPoints (t.simpleIndex ht i) k (Multiplicative.ofAdd 1) ≠ 1 := by
  intro hx
  have hconj := D.weylElement_conj_rootSubgroupPoints i (t.simpleIndex ht i) k 1
  have hy : D.rootSubgroupPoints
      ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i) (t.simpleIndex ht i))
      k (Multiplicative.ofAdd (-1)) = 1 := by
    rcases Int.units_eq_one_or (t.chevalleyWeylSign ht (t.simpleIndex ht i)
      (t.simpleIndex ht i)) with hε | hε
    · simpa [hx, hε] using congrArg Inv.inv hconj.symm
    · simpa [hx, hε] using hconj.symm
  have hw : D.weylElement (t.simpleIndex ht i) k 1 = 1 := by
    simp only [D.weylElement_def, inv_one, Units.val_one, hx, hy, one_mul]
  have hsub : (⟨D.weylElement (t.simpleIndex ht i) k 1,
      D.weylElement_mem_weylSubgroup k i⟩ : D.weylSubgroup k) = 1 := Subtype.ext hw
  have hproj := D.weylProjection_weylElement k i
  rw [hsub, map_one] at hproj
  exact RootPairing.weylGroup.ofIdx_ne_one (t.simplyConnectedRootDatum ht)
    (t.simpleIndex ht i) hproj.symm

/-- For every Chevalley datum over a nontrivial ring, the simple-root element with additive
parameter one is nonidentity. -/
@[simp]
theorem rootSubgroupPoints_simpleIndex_one_ne_one
    (A : Type v) [CommRing A] [Nontrivial A] (i : Fin t.rank) :
    D.rootSubgroupPoints (t.simpleIndex ht i) A (Multiplicative.ofAdd 1) ≠ 1 := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  let : M.IsMaximal := hM
  let := Ideal.Quotient.field M
  intro hx
  apply D.rootSubgroupPoints_simpleIndex_one_ne_one_field (A ⧸ M) i
  have h := congrArg
    ((D.pointsPresentation A).map (D.pointsPresentation (A ⧸ M)) (Ideal.Quotient.mk M)) hx
  simpa only [D.map_rootSubgroupPoints, toAdd_ofAdd, map_one] using h

/-- Every pinned simple Weyl representative conjugates some element of the positive Borel
outside that Borel, for every Chevalley datum over a nontrivial commutative ring. -/
theorem exists_weylElement_conj_notMem_borelSubgroup
    (A : Type v) [CommRing A] [Nontrivial A] (i : Fin t.rank) :
    ∃ b : D.borelSubgroup A,
      D.weylElement (t.simpleIndex ht i) A 1 * b.val *
        (D.weylElement (t.simpleIndex ht i) A 1)⁻¹ ∉ D.borelSubgroup A := by
  have hpos : t.simpleIndex ht i ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) :=
    support_subset_posRoots _ _ (t.simpleIndex_mem_support i)
  refine ⟨⟨D.rootSubgroupPoints (t.simpleIndex ht i) A (Multiplicative.ofAdd 1),
    D.positivePoints_le_borelSubgroup A (D.rootSubgroupPoints_mem_positivePoints A hpos _)⟩, ?_⟩
  rw [D.weylElement_conj_rootSubgroupPoints_simpleIndex_mem_borelSubgroup_iff]
  exact D.rootSubgroupPoints_simpleIndex_one_ne_one A i

end TauCeti.DynkinType.ChevalleyDatum
