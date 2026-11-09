/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyFinsupp

/-!
# Locally finite sums of functions with locally finite support

If `c : ι → Function.locallyFinsupp X Y` is a family of functions with locally finite support
whose supports form a locally finite family of subsets of `X`, then near every point only finitely
many `c j` are nonzero, so the pointwise sum `x ↦ ∑ᶠ j, c j x` is a genuine sum and again has
locally finite support. This is `Function.locallyFinsupp.locallyFiniteSum`.

Such sums are how algebraic cycles are added up over infinite families, for instance in the
definition of rational equivalence on a scheme that is not quasi-compact
([Stacks, Tag 02RV](https://stacks.math.columbia.edu/tag/02RV)). The file records the evaluation
formula and compatibility with negation, with sums over a disjoint union of index types and with
empty families.
-/

public section

open Set Filter Topology

namespace Function.locallyFinsupp

variable {X Y ι κ : Type*} [TopologicalSpace X]

section AddCommMonoid

variable [AddCommMonoid Y]

/-- The sum of a family of functions with locally finite support whose supports form a locally
finite family. Near each point only finitely many members are nonzero, so the pointwise `finsum`
is a genuine finite sum. -/
noncomputable def locallyFiniteSum (c : ι → locallyFinsupp X Y)
    (hc : LocallyFinite fun j ↦ (c j).support) : locallyFinsupp X Y where
  toFun x := ∑ᶠ j, c j x
  supportWithinDomain' := subset_univ _
  supportLocallyFiniteWithinDomain' z _ := by
    obtain ⟨t, ht, hfin⟩ := hc z
    choose u hu hufin using fun j ↦ (c j).supportLocallyFiniteWithinDomain' z (mem_univ z)
    refine ⟨t ∩ ⋂ j ∈ {j | ((c j).support ∩ t).Nonempty}, u j,
      inter_mem ht ((biInter_mem hfin).mpr fun j _ ↦ hu j), ?_⟩
    refine (hfin.biUnion fun j _ ↦ hufin j).subset ?_
    rintro x ⟨⟨hxt, hxu⟩, hx⟩
    obtain ⟨j, hj⟩ : ∃ j, c j x ≠ 0 := by
      by_contra! h
      exact hx (finsum_eq_zero_of_forall_eq_zero h)
    have hjJ : ((c j).support ∩ t).Nonempty := ⟨x, hj, hxt⟩
    exact mem_biUnion hjJ ⟨mem_iInter₂.mp hxu j hjJ, hj⟩

/-- A locally finite sum is evaluated pointwise as a `finsum`. -/
@[simp]
lemma locallyFiniteSum_apply (c : ι → locallyFinsupp X Y)
    (hc : LocallyFinite fun j ↦ (c j).support) (x : X) :
    locallyFiniteSum c hc x = ∑ᶠ j, c j x :=
  (rfl)

/-- At each point, only finitely many members of a family with locally finite supports are
nonzero. -/
lemma finite_support_apply (c : ι → locallyFinsupp X Y)
    (hc : LocallyFinite fun j ↦ (c j).support) (x : X) :
    (Function.support fun j ↦ c j x).Finite :=
  hc.point_finite x

/-- The locally finite sum of an empty family is zero. -/
@[simp]
lemma locallyFiniteSum_of_isEmpty [IsEmpty ι] (c : ι → locallyFinsupp X Y)
    (hc : LocallyFinite fun j ↦ (c j).support) :
    locallyFiniteSum c hc = 0 := by
  ext x
  simp [finsum_of_isEmpty]

/-- A locally finite sum over a disjoint union of index types is the sum of the two locally finite
sums. -/
lemma locallyFiniteSum_sumElim (c : ι → locallyFinsupp X Y) (d : κ → locallyFinsupp X Y)
    (hc : LocallyFinite fun j ↦ (c j).support) (hd : LocallyFinite fun j ↦ (d j).support)
    (hcd : LocallyFinite fun j ↦ (Sum.elim c d j).support) :
    locallyFiniteSum (Sum.elim c d) hcd = locallyFiniteSum c hc + locallyFiniteSum d hd := by
  ext x
  have hfin := finite_support_apply _ hcd x
  rw [locallyFiniteSum_apply, Function.locallyFinsuppWithin.coe_add, Pi.add_apply,
    locallyFiniteSum_apply, locallyFiniteSum_apply, ← finsum_mem_univ,
    ← Set.range_inl_union_range_inr,
    finsum_mem_union' Set.isCompl_range_inl_range_inr.disjoint (hfin.subset inter_subset_right)
      (hfin.subset inter_subset_right),
    finsum_mem_range Sum.inl_injective, finsum_mem_range Sum.inr_injective]
  rfl

end AddCommMonoid

/-- The locally finite sum of the negatives is the negative of the locally finite sum. -/
lemma locallyFiniteSum_neg [AddCommGroup Y] (c : ι → locallyFinsupp X Y)
    (hc : LocallyFinite fun j ↦ (c j).support) (hc' : LocallyFinite fun j ↦ (-c j).support) :
    locallyFiniteSum (fun j ↦ -c j) hc' = -locallyFiniteSum c hc := by
  ext x
  simp [finsum_neg_distrib]

end Function.locallyFinsupp
