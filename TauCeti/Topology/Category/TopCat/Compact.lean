/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
public import Mathlib.Topology.DiscreteSubset
public import TauCeti.Topology.Category.TopCat.Limits.Basic

/-!
# Compact subsets of colimits in `TopCat`

A space built as a sequential colimit of `T1` spaces along injective maps, such as the skeletal
filtration of the realization of a simplicial space, carries the final topology of its stages.
This file shows that compact subsets of such a colimit cannot spread over infinitely many stages,
and that the final topology is compactly generated as soon as the stages are.

* In the colimit of any diagram of `T1` spaces, a set whose preimage in every stage is finite is
  closed (`TauCeti.TopCat.isClosed_of_forall_finite_preimage`); since the same holds for all of
  its subsets, it is discrete (`TauCeti.TopCat.isDiscrete_of_forall_finite_preimage`).
* For a sequence of `T1` spaces along injective maps, every compact subset of the colimit lies in
  the image of one stage (`TauCeti.TopCat.exists_subset_range_ι_of_isCompact`). If the maps from
  the stages to the colimit are embeddings, every continuous map from a compact space into the
  colimit therefore factors continuously through one stage
  (`TauCeti.TopCat.exists_lift_of_compactSpace`). This supplies the compact-support hypothesis
  of `TauCeti.isColimitMapCoconeToSSet` and `TauCeti.isColimitMapCoconeSingularHomology`, so
  that singular chains and singular homology of such a colimit are computed stagewise.
* A colimit of compactly generated spaces in `TopCat` is compactly generated
  (`TauCeti.TopCat.uCompactlyGeneratedSpace_of_isColimit`), so such a colimit needs no
  replacement of its topology by the associated compactly generated one.

For the compactness statement, a compact set `K` meeting points outside every stage contains a
sequence of points `x k` lying in a stage of strictly increasing index `n (k + 1)` but outside the
stage of index `n k`. Every stage meets the set of these points in finitely many of them, so the
set is closed and discrete in the colimit, and as a closed subset of `K` it is compact, hence
finite, which is impossible.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Proposition A.1, that a compact subset of a CW complex meets only finitely many cells.
* M. Hovey, *Model Categories*, Mathematical Surveys and Monographs 63, American Mathematical
  Society, 1999, Section 2.4, on compact spaces and sequential colimits of `T1` spaces.
-/

public section

open CategoryTheory Limits Topology Set

universe w w' v u

namespace TauCeti.TopCat

section Colimit

variable {J : Type w} [Category.{w'} J] {F : J ⥤ TopCat.{u}} {c : Cocone F}

/-- In the colimit of a diagram of `T1` spaces in `TopCat`, a set meeting every stage in
finitely many points is closed. -/
theorem isClosed_of_forall_finite_preimage [∀ j, T1Space (F.obj j)] (hc : IsColimit c)
    {S : Set c.pt} (hS : ∀ j, (c.ι.app j ⁻¹' S).Finite) : IsClosed S :=
  (TopCat.isClosed_iff_of_isColimit _ hc S).2 fun j ↦ (hS j).isClosed

/-- In the colimit of a diagram of `T1` spaces in `TopCat`, a set meeting every stage in
finitely many points is discrete. -/
theorem isDiscrete_of_forall_finite_preimage [∀ j, T1Space (F.obj j)] (hc : IsColimit c)
    {S : Set c.pt} (hS : ∀ j, (c.ι.app j ⁻¹' S).Finite) : IsDiscrete S :=
  isDiscrete_iff_forall_mem_exists_isClosed.2 fun t ht ↦
    ⟨t, isClosed_of_forall_finite_preimage hc fun j ↦ (hS j).subset (preimage_mono ht),
      inter_eq_left.2 ht⟩

/-- A colimit of compactly generated spaces in `TopCat` is compactly generated. -/
theorem uCompactlyGeneratedSpace_of_isColimit [∀ j, UCompactlyGeneratedSpace.{v} (F.obj j)]
    (hc : IsColimit c) : UCompactlyGeneratedSpace.{v} c.pt :=
  uCompactlyGeneratedSpace_of_isClosed fun s hs ↦ (TopCat.isClosed_iff_of_isColimit _ hc s).2
    fun j ↦ UCompactlyGeneratedSpace.isClosed fun S f ↦ hs S ((c.ι.app j).hom.comp f)

end Colimit

section Sequential

variable {F : ℕ ⥤ TopCat.{u}} {c : Cocone F}

/-- In a sequential colimit of `T1` spaces in `TopCat` along injective maps, every compact subset
lies in the image of a single stage. -/
theorem exists_subset_range_ι_of_isCompact
    (hF : ∀ ⦃i j : ℕ⦄ (hij : i ≤ j), Function.Injective (F.map (homOfLE hij)))
    [∀ n, T1Space (F.obj n)] (hc : IsColimit c) {K : Set c.pt} (hK : IsCompact K) :
    ∃ n, K ⊆ range (c.ι.app n) := by
  by_contra! h
  have hmono {m n : ℕ} (hmn : m ≤ n) : range (c.ι.app m) ⊆ range (c.ι.app n) := by
    rintro _ ⟨y, rfl⟩
    exact ⟨F.map (homOfLE hmn) y, by rw [← ConcreteCategory.comp_apply, c.w]⟩
  have hcover (p : c.pt) : ∃ n, p ∈ range (c.ι.app n) := by
    obtain ⟨n, y, rfl⟩ :=
      Types.jointly_surjective_of_isColimit (isColimitOfPreserves (forget TopCat) hc) p
    exact ⟨n, y, rfl⟩
  -- For each stage `n`, a point `pt n` of `K` outside stage `n`, and a stage `next n` containing
  -- it; necessarily `n < next n`.
  choose pt hptK hpt using fun n ↦ not_subset.1 (h n)
  choose next hnext using fun n ↦ hcover (pt n)
  have hlt (n : ℕ) : n < next n := by
    by_contra! hle
    exact hpt n (hmono hle (hnext n))
  -- Iterating `next` gives strictly increasing stages `idx k`, and points `x k` outside stage
  -- `idx k` but inside stage `idx (k + 1)`.
  let idx (k : ℕ) : ℕ := next^[k] 0
  have hidx_succ (k : ℕ) : idx (k + 1) = next (idx k) := Function.iterate_succ_apply' next k 0
  have hidx : StrictMono idx := strictMono_nat_of_lt_succ fun k ↦ hidx_succ k ▸ hlt (idx k)
  let x (k : ℕ) : c.pt := pt (idx k)
  have hx {k n : ℕ} (hk : x k ∈ range (c.ι.app n)) : idx k < n := by
    by_contra! hle
    exact hpt _ (hmono hle hk)
  have hle {j k : ℕ} (hjk : x j = x k) : k ≤ j :=
    Nat.lt_succ_iff.1 <| hidx.lt_iff_lt.1 <| hx <| hjk ▸ hidx_succ j ▸ hnext (idx j)
  have hinj : Function.Injective x := fun j k hjk ↦ le_antisymm (hle hjk.symm) (hle hjk)
  -- Stage `n` meets the points `x k` only for `k < n`, so their set is closed and discrete.
  have hfin (n : ℕ) : (c.ι.app n ⁻¹' range x).Finite := by
    refine (((finite_Iio n).image x).preimage
      (injective_ι_of_isColimit hF hc n).injOn).subset ?_
    rintro y ⟨k, hk⟩
    exact ⟨k, (hidx.id_le k).trans_lt (hx ⟨y, hk.symm⟩), hk⟩
  have hcpt : IsCompact (range x) :=
    hK.of_isClosed_subset (isClosed_of_forall_finite_preimage hc hfin)
      (range_subset_iff.2 fun k ↦ hptK _)
  exact infinite_range_of_injective hinj
    (hcpt.finite (isDiscrete_of_forall_finite_preimage hc hfin))

/-- In a sequential colimit of `T1` spaces in `TopCat` whose maps from the stages are embeddings,
every continuous map from a compact space factors continuously through a single stage. -/
theorem exists_lift_of_compactSpace [∀ n, T1Space (F.obj n)] (hc : IsColimit c)
    (hι : ∀ n, IsEmbedding (c.ι.app n)) {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (g : C(X, c.pt)) : ∃ n, ∃ g' : C(X, F.obj n), (c.ι.app n).hom.comp g' = g := by
  have hF ⦃i j : ℕ⦄ (hij : i ≤ j) : Function.Injective (F.map (homOfLE hij)) := fun a b hab ↦
    (hι i).injective <| by rw [← c.w (homOfLE hij), ConcreteCategory.comp_apply, hab,
      ← ConcreteCategory.comp_apply]
  obtain ⟨n, hn⟩ := exists_subset_range_ι_of_isCompact hF hc (isCompact_range g.continuous)
  choose f hf using fun p ↦ hn ⟨p, rfl⟩
  have hfg : c.ι.app n ∘ f = g := funext hf
  exact ⟨n, ⟨f, (hι n).isInducing.continuous_iff.2 (hfg ▸ g.continuous)⟩, ContinuousMap.ext hf⟩

end Sequential

end TauCeti.TopCat
