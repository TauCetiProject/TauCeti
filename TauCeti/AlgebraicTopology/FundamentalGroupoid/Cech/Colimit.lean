/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroupoid.Cech.Diagram
public import TauCeti.AlgebraicTopology.FundamentalGroupoid.Glue

/-!
# The groupoid van Kampen theorem

For an open cover `U` of a topological space `X`, the fundamental groupoid of `X` is the colimit,
in the category of groupoids, of the fundamental groupoids of the nonempty finite intersections
of members of `U`, along the inclusions of intersections. No connectedness assumption is made on
the members of the cover or on their intersections.

The functor induced by a cocone is `TauCeti.FundamentalGroupoid.glue`, applied to the legs of the
cocone at the singleton indices: these are functors out of the fundamental groupoids of the
members of the cover which agree on pairwise intersections, because both factor through the leg
at the corresponding two-element index. Its uniqueness is `TauCeti.FundamentalGroupoid.eq_glue`.
With this theorem, the naturality statements of
`TauCeti.AlgebraicTopology.FundamentalGroupoid.Cech.Map` apply to every open cover.

## Main results

* `TauCeti.FundamentalGroupoid.isColimitCechCocone`: the Čech cocone of an open cover is a
  colimit cocone in the category of groupoids.

## References

* R. Brown, *Topology and Groupoids*, 3rd ed., Section 6.7.
* T. Zhu, [mathlib4#41603](https://github.com/leanprover-community/mathlib4/pull/41603), whose
  fundamental-groupoid cosheaf interface guides the colimit formulation.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Topology
open scoped FundamentalGroupoid

universe u v

namespace TauCeti.FundamentalGroupoid

open TauCeti.TopCat _root_.FundamentalGroupoid

variable {X : TopCat.{v}} {ι : Type u} (U : ι → Opens X)

/-- The leg at `s` of a cocone over the Čech diagram, as a functor out of the fundamental
groupoid of the intersection indexed by `s`. -/
private def coconeLeg (c : Cocone (cechDiagram U)) (s : CechIndex ι) :
    fundamentalGroupoidFunctor.obj (TopCat.of (cechIntersection U s)) ⟶ c.pt :=
  eqToHom (cechDiagram_obj U s).symm ≫ c.ι.app s

/-- The legs of a cocone over the Čech diagram are compatible with the inclusions of
intersections. -/
private lemma map_inclusion_comp_coconeLeg (c : Cocone (cechDiagram U)) {s t : CechIndex ι}
    (f : s ⟶ t) :
    fundamentalGroupoidFunctor.map (TopCat.ofHom (ContinuousMap.inclusion
        (SetLike.coe_subset_coe.2 (cechIntersection_mono U f.le)))) ≫ coconeLeg U c t =
      coconeLeg U c s := by
  have hmap : eqToHom (cechTopDiagram_obj U s).symm ≫ (cechTopDiagram U).map f ≫
      eqToHom (cechTopDiagram_obj U t) = TopCat.ofHom (ContinuousMap.inclusion
        (SetLike.coe_subset_coe.2 (cechIntersection_mono U f.le))) := by
    ext x
    exact congrArg Subtype.val (cechTopDiagram_map_apply U f x)
  have h := cechDiagram_map U f
  rw [hmap] at h
  rw [coconeLeg, coconeLeg, ← h, ← c.w f]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- The map induced by the inclusion of the intersection indexed by `s` is the leg at `s` of the
canonical Čech cocone, transported along `cechDiagram_obj`. -/
private lemma map_subtypeVal_eq_cechCocone_ι_app (s : CechIndex ι) :
    fundamentalGroupoidFunctor.map
        (TopCat.ofHom (ContinuousMap.subtypeVal (cechIntersection U s : Set X))) =
      eqToHom (cechDiagram_obj U s).symm ≫ (cechCocone U).ι.app s := by
  have hinc : eqToHom (cechTopDiagram_obj U s).symm ≫ cechInclusion U s =
      (TopCat.ofHom (ContinuousMap.subtypeVal (cechIntersection U s : Set X)) :
        TopCat.of (cechIntersection U s) ⟶ X) := by
    ext x
    exact cechInclusion_apply U s x
  -- The cocone point is by definition the fundamental groupoid of `X`.
  have hpt : eqToHom (cechCocone_pt U) = 𝟙 ((cechCocone U).pt) := rfl
  rw [← hinc, ← cechCocone_ι_app, hpt]
  exact (Category.assoc _ _ _).symm.trans (Category.comp_id _)

variable {U}

/-- Every point has a singleton Čech intersection of an open cover as a neighbourhood. -/
private lemma exists_cechIntersection_singleton_mem_nhds (hU : IsOpenCover U) (x : X) :
    ∃ i, (cechIntersection U (CechIndex.singleton i) : Set X) ∈ 𝓝 x := by
  obtain ⟨i, hi⟩ := exists_mem_cechIntersection_singleton U hU x
  exact ⟨i, (cechIntersection U _).isOpen.mem_nhds hi⟩

/-- The legs of a cocone at two singleton indices agree on the intersection of the two
singleton intersections, since both factor through the leg at the two-element index. -/
private lemma coconeLeg_singleton_compat (c : Cocone (cechDiagram U)) (i j : ι) :
    fundamentalGroupoidFunctor.map (TopCat.ofHom (ContinuousMap.inclusion
        (Set.inter_subset_left : (cechIntersection U (CechIndex.singleton i) : Set X) ∩
          cechIntersection U (CechIndex.singleton j) ⊆ _))) ≫
      coconeLeg U c (CechIndex.singleton i) =
    fundamentalGroupoidFunctor.map (TopCat.ofHom (ContinuousMap.inclusion
        (Set.inter_subset_right : (cechIntersection U (CechIndex.singleton i) : Set X) ∩
          cechIntersection U (CechIndex.singleton j) ⊆ _))) ≫
      coconeLeg U c (CechIndex.singleton j) := by
  classical
  let s : CechIndex ι := OrderDual.toDual ⟨{i, j}, Finset.insert_nonempty i {j}⟩
  have hs : (cechIntersection U (CechIndex.singleton i) : Set X) ∩
      cechIntersection U (CechIndex.singleton j) ⊆ cechIntersection U s := fun x hx ↦ by
    simp only [SetLike.mem_coe, mem_cechIntersection, CechIndex.coe_singleton,
      Finset.mem_singleton, forall_eq, Set.mem_inter_iff] at hx ⊢
    intro k hk
    rcases Finset.mem_insert.1 hk with rfl | hk
    · exact hx.1
    · exact Finset.mem_singleton.1 hk ▸ hx.2
  -- Both composites factor through the inclusion into the intersection indexed by `{i, j}`.
  have key : ∀ k (_ : s ⟶ CechIndex.singleton k)
      (h : (cechIntersection U (CechIndex.singleton i) : Set X) ∩
        cechIntersection U (CechIndex.singleton j) ⊆ cechIntersection U (CechIndex.singleton k)),
      fundamentalGroupoidFunctor.map (TopCat.ofHom (ContinuousMap.inclusion h)) ≫
        coconeLeg U c (CechIndex.singleton k) =
      fundamentalGroupoidFunctor.map (TopCat.ofHom (ContinuousMap.inclusion hs)) ≫
        coconeLeg U c s := fun k f h ↦ by
    rw [← map_inclusion_comp_coconeLeg U c f, ← Functor.map_comp_assoc, ← TopCat.ofHom_comp]
    -- A composite of inclusions of subsets is the inclusion
    -- (`ContinuousMap.inclusion_comp_inclusion` holds by `rfl`).
    rfl
  refine (key i (homOfLE (CechIndex.le_iff.2 ?_)) _).trans
    (key j (homOfLE (CechIndex.le_iff.2 ?_)) _).symm <;>
    rw [CechIndex.coe_singleton, Finset.singleton_subset_iff]
  exacts [Finset.mem_insert_self i {j}, Finset.mem_insert_of_mem (Finset.mem_singleton_self j)]

/-- **The groupoid van Kampen theorem.** For an open cover of `X`, the fundamental groupoid of
`X` is the colimit of the fundamental groupoids of the nonempty finite intersections of members
of the cover. -/
def isColimitCechCocone (hU : IsOpenCover U) : IsColimit (cechCocone U) where
  desc c := glue (exists_cechIntersection_singleton_mem_nhds hU)
    (fun i ↦ coconeLeg U c (CechIndex.singleton i)) (coconeLeg_singleton_compat c)
  fac c s := by
    obtain ⟨i, hi⟩ := (OrderDual.ofDual s).2
    let f : s ⟶ CechIndex.singleton i := homOfLE (CechIndex.le_iff.2
      (by rw [CechIndex.coe_singleton]; exact Finset.singleton_subset_iff.2 hi))
    -- The glued functor, viewed as a morphism of groupoids.
    let G : fundamentalGroupoidFunctor.obj X ⟶ c.pt :=
      glue (exists_cechIntersection_singleton_mem_nhds hU)
        (fun i ↦ coconeLeg U c (CechIndex.singleton i)) (coconeLeg_singleton_compat c)
    have hG : fundamentalGroupoidFunctor.map (TopCat.ofHom (ContinuousMap.subtypeVal
        (cechIntersection U (CechIndex.singleton i) : Set X))) ≫ G =
        coconeLeg U c (CechIndex.singleton i) :=
      map_subtypeVal_comp_glue (exists_cechIntersection_singleton_mem_nhds hU)
        (fun i ↦ coconeLeg U c (CechIndex.singleton i)) (coconeLeg_singleton_compat c) i
    have key := map_inclusion_comp_coconeLeg U c f
    rw [← hG, ← Category.assoc, ← Functor.map_comp, ← TopCat.ofHom_comp,
      ContinuousMap.subtypeVal_comp_inclusion, map_subtypeVal_eq_cechCocone_ι_app] at key
    exact (cancel_epi _).1 ((Category.assoc _ _ _).symm.trans key)
  uniq c m hm := by
    refine eq_glue _ _ _ fun i ↦ ?_
    have key : fundamentalGroupoidFunctor.map (TopCat.ofHom (ContinuousMap.subtypeVal
        (cechIntersection U (CechIndex.singleton i) : Set X))) ≫ m =
        coconeLeg U c (CechIndex.singleton i) := by
      rw [map_subtypeVal_eq_cechCocone_ι_app]
      exact (Category.assoc _ _ _).trans (congrArg _ (hm _))
    exact key

end TauCeti.FundamentalGroupoid
