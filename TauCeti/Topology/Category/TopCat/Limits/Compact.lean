/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Limits.Konig
public import Mathlib.CategoryTheory.Filtered.Final

/-!
# Finite-stage emptiness in compact Hausdorff limits

If a closed subset of one stage has empty inverse image in a cofiltered limit of compact
Hausdorff spaces, its inverse image is already empty after a transition map. No surjectivity
is required. This is the compactness argument used to detect finite-stage relations in inverse
limits, including spectral limits after passage to constructible topologies.

## Main results

* `TopCat.exists_preimage_eq_empty_of_isLimit`: a closed subset of a stage that misses the image
  of the limit misses the image of a later stage.
* `TopCat.exists_range_map_subset_of_isLimit`: an open subset of a stage that contains the image
  of the limit contains the image of a later stage.
* `TopCat.exists_comp_map_eq_of_isLimit`: two continuous maps from a stage to a discrete space
  that agree on the limit agree after a transition map. This is the uniqueness half of
  `Profinite.exists_locallyConstant`.

## References

* The Stacks Project, Tag 0A2Y, Lemma 5.24.4.
-/

public section

open CategoryTheory CategoryTheory.Limits Set Topology

namespace TopCat

universe v u

variable {J : Type v} [SmallCategory J] [IsCofiltered J]
  (F : J ⥤ TopCat.{max v u}) [∀ j, CompactSpace (F.obj j)] [∀ j, T2Space (F.obj j)]
  (c : Cone F) (hc : IsLimit c)

include hc

/-- A closed subset of a compact Hausdorff stage that misses the limit already misses a
later stage. The transition maps need not be surjective. -/
theorem exists_preimage_eq_empty_of_isLimit {i : J} {s : Set (F.obj i)} (hs : IsClosed s)
    (h : c.π.app i ⁻¹' s = ∅) : ∃ (j : J) (f : j ⟶ i), F.map f ⁻¹' s = ∅ := by
  classical
  by_contra! hn
  -- Restrict to the compact closed preimages over the category of arrows into `i`.
  let G : Over i ⥤ TopCat.{max v u} :=
    { obj := fun j ↦ TopCat.of (F.map j.hom ⁻¹' s)
      map := fun {j k} a ↦ TopCat.ofHom
        ⟨fun x ↦ ⟨F.map a.left x.val, by
          simpa only [mem_preimage, ← ConcreteCategory.comp_apply, ← F.map_comp,
            Over.w a] using x.property⟩,
          by fun_prop⟩
      map_id := by intro j; ext x; simp
      map_comp := by intro j k l a b; ext x; simp }
  have : ∀ j, CompactSpace (G.obj j) := fun j ↦
    isCompact_iff_compactSpace.mp (hs.preimage (F.map j.hom).hom.continuous).isCompact
  have : ∀ j, T2Space (G.obj j) := fun j ↦ inferInstanceAs (T2Space (F.map j.hom ⁻¹' s))
  have : ∀ j, Nonempty (G.obj j) := fun j ↦ by
    obtain ⟨z, hz⟩ := hn j.left j.hom
    exact ⟨⟨z, hz⟩⟩
  obtain ⟨x⟩ := nonempty_limitCone_of_compact_t2_cofiltered_system G
  -- The forgetful functor `Over i → J` is initial, so the compatible family gives a limit point.
  let d : Cone (Over.forget i ⋙ F) :=
    { pt := TopCat.of PUnit
      π :=
        { app := fun j ↦ TopCat.ofHom ⟨fun _ ↦ (x.val j).val, continuous_const⟩
          naturality := by
            intro j k a
            ext
            exact (congrArg Subtype.val (x.property a)).symm } }
  let hc' := (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc
  let y := hc'.lift d PUnit.unit
  have hy : c.π.app i y ∈ s := by
    have he : c.π.app i y = (x.val (Over.mk (𝟙 i))).val :=
      ConcreteCategory.congr_hom (hc'.fac d (Over.mk (𝟙 i))) PUnit.unit
    rw [he]
    simpa using (x.val (Over.mk (𝟙 i))).property
  have hm : y ∈ c.π.app i ⁻¹' s := hy
  rw [h] at hm
  exact hm

/-- An open subset of a compact Hausdorff stage that contains the image of the limit already
contains the image of a later stage. The transition maps need not be surjective. -/
theorem exists_range_map_subset_of_isLimit {i : J} {U : Set (F.obj i)} (hU : IsOpen U)
    (hU' : range (c.π.app i) ⊆ U) : ∃ (j : J) (f : j ⟶ i), range (F.map f) ⊆ U := by
  obtain ⟨j, f, hf⟩ := exists_preimage_eq_empty_of_isLimit F c hc hU.isClosed_compl
    (eq_empty_of_forall_notMem fun x hx ↦ hx (hU' ⟨x, rfl⟩))
  refine ⟨j, f, range_subset_iff.mpr fun y ↦ ?_⟩
  by_contra hy
  exact (eq_empty_iff_forall_notMem.mp hf) y hy

/-- Two continuous maps from a compact Hausdorff stage to a discrete space that agree on the limit
already agree after a transition map. -/
theorem exists_comp_map_eq_of_isLimit {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    {i : J} {g g' : C(F.obj i, A)} (h : g.comp (c.π.app i).hom = g'.comp (c.π.app i).hom) :
    ∃ (j : J) (f : j ⟶ i), g.comp (F.map f).hom = g'.comp (F.map f).hom := by
  obtain ⟨j, f, hf⟩ := exists_preimage_eq_empty_of_isLimit F c hc
    (s := {y | g y ≠ g' y})
    ((isClosed_discrete {q : A × A | q.1 ≠ q.2}).preimage (g.continuous.prodMk g'.continuous))
    (eq_empty_of_forall_notMem fun x hx ↦ hx (DFunLike.congr_fun h x))
  refine ⟨j, f, ContinuousMap.ext fun y ↦ ?_⟩
  by_contra hy
  exact (eq_empty_iff_forall_notMem.mp hf) y hy

end TopCat
