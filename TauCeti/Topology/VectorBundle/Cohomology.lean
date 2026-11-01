/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.DirectedUnion
public import TauCeti.Topology.VectorBundle.MayerVietoris

/-!
# Gluing top-degree classes of a vector bundle

Let a finite-dimensional real vector bundle have model fibre `F` of dimension `r`.
Classes in degree `r` of its Thom pairs over trivializing open sets glue uniquely when
they agree on each fibre in an overlap. The cover can be infinite, and the base need
not be compact, Hausdorff or paracompact. In particular, compatible local Thom classes
have a unique global extension over the union of their domains.

`TauCeti.existsUnique_singularCohomology_thomPairOver_iUnion` extends the finite-union
gluing theorem in `TauCeti.Topology.VectorBundle.MayerVietoris`. It passes through relative
homology of finite trivializing unions, rather than assuming that cohomology commutes
with unions.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, §10 (the Thom isomorphism).
* A. Hatcher, *Algebraic Topology*, §4.D (Thom classes).
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Set Module Topology

universe w

namespace TauCeti

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] {E : B → Type w}
  [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  {ι : Type w} (W : ι → Set B)

/-- The Thom pairs over finite unions of members of a cover. -/
private def thomCoverDiagram : Finset ι ⥤ TopPair.{w} where
  obj s := thomPairOver F E (⋃ i ∈ s, W i)
  map f := thomPairOverMap F E (biUnion_subset_biUnion_left f.le)
  map_id _ := by simp
  map_comp _ _ := (thomPairOverMap_comp_thomPairOverMap F E _ _).symm

/-- The finite restrictions map into the Thom pair over the entire union. -/
private def thomCoverCocone : Cocone (thomCoverDiagram (F := F) (E := E) W) where
  pt := thomPairOver F E (⋃ i, W i)
  ι :=
    { app _ := thomPairOverMap F E (iUnion₂_subset fun i _ ↦ subset_iUnion W i)
      naturality _ _ _ :=
        (thomPairOverMap_comp_thomPairOverMap F E _ _).trans (Category.comp_id _).symm }

/-- Compatible classes on the finite restrictions extend over their union. -/
private theorem existsUnique_thomCover
    {k : Type*} [CommRing k] (R M : ModuleCat.{w} k) [Module.Projective k R]
    (hWo : ∀ i, IsOpen (W i))
    (hWe : ∀ i, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (v : ∀ s : Finset ι,
      (thomPairOver F E (⋃ i ∈ s, W i)).singularCohomology R k M (finrank ℝ F))
    (hv : ∀ {s t : Finset ι} (hst : s ⊆ t), TopPair.singularCohomologyMap
      (thomPairOverMap F E (biUnion_subset_biUnion_left hst)) _ (v t) = v s) :
    ∃! x : (thomPairOver F E (⋃ i, W i)).singularCohomology R k M (finrank ℝ F),
      ∀ s : Finset ι, TopPair.singularCohomologyMap
        (thomPairOverMap F E (iUnion₂_subset fun i _ ↦ subset_iUnion W i)) _ x = v s := by
  let c := thomCoverCocone (F := F) (E := E) W
  have hfstK : ∀ K : Set c.pt.fst, IsCompact K →
      ∃ s, K ⊆ range (TopPair.Hom.fst (c.ι.app s)) := by
    -- Compact subsets of the total space project into finitely many members of the cover.
    intro K hK
    have hproj := hK.image ((FiberBundle.continuous_proj F E).comp continuous_subtype_val)
    obtain ⟨s, hs⟩ := hproj.elim_finite_subcover W hWo (by rintro _ ⟨v, _, rfl⟩; exact v.2)
    refine ⟨s, fun v hv ↦ ⟨⟨v.1, hs ⟨v, hv, rfl⟩⟩, ?_⟩⟩
    exact thomPairOverMap_fst_apply F E _ _
  have hsndK : ∀ K : Set c.pt.snd, IsCompact K →
      ∃ s, K ⊆ range (TopPair.Hom.snd (c.ι.app s)) := by
    -- The same argument applies to the complement of the zero section.
    intro K hK
    have hproj := hK.image ((FiberBundle.continuous_proj F E).comp continuous_subtype_val)
    obtain ⟨s, hs⟩ := hproj.elim_finite_subcover W hWo (by rintro _ ⟨v, _, rfl⟩; exact v.2.1)
    refine ⟨s, fun v hv ↦ ⟨⟨v.1, hs ⟨v, hv, rfl⟩, v.2.2⟩, ?_⟩⟩
    exact thomPairOverMap_snd_apply F E _ _
  exact TopPair.existsUnique_singularCohomology_of_directedUnion R M c
    (fun s ↦ by
      have h : ⇑(TopPair.Hom.fst (c.ι.app s)) =
          inclusion (preimage_mono (iUnion₂_subset fun i _ ↦ subset_iUnion W i)) :=
        funext (thomPairOverMap_fst_apply F E _)
      exact h.symm ▸ IsEmbedding.inclusion _) hfstK hsndK (finrank ℝ F)
    (fun s m hm ↦ isZero_singularHomology_thomPairOver_biUnion R s
      (fun i _ ↦ hWo i) (fun i _ ↦ hWe i) hm) v (fun f ↦ hv f.le)

/-- Compatible top-degree classes over an arbitrary trivializing open cover glue uniquely.
Compatibility need only be checked after restricting to the fibre over each point of an
overlap. Coefficients are `Hom(C(-; R), M)` over any commutative ring, with `R` projective. -/
theorem existsUnique_singularCohomology_thomPairOver_iUnion
    {k : Type*} [CommRing k] (R M : ModuleCat.{w} k) [Module.Projective k R]
    (hWo : ∀ i, IsOpen (W i))
    (hWe : ∀ i, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (u : ∀ i, (thomPairOver F E (W i)).singularCohomology R k M (finrank ℝ F))
    (hu : ∀ i j b (hi : b ∈ W i) (hj : b ∈ W j),
      TopPair.singularCohomologyMap (fiberThomPairOverMap F E hi) _ (u i) =
        TopPair.singularCohomologyMap (fiberThomPairOverMap F E hj) _ (u j)) :
    ∃! x : (thomPairOver F E (⋃ i, W i)).singularCohomology R k M (finrank ℝ F),
      ∀ i, TopPair.singularCohomologyMap (thomPairOverMap F E (subset_iUnion W i)) _ x = u i := by
  classical
  -- Finite gluing determines compatible classes on the filtered system of finite unions.
  choose v hv using fun s : Finset ι ↦ exists_singularCohomology_thomPairOver_biUnion s
    (fun i _ ↦ hWo i) (fun i _ ↦ hWe i) u (fun i _ j _ ↦ hu i j)
  have hfib (s : Finset ι) (i : ι) (hi : i ∈ s) (b : B) (hb : b ∈ W i) :
      TopPair.singularCohomologyMap
          (fiberThomPairOverMap F E (mem_iUnion₂_of_mem hi hb)) _ (v s) =
        TopPair.singularCohomologyMap (fiberThomPairOverMap F E hb) _ (u i) := by
    simpa only [← TopPair.singularCohomologyMap_comp_apply,
      fiberThomPairOverMap_comp_thomPairOverMap] using
        congrArg (fun a ↦ TopPair.singularCohomologyMap (fiberThomPairOverMap F E hb) _ a)
          (hv s i hi)
  have hcompat {s t : Finset ι} (hst : s ⊆ t) : TopPair.singularCohomologyMap
      (thomPairOverMap F E (biUnion_subset_biUnion_left hst)) _ (v t) = v s := by
    refine singularCohomology_thomPairOver_biUnion_ext s (fun i _ ↦ hWo i)
      (fun i _ ↦ hWe i) fun b hb ↦ ?_
    obtain ⟨i, hi, hbi⟩ := mem_iUnion₂.1 hb
    rw [hfib s i hi b hbi]
    rw [← TopPair.singularCohomologyMap_comp_apply,
      fiberThomPairOverMap_comp_thomPairOverMap]
    exact hfib t i (hst hi) b hbi
  obtain ⟨x, hx, huniq⟩ := existsUnique_thomCover W R M hWo hWe v hcompat
  have hxi (i : ι) :
      TopPair.singularCohomologyMap (thomPairOverMap F E (subset_iUnion W i)) _ x = u i := by
    have h := congrArg (fun a ↦ TopPair.singularCohomologyMap
      (thomPairOverMap F E (Finset.subset_set_biUnion_of_mem (Finset.mem_singleton_self i)))
        (finrank ℝ F) a) (hx {i})
    rw [← TopPair.singularCohomologyMap_comp_apply,
      thomPairOverMap_comp_thomPairOverMap] at h
    exact h.trans (hv {i} i (Finset.mem_singleton_self i))
  refine ⟨x, hxi, fun y hy ↦ huniq y fun s ↦ ?_⟩
  refine singularCohomology_thomPairOver_biUnion_ext s (fun i _ ↦ hWo i)
    (fun i _ ↦ hWe i) fun b hb ↦ ?_
  obtain ⟨i, hi, hbi⟩ := mem_iUnion₂.1 hb
  rw [hfib s i hi b hbi]
  rw [← TopPair.singularCohomologyMap_comp_apply,
    fiberThomPairOverMap_comp_thomPairOverMap]
  have h := congrArg
    (fun a ↦ TopPair.singularCohomologyMap (fiberThomPairOverMap F E hbi) _ a) (hy i)
  simpa only [← TopPair.singularCohomologyMap_comp_apply,
    fiberThomPairOverMap_comp_thomPairOverMap] using h

end TauCeti
