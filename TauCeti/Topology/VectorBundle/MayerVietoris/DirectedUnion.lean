/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.MayerVietoris.Basic
public import TauCeti.AlgebraicTopology.Singular.DirectedUnion

/-!
# Thom-pair vanishing over arbitrary bases

For a finite-dimensional real vector bundle `E → B` of rank `r`, the relative singular
homology of its total space modulo the nonzero vectors vanishes in degrees below `r`.
No compactness, separation, paracompactness or orientation of the base is needed.

Finite unions of trivializing open sets already have this vanishing by
`TauCeti.isZero_singularHomology_thomPairOver_biUnion`. Their Thom pairs form a filtered
diagram. Every compact subset of the total space, or of its nonzero subspace, projects
into finitely many trivializing sets. Thus `TopPair.isColimitMapCoconeSingularHomology`
identifies the homology of the whole Thom pair with a filtered colimit of zero objects.
Universal coefficients then gives the same vanishing for relative cohomology.

This is the below-rank vanishing used in constructing Thom classes from local fibre
generators. It does not identify the degree-r group or construct a Thom class.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, §10, Lemma 10.3 and
  the proof of Theorem 10.4 (finite trivializing unions and directed unions of chains).
* A. Hatcher, *Algebraic Topology*, §4.D, proof of Theorem 4D.10.
-/

public noncomputable section

open Bundle CategoryTheory Limits Set Module

universe w v u

namespace TauCeti

variable {B : Type w} [TopologicalSpace B] {F : Type w}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- The homology of the Thom pair of a real vector bundle vanishes below the rank,
with coefficients in an abelian category with exact filtered colimits. The base is arbitrary. -/
theorem isZero_singularHomology_thomPair
    {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
    [HasFilteredColimitsOfSize.{w, w} C] [AB5OfSize.{w, w} C]
    (R : C) {n : ℕ} (hn : n < finrank ℝ F) :
    IsZero ((thomPair F E).singularHomology R n) := by
  classical
  -- Index the restrictions by finite collections of trivializing charts, including the empty one.
  let U (s : Finset B) : Set B := ⋃ b ∈ s, (trivializationAt F E b).baseSet
  have hU : Monotone U := fun _ _ hst ↦ biUnion_subset_biUnion_left hst
  let D : Finset B ⥤ TopPair.{w} :=
    { obj s := thomPairOver F E (U s)
      map f := TopPair.ofHom
        (TopCat.ofHom (ContinuousMap.inclusion (preimage_mono (hU f.le))))
        (TopCat.ofHom (ContinuousMap.inclusion
          (inter_subset_inter_left _ (preimage_mono (hU f.le))))) (by ext; rfl)
      map_id _ := TopPair.hom_ext_of_fst _ (by ext; rfl)
      map_comp _ _ := TopPair.hom_ext_of_fst _ (by ext; rfl) }
  let c : Cocone D :=
    { pt := thomPair F E
      ι :=
        { app s := TopPair.ofHom (TopCat.ofHom (ContinuousMap.subtypeVal _))
            (TopCat.ofHom (ContinuousMap.inclusion inter_subset_right)) (by ext; rfl)
          naturality _ _ _ := TopPair.hom_ext_of_fst _ (by ext; rfl) } }
  -- Compact images in the base are absorbed by one finite trivializing union.
  have hK (K : Set (TotalSpace F E)) (hK : IsCompact K) :
      ∃ s : Finset B, K ⊆ π F E ⁻¹' U s := by
    obtain ⟨s, hs⟩ := (hK.image (FiberBundle.continuous_proj F E)).elim_finite_subcover
      (fun b : B ↦ (trivializationAt F E b).baseSet)
      (fun b ↦ (trivializationAt F E b).open_baseSet)
      (fun b _ ↦ mem_iUnion.2 ⟨b, mem_baseSet_trivializationAt F E b⟩)
    exact ⟨s, fun p hp ↦ hs (mem_image_of_mem _ hp)⟩
  -- Check absorption for both spaces of the pair, not just the total space.
  have hc := TopPair.isColimitMapCoconeSingularHomology R n c
    (fun _ ↦ Topology.IsEmbedding.subtypeVal) (fun K hcomp ↦ by
      obtain ⟨s, hs⟩ := hK K hcomp
      exact ⟨s, fun p hp ↦ ⟨⟨p, hs hp⟩, rfl⟩⟩) (fun K hcomp ↦ by
      obtain ⟨s, hs⟩ := hK (Subtype.val '' K) (hcomp.image continuous_subtype_val)
      exact ⟨s, fun p hp ↦ ⟨⟨p.1, hs (mem_image_of_mem _ hp), p.2⟩, rfl⟩⟩)
  -- All objects of the homology diagram vanish, so its colimit vanishes as well.
  rw [← TopPair.singularHomologyFunctor_obj (thomPair F E) R n, IsZero.iff_id_eq_zero]
  apply hc.hom_ext
  intro s
  have hz : IsZero ((TopPair.singularHomologyFunctor R n).obj (D.obj s)) := by
    rw [TopPair.singularHomologyFunctor_obj]
    exact isZero_singularHomology_thomPairOver_biUnion R s
      (fun b _ ↦ (trivializationAt F E b).open_baseSet)
      (fun b _ ↦ ⟨trivializationAt F E b, inferInstance, subset_rfl⟩) hn
  exact hz.eq_of_src _ _

/-- The relative cohomology of a real vector bundle modulo its nonzero vectors vanishes
below the rank, over an arbitrary base and with projective chain coefficients. -/
theorem isZero_singularCohomology_thomPair
    {k : Type*} [CommRing k] (R M : ModuleCat.{w} k) [Module.Projective k R]
    {n : ℕ} (hn : n < finrank ℝ F) :
    IsZero ((thomPair F E).singularCohomology R k M n) :=
  TopPair.isZero_singularCohomology_of_isZero_singularHomology _ R M n fun _ hj ↦
    isZero_singularHomology_thomPair R (hj.trans_lt hn)

end TauCeti
