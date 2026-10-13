/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Pair

/-!
# Plus rings under weighted coefficient quotients

A morphism of Huber pairs acts coefficientwise on completed weighted restricted series.
When the coefficient morphism is a quotient mapping and the target weights are the images of
the source weights, the induced morphism is a quotient mapping as soon as its underlying ring
map is an open quotient map. The additional conclusion is that the target plus ring is the
integral closure of the image of the source plus ring.

This separates the plus-ring calculation from the lifting of restricted coefficient families.
It applies to the coefficient quotient occurring between two finite-type presentations, with
arbitrary weights and without assuming that the base ring is Tate. Constants in the target
plus ring are integral over the images of source constants; weighted variables lift to source
weighted variables. The generator criterion
`TauCeti.Huber.Pair.Hom.isQuotientMapping_of_isIntegral_weighted` then controls the entire
completed plus ring.

The generator calculation generalizes the unweighted coefficient quotient in
`TauCeti.Huber.Pair.Hom.IsTopologicallyFiniteType.comp`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark and Definition 8.41,
  Definition 8.42 and Proposition 8.46.
-/

public section

open UniformSpace

namespace TauCeti.Huber.Pair.Hom

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  {S : Pair A} {U : Pair B} {k : ℕ} {T : Fin k → Set A} {T' : Fin k → Set B}

/-- The morphism of completed weighted Huber pairs induced by a coefficient morphism carrying
each source weight into the corresponding target weight. -/
noncomputable def weightedMapCompletion (f : Hom S U) (hT : IsWeightFamily T)
    (hT' : IsWeightFamily T') (hTT' : ∀ i, f.toRingHom '' T i ⊆ T' i) :
    Hom (S.weighted hT).completion (U.weighted hT').completion where
  toRingHom := Huber.weightedMapCompletion f.continuous_toRingHom hT hT' hTT'
  continuous_toRingHom := continuous_weightedMapCompletion ..
  map_mem_plus := weighted_completion_plus_le_comap_weightedMapCompletion hT f hT' hTT'

/-- The underlying ring map is the coefficientwise map on completions. -/
@[simp]
theorem toRingHom_weightedMapCompletion (f : Hom S U) (hT : IsWeightFamily T)
    (hT' : IsWeightFamily T') (hTT' : ∀ i, f.toRingHom '' T i ⊆ T' i) :
    (f.weightedMapCompletion hT hT' hTT').toRingHom =
      Huber.weightedMapCompletion f.continuous_toRingHom hT hT' hTT' :=
  (rfl)

/-- The coefficientwise morphism commutes with the structure morphisms of the weighted pairs.
-/
@[simp]
theorem weightedMapCompletion_comp_weightedCompletionHom (f : Hom S U)
    (hT : IsWeightFamily T) (hT' : IsWeightFamily T')
    (hTT' : ∀ i, f.toRingHom '' T i ⊆ T' i) :
    (f.weightedMapCompletion hT hT' hTT').comp (S.weightedCompletionHom hT) =
      (U.weightedCompletionHom hT').comp f := by
  apply Hom.ext
  ext a
  simp [algebraMap_completion_weightedRestrictedSubring_apply]

/-- A coefficient quotient mapping induces a quotient mapping of completed weighted pairs
provided that the target weights are exactly its images and the induced ring map is an open
quotient map. In particular, the target plus ring is the integral closure of the image plus ring.
No finiteness, completeness, separation or Tate hypothesis is imposed on the coefficient rings.
-/
theorem IsQuotientMapping.weightedMapCompletion {f : Hom S U} (hf : f.IsQuotientMapping)
    (hT : IsWeightFamily T) (hT' : IsWeightFamily T')
    (hTT' : ∀ i, f.toRingHom '' T i = T' i)
    (hF : IsOpenQuotientMap
      (Huber.weightedMapCompletion f.continuous_toRingHom hT hT' (fun i ↦ (hTT' i).le))) :
    (f.weightedMapCompletion hT hT' (fun i ↦ (hTT' i).le)).IsQuotientMapping := by
  let F := f.weightedMapCompletion hT hT' (fun i ↦ (hTT' i).le)
  have hFC (a : A) :
      F.toRingHom (weightedC T hT a : weightedRestrictedSubring T hT) =
        (weightedC T' hT' (f.toRingHom a) : weightedRestrictedSubring T' hT') := by
    simp [F, Huber.weightedMapCompletion_coe]
  refine Hom.isQuotientMapping_of_isIntegral_weighted F hF (fun b hb ↦ ?_)
    (fun i t ht ↦ ?_)
  · -- Transport the integral equation for a target constant along its constant-series map.
    let c : B →+* Completion (weightedRestrictedSubring T' hT') :=
      Completion.coeRingHom.comp (weightedC T' hT')
    let d : S.plus.map f.toRingHom →+* (S.weighted hT).completion.plus.map F.toRingHom :=
      c.restrict _ _ fun _ ⟨a, ha, hab⟩ ↦ Subring.mem_map.mpr
        ⟨_, S.weightedC_mem_weighted_completion_plus hT ha, by rw [← hab]; exact hFC a⟩
    exact (hf.mem_plus_iff.mp hb).map_of_comp_eq d c (by ext; rfl)
  · -- Every target weighted variable is the image of a source weighted variable.
    obtain ⟨a, ha, rfl⟩ := (hTT' i) ▸ ht
    have hFX :
        F.toRingHom (weightedC T hT a * weightedX T hT i : weightedRestrictedSubring T hT) =
          (weightedC T' hT' (f.toRingHom a) * weightedX T' hT' i :
            weightedRestrictedSubring T' hT') := by
      simp [F, Huber.weightedMapCompletion_coe]
    rw [← hFX]
    exact isIntegral_algebraMap (R := (S.weighted hT).completion.plus.map F.toRingHom)
      (x := ⟨_, Subring.mem_map.mpr
        ⟨_, S.weightedC_mul_weightedX_mem_weighted_completion_plus hT ha, rfl⟩⟩)

end TauCeti.Huber.Pair.Hom
