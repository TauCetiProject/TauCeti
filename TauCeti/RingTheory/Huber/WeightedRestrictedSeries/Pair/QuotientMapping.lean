/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.QuotientMapping
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Pair.Completion

/-!
# Plus rings under weighted coefficient quotients

A morphism of Huber pairs acts coefficientwise on completed weighted restricted series.
When the coefficient morphism is a quotient mapping and the target weights are the images of
the source weights, the induced morphism is a quotient mapping as soon as its underlying ring
map is an open quotient map. The additional conclusion is that the target plus ring is the
integral closure of the image of the source plus ring.

More generally, it suffices that the target coefficient plus ring be integral over the image
of the source coefficient plus ring, without requiring the coefficient morphism to be open.

The induced ring map is assumed to be an open quotient map; the theorems prove the
integral-closure condition on plus rings. They apply to coefficient quotients between finite-type
presentations, with arbitrary weights and without assuming that the base ring is Tate. Constants
in the target plus ring are integral over the images of source constants; weighted variables lift to
source weighted variables. The generator criterion
`TauCeti.Huber.Pair.Hom.isQuotientMapping_of_isIntegral_weighted` then controls the entire
completed plus ring.

The unweighted pair-composition theorem `TauCeti.Huber.Pair.Hom.IsTopologicallyFiniteType.comp`
uses `TauCeti.Huber.Pair.Hom.IsQuotientMapping.weightedMapCompletion`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark and Definition 8.41,
  Definition 8.42 and Proposition 8.46.
-/

public section

open UniformSpace

namespace TauCeti.Huber.Pair

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  {S : Pair A} {k : ℕ} {T : Fin k → Set A} {hT : IsWeightFamily T}

/-- **A morphism onto a completed weighted pair is a quotient mapping** as soon as it is an open
quotient map and the constants from `A⁺` and the weighted variables `t Xᵢ` (`t ∈ Tᵢ`) are
integral over the image of the source plus ring. -/
theorem Hom.isQuotientMapping_of_isIntegral_weighted {W : Pair B}
    (θ : Hom W (S.weighted hT).completion) (hθ : IsOpenQuotientMap θ.toRingHom)
    (hC : ∀ a ∈ S.plus, IsIntegral (W.plus.map θ.toRingHom)
      ((weightedC T hT a : weightedRestrictedSubring T hT) :
        Completion (weightedRestrictedSubring T hT)))
    (hX : ∀ i, ∀ t ∈ T i, IsIntegral (W.plus.map θ.toRingHom)
      ((weightedC T hT t * weightedX T hT i : weightedRestrictedSubring T hT) :
        Completion (weightedRestrictedSubring T hT))) :
    θ.IsQuotientMapping := by
  let R := (integralClosure (W.plus.map θ.toRingHom)
    (Completion (weightedRestrictedSubring T hT))).toSubring
  -- `R` contains the open image of `W⁺`, so it is open, hence closed
  have hopen :
      IsOpen (W.plus.map θ.toRingHom : Set (Completion (weightedRestrictedSubring T hT))) := by
    rw [Subring.coe_map]
    exact hθ.isOpenMap _ W.isRingOfIntegralElements.isOpen
  have hR : IsClosed (R : Set (Completion (weightedRestrictedSubring T hT))) :=
    R.toAddSubgroup.isClosed_of_isOpen <| AddSubgroup.isOpen_mono
      (H₁ := (W.plus.map θ.toRingHom).toAddSubgroup)
      (fun x hx ↦ isIntegral_algebraMap (R := W.plus.map θ.toRingHom) (x := ⟨x, hx⟩)) hopen
  exact (isQuotientMapping_iff_isOpenQuotientMap_and_isIntegral θ).mpr
    ⟨hθ, fun b hb ↦ S.weighted_completion_plus_le hT hR hC hX hb⟩

end TauCeti.Huber.Pair

namespace TauCeti.Huber.Pair.Hom

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  {S : Pair A} {U : Pair B} {k : ℕ} {T : Fin k → Set A} {T' : Fin k → Set B}

/-- A coefficient morphism whose target plus ring is integral over the image of its source plus
ring induces a quotient mapping of completed weighted pairs provided that the target weights
are exactly its images and the induced ring map is an open quotient map. In particular, the
target plus ring is the integral closure of the image plus ring.
No finiteness, completeness, separation or Tate hypothesis is imposed on the coefficient rings.
-/
theorem isQuotientMapping_weightedMapCompletion_of_isIntegral (f : Hom S U)
    (hplus : ∀ b ∈ U.plus, IsIntegral (S.plus.map f.toRingHom) b)
    (hT : IsWeightFamily T) (hT' : IsWeightFamily T')
    (hTT' : ∀ i, f.toRingHom '' T i = T' i)
    (hF : IsOpenQuotientMap
      (Huber.weightedMapCompletion f.continuous_toRingHom hT hT' (fun i ↦ (hTT' i).le))) :
    (f.weightedMapCompletion hT hT' (fun i ↦ (hTT' i).le)).IsQuotientMapping := by
  let F := f.weightedMapCompletion hT hT' (fun i ↦ (hTT' i).le)
  have hF : IsOpenQuotientMap F.toRingHom := by
    simpa only [F, toRingHom_weightedMapCompletion] using hF
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
    exact (hplus b hb).map_of_comp_eq d c (by ext; rfl)
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

/-- A coefficient quotient mapping induces a quotient mapping of completed weighted pairs
provided that the target weights are exactly its images and the induced ring map is an open
quotient map. No finiteness, completeness, separation or Tate hypothesis is imposed on the
coefficient rings. -/
theorem IsQuotientMapping.weightedMapCompletion {f : Hom S U} (hf : f.IsQuotientMapping)
    (hT : IsWeightFamily T) (hTT' : ∀ i, f.toRingHom '' T i = T' i) :
    let hT' : IsWeightFamily T' := by
      simpa only [hTT'] using hT.image f.continuous_toRingHom hf.isOpenQuotientMap.isOpenMap
    IsOpenQuotientMap
      (Huber.weightedMapCompletion f.continuous_toRingHom hT hT' (fun i ↦ (hTT' i).le)) →
    (f.weightedMapCompletion hT hT' (fun i ↦ (hTT' i).le)).IsQuotientMapping := by
  dsimp only
  exact isQuotientMapping_weightedMapCompletion_of_isIntegral f
    (fun _ hb ↦ hf.mem_plus_iff.mp hb) hT _ hTT'

end TauCeti.Huber.Pair.Hom
