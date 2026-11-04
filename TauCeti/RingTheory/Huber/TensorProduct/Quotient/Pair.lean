/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Quotient.Basic
public import TauCeti.RingTheory.Huber.QuotientMapping

/-!
# Quotient mappings of completed tensor products of Huber pairs

Completed tensor products preserve quotient mappings of Huber pairs along adic structure maps.
The induced map is an open surjection on rings, and its target plus ring is the integral closure
of the image of its source plus ring. Thus completed base change preserves the quotient-pair
condition in presentations of affinoid algebras, including the specified integral elements.

The ring-level open quotient theorem is `CompletedTensor.isOpenQuotientMap_map`. To identify
plus rings, the integral closure of the image of the source tensor plus ring is open and hence
closed. The target factor plus rings map into it by integrality, so the universal property of
the completed tensor plus ring gives the reverse inclusion. Completeness and separation of the
input rings, noetherianity and sheafiness are not required.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3, proof of Proposition 3.7.
* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.2, proof of Proposition 1.2.2(2).
-/

public section

namespace TauCeti.Huber.Pair.completedTensor

variable {A B C B' C' : Type*} [CommRing A] [CommRing B] [CommRing C]
  [CommRing B'] [CommRing C'] [Algebra A B] [Algebra A C] [Algebra A B'] [Algebra A C']
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [TopologicalSpace B'] [TopologicalSpace C']
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsTopologicalRing B'] [IsTopologicalRing C']
  [IsHuberRing B] [IsHuberRing C] [IsHuberRing B'] [IsHuberRing C']
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]
  [IsAdicHom (algebraMap A B')] [IsAdicHom (algebraMap A C')]
  {S : Pair B} {T : Pair C} {S' : Pair B'} {T' : Pair C'}

/-- **Completed tensor products preserve quotient mappings of Huber pairs.** The induced map
is an open surjection, and the target plus ring is the integral closure of the image of the
source plus ring. In particular this applies to completed base change, taking either factor
map to be the identity. -/
theorem isQuotientMapping_map (f : Hom S S') (g : Hom T T')
    (hfA : f.toRingHom.comp (algebraMap A B) = algebraMap A B')
    (hgA : g.toRingHom.comp (algebraMap A C) = algebraMap A C')
    (hf : f.IsQuotientMapping) (hg : g.IsQuotientMapping) :
    (map (RingHom.id A) f g hfA hgA).IsQuotientMapping := by
  let F := map (RingHom.id A) f g hfA hgA
  have hF : IsOpenQuotientMap F.toRingHom := by
    simpa only [F, toRingHom_map] using
      CompletedTensor.isOpenQuotientMap_map hfA hgA hf.isOpenQuotientMap hg.isOpenQuotientMap
  let R := (integralClosure ((S.completedTensor A T).plus.map F.toRingHom)
    (CompletedTensor A B' C')).toSubring
  have hopen : IsOpen ((S.completedTensor A T).plus.map F.toRingHom :
      Set (CompletedTensor A B' C')) := by
    rw [Subring.coe_map]
    exact hF.isOpenMap _ (S.completedTensor A T).isRingOfIntegralElements.isOpen
  have hR : IsClosed (R : Set (CompletedTensor A B' C')) :=
    R.toAddSubgroup.isClosed_of_isOpen (isOpen_integralClosure_toSubring hopen)
  refine (Hom.isQuotientMapping_iff_isOpenQuotientMap_and_isIntegral F).mpr
    ⟨hF, fun x hx ↦ ?_⟩
  apply (mem_integralClosure_iff _ _).mp
  refine S'.completedTensor_plus_le_comap T' hR
    (f := RingHom.id _) continuous_id (fun b hb ↦ ?_) (fun c hc ↦ ?_) hx
  · let d : S.plus.map f.toRingHom →+* (S.completedTensor A T).plus.map F.toRingHom :=
      (CompletedTensor.inl A B' C').restrict _ _ fun _ ⟨a, ha, hab⟩ ↦
        Subring.mem_map.mpr ⟨_, S.inl_mem_completedTensor_plus T ha, by simp [F, ← hab]⟩
    exact (mem_integralClosure_iff _ _).mpr <|
      (hf.mem_plus_iff.mp hb).map_of_comp_eq d (CompletedTensor.inl A B' C') (by ext; rfl)
  · let d : T.plus.map g.toRingHom →+* (S.completedTensor A T).plus.map F.toRingHom :=
      (CompletedTensor.inr A B' C').restrict _ _ fun _ ⟨a, ha, hac⟩ ↦
        Subring.mem_map.mpr ⟨_, S.inr_mem_completedTensor_plus T ha, by simp [F, ← hac]⟩
    exact (mem_integralClosure_iff _ _).mpr <|
      (hg.mem_plus_iff.mp hc).map_of_comp_eq d (CompletedTensor.inr A B' C') (by ext; rfl)

end TauCeti.Huber.Pair.completedTensor
