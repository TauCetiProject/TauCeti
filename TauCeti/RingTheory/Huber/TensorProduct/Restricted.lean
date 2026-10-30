/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Completion
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Adic
public import TauCeti.RingTheory.Huber.WeightedEval.Completion
public import Mathlib.Topology.Homeomorph.Defs

import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Completed base change of weighted restricted power series

Let `λ : A → B` be an adic homomorphism of Huber rings and `T` a weight family on `A`. Write
`A⟨X⟩_T` for the completion of the weighted restricted power series over `A`, and `B⟨X⟩_{T_B}`
for those over `B` with the image weights `T_B i = λ(T i)`, which are again a weight family
(`TauCeti.Huber.IsAdicHom.isWeightFamily_image`). This file proves that the natural map

```text
A⟨X⟩_T ⊗̂_A B → B⟨X⟩_{T_B},    f ⊗ b ↦ λ(f) · b,
```

induced by the coefficientwise map `λ : A⟨X⟩_T → B⟨X⟩_{T_B}` and the structure map of `B`, is an
isomorphism of topological rings. Its inverse sends the constant series `b` to `1 ⊗ b` and the
variable `Xᵢ` to `Xᵢ ⊗ 1`.

Both maps come from universal properties: the forward map from that of the completed tensor
product (`TauCeti.Huber.CompletedTensor.lift`), the inverse from Wedhorn's Proposition 5.50 for
`B⟨X⟩_{T_B}` (`TauCeti.Huber.weightedEvalHomCompletion`). For the latter the weighted monomials
`λ(t) Xᵛ ⊗ 1` must be bounded; they are the images of the bounded weighted monomials of
`A⟨X⟩_T` under the left coprojection, which is adic. The two composites are the identity
because continuous maps out of either side are determined on generators.

Only the topological rings are compared here; rings of integral elements are not.

## Main definitions

* `TauCeti.Huber.CompletedTensor.weightedRestrictedEquiv`: the ring isomorphism
  `A⟨X⟩_T ⊗̂_A B ≃+* B⟨X⟩_{T_B}`.

## Main results

* `TauCeti.Huber.CompletedTensor.isHomeomorph_weightedRestrictedEquiv`: it is a homeomorphism.
* `TauCeti.Huber.CompletedTensor.weightedRestrictedEquiv_inl` and `…_inr`: it is the
  coefficientwise map on the left factor and the structure map on the right factor.
* `TauCeti.Huber.CompletedTensor.weightedRestrictedEquiv_symm_weightedC` and `…_symm_weightedX`:
  the inverse sends constants to the right factor and each variable to the variable of the left
  factor.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3, Lemma 3.5(i) and the proof of Proposition 3.7.
* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, §1.2, proof of
  Proposition 1.2.2.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 5.50.
-/

public section

open UniformSpace

namespace TauCeti.Huber

namespace CompletedTensor

variable {k : ℕ} {A : Type*} (B : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsHuberRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
  [Algebra A B] [hAB : IsAdicHom (algebraMap A B)] {T : Fin k → Set A} (hT : IsWeightFamily T)

/-- The coefficientwise map `A⟨X⟩_T → B⟨X⟩_{T_B}` on completions. -/
private noncomputable abbrev coeffMap :
    Completion (weightedRestrictedSubring T hT) →+*
      Completion (weightedRestrictedSubring (fun i ↦ algebraMap A B '' T i)
        (hAB.isWeightFamily_image hT)) :=
  weightedMapCompletion hAB.continuous hT _ fun _ ↦ subset_rfl

/-- The coefficientwise map is compatible with the two coefficient maps out of `A`. -/
private theorem coeffMap_comp_algebraMap :
    (coeffMap B hT).comp (algebraMap A (Completion (weightedRestrictedSubring T hT))) =
      (algebraMap B (Completion (weightedRestrictedSubring (fun i ↦ algebraMap A B '' T i)
        (hAB.isWeightFamily_image hT)))).comp (algebraMap A B) := by
  ext a
  simp

/-- The forward map `A⟨X⟩_T ⊗̂_A B → B⟨X⟩_{T_B}`. -/
private noncomputable def toWeighted :
    CompletedTensor A (Completion (weightedRestrictedSubring T hT)) B →+*
      Completion (weightedRestrictedSubring (fun i ↦ algebraMap A B '' T i)
        (hAB.isWeightFamily_image hT)) :=
  lift (coeffMap B hT) (algebraMap B _) (coeffMap_comp_algebraMap B hT)
    (continuous_weightedMapCompletion _ _ _ _)
    (continuous_algebraMap_completion_weightedRestrictedSubring k B _)

omit [IsHuberRing B] in
/-- The weighted monomials `λ(t) Xᵛ ⊗ 1` are bounded in `A⟨X⟩_T ⊗̂_A B`: they are the images of
the weighted monomials of `A⟨X⟩_T` under the adic left coprojection. -/
private theorem isWeightBounded_inr :
    IsWeightBounded (inr A (Completion (weightedRestrictedSubring T hT)) B)
      (fun i ↦ algebraMap A B '' T i)
      fun i ↦ inl A (Completion (weightedRestrictedSubring T hT)) B
        (weightedX T hT i : weightedRestrictedSubring T hT) := by
  have h := (isAdicHom_inl A (Completion (weightedRestrictedSubring T hT)) B).isBounded_image
    ((isWeightBounded_iff _ _ _).mp (isWeightBounded_completion_weightedX hT))
  refine (isWeightBounded_iff _ _ _).mpr (h.subset ?_)
  rintro _ ⟨_, ⟨ν, rfl⟩, _, hs, rfl⟩
  rw [← image_weightPow] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  refine ⟨_, ⟨_, ⟨ν, rfl⟩, t, ht, rfl⟩, ?_⟩
  simp only [map_mul, map_prod, map_pow, inr_algebraMap, ← inl_algebraMap]

/-- The inverse map `B⟨X⟩_{T_B} → A⟨X⟩_T ⊗̂_A B`, from the universal property of `B⟨X⟩_{T_B}`. -/
private noncomputable def ofWeighted :
    Completion (weightedRestrictedSubring (fun i ↦ algebraMap A B '' T i)
        (hAB.isWeightFamily_image hT)) →+*
      CompletedTensor A (Completion (weightedRestrictedSubring T hT)) B :=
  weightedEvalHomCompletion _ (continuous_inr _ _ _).continuousAt (isWeightBounded_inr B hT)

private theorem continuous_toWeighted : Continuous (toWeighted B hT) :=
  continuous_lift _ _ _ _ _

private theorem continuous_ofWeighted : Continuous (ofWeighted B hT) :=
  continuous_weightedEvalHomCompletion _ _ _

private theorem ofWeighted_weightedC (b : B) :
    ofWeighted B hT (weightedC _ (hAB.isWeightFamily_image hT) b) =
      inr A (Completion (weightedRestrictedSubring T hT)) B b := by
  rw [ofWeighted, weightedEvalHomCompletion_coe, weightedEvalHom_weightedC]

private theorem ofWeighted_weightedX (i : Fin k) :
    ofWeighted B hT (weightedX _ (hAB.isWeightFamily_image hT) i) =
      inl A (Completion (weightedRestrictedSubring T hT)) B
        (weightedX T hT i : weightedRestrictedSubring T hT) := by
  rw [ofWeighted, weightedEvalHomCompletion_coe, weightedEvalHom_weightedX]

private theorem toWeighted_inl (f : Completion (weightedRestrictedSubring T hT)) :
    toWeighted B hT (inl _ _ _ f) = coeffMap B hT f :=
  lift_inl _ _ _ _ _ f

private theorem toWeighted_inr (b : B) :
    toWeighted B hT (inr _ _ _ b) =
      algebraMap B (Completion (weightedRestrictedSubring (fun i ↦ algebraMap A B '' T i)
        (hAB.isWeightFamily_image hT))) b :=
  lift_inr _ _ _ _ _ b

private theorem ofWeighted_comp_toWeighted :
    (ofWeighted B hT).comp (toWeighted B hT) = RingHom.id _ := by
  refine hom_ext ((continuous_ofWeighted B hT).comp (continuous_toWeighted B hT)) continuous_id
    ?_ ?_
  · -- on the left factor, compare the two maps on the constants and the variables of `A⟨X⟩_T`
    refine completion_weightedRestrictedSubring_ringHom_ext_of_continuous hT
      (((continuous_ofWeighted B hT).comp (continuous_toWeighted B hT)).comp (continuous_inl _ _ _))
      (continuous_inl _ _ _) (fun a ↦ ?_) fun i ↦ ?_
    · simp only [RingHom.comp_apply, RingHom.id_apply, toWeighted_inl, weightedMapCompletion_coe,
        weightedMap_weightedC, ofWeighted_weightedC, inr_algebraMap, ← inl_algebraMap]
      rw [algebraMap_completion_weightedRestrictedSubring_apply]
    · simp only [RingHom.comp_apply, RingHom.id_apply, toWeighted_inl, weightedMapCompletion_coe,
        weightedMap_weightedX, ofWeighted_weightedX]
  · ext b
    simp only [RingHom.comp_apply, RingHom.id_apply, toWeighted_inr,
      algebraMap_completion_weightedRestrictedSubring_apply, ofWeighted_weightedC]

private theorem toWeighted_comp_ofWeighted :
    (toWeighted B hT).comp (ofWeighted B hT) = RingHom.id _ := by
  refine completion_weightedRestrictedSubring_ringHom_ext_of_continuous _
    ((continuous_toWeighted B hT).comp (continuous_ofWeighted B hT)) continuous_id (fun b ↦ ?_)
    fun i ↦ ?_
  · simp only [RingHom.comp_apply, RingHom.id_apply, ofWeighted_weightedC, toWeighted_inr,
      algebraMap_completion_weightedRestrictedSubring_apply]
  · simp only [RingHom.comp_apply, RingHom.id_apply, ofWeighted_weightedX, toWeighted_inl,
      weightedMapCompletion_coe, weightedMap_weightedX]

/-- **Completed base change of weighted restricted power series.** For an adic homomorphism
`λ : A → B` of Huber rings and a weight family `T` on `A`, the completed tensor product
`A⟨X⟩_T ⊗̂_A B` is isomorphic to `B⟨X⟩_{λ(T)}`, the completed weighted restricted power series
over `B` with the image weights. The isomorphism is `λ` coefficientwise on the left factor and
the structure map on the right factor, and it is a homeomorphism
(`TauCeti.Huber.CompletedTensor.isHomeomorph_weightedRestrictedEquiv`). -/
noncomputable def weightedRestrictedEquiv :
    CompletedTensor A (Completion (weightedRestrictedSubring T hT)) B ≃+*
      Completion (weightedRestrictedSubring (fun i ↦ algebraMap A B '' T i)
        (hAB.isWeightFamily_image hT)) :=
  RingEquiv.ofRingHom (toWeighted B hT) (ofWeighted B hT) (toWeighted_comp_ofWeighted B hT)
    (ofWeighted_comp_toWeighted B hT)

/-- On the left factor the isomorphism is the coefficientwise map `A⟨X⟩_T → B⟨X⟩_{λ(T)}`. -/
@[simp] theorem weightedRestrictedEquiv_inl (f : Completion (weightedRestrictedSubring T hT)) :
    weightedRestrictedEquiv B hT (inl _ _ _ f) =
      weightedMapCompletion hAB.continuous hT (hAB.isWeightFamily_image hT)
        (fun _ ↦ subset_rfl) f :=
  toWeighted_inl B hT f

/-- On the right factor the isomorphism is the structure map `B → B⟨X⟩_{λ(T)}`. -/
@[simp] theorem weightedRestrictedEquiv_inr (b : B) :
    weightedRestrictedEquiv B hT (inr _ _ _ b) =
      algebraMap B (Completion (weightedRestrictedSubring (fun i ↦ algebraMap A B '' T i)
        (hAB.isWeightFamily_image hT))) b :=
  toWeighted_inr B hT b

/-- The inverse sends the constant series `b` to `1 ⊗ b`. -/
@[simp] theorem weightedRestrictedEquiv_symm_weightedC (b : B) :
    (weightedRestrictedEquiv B hT).symm
        (weightedC _ (hAB.isWeightFamily_image hT) b :
          weightedRestrictedSubring (fun i ↦ algebraMap A B '' T i)
            (hAB.isWeightFamily_image hT)) =
      inr A (Completion (weightedRestrictedSubring T hT)) B b :=
  ofWeighted_weightedC B hT b

/-- The inverse sends the variable `Xᵢ` of `B⟨X⟩_{λ(T)}` to `Xᵢ ⊗ 1`. -/
@[simp] theorem weightedRestrictedEquiv_symm_weightedX (i : Fin k) :
    (weightedRestrictedEquiv B hT).symm
        (weightedX _ (hAB.isWeightFamily_image hT) i :
          weightedRestrictedSubring (fun i ↦ algebraMap A B '' T i)
            (hAB.isWeightFamily_image hT)) =
      inl A (Completion (weightedRestrictedSubring T hT)) B
        (weightedX T hT i : weightedRestrictedSubring T hT) :=
  ofWeighted_weightedX B hT i

/-- The isomorphism is continuous. -/
@[fun_prop] theorem continuous_weightedRestrictedEquiv :
    Continuous (weightedRestrictedEquiv B hT) :=
  continuous_toWeighted B hT

/-- The inverse isomorphism is continuous. -/
@[fun_prop] theorem continuous_weightedRestrictedEquiv_symm :
    Continuous (weightedRestrictedEquiv B hT).symm :=
  continuous_ofWeighted B hT

/-- **The completed base change of `A⟨X⟩_T` is `B⟨X⟩_{λ(T)}` as a topological ring.** -/
theorem isHomeomorph_weightedRestrictedEquiv : IsHomeomorph (weightedRestrictedEquiv B hT) :=
  (weightedRestrictedEquiv B hT).toEquiv.isHomeomorph_iff.mpr
    ⟨continuous_weightedRestrictedEquiv B hT, continuous_weightedRestrictedEquiv_symm B hT⟩

end CompletedTensor

end TauCeti.Huber
