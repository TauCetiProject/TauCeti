/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Completion
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Adic
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Pair.Polydisc
public import TauCeti.RingTheory.Huber.WeightedEval.Completion
public import Mathlib.Topology.Algebra.Algebra.Equiv

/-!
# Completed tensor products of closed polydiscs

For a Huber ring `A`, write `A⟨T₁, …, Tₙ⟩` for `restrictedMvPowerSeriesCompletion n A`, with
coordinates `Pair.polydiscVar n A i`. This file proves that the completed tensor product of two
of them is again one:

```text
A⟨T₁, …, Tₘ⟩ ⊗̂_A A⟨S₁, …, Sₙ⟩ ≃ A⟨T₁, …, Tₘ, S₁, …, Sₙ⟩,
  Tᵢ ⊗ 1 ↦ T_{castAdd i},   1 ⊗ Sⱼ ↦ T_{natAdd j}.
```

The forward map comes from the universal property of the completed tensor product
(`TauCeti.Huber.CompletedTensor.lift`), each factor being evaluated at the corresponding block of
coordinates (`TauCeti.Huber.weightedEvalHomCompletion`). The inverse evaluates the coordinates at
`Tᵢ ⊗ 1` and `1 ⊗ Sⱼ`. Both composites are the identity because continuous maps out of either
side are determined by generators.

On spaces this is the fibre product of two closed polydiscs over `Spa A`.

## Main definitions

* `TauCeti.Huber.CompletedTensor.polydiscEquiv`: the isomorphism of topological `A`-algebras
  `A⟨T⟩ ⊗̂_A A⟨S⟩ ≃A[A] A⟨T, S⟩`.

## Main results

* `TauCeti.Huber.CompletedTensor.polydiscEquiv_inl_polydiscVar` and
  `…_inr_polydiscVar`: the coordinates of the two factors go to the two blocks of coordinates.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3, Lemma 3.5(i) and the proof of Proposition 3.7.
* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, §1.2, proof of
  Proposition 1.2.2.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 5.50.
-/

public section

open UniformSpace

namespace TauCeti.Huber.CompletedTensor

variable (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  (m n : ℕ)

/-- Evaluation of `A⟨T₁, …, Tₖ⟩` at the coordinates `T_{e i}` of `A⟨T₁, …, Tₗ⟩`. -/
private noncomputable def polydiscBlock {k l : ℕ} (e : Fin k → Fin l) :
    restrictedMvPowerSeriesCompletion k A →+* restrictedMvPowerSeriesCompletion l A :=
  weightedEvalHomCompletion isWeightFamily_one_weight
    (continuous_algebraMap_completion_weightedRestrictedSubring l A
      isWeightFamily_one_weight).continuousAt
    ((isWeightBounded_one_weight_iff_forall_isPowerBounded _ _).mpr
      fun i ↦ Pair.isPowerBounded_polydiscVar _ A (e i))

private theorem continuous_polydiscBlock {k l : ℕ} (e : Fin k → Fin l) :
    Continuous (polydiscBlock A e) :=
  continuous_weightedEvalHomCompletion _ _ _

private theorem polydiscBlock_algebraMap {k l : ℕ} (e : Fin k → Fin l) (a : A) :
    polydiscBlock A e (algebraMap A (restrictedMvPowerSeriesCompletion k A) a) =
      algebraMap A (restrictedMvPowerSeriesCompletion l A) a := by
  rw [algebraMap_completion_weightedRestrictedSubring_apply, polydiscBlock,
    weightedEvalHomCompletion_coe, weightedEvalHom_weightedC]

private theorem polydiscBlock_polydiscVar {k l : ℕ} (e : Fin k → Fin l) (i : Fin k) :
    polydiscBlock A e (Pair.polydiscVar k A i) = Pair.polydiscVar l A (e i) := by
  rw [polydiscBlock, weightedEvalHomCompletion_coe, weightedEvalHom_weightedX]

/-- The forward map `A⟨T⟩ ⊗̂_A A⟨S⟩ → A⟨T, S⟩`. -/
private noncomputable def toPolydisc :
    CompletedTensor A (restrictedMvPowerSeriesCompletion m A)
        (restrictedMvPowerSeriesCompletion n A) →+*
      restrictedMvPowerSeriesCompletion (m + n) A :=
  lift (polydiscBlock A (Fin.castAdd n)) (polydiscBlock A (Fin.natAdd m))
    (by ext a; simp only [RingHom.comp_apply, polydiscBlock_algebraMap])
    (continuous_polydiscBlock _ _)
    (continuous_polydiscBlock _ _)

private theorem continuous_toPolydisc : Continuous (toPolydisc A m n) :=
  continuous_lift _ _ _ _ _

/-- The images of the coordinates in the completed tensor product, in the order `T, S`. -/
private noncomputable def tensorVar :
    Fin (m + n) → CompletedTensor A (restrictedMvPowerSeriesCompletion m A)
      (restrictedMvPowerSeriesCompletion n A) :=
  Fin.append (fun i ↦ inl A _ _ (Pair.polydiscVar m A i))
    (fun j ↦ inr A _ _ (Pair.polydiscVar n A j))

private theorem isPowerBounded_tensorVar (i : Fin (m + n)) :
    IsPowerBounded (tensorVar A m n i) := by
  induction i using Fin.addCases with
  | left i =>
    simpa [tensorVar] using (isAdicHom_inl A _ _).isPowerBounded_map
      (Pair.isPowerBounded_polydiscVar _ A i)
  | right j =>
    simpa [tensorVar] using (isAdicHom_inr A _ _).isPowerBounded_map
      (Pair.isPowerBounded_polydiscVar _ A j)

/-- The inverse map `A⟨T, S⟩ → A⟨T⟩ ⊗̂_A A⟨S⟩`. -/
private noncomputable def ofPolydisc :
    restrictedMvPowerSeriesCompletion (m + n) A →+*
      CompletedTensor A (restrictedMvPowerSeriesCompletion m A)
        (restrictedMvPowerSeriesCompletion n A) :=
  weightedEvalHomCompletion (φ := algebraMap A (CompletedTensor A
      (restrictedMvPowerSeriesCompletion m A) (restrictedMvPowerSeriesCompletion n A)))
    isWeightFamily_one_weight
    ((continuous_inl _ _ _).comp (continuous_algebraMap_completion_weightedRestrictedSubring m A
      isWeightFamily_one_weight)).continuousAt
    ((isWeightBounded_one_weight_iff_forall_isPowerBounded _ _).mpr
      (isPowerBounded_tensorVar A m n))

private theorem continuous_ofPolydisc : Continuous (ofPolydisc A m n) :=
  continuous_weightedEvalHomCompletion _ _ _

private theorem ofPolydisc_algebraMap (a : A) :
    ofPolydisc A m n (algebraMap A (restrictedMvPowerSeriesCompletion (m + n) A) a) =
      algebraMap A (CompletedTensor A (restrictedMvPowerSeriesCompletion m A)
        (restrictedMvPowerSeriesCompletion n A)) a := by
  rw [algebraMap_completion_weightedRestrictedSubring_apply, ofPolydisc,
    weightedEvalHomCompletion_coe, weightedEvalHom_weightedC]

private theorem ofPolydisc_polydiscVar (i : Fin (m + n)) :
    ofPolydisc A m n (Pair.polydiscVar (m + n) A i) = tensorVar A m n i := by
  rw [ofPolydisc, weightedEvalHomCompletion_coe, weightedEvalHom_weightedX]

private theorem toPolydisc_inl (f : restrictedMvPowerSeriesCompletion m A) :
    toPolydisc A m n (inl A _ _ f) = polydiscBlock A (Fin.castAdd n) f :=
  lift_inl _ _ _ _ _ f

private theorem toPolydisc_inr (f : restrictedMvPowerSeriesCompletion n A) :
    toPolydisc A m n (inr A _ _ f) = polydiscBlock A (Fin.natAdd m) f :=
  lift_inr _ _ _ _ _ f

private theorem toPolydisc_comp_ofPolydisc :
    (toPolydisc A m n).comp (ofPolydisc A m n) = RingHom.id _ := by
  refine restrictedMvPowerSeriesCompletion_ringHom_ext
    ((continuous_toPolydisc A m n).comp (continuous_ofPolydisc A m n)) continuous_id
    (fun a ↦ ?_) fun i ↦ ?_
  · rw [RingHom.comp_apply, ofPolydisc_algebraMap, algebraMap_eq_inl, RingHom.comp_apply,
      toPolydisc_inl, polydiscBlock_algebraMap, RingHom.id_apply]
  · rw [RingHom.comp_apply, RingHom.id_apply, ofPolydisc_polydiscVar]
    induction i using Fin.addCases with
    | left i => simp [tensorVar, toPolydisc_inl, polydiscBlock_polydiscVar]
    | right j => simp [tensorVar, toPolydisc_inr, polydiscBlock_polydiscVar]

private theorem ofPolydisc_comp_polydiscBlock_castAdd :
    (ofPolydisc A m n).comp (polydiscBlock A (Fin.castAdd n)) = inl A _ _ := by
  refine restrictedMvPowerSeriesCompletion_ringHom_ext
    ((continuous_ofPolydisc A m n).comp (continuous_polydiscBlock _ _)) (continuous_inl _ _ _)
    (fun a ↦ ?_) fun i ↦ ?_
  · rw [RingHom.comp_apply, polydiscBlock_algebraMap, ofPolydisc_algebraMap, algebraMap_eq_inl,
      RingHom.comp_apply]
  · rw [RingHom.comp_apply, polydiscBlock_polydiscVar, ofPolydisc_polydiscVar]
    simp [tensorVar]

private theorem ofPolydisc_comp_polydiscBlock_natAdd :
    (ofPolydisc A m n).comp (polydiscBlock A (Fin.natAdd m)) = inr A _ _ := by
  refine restrictedMvPowerSeriesCompletion_ringHom_ext
    ((continuous_ofPolydisc A m n).comp (continuous_polydiscBlock _ _)) (continuous_inr _ _ _)
    (fun a ↦ ?_) fun i ↦ ?_
  · rw [RingHom.comp_apply, polydiscBlock_algebraMap, ofPolydisc_algebraMap, algebraMap_eq_inl,
      inl_comp_algebraMap, RingHom.comp_apply]
  · rw [RingHom.comp_apply, polydiscBlock_polydiscVar, ofPolydisc_polydiscVar]
    simp [tensorVar]

private theorem ofPolydisc_comp_toPolydisc :
    (ofPolydisc A m n).comp (toPolydisc A m n) = RingHom.id _ := by
  refine hom_ext ((continuous_ofPolydisc A m n).comp (continuous_toPolydisc A m n))
    continuous_id ?_ ?_
  · rw [RingHom.comp_assoc, toPolydisc, lift_comp_inl, ofPolydisc_comp_polydiscBlock_castAdd,
      RingHom.id_comp]
  · rw [RingHom.comp_assoc, toPolydisc, lift_comp_inr, ofPolydisc_comp_polydiscBlock_natAdd,
      RingHom.id_comp]

private theorem toPolydisc_algebraMap (a : A) :
    toPolydisc A m n (algebraMap A _ a) =
      algebraMap A (restrictedMvPowerSeriesCompletion (m + n) A) a := by
  rw [algebraMap_eq_inl, RingHom.comp_apply, toPolydisc_inl, polydiscBlock_algebraMap]

/-- **The completed tensor product of two closed polydiscs is a closed polydisc.** For a Huber
ring `A`, `A⟨T₁, …, Tₘ⟩ ⊗̂_A A⟨S₁, …, Sₙ⟩` is isomorphic as a topological `A`-algebra to
`A⟨T₁, …, Tₘ, S₁, …, Sₙ⟩`, the coordinates of the left factor going to the first `m` coordinates
and those of the right factor to the last `n`. -/
noncomputable def polydiscEquiv :
    CompletedTensor A (restrictedMvPowerSeriesCompletion m A)
        (restrictedMvPowerSeriesCompletion n A) ≃A[A]
      restrictedMvPowerSeriesCompletion (m + n) A where
  toAlgEquiv := AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom (toPolydisc A m n)
    (ofPolydisc A m n) (toPolydisc_comp_ofPolydisc A m n) (ofPolydisc_comp_toPolydisc A m n))
    (toPolydisc_algebraMap A m n)
  continuous_toFun := continuous_toPolydisc A m n
  continuous_invFun := continuous_ofPolydisc A m n

/-- `polydiscEquiv` is `toPolydisc` by definition of `AlgEquiv.ofRingEquiv` and
`RingEquiv.ofRingHom`. -/
private theorem polydiscEquiv_apply
    (x : CompletedTensor A (restrictedMvPowerSeriesCompletion m A)
      (restrictedMvPowerSeriesCompletion n A)) :
    polydiscEquiv A m n x = toPolydisc A m n x :=
  rfl

/-- The coordinate `Tᵢ ⊗ 1` goes to the coordinate `T_{castAdd i}`. -/
@[simp] theorem polydiscEquiv_inl_polydiscVar (i : Fin m) :
    polydiscEquiv A m n (inl A _ _ (Pair.polydiscVar m A i)) =
      Pair.polydiscVar (m + n) A (Fin.castAdd n i) := by
  rw [polydiscEquiv_apply, toPolydisc_inl, polydiscBlock_polydiscVar]

/-- The coordinate `1 ⊗ Sⱼ` goes to the coordinate `T_{natAdd j}`. -/
@[simp] theorem polydiscEquiv_inr_polydiscVar (j : Fin n) :
    polydiscEquiv A m n (inr A _ _ (Pair.polydiscVar n A j)) =
      Pair.polydiscVar (m + n) A (Fin.natAdd m j) := by
  rw [polydiscEquiv_apply, toPolydisc_inr, polydiscBlock_polydiscVar]

/-- The isomorphism is the identity on the base ring. -/
@[simp] theorem polydiscEquiv_algebraMap (a : A) :
    polydiscEquiv A m n (algebraMap A _ a) =
      algebraMap A (restrictedMvPowerSeriesCompletion (m + n) A) a :=
  AlgHomClass.commutes _ a

/-- The inverse isomorphism is the identity on the base ring. Not `@[simp]`: the simp normal form
of `algebraMap A (restrictedMvPowerSeriesCompletion (m + n) A) a` is a coerced `weightedC`. -/
theorem polydiscEquiv_symm_algebraMap (a : A) :
    (polydiscEquiv A m n).symm (algebraMap A (restrictedMvPowerSeriesCompletion (m + n) A) a) =
      algebraMap A _ a :=
  AlgHomClass.commutes _ a

/-- The inverse sends the first `m` coordinates to the left factor. -/
@[simp] theorem polydiscEquiv_symm_polydiscVar_castAdd (i : Fin m) :
    (polydiscEquiv A m n).symm (Pair.polydiscVar (m + n) A (Fin.castAdd n i)) =
      inl A _ _ (Pair.polydiscVar m A i) := by
  rw [ContinuousAlgEquiv.symm_apply_eq, polydiscEquiv_inl_polydiscVar]

/-- The inverse sends the last `n` coordinates to the right factor. -/
@[simp] theorem polydiscEquiv_symm_polydiscVar_natAdd (j : Fin n) :
    (polydiscEquiv A m n).symm (Pair.polydiscVar (m + n) A (Fin.natAdd m j)) =
      inr A _ _ (Pair.polydiscVar n A j) := by
  rw [ContinuousAlgEquiv.symm_apply_eq, polydiscEquiv_inr_polydiscVar]

end TauCeti.Huber.CompletedTensor
