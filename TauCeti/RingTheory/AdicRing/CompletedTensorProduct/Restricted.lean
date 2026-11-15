/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicRing.CompletedTensorProduct
public import TauCeti.RingTheory.Huber.Restricted.Adic
public import TauCeti.RingTheory.Huber.WeightedEval.Completion

/-!
# Base change of restricted power series along a completed tensor product

Let `A` and `C` be adic rings of finite ideal type and `A → C` a continuous ring homomorphism.
Completing the tensor product with a restricted power-series algebra changes its coefficients:
`A⟨X₁, …, Xₘ⟩ ⊗̂_A C ≅ C⟨X₁, …, Xₘ⟩`, the isomorphism sending `f ⊗ c` to `c` times the series
obtained by mapping the coefficients of `f` into `C`. In formal geometry this says that the
formal affine space over `Spf A` base changes along `Spf C → Spf A` to the formal affine space
over `Spf C`.

Both directions are induced by universal properties: the map out of `A⟨X⟩ ⊗̂_A C` by that of
the completed tensor product (`TauCeti.AdicRing.CompletedTensorProduct.lift`), the map out of
`C⟨X⟩` by that of restricted power series into a linearly topologised ring
(`TauCeti.Huber.weightedEvalHomCompletion`), and both composites are identities because a
continuous homomorphism out of either ring is determined by its values on generators.

This is the same argument as for Huber's completed tensor product in
`TauCeti.Huber.CompletedTensor.weightedRestrictedEquiv`. That result concerns a different ring,
the uniform completion of the tensor topology, and needs `A → C` to be adic; here the ring is
the adic completion `TauCeti.AdicRing.CompletedTensorProduct` used in formal geometry, and
`A → C` need only be continuous.

## Main definitions

* `TauCeti.AdicRing.CompletedTensorProduct.restrictedEquiv`: the ring isomorphism
  `A⟨X₁, …, Xₘ⟩ ⊗̂_A C ≃+* C⟨X₁, …, Xₘ⟩`.

## Main results

* `TauCeti.AdicRing.CompletedTensorProduct.restrictedEquiv_inl`: on `A⟨X⟩` it maps the
  coefficients into `C`, so it sends each variable to the same variable.
* `TauCeti.AdicRing.CompletedTensorProduct.restrictedEquiv_inr`: on `C` it is the constant
  series.
* `TauCeti.AdicRing.CompletedTensorProduct.restrictedEquiv_symm_weightedC` and
  `restrictedEquiv_symm_weightedX`: the inverse sends a constant `c` to `1 ⊗ c` and each
  variable `X` to `X ⊗ 1`.
* `TauCeti.AdicRing.CompletedTensorProduct.isHomeomorph_restrictedEquiv`: it is a homeomorphism.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, 7.5.3 and
  7.7.6, and Ch. I, 10.7.
-/

public section

namespace TauCeti.AdicRing.CompletedTensorProduct

open Huber

variable (m : ℕ) (A C : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsAdicRing A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsAdicRing C]
  [Algebra A C]

/-- The homomorphism `C⟨X₁, …, Xₘ⟩ → A⟨X₁, …, Xₘ⟩ ⊗̂_A C` restricting to `inr` on `C` and sending
each variable to the image of the variable under `inl`. -/
private noncomputable def ofRestricted :
    restrictedMvPowerSeriesCompletion m C →+*
      CompletedTensorProduct A (restrictedMvPowerSeriesCompletion m A) C :=
  weightedEvalHomCompletion isWeightFamily_one_weight (continuous_inr ..).continuousAt
    (isWeightBounded_of_isLinearTopology _ _ fun i ↦ inl A _ C
      ((weightedX _ isWeightFamily_one_weight i :
        weightedRestrictedSubring (fun _ : Fin m ↦ ({1} : Set A)) isWeightFamily_one_weight) :
          restrictedMvPowerSeriesCompletion m A))

private theorem continuous_ofRestricted : Continuous (ofRestricted m A C) :=
  continuous_weightedEvalHomCompletion ..

private theorem ofRestricted_algebraMap (c : C) :
    ofRestricted m A C (algebraMap C (restrictedMvPowerSeriesCompletion m C) c) =
      inr A (restrictedMvPowerSeriesCompletion m A) C c := by
  rw [ofRestricted, algebraMap_completion_weightedRestrictedSubring_apply,
    weightedEvalHomCompletion_coe, weightedEvalHom_weightedC, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe]

private theorem ofRestricted_weightedX (i : Fin m) :
    ofRestricted m A C ((weightedX _ isWeightFamily_one_weight i :
        weightedRestrictedSubring (fun _ : Fin m ↦ ({1} : Set C)) isWeightFamily_one_weight) :
          restrictedMvPowerSeriesCompletion m C) =
      inl A _ C ((weightedX _ isWeightFamily_one_weight i :
        weightedRestrictedSubring (fun _ : Fin m ↦ ({1} : Set A)) isWeightFamily_one_weight) :
          restrictedMvPowerSeriesCompletion m A) := by
  rw [ofRestricted, weightedEvalHomCompletion_coe, weightedEvalHom_weightedX]

/-- The `A`-algebra structure on `C⟨X₁, …, Xₘ⟩` through `C`. -/
private noncomputable abbrev restrictedAlgebra :
    Algebra A (restrictedMvPowerSeriesCompletion m C) :=
  ((algebraMap C (restrictedMvPowerSeriesCompletion m C)).comp (algebraMap A C)).toAlgebra

omit [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A] in
/-- `A → C → C⟨X₁, …, Xₘ⟩` is a scalar tower for `restrictedAlgebra`. -/
private theorem isScalarTower_restricted :
    letI := restrictedAlgebra m A C
    IsScalarTower A C (restrictedMvPowerSeriesCompletion m C) :=
  letI := restrictedAlgebra m A C
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

variable [ContinuousSMul A C]

/-- The coefficient map `A⟨X₁, …, Xₘ⟩ → C⟨X₁, …, Xₘ⟩`, as an `A`-algebra homomorphism. -/
private noncomputable def restrictedMap :
    letI := restrictedAlgebra m A C
    restrictedMvPowerSeriesCompletion m A →ₐ[A] restrictedMvPowerSeriesCompletion m C :=
  letI := restrictedAlgebra m A C
  { weightedMapCompletion (continuous_algebraMap A C) isWeightFamily_one_weight
      isWeightFamily_one_weight (fun _ ↦ by simp) with
    commutes' a := by
      simp [RingHom.algebraMap_toAlgebra] }

/-- The homomorphism `A⟨X₁, …, Xₘ⟩ ⊗̂_A C → C⟨X₁, …, Xₘ⟩` induced by the coefficient map and the
constant series. -/
private noncomputable def toRestricted :
    CompletedTensorProduct A (restrictedMvPowerSeriesCompletion m A) C →+*
      restrictedMvPowerSeriesCompletion m C :=
  letI := restrictedAlgebra m A C
  haveI := isScalarTower_restricted m A C
  (lift (restrictedMap m A C) (IsScalarTower.toAlgHom A C _)
    (continuous_weightedMapCompletion ..)
    (continuous_algebraMap_restrictedMvPowerSeriesCompletion m C)).toRingHom

private theorem continuous_toRestricted : Continuous (toRestricted m A C) :=
  letI := restrictedAlgebra m A C
  continuous_lift ..

private theorem toRestricted_inl (x : restrictedMvPowerSeriesCompletion m A) :
    toRestricted m A C (inl A _ C x) =
      weightedMapCompletion (continuous_algebraMap A C) isWeightFamily_one_weight
        isWeightFamily_one_weight (fun _ ↦ by simp) x :=
  letI := restrictedAlgebra m A C
  lift_inl ..

private theorem toRestricted_inr (c : C) :
    toRestricted m A C (inr A (restrictedMvPowerSeriesCompletion m A) C c) =
      algebraMap C (restrictedMvPowerSeriesCompletion m C) c :=
  letI := restrictedAlgebra m A C
  haveI := isScalarTower_restricted m A C
  lift_inr ..

private theorem toRestricted_comp_ofRestricted :
    (toRestricted m A C).comp (ofRestricted m A C) = RingHom.id _ :=
  completion_weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight
    ((continuous_toRestricted m A C).comp (continuous_ofRestricted m A C)) continuous_id
    (fun c ↦ by
      simp only [RingHom.comp_apply, RingHom.id_apply,
        ← algebraMap_completion_weightedRestrictedSubring_apply, ofRestricted_algebraMap,
        toRestricted_inr])
    fun i ↦ by
      simp only [RingHom.comp_apply, RingHom.id_apply, ofRestricted_weightedX, toRestricted_inl,
        weightedMapCompletion_coe, weightedMap_weightedX]

private theorem ofRestricted_comp_toRestricted :
    (ofRestricted m A C).comp (toRestricted m A C) = RingHom.id _ := by
  refine ringHom_ext ((continuous_ofRestricted m A C).comp (continuous_toRestricted m A C))
    continuous_id ?_ ?_
  · refine completion_weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight
      (((continuous_ofRestricted m A C).comp (continuous_toRestricted m A C)).comp
        (continuous_inl ..)) (continuous_inl ..) (fun a ↦ ?_) fun i ↦ ?_
    · -- both sides are the image of `a` under the structure map of the completed tensor product
      simp only [RingHom.comp_apply, RingHom.id_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        toRestricted_inl, weightedMapCompletion_coe, weightedMap_weightedC]
      rw [← algebraMap_completion_weightedRestrictedSubring_apply m C, ofRestricted_algebraMap,
        ← algebraMap_completion_weightedRestrictedSubring_apply m A, AlgHom.commutes,
        AlgHom.commutes]
    · simp only [RingHom.comp_apply, RingHom.id_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        toRestricted_inl, weightedMapCompletion_coe, weightedMap_weightedX, ofRestricted_weightedX]
  · ext c
    simp only [RingHom.comp_apply, RingHom.id_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      toRestricted_inr, ofRestricted_algebraMap]

/-- **Base change of restricted power series**: the completed tensor product
`A⟨X₁, …, Xₘ⟩ ⊗̂_A C` is the restricted power-series ring `C⟨X₁, …, Xₘ⟩`. -/
noncomputable def restrictedEquiv :
    CompletedTensorProduct A (restrictedMvPowerSeriesCompletion m A) C ≃+*
      restrictedMvPowerSeriesCompletion m C :=
  RingEquiv.ofRingHom (toRestricted m A C) (ofRestricted m A C)
    (toRestricted_comp_ofRestricted m A C) (ofRestricted_comp_toRestricted m A C)

/-- On `A⟨X₁, …, Xₘ⟩`, `restrictedEquiv` maps the coefficients of a series into `C`. -/
@[simp]
theorem restrictedEquiv_inl (x : restrictedMvPowerSeriesCompletion m A) :
    restrictedEquiv m A C (inl A _ C x) =
      weightedMapCompletion (continuous_algebraMap A C) isWeightFamily_one_weight
        isWeightFamily_one_weight (fun _ ↦ by simp) x :=
  toRestricted_inl m A C x

/-- On `C`, `restrictedEquiv` is the constant series. -/
@[simp]
theorem restrictedEquiv_inr (c : C) :
    restrictedEquiv m A C (inr A (restrictedMvPowerSeriesCompletion m A) C c) =
      algebraMap C (restrictedMvPowerSeriesCompletion m C) c :=
  toRestricted_inr m A C c

/-- The inverse of `restrictedEquiv` sends a constant series `c` to `1 ⊗ c`. -/
@[simp]
theorem restrictedEquiv_symm_weightedC (c : C) :
    (restrictedEquiv m A C).symm ((weightedC _ isWeightFamily_one_weight c :
        weightedRestrictedSubring (fun _ : Fin m ↦ ({1} : Set C)) isWeightFamily_one_weight) :
          restrictedMvPowerSeriesCompletion m C) =
      inr A (restrictedMvPowerSeriesCompletion m A) C c := by
  rw [← algebraMap_completion_weightedRestrictedSubring_apply]
  exact ofRestricted_algebraMap m A C c

/-- The inverse of `restrictedEquiv` sends each variable of `C⟨X₁, …, Xₘ⟩` to `X ⊗ 1` for the same
variable `X` of `A⟨X₁, …, Xₘ⟩`. -/
@[simp]
theorem restrictedEquiv_symm_weightedX (i : Fin m) :
    (restrictedEquiv m A C).symm ((weightedX _ isWeightFamily_one_weight i :
        weightedRestrictedSubring (fun _ : Fin m ↦ ({1} : Set C)) isWeightFamily_one_weight) :
          restrictedMvPowerSeriesCompletion m C) =
      inl A _ C ((weightedX _ isWeightFamily_one_weight i :
        weightedRestrictedSubring (fun _ : Fin m ↦ ({1} : Set A)) isWeightFamily_one_weight) :
          restrictedMvPowerSeriesCompletion m A) :=
  ofRestricted_weightedX m A C i

/-- `restrictedEquiv` is a homeomorphism: it is an isomorphism of topological rings. -/
theorem isHomeomorph_restrictedEquiv : IsHomeomorph (restrictedEquiv m A C) :=
  (restrictedEquiv m A C).toEquiv.isHomeomorph_iff.mpr
    ⟨continuous_toRestricted m A C, continuous_ofRestricted m A C⟩

end TauCeti.AdicRing.CompletedTensorProduct
