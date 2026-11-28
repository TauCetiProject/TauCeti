/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicRing.CompletedTensorProduct.Restricted
public import TauCeti.RingTheory.Huber.Restricted.Comparison.Basic

/-!
# Completed-tensor base change on Gauss-normed restricted power series

For adic ultrametric normed commutative rings `R` and `S` connected by a continuous `R`-algebra
structure, `TauCeti.MvPowerSeries.isAdicRing_isRestricted_subring` makes `R⟨X₁, …, Xₖ⟩` an adic
ring of finite ideal type and `TauCeti.IsAdicRing.completeSpace` supplies completeness of `R`, `S`.
This file transports `TauCeti.AdicRing.CompletedTensorProduct.restrictedEquiv` along
`CompletedTensorProduct.mapRingHom` and `restrictedMvPowerSeriesCompletionGaussAlgEquiv` to obtain a
topological `R`-algebra isomorphism `R⟨X₁, …, Xₖ⟩ ⊗̂_R S ≃ₐ[R] S⟨X₁, …, Xₖ⟩` acting on `R⟨X⟩` via
`TauCeti.MvPowerSeries.restrictedMapOfContinuous (continuous_algebraMap R S)`.

## Main definitions and results

* `TauCeti.AdicRing.CompletedTensorProduct.restrictedGaussEquiv`: `R⟨X⟩ ⊗̂_R S ≃ₐ[R] S⟨X⟩`
  transported from `TauCeti.AdicRing.CompletedTensorProduct.restrictedEquiv`.
* `isHomeomorph_restrictedGaussEquiv`, `restrictedGaussEquiv_eq_restrictedEquiv`,
  `restrictedGaussEquiv_mapRingHom`, `restrictedGaussEquiv_inl`, and `restrictedGaussEquiv_inr`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, §§7.5.3, 7.7.6,
  and Ch. I, §10.7.
-/

public section

namespace TauCeti.AdicRing.CompletedTensorProduct

open _root_.MvPowerSeries TauCeti.Huber TauCeti.MvPowerSeries

section GaussBaseChange

variable (k : ℕ) (R S : Type*) [NormedCommRing R] [IsUltrametricDist R] [IsAdicRing R]
  [NormedCommRing S] [IsUltrametricDist S] [IsAdicRing S] [Algebra R S]

local notation:max "Tate" k':max R':max => IsRestricted.subring (R := R') (fun _ : Fin k' ↦ 1)
local notation:max "WComp" k':max R':max => restrictedMvPowerSeriesCompletion k' R'
local notation:max "GEquiv" k':max R':max =>
  restrictedMvPowerSeriesCompletionGaussEquiv (n := k') (R := R')

private noncomputable def toHuberCompletedTensor :
    CompletedTensorProduct R (Tate k R) S →+* CompletedTensorProduct R (WComp k R) S :=
  mapRingHom (.id R) (GEquiv k R).symm.toRingHom (.id S)
    (restrictedMvPowerSeriesCompletionGaussEquiv_symm_comp_algebraMap.trans
      (RingHom.comp_id _).symm)
    rfl (by simpa [RingEquiv.coe_toRingHom] using
      continuous_restrictedMvPowerSeriesCompletionGaussEquiv_symm) continuous_id

private noncomputable def ofHuberCompletedTensor :
    CompletedTensorProduct R (WComp k R) S →+* CompletedTensorProduct R (Tate k R) S :=
  mapRingHom (.id R) (GEquiv k R).toRingHom (.id S)
    (restrictedMvPowerSeriesCompletionGaussEquiv_comp_algebraMap.trans
      (RingHom.comp_id _).symm)
    rfl (by simpa [RingEquiv.coe_toRingHom] using
      continuous_restrictedMvPowerSeriesCompletionGaussEquiv) continuous_id

private theorem toHuberCompletedTensor_apply (z : CompletedTensorProduct R (Tate k R) S) :
    toHuberCompletedTensor k R S z = mapRingHom (.id R) (GEquiv k R).symm.toRingHom (.id S)
      (restrictedMvPowerSeriesCompletionGaussEquiv_symm_comp_algebraMap.trans
        (RingHom.comp_id _).symm)
      rfl (by simpa [RingEquiv.coe_toRingHom] using
        continuous_restrictedMvPowerSeriesCompletionGaussEquiv_symm) continuous_id z := rfl

private theorem ofHuberCompletedTensor_apply (x : CompletedTensorProduct R (WComp k R) S) :
    ofHuberCompletedTensor k R S x = mapRingHom (.id R) (GEquiv k R).toRingHom (.id S)
      (restrictedMvPowerSeriesCompletionGaussEquiv_comp_algebraMap.trans
        (RingHom.comp_id _).symm)
      rfl (by simpa [RingEquiv.coe_toRingHom] using
        continuous_restrictedMvPowerSeriesCompletionGaussEquiv) continuous_id x := rfl

omit [IsUltrametricDist R] [IsAdicRing R] in
private theorem mapRingHom_id_of_eq {B : Type*} [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [IsAdicRing B] [Algebra R B] (f : B →+* B) (hf : f = .id B)
    (hB : f.comp (algebraMap R B) = (algebraMap R B).comp (.id R))
    (hC : (RingHom.id S).comp (algebraMap R S) = (algebraMap R S).comp (.id R))
    (hfc : Continuous f) (hSc : Continuous (RingHom.id S)) :
    mapRingHom (.id R) f (.id S) hB hC hfc hSc = .id (CompletedTensorProduct R B S) := by
  subst hf; exact mapRingHom_id R B S hB hC

private theorem toHuberCompletedTensor_comp_ofHuberCompletedTensor :
    (toHuberCompletedTensor k R S).comp (ofHuberCompletedTensor k R S) = .id _ :=
  (mapRingHom_comp (.id R) _ (.id S)
    (restrictedMvPowerSeriesCompletionGaussEquiv_comp_algebraMap.trans (RingHom.comp_id _).symm)
    rfl (by simpa [RingEquiv.coe_toRingHom] using
      continuous_restrictedMvPowerSeriesCompletionGaussEquiv) continuous_id
    (.id R) _ (.id S)
    (restrictedMvPowerSeriesCompletionGaussEquiv_symm_comp_algebraMap.trans
      (RingHom.comp_id _).symm)
    rfl (by simpa [RingEquiv.coe_toRingHom] using
      continuous_restrictedMvPowerSeriesCompletionGaussEquiv_symm) continuous_id
    (RingHom.ext fun _ ↦ by simp) rfl).trans <|
    mapRingHom_id_of_eq R S _ (RingHom.ext (GEquiv k R).symm_apply_apply) _ _ _ _

private theorem ofHuberCompletedTensor_comp_toHuberCompletedTensor :
    (ofHuberCompletedTensor k R S).comp (toHuberCompletedTensor k R S) = .id _ :=
  (mapRingHom_comp (.id R) _ (.id S)
    (restrictedMvPowerSeriesCompletionGaussEquiv_symm_comp_algebraMap.trans
      (RingHom.comp_id _).symm)
    rfl (by simpa [RingEquiv.coe_toRingHom] using
      continuous_restrictedMvPowerSeriesCompletionGaussEquiv_symm) continuous_id
    (.id R) _ (.id S)
    (restrictedMvPowerSeriesCompletionGaussEquiv_comp_algebraMap.trans (RingHom.comp_id _).symm)
    rfl (by simpa [RingEquiv.coe_toRingHom] using
      continuous_restrictedMvPowerSeriesCompletionGaussEquiv) continuous_id
    (RingHom.ext fun _ ↦ by simp) rfl).trans <|
    mapRingHom_id_of_eq R S _ (RingHom.ext (GEquiv k R).apply_symm_apply) _ _ _ _

private noncomputable def completedTensorGaussRingEquiv :
    CompletedTensorProduct R (Tate k R) S ≃+* CompletedTensorProduct R (WComp k R) S :=
  RingEquiv.ofRingHom (toHuberCompletedTensor k R S) (ofHuberCompletedTensor k R S)
    (toHuberCompletedTensor_comp_ofHuberCompletedTensor k R S)
    (ofHuberCompletedTensor_comp_toHuberCompletedTensor k R S)

private theorem completedTensorGaussRingEquiv_apply (z : CompletedTensorProduct R (Tate k R) S) :
    completedTensorGaussRingEquiv k R S z = toHuberCompletedTensor k R S z := by
  simp [completedTensorGaussRingEquiv]

variable [ContinuousSMul R S]

/-- **Completed-tensor base change on Gauss-normed restricted power series** (transported from
`TauCeti.AdicRing.CompletedTensorProduct.restrictedEquiv` via `mapRingHom` and
`restrictedMvPowerSeriesCompletionGaussAlgEquiv`). -/
noncomputable def restrictedGaussEquiv : CompletedTensorProduct R (Tate k R) S ≃ₐ[R] Tate k S :=
  AlgEquiv.ofRingEquiv (f := (completedTensorGaussRingEquiv k R S).trans
      ((restrictedEquiv k R S).trans (GEquiv k S))) fun r ↦ by
    rw [← (inl R (Tate k R) S).commutes r, RingEquiv.trans_apply, RingEquiv.trans_apply,
      completedTensorGaussRingEquiv_apply, toHuberCompletedTensor_apply, mapRingHom_inl,
      restrictedEquiv_inl,
      restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletion_of_continuous]
    simp [← IsScalarTower.algebraMap_apply R S]

/-- `restrictedGaussEquiv` is a homeomorphism of topological `R`-algebras. -/
theorem isHomeomorph_restrictedGaussEquiv : IsHomeomorph (restrictedGaussEquiv k R S) :=
  ((GEquiv k S).toEquiv.isHomeomorph_iff.mpr
      ⟨continuous_restrictedMvPowerSeriesCompletionGaussEquiv,
       continuous_restrictedMvPowerSeriesCompletionGaussEquiv_symm⟩ |>.comp
    (isHomeomorph_restrictedEquiv k R S)).comp
    ((completedTensorGaussRingEquiv k R S).toEquiv.isHomeomorph_iff.mpr
      ⟨continuous_mapRingHom .., continuous_mapRingHom ..⟩)

variable {k R S}

/-- Cross-carrier comparison: `restrictedGaussEquiv` equals `restrictedEquiv` conjugated by
`CompletedTensorProduct.mapRingHom` and `restrictedMvPowerSeriesCompletionGaussEquiv`. -/
theorem restrictedGaussEquiv_eq_restrictedEquiv (z : CompletedTensorProduct R (Tate k R) S) :
    restrictedGaussEquiv k R S z = GEquiv k S (restrictedEquiv k R S
      (mapRingHom (.id R) (GEquiv k R).symm.toRingHom (.id S)
        (restrictedMvPowerSeriesCompletionGaussEquiv_symm_comp_algebraMap.trans
          (RingHom.comp_id _).symm)
        rfl (by simpa [RingEquiv.coe_toRingHom] using
          continuous_restrictedMvPowerSeriesCompletionGaussEquiv_symm) continuous_id z)) := by
  rw [restrictedGaussEquiv, AlgEquiv.ofRingEquiv_apply, RingEquiv.trans_apply,
    RingEquiv.trans_apply, completedTensorGaussRingEquiv_apply, toHuberCompletedTensor_apply]

/-- Cross-carrier commutativity from the Huber completed tensor product via `mapRingHom`. -/
theorem restrictedGaussEquiv_mapRingHom (x : CompletedTensorProduct R (WComp k R) S) :
    restrictedGaussEquiv k R S
        (mapRingHom (.id R) (GEquiv k R).toRingHom (.id S)
          (restrictedMvPowerSeriesCompletionGaussEquiv_comp_algebraMap.trans
            (RingHom.comp_id _).symm)
          rfl (by simpa [RingEquiv.coe_toRingHom] using
            continuous_restrictedMvPowerSeriesCompletionGaussEquiv) continuous_id x) =
      GEquiv k S (restrictedEquiv k R S x) := by
  rw [← ofHuberCompletedTensor_apply, restrictedGaussEquiv_eq_restrictedEquiv,
    ← toHuberCompletedTensor_apply]
  exact congrArg (fun y ↦ GEquiv k S (restrictedEquiv k R S y))
    congr($(toHuberCompletedTensor_comp_ofHuberCompletedTensor k R S) x)

/-- On `R⟨X⟩`, `restrictedGaussEquiv` acts unconditionally as `restrictedMapOfContinuous`. -/
@[simp] theorem restrictedGaussEquiv_inl (g : Tate k R) :
    restrictedGaussEquiv k R S (inl R _ S g) =
      restrictedMapOfContinuous (continuous_algebraMap R S) g := by
  rw [restrictedGaussEquiv_eq_restrictedEquiv, mapRingHom_inl, restrictedEquiv_inl,
    restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletion_of_continuous]; simp

/-- On `S`, `restrictedGaussEquiv` is the constant-series embedding `algebraMap`. -/
@[simp] theorem restrictedGaussEquiv_inr (s : S) :
    restrictedGaussEquiv k R S (inr R (Tate k R) S s) = algebraMap S (Tate k S) s := by
  rw [restrictedGaussEquiv_eq_restrictedEquiv, mapRingHom_inr, RingHom.id_apply,
    restrictedEquiv_inr]; simp

/-- `restrictedGaussEquiv.symm` sends a constant series `s` to `inr s`. -/
@[simp] theorem restrictedGaussEquiv_symm_algebraMap (s : S) :
    (restrictedGaussEquiv k R S).symm (algebraMap S (Tate k S) s) = inr R (Tate k R) S s := by
  rw [AlgEquiv.symm_apply_eq, restrictedGaussEquiv_inr]

/-- `restrictedGaussEquiv.symm` sends each coordinate `Xᵢ` to `inl Xᵢ`. -/
@[simp] theorem restrictedGaussEquiv_symm_X (i : Fin k) :
    (restrictedGaussEquiv k R S).symm ⟨MvPowerSeries.X i, isRestricted_X _ i⟩ =
      inl R (Tate k R) S ⟨MvPowerSeries.X i, isRestricted_X _ i⟩ := by
  rw [AlgEquiv.symm_apply_eq, restrictedGaussEquiv_inl, restrictedMapOfContinuous_X]

end GaussBaseChange
end TauCeti.AdicRing.CompletedTensorProduct
