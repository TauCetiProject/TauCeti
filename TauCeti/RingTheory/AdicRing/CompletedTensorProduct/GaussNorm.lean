/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicRing.CompletedTensorProduct.Restricted
public import TauCeti.RingTheory.Huber.Restricted.Comparison

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

private theorem gaussToHuber_commutes :
    (GEquiv k R).symm.toRingHom.comp (algebraMap R (Tate k R)) =
      (algebraMap R (WComp k R)).comp (RingHom.id R) := RingHom.ext fun r ↦ by
  rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.id_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe, ← coe_restrictedMvPowerSeriesCompletionGaussAlgEquiv_symm]
  exact (restrictedMvPowerSeriesCompletionGaussAlgEquiv (n := k) (R := R)).symm.commutes r

private theorem huberToGauss_commutes : (GEquiv k R).toRingHom.comp (algebraMap R (WComp k R)) =
    (algebraMap R (Tate k R)).comp (RingHom.id R) := RingHom.ext fun _ ↦ by simp

private theorem cont_gaussToHuber : Continuous (GEquiv k R).symm.toRingHom :=
  continuous_restrictedMvPowerSeriesCompletionGaussEquiv_symm

private theorem cont_huberToGauss : Continuous (GEquiv k R).toRingHom :=
  continuous_restrictedMvPowerSeriesCompletionGaussEquiv

private noncomputable def toHuberCompletedTensor :
    CompletedTensorProduct R (Tate k R) S →+* CompletedTensorProduct R (WComp k R) S :=
  mapRingHom (.id R) (GEquiv k R).symm.toRingHom (.id S) (gaussToHuber_commutes k R) rfl
    (cont_gaussToHuber k R) continuous_id

private noncomputable def ofHuberCompletedTensor :
    CompletedTensorProduct R (WComp k R) S →+* CompletedTensorProduct R (Tate k R) S :=
  mapRingHom (.id R) (GEquiv k R).toRingHom (.id S) (huberToGauss_commutes k R) rfl
    (cont_huberToGauss k R) continuous_id

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
  (mapRingHom_comp (.id R) _ (.id S) (huberToGauss_commutes k R) rfl
    (cont_huberToGauss k R) continuous_id (.id R) _ (.id S)
    (gaussToHuber_commutes k R) rfl (cont_gaussToHuber k R)
    continuous_id (RingHom.ext fun _ ↦ by simp) rfl).trans <|
    mapRingHom_id_of_eq R S _ (RingHom.ext (GEquiv k R).symm_apply_apply) _ _ _ _

private theorem ofHuberCompletedTensor_comp_toHuberCompletedTensor :
    (ofHuberCompletedTensor k R S).comp (toHuberCompletedTensor k R S) = .id _ :=
  (mapRingHom_comp (.id R) _ (.id S) (gaussToHuber_commutes k R) rfl
    (cont_gaussToHuber k R) continuous_id (.id R) _ (.id S)
    (huberToGauss_commutes k R) rfl (cont_huberToGauss k R)
    continuous_id (RingHom.ext fun _ ↦ by simp) rfl).trans <|
    mapRingHom_id_of_eq R S _ (RingHom.ext (GEquiv k R).apply_symm_apply) _ _ _ _

private noncomputable def completedTensorGaussRingEquiv :
    CompletedTensorProduct R (Tate k R) S ≃+* CompletedTensorProduct R (WComp k R) S :=
  RingEquiv.ofRingHom (toHuberCompletedTensor k R S) (ofHuberCompletedTensor k R S)
    (toHuberCompletedTensor_comp_ofHuberCompletedTensor k R S)
    (ofHuberCompletedTensor_comp_toHuberCompletedTensor k R S)

variable [ContinuousSMul R S]

/-- **Completed-tensor base change on Gauss-normed restricted power series** (transported from
`TauCeti.AdicRing.CompletedTensorProduct.restrictedEquiv` via `mapRingHom` and
`restrictedMvPowerSeriesCompletionGaussAlgEquiv`). -/
noncomputable def restrictedGaussEquiv : CompletedTensorProduct R (Tate k R) S ≃ₐ[R] Tate k S :=
  AlgEquiv.ofRingEquiv (f := (completedTensorGaussRingEquiv k R S).trans
      ((restrictedEquiv k R S).trans (GEquiv k S))) fun r ↦ by
    rw [← (inl R (Tate k R) S).commutes r, RingEquiv.trans_apply, RingEquiv.trans_apply]
    change GEquiv k S (restrictedEquiv k R S
      (toHuberCompletedTensor k R S (inl R _ S (algebraMap R (Tate k R) r)))) = _
    rw [toHuberCompletedTensor, mapRingHom_inl, restrictedEquiv_inl,
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
theorem restrictedGaussEquiv_eq_restrictedEquiv
    (hB : (GEquiv k R).symm.toRingHom.comp (algebraMap R (Tate k R)) =
      (algebraMap R (WComp k R)).comp (.id R))
    (hS : (RingHom.id S).comp (algebraMap R S) = (algebraMap R S).comp (.id R))
    (hfB : Continuous (GEquiv k R).symm.toRingHom) (hfS : Continuous (RingHom.id S))
    (z : CompletedTensorProduct R (Tate k R) S) :
    restrictedGaussEquiv k R S z = GEquiv k S (restrictedEquiv k R S
      (mapRingHom (.id R) (GEquiv k R).symm.toRingHom (.id S) hB hS hfB hfS z)) := by rfl

/-- Cross-carrier commutativity from the Huber completed tensor product via `mapRingHom`. -/
theorem restrictedGaussEquiv_mapRingHom
    (hB : (GEquiv k R).toRingHom.comp (algebraMap R (WComp k R)) =
      (algebraMap R (Tate k R)).comp (.id R))
    (hS : (RingHom.id S).comp (algebraMap R S) = (algebraMap R S).comp (.id R))
    (hfB : Continuous (GEquiv k R).toRingHom) (hfS : Continuous (RingHom.id S))
    (x : CompletedTensorProduct R (WComp k R) S) :
    restrictedGaussEquiv k R S (mapRingHom (.id R) (GEquiv k R).toRingHom (.id S) hB hS hfB hfS x) =
      GEquiv k S (restrictedEquiv k R S x) := by
  change restrictedGaussEquiv k R S (ofHuberCompletedTensor k R S x) = _
  rw [restrictedGaussEquiv_eq_restrictedEquiv (S := S) (gaussToHuber_commutes k R) rfl
    (cont_gaussToHuber k R) continuous_id]
  exact congrArg (fun y ↦ GEquiv k S (restrictedEquiv k R S y))
    congr($(toHuberCompletedTensor_comp_ofHuberCompletedTensor k R S) x)

/-- On `R⟨X⟩`, `restrictedGaussEquiv` acts unconditionally as `restrictedMapOfContinuous`. -/
@[simp] theorem restrictedGaussEquiv_inl (g : Tate k R) :
    restrictedGaussEquiv k R S (inl R _ S g) =
      restrictedMapOfContinuous (continuous_algebraMap R S) g := by
  rw [restrictedGaussEquiv_eq_restrictedEquiv (S := S) (gaussToHuber_commutes k R) rfl
      (cont_gaussToHuber k R) continuous_id, mapRingHom_inl, restrictedEquiv_inl,
    restrictedMvPowerSeriesCompletionGaussEquiv_weightedMapCompletion_of_continuous]; simp

/-- As a formal power series, `restrictedGaussEquiv (inl g)` maps coefficients via `algebraMap`. -/
theorem coe_restrictedGaussEquiv_inl (g : Tate k R) :
    (restrictedGaussEquiv k R S (inl R _ S g) : MvPowerSeries (Fin k) S) =
      MvPowerSeries.map (algebraMap R S) g := by
  rw [restrictedGaussEquiv_inl, coe_restrictedMapOfContinuous]

/-- Under a norm bound on `algebraMap R S`, `restrictedGaussEquiv` acts as `restrictedMap`. -/
theorem restrictedGaussEquiv_inl_of_norm_le {C : ℝ} (hφ : ∀ r, ‖algebraMap R S r‖ ≤ C * ‖r‖)
    (g : Tate k R) : restrictedGaussEquiv k R S (inl R _ S g) =
      restrictedMap (algebraMap R S) hφ g := by
  rw [restrictedGaussEquiv_inl,
    restrictedMapOfContinuous_eq_restrictedMap (continuous_algebraMap R S) hφ]

/-- On `S`, `restrictedGaussEquiv` is the constant-series embedding `algebraMap`. -/
@[simp] theorem restrictedGaussEquiv_inr (s : S) :
    restrictedGaussEquiv k R S (inr R (Tate k R) S s) = algebraMap S (Tate k S) s := by
  rw [restrictedGaussEquiv_eq_restrictedEquiv (S := S) (gaussToHuber_commutes k R) rfl
      (cont_gaussToHuber k R) continuous_id,
    mapRingHom_inr, RingHom.id_apply, restrictedEquiv_inr]; simp

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
