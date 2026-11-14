/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.UnitWeight
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Iterate.Basic
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Sum

/-!
# Iteration compatibility of the completed Gauss comparison

For a complete ultrametric normed ring `R` that is a Huber ring, Huber's iteration isomorphism
`TauCeti.Huber.iterateRingEquiv` splits `k + m` variables into an inner block of `k` variables and
an outer block of `m` variables, while `TauCeti.MvPowerSeries.restrictedFinAddEquiv` performs the
same splitting on Gauss-normed restricted power series.

This file constructs the iterated completed Gauss comparisons, both at the trivial weight `{1}`
(without assuming `[NormOneClass R]`) and at singleton multiplicative-unit weights `Tₗ = {uₗ}` with
`‖uₗ‖ * cₗ = 1`, and proves that they intertwine `iterateSplitHom`, `iterateRingEquiv`,
`iterateJoinHom`, and `iterateFirstBlockHom` with `restrictedFinAddEquiv`, its inverse, and
`restrictedFinAddFirstBlockAlgHom`. Consequently, all four iteration maps preserve the transported
Gauss norms.

## Main definitions

* `TauCeti.Huber.restrictedMvPowerSeriesIterateGaussEquiv`: the iterated completed Gauss comparison
  at unit radius `{1}`.
* `TauCeti.Huber.weightedRestrictedIterateGaussEquiv`: the iterated completed Gauss comparison for
  multiplicative-unit weights `{uₗ}`.

## Main results

* `TauCeti.Huber.restrictedMvPowerSeriesIterateGaussEquiv_iterateSplitHom`,
  `TauCeti.Huber.restrictedMvPowerSeriesIterateGaussEquiv_iterateRingEquiv`,
  `TauCeti.Huber.restrictedMvPowerSeriesCompletionGaussEquiv_iterateJoinHom`, and
  `TauCeti.Huber.restrictedMvPowerSeriesCompletionGaussEquiv_iterateFirstBlockHom`: iteration
  compatibility at unit radius, with Gauss-norm preservation
  `TauCeti.Huber.norm_restrictedMvPowerSeriesIterateGaussEquiv_iterateSplitHom`.
* `TauCeti.Huber.weightedRestrictedIterateGaussEquiv_iterateSplitHom`,
  `TauCeti.Huber.weightedRestrictedIterateGaussEquiv_iterateRingEquiv`,
  `TauCeti.Huber.weightedRestrictedCompletionGaussAlgEquiv_iterateJoinHom`, and
  `TauCeti.Huber.weightedRestrictedCompletionGaussAlgEquiv_iterateFirstBlockHom`: iteration
  compatibility for multiplicative-unit weights, with Gauss-norm preservation
  `TauCeti.Huber.norm_weightedRestrictedIterateGaussEquiv_iterateSplitHom`.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.1.1.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Remark and Definition 5.48 and Proposition 5.50.
-/

public section

namespace TauCeti.Huber

open UniformSpace _root_.MvPowerSeries TauCeti.MvPowerSeries

section GeneralComm

variable {k m : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [IsHuberRing R]
  {T : Fin k → Set R} (hT : IsWeightFamily T)
  {W : Fin m → Set (Completion (weightedRestrictedSubring T hT))} (hW : IsWeightFamily W)
  {U : Fin (k + m) → Set R} (hU : IsWeightFamily U)
  (hTU : ∀ i, U (Fin.castAdd m i) = T i)
  (hUW : ∀ j, algebraMap R (Completion (weightedRestrictedSubring T hT)) '' U (Fin.natAdd k j) =
    W j)
  {c : Fin (k + m) → ℝ} [∀ l, Fact (0 < c l)]

private theorem iterateFirstBlockHom_gauss_comm
    {eU : Completion (weightedRestrictedSubring U hU) →+* IsRestricted.subring (R := R) c}
    {eT : Completion (weightedRestrictedSubring T hT) →+*
      IsRestricted.subring (R := R) (c ∘ Fin.castAdd m)}
    (heU : Continuous eU) (heT : Continuous eT)
    (heU_C : ∀ r, eU (weightedC U hU r) = algebraMap R _ r)
    (heU_X : ∀ l, eU (weightedX U hU l) = ⟨X l, isRestricted_X c l⟩)
    (heT_C : ∀ r, eT (weightedC T hT r) = algebraMap R _ r)
    (heT_X : ∀ i, eT (weightedX T hT i) = ⟨X i, isRestricted_X (c ∘ Fin.castAdd m) i⟩) :
    eU.comp (iterateFirstBlockHom hT hU hTU) =
      (restrictedFinAddFirstBlockAlgHom (R := R) (r := c) (m := m)).toRingHom.comp eT := by
  have hcont_fb : Continuous (restrictedFinAddFirstBlockAlgHom (k := k) (m := m) (R := R)
      (r := c)) := isometry_restrictedFinAddFirstBlockAlgHom.continuous
  refine completion_weightedRestrictedSubring_ringHom_ext_of_continuous hT
    (heU.comp (continuous_iterateFirstBlockHom hT hU hTU)) (hcont_fb.comp heT) (fun r ↦ ?_)
    fun i ↦ ?_
  · simp only [RingHom.coe_comp, Function.comp_apply, iterateFirstBlockHom_coe_weightedC,
      algebraMap_completion_weightedRestrictedSubring_apply _ _ hU, heU_C, heT_C,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  · simp only [RingHom.coe_comp, Function.comp_apply, iterateFirstBlockHom_coe_weightedX,
      heU_X, heT_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      restrictedFinAddFirstBlockAlgHom_X]

private theorem iterateSplitHom_gauss_comm
    {eU : Completion (weightedRestrictedSubring U hU) →+* IsRestricted.subring (R := R) c}
    {eT : Completion (weightedRestrictedSubring T hT) →+*
      IsRestricted.subring (R := R) (c ∘ Fin.castAdd m)}
    {eW : Completion (weightedRestrictedSubring W hW) →+*
      IsRestricted.subring
        (R := IsRestricted.subring (R := R) (c ∘ Fin.castAdd m)) (c ∘ Fin.natAdd k)}
    (heU : Continuous eU) (heW : Continuous eW)
    (heU_C : ∀ r, eU (weightedC U hU r) = algebraMap R _ r)
    (heU_X : ∀ l, eU (weightedX U hU l) = ⟨X l, isRestricted_X c l⟩)
    (heT_C : ∀ r, eT (weightedC T hT r) = algebraMap R _ r)
    (heT_X : ∀ i, eT (weightedX T hT i) = ⟨X i, isRestricted_X (c ∘ Fin.castAdd m) i⟩)
    (heW_C : ∀ b, eW (weightedC W hW b) =
      algebraMap (IsRestricted.subring (R := R) (c ∘ Fin.castAdd m)) _ (eT b))
    (heW_X : ∀ j, eW (weightedX W hW j) = ⟨X j, isRestricted_X (c ∘ Fin.natAdd k) j⟩) :
    eW.comp (iterateSplitHom hT hW hU hTU hUW) =
      (restrictedFinAddEquiv (R := R) (r := c)).toRingHom.comp eU := by
  refine completion_weightedRestrictedSubring_ringHom_ext_of_continuous hU
    (heW.comp (continuous_iterateSplitHom hT hW hU hTU hUW))
    (isometry_restrictedFinAddEquiv.continuous.comp heU) (fun r ↦ ?_) fun l ↦ ?_
  · simp only [RingHom.coe_comp, Function.comp_apply, iterateSplitHom_coe_weightedC,
      iterateStructureHom_apply, heW_C, heT_C, heU_C, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, restrictedFinAddEquiv_algebraMap]
    exact Subtype.ext (by simp [coe_algebraMap_isRestrictedSubring_apply])
  · simp only [RingHom.coe_comp, Function.comp_apply, iterateSplitHom_coe_weightedX, heU_X,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) l
    · rw [iterateVar_castAdd, heW_C, heT_X, restrictedFinAddEquiv_X_castAdd]
    · rw [iterateVar_natAdd, heW_X, restrictedFinAddEquiv_X_natAdd]

end GeneralComm

private theorem weightedMapCompletionEquiv_coe_weightedC {m : ℕ} {A B : Type*} [CommRing A]
    [TopologicalSpace A] [NonarchimedeanRing A] [CommRing B] [TopologicalSpace B]
    [NonarchimedeanRing B] {T : Fin m → Set A} {S : Fin m → Set B} (e : A ≃+* B)
    (he : Continuous e) (he' : Continuous e.symm) (hT : IsWeightFamily T) (hS : IsWeightFamily S)
    (hTS : ∀ i, (e : A →+* B) '' T i ⊆ S i) (hST : ∀ i, (e.symm : B →+* A) '' S i ⊆ T i)
    (b : A) :
    weightedMapCompletionEquiv e he he' hT hS hTS hST (weightedC T hT b) =
      weightedC S hS (e b) :=
  (weightedMapCompletionEquiv_apply e he he' hT hS hTS hST _).trans
    ((weightedMapCompletion_coe he hT hS hTS _).trans
      (congrArg ((↑) : weightedRestrictedSubring S hS →
          Completion (weightedRestrictedSubring S hS))
        (weightedMap_weightedC he hTS b)))

private theorem weightedMapCompletionEquiv_coe_weightedX {m : ℕ} {A B : Type*} [CommRing A]
    [TopologicalSpace A] [NonarchimedeanRing A] [CommRing B] [TopologicalSpace B]
    [NonarchimedeanRing B] {T : Fin m → Set A} {S : Fin m → Set B} (e : A ≃+* B)
    (he : Continuous e) (he' : Continuous e.symm) (hT : IsWeightFamily T) (hS : IsWeightFamily S)
    (hTS : ∀ i, (e : A →+* B) '' T i ⊆ S i) (hST : ∀ i, (e.symm : B →+* A) '' S i ⊆ T i)
    (j : Fin m) :
    weightedMapCompletionEquiv e he he' hT hS hTS hST (weightedX T hT j) =
      weightedX S hS j :=
  (weightedMapCompletionEquiv_apply e he he' hT hS hTS hST _).trans
    ((weightedMapCompletion_coe he hT hS hTS _).trans
      (congrArg ((↑) : weightedRestrictedSubring S hS →
          Completion (weightedRestrictedSubring S hS))
        (weightedMap_weightedX he hTS j)))

/-! ### Unit-radius iteration compatibility -/

section OneWeight

variable {k m : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]

/-- **The iterated completed Gauss comparison at unit radius.** Identifies
`restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k R)` with
`R{X₁, …, Xₖ}{Y₁, …, Yₘ}` without assuming `[NormOneClass R]`. -/
noncomputable def restrictedMvPowerSeriesIterateGaussEquiv :
    restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k R) ≃+*
      IsRestricted.subring
        (R := IsRestricted.subring (R := R) (fun _ : Fin k ↦ (1 : ℝ)))
        (fun _ : Fin m ↦ (1 : ℝ)) :=
  (weightedMapCompletionEquiv
    (restrictedMvPowerSeriesCompletionGaussEquiv (n := k) (R := R))
    continuous_restrictedMvPowerSeriesCompletionGaussEquiv
    continuous_restrictedMvPowerSeriesCompletionGaussEquiv_symm
    isWeightFamily_one_weight isWeightFamily_one_weight (fun _ ↦ by simp) (fun _ ↦ by simp)).trans
    (restrictedMvPowerSeriesCompletionGaussEquiv (n := m)
      (R := IsRestricted.subring (R := R) (fun _ : Fin k ↦ (1 : ℝ))))

/-- The iterated unit-radius Gauss comparison is continuous. -/
theorem continuous_restrictedMvPowerSeriesIterateGaussEquiv :
    Continuous (restrictedMvPowerSeriesIterateGaussEquiv (k := k) (m := m) (R := R)) := by
  rw [restrictedMvPowerSeriesIterateGaussEquiv, RingEquiv.coe_trans]
  exact continuous_restrictedMvPowerSeriesCompletionGaussEquiv.comp
    (continuous_weightedMapCompletionEquiv ..)

/-- The inverse iterated unit-radius Gauss comparison is continuous. -/
theorem continuous_restrictedMvPowerSeriesIterateGaussEquiv_symm :
    Continuous (restrictedMvPowerSeriesIterateGaussEquiv (k := k) (m := m) (R := R)).symm := by
  rw [restrictedMvPowerSeriesIterateGaussEquiv, RingEquiv.symm_trans, RingEquiv.coe_trans]
  exact (continuous_weightedMapCompletionEquiv_symm ..).comp
    continuous_restrictedMvPowerSeriesCompletionGaussEquiv_symm

/-- On a constant of the outer completion, `restrictedMvPowerSeriesIterateGaussEquiv` applies
`restrictedMvPowerSeriesCompletionGaussEquiv` and embeds the result as a constant series. -/
@[simp]
theorem restrictedMvPowerSeriesIterateGaussEquiv_coe_weightedC
    (b : restrictedMvPowerSeriesCompletion k R) :
    restrictedMvPowerSeriesIterateGaussEquiv
        ((weightedC (fun _ : Fin m ↦ ({1} : Set (restrictedMvPowerSeriesCompletion k R)))
          isWeightFamily_one_weight b :
          restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k R))) =
      algebraMap (IsRestricted.subring (R := R) (fun _ : Fin k ↦ (1 : ℝ))) _
        (restrictedMvPowerSeriesCompletionGaussEquiv b) := by
  rw [restrictedMvPowerSeriesIterateGaussEquiv, RingEquiv.trans_apply,
    weightedMapCompletionEquiv_coe_weightedC, restrictedMvPowerSeriesCompletionGaussEquiv_coe]
  exact Subtype.ext (by simp)

/-- On the `j`-th outer variable, `restrictedMvPowerSeriesIterateGaussEquiv` returns `X j`. -/
@[simp]
theorem restrictedMvPowerSeriesIterateGaussEquiv_coe_weightedX (j : Fin m) :
    restrictedMvPowerSeriesIterateGaussEquiv
        ((weightedX (fun _ : Fin m ↦ ({1} : Set (restrictedMvPowerSeriesCompletion k R)))
          isWeightFamily_one_weight j :
          restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k R))) =
      ⟨X j, isRestricted_X _ j⟩ := by
  rw [restrictedMvPowerSeriesIterateGaussEquiv, RingEquiv.trans_apply,
    weightedMapCompletionEquiv_coe_weightedX, restrictedMvPowerSeriesCompletionGaussEquiv_coe]
  exact Subtype.ext (by simp)

variable [IsHuberRing R]

/-- **Huber variable splitting commutes with Gauss-normed variable splitting at unit radius.** -/
@[simp]
theorem restrictedMvPowerSeriesIterateGaussEquiv_iterateSplitHom
    (hUW : ∀ j : Fin m,
      algebraMap R (restrictedMvPowerSeriesCompletion k R) ''
        (fun _ : Fin (k + m) ↦ ({1} : Set R)) (Fin.natAdd k j) =
        ({1} : Set (restrictedMvPowerSeriesCompletion k R)))
    (x : restrictedMvPowerSeriesCompletion (k + m) R) :
    restrictedMvPowerSeriesIterateGaussEquiv
        (iterateSplitHom isWeightFamily_one_weight isWeightFamily_one_weight
          isWeightFamily_one_weight (fun _ ↦ rfl) hUW x) =
      restrictedFinAddEquiv (r := fun _ : Fin (k + m) ↦ (1 : ℝ))
        (restrictedMvPowerSeriesCompletionGaussEquiv x) := by
  simpa using DFunLike.congr_fun (iterateSplitHom_gauss_comm isWeightFamily_one_weight
    isWeightFamily_one_weight isWeightFamily_one_weight (fun _ ↦ rfl) hUW
    (c := fun _ : Fin (k + m) ↦ (1 : ℝ))
    (eU := (restrictedMvPowerSeriesCompletionGaussEquiv (n := k + m) (R := R)).toRingHom)
    (eT := (restrictedMvPowerSeriesCompletionGaussEquiv (n := k) (R := R)).toRingHom)
    (eW := (restrictedMvPowerSeriesIterateGaussEquiv (k := k) (m := m) (R := R)).toRingHom)
    continuous_restrictedMvPowerSeriesCompletionGaussEquiv
    continuous_restrictedMvPowerSeriesIterateGaussEquiv
    (fun r ↦ Subtype.ext (by simp)) (fun l ↦ Subtype.ext (by simp))
    (fun r ↦ Subtype.ext (by simp)) (fun i ↦ Subtype.ext (by simp))
    restrictedMvPowerSeriesIterateGaussEquiv_coe_weightedC
    restrictedMvPowerSeriesIterateGaussEquiv_coe_weightedX) x

/-- `iterateRingEquiv` at unit radius intertwines the completed Gauss comparisons with
`restrictedFinAddEquiv`. -/
theorem restrictedMvPowerSeriesIterateGaussEquiv_iterateRingEquiv
    (hUW : ∀ j : Fin m,
      algebraMap R (restrictedMvPowerSeriesCompletion k R) ''
        (fun _ : Fin (k + m) ↦ ({1} : Set R)) (Fin.natAdd k j) =
        ({1} : Set (restrictedMvPowerSeriesCompletion k R)))
    (x : restrictedMvPowerSeriesCompletion (k + m) R) :
    restrictedMvPowerSeriesIterateGaussEquiv
        (iterateRingEquiv isWeightFamily_one_weight isWeightFamily_one_weight
          isWeightFamily_one_weight (fun _ ↦ rfl) hUW x) =
      restrictedFinAddEquiv (r := fun _ : Fin (k + m) ↦ (1 : ℝ))
        (restrictedMvPowerSeriesCompletionGaussEquiv x) := by
  rw [iterateRingEquiv_apply, restrictedMvPowerSeriesIterateGaussEquiv_iterateSplitHom]

/-- `iterateJoinHom` at unit radius intertwines the completed Gauss comparisons with
`restrictedFinAddEquiv.symm`. -/
@[simp]
theorem restrictedMvPowerSeriesCompletionGaussEquiv_iterateJoinHom
    (hUW : ∀ j : Fin m,
      algebraMap R (restrictedMvPowerSeriesCompletion k R) ''
        (fun _ : Fin (k + m) ↦ ({1} : Set R)) (Fin.natAdd k j) =
        ({1} : Set (restrictedMvPowerSeriesCompletion k R)))
    (y : restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k R)) :
    restrictedMvPowerSeriesCompletionGaussEquiv
        (iterateJoinHom isWeightFamily_one_weight isWeightFamily_one_weight
          isWeightFamily_one_weight (fun _ ↦ rfl) hUW y) =
      (restrictedFinAddEquiv (r := fun _ : Fin (k + m) ↦ (1 : ℝ))).symm
        (restrictedMvPowerSeriesIterateGaussEquiv y) := by
  apply (restrictedFinAddEquiv (r := fun _ : Fin (k + m) ↦ (1 : ℝ))).injective
  rw [RingEquiv.apply_symm_apply,
    ← restrictedMvPowerSeriesIterateGaussEquiv_iterateSplitHom hUW,
    ← RingHom.comp_apply, iterateSplitHom_comp_iterateJoinHom, RingHom.id_apply]

/-- `iterateFirstBlockHom` at unit radius intertwines the completed Gauss comparisons with
`restrictedFinAddFirstBlockAlgHom`. -/
@[simp]
theorem restrictedMvPowerSeriesCompletionGaussEquiv_iterateFirstBlockHom
    (x : restrictedMvPowerSeriesCompletion k R) :
    restrictedMvPowerSeriesCompletionGaussEquiv
        (iterateFirstBlockHom isWeightFamily_one_weight
          (hU := isWeightFamily_one_weight (k := k + m) (A := R)) (fun _ ↦ rfl) x) =
      restrictedFinAddFirstBlockAlgHom (r := fun _ : Fin (k + m) ↦ (1 : ℝ)) (m := m)
        (restrictedMvPowerSeriesCompletionGaussEquiv x) := by
  simpa using DFunLike.congr_fun (iterateFirstBlockHom_gauss_comm isWeightFamily_one_weight
    isWeightFamily_one_weight (fun _ ↦ rfl) (c := fun _ : Fin (k + m) ↦ (1 : ℝ))
    (eU := (restrictedMvPowerSeriesCompletionGaussEquiv (n := k + m) (R := R)).toRingHom)
    (eT := (restrictedMvPowerSeriesCompletionGaussEquiv (n := k) (R := R)).toRingHom)
    continuous_restrictedMvPowerSeriesCompletionGaussEquiv
    continuous_restrictedMvPowerSeriesCompletionGaussEquiv
    (fun r ↦ Subtype.ext (by simp)) (fun l ↦ Subtype.ext (by simp))
    (fun r ↦ Subtype.ext (by simp)) (fun i ↦ Subtype.ext (by simp))) x

/-- `iterateSplitHom` at unit radius preserves the Gauss norm transported across the completed
Gauss comparisons. -/
theorem norm_restrictedMvPowerSeriesIterateGaussEquiv_iterateSplitHom
    (hUW : ∀ j : Fin m,
      algebraMap R (restrictedMvPowerSeriesCompletion k R) ''
        (fun _ : Fin (k + m) ↦ ({1} : Set R)) (Fin.natAdd k j) =
        ({1} : Set (restrictedMvPowerSeriesCompletion k R)))
    (x : restrictedMvPowerSeriesCompletion (k + m) R) :
    ‖restrictedMvPowerSeriesIterateGaussEquiv
        (iterateSplitHom isWeightFamily_one_weight isWeightFamily_one_weight
          isWeightFamily_one_weight (fun _ ↦ rfl) hUW x)‖ =
      ‖restrictedMvPowerSeriesCompletionGaussEquiv x‖ := by
  rw [restrictedMvPowerSeriesIterateGaussEquiv_iterateSplitHom, norm_restrictedFinAddEquiv]

/-- `iterateRingEquiv` at unit radius preserves the Gauss norm transported across the completed
Gauss comparisons. -/
theorem norm_restrictedMvPowerSeriesIterateGaussEquiv_iterateRingEquiv
    (hUW : ∀ j : Fin m,
      algebraMap R (restrictedMvPowerSeriesCompletion k R) ''
        (fun _ : Fin (k + m) ↦ ({1} : Set R)) (Fin.natAdd k j) =
        ({1} : Set (restrictedMvPowerSeriesCompletion k R)))
    (x : restrictedMvPowerSeriesCompletion (k + m) R) :
    ‖restrictedMvPowerSeriesIterateGaussEquiv
        (iterateRingEquiv isWeightFamily_one_weight isWeightFamily_one_weight
          isWeightFamily_one_weight (fun _ ↦ rfl) hUW x)‖ =
      ‖restrictedMvPowerSeriesCompletionGaussEquiv x‖ := by
  rw [restrictedMvPowerSeriesIterateGaussEquiv_iterateRingEquiv, norm_restrictedFinAddEquiv]

/-- `iterateJoinHom` at unit radius preserves the Gauss norm transported across the completed Gauss
comparisons. -/
theorem norm_restrictedMvPowerSeriesCompletionGaussEquiv_iterateJoinHom
    (hUW : ∀ j : Fin m,
      algebraMap R (restrictedMvPowerSeriesCompletion k R) ''
        (fun _ : Fin (k + m) ↦ ({1} : Set R)) (Fin.natAdd k j) =
        ({1} : Set (restrictedMvPowerSeriesCompletion k R)))
    (y : restrictedMvPowerSeriesCompletion m (restrictedMvPowerSeriesCompletion k R)) :
    ‖restrictedMvPowerSeriesCompletionGaussEquiv
        (iterateJoinHom isWeightFamily_one_weight isWeightFamily_one_weight
          isWeightFamily_one_weight (fun _ ↦ rfl) hUW y)‖ =
      ‖restrictedMvPowerSeriesIterateGaussEquiv y‖ := by
  rw [restrictedMvPowerSeriesCompletionGaussEquiv_iterateJoinHom, norm_restrictedFinAddEquiv_symm]

/-- `iterateFirstBlockHom` at unit radius preserves the Gauss norm transported across the completed
Gauss comparisons. -/
theorem norm_restrictedMvPowerSeriesCompletionGaussEquiv_iterateFirstBlockHom
    (x : restrictedMvPowerSeriesCompletion k R) :
    ‖restrictedMvPowerSeriesCompletionGaussEquiv
        (iterateFirstBlockHom isWeightFamily_one_weight
          (hU := isWeightFamily_one_weight (k := k + m) (A := R)) (fun _ ↦ rfl) x)‖ =
      ‖restrictedMvPowerSeriesCompletionGaussEquiv x‖ := by
  rw [restrictedMvPowerSeriesCompletionGaussEquiv_iterateFirstBlockHom,
    norm_restrictedFinAddFirstBlockAlgHom]

end OneWeight

/-! ### Multiplicative-unit weight iteration compatibility -/

section UnitWeight

variable {k m : ℕ} {R : Type*} [NormedCommRing R] [IsUltrametricDist R]
  (u : Fin (k + m) → Rˣ) (hu : ∀ l, IsNormMulUnit (u l : R))
  {c : Fin (k + m) → ℝ} [∀ l, Fact (0 < c l)] (hc : ∀ l, ‖(u l : R)‖ * c l = 1)

private noncomputable def innerUnits (j : Fin m) :
    (IsRestricted.subring (R := R) (c ∘ Fin.castAdd m))ˣ :=
  Units.map (algebraMap R (IsRestricted.subring (R := R) (c ∘ Fin.castAdd m))).toMonoidHom
    (u (Fin.natAdd k j))

include hu in
private theorem isNormMulUnit_innerUnits (j : Fin m) :
    IsNormMulUnit (innerUnits u (c := c) j :
      IsRestricted.subring (R := R) (c ∘ Fin.castAdd m)) :=
  (hu (Fin.natAdd k j)).map
    (algebraMap R (IsRestricted.subring (R := R) (c ∘ Fin.castAdd m))).toMonoidHom
    norm_algebraMap_isRestrictedSubring

include hc in
private theorem norm_innerUnits_mul (j : Fin m) :
    ‖(innerUnits u (c := c) j :
      IsRestricted.subring (R := R) (c ∘ Fin.castAdd m))‖ * (c ∘ Fin.natAdd k) j = 1 := by
  change ‖algebraMap R (IsRestricted.subring (R := R) (c ∘ Fin.castAdd m))
    (u (Fin.natAdd k j))‖ * c (Fin.natAdd k j) = 1
  rw [norm_algebraMap_isRestrictedSubring]
  exact hc (Fin.natAdd k j)

variable [CompleteSpace R]

omit [∀ l, Fact (0 < c l)] in
private theorem image_outerWeight_subset
    {W : Fin m → Set (Completion (weightedRestrictedSubring
      (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
      (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i)))))}
    (hUW : ∀ j, algebraMap R (Completion (weightedRestrictedSubring
        (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
        (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i))))) ''
      ({(u (Fin.natAdd k j) : R)} : Set R) = W j) (j : Fin m) :
    ((weightedRestrictedCompletionGaussAlgEquiv (fun i ↦ u (Fin.castAdd m i))
        (fun i ↦ hu (Fin.castAdd m i)) (c := c ∘ Fin.castAdd m)
        (fun i ↦ hc (Fin.castAdd m i))).toRingEquiv : _ →+* _) '' W j ⊆
      {(innerUnits u (c := c) j :
        IsRestricted.subring (R := R) (c ∘ Fin.castAdd m))} := by
  rw [← hUW j, Set.image_singleton, Set.image_singleton, Set.singleton_subset_singleton]
  exact (weightedRestrictedCompletionGaussAlgEquiv (fun i ↦ u (Fin.castAdd m i))
    (fun i ↦ hu (Fin.castAdd m i)) (c := c ∘ Fin.castAdd m)
    (fun i ↦ hc (Fin.castAdd m i))).commutes (u (Fin.natAdd k j) : R)

omit [∀ l, Fact (0 < c l)] in
private theorem symm_image_innerUnits_subset
    {W : Fin m → Set (Completion (weightedRestrictedSubring
      (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
      (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i)))))}
    (hUW : ∀ j, algebraMap R (Completion (weightedRestrictedSubring
        (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
        (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i))))) ''
      ({(u (Fin.natAdd k j) : R)} : Set R) = W j) (j : Fin m) :
    ((weightedRestrictedCompletionGaussAlgEquiv (fun i ↦ u (Fin.castAdd m i))
        (fun i ↦ hu (Fin.castAdd m i)) (c := c ∘ Fin.castAdd m)
        (fun i ↦ hc (Fin.castAdd m i))).toRingEquiv.symm : _ →+* _) ''
      {(innerUnits u (c := c) j :
        IsRestricted.subring (R := R) (c ∘ Fin.castAdd m))} ⊆ W j := by
  rw [← hUW j, Set.image_singleton, Set.image_singleton, Set.singleton_subset_singleton]
  exact (weightedRestrictedCompletionGaussAlgEquiv (fun i ↦ u (Fin.castAdd m i))
    (fun i ↦ hu (Fin.castAdd m i)) (c := c ∘ Fin.castAdd m)
    (fun i ↦ hc (Fin.castAdd m i))).symm.commutes (u (Fin.natAdd k j) : R)

/-- **The iterated completed Gauss comparison for multiplicative-unit weights.** For any admissible
outer weight family `W` on the inner completion with `W j = algebraMap R _ '' {u (k + j)}`,
identifies `Completion (weightedRestrictedSubring W hW)` with
`R{X₁, …, Xₖ / c₁}{Y₁, …, Yₘ / c₂}`. -/
noncomputable def weightedRestrictedIterateGaussEquiv
    {W : Fin m → Set (Completion (weightedRestrictedSubring
      (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
      (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i)))))}
    (hW : IsWeightFamily W)
    (hUW : ∀ j, algebraMap R (Completion (weightedRestrictedSubring
        (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
        (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i))))) ''
      ({(u (Fin.natAdd k j) : R)} : Set R) = W j) :
    Completion (weightedRestrictedSubring W hW) ≃+*
      IsRestricted.subring
        (R := IsRestricted.subring (R := R) (c ∘ Fin.castAdd m))
        (c ∘ Fin.natAdd k) :=
  (weightedMapCompletionEquiv
    (weightedRestrictedCompletionGaussAlgEquiv (fun i ↦ u (Fin.castAdd m i))
      (fun i ↦ hu (Fin.castAdd m i)) (c := c ∘ Fin.castAdd m)
      (fun i ↦ hc (Fin.castAdd m i))).toRingEquiv
    (show Continuous (weightedRestrictedCompletionGaussAlgEquiv (fun i ↦ u (Fin.castAdd m i))
        (fun i ↦ hu (Fin.castAdd m i)) (c := c ∘ Fin.castAdd m)
        (fun i ↦ hc (Fin.castAdd m i))).toRingEquiv from
      continuous_weightedRestrictedCompletionGaussAlgEquiv (fun i ↦ u (Fin.castAdd m i))
        (fun i ↦ hu (Fin.castAdd m i)) (fun i ↦ hc (Fin.castAdd m i)))
    (show Continuous (weightedRestrictedCompletionGaussAlgEquiv (fun i ↦ u (Fin.castAdd m i))
        (fun i ↦ hu (Fin.castAdd m i)) (c := c ∘ Fin.castAdd m)
        (fun i ↦ hc (Fin.castAdd m i))).toRingEquiv.symm from
      continuous_weightedRestrictedCompletionGaussAlgEquiv_symm
        (fun i ↦ u (Fin.castAdd m i)) (fun i ↦ hu (Fin.castAdd m i))
        (fun i ↦ hc (Fin.castAdd m i)))
    hW (isWeightFamily_units (innerUnits u (c := c)))
    (image_outerWeight_subset u hu hc hUW)
    (symm_image_innerUnits_subset u hu hc hUW)).trans
    (weightedRestrictedCompletionGaussAlgEquiv (innerUnits u (c := c))
      (isNormMulUnit_innerUnits u hu) (norm_innerUnits_mul u hc)).toRingEquiv

/-- `weightedRestrictedIterateGaussEquiv` is continuous. -/
theorem continuous_weightedRestrictedIterateGaussEquiv
    {W : Fin m → Set (Completion (weightedRestrictedSubring
      (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
      (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i)))))}
    (hW : IsWeightFamily W)
    (hUW : ∀ j, algebraMap R (Completion (weightedRestrictedSubring
        (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
        (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i))))) ''
      ({(u (Fin.natAdd k j) : R)} : Set R) = W j) :
    Continuous (weightedRestrictedIterateGaussEquiv u hu hc hW hUW) := by
  rw [weightedRestrictedIterateGaussEquiv, RingEquiv.coe_trans]
  exact (continuous_weightedRestrictedCompletionGaussAlgEquiv (innerUnits u (c := c))
    (isNormMulUnit_innerUnits u hu) (norm_innerUnits_mul u hc)).comp
    (continuous_weightedMapCompletionEquiv ..)

/-- The inverse of `weightedRestrictedIterateGaussEquiv` is continuous. -/
theorem continuous_weightedRestrictedIterateGaussEquiv_symm
    {W : Fin m → Set (Completion (weightedRestrictedSubring
      (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
      (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i)))))}
    (hW : IsWeightFamily W)
    (hUW : ∀ j, algebraMap R (Completion (weightedRestrictedSubring
        (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
        (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i))))) ''
      ({(u (Fin.natAdd k j) : R)} : Set R) = W j) :
    Continuous (weightedRestrictedIterateGaussEquiv u hu hc hW hUW).symm := by
  rw [weightedRestrictedIterateGaussEquiv, RingEquiv.symm_trans, RingEquiv.coe_trans]
  exact (continuous_weightedMapCompletionEquiv_symm ..).comp
    (continuous_weightedRestrictedCompletionGaussAlgEquiv_symm (innerUnits u (c := c))
      (isNormMulUnit_innerUnits u hu) (norm_innerUnits_mul u hc))

/-- On a constant of the outer weighted completion, `weightedRestrictedIterateGaussEquiv` applies
the inner `weightedRestrictedCompletionGaussAlgEquiv` and embeds the result as a constant. -/
@[simp]
theorem weightedRestrictedIterateGaussEquiv_coe_weightedC
    {W : Fin m → Set (Completion (weightedRestrictedSubring
      (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
      (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i)))))}
    (hW : IsWeightFamily W)
    (hUW : ∀ j, algebraMap R (Completion (weightedRestrictedSubring
        (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
        (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i))))) ''
      ({(u (Fin.natAdd k j) : R)} : Set R) = W j)
    (b : Completion (weightedRestrictedSubring
      (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
      (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i))))) :
    weightedRestrictedIterateGaussEquiv u hu hc hW hUW
        ((weightedC W hW b : weightedRestrictedSubring W hW) : Completion _) =
      algebraMap (IsRestricted.subring (R := R) (c ∘ Fin.castAdd m)) _
        (weightedRestrictedCompletionGaussAlgEquiv (fun i ↦ u (Fin.castAdd m i))
          (fun i ↦ hu (Fin.castAdd m i)) (c := c ∘ Fin.castAdd m)
          (fun i ↦ hc (Fin.castAdd m i)) b) := by
  rw [weightedRestrictedIterateGaussEquiv, RingEquiv.trans_apply,
    weightedMapCompletionEquiv_coe_weightedC]
  exact weightedRestrictedCompletionGaussAlgEquiv_coe_weightedC (innerUnits u (c := c))
    (isNormMulUnit_innerUnits u hu) (norm_innerUnits_mul u hc) _

/-- On the `j`-th outer variable, `weightedRestrictedIterateGaussEquiv` returns `X j`. -/
@[simp]
theorem weightedRestrictedIterateGaussEquiv_coe_weightedX
    {W : Fin m → Set (Completion (weightedRestrictedSubring
      (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
      (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i)))))}
    (hW : IsWeightFamily W)
    (hUW : ∀ j, algebraMap R (Completion (weightedRestrictedSubring
        (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
        (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i))))) ''
      ({(u (Fin.natAdd k j) : R)} : Set R) = W j)
    (j : Fin m) :
    weightedRestrictedIterateGaussEquiv u hu hc hW hUW
        ((weightedX W hW j : weightedRestrictedSubring W hW) : Completion _) =
      ⟨X j, isRestricted_X (c ∘ Fin.natAdd k) j⟩ := by
  rw [weightedRestrictedIterateGaussEquiv, RingEquiv.trans_apply,
    weightedMapCompletionEquiv_coe_weightedX]
  exact weightedRestrictedCompletionGaussAlgEquiv_coe_weightedX (innerUnits u (c := c))
    (isNormMulUnit_innerUnits u hu) (norm_innerUnits_mul u hc) j

variable [IsHuberRing R]

/-- **Huber variable splitting commutes with Gauss-normed variable splitting for unit weights.** -/
@[simp]
theorem weightedRestrictedIterateGaussEquiv_iterateSplitHom
    {W : Fin m → Set (Completion (weightedRestrictedSubring
      (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
      (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i)))))}
    (hW : IsWeightFamily W)
    (hUW : ∀ j, algebraMap R (Completion (weightedRestrictedSubring
        (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
        (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i))))) ''
      ({(u (Fin.natAdd k j) : R)} : Set R) = W j)
    (x : Completion (weightedRestrictedSubring (fun l ↦ ({(u l : R)} : Set R))
      (isWeightFamily_units u))) :
    weightedRestrictedIterateGaussEquiv u hu hc hW hUW
        (iterateSplitHom (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i))) hW
          (isWeightFamily_units u) (fun _ ↦ rfl) hUW x) =
      restrictedFinAddEquiv (r := c) (weightedRestrictedCompletionGaussAlgEquiv u hu hc x) := by
  simpa using DFunLike.congr_fun (iterateSplitHom_gauss_comm
    (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i))) hW (isWeightFamily_units u)
    (fun _ ↦ rfl) hUW (c := c)
    (eU := (weightedRestrictedCompletionGaussAlgEquiv u hu hc).toRingHom)
    (eT := (weightedRestrictedCompletionGaussAlgEquiv (fun i ↦ u (Fin.castAdd m i))
      (fun i ↦ hu (Fin.castAdd m i)) (c := c ∘ Fin.castAdd m)
      (fun i ↦ hc (Fin.castAdd m i))).toRingHom)
    (eW := (weightedRestrictedIterateGaussEquiv u hu hc hW hUW).toRingHom)
    (continuous_weightedRestrictedCompletionGaussAlgEquiv u hu hc)
    (continuous_weightedRestrictedIterateGaussEquiv u hu hc hW hUW)
    (weightedRestrictedCompletionGaussAlgEquiv_coe_weightedC u hu hc)
    (weightedRestrictedCompletionGaussAlgEquiv_coe_weightedX u hu hc)
    (weightedRestrictedCompletionGaussAlgEquiv_coe_weightedC (fun i ↦ u (Fin.castAdd m i))
      (fun i ↦ hu (Fin.castAdd m i)) (fun i ↦ hc (Fin.castAdd m i)))
    (weightedRestrictedCompletionGaussAlgEquiv_coe_weightedX (fun i ↦ u (Fin.castAdd m i))
      (fun i ↦ hu (Fin.castAdd m i)) (fun i ↦ hc (Fin.castAdd m i)))
    (weightedRestrictedIterateGaussEquiv_coe_weightedC u hu hc hW hUW)
    (weightedRestrictedIterateGaussEquiv_coe_weightedX u hu hc hW hUW)) x

/-- `iterateRingEquiv` for unit weights intertwines the completed Gauss comparisons with
`restrictedFinAddEquiv`. -/
theorem weightedRestrictedIterateGaussEquiv_iterateRingEquiv
    {W : Fin m → Set (Completion (weightedRestrictedSubring
      (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
      (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i)))))}
    (hW : IsWeightFamily W)
    (hUW : ∀ j, algebraMap R (Completion (weightedRestrictedSubring
        (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
        (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i))))) ''
      ({(u (Fin.natAdd k j) : R)} : Set R) = W j)
    (x : Completion (weightedRestrictedSubring (fun l ↦ ({(u l : R)} : Set R))
      (isWeightFamily_units u))) :
    weightedRestrictedIterateGaussEquiv u hu hc hW hUW
        (iterateRingEquiv (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i))) hW
          (isWeightFamily_units u) (fun _ ↦ rfl) hUW x) =
      restrictedFinAddEquiv (r := c) (weightedRestrictedCompletionGaussAlgEquiv u hu hc x) := by
  rw [iterateRingEquiv_apply, weightedRestrictedIterateGaussEquiv_iterateSplitHom]

/-- `iterateJoinHom` for unit weights intertwines the completed Gauss comparisons with
`restrictedFinAddEquiv.symm`. -/
@[simp]
theorem weightedRestrictedCompletionGaussAlgEquiv_iterateJoinHom
    {W : Fin m → Set (Completion (weightedRestrictedSubring
      (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
      (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i)))))}
    (hW : IsWeightFamily W)
    (hUW : ∀ j, algebraMap R (Completion (weightedRestrictedSubring
        (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
        (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i))))) ''
      ({(u (Fin.natAdd k j) : R)} : Set R) = W j)
    (y : Completion (weightedRestrictedSubring W hW)) :
    weightedRestrictedCompletionGaussAlgEquiv u hu hc
        (iterateJoinHom (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i))) hW
          (isWeightFamily_units u) (fun _ ↦ rfl) hUW y) =
      (restrictedFinAddEquiv (r := c)).symm
        (weightedRestrictedIterateGaussEquiv u hu hc hW hUW y) := by
  apply (restrictedFinAddEquiv (r := c)).injective
  rw [RingEquiv.apply_symm_apply,
    ← weightedRestrictedIterateGaussEquiv_iterateSplitHom u hu hc hW hUW,
    ← RingHom.comp_apply, iterateSplitHom_comp_iterateJoinHom, RingHom.id_apply]

/-- `iterateFirstBlockHom` for unit weights intertwines the completed Gauss comparisons with
`restrictedFinAddFirstBlockAlgHom`. -/
@[simp]
theorem weightedRestrictedCompletionGaussAlgEquiv_iterateFirstBlockHom
    (x : Completion (weightedRestrictedSubring
      (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
      (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i))))) :
    weightedRestrictedCompletionGaussAlgEquiv u hu hc
        (iterateFirstBlockHom (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i)))
          (isWeightFamily_units u) (fun _ ↦ rfl) x) =
      restrictedFinAddFirstBlockAlgHom (r := c) (m := m)
        (weightedRestrictedCompletionGaussAlgEquiv (fun i ↦ u (Fin.castAdd m i))
          (fun i ↦ hu (Fin.castAdd m i)) (c := c ∘ Fin.castAdd m)
          (fun i ↦ hc (Fin.castAdd m i)) x) := by
  simpa using DFunLike.congr_fun (iterateFirstBlockHom_gauss_comm
    (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i))) (isWeightFamily_units u) (fun _ ↦ rfl)
    (c := c)
    (eU := (weightedRestrictedCompletionGaussAlgEquiv u hu hc).toRingHom)
    (eT := (weightedRestrictedCompletionGaussAlgEquiv (fun i ↦ u (Fin.castAdd m i))
      (fun i ↦ hu (Fin.castAdd m i)) (c := c ∘ Fin.castAdd m)
      (fun i ↦ hc (Fin.castAdd m i))).toRingHom)
    (continuous_weightedRestrictedCompletionGaussAlgEquiv u hu hc)
    (continuous_weightedRestrictedCompletionGaussAlgEquiv (fun i ↦ u (Fin.castAdd m i))
      (fun i ↦ hu (Fin.castAdd m i)) (fun i ↦ hc (Fin.castAdd m i)))
    (weightedRestrictedCompletionGaussAlgEquiv_coe_weightedC u hu hc)
    (weightedRestrictedCompletionGaussAlgEquiv_coe_weightedX u hu hc)
    (weightedRestrictedCompletionGaussAlgEquiv_coe_weightedC (fun i ↦ u (Fin.castAdd m i))
      (fun i ↦ hu (Fin.castAdd m i)) (fun i ↦ hc (Fin.castAdd m i)))
    (weightedRestrictedCompletionGaussAlgEquiv_coe_weightedX (fun i ↦ u (Fin.castAdd m i))
      (fun i ↦ hu (Fin.castAdd m i)) (fun i ↦ hc (Fin.castAdd m i)))) x

/-- `iterateSplitHom` for unit weights preserves the Gauss norm transported across the completed
Gauss comparisons. -/
theorem norm_weightedRestrictedIterateGaussEquiv_iterateSplitHom
    {W : Fin m → Set (Completion (weightedRestrictedSubring
      (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
      (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i)))))}
    (hW : IsWeightFamily W)
    (hUW : ∀ j, algebraMap R (Completion (weightedRestrictedSubring
        (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
        (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i))))) ''
      ({(u (Fin.natAdd k j) : R)} : Set R) = W j)
    (x : Completion (weightedRestrictedSubring (fun l ↦ ({(u l : R)} : Set R))
      (isWeightFamily_units u))) :
    ‖weightedRestrictedIterateGaussEquiv u hu hc hW hUW
        (iterateSplitHom (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i))) hW
          (isWeightFamily_units u) (fun _ ↦ rfl) hUW x)‖ =
      ‖weightedRestrictedCompletionGaussAlgEquiv u hu hc x‖ := by
  rw [weightedRestrictedIterateGaussEquiv_iterateSplitHom, norm_restrictedFinAddEquiv]

/-- `iterateRingEquiv` for unit weights preserves the Gauss norm transported across the completed
Gauss comparisons. -/
theorem norm_weightedRestrictedIterateGaussEquiv_iterateRingEquiv
    {W : Fin m → Set (Completion (weightedRestrictedSubring
      (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
      (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i)))))}
    (hW : IsWeightFamily W)
    (hUW : ∀ j, algebraMap R (Completion (weightedRestrictedSubring
        (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
        (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i))))) ''
      ({(u (Fin.natAdd k j) : R)} : Set R) = W j)
    (x : Completion (weightedRestrictedSubring (fun l ↦ ({(u l : R)} : Set R))
      (isWeightFamily_units u))) :
    ‖weightedRestrictedIterateGaussEquiv u hu hc hW hUW
        (iterateRingEquiv (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i))) hW
          (isWeightFamily_units u) (fun _ ↦ rfl) hUW x)‖ =
      ‖weightedRestrictedCompletionGaussAlgEquiv u hu hc x‖ := by
  rw [weightedRestrictedIterateGaussEquiv_iterateRingEquiv, norm_restrictedFinAddEquiv]

/-- `iterateJoinHom` for unit weights preserves the Gauss norm transported across the completed
Gauss comparisons. -/
theorem norm_weightedRestrictedCompletionGaussAlgEquiv_iterateJoinHom
    {W : Fin m → Set (Completion (weightedRestrictedSubring
      (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
      (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i)))))}
    (hW : IsWeightFamily W)
    (hUW : ∀ j, algebraMap R (Completion (weightedRestrictedSubring
        (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
        (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i))))) ''
      ({(u (Fin.natAdd k j) : R)} : Set R) = W j)
    (y : Completion (weightedRestrictedSubring W hW)) :
    ‖weightedRestrictedCompletionGaussAlgEquiv u hu hc
        (iterateJoinHom (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i))) hW
          (isWeightFamily_units u) (fun _ ↦ rfl) hUW y)‖ =
      ‖weightedRestrictedIterateGaussEquiv u hu hc hW hUW y‖ := by
  rw [weightedRestrictedCompletionGaussAlgEquiv_iterateJoinHom, norm_restrictedFinAddEquiv_symm]

/-- `iterateFirstBlockHom` for unit weights preserves the Gauss norm transported across the
completed Gauss comparisons. -/
theorem norm_weightedRestrictedCompletionGaussAlgEquiv_iterateFirstBlockHom
    (x : Completion (weightedRestrictedSubring
      (fun i ↦ ({(u (Fin.castAdd m i) : R)} : Set R))
      (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i))))) :
    ‖weightedRestrictedCompletionGaussAlgEquiv u hu hc
        (iterateFirstBlockHom (isWeightFamily_units (fun i ↦ u (Fin.castAdd m i)))
          (isWeightFamily_units u) (fun _ ↦ rfl) x)‖ =
      ‖weightedRestrictedCompletionGaussAlgEquiv (fun i ↦ u (Fin.castAdd m i))
        (fun i ↦ hu (Fin.castAdd m i)) (c := c ∘ Fin.castAdd m)
        (fun i ↦ hc (Fin.castAdd m i)) x‖ := by
  rw [weightedRestrictedCompletionGaussAlgEquiv_iterateFirstBlockHom,
    norm_restrictedFinAddFirstBlockAlgHom]

end UnitWeight

end TauCeti.Huber
