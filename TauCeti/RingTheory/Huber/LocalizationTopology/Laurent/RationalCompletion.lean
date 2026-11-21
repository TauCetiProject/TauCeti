/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.RationalCompletion
import TauCeti.RingTheory.Huber.LocalizationTopology.Evaluation
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Laurent.Basic
import TauCeti.Topology.Algebra.Ring.Ideal

/-!
# Simple Laurent covers for models of completed rational localisations

This file proves Kedlaya–Liu's Lemma 2.4.22 for models of the completed rational localisations
forming a two-piece simple Laurent cover (`IsRationalCompletion.surjective_sub_laurent`), and
constructs the unique continuous transition homomorphisms between the pieces and their overlap
(`IsRationalCompletion.existsUnique_laurentLeftAlgHom`,
`IsRationalCompletion.existsUnique_laurentRightAlgHom`, and the canonical `ratLoc` maps
`laurentLeftAlgHom`, `laurentRightAlgHom`).

## Main definitions

* `TauCeti.Huber.laurentLeftAlgHom` and `TauCeti.Huber.laurentRightAlgHom`: the canonical
  continuous `A`-algebra transition maps `A⟨{f, 1}/1⟩ →ₐ[A] A⟨{f², 1}/f⟩` and
  `A⟨{1}/f⟩ →ₐ[A] A⟨{f², 1}/f⟩`.

## Main results

* `TauCeti.Huber.IsRationalCompletion.surjective_sub_laurent` and
  `TauCeti.Huber.IsRationalCompletion.surjective_algebraMap_sub_laurent`: surjectivity of
  `(b₁, b₂) ↦ ρ₁ b₁ - ρ₂ b₂` on a simple Laurent cover (Kedlaya–Liu, Lemma 2.4.22).
* `TauCeti.Huber.IsRationalCompletion.existsUnique_laurentLeftAlgHom` and
  `TauCeti.Huber.IsRationalCompletion.existsUnique_laurentRightAlgHom`: unique continuous
  transition maps from models of `A⟨{f, 1}/1⟩` and `A⟨{1}/f⟩` to a model of `A⟨{f², 1}/f⟩`.
* `TauCeti.Huber.laurentLeftAlgHom_coe` and `TauCeti.Huber.laurentRightAlgHom_coe`: computation
  rules for the canonical transition maps on the dense images of the uncompleted localisations.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: Foundations*, Astérisque 371 (2015),
  §2.4, Lemma 2.4.22.
-/

public section

namespace TauCeti.Huber

open UniformSpace TauCeti.Localization

section Uniform

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]

/-! ### Surjectivity of the difference map on a simple Laurent cover -/

section SimpleLaurent

variable [CompleteSpace A] [T0Space A]

section ModelEval

variable (P : PairOfDefinition A) {T : Finset A} {s : A}
  (hT : IsOpen (Ideal.span (T : Set A) : Set A))
  {B : Type*} [CommRing B] [Algebra A B]
  (e : ratLoc P T s (P.hasDenominatorPower_of_isOpen_span T s _ hT) ≃ₐ[A] B)
  {k : ℕ} (t : Fin k → A) (ht : ∀ i, t i ∈ T)

/-- Evaluation `A⟨X₁, …, Xₖ⟩ → B` from the uncompleted restricted power series ring into a model
`B` of `A⟨T/s⟩`. -/
private noncomputable def modelEvalHom :
    letI := P.toNonarchimedeanRing
    weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight →+* B :=
  letI := P.toNonarchimedeanRing
  e.toRingHom.comp ((P.rationalEvalHom T s (Localization.Away s)
    (P.hasDenominatorPower_of_isOpen_span T s _ hT) t ht).comp
      (restrictedMvPowerSeriesCompletionEquiv k A).symm.toRingHom)

private theorem continuous_modelEvalHom [TopologicalSpace B] (he : Continuous e) :
    letI := P.toNonarchimedeanRing; Continuous (modelEvalHom P hT e t ht) :=
  letI := P.toNonarchimedeanRing
  he.comp ((P.continuous_rationalEvalHom T s _ _ t ht).comp
    uniformContinuous_restrictedMvPowerSeriesCompletionEquiv_symm.continuous)

private theorem modelEvalHom_apply (x : letI := P.toNonarchimedeanRing
    weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    letI := P.toNonarchimedeanRing
    modelEvalHom P hT e t ht x = e (P.rationalEvalHom T s (Localization.Away s)
      (P.hasDenominatorPower_of_isOpen_span T s _ hT) t ht
      ((restrictedMvPowerSeriesCompletionEquiv k A).symm x)) := by
  let _ := P.toNonarchimedeanRing
  simp only [modelEvalHom, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    AlgEquiv.coe_toRingEquiv]

private theorem modelEvalHom_weightedC (a : A) :
    letI := P.toNonarchimedeanRing
    modelEvalHom P hT e t ht (weightedC _ isWeightFamily_one_weight a) = algebraMap A B a := by
  let _ := P.toNonarchimedeanRing
  rw [modelEvalHom_apply, restrictedMvPowerSeriesCompletionEquiv_symm_apply,
    P.rationalEvalHom_coe_weightedC, ← algebraMap_ratLoc, e.commutes]

private theorem modelEvalHom_X_eq_algebraMap_of_mul (i : Fin k) {a : A} (hti : t i = s * a) :
    letI := P.toNonarchimedeanRing
    modelEvalHom P hT e t ht (weightedX _ isWeightFamily_one_weight i) = algebraMap A B a := by
  let _ := P.toNonarchimedeanRing
  rw [modelEvalHom_apply, restrictedMvPowerSeriesCompletionEquiv_symm_apply,
    P.rationalEvalHom_coe_weightedX, hti, divBy_mul_cancel_left a s, ← P.toCompletionLoc_apply,
    ← algebraMap_ratLoc, e.commutes]

private theorem modelEvalHom_X_mul_inv (i : Fin k) (hti : t i = 1) :
    letI := P.toNonarchimedeanRing
    algebraMap A B s * modelEvalHom P hT e t ht (weightedX _ isWeightFamily_one_weight i) = 1 := by
  let _ := P.toNonarchimedeanRing
  let S := Localization.Away s
  let hden := P.hasDenominatorPower_of_isOpen_span T s S hT
  let _ := P.locUniformSpace T s S hden
  have _ := P.isUniformAddGroup_locUniformSpace T s S hden
  have _ := P.isTopologicalRing_locUniformSpace T s S hden
  rw [modelEvalHom_apply, restrictedMvPowerSeriesCompletionEquiv_symm_apply,
    P.rationalEvalHom_coe_weightedX, ← e.commutes s, ← map_mul, algebraMap_ratLoc,
    P.toCompletionLoc_apply, ← Completion.coe_mul, hti, divBy_one,
    IsLocalization.Away.mul_invSelf]
  exact map_one e

end ModelEval

private theorem comp_modelEvalHom_eq_weightedRename (P : PairOfDefinition A)
    {T₁ T₂ : Finset A} {s₁ s₂ : A} (hT₁ : IsOpen (Ideal.span (T₁ : Set A) : Set A))
    (hT₂ : IsOpen (Ideal.span (T₂ : Set A) : Set A))
    {B B₁₂ : Type*} [CommRing B] [TopologicalSpace B] [Algebra A B]
    [CommRing B₁₂] [TopologicalSpace B₁₂] [T2Space B₁₂] [Algebra A B₁₂]
    (e : ratLoc P T₁ s₁ (P.hasDenominatorPower_of_isOpen_span T₁ s₁ _ hT₁) ≃ₐ[A] B)
    (he : Continuous e)
    (e₁₂ : ratLoc P T₂ s₂ (P.hasDenominatorPower_of_isOpen_span T₂ s₂ _ hT₂) ≃ₐ[A] B₁₂)
    (he₁₂ : Continuous e₁₂) (t : Fin 1 → A) (ht : ∀ i, t i ∈ T₁)
    (t₁₂ : Fin 2 → A) (ht₁₂ : ∀ i, t₁₂ i ∈ T₂) (ρ : B →ₐ[A] B₁₂) (hc : Continuous ρ)
    (emb : Fin 1 ↪ Fin 2) (hX : letI := P.toNonarchimedeanRing
      ρ (modelEvalHom P hT₁ e t ht (weightedX _ isWeightFamily_one_weight 0)) =
        modelEvalHom P hT₂ e₁₂ t₁₂ ht₁₂ (weightedX _ isWeightFamily_one_weight (emb 0))) :
    letI := P.toNonarchimedeanRing
    ρ.toRingHom.comp (modelEvalHom P hT₁ e t ht) =
      (modelEvalHom P hT₂ e₁₂ t₁₂ ht₁₂).comp (weightedRename emb isWeightFamily_one_weight
        isWeightFamily_one_weight fun _ ↦ subset_rfl) := by
  let _ := P.toNonarchimedeanRing
  refine weightedRestrictedSubring_ringHom_ext_of_continuous isWeightFamily_one_weight
    (hc.comp (continuous_modelEvalHom P hT₁ e t ht he))
    ((continuous_modelEvalHom P hT₂ e₁₂ t₁₂ ht₁₂ he₁₂).comp (continuous_weightedRename emb _ _ _))
    (fun a ↦ by
      rw [RingHom.comp_apply, RingHom.comp_apply, weightedRename_weightedC,
        modelEvalHom_weightedC, modelEvalHom_weightedC, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, ρ.commutes])
    (fun i ↦ by
      rw [Subsingleton.elim i 0, RingHom.comp_apply, RingHom.comp_apply, weightedRename_weightedX,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hX])

variable [DecidableEq A]

private theorem modelEvalHom_surjective_overlap (P : PairOfDefinition A) (f : A)
    (hT₁₂ : IsOpen (Ideal.span (({f * f, 1} : Finset A) : Set A) : Set A))
    {B₁₂ : Type*} [CommRing B₁₂] [Algebra A B₁₂]
    (e₁₂ : ratLoc P {f * f, 1} f
      (P.hasDenominatorPower_of_isOpen_span ({f * f, 1} : Finset A) f _ hT₁₂) ≃ₐ[A] B₁₂) :
    letI := P.toNonarchimedeanRing
    Function.Surjective (modelEvalHom P hT₁₂ e₁₂ ![f * f, 1]
      (Fin.forall_fin_two.mpr ⟨by simp, by simp⟩)) := by
  let _ := P.toNonarchimedeanRing
  have _ : (nhds (0 : A)).IsCountablyGenerated := P.hasBasis_nhds_zero.isCountablyGenerated
  have hspan : Ideal.span (insert f (Set.range (![f * f, 1] : Fin 2 → A))) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_range.mpr ⟨1, rfl⟩))) isUnit_one
  have hTt : Set.range (fun y : ↥({f * f, 1} : Finset A) ↦ (divBy (y : A) f : Localization.Away f))
      ⊆ Set.range fun i : Fin 2 ↦ (divBy (![f * f, 1] i) f : Localization.Away f) := by
    rintro _ ⟨⟨y, hy⟩, rfl⟩
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact ⟨0, rfl⟩
    · rcases Finset.mem_singleton.mp hy with rfl; exact ⟨1, rfl⟩
  exact e₁₂.surjective.comp ((P.rationalEvalHom_surjective {f * f, 1} f _ _ ![f * f, 1] _
    hspan hTt).comp (restrictedMvPowerSeriesCompletionEquiv 2 A).symm.surjective)

section Surjective

variable {P : PairOfDefinition A} {f : A}
  {B₁ B₂ B₁₂ : Type*} [CommRing B₁] [CommRing B₂] [CommRing B₁₂]
  [TopologicalSpace B₁] [TopologicalSpace B₂] [TopologicalSpace B₁₂]
  [Algebra A B₁] [Algebra A B₂] [Algebra A B₁₂]
  {hT₁ : IsOpen (Ideal.span (({f, 1} : Finset A) : Set A) : Set A)}
  {hT₂ : IsOpen (Ideal.span (({1} : Finset A) : Set A) : Set A)}
  {hT₁₂ : IsOpen (Ideal.span (({f * f, 1} : Finset A) : Set A) : Set A)}

/-- **Kedlaya–Liu, Lemma 2.4.22.** For a complete Hausdorff Huber ring `A` and any `f : A`,
given models `B₁`, `B₂`, `B₁₂` of the simple Laurent pieces `A⟨f, 1/1⟩`, `A⟨1/f⟩`, and their
overlap `A⟨f², 1/f⟩`, together with continuous `A`-algebra maps `ρ₁ : B₁ →ₐ[A] B₁₂` and
`ρ₂ : B₂ →ₐ[A] B₁₂`, the difference map `(b₁, b₂) ↦ ρ₁ b₁ - ρ₂ b₂` is surjective. -/
theorem IsRationalCompletion.surjective_sub_laurent
    (h₁ : IsRationalCompletion P {f, 1} 1 hT₁ B₁) (h₂ : IsRationalCompletion P {1} f hT₂ B₂)
    (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ B₁₂)
    (ρ₁ : B₁ →ₐ[A] B₁₂) (ρ₂ : B₂ →ₐ[A] B₁₂) (hc₁ : Continuous ρ₁) (hc₂ : Continuous ρ₂) :
    Function.Surjective fun x : B₁ × B₂ ↦ ρ₁ x.1 - ρ₂ x.2 := by
  let _ := P.toNonarchimedeanRing
  have _ : T2Space B₁₂ := h₁₂.t2Space
  obtain ⟨e₁, he₁, -⟩ := (isRationalCompletion_iff_ratLoc _ _ _ _ _).mp h₁
  obtain ⟨e₂, he₂, -⟩ := (isRationalCompletion_iff_ratLoc _ _ _ _ _).mp h₂
  obtain ⟨e₁₂, he₁₂, -⟩ := (isRationalCompletion_iff_ratLoc _ _ _ _ _).mp h₁₂
  have ht₁ : ∀ i : Fin 1, ![f] i ∈ ({f, 1} : Finset A) := fun i ↦ by fin_cases i; simp
  have ht₂ : ∀ i : Fin 1, ![1] i ∈ ({1} : Finset A) := fun i ↦ by fin_cases i; simp
  have ht₁₂ : ∀ i : Fin 2, ![f * f, 1] i ∈ ({f * f, 1} : Finset A) :=
    Fin.forall_fin_two.mpr ⟨by simp, by simp⟩
  let π₁ := modelEvalHom P hT₁ e₁ ![f] ht₁
  let π₂ := modelEvalHom P hT₂ e₂ ![1] ht₂
  let π₁₂ := modelEvalHom P hT₁₂ e₁₂ ![f * f, 1] ht₁₂
  have hX₀ : π₁₂ (weightedX _ isWeightFamily_one_weight 0) = algebraMap A B₁₂ f :=
    modelEvalHom_X_eq_algebraMap_of_mul P hT₁₂ e₁₂ ![f * f, 1] ht₁₂ 0 rfl
  have hmul₁₂ : algebraMap A B₁₂ f * π₁₂ (weightedX _ isWeightFamily_one_weight 1) = 1 :=
    modelEvalHom_X_mul_inv P hT₁₂ e₁₂ ![f * f, 1] ht₁₂ 1 rfl
  have hρ₁ := comp_modelEvalHom_eq_weightedRename P hT₁ hT₁₂ e₁ he₁ e₁₂ he₁₂
    ![f] ht₁ ![f * f, 1] ht₁₂ ρ₁ hc₁ Fin.castSuccEmb (by
      rw [Fin.castSuccEmb_apply, Fin.castSucc_zero,
        modelEvalHom_X_eq_algebraMap_of_mul P hT₁ e₁ ![f] ht₁ 0 (one_mul f).symm, ρ₁.commutes]
      exact hX₀.symm)
  have hρ₂ := comp_modelEvalHom_eq_weightedRename P hT₂ hT₁₂ e₂ he₂ e₁₂ he₁₂
    ![1] ht₂ ![f * f, 1] ht₁₂ ρ₂ hc₂ (Fin.succEmb 1) (by
      have hmul₂ : algebraMap A B₁₂ f *
          ρ₂ (π₂ (weightedX _ isWeightFamily_one_weight 0)) = 1 := by
        rw [← ρ₂.commutes f, ← map_mul,
          modelEvalHom_X_mul_inv P hT₂ e₂ ![1] ht₂ 0 rfl, map_one]
      rw [Fin.coe_succEmb, Fin.succ_zero_eq_one']
      exact left_inv_eq_right_inv (by rw [mul_comm]; exact hmul₂) hmul₁₂)
  intro y
  obtain ⟨u, rfl⟩ := modelEvalHom_surjective_overlap P f hT₁₂ e₁₂ y
  obtain ⟨⟨g, h⟩, hgh⟩ := laurentDiff_surjective A (Ideal.Quotient.mk (laurentIdeal A) u)
  rw [laurentDiff_apply, Ideal.Quotient.eq, mem_laurentIdeal] at hgh
  obtain ⟨w, hw⟩ := hgh
  refine ⟨(π₁ g, π₂ h), ?_⟩
  have hrel : π₁₂ (1 - weightedX _ isWeightFamily_one_weight 0 *
      weightedX _ isWeightFamily_one_weight 1) = 0 := by
    rw [map_sub, map_one, map_mul, hX₀, hmul₁₂, sub_self]
  have hsub := congrArg π₁₂ hw
  rw [map_sub, map_sub, map_mul, hrel, zero_mul, sub_eq_zero] at hsub
  have hρ₁g := RingHom.congr_fun hρ₁ g
  have hρ₂h := RingHom.congr_fun hρ₂ h
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hρ₁g hρ₂h
  dsimp only [π₁, π₂, π₁₂] at hsub ⊢
  rwa [hρ₁g, hρ₂h]

/-- Scalar-tower form of `IsRationalCompletion.surjective_sub_laurent`, for `B₁ → B₁₂` and
`B₂ → B₁₂` given as `[Algebra B₁ B₁₂]` and `[Algebra B₂ B₁₂]`. -/
theorem IsRationalCompletion.surjective_algebraMap_sub_laurent
    [Algebra B₁ B₁₂] [Algebra B₂ B₁₂] [IsScalarTower A B₁ B₁₂] [IsScalarTower A B₂ B₁₂]
    (h₁ : IsRationalCompletion P {f, 1} 1 hT₁ B₁) (h₂ : IsRationalCompletion P {1} f hT₂ B₂)
    (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ B₁₂)
    (hc₁ : Continuous (algebraMap B₁ B₁₂)) (hc₂ : Continuous (algebraMap B₂ B₁₂)) :
    Function.Surjective fun x : B₁ × B₂ ↦ algebraMap B₁ B₁₂ x.1 - algebraMap B₂ B₁₂ x.2 :=
  h₁.surjective_sub_laurent h₂ h₁₂ (IsScalarTower.toAlgHom A B₁ B₁₂)
    (IsScalarTower.toAlgHom A B₂ B₁₂) hc₁ hc₂

end Surjective

end SimpleLaurent

end Uniform

section LaurentTransition

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [DecidableEq A]
  {P : PairOfDefinition A} {f : A} {B₁₂ : Type*} [CommRing B₁₂] [TopologicalSpace B₁₂]
  [Algebra A B₁₂] {hT₁₂ : IsOpen (Ideal.span (({f * f, 1} : Finset A) : Set A) : Set A)}

/-- There is a unique continuous `A`-algebra transition map `B₁ →ₐ[A] B₁₂` from any model `B₁` of
`A⟨f, 1/1⟩` to any model `B₁₂` of `A⟨f², 1/f⟩`: in `B₁₂`, `f = f² / f` is a distinguished
fraction and `1 / 1 = 1`. -/
theorem IsRationalCompletion.existsUnique_laurentLeftAlgHom {B₁ : Type*} [CommRing B₁]
    [TopologicalSpace B₁] [Algebra A B₁]
    {hT₁ : IsOpen (Ideal.span (({f, 1} : Finset A) : Set A) : Set A)}
    (h₁ : IsRationalCompletion P {f, 1} 1 hT₁ B₁)
    (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ B₁₂) :
    ∃! ρ₁ : B₁ →ₐ[A] B₁₂, Continuous ρ₁ :=
  h₁.existsUnique_continuous_algHom_of_refines h₁₂ (one_mul f).symm fun t ht ↦
    (Finset.mem_insert.mp ht).elim (fun h ↦ Or.inr (by simp [h]))
      (fun h ↦ Or.inl (Finset.mem_singleton.mp h))

/-- There is a unique continuous `A`-algebra transition map `B₂ →ₐ[A] B₁₂` from any model `B₂` of
`A⟨1/f⟩` to any model `B₁₂` of `A⟨f², 1/f⟩`. -/
theorem IsRationalCompletion.existsUnique_laurentRightAlgHom {B₂ : Type*} [CommRing B₂]
    [TopologicalSpace B₂] [Algebra A B₂]
    {hT₂ : IsOpen (Ideal.span (({1} : Finset A) : Set A) : Set A)}
    (h₂ : IsRationalCompletion P {1} f hT₂ B₂)
    (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ B₁₂) :
    ∃! ρ₂ : B₂ →ₐ[A] B₁₂, Continuous ρ₂ :=
  h₂.existsUnique_continuous_algHom_of_refines h₁₂ (mul_one f).symm fun t ht ↦
    Or.inr (by rw [Finset.mem_singleton.mp ht]; simp)

/-- The canonical continuous `A`-algebra transition map `A⟨{f, 1}/1⟩ →ₐ[A] A⟨{f², 1}/f⟩` between
the canonical `ratLoc` models of the first Laurent piece and the overlap. -/
noncomputable def laurentLeftAlgHom (P : PairOfDefinition A) (f : A)
    {hden₁ : P.HasDenominatorPower ({f, 1} : Finset A) 1 (Localization.Away (1 : A))}
    {hden₁₂ : P.HasDenominatorPower ({f * f, 1} : Finset A) f (Localization.Away f)} :
    ratLoc P {f, 1} 1 hden₁ →ₐ[A] ratLoc P {f * f, 1} f hden₁₂ :=
  ((isRationalCompletion_ratLoc P {f, 1} 1
      (isOpen_span_of_one_mem (by simp))).existsUnique_laurentLeftAlgHom
    (isRationalCompletion_ratLoc P {f * f, 1} f
      (isOpen_span_of_one_mem (by simp)))).choose

/-- `laurentLeftAlgHom` is continuous. -/
theorem continuous_laurentLeftAlgHom (P : PairOfDefinition A) (f : A)
    {hden₁ : P.HasDenominatorPower ({f, 1} : Finset A) 1 (Localization.Away (1 : A))}
    {hden₁₂ : P.HasDenominatorPower ({f * f, 1} : Finset A) f (Localization.Away f)} :
    Continuous (laurentLeftAlgHom P f (hden₁ := hden₁) (hden₁₂ := hden₁₂)) :=
  ((isRationalCompletion_ratLoc P {f, 1} 1
      (isOpen_span_of_one_mem (by simp))).existsUnique_laurentLeftAlgHom
    (isRationalCompletion_ratLoc P {f * f, 1} f
      (isOpen_span_of_one_mem (by simp)))).choose_spec.1

/-- On the dense image of `A₁`, `laurentLeftAlgHom` acts by the localisation map sending `1` to
`f / f`. -/
@[simp]
theorem laurentLeftAlgHom_coe (P : PairOfDefinition A) (f : A)
    {hden₁ : P.HasDenominatorPower ({f, 1} : Finset A) 1 (Localization.Away (1 : A))}
    {hden₁₂ : P.HasDenominatorPower ({f * f, 1} : Finset A) f (Localization.Away f)}
    (x : Localization.Away (1 : A)) :
    laurentLeftAlgHom P f (hden₁ := hden₁) (hden₁₂ := hden₁₂)
        (@UniformSpace.Completion.coe' (Localization.Away (1 : A))
          (P.locUniformSpace ({f, 1} : Finset A) 1 (Localization.Away (1 : A)) hden₁) x) =
      @UniformSpace.Completion.coe' (Localization.Away f)
        (P.locUniformSpace ({f * f, 1} : Finset A) f (Localization.Away f) hden₁₂)
        (IsLocalization.Away.lift (1 : A)
          (IsLocalization.Away.isUnit_of_dvd f ⟨f, (one_mul f).symm⟩) x) := by
  let _ := P.locUniformSpace ({f, 1} : Finset A) 1 (Localization.Away (1 : A)) hden₁
  have _ := P.isUniformAddGroup_locUniformSpace ({f, 1} : Finset A) 1
    (Localization.Away (1 : A)) hden₁
  have _ := P.isTopologicalRing_locUniformSpace ({f, 1} : Finset A) 1
    (Localization.Away (1 : A)) hden₁
  let _ := P.locUniformSpace ({f * f, 1} : Finset A) f (Localization.Away f) hden₁₂
  have _ := P.isUniformAddGroup_locUniformSpace ({f * f, 1} : Finset A) f
    (Localization.Away f) hden₁₂
  have _ := P.isTopologicalRing_locUniformSpace ({f * f, 1} : Finset A) f
    (Localization.Away f) hden₁₂
  have h : (laurentLeftAlgHom P f (hden₁ := hden₁) (hden₁₂ := hden₁₂)).toRingHom.comp
      UniformSpace.Completion.coeRingHom =
      UniformSpace.Completion.coeRingHom.comp (IsLocalization.Away.lift (1 : A)
        (IsLocalization.Away.isUnit_of_dvd f ⟨f, (one_mul f).symm⟩)) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (1 : A)) (RingHom.ext fun a ↦ ?_)
    simp only [RingHom.coe_comp, Function.comp_apply, UniformSpace.Completion.coe_coeRingHom,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, IsLocalization.Away.lift_eq]
    rw [← P.toCompletionLoc_apply ({f, 1} : Finset A) 1 (Localization.Away (1 : A)) hden₁ a,
      ← algebraMap_ratLoc, (laurentLeftAlgHom P f).commutes a, algebraMap_ratLoc,
      P.toCompletionLoc_apply]
  exact RingHom.congr_fun h x

/-- The canonical continuous `A`-algebra transition map `A⟨{1}/f⟩ →ₐ[A] A⟨{f², 1}/f⟩` between
the canonical `ratLoc` models of the second Laurent piece and the overlap. -/
noncomputable def laurentRightAlgHom (P : PairOfDefinition A) (f : A)
    {hden₂ : P.HasDenominatorPower ({1} : Finset A) f (Localization.Away f)}
    {hden₁₂ : P.HasDenominatorPower ({f * f, 1} : Finset A) f (Localization.Away f)} :
    ratLoc P {1} f hden₂ →ₐ[A] ratLoc P {f * f, 1} f hden₁₂ :=
  ((isRationalCompletion_ratLoc P {1} f
      (isOpen_span_of_one_mem (by simp))).existsUnique_laurentRightAlgHom
    (isRationalCompletion_ratLoc P {f * f, 1} f
      (isOpen_span_of_one_mem (by simp)))).choose

/-- `laurentRightAlgHom` is continuous. -/
theorem continuous_laurentRightAlgHom (P : PairOfDefinition A) (f : A)
    {hden₂ : P.HasDenominatorPower ({1} : Finset A) f (Localization.Away f)}
    {hden₁₂ : P.HasDenominatorPower ({f * f, 1} : Finset A) f (Localization.Away f)} :
    Continuous (laurentRightAlgHom P f (hden₂ := hden₂) (hden₁₂ := hden₁₂)) :=
  ((isRationalCompletion_ratLoc P {1} f
      (isOpen_span_of_one_mem (by simp))).existsUnique_laurentRightAlgHom
    (isRationalCompletion_ratLoc P {f * f, 1} f
      (isOpen_span_of_one_mem (by simp)))).choose_spec.1

/-- On the dense image of `A_f`, `laurentRightAlgHom` fixes each fraction elementwise. -/
@[simp]
theorem laurentRightAlgHom_coe (P : PairOfDefinition A) (f : A)
    {hden₂ : P.HasDenominatorPower ({1} : Finset A) f (Localization.Away f)}
    {hden₁₂ : P.HasDenominatorPower ({f * f, 1} : Finset A) f (Localization.Away f)}
    (x : Localization.Away f) :
    laurentRightAlgHom P f (hden₂ := hden₂) (hden₁₂ := hden₁₂)
        (@UniformSpace.Completion.coe' (Localization.Away f)
          (P.locUniformSpace ({1} : Finset A) f (Localization.Away f) hden₂) x) =
      @UniformSpace.Completion.coe' (Localization.Away f)
        (P.locUniformSpace ({f * f, 1} : Finset A) f (Localization.Away f) hden₁₂) x := by
  let c₂ : Localization.Away f →+* ratLoc P {1} f hden₂ :=
    let _ := P.locUniformSpace ({1} : Finset A) f (Localization.Away f) hden₂
    have _ := P.isUniformAddGroup_locUniformSpace ({1} : Finset A) f (Localization.Away f) hden₂
    have _ := P.isTopologicalRing_locUniformSpace ({1} : Finset A) f (Localization.Away f) hden₂
    UniformSpace.Completion.coeRingHom
  let c₁₂ : Localization.Away f →+* ratLoc P {f * f, 1} f hden₁₂ :=
    let _ := P.locUniformSpace ({f * f, 1} : Finset A) f (Localization.Away f) hden₁₂
    have _ := P.isUniformAddGroup_locUniformSpace ({f * f, 1} : Finset A) f
      (Localization.Away f) hden₁₂
    have _ := P.isTopologicalRing_locUniformSpace ({f * f, 1} : Finset A) f
      (Localization.Away f) hden₁₂
    UniformSpace.Completion.coeRingHom
  have h : (laurentRightAlgHom P f (hden₂ := hden₂) (hden₁₂ := hden₁₂)).toRingHom.comp c₂ =
      c₁₂ := by
    refine IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun a ↦ ?_)
    have hc₂ : c₂ (algebraMap A (Localization.Away f) a) =
        algebraMap A (ratLoc P {1} f hden₂) a := by
      rw [algebraMap_ratLoc, P.toCompletionLoc_apply]
      rfl
    have hc₁₂ : c₁₂ (algebraMap A (Localization.Away f) a) =
        algebraMap A (ratLoc P {f * f, 1} f hden₁₂) a := by
      rw [algebraMap_ratLoc, P.toCompletionLoc_apply]
      rfl
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      hc₂, hc₁₂, (laurentRightAlgHom P f).commutes]
  exact RingHom.congr_fun h x

end LaurentTransition

end TauCeti.Huber

end
