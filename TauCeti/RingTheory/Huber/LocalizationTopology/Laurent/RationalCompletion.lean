/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.LocalizationTopology.RationalCompletion
import TauCeti.RingTheory.Huber.LocalizationTopology.Evaluation
import TauCeti.RingTheory.Huber.LocalizationTopology.ModelEvaluation
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Laurent.Basic

/-!
# Surjectivity of simple Laurent covers for models of completed rational localisations

This file proves Kedlaya–Liu Lemma 2.4.22 for models of completed rational localisations of a
two-piece simple Laurent cover (`IsRationalCompletion.surjective_sub_laurent`).

## Main results

* `TauCeti.Huber.IsRationalCompletion.surjective_sub_laurent` and
  `TauCeti.Huber.IsRationalCompletion.surjective_algebraMap_sub_laurent`: surjectivity of
  `(b₁, b₂) ↦ ρ₁ b₁ - ρ₂ b₂` on a simple Laurent cover.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: Foundations*, Astérisque 371 (2015),
  §2.4, Lemma 2.4.22.
-/

public section

namespace TauCeti.Huber

open UniformSpace TauCeti.Localization

section Uniform

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
  [CompleteSpace A] [T0Space A] [DecidableEq A]

private theorem modelEvalHom_surjective_overlap (P : PairOfDefinition A) (f : A)
    (hT₁₂ : IsOpen (Ideal.span (({f * f, 1} : Finset A) : Set A) : Set A))
    {B₁₂ : Type*} [CommRing B₁₂] [Algebra A B₁₂] (e₁₂ : ratLoc P {f * f, 1} f
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
  rw [show (modelEvalHom P hT₁₂ e₁₂ ![f * f, 1]
      (Fin.forall_fin_two.mpr ⟨by simp, by simp⟩) : _ → B₁₂) = _ from
    funext (modelEvalHom_apply P hT₁₂ e₁₂ ![f * f, 1] _)]
  exact e₁₂.surjective.comp ((P.rationalEvalHom_surjective {f * f, 1} f _ _ ![f * f, 1] _
    hspan hTt).comp (restrictedMvPowerSeriesCompletionEquiv 2 A).symm.surjective)

section Surjective
variable {P : PairOfDefinition A} {f : A} {B₁ B₂ B₁₂ : Type*} [CommRing B₁] [CommRing B₂]
  [CommRing B₁₂] [TopologicalSpace B₁] [TopologicalSpace B₂] [TopologicalSpace B₁₂]
  [Algebra A B₁] [Algebra A B₂] [Algebra A B₁₂]
  {hT₁ : IsOpen (Ideal.span (({f, 1} : Finset A) : Set A) : Set A)}
  {hT₂ : IsOpen (Ideal.span (({1} : Finset A) : Set A) : Set A)}
  {hT₁₂ : IsOpen (Ideal.span (({f * f, 1} : Finset A) : Set A) : Set A)}

/-- **Kedlaya–Liu, Lemma 2.4.22.** For a complete Hausdorff Huber ring `A` and `f : A`,
given models `B₁`, `B₂`, `B₁₂` of `A⟨{f, 1}/1⟩`, `A⟨{1}/f⟩`, and `A⟨{f², 1}/f⟩` with continuous
`A`-algebra maps `ρ₁ : B₁ →ₐ[A] B₁₂` and `ρ₂ : B₂ →ₐ[A] B₁₂`, `(b₁, b₂) ↦ ρ₁ b₁ - ρ₂ b₂` is
surjective. -/
theorem IsRationalCompletion.surjective_sub_laurent
    (h₁ : IsRationalCompletion P {f, 1} 1 hT₁ B₁) (h₂ : IsRationalCompletion P {1} f hT₂ B₂)
    (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ B₁₂) (ρ₁ : B₁ →ₐ[A] B₁₂)
    (ρ₂ : B₂ →ₐ[A] B₁₂) (hc₁ : Continuous ρ₁) (hc₂ : Continuous ρ₂) :
    Function.Surjective fun x : B₁ × B₂ ↦ ρ₁ x.1 - ρ₂ x.2 := by
  let _ := P.toNonarchimedeanRing; have _ : T2Space B₁₂ := h₁₂.t2Space
  have ht₁ : ∀ i : Fin 1, ![f] i ∈ ({f, 1} : Finset A) := fun i ↦ by fin_cases i; simp
  have ht₂ : ∀ i : Fin 1, ![1] i ∈ ({1} : Finset A) := fun i ↦ by fin_cases i; simp
  have ht₁₂ : ∀ i : Fin 2, ![f * f, 1] i ∈ ({f * f, 1} : Finset A) :=
    Fin.forall_fin_two.mpr ⟨by simp, by simp⟩
  let π₂ := modelEvalHom P hT₂ h₂.ratLocEquiv ![1] ht₂
  let π₁₂ := modelEvalHom P hT₁₂ h₁₂.ratLocEquiv ![f * f, 1] ht₁₂
  have hX₀ : π₁₂ (weightedX _ isWeightFamily_one_weight 0) = algebraMap A B₁₂ f :=
    modelEvalHom_X_eq_algebraMap_of_mul P hT₁₂ h₁₂.ratLocEquiv ![f * f, 1] ht₁₂ 0 rfl
  have hmul₁₂ : algebraMap A B₁₂ f * π₁₂ (weightedX _ isWeightFamily_one_weight 1) = 1 :=
    algebraMap_mul_modelEvalHom_X_of_eq_one P hT₁₂ h₁₂.ratLocEquiv ![f * f, 1] ht₁₂ 1 rfl
  have hπ₁₂_cont := continuous_modelEvalHom P hT₁₂ h₁₂.ratLocEquiv
    ![f * f, 1] ht₁₂ h₁₂.continuous_ratLocEquiv
  have hρ₁ := apply_eq_apply_weightedRename (ρ := ρ₁.toRingHom) hc₁
    (continuous_modelEvalHom P hT₁ h₁.ratLocEquiv ![f] ht₁ h₁.continuous_ratLocEquiv)
    hπ₁₂_cont (fun a ↦ by simp [ρ₁.commutes]) fun i ↦ by
      rw [Subsingleton.elim i 0, Fin.castSuccEmb_apply, Fin.castSucc_zero,
        modelEvalHom_X_eq_algebraMap_of_mul P hT₁ h₁.ratLocEquiv ![f] ht₁ 0 (one_mul f).symm,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ρ₁.commutes, ← hX₀]
  have hρ₂ := apply_eq_apply_weightedRename (ρ := ρ₂.toRingHom) hc₂
    (continuous_modelEvalHom P hT₂ h₂.ratLocEquiv ![1] ht₂ h₂.continuous_ratLocEquiv)
    hπ₁₂_cont (fun a ↦ by simp [ρ₂.commutes]) fun i ↦ by
      have hmul₂ : algebraMap A B₁₂ f * ρ₂ (π₂ (weightedX _ isWeightFamily_one_weight 0)) = 1 := by
        rw [← ρ₂.commutes f, ← map_mul,
          algebraMap_mul_modelEvalHom_X_of_eq_one P hT₂ h₂.ratLocEquiv ![1] ht₂ 0 rfl, map_one]
      rw [Subsingleton.elim i 0, Fin.coe_succEmb, Fin.succ_zero_eq_one']
      exact left_inv_eq_right_inv (by rw [mul_comm]; exact hmul₂) hmul₁₂
  have hrel : π₁₂ (1 - weightedX _ isWeightFamily_one_weight 0 *
      weightedX _ isWeightFamily_one_weight 1) = 0 := by
    rw [map_sub, map_one, map_mul, hX₀, hmul₁₂, sub_self]
  intro y; obtain ⟨x₁, x₂, h⟩ := exists_sub_eq_of_surjective_of_map_laurentRelation_eq_zero
    (modelEvalHom_surjective_overlap P f hT₁₂ h₁₂.ratLocEquiv) hρ₁ hρ₂ hrel y
  exact ⟨(x₁, x₂), h⟩

/-- Scalar-tower form of `IsRationalCompletion.surjective_sub_laurent`, for `[Algebra B₁ B₁₂]`
and `[Algebra B₂ B₁₂]`. -/
theorem IsRationalCompletion.surjective_algebraMap_sub_laurent
    [Algebra B₁ B₁₂] [Algebra B₂ B₁₂] [IsScalarTower A B₁ B₁₂] [IsScalarTower A B₂ B₁₂]
    (h₁ : IsRationalCompletion P {f, 1} 1 hT₁ B₁) (h₂ : IsRationalCompletion P {1} f hT₂ B₂)
    (h₁₂ : IsRationalCompletion P {f * f, 1} f hT₁₂ B₁₂)
    (hc₁ : Continuous (algebraMap B₁ B₁₂)) (hc₂ : Continuous (algebraMap B₂ B₁₂)) :
    Function.Surjective fun x : B₁ × B₂ ↦ algebraMap B₁ B₁₂ x.1 - algebraMap B₂ B₁₂ x.2 :=
  h₁.surjective_sub_laurent h₂ h₁₂ (IsScalarTower.toAlgHom A B₁ B₁₂)
    (IsScalarTower.toAlgHom A B₂ B₁₂) hc₁ hc₂
end Surjective

end Uniform

end TauCeti.Huber

end
