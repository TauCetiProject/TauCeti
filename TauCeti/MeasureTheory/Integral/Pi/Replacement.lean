/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Coordinate replacement in finite product measures

A uniform bound on the change of the integral in each coordinate gives a sum bound
for the change between two product laws. A coordinate can itself be vector-valued.
-/

public section

open Finset

namespace MeasureTheory

variable {ι α E : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {f : (ι → α) → E}

private theorem norm_integral_pi_sub_integral_pi_le_of_eq_off
    (μ ν : ι → Measure α) [∀ j, IsProbabilityMeasure (μ j)]
    [∀ j, IsProbabilityMeasure (ν j)] (i : ι) (heq : ∀ j ≠ i, μ j = ν j)
    (hμ : Integrable f (Measure.pi μ)) (hν : Integrable f (Measure.pi ν)) {C : ℝ}
    (hC : ∀ x, ‖(∫ t, f ((Equiv.piSplitAt i (fun _ : ι ↦ α)).symm (t, x)) ∂μ i) -
      ∫ t, f ((Equiv.piSplitAt i (fun _ : ι ↦ α)).symm (t, x)) ∂ν i‖ ≤ C) :
    ‖(∫ x, f x ∂Measure.pi μ) - ∫ x, f x ∂Measure.pi ν‖ ≤ C := by
  let e : (ι → α) ≃ᵐ α × ({j // j ≠ i} → α) :=
    { Equiv.piSplitAt i (fun _ : ι ↦ α) with
      measurable_toFun := (TauCeti.measurePreserving_piSplitAt μ i).measurable
      measurable_invFun := by
        refine measurable_pi_iff.mpr fun j ↦ ?_
        by_cases hj : j = i
        · subst j
          simpa [Equiv.piSplitAt] using (measurable_fst :
            Measurable (Prod.fst : α × ({j // j ≠ i} → α) → α))
        · simpa [Equiv.piSplitAt, hj, Function.comp_def] using
            (measurable_pi_apply (⟨j, hj⟩ : {j // j ≠ i})).comp measurable_snd }
  have hr : (fun j : {j // j ≠ i} ↦ ν j) = (fun j : {j // j ≠ i} ↦ μ j) :=
    funext fun j ↦ (heq j j.property).symm
  have hprod (ρ : ι → Measure α) [∀ j, IsProbabilityMeasure (ρ j)]
      (hint : Integrable f (Measure.pi ρ)) :
      Integrable (fun p ↦ f (e.symm p)) ((ρ i).prod (Measure.pi fun j : {j // j ≠ i} ↦ ρ j)) ∧
        (∫ x, f x ∂Measure.pi ρ) = ∫ p, f (e.symm p)
          ∂((ρ i).prod (Measure.pi fun j : {j // j ≠ i} ↦ ρ j)) := by
    have he := MeasurePreserving.symm e (TauCeti.measurePreserving_piSplitAt ρ i)
    exact ⟨he.integrable_comp_of_integrable hint, (he.integral_comp' f).symm⟩
  obtain ⟨hμ', hμeq⟩ := hprod μ hμ
  obtain ⟨hν', hνeq⟩ := hprod ν hν
  rw [hμeq, hνeq, integral_prod_symm _ hμ', integral_prod_symm _ hν', hr,
    ← integral_sub hμ'.integral_prod_right (hr ▸ hν'.integral_prod_right)]
  refine (norm_integral_le_of_norm_le_const (C := C) ?_).trans (by simp)
  exact Filter.Eventually.of_forall fun x ↦ hC x

/-- If the change in each one-coordinate integral is bounded by the corresponding term of
the sum, uniformly in the other coordinates, their sum bounds the change of the product
integral. Integrability is required under all the intermediate product laws. -/
theorem norm_integral_pi_sub_integral_pi_le_of_splitAt
    (μ ν : ι → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, IsProbabilityMeasure (ν i)]
    (hf : ∀ s : Finset ι, Integrable f (Measure.pi fun i ↦ if i ∈ s then ν i else μ i))
    (C : ι → ℝ)
    (hC : ∀ i x, ‖(∫ t, f ((Equiv.piSplitAt i (fun _ : ι ↦ α)).symm (t, x)) ∂μ i) -
      ∫ t, f ((Equiv.piSplitAt i (fun _ : ι ↦ α)).symm (t, x)) ∂ν i‖ ≤ C i) :
    ‖(∫ x, f x ∂Measure.pi μ) - ∫ x, f x ∂Measure.pi ν‖ ≤ ∑ i, C i := by
  let ρ (s : Finset ι) (i : ι) := if i ∈ s then ν i else μ i
  have (s : Finset ι) (i : ι) : IsProbabilityMeasure (ρ s i) := by
    dsimp [ρ]
    split <;> infer_instance
  let F (s : Finset ι) := ∫ x, f x ∂Measure.pi (ρ s)
  have hstep (s : Finset ι) (i : ι) (hi : i ∉ s) : ‖F s - F (insert i s)‖ ≤ C i := by
    apply norm_integral_pi_sub_integral_pi_le_of_eq_off (ρ s) (ρ (insert i s)) i
      (fun j hj ↦ by simp [ρ, hj]) (hf s) (hf (insert i s))
    simpa only [ρ, hi, mem_insert_self, ite_true, ite_false] using hC i
  have h (s : Finset ι) : ‖F ∅ - F s‖ ≤ ∑ i ∈ s, C i := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [sum_insert hi]
      exact (norm_sub_le_norm_sub_add_norm_sub (F ∅) (F s) (F (insert i s))).trans
        (by linarith [hstep s i hi])
  simpa [F, ρ] using h univ

end MeasureTheory
