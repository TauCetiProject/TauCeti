/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomizedSmoothing.Basic

/-!
# Checks for Gaussian smoothing

A constant strictly between zero and one stays in the interior, a singleton indicator
smooths to zero in positive dimension despite being nonzero at the origin, and on a trivial
space smoothing evaluates the function at its unique point.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open TauCeti.Probability TauCeti.Probability.RandomizedSmoothing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

example (σ : ℝ) (x : E) : smooth σ (fun _ : E => (1 / 2 : ℝ)) x ∈ Ioo 0 1 := by
  rw [smooth_const]
  constructor <;> norm_num

example [Nontrivial E] {σ : ℝ} (hσ : σ ≠ 0) :
    ({0} : Set E).indicator (fun _ => (1 : ℝ)) 0 = 1 ∧
      ∀ x, smooth σ (({0} : Set E).indicator (fun _ => (1 : ℝ))) x = 0 := by
  have hz : ∀ᵐ z ∂stdGaussian E, z ∉ ({0} : Set E) :=
    (stdGaussian_absolutelyContinuous_volume (E := E)).ae_le
      ((countable_singleton (0 : E)).ae_notMem volume)
  have hf : ({0} : Set E).indicator (fun _ => (1 : ℝ)) =ᵐ[stdGaussian E] 0 := by
    filter_upwards [hz] with z hz
    simp [hz]
  refine ⟨by simp, fun x => ?_⟩
  rw [smooth_congr_ae hf hσ x]
  exact smooth_const σ 0 x

example [Subsingleton E] (σ : ℝ) (f : E → ℝ) (x : E) : smooth σ f x = f x := by
  have h : ∀ z : E, x + σ • z = x := fun z => Subsingleton.elim _ _
  simp [smooth_def, h]

example [Subsingleton E] (σ : ℝ) (f : E → ℝ) (hf : f 0 ∈ Icc 0 1) :
    (∀ x, smooth σ f x = 0) ∨ (∀ x, smooth σ f x = 1) ∨
      (∀ x, smooth σ f x ∈ Ioo 0 1) := by
  have heq : f = fun _ => f 0 := funext fun x => congrArg f (Subsingleton.elim _ _)
  rw [heq]
  simp only [smooth_const]
  rcases eq_or_lt_of_le hf.1 with h | h
  · exact Or.inl fun _ => h.symm
  rcases eq_or_lt_of_le hf.2 with h' | h'
  · exact Or.inr (Or.inl fun _ => h')
  · exact Or.inr (Or.inr fun _ => ⟨h, h'⟩)
