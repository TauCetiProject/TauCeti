/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import TauCeti.MeasureTheory.Measure.ProjectiveLimit.Countable
public import TauCeti.Probability.Process.Kolmogorov
public import Mathlib.Probability.BrownianMotion.GaussianProjectiveFamily

/-!
# Brownian laws on countable time sets

Construct the Gaussian Brownian skeleton on any countable subset of nonnegative real time.
Its finite-dimensional laws are Mathlib's `BrownianReal.projectiveFamily`, not independent
Gaussian marginals. Its increments satisfy the fourth-moment Kolmogorov condition, so this
construction supplies the countable-time input for continuous-modification arguments.
No path continuity or law on continuous path space is asserted here.

The construction combines `TauCeti.Measure.exists_isProjectiveLimit_of_countable` with
Mathlib's Gaussian projective family. See Karatzas–Shreve, *Brownian Motion and Stochastic
Calculus*, second edition, Chapter 2, §2, for the Gaussian skeleton construction.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace TauCeti

/-- A law with the Brownian finite-dimensional distributions on a time set has centered
Gaussian increments, including increments of zero length. -/
theorem hasLaw_sub_of_brownian_finset {S : Set ℝ≥0} {P : Measure (S → ℝ)}
    (hP : ∀ J : Finset S, MeasurePreserving
      (fun (x : S → ℝ) (i : J.map (Function.Embedding.subtype (· ∈ S))) ↦
        x ((J.equivMap (Function.Embedding.subtype (· ∈ S))).symm i)) P
      (BrownianReal.projectiveFamily (J.map (Function.Embedding.subtype (· ∈ S))))) (s t : S) :
    HasLaw (fun x ↦ x s - x t) (gaussianReal 0 (nndist s.1 t.1)) P := by
  classical
  let J : Finset S := {s, t}
  let e := Function.Embedding.subtype (· ∈ S)
  let a : J := ⟨s, by simp [J]⟩
  let b : J := ⟨t, by simp [J]⟩
  have h := (BrownianReal.measurePreserving_eval_sub_eval_projectiveFamily (J.map e)
    (J.equivMap e a) (J.equivMap e b)).comp (hP J)
  dsimp only [e] at h
  simpa only [Function.comp_def, Equiv.symm_apply_apply, Finset.equivMap_apply_coe,
    Function.Embedding.subtype_apply, a, b] using h.hasLaw

/-- On every countable time set there is a probability law with the Brownian finite-dimensional
Gaussian laws and the fourth-moment Kolmogorov bound. Finite image coordinates retain their
original nonnegative-real labels. In particular, this applies to nonnegative rational times. -/
theorem exists_brownianLaw_on_countable (S : Set ℝ≥0) [Countable S] :
    ∃ P : Measure (S → ℝ), IsProbabilityMeasure P ∧
      (∀ J : Finset S, MeasurePreserving
        (fun (x : S → ℝ) (i : J.map (Function.Embedding.subtype (· ∈ S))) ↦
          x ((J.equivMap (Function.Embedding.subtype (· ∈ S))).symm i)) P
        (BrownianReal.projectiveFamily (J.map (Function.Embedding.subtype (· ∈ S))))) ∧
      IsKolmogorovProcess (fun (t : S) (x : S → ℝ) ↦ x t) P 4 2 3 := by
  obtain ⟨P, hprob, hP⟩ := Function.Embedding.exists_measurePreserving_finset_map_of_countable
    (Function.Embedding.subtype (· ∈ S)) BrownianReal.projectiveFamily
    BrownianReal.isProjectiveMeasureFamily_projectiveFamily
  refine ⟨P, hprob, hP, isKolmogorovProcess_of_hasLaw_sub_gaussianReal
    (fun t ↦ measurable_pi_apply t) ?_⟩
  intro s t
  exact hasLaw_sub_of_brownian_finset hP s t

end TauCeti
