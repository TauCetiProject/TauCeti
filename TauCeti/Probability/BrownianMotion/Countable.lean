/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import Mathlib.Probability.BrownianMotion.GaussianProjectiveFamily
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Process.Kolmogorov
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Def
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

import TauCeti.MeasureTheory.Measure.ProjectiveLimit.Countable
import TauCeti.Probability.Process.Kolmogorov
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-!
# Brownian Gaussian skeletons on countable time sets

Construct a Gaussian skeleton on any countable subset of nonnegative real time, with
Mathlib's `BrownianReal.projectiveFamily` as its finite-dimensional laws, not independent
Gaussian marginals. The coordinate process satisfies every positive even-moment Kolmogorov
bound. No path continuity or law on continuous path space is asserted here.

The finite-dimensional laws are indexed directly by finite sets of nonnegative real times
contained in the time set. Their single-coordinate Gaussian laws, increment laws, covariance
and `IsGaussianProcess` property are available for arbitrary processes with these laws.

The construction uses `Set.exists_measurePreserving_finset_of_countable`
and `ProbabilityTheory.isKolmogorovProcess_of_hasLaw_sub_gaussianReal`.
See Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
Chapter 2, §2, for the Gaussian skeleton construction.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Nat

namespace TauCeti

section Laws

variable {S : Set ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : S → Ω → ℝ}
  (hX : ∀ (I : Finset ℝ≥0) (hI : (I : Set ℝ≥0) ⊆ S),
    HasLaw (fun ω (i : I) ↦ X ⟨i.1, hI i.2⟩ ω) (BrownianReal.projectiveFamily I) P)

include hX

/-- A process with the Brownian finite-dimensional laws has centered Gaussian marginals
with variance equal to the time. -/
theorem hasLaw_gaussianReal_of_hasLaw_brownianRealProjectiveFamily (s : S) :
    HasLaw (X s) (gaussianReal 0 s.1) P := by
  classical
  let I : Finset ℝ≥0 := {s.1}
  have hI : (I : Set ℝ≥0) ⊆ S := by simp [I]
  exact (BrownianReal.measurePreserving_eval_projectiveFamily
    (⟨s.1, by simp [I]⟩ : I)).comp_hasLaw (hX I hI)

/-- A process with the Brownian finite-dimensional laws has centered Gaussian increments,
including increments of zero length. No assumption on its sample space is needed. -/
theorem hasLaw_sub_gaussianReal_of_hasLaw_brownianRealProjectiveFamily (s t : S) :
    HasLaw (fun ω ↦ X s ω - X t ω) (gaussianReal 0 (nndist s.1 t.1)) P := by
  classical
  let I : Finset ℝ≥0 := {s.1, t.1}
  have hI : (I : Set ℝ≥0) ⊆ S := by
    simp [I, Set.insert_subset_iff, Set.singleton_subset_iff]
  exact (BrownianReal.measurePreserving_eval_sub_eval_projectiveFamily I
    ⟨s.1, by simp [I]⟩ ⟨t.1, by simp [I]⟩).comp_hasLaw (hX I hI)

/-- Brownian finite-dimensional laws give covariance `min s t`, not independent marginals. -/
theorem covariance_eq_min_of_hasLaw_brownianRealProjectiveFamily (s t : S) :
    cov[X s, X t; P] = min (s.1 : ℝ) (t.1 : ℝ) := by
  classical
  let I : Finset ℝ≥0 := {s.1, t.1}
  have hI : (I : Set ℝ≥0) ⊆ S := by
    simp [I, Set.insert_subset_iff, Set.singleton_subset_iff]
  have h := (hX I hI).covariance_comp
    (f := fun x ↦ x ⟨s.1, by simp [I]⟩) (g := fun x ↦ x ⟨t.1, by simp [I]⟩)
    (measurable_pi_apply _).aemeasurable (measurable_pi_apply _).aemeasurable
  exact h.trans (BrownianReal.covariance_eval_projectiveFamily I _ _)

/-- A process with the Brownian finite-dimensional laws is a Gaussian process. -/
theorem isGaussianProcess_of_hasLaw_brownianRealProjectiveFamily : IsGaussianProcess X P := by
  constructor
  intro J
  let e := Function.Embedding.subtype (· ∈ S)
  have hI : (↑(J.map e) : Set ℝ≥0) ⊆ S := J.map_subtype_subset
  let L : (J.map e → ℝ) →L[ℝ] (J → ℝ) :=
    ContinuousLinearMap.pi fun j ↦ ContinuousLinearMap.proj (R := ℝ) (J.equivMap e j)
  convert (hX (J.map e) hI).hasGaussianLaw.map L using 1
  ext ω j
  simp [L, e]

end Laws

/-- Every countable set of nonnegative real times supports a probability law with the Brownian
finite-dimensional Gaussian laws and all positive even-moment Kolmogorov bounds. Finite time
sets are indexed directly by their original labels. In particular, this applies to nonnegative
rational times. The choice `n = 2` gives exponents 4 and 2 and constant 3. -/
theorem exists_measurePreserving_brownianRealProjectiveFamily_isKolmogorovProcess_of_countable
    (S : Set ℝ≥0) [Countable S] :
    ∃ P : Measure (S → ℝ), IsProbabilityMeasure P ∧
      (∀ (I : Finset ℝ≥0) (hI : (I : Set ℝ≥0) ⊆ S),
        MeasurePreserving (fun (x : S → ℝ) (i : I) ↦ x ⟨i.1, hI i.2⟩) P
          (BrownianReal.projectiveFamily I)) ∧
      ∀ ⦃n : ℕ⦄, n ≠ 0 →
        IsKolmogorovProcess (fun (t : S) (x : S → ℝ) ↦ x t) P (2 * n : ℕ) n (2 * n - 1)‼ := by
  obtain ⟨P, hprob, hP⟩ := S.exists_measurePreserving_finset_of_countable (X := fun _ ↦ ℝ)
    BrownianReal.projectiveFamily BrownianReal.isProjectiveMeasureFamily_projectiveFamily
  refine ⟨P, hprob, hP, fun _ hn ↦ isKolmogorovProcess_of_hasLaw_sub_gaussianReal
    (fun t ↦ measurable_pi_apply t) ?_ hn⟩
  exact hasLaw_sub_gaussianReal_of_hasLaw_brownianRealProjectiveFamily
    (fun I hI ↦ (hP I hI).hasLaw)

end TauCeti
