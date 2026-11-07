/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.Probability.IdentDistrib
public import TauCeti.Probability.Distributions.Poisson.Basic

import TauCeti.Probability.Independence.Basic

/-!
# Poisson random measures

A Poisson random measure is a measurable measure-valued map whose counts on finite families of
disjoint measurable sets of finite intensity are independent Poisson variables, and whose counts
on measurable sets of infinite intensity are almost surely infinite. The sample space and its
probability measure remain explicit, and the state space needs only a measurable structure.
In particular, atomic intensities and multiple occurrences at one location are permitted.

This file provides the defining count API, transfer through equality in distribution, and
preservation by measurable mapping and restriction. These operations are the elementary ingredients
of thinning and displacement constructions.

The definition and the mapping and restriction results follow Chapters 3 and 5 of G. Last and
M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press, 2018.
-/

public section

open Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω Ω' X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  [MeasurableSpace X] [MeasurableSpace Y]
  {P : Measure Ω} {P' : Measure Ω'}
  {N : Ω → Measure X} {N' : Ω' → Measure X} {Λ : Measure X}

/-- A measurable random measure with independent Poisson counts on disjoint measurable sets of
finite intensity and almost surely infinite counts on measurable sets of infinite intensity.
No topology or simplicity assumption is imposed. -/
def IsPoissonRandomMeasure (P : Measure Ω) (N : Ω → Measure X) (Λ : Measure X) : Prop :=
  Measurable N ∧
    (∀ (n : ℕ) (A : Fin n → Set X), (∀ i, MeasurableSet (A i) ∧ Λ (A i) < ∞) →
      Pairwise (Disjoint on A) →
        iIndepFun (fun i ω => N ω (A i)) P ∧
          ∀ i, HasLaw (fun ω => N ω (A i))
            ((poissonMeasure (Λ (A i)).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞)) P)
    ∧ ∀ A, MeasurableSet A → Λ A = ∞ → ∀ᵐ ω ∂P, N ω A = ∞

/-- The defining independent-count criterion, usable without unfolding the predicate. -/
theorem isPoissonRandomMeasure_iff :
    IsPoissonRandomMeasure P N Λ ↔
      Measurable N ∧
        (∀ (n : ℕ) (A : Fin n → Set X), (∀ i, MeasurableSet (A i) ∧ Λ (A i) < ∞) →
          Pairwise (Disjoint on A) →
            iIndepFun (fun i ω => N ω (A i)) P ∧
              ∀ i, HasLaw (fun ω => N ω (A i))
                ((poissonMeasure (Λ (A i)).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞)) P)
        ∧ ∀ A, MeasurableSet A → Λ A = ∞ → ∀ᵐ ω ∂P, N ω A = ∞ :=
  (Iff.rfl)

/-- A Poisson random measure is measurable for the evaluation measurable structure. -/
@[fun_prop]
theorem IsPoissonRandomMeasure.measurable (h : IsPoissonRandomMeasure P N Λ) : Measurable N :=
  (isPoissonRandomMeasure_iff.mp h).1

/-- Counts on a finite disjoint measurable family of finite intensity are independent. -/
theorem IsPoissonRandomMeasure.iIndepFun (h : IsPoissonRandomMeasure P N Λ)
    {n : ℕ} {A : Fin n → Set X} (hA : ∀ i, MeasurableSet (A i))
    (hfin : ∀ i, Λ (A i) < ∞) (hdisj : Pairwise (Disjoint on A)) :
    iIndepFun (fun i ω => N ω (A i)) P :=
  ((isPoissonRandomMeasure_iff.mp h).2.1 n A (fun i => ⟨hA i, hfin i⟩) hdisj).1

/-- A count on a measurable set of finite intensity has the corresponding Poisson law. -/
theorem IsPoissonRandomMeasure.hasLaw (h : IsPoissonRandomMeasure P N Λ)
    {A : Set X} (hA : MeasurableSet A) (hfin : Λ A < ∞) :
    HasLaw (fun ω => N ω A)
      ((poissonMeasure (Λ A).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞)) P := by
  exact ((isPoissonRandomMeasure_iff.mp h).2.1 1 (fun _ => A) (fun _ => ⟨hA, hfin⟩)
    (fun i j hij => False.elim (hij (Subsingleton.elim i j)))).2 0

/-- A count on a measurable set of infinite intensity is almost surely infinite. -/
theorem IsPoissonRandomMeasure.ae_eq_top (h : IsPoissonRandomMeasure P N Λ)
    {A : Set X} (hA : MeasurableSet A) (hΛ : Λ A = ∞) :
    ∀ᵐ ω ∂P, N ω A = ∞ :=
  (isPoissonRandomMeasure_iff.mp h).2.2 A hA hΛ

/-- The independent-count criterion forces the sample measure to be a probability measure. -/
theorem IsPoissonRandomMeasure.isProbabilityMeasure (h : IsPoissonRandomMeasure P N Λ) :
    IsProbabilityMeasure P :=
  (h.iIndepFun (n := 0) (A := fun _ => ∅) (fun _ => .empty)
    (by simp) (by simp)).isProbabilityMeasure

/-- The Poisson property depends only on the law of a measurable random measure. -/
theorem IsPoissonRandomMeasure.of_identDistrib (h : IsPoissonRandomMeasure P N Λ)
    (hN' : Measurable N') (hLaw : IdentDistrib N N' P P') :
    IsPoissonRandomMeasure P' N' Λ := by
  let := h.isProbabilityMeasure
  let : IsProbabilityMeasure P' :=
    (hLaw.hasLaw (hasLaw_map h.measurable.aemeasurable)).isProbabilityMeasure
  refine isPoissonRandomMeasure_iff.mpr ⟨hN', ?_, ?_⟩
  · intro n A hA hd
    have hcounts := (isPoissonRandomMeasure_iff.mp h).2.1 n A hA hd
    have hvec := hLaw.comp (measurable_pi_iff.mpr fun i => Measure.measurable_coe (hA i).1)
    have hpi := hvec.hasLaw (iIndepFun.hasLaw_pi hcounts.2 hcounts.1)
    have hlaw : ∀ i, HasLaw (fun ω => N' ω (A i))
        ((poissonMeasure (Λ (A i)).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞)) P' :=
      fun i => (hLaw.comp (Measure.measurable_coe (hA i).1)).hasLaw (hcounts.2 i)
    exact ⟨(iIndepFun_iff_hasLaw_pi_pi hlaw).mpr hpi, hlaw⟩
  · intro A hA hΛ
    exact (hLaw.comp (Measure.measurable_coe hA)).ae_snd
      (measurableSet_singleton ∞) (h.ae_eq_top hA hΛ)

/-- Changing a measurable random measure on a null set preserves its Poisson property. -/
theorem IsPoissonRandomMeasure.congr (h : IsPoissonRandomMeasure P N Λ)
    {M : Ω → Measure X} (hM : Measurable M) (hNM : N =ᵐ[P] M) :
    IsPoissonRandomMeasure P M Λ :=
  h.of_identDistrib hM (.of_ae_eq h.measurable.aemeasurable hNM)

/-- Measurable maps send Poisson random measures to Poisson random measures with pushed-forward
intensity. No finiteness assumption on the preimages beyond the tested count sets is needed. -/
theorem IsPoissonRandomMeasure.map (h : IsPoissonRandomMeasure P N Λ)
    {f : X → Y} (hf : Measurable f) :
    IsPoissonRandomMeasure P (fun ω => (N ω).map f) (Λ.map f) := by
  refine isPoissonRandomMeasure_iff.mpr
    ⟨(Measure.measurable_map f hf).comp h.measurable, ?_, ?_⟩
  · intro n A hA hd
    have hc := (isPoissonRandomMeasure_iff.mp h).2.1 n (fun i => f ⁻¹' A i)
      (fun i => ⟨hf (hA i).1, by simpa [Measure.map_apply hf (hA i).1] using (hA i).2⟩)
      (fun i j hij => (hd hij).preimage f)
    simpa only [Measure.map_apply hf, (hA _).1] using hc
  · intro A hA hΛ
    have hc := h.ae_eq_top (hf hA) (by simpa [Measure.map_apply hf hA] using hΛ)
    simpa only [Measure.map_apply hf hA] using hc

/-- Restricting a Poisson random measure to a measurable set restricts its intensity. -/
theorem IsPoissonRandomMeasure.restrict (h : IsPoissonRandomMeasure P N Λ)
    {s : Set X} (hs : MeasurableSet s) :
    IsPoissonRandomMeasure P (fun ω => (N ω).restrict s) (Λ.restrict s) := by
  have hm : Measurable fun ω => (N ω).restrict s := by
    refine Measure.measurable_measure.mpr fun A hA => ?_
    simpa only [Measure.restrict_apply hA, Function.comp_def] using
      (Measure.measurable_coe (hA.inter hs)).comp h.measurable
  refine isPoissonRandomMeasure_iff.mpr ⟨hm, ?_, ?_⟩
  · intro n A hA hd
    have hc := (isPoissonRandomMeasure_iff.mp h).2.1 n (fun i => A i ∩ s)
      (fun i => ⟨(hA i).1.inter hs, by simpa [Measure.restrict_apply (hA i).1] using (hA i).2⟩)
      (fun i j hij => (hd hij).mono Set.inter_subset_left Set.inter_subset_left)
    simpa only [Measure.restrict_apply, (hA _).1] using hc
  · intro A hA hΛ
    have hc := h.ae_eq_top (hA.inter hs)
      (by simpa [Measure.restrict_apply hA] using hΛ)
    simpa only [Measure.restrict_apply hA] using hc

/-- A Poisson number of occurrences placed at a fixed location is a Poisson random measure.
This permits arbitrary measurable state spaces, positive atomic intensities, and multiplicities. -/
theorem isPoissonRandomMeasure_smul_dirac (r : ℝ≥0) (x : X) :
    IsPoissonRandomMeasure (poissonMeasure r)
      (fun k : ℕ => (k : ℝ≥0∞) • Measure.dirac x) ((r : ℝ≥0∞) • Measure.dirac x) := by
  classical
  refine isPoissonRandomMeasure_iff.mpr ⟨Measurable.of_discrete, ?_, ?_⟩
  swap
  · intro A hA hΛ
    let : IsFiniteMeasure ((r : ℝ≥0∞) • Measure.dirac x) :=
      (Measure.dirac x).smul_finite ENNReal.coe_ne_top
    exact False.elim (measure_ne_top _ A hΛ)
  intro n A hA hd
  have heval (i : Fin n) (k : ℕ) :
      ((k : ℝ≥0∞) • Measure.dirac x) (A i) = if x ∈ A i then (k : ℝ≥0∞) else 0 := by
    by_cases hx : x ∈ A i <;> simp [Measure.dirac_apply' _ (hA i).1, hx]
  have hrate (i : Fin n) :
      (((r : ℝ≥0∞) • Measure.dirac x) (A i)).toNNReal = if x ∈ A i then r else 0 := by
    by_cases hx : x ∈ A i <;> simp [Measure.dirac_apply' _ (hA i).1, hx]
  constructor
  · apply iIndepFun_of_ae_eq_const_outside_subsingleton (s := {i | x ∈ A i})
    · intro i hi j hj
      by_contra hij
      exact Set.disjoint_left.mp (hd hij) hi hj
    · intro i hi
      simp only [Set.mem_ofPred_eq] at hi
      exact ⟨0, Filter.Eventually.of_forall fun k => by simp [heval, hi]⟩
  · intro i
    by_cases hx : x ∈ A i
    · simpa only [heval, hrate, hx, ↓reduceIte] using
        (hasLaw_map (P := poissonMeasure r) (X := (Nat.cast : ℕ → ℝ≥0∞))
          Measurable.of_discrete.aemeasurable)
    · simpa only [heval, hrate, hx, ↓reduceIte, poissonMeasure_zero,
        Measure.map_dirac, Nat.cast_zero] using
        (hasLaw_dirac_of_ae_eq (P := poissonMeasure r)
          (X := fun _ : ℕ => (0 : ℝ≥0∞)) Filter.EventuallyEq.rfl)

end TauCeti.Probability
