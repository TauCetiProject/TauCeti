/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Poisson.Basic
public import Mathlib.Topology.Algebra.Monoid.FunOnFinite
import Mathlib.Probability.ProductMeasure

/-!
# Finite sums of independent Poisson variables

The sum of independent Poisson counts is Poisson with rate equal to the sum of their rates.
The native natural-number law is given both for random variables and as a product-measure
pushforward. Empty families and zero rates are included, as needed when conditioning on a
Poisson total or allocating a total among categories.

Aggregation over the fibres of a finite category map preserves independence and adds rates
over those fibres, including empty fibres. This also permits aggregation inside Poisson
mixtures, such as the negative-multinomial family.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TauCeti.Probability

variable {ι : Type*}

/-- The sum of a finite independent family of Poisson variables is Poisson with rate equal
to the sum of the rates. Only the variables indexed by `s` need carry a Poisson law.
Empty families and zero rates are included. -/
theorem _root_.ProbabilityTheory.iIndepFun.hasLaw_sum_poissonMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ι → Ω → ℕ} {r : ι → ℝ≥0}
    {s : Finset ι} (hindep : iIndepFun X P)
    (hlaw : ∀ i ∈ s, HasLaw (X i) (poissonMeasure (r i)) P) :
    HasLaw (fun ω => ∑ i ∈ s, X i ω) (poissonMeasure (∑ i ∈ s, r i)) P := by
  classical
  let _ := hindep.isProbabilityMeasure
  have hmeas : AEMeasurable (fun ω => ∑ i ∈ s, X i ω) P :=
    Finset.aemeasurable_fun_sum _ fun i hi => (hlaw i hi).aemeasurable
  refine ⟨hmeas, measure_eq_of_pgf_eqOn fun z hz => ?_⟩
  rw [pgf_map hmeas]
  have hsum := iIndepFun.pgf_sum_of_abs_le_one hindep s
    (fun i hi => (hlaw i hi).aemeasurable) (abs_le.mpr ⟨hz.1.le, hz.2.le⟩)
  have hfun : (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, X i := by
    funext ω
    exact (Finset.sum_apply ω s X).symm
  rw [hfun, hsum]
  rw [Finset.prod_congr rfl (fun i hi => HasLaw.pgf_eq (hlaw i hi) z)]
  simp_rw [pgf_poissonMeasure]
  rw [← Real.exp_sum, ← Finset.sum_mul, NNReal.coe_sum]

/-- The sum pushforward of independent Poisson laws has rate equal to the sum of their rates. -/
@[simp]
theorem map_sum_pi_poissonMeasure [Fintype ι] (r : ι → ℝ≥0) :
    (Measure.pi (fun i => poissonMeasure (r i))).map (fun k => ∑ i, k i) =
      poissonMeasure (∑ i, r i) := by
  have hindep : iIndepFun (fun i (k : ι → ℕ) => k i)
      (Measure.pi (fun i => poissonMeasure (r i))) :=
    iIndepFun_pi (X := fun _ => (id : ℕ → ℕ)) fun _ => aemeasurable_id
  exact (hindep.hasLaw_sum_poissonMeasure (s := Finset.univ)
    (fun i _ => (measurePreserving_eval (fun i => poissonMeasure (r i)) i).hasLaw)).map_eq

/-- Summing independent Poisson counts over the fibres of any finite category map preserves
independence and adds the rates over the same fibres. Empty fibres give zero-rate counts. -/
@[simp]
theorem map_funOnFinite_map_pi_poissonMeasure {κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (f : ι → κ) (r : ι → ℝ≥0) :
    (Measure.pi fun i ↦ poissonMeasure (r i)).map (FunOnFinite.map (M := ℕ) f) =
      Measure.pi fun j ↦ poissonMeasure (∑ i with f i = j, r i) := by
  classical
  -- Read the coordinates of the product along the fibre decomposition of `ι`.
  have h₁ : MeasurePreserving
      (fun (x : ι → ℕ) (p : (j : κ) × {i // f i = j}) ↦ x p.2)
      (Measure.pi fun i ↦ poissonMeasure (r i))
      (Measure.pi fun p : (j : κ) × {i // f i = j} ↦ poissonMeasure (r p.2)) := by
    have h := (measurePreserving_piCongrLeft (fun i : ι ↦ poissonMeasure (r i))
      (Equiv.sigmaFiberEquiv f)).symm
      (MeasurableEquiv.piCongrLeft (fun _ : ι ↦ ℕ) (Equiv.sigmaFiberEquiv f))
    have hfun : ⇑(MeasurableEquiv.piCongrLeft (fun _ : ι ↦ ℕ) (Equiv.sigmaFiberEquiv f)).symm =
        fun (x : ι → ℕ) (p : (j : κ) × {i // f i = j}) ↦ x p.2 := by
      funext x p
      simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_symm_apply, Equiv.sigmaFiberEquiv]
    rw [hfun] at h
    exact h
  -- Group those coordinates by fibre.
  have h₂ : MeasurePreserving
      (Sigma.curry (γ := fun (j : κ) (_ : {i // f i = j}) ↦ ℕ))
      (Measure.pi fun p : (j : κ) × {i // f i = j} ↦ poissonMeasure (r p.2))
      (Measure.pi fun j ↦ Measure.pi fun i : {i // f i = j} ↦ poissonMeasure (r i)) := by
    refine ⟨(MeasurableEquiv.piCurry fun (j : κ) (_ : {i // f i = j}) ↦ ℕ).measurable, ?_⟩
    have h := Measure.infinitePi_map_piCurry
      (X := fun (j : κ) (_ : {i // f i = j}) ↦ ℕ)
      (μ := fun (j : κ) (i : {i // f i = j}) ↦ poissonMeasure (r i))
    simpa only [Measure.infinitePi_eq_pi, MeasurableEquiv.coe_piCurry] using h
  -- Add up the coordinates inside each fibre.
  have hfactor (j : κ) : MeasurePreserving (fun y : {i // f i = j} → ℕ ↦ ∑ i, y i)
      (Measure.pi fun i : {i // f i = j} ↦ poissonMeasure (r i))
      (poissonMeasure (∑ i with f i = j, r i)) := by
    refine ⟨by fun_prop, ?_⟩
    rw [map_sum_pi_poissonMeasure]
    congr 1
    exact (Finset.sum_subtype _ (by simp) r).symm
  have hcomp : ((fun (y : (j : κ) → {i // f i = j} → ℕ) (j : κ) ↦ ∑ i, y j i) ∘
      Sigma.curry) ∘ (fun (x : ι → ℕ) (p : (j : κ) × {i // f i = j}) ↦ x p.2) =
      FunOnFinite.map (M := ℕ) f := by
    funext x j
    simp only [Function.comp_apply, Sigma.curry, FunOnFinite.map_apply_apply]
    exact (Finset.sum_subtype _ (by simp) x).symm
  have hmp := ((measurePreserving_pi _ _ hfactor).comp h₂).comp h₁
  rw [hcomp] at hmp
  exact hmp.map_eq

end TauCeti.Probability
