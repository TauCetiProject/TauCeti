/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Hidden Markov models and their joint densities

A hidden Markov model `M : HMM S Y` has hidden states in a type `S` and observations in a
measurable space `Y`. It consists of an initial law `M.init : PMF S`, a transition law
`M.trans s : PMF S` for each state, a reference measure `M.ref` on `Y`, and for each state `s`
the density `M.dens s : Y → ℝ≥0` of its emission law with respect to `M.ref`.

The **joint density** `M.jointDensity x y n` of a state path `x : ℕ → S` and an observation
sequence `y : ℕ → Y` up to time `n` is
`init (x 0) * dens (x 0) (y 0) * ∏ t < n, trans (x t) (x (t + 1)) * dens (x (t + 1)) (y (t + 1))`:
the observation at each time is weighted by the state at that same time. It only depends on the
states `x 0, …, x n` (`jointDensity_congr`). Summed over these finitely many states, that is over
the state sequences `Fin (n + 1) → S`, it gives the likelihood of the observations up to time `n`;
its maximum over the same state sequences is the value of a most probable state sequence.

## Main definitions

* `TauCeti.HMM`: hidden Markov models with emission densities.
* `TauCeti.HMM.ofPMF`: the model with a discrete observation space, counting measure as reference
  measure and emission laws given by probability mass functions.
* `TauCeti.HMM.ofMeasure`: the model whose emission laws are given probability measures dominated
  by a σ-finite reference measure, with their Radon–Nikodym derivatives as densities.
* `TauCeti.HMM.jointDensity`: the joint density of a state path and an observation sequence.

## Main statements

* `TauCeti.HMM.jointDensity_succ`: the joint density at horizon `n + 1` is the joint density at
  horizon `n` times one transition probability and one emission density.
* `TauCeti.HMM.jointDensity_congr`: the joint density up to time `n` only depends on the states and
  observations at times `≤ n`.
* `TauCeti.HMM.measurable_jointDensity_clamp`: the joint density is a measurable function of the
  finite observation record.
* `TauCeti.HMM.withDensity_ofMeasure_dens`: every family of emission laws dominated by a σ-finite
  measure is the family of emission laws of a model.

## References

* L. R. Rabiner, *A tutorial on hidden Markov models and selected applications in speech
  recognition*, Proc. IEEE **77** (1989), equations (12)–(15).
* R. van Handel, *Hidden Markov models*, lecture notes, Princeton University (2008),
  Definitions 1.6 and 1.9.
-/

public section

noncomputable section

open MeasureTheory Finset
open scoped ENNReal NNReal

namespace TauCeti

/-- A hidden Markov model with hidden states in `S` and observations in the measurable space `Y`:
an initial law and a transition law on the states, and for each state an emission law on `Y`,
given by its density with respect to a common reference measure. -/
@[ext]
structure HMM (S Y : Type*) [MeasurableSpace Y] where
  /-- The law of the state at time `0`. -/
  init : PMF S
  /-- The law of the next state, from each state. -/
  trans : S → PMF S
  /-- The reference measure on the observations. -/
  ref : Measure Y
  /-- The density with respect to `ref` of the law of the observation emitted in each state. -/
  dens : S → Y → ℝ≥0
  /-- Each emission density is measurable. -/
  measurable_dens : ∀ s, Measurable (dens s)
  /-- Each emission density integrates to `1`, so that it is the density of a probability
  measure. -/
  lintegral_dens : ∀ s, ∫⁻ y, (dens s y : ℝ≥0∞) ∂ref = 1

namespace HMM

attribute [fun_prop] measurable_dens

variable {S Y : Type*} [MeasurableSpace Y]

/-! ### Discrete observations -/

section OfPMF

variable [DiscreteMeasurableSpace Y]

/-- The hidden Markov model with initial law `init`, transition laws `trans` and emission mass
functions `emit` on a discrete observation space; its reference measure is counting measure and
its emission densities are the mass functions. -/
def ofPMF (init : PMF S) (trans : S → PMF S) (emit : S → PMF Y) : HMM S Y where
  init := init
  trans := trans
  ref := Measure.count
  dens s y := (emit s y).toNNReal
  measurable_dens _ := .of_discrete
  lintegral_dens s := by
    simp [lintegral_count, ENNReal.coe_toNNReal, PMF.apply_ne_top]

variable (init : PMF S) (trans : S → PMF S) (emit : S → PMF Y)

@[simp]
theorem ofPMF_init : (ofPMF init trans emit).init = init := (rfl)

@[simp]
theorem ofPMF_trans : (ofPMF init trans emit).trans = trans := (rfl)

@[simp]
theorem ofPMF_ref : (ofPMF init trans emit).ref = Measure.count := (rfl)

/-- The emission density of `ofPMF init trans emit` in the state `s` at `y` is the mass
`emit s y`, truncated to `ℝ≥0`. -/
theorem ofPMF_dens (s : S) (y : Y) : (ofPMF init trans emit).dens s y = (emit s y).toNNReal :=
  (rfl)

/-- The emission densities of `ofPMF init trans emit` are the emission mass functions. -/
@[simp]
theorem coe_ofPMF_dens (s : S) (y : Y) : ((ofPMF init trans emit).dens s y : ℝ≥0∞) = emit s y :=
  ENNReal.coe_toNNReal (PMF.apply_ne_top _ _)

/-- The emission law of `ofPMF init trans emit` in the state `s` is the measure of `emit s`. -/
theorem withDensity_ofPMF_dens (s : S) :
    (ofPMF init trans emit).ref.withDensity (fun y ↦ ((ofPMF init trans emit).dens s y : ℝ≥0∞)) =
      (emit s).toMeasure := by
  ext t ht
  rw [withDensity_apply _ ht, PMF.toMeasure_apply _ ht, ← lintegral_indicator ht, ofPMF_ref,
    lintegral_count]
  simp

end OfPMF

/-! ### Emission laws dominated by a σ-finite measure -/

section OfMeasure

variable (init : PMF S) (trans : S → PMF S) (ref : Measure Y) [SigmaFinite ref]
  (emit : S → Measure Y) [∀ s, IsProbabilityMeasure (emit s)] (hemit : ∀ s, emit s ≪ ref)

/-- The hidden Markov model with initial law `init`, transition laws `trans`, reference measure
`ref` and emission laws `emit`, each absolutely continuous with respect to `ref`. Its emission
densities are the Radon–Nikodym derivatives `(emit s).rnDeriv ref`, which are finite almost
everywhere, truncated to `ℝ≥0`. -/
def ofMeasure : HMM S Y where
  init := init
  trans := trans
  ref := ref
  dens s y := ((emit s).rnDeriv ref y).toNNReal
  measurable_dens s := (Measure.measurable_rnDeriv _ _).ennreal_toNNReal
  lintegral_dens s := by
    rw [lintegral_congr_ae ((Measure.rnDeriv_ne_top (emit s) ref).mono fun _ h ↦
        ENNReal.coe_toNNReal h), Measure.lintegral_rnDeriv (hemit s), measure_univ]

@[simp]
theorem ofMeasure_init : (ofMeasure init trans ref emit hemit).init = init := (rfl)

@[simp]
theorem ofMeasure_trans : (ofMeasure init trans ref emit hemit).trans = trans := (rfl)

@[simp]
theorem ofMeasure_ref : (ofMeasure init trans ref emit hemit).ref = ref := (rfl)

/-- The emission density of `ofMeasure init trans ref emit hemit` in the state `s` at `y` is the
Radon–Nikodym derivative `(emit s).rnDeriv ref y`, truncated to `ℝ≥0`. -/
theorem ofMeasure_dens (s : S) (y : Y) :
    (ofMeasure init trans ref emit hemit).dens s y = ((emit s).rnDeriv ref y).toNNReal :=
  (rfl)

/-- The emission densities of `ofMeasure init trans ref emit hemit` are the Radon–Nikodym
derivatives of the emission laws, almost everywhere with respect to the reference measure. -/
theorem coe_ofMeasure_dens_ae_eq (s : S) :
    (fun y ↦ ((ofMeasure init trans ref emit hemit).dens s y : ℝ≥0∞)) =ᵐ[ref]
      (emit s).rnDeriv ref :=
  (Measure.rnDeriv_ne_top (emit s) ref).mono fun _ h ↦ ENNReal.coe_toNNReal h

/-- Every family of probability measures dominated by a σ-finite measure `ref` is the family of
emission laws of a hidden Markov model with reference measure `ref`: the emission law in the state
`s` of `ofMeasure init trans ref emit hemit` is `emit s`. -/
theorem withDensity_ofMeasure_dens (s : S) :
    ref.withDensity (fun y ↦ ((ofMeasure init trans ref emit hemit).dens s y : ℝ≥0∞)) =
      emit s := by
  rw [withDensity_congr_ae (coe_ofMeasure_dens_ae_eq init trans ref emit hemit s),
    Measure.withDensity_rnDeriv_eq _ _ (hemit s)]

end OfMeasure

/-! ### The joint density -/

variable (M : HMM S Y)

/-- The joint density of the state path `x` and the observation sequence `y` up to time `n`:
`init (x 0) * dens (x 0) (y 0) * ∏ t < n, trans (x t) (x (t + 1)) * dens (x (t + 1)) (y (t + 1))`.
It only depends on `x` and `y` at times `≤ n` (`jointDensity_congr`). -/
def jointDensity (x : ℕ → S) (y : ℕ → Y) (n : ℕ) : ℝ≥0∞ :=
  M.init (x 0) * M.dens (x 0) (y 0) *
    ∏ t ∈ range n, (M.trans (x t) (x (t + 1)) * M.dens (x (t + 1)) (y (t + 1)))

/-- The defining formula of the joint density as a product over the time steps `t < n`. -/
theorem jointDensity_def (x : ℕ → S) (y : ℕ → Y) (n : ℕ) :
    M.jointDensity x y n = M.init (x 0) * M.dens (x 0) (y 0) *
      ∏ t ∈ range n, (M.trans (x t) (x (t + 1)) * M.dens (x (t + 1)) (y (t + 1))) :=
  (rfl)

/-- The joint density at horizon `0` weighs the observation at time `0` by the state at
time `0`. -/
@[simp]
theorem jointDensity_zero (x : ℕ → S) (y : ℕ → Y) :
    M.jointDensity x y 0 = M.init (x 0) * M.dens (x 0) (y 0) := by
  simp [jointDensity]

/-- One more time step multiplies the joint density by the transition probability into the new
state and the density of the new observation in the new state. -/
@[simp]
theorem jointDensity_succ (x : ℕ → S) (y : ℕ → Y) (n : ℕ) :
    M.jointDensity x y (n + 1) =
      M.jointDensity x y n * M.trans (x n) (x (n + 1)) * M.dens (x (n + 1)) (y (n + 1)) := by
  simp only [jointDensity, prod_range_succ, mul_assoc]

/-- The joint density up to time `n` only depends on the states and observations at times
`≤ n`. -/
theorem jointDensity_congr {x x' : ℕ → S} {y y' : ℕ → Y} {n : ℕ} (hx : ∀ t ≤ n, x t = x' t)
    (hy : ∀ t ≤ n, y t = y' t) : M.jointDensity x y n = M.jointDensity x' y' n := by
  induction n with
  | zero => simp [hx 0 le_rfl, hy 0 le_rfl]
  | succ n ih =>
    rw [jointDensity_succ, jointDensity_succ,
      ih (fun t ht ↦ hx t (by omega)) (fun t ht ↦ hy t (by omega)),
      hx n (by omega), hx (n + 1) le_rfl, hy (n + 1) le_rfl]

/-- The joint density is finite. -/
@[simp, aesop (rule_sets := [finiteness]) safe apply]
theorem jointDensity_ne_top (x : ℕ → S) (y : ℕ → Y) (n : ℕ) : M.jointDensity x y n ≠ ∞ := by
  induction n with
  | zero => simp [ENNReal.mul_eq_top, PMF.apply_ne_top]
  | succ n ih => simp [ENNReal.mul_eq_top, PMF.apply_ne_top, ih]

/-- The joint density is finite. -/
theorem jointDensity_lt_top (x : ℕ → S) (y : ℕ → Y) (n : ℕ) : M.jointDensity x y n < ∞ :=
  (M.jointDensity_ne_top x y n).lt_top

/-- For a fixed state path and horizon, the joint density is a measurable function of the
observation sequence. -/
@[fun_prop]
theorem measurable_jointDensity (x : ℕ → S) (n : ℕ) :
    Measurable fun y : ℕ → Y ↦ M.jointDensity x y n := by
  simp only [jointDensity_def]
  fun_prop

/-- For a fixed state path and horizon `n`, the joint density is a measurable function of the
observation record `w : Fin (n + 1) → Y`, read as the sequence `fun i ↦ w (Fin.clamp i n)`. -/
theorem measurable_jointDensity_clamp (x : ℕ → S) (n : ℕ) :
    Measurable fun w : Fin (n + 1) → Y ↦ M.jointDensity x (fun i ↦ w (Fin.clamp i n)) n := by
  fun_prop

end HMM

end TauCeti
