/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.Basic
public import Mathlib.Analysis.Complex.Trigonometric

/-!
# Coordinatewise activation layers

`activation σ` is a realization map with singleton parameter space: it applies the fixed
scalar function `σ` to every coordinate. Thus activations can be used with the same
realized-function and fibre interface as layers with trainable parameters. The coordinate
type is arbitrary, including empty types; finite coordinate types give the usual layers.
The reindexing law includes compatibility with every permutation of neurons.

`powerActivation`, `reluActivation`, and `tanhActivation` instantiate the construction.
The power exponent may be zero, in which case every output coordinate is one.
No polynomiality is claimed for the real ReLU or hyperbolic tangent layers.

The coordinatewise convention follows Marchetti–Shahverdi–Mereta–Trager–Kohn,
*Algebra Unveils Deep Learning — An Invitation to Neuroalgebraic Geometry*,
[arXiv:2501.18915v2](https://arxiv.org/abs/2501.18915v2), §3, equation (2).
The power specialization is that of Finkel–Rodriguez–Wu–Yahl,
*Activation degree thresholds and expressiveness of polynomial neural networks*,
[arXiv:2408.04569v4](https://arxiv.org/abs/2408.04569v4), Definition 1.
The construction uses Mathlib's `Pi.map`, rather than a separate coordinate-map API.
-/

public section

namespace TauCeti.Neuromanifold

variable {ι κ K K' : Type*}

/-- A fixed coordinatewise scalar map, regarded as a model with no trainable parameters. -/
def activation (σ : K → K') : PUnit → (ι → K) → (ι → K') :=
  fun _ => Pi.map fun _ => σ

/-- An activation layer is the constant model supplied by Mathlib's coordinate map. -/
theorem activation_def (σ : K → K') :
    activation (ι := ι) σ = fun _ => Pi.map (fun _ => σ) := (rfl)

/-- Evaluation applies the scalar activation in the selected coordinate. -/
@[simp] theorem activation_apply (σ : K → K') (p : PUnit) (x : ι → K) (i : ι) :
    activation σ p x i = σ (x i) := (rfl)

/-- The identity activation gives the parameter-free identity model. -/
@[simp] theorem activation_id : activation (ι := ι) (@id K) = fun _ => id := (rfl)

/-- Activation commutes with coordinate reindexing, in particular with permutations.
For a permutation, take `a` to be the underlying function of an equivalence. -/
theorem activation_reindex (σ : K → K') (a : κ → ι) (p : PUnit) (x : ι → K) :
    activation σ p (x ∘ a) = activation σ p x ∘ a := (rfl)

/-- A fixed activation realizes exactly its coordinatewise scalar map. -/
@[simp] theorem realizedFunctions_activation (σ : K → K') :
    realizedFunctions (activation (ι := ι) σ) = {Pi.map fun _ => σ} := by
  rw [realizedFunctions_def, Set.range_unique, activation_def]

/-- The coordinatewise power layer, including exponent zero. -/
def powerActivation [Pow K ℕ] (r : ℕ) : PUnit → (ι → K) → (ι → K) :=
  activation fun t => t ^ r

/-- The power layer is the activation associated to the scalar power function. -/
theorem powerActivation_def [Pow K ℕ] (r : ℕ) :
    powerActivation (ι := ι) (K := K) r = activation (fun t => t ^ r) := (rfl)

/-- Each coordinate of a power layer is the corresponding scalar power. -/
@[simp] theorem powerActivation_apply [Pow K ℕ] (r : ℕ) (p : PUnit)
    (x : ι → K) (i : ι) : powerActivation r p x i = x i ^ r := (rfl)

/-- Exponent zero gives the constant-one output, even at zero input coordinates. -/
@[simp] theorem powerActivation_zero [Monoid K] :
    powerActivation (ι := ι) (K := K) 0 = fun _ _ _ => 1 := by
  funext p x i
  simp

/-- Exponent one gives the parameter-free identity model. -/
@[simp] theorem powerActivation_one [Monoid K] :
    powerActivation (ι := ι) (K := K) 1 = fun _ => id := by
  funext p x i
  simp

/-- ReLU as a fixed real coordinatewise layer. -/
def reluActivation : PUnit → (ι → ℝ) → (ι → ℝ) :=
  activation fun t => max 0 t

/-- ReLU is the activation associated to the scalar function `t ↦ max 0 t`. -/
theorem reluActivation_def :
    reluActivation (ι := ι) = activation (fun t : ℝ => max 0 t) := (rfl)

/-- Each coordinate of ReLU is the maximum of zero and the input coordinate. -/
@[simp] theorem reluActivation_apply (p : PUnit) (x : ι → ℝ) (i : ι) :
    reluActivation p x i = max 0 (x i) := (rfl)

/-- Hyperbolic tangent as a fixed real coordinatewise layer. -/
noncomputable def tanhActivation : PUnit → (ι → ℝ) → (ι → ℝ) := activation Real.tanh

/-- The hyperbolic tangent layer is the activation associated to `Real.tanh`. -/
theorem tanhActivation_def :
    tanhActivation (ι := ι) = activation Real.tanh := (rfl)

/-- Each coordinate of the hyperbolic tangent layer is the scalar hyperbolic tangent. -/
@[simp] theorem tanhActivation_apply (p : PUnit) (x : ι → ℝ) (i : ι) :
    tanhActivation p x i = Real.tanh (x i) := (rfl)

end TauCeti.Neuromanifold
