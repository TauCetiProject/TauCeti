/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Kernel.Composition.CompNotation
public import Mathlib.Probability.ProductMeasure
import TauCeti.Probability.Distributions.Gaussian.Affine
import TauCeti.Probability.Distributions.Gaussian.Moments

/-!
# The Gaussian sequence model

The Gaussian sequence model observes `Y = θ + ε ξ` on `ℕ → ℝ`, where `θ : ℕ → ℝ` is the unknown
parameter, `ε` the noise level and `ξ` a sequence of independent standard Gaussian variables.
Its law `gaussSeqLaw θ ε` is the countable product of the Gaussian laws of mean `θ j` and
variance `ε²`, for every `θ`, without a summability condition. Estimators are Markov kernels, and
the squared-error risk `gaussSeqRisk κ θ ε` is the lower Lebesgue integral of
`∑' j, (y j - θ j)²` in `ℝ≥0∞`, so that an estimate with a nonsummable error has infinite loss.
The minimax risk over a parameter set `Θ` is the infimum over Markov kernels of the supremum over
`Θ` of the risk, and the linear minimax risk is the same infimum over the diagonal estimators
`y ↦ (c j * y j)_j`, written with their risk `∑' j, (c j² ε² + (1 - c j)² θ j²)`. The usual
parameter sets are the ellipsoids `∑' j, a j² θ j² ≤ C²`.

## Main definitions

* `TauCeti.gaussSeqLaw θ ε`: the law of `Y = θ + ε ξ`.
* `TauCeti.ellipsoid a C`: the ellipsoid `∑' j, a j² θ j² ≤ C²`, the sum taken in `ℝ≥0∞`.
* `TauCeti.gaussSeqRisk κ θ ε`: the squared-error risk of a randomized estimator `κ`.
* `TauCeti.gaussSeqMinimax Θ ε`: the minimax risk over `Θ`.
* `TauCeti.gaussSeqLinearMinimax Θ ε`: the minimax risk over `Θ` among diagonal linear
  estimators.

## Main results

* `TauCeti.gaussSeqRisk_diagonal`: the diagonal estimator `y ↦ c ⊙ y` is measurable and its risk
  is `∑' j, (c j² ε² + (1 - c j)² θ j²)`.
* `TauCeti.map_restrict_gaussSeqLaw_eq`: if `θ` and `θ'` agree outside a finite set `S`, the
  coordinates outside `S` have the same law under `gaussSeqLaw θ ε` and `gaussSeqLaw θ' ε`.
* `TauCeti.ellipsoid_mono`: lowering the squared weights and raising the squared radius enlarges
  an ellipsoid.
* `TauCeti.gaussSeqLaw_map_restrict`: the coordinates in any set of indices have the product law.
* `TauCeti.gaussSeqMinimax_le_gaussSeqLinearMinimax`: the minimax risk is at most the linear
  minimax risk.
* `TauCeti.le_gaussSeqMinimax`, `TauCeti.le_gaussSeqLinearMinimax`: lower bounds on the two
  minimax risks from lower bounds on the largest risk of every estimator.

The definitions follow `CKSD.gaussianSequenceLaw`, `CKSD.sequenceEllipsoid`,
`CKSD.gaussianSequenceMinimaxRisk` and `CKSD.gaussianSequenceLinearMinimaxRisk` of lean-CKSD
(`CKSD/Nonparametric/Models.lean`), with three changes: estimators are Markov kernels, the
ellipsoid is bounded by `C²`, and the linear minimax risk is written with the closed-form risk
`∑' j, (c j² ε² + (1 - c j)² θ j²)` of the diagonal estimators.

## References

* I. M. Johnstone, *Gaussian Estimation: Sequence and Wavelet Models*, draft, 2019.
* A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer, 2009, Section 3.1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti

/-! ### The law of the observation -/

/-- The law of the observation `Y = θ + ε ξ` of the Gaussian sequence model on `ℕ → ℝ`: the
product of the Gaussian laws of mean `θ j` and variance `ε²`. -/
def gaussSeqLaw (θ : ℕ → ℝ) (ε : ℝ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun j ↦ gaussianReal (θ j) (ε ^ 2).toNNReal

theorem gaussSeqLaw_def (θ : ℕ → ℝ) (ε : ℝ) :
    gaussSeqLaw θ ε = Measure.infinitePi fun j ↦ gaussianReal (θ j) (ε ^ 2).toNNReal :=
  (rfl)

instance (θ : ℕ → ℝ) (ε : ℝ) : IsProbabilityMeasure (gaussSeqLaw θ ε) := by
  rw [gaussSeqLaw_def]
  infer_instance

/-- Only `ε²` enters the law of the sequence model. -/
@[simp]
theorem gaussSeqLaw_neg (θ : ℕ → ℝ) (ε : ℝ) : gaussSeqLaw θ (-ε) = gaussSeqLaw θ ε := by
  simp [gaussSeqLaw_def]

/-- Without noise the observation is the parameter itself. -/
@[simp]
theorem gaussSeqLaw_zero_right (θ : ℕ → ℝ) : gaussSeqLaw θ 0 = Measure.dirac θ := by
  simp [gaussSeqLaw_def, gaussianReal_zero_var]

/-- The `j`-th coordinate of the observation has the Gaussian law of mean `θ j` and variance
`ε²`. -/
theorem measurePreserving_eval_gaussSeqLaw (θ : ℕ → ℝ) (ε : ℝ) (j : ℕ) :
    MeasurePreserving (Function.eval j) (gaussSeqLaw θ ε)
      (gaussianReal (θ j) (ε ^ 2).toNNReal) := by
  rw [gaussSeqLaw_def]
  exact measurePreserving_eval_infinitePi _ j

/-- The coordinates of the observation with index in a set `{j | p j}` have the product of the
Gaussian laws of mean `θ j` and variance `ε²` over that set. -/
theorem gaussSeqLaw_map_restrict (θ : ℕ → ℝ) (ε : ℝ) (p : ℕ → Prop) :
    (gaussSeqLaw θ ε).map (fun y (j : {j // p j}) ↦ y j) =
      Measure.infinitePi fun j : {j // p j} ↦ gaussianReal (θ j) (ε ^ 2).toNNReal := by
  rw [gaussSeqLaw_def]
  exact Measure.infinitePi_map_restrict' (μ := fun j ↦ gaussianReal (θ j) (ε ^ 2).toNNReal)
    (I := {j | p j})

/-- **Finite-coordinate reduction.** If `θ` and `θ'` agree outside a finite set `S`, the
coordinates outside `S` have the same law under `gaussSeqLaw θ ε` and `gaussSeqLaw θ' ε`. -/
theorem map_restrict_gaussSeqLaw_eq {θ θ' : ℕ → ℝ} (S : Finset ℕ) (h : ∀ j ∉ S, θ j = θ' j)
    (ε : ℝ) :
    (gaussSeqLaw θ ε).map (fun y (j : {j // j ∉ S}) ↦ y j) =
      (gaussSeqLaw θ' ε).map (fun y (j : {j // j ∉ S}) ↦ y j) := by
  simp only [gaussSeqLaw_map_restrict]
  congr with j : 1
  rw [h j j.property]

/-! ### Ellipsoids -/

/-- The ellipsoid `∑' j, a j² θ j² ≤ C²` in `ℕ → ℝ`, the sum taken in `ℝ≥0∞`, so that a
parameter with a nonsummable weighted square is outside every ellipsoid. -/
def ellipsoid (a : ℕ → ℝ) (C : ℝ) : Set (ℕ → ℝ) :=
  {θ | ∑' j, ENNReal.ofReal (a j ^ 2 * θ j ^ 2) ≤ ENNReal.ofReal (C ^ 2)}

@[simp]
theorem mem_ellipsoid {a θ : ℕ → ℝ} {C : ℝ} :
    θ ∈ ellipsoid a C ↔ ∑' j, ENNReal.ofReal (a j ^ 2 * θ j ^ 2) ≤ ENNReal.ofReal (C ^ 2) :=
  Iff.rfl

/-- Only `C²` enters an ellipsoid. -/
@[simp]
theorem ellipsoid_neg_right (a : ℕ → ℝ) (C : ℝ) : ellipsoid a (-C) = ellipsoid a C := by
  ext θ
  simp

/-- Only the squares `a j²` enter an ellipsoid. -/
@[simp]
theorem ellipsoid_neg_left (a : ℕ → ℝ) (C : ℝ) : ellipsoid (-a) C = ellipsoid a C := by
  ext θ
  simp

/-- With zero weights the ellipsoid is the whole space. -/
@[simp]
theorem ellipsoid_zero_left (C : ℝ) : ellipsoid 0 C = univ := by
  ext θ
  simp

/-- **Inclusion of ellipsoids.** Lowering the squared weights and raising the squared radius
enlarges an ellipsoid. -/
theorem ellipsoid_mono {a a' : ℕ → ℝ} {C C' : ℝ} (ha : ∀ j, a' j ^ 2 ≤ a j ^ 2)
    (hC : C ^ 2 ≤ C' ^ 2) : ellipsoid a C ⊆ ellipsoid a' C' := fun θ hθ ↦
  calc ∑' j, ENNReal.ofReal (a' j ^ 2 * θ j ^ 2)
      ≤ ∑' j, ENNReal.ofReal (a j ^ 2 * θ j ^ 2) := tsum_le_tsum fun j ↦
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (ha j) (sq_nonneg _))
    _ ≤ ENNReal.ofReal (C ^ 2) := hθ
    _ ≤ ENNReal.ofReal (C' ^ 2) := ENNReal.ofReal_le_ofReal hC

/-- Lowering the squared weights enlarges an ellipsoid. -/
theorem ellipsoid_mono_left {a a' : ℕ → ℝ} (ha : ∀ j, a' j ^ 2 ≤ a j ^ 2) (C : ℝ) :
    ellipsoid a C ⊆ ellipsoid a' C :=
  ellipsoid_mono ha le_rfl

/-- Raising the squared radius enlarges an ellipsoid. -/
theorem ellipsoid_mono_right (a : ℕ → ℝ) {C C' : ℝ} (hC : C ^ 2 ≤ C' ^ 2) :
    ellipsoid a C ⊆ ellipsoid a C' :=
  ellipsoid_mono (fun _ ↦ le_rfl) hC

/-- The zero parameter lies in every ellipsoid. -/
theorem zero_mem_ellipsoid (a : ℕ → ℝ) (C : ℝ) : (0 : ℕ → ℝ) ∈ ellipsoid a C := by
  simp

/-! ### Risks -/

/-- The squared-error risk `∫⁻ ∑' j, (y j - θ j)²` of a randomized estimator `κ` in the Gaussian
sequence model, a lower Lebesgue integral in `ℝ≥0∞`. -/
def gaussSeqRisk (κ : Kernel (ℕ → ℝ) (ℕ → ℝ)) (θ : ℕ → ℝ) (ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ y, ∑' j, ENNReal.ofReal ((y j - θ j) ^ 2) ∂(κ ∘ₘ gaussSeqLaw θ ε)

theorem gaussSeqRisk_def (κ : Kernel (ℕ → ℝ) (ℕ → ℝ)) (θ : ℕ → ℝ) (ε : ℝ) :
    gaussSeqRisk κ θ ε = ∫⁻ y, ∑' j, ENNReal.ofReal ((y j - θ j) ^ 2) ∂(κ ∘ₘ gaussSeqLaw θ ε) :=
  (rfl)

/-- The risk of a deterministic estimator `T` is the expected squared error of `T Y`. -/
theorem gaussSeqRisk_deterministic {T : (ℕ → ℝ) → ℕ → ℝ} (hT : Measurable T) (θ : ℕ → ℝ)
    (ε : ℝ) :
    gaussSeqRisk (Kernel.deterministic T hT) θ ε =
      ∫⁻ y, ∑' j, ENNReal.ofReal ((T y j - θ j) ^ 2) ∂gaussSeqLaw θ ε := by
  rw [gaussSeqRisk_def, Measure.deterministic_comp_eq_map,
    lintegral_map (Measurable.tsum fun j ↦ by fun_prop) hT]

/-- **Risk of a diagonal estimator.** The diagonal estimator `y ↦ c ⊙ y` is measurable and its
risk is `∑' j, (c j² ε² + (1 - c j)² θ j²)`. -/
theorem gaussSeqRisk_diagonal (c θ : ℕ → ℝ) (ε : ℝ) :
    ∃ hc : Measurable fun y : ℕ → ℝ ↦ fun j ↦ c j * y j,
      gaussSeqRisk (Kernel.deterministic _ hc) θ ε =
        ∑' j, ENNReal.ofReal (c j ^ 2 * ε ^ 2 + (1 - c j) ^ 2 * θ j ^ 2) := by
  refine ⟨by fun_prop, ?_⟩
  have hmeas (j : ℕ) : Measurable fun y : ℕ → ℝ ↦ ENNReal.ofReal ((c j * y j - θ j) ^ 2) := by
    fun_prop
  rw [gaussSeqRisk_deterministic, lintegral_tsum fun j ↦ (hmeas j).aemeasurable]
  refine tsum_congr fun j ↦ ?_
  rw [(measurePreserving_eval_gaussSeqLaw θ ε j).lintegral_comp
    (f := fun x ↦ ENNReal.ofReal ((c j * x - θ j) ^ 2)) (by fun_prop)]
  -- The estimation error `c j * Y j - θ j` is Gaussian with mean `(c j - 1) θ j` and variance
  -- `c j² ε²`; its second moment is the claimed term.
  have hmap : (gaussianReal (θ j) (ε ^ 2).toNNReal).map (fun x ↦ c j * x - θ j) =
      gaussianReal (c j * θ j - θ j) (.mk (c j ^ 2) (sq_nonneg _) * (ε ^ 2).toNNReal) := by
    have h := Probability.gaussianReal_map_const_add_const_mul (θ j) (ε ^ 2).toNNReal (-θ j) (c j)
    simp only [neg_add_eq_sub] at h
    exact h
  rw [← lintegral_map (f := fun x ↦ ENNReal.ofReal (x ^ 2)) (by fun_prop) (by fun_prop), hmap,
    Probability.lintegral_ofReal_sq_gaussianReal]
  congr 1
  simp only [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ (sq_nonneg ε)]
  ring

/-! ### Minimax risks -/

/-- The minimax risk over `Θ` in the Gaussian sequence model: the infimum over randomized
estimators of the largest risk over `Θ`. -/
def gaussSeqMinimax (Θ : Set (ℕ → ℝ)) (ε : ℝ) : ℝ≥0∞ :=
  ⨅ κ : {κ : Kernel (ℕ → ℝ) (ℕ → ℝ) // IsMarkovKernel κ}, ⨆ θ ∈ Θ, gaussSeqRisk κ.val θ ε

theorem gaussSeqMinimax_def (Θ : Set (ℕ → ℝ)) (ε : ℝ) :
    gaussSeqMinimax Θ ε =
      ⨅ κ : {κ : Kernel (ℕ → ℝ) (ℕ → ℝ) // IsMarkovKernel κ}, ⨆ θ ∈ Θ, gaussSeqRisk κ.val θ ε :=
  (rfl)

/-- The minimax risk is at most the largest risk over `Θ` of any randomized estimator. -/
theorem gaussSeqMinimax_le (κ : Kernel (ℕ → ℝ) (ℕ → ℝ)) [IsMarkovKernel κ] (Θ : Set (ℕ → ℝ))
    (ε : ℝ) : gaussSeqMinimax Θ ε ≤ ⨆ θ ∈ Θ, gaussSeqRisk κ θ ε :=
  iInf_le (fun κ : {κ : Kernel (ℕ → ℝ) (ℕ → ℝ) // IsMarkovKernel κ} ↦
    ⨆ θ ∈ Θ, gaussSeqRisk κ.val θ ε) ⟨κ, inferInstance⟩

/-- A lower bound on the largest risk over `Θ` of every randomized estimator is a lower bound on
the minimax risk. -/
theorem le_gaussSeqMinimax {Θ : Set (ℕ → ℝ)} {ε : ℝ} {b : ℝ≥0∞}
    (h : ∀ κ : Kernel (ℕ → ℝ) (ℕ → ℝ), IsMarkovKernel κ → b ≤ ⨆ θ ∈ Θ, gaussSeqRisk κ θ ε) :
    b ≤ gaussSeqMinimax Θ ε :=
  le_iInf fun κ ↦ h κ.val κ.property

/-- The minimax risk is monotone in the parameter set. -/
theorem gaussSeqMinimax_mono {Θ Θ' : Set (ℕ → ℝ)} (h : Θ ⊆ Θ') (ε : ℝ) :
    gaussSeqMinimax Θ ε ≤ gaussSeqMinimax Θ' ε :=
  iInf_mono fun _ ↦ biSup_mono h

/-- The minimax risk over a single parameter vanishes: the constant estimator has risk zero. -/
@[simp]
theorem gaussSeqMinimax_singleton (θ₀ : ℕ → ℝ) (ε : ℝ) : gaussSeqMinimax {θ₀} ε = 0 := by
  refine le_antisymm ((gaussSeqMinimax_le (Kernel.deterministic (fun _ ↦ θ₀)
    measurable_const) _ ε).trans_eq ?_) zero_le
  simp [gaussSeqRisk_deterministic]

/-- The minimax risk over the empty set vanishes. -/
@[simp]
theorem gaussSeqMinimax_empty (ε : ℝ) : gaussSeqMinimax ∅ ε = 0 :=
  le_antisymm ((gaussSeqMinimax_mono (empty_subset {0}) ε).trans_eq
    (gaussSeqMinimax_singleton 0 ε)) zero_le

/-- The linear minimax risk over `Θ`: the infimum over the diagonal estimators `y ↦ c ⊙ y` of
the largest over `Θ` of their risk `∑' j, (c j² ε² + (1 - c j)² θ j²)`. -/
def gaussSeqLinearMinimax (Θ : Set (ℕ → ℝ)) (ε : ℝ) : ℝ≥0∞ :=
  ⨅ c : ℕ → ℝ, ⨆ θ ∈ Θ, ∑' j, ENNReal.ofReal (c j ^ 2 * ε ^ 2 + (1 - c j) ^ 2 * θ j ^ 2)

theorem gaussSeqLinearMinimax_def (Θ : Set (ℕ → ℝ)) (ε : ℝ) :
    gaussSeqLinearMinimax Θ ε =
      ⨅ c : ℕ → ℝ, ⨆ θ ∈ Θ, ∑' j, ENNReal.ofReal (c j ^ 2 * ε ^ 2 + (1 - c j) ^ 2 * θ j ^ 2) :=
  (rfl)

/-- The linear minimax risk is at most the largest risk over `Θ` of any diagonal estimator. -/
theorem gaussSeqLinearMinimax_le (c : ℕ → ℝ) (Θ : Set (ℕ → ℝ)) (ε : ℝ) :
    gaussSeqLinearMinimax Θ ε ≤
      ⨆ θ ∈ Θ, ∑' j, ENNReal.ofReal (c j ^ 2 * ε ^ 2 + (1 - c j) ^ 2 * θ j ^ 2) :=
  iInf_le (fun c : ℕ → ℝ ↦
    ⨆ θ ∈ Θ, ∑' j, ENNReal.ofReal (c j ^ 2 * ε ^ 2 + (1 - c j) ^ 2 * θ j ^ 2)) c

/-- A lower bound on the largest risk over `Θ` of every diagonal estimator is a lower bound on
the linear minimax risk. -/
theorem le_gaussSeqLinearMinimax {Θ : Set (ℕ → ℝ)} {ε : ℝ} {b : ℝ≥0∞}
    (h : ∀ c : ℕ → ℝ,
      b ≤ ⨆ θ ∈ Θ, ∑' j, ENNReal.ofReal (c j ^ 2 * ε ^ 2 + (1 - c j) ^ 2 * θ j ^ 2)) :
    b ≤ gaussSeqLinearMinimax Θ ε :=
  le_iInf h

/-- The linear minimax risk is monotone in the parameter set. -/
theorem gaussSeqLinearMinimax_mono {Θ Θ' : Set (ℕ → ℝ)} (h : Θ ⊆ Θ') (ε : ℝ) :
    gaussSeqLinearMinimax Θ ε ≤ gaussSeqLinearMinimax Θ' ε :=
  iInf_mono fun _ ↦ biSup_mono h

/-- The linear minimax risk over the zero parameter vanishes, attained by `c = 0`. -/
@[simp]
theorem gaussSeqLinearMinimax_singleton_zero (ε : ℝ) : gaussSeqLinearMinimax {0} ε = 0 :=
  le_antisymm ((gaussSeqLinearMinimax_le 0 _ ε).trans_eq (by simp)) zero_le

/-- The linear minimax risk over the empty set vanishes. -/
@[simp]
theorem gaussSeqLinearMinimax_empty (ε : ℝ) : gaussSeqLinearMinimax ∅ ε = 0 :=
  le_antisymm ((gaussSeqLinearMinimax_mono (empty_subset {0}) ε).trans_eq
    (gaussSeqLinearMinimax_singleton_zero ε)) zero_le

/-- The minimax risk is at most the linear minimax risk, since every diagonal estimator is a
deterministic estimator. -/
theorem gaussSeqMinimax_le_gaussSeqLinearMinimax (Θ : Set (ℕ → ℝ)) (ε : ℝ) :
    gaussSeqMinimax Θ ε ≤ gaussSeqLinearMinimax Θ ε := by
  refine le_gaussSeqLinearMinimax fun c ↦ ?_
  obtain ⟨hc, -⟩ := gaussSeqRisk_diagonal c 0 ε
  refine (gaussSeqMinimax_le (Kernel.deterministic _ hc) Θ ε).trans_eq ?_
  exact biSup_congr fun θ _ ↦ (gaussSeqRisk_diagonal c θ ε).choose_spec

end TauCeti
