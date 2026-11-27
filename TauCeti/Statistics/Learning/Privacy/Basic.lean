/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Probability.Kernel.Composition.MeasureComp
-- Proof-only: a path of single-record changes between two data sets.
import TauCeti.InformationTheory.Hamming
-- Proof-only: affine domination of measures extends from sets to `[0, 1]`-valued functions.
import TauCeti.MeasureTheory.Integral.LayerCake

/-!
# Differential privacy: definitions, post-processing and group privacy

A randomized algorithm on data sets of `n` records is a map `M : (Fin n → X) → Measure Y`. It is
`(ε, δ)`-differentially private (`TauCeti.IsDifferentiallyPrivate M ε δ`) when, for any two data
sets `D, D'` that differ in at most one record (`hammingDist D D' ≤ 1`) and every measurable event
`A`, `P(M(D) ∈ A) ≤ e^ε P(M(D') ∈ A) + δ` (Dwork–Roth, *The algorithmic foundations of
differential privacy*, 2014, Def 2.4, p. 17, with neighbours differing by substitution of a
record). A release kernel `Q : X → Measure Y` is `ε`-locally private
(`TauCeti.IsLocallyPrivate Q ε`) when `Q(B | x) ≤ e^ε Q(B | x')` for all inputs `x, x'` and
measurable `B`; this is `ε`-differential privacy of `Q` on data sets of one record.

The privacy inequality is stated for the real values `Measure.real` of the measures; for finite
measures and `δ ≥ 0` it is equivalent to the same inequality in `ℝ≥0∞`
(`TauCeti.isDifferentiallyPrivate_iff_measure_le`), in which form it extends from events to
functions with values in `[0, 1]` (`TauCeti.IsDifferentiallyPrivate.lintegral_le`).

## Main results

* `TauCeti.IsDifferentiallyPrivate.lintegral_le`: the function form of the privacy inequality,
  `∫⁻ f d(M D) ≤ e^ε ∫⁻ f d(M D') + δ` for `f ≤ 1`.
* `TauCeti.IsDifferentiallyPrivate.postProcess`: for algorithms with finite measures as values,
  post-processing by a Markov kernel preserves `(ε, δ)`-differential privacy (Dwork–Roth,
  Prop 2.1, p. 19).
* `TauCeti.IsDifferentiallyPrivate.measureReal_le_of_hammingDist_le`: group privacy, an
  `ε`-differentially private algorithm compares data sets at Hamming distance at most `k` with the
  factor `e^(kε)` (Dwork–Roth, Thm 2.2, p. 20).
* `TauCeti.isDifferentiallyPrivate_postProcess`: the conjunction of post-processing, for
  probability measures as values and Markov kernels, and group privacy for `δ = 0`.
* `TauCeti.isLocallyPrivate_iff_isDifferentiallyPrivate`: local privacy is differential privacy
  on data sets of one record; `TauCeti.IsLocallyPrivate.postProcess` is post-processing for it.

The layer-cake proof of the function form follows the first stage of the proof of
`CKSD.isDifferentiallyPrivate_compProd` in lean-CKSD (<https://github.com/bjbraams/lean-CKSD>),
file `CKSD/Learning/Privacy/Basic.lean`, whose privacy predicate is stated for kernels and an
arbitrary neighbour relation in `ℝ≥0∞`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti

variable {X Y Y' : Type*} [MeasurableSpace Y] [MeasurableSpace Y'] {n : ℕ}

/-! ### Differential privacy -/

/-- `(ε, δ)`-differential privacy of a randomized algorithm on data sets of `n` records: for data
sets differing in at most one record and every measurable event,
`P(M(D) ∈ A) ≤ e^ε P(M(D') ∈ A) + δ`. -/
def IsDifferentiallyPrivate [DecidableEq X] (M : (Fin n → X) → Measure Y) (ε δ : ℝ) : Prop :=
  ∀ D D' : Fin n → X, hammingDist D D' ≤ 1 → ∀ A : Set Y, MeasurableSet A →
    (M D).real A ≤ Real.exp ε * (M D').real A + δ

section DifferentiallyPrivate

variable [DecidableEq X] {M : (Fin n → X) → Measure Y} {ε ε' δ δ' : ℝ}

/-- The defining property of `(ε, δ)`-differential privacy. -/
theorem isDifferentiallyPrivate_iff :
    IsDifferentiallyPrivate M ε δ ↔ ∀ D D' : Fin n → X, hammingDist D D' ≤ 1 →
      ∀ A : Set Y, MeasurableSet A → (M D).real A ≤ Real.exp ε * (M D').real A + δ :=
  Iff.rfl

/-- The privacy inequality for one pair of neighbouring data sets and one measurable event. -/
theorem IsDifferentiallyPrivate.measureReal_le (h : IsDifferentiallyPrivate M ε δ)
    {D D' : Fin n → X} (hD : hammingDist D D' ≤ 1) {A : Set Y} (hA : MeasurableSet A) :
    (M D).real A ≤ Real.exp ε * (M D').real A + δ :=
  h D D' hD A hA

/-- Once there is a data set, the additive parameter of a private algorithm is nonnegative. -/
theorem IsDifferentiallyPrivate.delta_nonneg (h : IsDifferentiallyPrivate M ε δ)
    (D : Fin n → X) : 0 ≤ δ := by
  simpa using h.measureReal_le (D := D) (D' := D) (by simp) MeasurableSet.empty

/-- Differential privacy is monotone in both parameters. -/
theorem IsDifferentiallyPrivate.mono (h : IsDifferentiallyPrivate M ε δ) (hε : ε ≤ ε')
    (hδ : δ ≤ δ') : IsDifferentiallyPrivate M ε' δ' := fun D D' hD A hA ↦ by
  have := h.measureReal_le hD hA
  have : Real.exp ε * (M D').real A ≤ Real.exp ε' * (M D').real A := by gcongr
  linarith

/-- For finite measures and `δ ≥ 0`, differential privacy is the same inequality in `ℝ≥0∞`:
`M D A ≤ e^ε M D' A + δ`. -/
theorem isDifferentiallyPrivate_iff_measure_le (hM : ∀ D, IsFiniteMeasure (M D)) (hδ : 0 ≤ δ) :
    IsDifferentiallyPrivate M ε δ ↔ ∀ D D' : Fin n → X, hammingDist D D' ≤ 1 →
      ∀ A : Set Y, MeasurableSet A →
        M D A ≤ ENNReal.ofReal (Real.exp ε) * M D' A + ENNReal.ofReal δ := by
  refine forall₄_congr fun D D' _ A ↦ forall_congr' fun _ ↦ ?_
  rw [← ofReal_measureReal, ← ofReal_measureReal (μ := M D'),
    ← ENNReal.ofReal_mul (Real.exp_pos ε).le, ← ENNReal.ofReal_add (by positivity) hδ,
    ENNReal.ofReal_le_ofReal_iff (by positivity)]

/-- **Function form of differential privacy.** For finite measures, the privacy inequality
extends from events to functions with values at most `1`:
`∫⁻ f d(M D) ≤ e^ε ∫⁻ f d(M D') + δ`. -/
theorem IsDifferentiallyPrivate.lintegral_le (h : IsDifferentiallyPrivate M ε δ)
    (hM : ∀ D, IsFiniteMeasure (M D)) {D D' : Fin n → X} (hD : hammingDist D D' ≤ 1)
    {f : Y → ℝ≥0∞} (hf : ∀ y, f y ≤ 1) :
    ∫⁻ y, f y ∂M D ≤ ENNReal.ofReal (Real.exp ε) * ∫⁻ y, f y ∂M D' + ENNReal.ofReal δ :=
  lintegral_le_mul_lintegral_add_of_forall_measure_le
    ((isDifferentiallyPrivate_iff_measure_le hM (h.delta_nonneg D)).1 h D D' hD) hf

/-- **Post-processing** (Dwork–Roth, Prop 2.1). Applying a Markov kernel (or the zero kernel) to
the output of an `(ε, δ)`-differentially private algorithm with finite measures as values gives
an `(ε, δ)`-differentially private algorithm. -/
theorem IsDifferentiallyPrivate.postProcess (h : IsDifferentiallyPrivate M ε δ)
    (hM : ∀ D, IsFiniteMeasure (M D)) (K : Kernel Y Y') [IsZeroOrMarkovKernel K] :
    IsDifferentiallyPrivate (fun D ↦ K ∘ₘ M D) ε δ := by
  rcases isEmpty_or_nonempty (Fin n → X) with hX | ⟨⟨D₀⟩⟩
  · exact fun D ↦ hX.elim D
  refine (isDifferentiallyPrivate_iff_measure_le (fun _ ↦ inferInstance)
    (h.delta_nonneg D₀)).2 fun D D' hD A hA ↦ ?_
  simp only [Measure.bind_apply hA K.aemeasurable]
  exact h.lintegral_le hM hD fun _ ↦ prob_le_one

/-- **Group privacy** (Dwork–Roth, Thm 2.2). An `ε`-differentially private algorithm compares
data sets at Hamming distance at most `k` with the factor `e^(kε)`. -/
theorem IsDifferentiallyPrivate.measureReal_le_of_hammingDist_le
    (h : IsDifferentiallyPrivate M ε 0) {k : ℕ} {D D' : Fin n → X} (hD : hammingDist D D' ≤ k)
    {A : Set Y} (hA : MeasurableSet A) :
    (M D).real A ≤ Real.exp (k * ε) * (M D').real A := by
  induction k generalizing D with
  | zero =>
    rw [Nat.le_zero, hammingDist_eq_zero] at hD
    simp [hD]
  | succ k ih =>
    obtain ⟨E, hDE, hED⟩ := exists_hammingDist_le_one_and_hammingDist_le hD
    calc (M D).real A ≤ Real.exp ε * (M E).real A := by simpa using h.measureReal_le hDE hA
      _ ≤ Real.exp ε * (Real.exp (k * ε) * (M D').real A) := by gcongr; exact ih hED
      _ = Real.exp ((k + 1 : ℕ) * ε) * (M D').real A := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        push_cast
        ring

/-- **Post-processing and group privacy** (Dwork–Roth, Prop 2.1 and Thm 2.2): a Markov kernel
applied to a private release with probability measures as values is private with the same
parameters, and an `ε`-private algorithm compares data sets at Hamming distance at most `k` with
the factor `e^(kε)`. -/
theorem isDifferentiallyPrivate_postProcess (M : (Fin n → X) → Measure Y)
    (hM : ∀ D, IsProbabilityMeasure (M D)) (ε δ : ℝ) (hdp : IsDifferentiallyPrivate M ε δ) :
    (∀ K : Kernel Y Y', IsMarkovKernel K → IsDifferentiallyPrivate (fun D ↦ K ∘ₘ M D) ε δ) ∧
      (δ = 0 → ∀ k : ℕ, ∀ D D' : Fin n → X, hammingDist D D' ≤ k → ∀ A : Set Y,
        MeasurableSet A → (M D).real A ≤ Real.exp (k * ε) * (M D').real A) := by
  refine ⟨fun K _ ↦ hdp.postProcess (fun D ↦ inferInstance) K, ?_⟩
  rintro rfl k D D' hD A hA
  exact hdp.measureReal_le_of_hammingDist_le hD hA

/-- An algorithm whose output law is the same on neighbouring data sets is
`(0, 0)`-differentially private. -/
theorem isDifferentiallyPrivate_of_forall_eq
    (h : ∀ D D' : Fin n → X, hammingDist D D' ≤ 1 → M D = M D') :
    IsDifferentiallyPrivate M 0 0 := fun D D' hD A _ ↦ by
  simp [h D D' hD]

/-- A constant algorithm is `(0, 0)`-differentially private. -/
theorem isDifferentiallyPrivate_const (ν : Measure Y) :
    IsDifferentiallyPrivate (fun _ : Fin n → X ↦ ν) 0 0 :=
  isDifferentiallyPrivate_of_forall_eq fun _ _ _ ↦ rfl

/-- Every algorithm with probability measures (or zero measures) as values is
`(ε, δ)`-differentially private when `δ ≥ 1`. -/
theorem isDifferentiallyPrivate_of_one_le (hM : ∀ D, IsZeroOrProbabilityMeasure (M D))
    (hδ : 1 ≤ δ) : IsDifferentiallyPrivate M ε δ := fun D D' _ A _ ↦ by
  have : (M D).real A ≤ 1 := measureReal_le_one
  have : 0 ≤ Real.exp ε * (M D').real A := by positivity
  linarith

end DifferentiallyPrivate

/-! ### Local privacy -/

/-- `ε`-local privacy of a release kernel: `Q(B | x) ≤ e^ε Q(B | x')` for all inputs `x, x'` and
measurable `B`. -/
def IsLocallyPrivate (Q : X → Measure Y) (ε : ℝ) : Prop :=
  ∀ x x' : X, ∀ B : Set Y, MeasurableSet B → (Q x).real B ≤ Real.exp ε * (Q x').real B

section LocallyPrivate

variable {Q : X → Measure Y} {ε ε' : ℝ}

/-- The defining property of `ε`-local privacy. -/
theorem isLocallyPrivate_iff :
    IsLocallyPrivate Q ε ↔ ∀ x x' : X, ∀ B : Set Y, MeasurableSet B →
      (Q x).real B ≤ Real.exp ε * (Q x').real B :=
  Iff.rfl

/-- The local privacy inequality for one pair of inputs and one measurable event. -/
theorem IsLocallyPrivate.measureReal_le (h : IsLocallyPrivate Q ε) (x x' : X) {B : Set Y}
    (hB : MeasurableSet B) : (Q x).real B ≤ Real.exp ε * (Q x').real B :=
  h x x' B hB

/-- Local privacy is monotone in the parameter. -/
theorem IsLocallyPrivate.mono (h : IsLocallyPrivate Q ε) (hε : ε ≤ ε') :
    IsLocallyPrivate Q ε' := fun x x' B hB ↦
  (h.measureReal_le x x' hB).trans (by gcongr)

/-- Local privacy is differential privacy, with `δ = 0`, on data sets of one record. -/
theorem isLocallyPrivate_iff_isDifferentiallyPrivate [DecidableEq X] :
    IsLocallyPrivate Q ε ↔ IsDifferentiallyPrivate (fun D : Fin 1 → X ↦ Q (D 0)) ε 0 := by
  refine ⟨fun h D D' _ A hA ↦ by simpa using h.measureReal_le (D 0) (D' 0) hA,
    fun h x x' B hB ↦ ?_⟩
  simpa using h.measureReal_le (hammingDist_le_one_of_subsingleton (fun _ ↦ x) fun _ ↦ x') hB

/-- For finite measures, local privacy is the same inequality in `ℝ≥0∞`:
`Q x B ≤ e^ε Q x' B`. -/
theorem isLocallyPrivate_iff_measure_le (hQ : ∀ x, IsFiniteMeasure (Q x)) :
    IsLocallyPrivate Q ε ↔
      ∀ x x' : X, ∀ B : Set Y, MeasurableSet B → Q x B ≤ ENNReal.ofReal (Real.exp ε) * Q x' B := by
  refine forall₃_congr fun x x' B ↦ forall_congr' fun _ ↦ ?_
  rw [← ofReal_measureReal, ← ofReal_measureReal (μ := Q x'),
    ← ENNReal.ofReal_mul (Real.exp_pos ε).le, ENNReal.ofReal_le_ofReal_iff (by positivity)]

/-- **Post-processing** for local privacy: applying a Markov kernel (or the zero kernel) to the
releases of an `ε`-locally private kernel with finite measures as values gives an `ε`-locally
private kernel. -/
theorem IsLocallyPrivate.postProcess (h : IsLocallyPrivate Q ε) (hQ : ∀ x, IsFiniteMeasure (Q x))
    (K : Kernel Y Y') [IsZeroOrMarkovKernel K] : IsLocallyPrivate (fun x ↦ K ∘ₘ Q x) ε := by
  classical
  exact isLocallyPrivate_iff_isDifferentiallyPrivate.2 <|
    (isLocallyPrivate_iff_isDifferentiallyPrivate.1 h).postProcess (fun D ↦ hQ (D 0)) K

end LocallyPrivate

end TauCeti
