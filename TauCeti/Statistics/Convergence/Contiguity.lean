/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs
import TauCeti.MeasureTheory.Measure.TotalVariation.Basic

/-!
# Contiguity of sequences of measures

A family of measures `Q` on varying measurable spaces `Ω i` is **contiguous** to `P` along a
filter `l` (written `IsContiguous l P Q`, corresponding to the classical notation `Q ◁ P`) if for
every family of measurable events `A i : Set (Ω i)`, `(P i).real (A i) → 0` along `l` implies
`(Q i).real (A i) → 0` along `l`.

Contiguity is an asymptotic analogue of absolute continuity: it forms a preorder (reflexive and
transitive), transfers convergence in probability to a constant from `P` to `Q`, follows from
total variation convergence `tvDist (P i) (Q i) → 0`, and follows from eventual absolute
continuity `Q i ≪ P i` together with uniform integrability of the likelihood ratios
`(Q i).rnDeriv (P i)` (a consequence of Le Cam's first lemma).

## Main definitions

* `TauCeti.IsContiguous` — contiguity of a family of measures `Q` to `P` along a filter `l` on
  possibly varying sample spaces `Ω i`.

## Main statements

* `TauCeti.isContiguous_iff` — definitional characterization.
* `TauCeti.IsContiguous.refl` and `TauCeti.IsContiguous.trans` — reflexivity and transitivity.
* `TauCeti.isContiguous_of_tendsto_tvDist_zero` — vanishing total variation distance implies
  contiguity.
* `TauCeti.IsContiguous.tendsto_measureReal_dist_ge_zero` and
  `TauCeti.IsContiguous.tendstoInMeasure_const` — contiguity transfers convergence in probability
  to a constant.
* `TauCeti.isContiguous_of_absolutelyContinuous_of_uniformlyIntegrable` — eventual absolute
  continuity plus uniform tail control of likelihood ratios implies contiguity.
* `TauCeti.isContiguous_const_of_absolutelyContinuous` — constant finite measures with `Q₀ ≪ P₀`
  are contiguous along any filter.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, §6.2,
  Lemma 6.4, pp. 87–88.
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace TauCeti

section Basic

variable {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]

/-- `IsContiguous l P Q` states that `Q` is **contiguous** to `P` along the filter `l` (classically
`Q ◁ P`): for every family of measurable events `A i : Set (Ω i)`, `(P i).real (A i) → 0` along
`l` implies `(Q i).real (A i) → 0` along `l`. -/
def IsContiguous (l : Filter ι) (P Q : (i : ι) → Measure (Ω i)) : Prop :=
  ∀ A : (i : ι) → Set (Ω i), (∀ i, MeasurableSet (A i)) →
    Tendsto (fun i ↦ (P i).real (A i)) l (𝓝 0) →
    Tendsto (fun i ↦ (Q i).real (A i)) l (𝓝 0)

/-- Characterization of `IsContiguous`. -/
theorem isContiguous_iff {l : Filter ι} {P Q : (i : ι) → Measure (Ω i)} :
    IsContiguous l P Q ↔
      ∀ A : (i : ι) → Set (Ω i), (∀ i, MeasurableSet (A i)) →
        Tendsto (fun i ↦ (P i).real (A i)) l (𝓝 0) →
        Tendsto (fun i ↦ (Q i).real (A i)) l (𝓝 0) :=
  Iff.rfl

/-- Contiguity is reflexive. -/
@[refl]
theorem IsContiguous.refl (l : Filter ι) (P : (i : ι) → Measure (Ω i)) :
    IsContiguous l P P :=
  fun _ _ hP ↦ hP

/-- Contiguity is transitive. -/
@[trans]
theorem IsContiguous.trans {l : Filter ι} {P Q R : (i : ι) → Measure (Ω i)}
    (hPQ : IsContiguous l P Q) (hQR : IsContiguous l Q R) : IsContiguous l P R :=
  fun A hA hP ↦ hQR A hA (hPQ A hA hP)

/-- If the total variation distance between finite measures `P i` and `Q i` tends to `0` along `l`,
then `Q` is contiguous to `P` along `l`. -/
theorem isContiguous_of_tendsto_tvDist_zero {l : Filter ι} {P Q : (i : ι) → Measure (Ω i)}
    [∀ i, IsFiniteMeasure (P i)] [∀ i, IsFiniteMeasure (Q i)]
    (htv : Tendsto (fun i ↦ tvDist (P i) (Q i)) l (𝓝 0)) :
    IsContiguous l P Q := by
  intro A hA hP
  refine squeeze_zero (fun _ ↦ measureReal_nonneg) (fun i ↦ ?_)
    (by simpa only [add_zero] using hP.add htv)
  have hdiff := abs_measureReal_sub_le_tvDist (μ := P i) (ν := Q i) (hA i)
  linarith [neg_le_of_abs_le hdiff]

/-- Under contiguity, convergence to a constant in `P`-probability along varying sample spaces
implies convergence to the same constant in `Q`-probability. -/
theorem IsContiguous.tendsto_measureReal_dist_ge_zero {E : Type*} [PseudoMetricSpace E]
    [MeasurableSpace E] [OpensMeasurableSpace E] {l : Filter ι} {P Q : (i : ι) → Measure (Ω i)}
    (h : IsContiguous l P Q) {X : (i : ι) → Ω i → E} (hX : ∀ i, Measurable (X i)) {c : E}
    (hP : ∀ ε > 0, Tendsto (fun i ↦ (P i).real {ω | ε ≤ dist (X i ω) c}) l (𝓝 0)) :
    ∀ ε > 0, Tendsto (fun i ↦ (Q i).real {ω | ε ≤ dist (X i ω) c}) l (𝓝 0) := fun ε hε ↦
  h (fun i ↦ {ω | ε ≤ dist (X i ω) c})
    (fun i ↦
      (isClosed_le continuous_const (continuous_id.dist continuous_const)).measurableSet.preimage
        (hX i))
    (hP ε hε)

/-- Under contiguity for constant finite measures on a shared sample space, convergence in
`P₀`-measure to a constant implies convergence in `Q₀`-measure to the same constant. -/
theorem IsContiguous.tendstoInMeasure_const {Ω₀ E : Type*} [MeasurableSpace Ω₀]
    [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {l : Filter ι} {P₀ Q₀ : Measure Ω₀} [IsFiniteMeasure P₀] [IsFiniteMeasure Q₀]
    (h : IsContiguous l (fun _ ↦ P₀) (fun _ ↦ Q₀))
    {X : ι → Ω₀ → E} (hX : ∀ i, Measurable (X i)) {c : E}
    (hP : TendstoInMeasure P₀ X l (fun _ ↦ c)) :
    TendstoInMeasure Q₀ X l (fun _ ↦ c) := by
  rw [tendstoInMeasure_iff_measureReal_dist] at hP ⊢
  exact h.tendsto_measureReal_dist_ge_zero hX hP

/-- **Contiguity from absolute continuity and uniform tail control of likelihood ratios.** If
`P i`, `Q i` are finite measures with `Q i ≪ P i` eventually along `l`, and the `Q i`-mass of
`{ω | C < dQᵢ/dPᵢ (ω)}` can be made uniformly small for large `C`, then `Q` is contiguous to `P`
along `l`. -/
theorem isContiguous_of_absolutelyContinuous_of_uniformlyIntegrable {l : Filter ι}
    {P Q : (i : ι) → Measure (Ω i)} [∀ i, IsFiniteMeasure (P i)] [∀ i, IsFiniteMeasure (Q i)]
    (hac : ∀ᶠ i in l, Q i ≪ P i)
    (hui : ∀ ε > 0, ∃ C : ℝ≥0,
      ∀ᶠ i in l, (Q i).real {ω | (C : ℝ≥0∞) < (Q i).rnDeriv (P i) ω} ≤ ε) :
    IsContiguous l P Q := by
  intro A hA hP
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨C, hC⟩ := hui (ε / 2) (half_pos hε)
  set M : ℝ := (C : ℝ) + 1
  have hM : 0 < M := by positivity
  have hP_ev := Metric.tendsto_nhds.1 hP ((ε / 2) / M) (by positivity)
  filter_upwards [hac, hC, hP_ev] with i h_ac h_tail h_Pi
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at h_Pi ⊢
  let B : Set (Ω i) := {ω | (C : ℝ≥0∞) < (Q i).rnDeriv (P i) ω}
  have hB : MeasurableSet B := measurableSet_lt measurable_const (Measure.measurable_rnDeriv _ _)
  have h_le_enn : Q i (A i ∩ Bᶜ) ≤ (C : ℝ≥0∞) * P i (A i) := by
    calc Q i (A i ∩ Bᶜ)
        = ∫⁻ ω in A i ∩ Bᶜ, (Q i).rnDeriv (P i) ω ∂(P i) :=
            (Measure.setLIntegral_rnDeriv h_ac (A i ∩ Bᶜ)).symm
      _ ≤ ∫⁻ _ in A i ∩ Bᶜ, (C : ℝ≥0∞) ∂(P i) :=
            setLIntegral_mono' ((hA i).inter hB.compl) fun ω hω ↦ not_lt.1 hω.2
      _ = (C : ℝ≥0∞) * P i (A i ∩ Bᶜ) := setLIntegral_const _ _
      _ ≤ (C : ℝ≥0∞) * P i (A i) := by gcongr; exact Set.inter_subset_left
  have h_le_real : (Q i).real (A i ∩ Bᶜ) ≤ (C : ℝ) * (P i).real (A i) := by
    have hto := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _)) h_le_enn
    simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.coe_toReal] using hto
  have h_low : (Q i).real (A i ∩ Bᶜ) < ε / 2 := by
    calc (Q i).real (A i ∩ Bᶜ)
        ≤ (C : ℝ) * (P i).real (A i) := h_le_real
      _ ≤ M * (P i).real (A i) :=
            mul_le_mul_of_nonneg_right (by linarith) measureReal_nonneg
      _ < M * ((ε / 2) / M) := mul_lt_mul_of_pos_left h_Pi hM
      _ = ε / 2 := mul_div_cancel₀ (ε / 2) hM.ne'
  have h_split : A i ⊆ (A i ∩ Bᶜ) ∪ B := fun ω hω ↦ by
    by_cases hωB : ω ∈ B
    · exact Or.inr hωB
    · exact Or.inl ⟨hω, hωB⟩
  calc (Q i).real (A i)
      ≤ (Q i).real ((A i ∩ Bᶜ) ∪ B) := measureReal_mono h_split
    _ ≤ (Q i).real (A i ∩ Bᶜ) + (Q i).real B := measureReal_union_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le h_low h_tail
    _ = ε := add_halves ε

/-- For constant finite measures `P₀`, `Q₀`, absolute continuity `Q₀ ≪ P₀` implies contiguity
along any filter `l`. -/
theorem isContiguous_const_of_absolutelyContinuous {Ω₀ : Type*} [MeasurableSpace Ω₀]
    (l : Filter ι) {P₀ Q₀ : Measure Ω₀} [IsFiniteMeasure P₀] [IsFiniteMeasure Q₀]
    (h : Q₀ ≪ P₀) : IsContiguous l (fun _ ↦ P₀) (fun _ ↦ Q₀) := by
  intro A _ hP
  have hP' : Tendsto (fun i ↦ P₀ (A i)) l (𝓝 0) := by
    have := ENNReal.tendsto_ofReal hP
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top P₀ _),
      ENNReal.ofReal_zero] using this
  have hQ' := tendsto_setLIntegral_zero (μ := P₀) (f := Q₀.rnDeriv P₀)
    (Measure.lintegral_rnDeriv_lt_top Q₀ P₀).ne hP'
  simp_rw [Measure.setLIntegral_rnDeriv h] at hQ'
  simpa only [measureReal_def, Function.comp_def, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hQ'

end Basic

end TauCeti
