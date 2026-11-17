/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.Poisson.Temporal
public import TauCeti.Probability.PointProcess.OccurrenceTime.Gap
public import TauCeti.Probability.Distributions.Exponential.Basic
public import Mathlib.Probability.ProductMeasure
import TauCeti.Probability.Renewal.Exponential.Poisson
import Mathlib.Probability.Independence.InfinitePi

/-!
# Exponential interarrival gaps of homogeneous Poisson random measures

A positive-rate homogeneous temporal Poisson random measure `M` of intensity `r • nnvolume` has
independent interarrival gaps `Measure.occurrenceGap (M ω)` with the exponential law of rate
`r`. Equivalently, the full gap sequence has the product law
`Measure.infinitePi fun _ ↦ nnrealExpMeasure r`, and all gaps are simultaneously strictly
positive almost surely.

Conversely, a measurable random measure on the half-line whose realizations are almost surely
integer-valued and whose interarrival gaps are independent with exponential law of rate `r` is
a homogeneous Poisson random measure of intensity `r • nnvolume`. Local finiteness, infinite
total mass, absence of mass at zero, and simplicity all follow automatically from the
exponential gap laws. Integrality cannot be dropped because adding a fractional mass smaller
than one at the origin leaves all occurrence times and gaps unchanged.

Together with `isPoissonRandomMeasure_smul_nnvolume_iff_count_increments`, this gives the
equivalence between homogeneous Poisson random measures, natural count processes starting at
zero with independent Poisson increments, and independent exponential interarrival gaps. The
zero-rate case is handled separately by `isPoissonRandomMeasure_zero_iff`, where the random
measure is almost surely zero rather than having exponential gaps.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  2nd edition, Wiley, 1971, Chapter I, §4 and Chapter XI, §1.
* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press, 2018, Chapters 3 and 7.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {M : Ω → Measure ℝ≥0} {r : ℝ≥0}

/-- The full interarrival-gap sequence of a positive-rate homogeneous Poisson random measure
has the product law of independent rate-`r` exponential measures on `ℝ≥0`. -/
theorem IsPoissonRandomMeasure.hasLaw_occurrenceGap_infinitePi
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    HasLaw (fun ω ↦ (M ω).occurrenceGap)
      (Measure.infinitePi fun _ : ℕ ↦ nnrealExpMeasure r) P := by
  have := isProbabilityMeasure_expMeasure (NNReal.coe_pos.mpr hr)
  let Q : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ ↦ expMeasure r
  let T (n : ℕ) (ω : ℕ → ℝ) : ℝ≥0 := (ω n).toNNReal
  have hT (n : ℕ) : Measurable (T n) := by fun_prop
  have hi : ProbabilityTheory.iIndepFun T Q :=
    iIndepFun_infinitePi fun _ ↦ measurable_real_toNNReal
  have hcoord (n : ℕ) : HasLaw (fun ω : ℕ → ℝ ↦ ω n) (expMeasure r) Q :=
    ⟨(measurable_pi_apply n).aemeasurable, Measure.infinitePi_map_eval _ n⟩
  have hTL (n : ℕ) : HasLaw (fun ω ↦ (T n ω : ℝ)) (expMeasure r) Q := by
    apply (hcoord n).congr
    filter_upwards [ae_pos_of_hasLaw_expMeasure (hcoord n)] with ω hω
    exact Real.coe_toNNReal _ hω.le
  have hid := identDistrib_increments_occurrenceGap_of_isPoissonRandomMeasure hT hi hTL h
  refine ⟨(Measure.measurable_occurrenceGap.comp h.measurable).aemeasurable, ?_⟩
  rw [← hid.map_eq, hi.map_fun_eq_infinitePi_map hT]
  congr 1
  funext n
  have hcomp : T n = Real.toNNReal ∘ fun ω : ℕ → ℝ ↦ ω n := rfl
  rw [hcomp, ← Measure.map_map measurable_real_toNNReal (measurable_pi_apply n),
    (hcoord n).map_eq, nnrealExpMeasure_def]

/-- Each interarrival gap of a positive-rate homogeneous Poisson random measure has the
nonnegative exponential law of rate `r`. -/
theorem IsPoissonRandomMeasure.hasLaw_occurrenceGap_nnrealExpMeasure
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) (n : ℕ) :
    HasLaw (fun ω ↦ (M ω).occurrenceGap n) (nnrealExpMeasure r) P := by
  have := isProbabilityMeasure_nnrealExpMeasure (NNReal.coe_pos.mpr hr)
  have hcoord := (hasLaw_map (P := Measure.infinitePi fun _ : ℕ ↦ nnrealExpMeasure r)
    (measurable_pi_apply n).aemeasurable).comp (h.hasLaw_occurrenceGap_infinitePi hr)
  simpa only [Measure.infinitePi_map_eval, Function.comp_def] using hcoord

/-- Each interarrival gap of a positive-rate homogeneous Poisson random measure, coerced to `ℝ`,
has Mathlib's exponential law of rate `r`. -/
theorem IsPoissonRandomMeasure.hasLaw_occurrenceGap_expMeasure
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) (n : ℕ) :
    HasLaw (fun ω ↦ ((M ω).occurrenceGap n : ℝ)) (expMeasure r) P := by
  have hcomp := (hasLaw_map (P := nnrealExpMeasure r)
    measurable_coe_nnreal_real.aemeasurable).comp (h.hasLaw_occurrenceGap_nnrealExpMeasure hr n)
  have hmap : (nnrealExpMeasure r).map ((↑) : ℝ≥0 → ℝ) = expMeasure r := by
    rw [nnrealExpMeasure_def, Measure.map_map measurable_coe_nnreal_real measurable_real_toNNReal]
    calc
      (expMeasure r).map (((↑) : ℝ≥0 → ℝ) ∘ Real.toNNReal) = (expMeasure r).map id := by
        apply Measure.map_congr
        filter_upwards [ae_pos_expMeasure r] with x hx
        exact Real.coe_toNNReal x hx.le
      _ = expMeasure r := Measure.map_id
  simpa only [hmap, Function.comp_def] using hcomp

/-- The interarrival gaps of a positive-rate homogeneous Poisson random measure are mutually
independent. -/
theorem IsPoissonRandomMeasure.iIndepFun_occurrenceGap
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    ProbabilityTheory.iIndepFun (fun n ω ↦ (M ω).occurrenceGap n) P := by
  have := h.isProbabilityMeasure
  exact (iIndepFun_iff_hasLaw_Pi_infinitePi
    (fun n ↦ h.hasLaw_occurrenceGap_nnrealExpMeasure hr n)
    (Measure.measurable_occurrenceGap.comp h.measurable).aemeasurable).2
    (h.hasLaw_occurrenceGap_infinitePi hr)

/-- All interarrival gaps of a positive-rate homogeneous Poisson random measure are
simultaneously strictly positive on one full-measure event. -/
theorem IsPoissonRandomMeasure.ae_forall_occurrenceGap_pos
    (h : IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume)) (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ n, 0 < (M ω).occurrenceGap n := by
  rw [ae_all_iff]
  intro n
  filter_upwards [ae_pos_of_hasLaw_expMeasure (h.hasLaw_occurrenceGap_expMeasure hr n)] with ω hω
  exact_mod_cast hω

/-- A measurable random measure on the half-line that is almost surely integer-valued with
independent exponential interarrival gaps of rate `r` is a homogeneous Poisson random measure
of intensity `r • nnvolume`. Local finiteness, infinite total mass, absence of mass at zero,
simplicity, and positivity of `r` all follow from the exponential gap laws. -/
theorem isPoissonRandomMeasure_of_occurrenceGap_expMeasure
    (hM : Measurable M) (hint : ∀ᵐ ω ∂P, (M ω).IsIntegerValued)
    (hindep : iIndepFun (fun n ω ↦ (M ω).occurrenceGap n) P)
    (hlaw : ∀ n, HasLaw (fun ω ↦ ((M ω).occurrenceGap n : ℝ)) (expMeasure r) P) :
    IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume) := by
  let T : ℕ → Ω → ℝ≥0 := fun n ω ↦ (M ω).occurrenceGap n
  have hT (n : ℕ) : Measurable (T n) := (Measure.measurable_occurrenceGap_apply n).comp hM
  have hpois : IsPoissonRandomMeasure P (renewalArrivalMeasure T) ((r : ℝ≥0∞) • nnvolume) :=
    isPoissonRandomMeasure_renewalArrivalMeasure_of_expMeasure hT hindep hlaw
  have hpos : ∀ᵐ ω ∂P, ∀ n, 0 < (M ω).occurrenceGap n := by
    rw [ae_all_iff]
    intro n
    filter_upwards [ae_pos_of_hasLaw_expMeasure (hlaw n)] with ω hω
    exact_mod_cast hω
  have hae : renewalArrivalMeasure T =ᵐ[P] M := by
    filter_upwards [hint, hpos, ae_tendsto_arrival_atTop_of_expMeasure hindep hlaw]
      with ω hωint hωpos hωdiv
    have hfin (n : ℕ) : (M ω).occurrenceTime n ≠ ∞ :=
      Measure.occurrenceTime_ne_top_of_occurrenceGap_pos (hωpos n)
    have huniv : M ω univ = ∞ := Measure.apply_univ_eq_top_of_forall_occurrenceGap_pos hωpos
    have hocc : (M ω).occurrenceTime = fun n ↦ (arrival T (n + 1) ω : ℝ≥0∞) := by
      funext n
      rw [arrival_occurrenceGap M (hfin n), ENNReal.coe_toNNReal (hfin n)]
    have hloc : IsLocallyFiniteMeasure (M ω) := by
      rw [Measure.isLocallyFiniteMeasure_iff_tendsto_occurrenceTime_nhds_top, hocc,
        ENNReal.tendsto_coe_nhds_top]
      exact (Filter.tendsto_add_atTop_iff_nat 1).2 hωdiv
    exact renewalArrivalMeasure_occurrenceGap M hωint huniv
  exact hpois.congr hM hae

/-- **Exponential-gap characterization of homogeneous Poisson random measures.**
For a positive rate `r`, a measurable random measure on the half-line is a homogeneous Poisson
random measure of intensity `r • nnvolume` if and only if its realizations are almost surely
integer-valued and its interarrival gaps are independent with exponential law of rate `r`.

Integrality cannot be dropped because adding a fractional mass smaller than one at the origin
leaves all occurrence times and gaps unchanged. For `r = 0`, see
`isPoissonRandomMeasure_zero_iff`. -/
theorem isPoissonRandomMeasure_smul_nnvolume_iff_occurrenceGap
    (hr : 0 < r) (hM : Measurable M) :
    IsPoissonRandomMeasure P M ((r : ℝ≥0∞) • nnvolume) ↔
      (∀ᵐ ω ∂P, (M ω).IsIntegerValued) ∧
      iIndepFun (fun n ω ↦ (M ω).occurrenceGap n) P ∧
      ∀ n, HasLaw (fun ω ↦ ((M ω).occurrenceGap n : ℝ)) (expMeasure r) P :=
  ⟨fun h ↦ ⟨h.ae_isIntegerValued, h.iIndepFun_occurrenceGap hr,
    h.hasLaw_occurrenceGap_expMeasure hr⟩,
    fun ⟨hint, hindep, hlaw⟩ ↦
      isPoissonRandomMeasure_of_occurrenceGap_expMeasure hM hint hindep hlaw⟩

/-- **Equivalence of Poisson count increments and exponential interarrival gaps.**
For a measurable random measure represented almost surely on all closed initial intervals by a
natural-valued process `N`, and a positive rate `r`, `N` starts at zero almost surely with
independent rate-`r` Poisson increments if and only if the interarrival gaps of `M` are
independent with exponential law of rate `r`. -/
theorem count_increments_iff_occurrenceGap_expMeasure
    {N : ℝ≥0 → Ω → ℕ} (hr : 0 < r) (hM : Measurable M)
    (hcount : ∀ᵐ ω ∂P, ∀ t, M ω (Iic t) = (N t ω : ℝ≥0∞)) :
    ((∀ᵐ ω ∂P, N 0 ω = 0) ∧ HasIndepIncrements N P ∧
      ∀ s t, s ≤ t → HasLaw (fun ω ↦ N t ω - N s ω) (poissonMeasure (r * (t - s))) P) ↔
    (iIndepFun (fun n ω ↦ (M ω).occurrenceGap n) P ∧
      ∀ n, HasLaw (fun ω ↦ ((M ω).occurrenceGap n : ℝ)) (expMeasure r) P) := by
  have hint : ∀ᵐ ω ∂P, (M ω).IsIntegerValued := by
    filter_upwards [hcount] with ω hω
    apply Measure.isIntegerValued_of_restrict (s := fun n : ℕ ↦ Iic (n : ℝ≥0))
    · ext t
      simp only [mem_iUnion, mem_Iic, mem_univ, iff_true]
      exact exists_nat_ge t
    · intro n
      apply Measure.isIntegerValued_of_isPiSystem
        (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Iic (α := ℝ≥0))) isPiSystem_Iic
      · rintro _ ⟨t, rfl⟩
        exact ⟨N (min t n) ω, by
          simp [Measure.restrict_apply measurableSet_Iic, Iic_inter_Iic, hω]⟩
      · exact ⟨N n ω, by simp [hω]⟩
  rw [← isPoissonRandomMeasure_smul_nnvolume_iff_count_increments hM hcount,
    isPoissonRandomMeasure_smul_nnvolume_iff_occurrenceGap hr hM]
  exact ⟨fun ⟨_, hi, hl⟩ ↦ ⟨hi, hl⟩, fun ⟨hi, hl⟩ ↦ ⟨hint, hi, hl⟩⟩

end TauCeti.Probability
