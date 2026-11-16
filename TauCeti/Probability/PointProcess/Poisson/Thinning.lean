/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.Poisson.Marking
public import TauCeti.Probability.PointProcess.Poisson.Splitting
import TauCeti.Probability.Distributions.Bernoulli.Measurability
import TauCeti.MeasureTheory.Measure.Prod

/-!
# Independent thinning of uncoloured temporal Poisson random measures

Given an uncoloured temporal Poisson random measure `N : Ω → Measure ℝ≥0` with locally finite
intensity `Λ`, independent binary marking by any Markov kernel `κ : Kernel ℝ≥0 Bool` produces
a marked Poisson random measure `M` on `ℝ≥0 × Bool` with intensity `Λ ⊗ₘ κ` whose ground
projection recovers `N` almost surely. On `ℝ≥0`, canonical marking `κ.marking` agrees on every
locally finite integer-valued realization with independently marking its ordered finite
`Measure.occurrenceTime`s.

This file connects the marking construction in `Poisson.Marking` with the marked temporal count
splitting API in `Poisson.Splitting`:

* For any probability space carrying a coupled pair `(N, M)` with joint law
  `(P.map N) ⊗ₘ κ.marking`, the two colour projections sum to `N` almost surely, their
  complete natural count paths on `(0, t]` are independent, have independent increments with
  Poisson interval and increment laws `∫⁻ x in Ioc s t, κ x {b} ∂Λ`, and add to the ground
  count path of `N` simultaneously at all times `t : ℝ≥0` on a single full-measure event.
* For constant Bernoulli marks `bernoulliMeasure true false p` (including `p = 0`, `p = 1`) and
  homogeneous ground intensity `r • nnvolume` (including `r = 0`), the thinned random measures
  and count processes have rates `r * p` and `r * (1 - p)`, with explicit boundary-case
  characterizations where a zero-rate colour vanishes identically almost surely while the
  complementary colour equals `N` almost surely.
* Existential theorems construct these independent time-dependent and homogeneous Bernoulli
  thinnings on the canonical measure-preserving extension `Ω × Measure (ℝ≥0 × Bool)` of any
  uncoloured temporal Poisson random measure.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Chapters 5 and 7 (independent marking and thinning of temporal Poisson processes).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti.Probability.IsPoissonRandomMeasure

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {N : Ω → Measure ℝ≥0} {Λ : Measure ℝ≥0}

private theorem compProd_Ioc_prod_singleton_lt_top [IsLocallyFiniteMeasure Λ]
    (κ : Kernel ℝ≥0 Bool) [IsMarkovKernel κ] (b : Bool) (s t : ℝ≥0) :
    (Λ ⊗ₘ κ) (Ioc s t ×ˢ {b}) < ∞ := by
  calc
    (Λ ⊗ₘ κ) (Ioc s t ×ˢ {b}) ≤ (Λ ⊗ₘ κ) (Ioc s t ×ˢ univ) :=
      measure_mono (prod_mono Subset.rfl (subset_univ _))
    _ = Λ (Ioc s t) := by
      rw [prod_univ, ← Measure.fst_apply measurableSet_Ioc, Measure.fst_compProd]
    _ < ∞ := measure_Ioc_lt_top

section CoupledBinary

variable {κ : Kernel ℝ≥0 Bool} {M : Ω → Measure (ℝ≥0 × Bool)}

/-- For any binary Markov kernel `κ` and any coupled marking `(N, M)` with joint law
`(P.map N) ⊗ₘ κ.marking`, the two colour projections sum to `N` almost surely. -/
theorem ae_map_fst_restrict_add_of_map_prod_eq_marking [IsLocallyFiniteMeasure Λ]
    [IsMarkovKernel κ] (h : IsPoissonRandomMeasure P N Λ) (hM : Measurable M)
    (hjoint : P.map (fun ω => (N ω, M ω)) = (P.map N) ⊗ₘ κ.marking) :
    ∀ᵐ ω ∂P,
      ((M ω).restrict (univ ×ˢ {true})).map Prod.fst +
        ((M ω).restrict (univ ×ˢ {false})).map Prod.fst = N ω := by
  have hcompl : ({true}ᶜ : Set Bool) = {false} := by ext b; cases b <;> simp
  filter_upwards [(h.of_map_prod_eq_compProd_marking hM hjoint).2] with ω hω
  have hsum := (M ω).map_fst_restrict_univ_prod_add_compl (measurableSet_singleton true)
  rwa [hcompl, hω] at hsum

/-- The natural cumulative count paths of the two binary colour projections add to the ground
count path of `N` simultaneously at every time `t : ℝ≥0` on a single full-measure event. -/
theorem ae_nat_count_eq_add_of_map_prod_eq_marking [IsLocallyFiniteMeasure Λ]
    [IsMarkovKernel κ] (h : IsPoissonRandomMeasure P N Λ) (hM : Measurable M)
    (hjoint : P.map (fun ω => (N ω, M ω)) = (P.map N) ⊗ₘ κ.marking) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ⌊(N ω (Ioc 0 t)).toNNReal⌋₊ =
        ⌊(M ω (Ioc 0 t ×ˢ {true})).toNNReal⌋₊ +
          ⌊(M ω (Ioc 0 t ×ˢ {false})).toNNReal⌋₊ := by
  obtain ⟨hPM, hproj⟩ := h.of_map_prod_eq_compProd_marking hM hjoint
  have hadd := hPM.ae_nat_count_prod_union_eq_add_of_measure_Ioc_prod_lt_top
    (measurableSet_singleton true) (measurableSet_singleton false)
    (disjoint_singleton.mpr (by decide))
    (compProd_Ioc_prod_singleton_lt_top κ true 0)
    (compProd_Ioc_prod_singleton_lt_top κ false 0)
  have hunion : ({true} ∪ {false} : Set Bool) = univ := by ext b; cases b <;> simp
  filter_upwards [hproj, hadd] with ω hω hωadd t
  have hground : M ω (Ioc 0 t ×ˢ univ) = N ω (Ioc 0 t) := by
    rw [← hω, Measure.map_apply measurable_fst measurableSet_Ioc, ← prod_univ]
  simpa only [hunion, hground] using hωadd t

/-- The complete temporal count paths of the two colour projections of a binary independent
marking of `N` are independent. -/
theorem indepFun_nat_count_of_map_prod_eq_marking [IsLocallyFiniteMeasure Λ]
    [IsMarkovKernel κ] (h : IsPoissonRandomMeasure P N Λ) (hM : Measurable M)
    (hjoint : P.map (fun ω => (N ω, M ω)) = (P.map N) ⊗ₘ κ.marking) :
    IndepFun (fun ω (t : ℝ≥0) => ⌊(M ω (Ioc 0 t ×ˢ {true})).toNNReal⌋₊)
      (fun ω (t : ℝ≥0) => ⌊(M ω (Ioc 0 t ×ˢ {false})).toNNReal⌋₊) P :=
  (h.of_map_prod_eq_compProd_marking hM hjoint).1.indepFun_nat_count_prod_singleton_bool

/-- Each colour count process of a binary independent marking of `N` has independent
increments. -/
theorem hasIndepIncrements_nat_count_of_map_prod_eq_marking [IsLocallyFiniteMeasure Λ]
    [IsMarkovKernel κ] (h : IsPoissonRandomMeasure P N Λ) (hM : Measurable M)
    (hjoint : P.map (fun ω => (N ω, M ω)) = (P.map N) ⊗ₘ κ.marking) (b : Bool) :
    HasIndepIncrements (fun t ω => ⌊(M ω (Ioc 0 t ×ˢ {b})).toNNReal⌋₊) P := by
  have hPM := (h.of_map_prod_eq_compProd_marking hM hjoint).1
  exact hPM.hasIndepIncrements_nat_count_prod_of_measure_Ioc_prod_lt_top
    (measurableSet_singleton b) (compProd_Ioc_prod_singleton_lt_top κ b 0)

/-- Each colour interval count has Poisson law with parameter `∫⁻ x in Ioc s t, κ x {b} ∂Λ`,
including empty intervals and atomic intensities. -/
theorem hasLaw_nat_count_Ioc_of_map_prod_eq_marking [IsLocallyFiniteMeasure Λ]
    [IsMarkovKernel κ] (h : IsPoissonRandomMeasure P N Λ) (hM : Measurable M)
    (hjoint : P.map (fun ω => (N ω, M ω)) = (P.map N) ⊗ₘ κ.marking)
    (b : Bool) (s t : ℝ≥0) :
    HasLaw (fun ω => ⌊(M ω (Ioc s t ×ˢ {b})).toNNReal⌋₊)
      (poissonMeasure (∫⁻ x in Ioc s t, κ x {b} ∂Λ).toNNReal) P := by
  have hPM := (h.of_map_prod_eq_compProd_marking hM hjoint).1
  simpa only [Measure.compProd_apply_prod measurableSet_Ioc (measurableSet_singleton b)] using
    hPM.hasLaw_nat_count_prod_Ioc_of_lt_top (measurableSet_singleton b) s t
      (compProd_Ioc_prod_singleton_lt_top κ b s t)

/-- Each colour count increment over `(s, t]` has Poisson law with parameter
`∫⁻ x in Ioc s t, κ x {b} ∂Λ`. -/
theorem hasLaw_nat_count_sub_of_map_prod_eq_marking [IsLocallyFiniteMeasure Λ]
    [IsMarkovKernel κ] (h : IsPoissonRandomMeasure P N Λ) (hM : Measurable M)
    (hjoint : P.map (fun ω => (N ω, M ω)) = (P.map N) ⊗ₘ κ.marking)
    (b : Bool) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω => ⌊(M ω (Ioc 0 t ×ˢ {b})).toNNReal⌋₊ -
      ⌊(M ω (Ioc 0 s ×ˢ {b})).toNNReal⌋₊)
      (poissonMeasure (∫⁻ x in Ioc s t, κ x {b} ∂Λ).toNNReal) P := by
  have hPM := (h.of_map_prod_eq_compProd_marking hM hjoint).1
  simpa only [Measure.compProd_apply_prod measurableSet_Ioc (measurableSet_singleton b)] using
    hPM.hasLaw_nat_count_prod_sub_of_measure_Ioc_prod_lt_top (measurableSet_singleton b) hst
      (compProd_Ioc_prod_singleton_lt_top κ b 0 t)

end CoupledBinary

section BernoulliCoupled

variable {M : Ω → Measure (ℝ≥0 × Bool)}

/-- Independent constant Bernoulli marking of a temporal Poisson random measure of locally finite
intensity `Λ` gives a marked Poisson random measure of product intensity
`Λ.prod (bernoulliMeasure true false p)`. -/
theorem isPoissonRandomMeasure_of_map_prod_eq_bernoulli_marking [IsLocallyFiniteMeasure Λ]
    (h : IsPoissonRandomMeasure P N Λ) {p : unitInterval} (hM : Measurable M)
    (hjoint : P.map (fun ω => (N ω, M ω)) =
      (P.map N) ⊗ₘ (Kernel.const ℝ≥0 (bernoulliMeasure true false p)).marking) :
    IsPoissonRandomMeasure P M (Λ.prod (bernoulliMeasure true false p)) := by
  simpa only [Measure.compProd_const] using
    (h.of_map_prod_eq_compProd_marking hM hjoint).1

/-- Each colour projection of an independent constant Bernoulli marking of `N` is a Poisson
random measure with intensity scaled by `p` or `1 - p`, including `p = 0` and `p = 1`. -/
theorem isPoissonRandomMeasure_thinned_of_map_prod_eq_bernoulli_marking [IsLocallyFiniteMeasure Λ]
    (h : IsPoissonRandomMeasure P N Λ) {p : unitInterval} (hM : Measurable M)
    (hjoint : P.map (fun ω => (N ω, M ω)) =
      (P.map N) ⊗ₘ (Kernel.const ℝ≥0 (bernoulliMeasure true false p)).marking) (b : Bool) :
    IsPoissonRandomMeasure P (fun ω => ((M ω).restrict (univ ×ˢ {b})).map Prod.fst)
      (((if b then unitInterval.toNNReal p else
        1 - unitInterval.toNNReal p : ℝ≥0) : ℝ≥0∞) • Λ) :=
  (h.isPoissonRandomMeasure_of_map_prod_eq_bernoulli_marking hM
    hjoint).acceptance_univ_prod_singleton_of_bernoulliMeasure b

/-- For homogeneous ground rate `r : ℝ≥0` (including `r = 0`) and retention probability
`p : unitInterval` (including `p = 0, 1`), each thinned count increment has Poisson law with
parameter `r * p * (t - s)` or `r * (1 - p) * (t - s)`. -/
theorem hasLaw_nat_count_sub_of_map_prod_eq_bernoulli_marking_smul_nnvolume {r : ℝ≥0}
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) {p : unitInterval}
    (hM : Measurable M)
    (hjoint : P.map (fun ω => (N ω, M ω)) =
      (P.map N) ⊗ₘ (Kernel.const ℝ≥0 (bernoulliMeasure true false p)).marking)
    (b : Bool) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω => ⌊(M ω (Ioc 0 t ×ˢ {b})).toNNReal⌋₊ -
      ⌊(M ω (Ioc 0 s ×ˢ {b})).toNNReal⌋₊)
      (poissonMeasure ((r * if b then unitInterval.toNNReal p else
        1 - unitInterval.toNNReal p) * (t - s))) P := by
  have : IsLocallyFiniteMeasure ((r : ℝ≥0∞) • nnvolume) :=
    nnvolume.isLocallyFiniteMeasure_smul ENNReal.coe_ne_top
  exact (h.isPoissonRandomMeasure_of_map_prod_eq_bernoulli_marking hM
    hjoint).hasLaw_nat_count_prod_singleton_sub_of_bernoulliMeasure b hst

/-- Boundary case `p = 0`: the accepted component vanishes almost surely and the rejected
component equals `N` almost surely. -/
theorem ae_thinned_of_p_eq_zero [IsLocallyFiniteMeasure Λ]
    (h : IsPoissonRandomMeasure P N Λ) (hM : Measurable M)
    (hjoint : P.map (fun ω => (N ω, M ω)) =
      (P.map N) ⊗ₘ (Kernel.const ℝ≥0 (bernoulliMeasure true false 0)).marking) :
    (∀ᵐ ω ∂P, ((M ω).restrict (univ ×ˢ {true})).map Prod.fst = 0) ∧
    (∀ᵐ ω ∂P, ((M ω).restrict (univ ×ˢ {false})).map Prod.fst = N ω) := by
  have htrue := h.isPoissonRandomMeasure_thinned_of_map_prod_eq_bernoulli_marking hM hjoint true
  have hzero : ∀ᵐ ω ∂P, ((M ω).restrict (univ ×ˢ {true})).map Prod.fst = 0 :=
    (htrue.ae_eq_zero (A := univ) (by simp)).mono fun _ hω =>
      Measure.measure_univ_eq_zero.mp hω
  refine ⟨hzero, ?_⟩
  filter_upwards [hzero, h.ae_map_fst_restrict_add_of_map_prod_eq_marking hM hjoint] with ω hz hsum
  simpa only [hz, zero_add] using hsum

/-- Boundary case `p = 1`: the rejected component vanishes almost surely and the accepted
component equals `N` almost surely. -/
theorem ae_thinned_of_p_eq_one [IsLocallyFiniteMeasure Λ]
    (h : IsPoissonRandomMeasure P N Λ) (hM : Measurable M)
    (hjoint : P.map (fun ω => (N ω, M ω)) =
      (P.map N) ⊗ₘ (Kernel.const ℝ≥0 (bernoulliMeasure true false 1)).marking) :
    (∀ᵐ ω ∂P, ((M ω).restrict (univ ×ˢ {false})).map Prod.fst = 0) ∧
    (∀ᵐ ω ∂P, ((M ω).restrict (univ ×ˢ {true})).map Prod.fst = N ω) := by
  have hfalse := h.isPoissonRandomMeasure_thinned_of_map_prod_eq_bernoulli_marking hM hjoint false
  have hzero : ∀ᵐ ω ∂P, ((M ω).restrict (univ ×ˢ {false})).map Prod.fst = 0 :=
    (hfalse.ae_eq_zero (A := univ) (by simp)).mono fun _ hω =>
      Measure.measure_univ_eq_zero.mp hω
  refine ⟨hzero, ?_⟩
  filter_upwards [hzero, h.ae_map_fst_restrict_add_of_map_prod_eq_marking hM hjoint] with ω hz hsum
  simpa only [hz, add_zero] using hsum

/-- Zero-rate thinning boundary case: whenever the effective rate of colour `b` vanishes
(covering `r = 0`, `b = true` with `p = 0`, and `b = false` with `p = 1`), the thinned measure
is zero almost surely and its cumulative count path is identically zero simultaneously at all
times. -/
theorem ae_thinned_eq_zero_of_rate_eq_zero {r : ℝ≥0}
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) {p : unitInterval}
    (hM : Measurable M)
    (hjoint : P.map (fun ω => (N ω, M ω)) =
      (P.map N) ⊗ₘ (Kernel.const ℝ≥0 (bernoulliMeasure true false p)).marking)
    (b : Bool)
    (hzero : r * (if b then unitInterval.toNNReal p else 1 - unitInterval.toNNReal p) = 0) :
    (∀ᵐ ω ∂P, ((M ω).restrict (univ ×ˢ {b})).map Prod.fst = 0) ∧
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0, ⌊(M ω (Ioc 0 t ×ˢ {b})).toNNReal⌋₊ = 0) := by
  have : IsLocallyFiniteMeasure ((r : ℝ≥0∞) • nnvolume) :=
    nnvolume.isLocallyFiniteMeasure_smul ENNReal.coe_ne_top
  have hPM := h.isPoissonRandomMeasure_of_map_prod_eq_bernoulli_marking hM hjoint
  have hb := hPM.acceptance_univ_prod_singleton_smul_of_bernoulliMeasure b
  have hmeas : ∀ᵐ ω ∂P, ((M ω).restrict (univ ×ˢ {b})).map Prod.fst = 0 :=
    (hb.ae_eq_zero (A := univ) (by simp [hzero])).mono fun _ hω =>
      Measure.measure_univ_eq_zero.mp hω
  refine ⟨hmeas, ?_⟩
  filter_upwards [hmeas] with ω hω t
  have h0 : M ω (Ioc 0 t ×ˢ {b}) = 0 := by
    have := congrArg (fun μ : Measure ℝ≥0 => μ (Ioc 0 t)) hω
    simpa only [Measure.map_fst_restrict_prod_apply _ _ _ measurableSet_Ioc, inter_univ,
      FunLike.coe_zero, Pi.zero_apply] using this
  simp [h0]

end BernoulliCoupled

section Existential

/-- **Independent time-dependent thinning of an uncoloured temporal Poisson random measure.**
Any Poisson random measure `N` on `ℝ≥0` with locally finite intensity `Λ` admits a
measure-preserving extension carrying two independent thinned Poisson random measures with
intensities `Λ.withDensity p` and `Λ.withDensity (1 - p)`, independent complete natural count
paths, almost-sure measure additivity, and simultaneous natural count-path additivity at all
times `t : ℝ≥0`. Endpoint values `0` and `1` and atomic intensities are allowed. -/
theorem exists_independent_temporal_thinning [IsLocallyFiniteMeasure Λ]
    (h : IsPoissonRandomMeasure P N Λ) {p : ℝ≥0 → unitInterval} (hp : Measurable p) :
    ∃ P' : Measure (Ω × Measure (ℝ≥0 × Bool)),
      MeasurePreserving Prod.fst P' P ∧
      IndepFun (fun q => (q.2.restrict (univ ×ˢ {true})).map Prod.fst)
        (fun q => (q.2.restrict (univ ×ˢ {false})).map Prod.fst) P' ∧
      IndepFun (fun q (t : ℝ≥0) => ⌊(q.2 (Ioc 0 t ×ˢ {true})).toNNReal⌋₊)
        (fun q (t : ℝ≥0) => ⌊(q.2 (Ioc 0 t ×ˢ {false})).toNNReal⌋₊) P' ∧
      IsPoissonRandomMeasure P' (fun q => (q.2.restrict (univ ×ˢ {true})).map Prod.fst)
        (Λ.withDensity fun x => (unitInterval.toNNReal (p x) : ℝ≥0∞)) ∧
      IsPoissonRandomMeasure P' (fun q => (q.2.restrict (univ ×ˢ {false})).map Prod.fst)
        (Λ.withDensity fun x => (unitInterval.toNNReal (unitInterval.symm (p x)) : ℝ≥0∞)) ∧
      (∀ᵐ q ∂P',
        ((q.2.restrict (univ ×ˢ {true})).map Prod.fst) +
          ((q.2.restrict (univ ×ˢ {false})).map Prod.fst) = N q.1) ∧
      (∀ᵐ q ∂P', ∀ t : ℝ≥0,
        ⌊(N q.1 (Ioc 0 t)).toNNReal⌋₊ =
          ⌊(q.2 (Ioc 0 t ×ˢ {true})).toNNReal⌋₊ +
            ⌊(q.2 (Ioc 0 t ×ˢ {false})).toNNReal⌋₊) := by
  let := h.isProbabilityMeasure
  let κ : Kernel ℝ≥0 Bool := Kernel.bernoulli true false hp
  let P' : Measure (Ω × Measure (ℝ≥0 × Bool)) := P ⊗ₘ (κ.marking.comap N h.measurable)
  have hmp : MeasurePreserving Prod.fst P' P :=
    ⟨measurable_fst, Measure.fst_compProd P (κ.marking.comap N h.measurable)⟩
  have hN' : IsPoissonRandomMeasure P' (N ∘ Prod.fst) Λ :=
    h.of_identDistrib (h.measurable.comp measurable_fst)
      ⟨h.measurable.aemeasurable, (h.measurable.comp measurable_fst).aemeasurable, by
        rw [← Measure.map_map h.measurable measurable_fst, hmp.map_eq]⟩
  have hjoint : P'.map (fun q => ((N ∘ Prod.fst) q, q.2)) =
      (P'.map (N ∘ Prod.fst)) ⊗ₘ κ.marking := h.map_prod_compProd_marking
  have hM : IsPoissonRandomMeasure P' Prod.snd (Λ ⊗ₘ κ) :=
    (hN'.of_map_prod_eq_compProd_marking measurable_snd hjoint).1
  have htrue : IsPoissonRandomMeasure P' (fun q => (q.2.restrict (univ ×ˢ {true})).map Prod.fst)
      (Λ.withDensity fun x => (unitInterval.toNNReal (p x) : ℝ≥0∞)) := by
    simpa [κ, Kernel.bernoulli_apply] using
      hM.acceptance_compProd_univ_prod (B := {true}) (measurableSet_singleton true)
  have hfalse : IsPoissonRandomMeasure P' (fun q => (q.2.restrict (univ ×ˢ {false})).map Prod.fst)
      (Λ.withDensity fun x => (unitInterval.toNNReal (unitInterval.symm (p x)) : ℝ≥0∞)) := by
    simpa [κ, Kernel.bernoulli_apply] using
      hM.acceptance_compProd_univ_prod (B := {false}) (measurableSet_singleton false)
  exact ⟨P', hmp,
    hM.indepFun_map_fst_restrict_univ_prod (measurableSet_singleton true)
      (measurableSet_singleton false) (disjoint_singleton.mpr (by decide)),
    hN'.indepFun_nat_count_of_map_prod_eq_marking measurable_snd hjoint,
    htrue, hfalse,
    hN'.ae_map_fst_restrict_add_of_map_prod_eq_marking measurable_snd hjoint,
    hN'.ae_nat_count_eq_add_of_map_prod_eq_marking measurable_snd hjoint⟩

/-- **Independent Bernoulli thinning of an uncoloured homogeneous temporal Poisson random
measure.** Any homogeneous Poisson random measure `N` on `ℝ≥0` of rate `r : ℝ≥0` (including
`r = 0`) and any retention probability `p : unitInterval` (including `p = 0, 1`) admit a
measure-preserving extension carrying two independent homogeneous Poisson random measures of
rates `r * p` and `r * (1 - p)` with independent complete count paths, almost-sure measure
additivity, and simultaneous natural count-path additivity at every time `t : ℝ≥0`. -/
theorem exists_independent_bernoulli_thinning_smul_nnvolume {r : ℝ≥0}
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (p : unitInterval) :
    ∃ P' : Measure (Ω × Measure (ℝ≥0 × Bool)),
      MeasurePreserving Prod.fst P' P ∧
      IndepFun (fun q => (q.2.restrict (univ ×ˢ {true})).map Prod.fst)
        (fun q => (q.2.restrict (univ ×ˢ {false})).map Prod.fst) P' ∧
      IndepFun (fun q (t : ℝ≥0) => ⌊(q.2 (Ioc 0 t ×ˢ {true})).toNNReal⌋₊)
        (fun q (t : ℝ≥0) => ⌊(q.2 (Ioc 0 t ×ˢ {false})).toNNReal⌋₊) P' ∧
      IsPoissonRandomMeasure P' (fun q => (q.2.restrict (univ ×ˢ {true})).map Prod.fst)
        (((r * unitInterval.toNNReal p : ℝ≥0) : ℝ≥0∞) • nnvolume) ∧
      IsPoissonRandomMeasure P' (fun q => (q.2.restrict (univ ×ˢ {false})).map Prod.fst)
        (((r * (1 - unitInterval.toNNReal p) : ℝ≥0) : ℝ≥0∞) • nnvolume) ∧
      (∀ᵐ q ∂P',
        ((q.2.restrict (univ ×ˢ {true})).map Prod.fst) +
          ((q.2.restrict (univ ×ˢ {false})).map Prod.fst) = N q.1) ∧
      (∀ᵐ q ∂P', ∀ t : ℝ≥0,
        ⌊(N q.1 (Ioc 0 t)).toNNReal⌋₊ =
          ⌊(q.2 (Ioc 0 t ×ˢ {true})).toNNReal⌋₊ +
            ⌊(q.2 (Ioc 0 t ×ˢ {false})).toNNReal⌋₊) := by
  have : IsLocallyFiniteMeasure ((r : ℝ≥0∞) • nnvolume) :=
    nnvolume.isLocallyFiniteMeasure_smul ENNReal.coe_ne_top
  obtain ⟨P', hmp, hind, hindc, htrue, hfalse, hadd, hcount⟩ :=
    h.exists_independent_temporal_thinning (p := fun _ => p) measurable_const
  have hsymm : unitInterval.toNNReal (unitInterval.symm p) = 1 - unitInterval.toNNReal p :=
    eq_tsub_of_add_eq (unitInterval.toNNReal_symm_add_toNNReal p)
  rw [withDensity_const, smul_smul, ← ENNReal.coe_mul, mul_comm] at htrue hfalse
  rw [hsymm] at hfalse
  exact ⟨P', hmp, hind, hindc, htrue, hfalse, hadd, hcount⟩

end Existential

end TauCeti.Probability.IsPoissonRandomMeasure
