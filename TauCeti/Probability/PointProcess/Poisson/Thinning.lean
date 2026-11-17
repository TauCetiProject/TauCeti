/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.Poisson.Marking
public import TauCeti.Probability.PointProcess.Poisson.Splitting
import Mathlib.Data.Bool.Set
import TauCeti.Topology.UnitInterval.NNReal

/-!
# Independent thinning of uncoloured temporal Poisson random measures

Given an uncoloured temporal Poisson random measure `N : Ω → Measure ℝ≥0` with locally finite
intensity `Λ`, independent marking by any Markov kernel `κ : Kernel ℝ≥0 E` produces a marked
Poisson random measure `M` on `ℝ≥0 × E` with intensity `Λ ⊗ₘ κ` whose ground projection recovers
`N` almost surely (and on `ℝ≥0`, canonical marking `κ.marking` agrees with independently marking
the ordered finite `Measure.occurrenceTime`s, see
`TauCeti.Probability.PointProcess.Marking.OccurrenceTime`).

This file connects the general marking and thinning results in `Poisson.Marking` with the temporal
count-splitting API in `Poisson.Splitting`:

* For any marked temporal Poisson random measure `M` whose ground projection equals `N` almost
  surely (in particular, any coupled pair `(N, M)` with joint law `(P.map N) ⊗ₘ κ.marking`), the
  cumulative natural count paths of a measurable mark set `B` and its complement `Bᶜ` add to the
  ground count path of `N` simultaneously at all times `t : ℝ≥0` on a single full-measure event,
  and interval and increment counts have Poisson laws with parameter `∫⁻ x in Ioc s t, κ x B ∂Λ`.
* For constant Bernoulli marks `Kernel.const ℝ≥0 (bernoulliMeasure true false p)` and scaled
  locally finite intensity `r • Λ` (in particular homogeneous `r • nnvolume`), whenever the
  effective rate `r * p` or `r * (1 - p)` vanishes, both the projected measure and its cumulative
  count path vanish simultaneously at all times almost surely.
* Existential theorems construct independent time-dependent, constant-`p`, and scaled-intensity
  Bernoulli thinnings on the canonical measure-preserving extension `Ω × Measure (ℝ≥0 × Bool)` of
  any uncoloured temporal Poisson random measure, combining the measure-level thinning bundle with
  independent complete natural count paths and simultaneous count-path additivity.

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

section CoupledTemporal

variable {E : Type*} [MeasurableSpace E] {κ : Kernel ℝ≥0 E} {M : Ω → Measure (ℝ≥0 × E)}

/-- For any marked temporal Poisson random measure `M` whose ground projection equals `N` almost
surely and whose intensity is finite on every bounded positive-time cylinder `Ioc 0 t ×ˢ univ`,
the cumulative natural count paths of a measurable mark set `B` and its complement `Bᶜ` add to the
ground count path of `N` simultaneously at every time `t : ℝ≥0` on a single full-measure event. -/
theorem ae_nat_count_eq_add_compl_of_ae_map_fst {Γ : Measure (ℝ≥0 × E)}
    (hM : IsPoissonRandomMeasure P M Γ) (hproj : ∀ᵐ ω ∂P, (M ω).map Prod.fst = N ω)
    {B : Set E} (hB : MeasurableSet B) (hfin : ∀ t : ℝ≥0, Γ (Ioc 0 t ×ˢ univ) < ∞) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ⌊(N ω (Ioc 0 t)).toNNReal⌋₊ =
        ⌊(M ω (Ioc 0 t ×ˢ B)).toNNReal⌋₊ +
          ⌊(M ω (Ioc 0 t ×ˢ Bᶜ)).toNNReal⌋₊ := by
  have hadd := hM.ae_nat_count_prod_union_eq_add_of_measure_Ioc_prod_lt_top hB hB.compl
    disjoint_compl_right
    (fun t => (measure_mono (prod_mono Subset.rfl (subset_univ _))).trans_lt (hfin t))
    (fun t => (measure_mono (prod_mono Subset.rfl (subset_univ _))).trans_lt (hfin t))
  filter_upwards [hproj, hadd] with ω hω hωadd t
  have hground : M ω (Ioc 0 t ×ˢ univ) = N ω (Ioc 0 t) := by
    rw [← hω, Measure.map_apply measurable_fst measurableSet_Ioc, ← prod_univ]
  simpa only [union_compl_self, hground] using hωadd t

/-- For any coupled marking `(N, M)` with joint law `(P.map N) ⊗ₘ κ.marking` and any measurable
mark set `B`, the cumulative natural count paths of `B` and `Bᶜ` add to the ground count path of
`N` simultaneously at every time `t : ℝ≥0` on a single full-measure event. -/
theorem ae_nat_count_eq_add_compl_of_map_prod_eq_compProd_marking [IsLocallyFiniteMeasure Λ]
    [IsMarkovKernel κ] (h : IsPoissonRandomMeasure P N Λ) (hM : Measurable M)
    (hjoint : P.map (fun ω => (N ω, M ω)) = (P.map N) ⊗ₘ κ.marking)
    {B : Set E} (hB : MeasurableSet B) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ⌊(N ω (Ioc 0 t)).toNNReal⌋₊ =
        ⌊(M ω (Ioc 0 t ×ˢ B)).toNNReal⌋₊ +
          ⌊(M ω (Ioc 0 t ×ˢ Bᶜ)).toNNReal⌋₊ := by
  obtain ⟨hPM, hproj⟩ := h.of_map_prod_eq_compProd_marking hM hjoint
  exact hPM.ae_nat_count_eq_add_compl_of_ae_map_fst hproj hB (Λ.compProd_Ioc_prod_lt_top κ univ 0)

/-- Each measurable mark-set interval count of a coupled marking `(N, M)` has Poisson law with
parameter `∫⁻ x in Ioc s t, κ x B ∂Λ`, including empty intervals and atomic intensities. -/
theorem hasLaw_nat_count_Ioc_of_map_prod_eq_compProd_marking [IsLocallyFiniteMeasure Λ]
    [IsMarkovKernel κ] (h : IsPoissonRandomMeasure P N Λ) (hM : Measurable M)
    (hjoint : P.map (fun ω => (N ω, M ω)) = (P.map N) ⊗ₘ κ.marking)
    {B : Set E} (hB : MeasurableSet B) (s t : ℝ≥0) :
    HasLaw (fun ω => ⌊(M ω (Ioc s t ×ˢ B)).toNNReal⌋₊)
      (poissonMeasure (∫⁻ x in Ioc s t, κ x B ∂Λ).toNNReal) P := by
  have hPM := (h.of_map_prod_eq_compProd_marking hM hjoint).1
  simpa only [Measure.compProd_apply_prod measurableSet_Ioc hB] using
    hPM.hasLaw_nat_count_prod_Ioc_of_lt_top hB s t (Λ.compProd_Ioc_prod_lt_top κ B s t)

/-- Each measurable mark-set count increment over `(s, t]` of a coupled marking `(N, M)` has
Poisson law with parameter `∫⁻ x in Ioc s t, κ x B ∂Λ`. -/
theorem hasLaw_nat_count_sub_of_map_prod_eq_compProd_marking [IsLocallyFiniteMeasure Λ]
    [IsMarkovKernel κ] (h : IsPoissonRandomMeasure P N Λ) (hM : Measurable M)
    (hjoint : P.map (fun ω => (N ω, M ω)) = (P.map N) ⊗ₘ κ.marking)
    {B : Set E} (hB : MeasurableSet B) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω => ⌊(M ω (Ioc 0 t ×ˢ B)).toNNReal⌋₊ -
      ⌊(M ω (Ioc 0 s ×ˢ B)).toNNReal⌋₊)
      (poissonMeasure (∫⁻ x in Ioc s t, κ x B ∂Λ).toNNReal) P := by
  have hPM := (h.of_map_prod_eq_compProd_marking hM hjoint).1
  simpa only [Measure.compProd_apply_prod measurableSet_Ioc hB] using
    hPM.hasLaw_nat_count_prod_sub_of_measure_Ioc_prod_lt_top hB hst
      (Λ.compProd_Ioc_prod_lt_top κ B 0 t)

end CoupledTemporal

section BernoulliBoundary

/-- Zero-rate constant-Bernoulli boundary case for any scaled locally finite intensity `r • Λ`
(in particular homogeneous `r • nnvolume`): whenever the effective rate of colour `b` vanishes
(covering `r = 0`, `b = true` with `p = 0`, and `b = false` with `p = 1`), the `b`-projection
vanishes almost surely and its cumulative count path is identically zero simultaneously at all
times. -/
theorem ae_map_fst_restrict_singleton_and_nat_count_eq_zero_of_const_bernoulliMeasure_smul
    [IsLocallyFiniteMeasure Λ] {r : ℝ≥0}
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • Λ)) {p : unitInterval}
    {M : Ω → Measure (ℝ≥0 × Bool)} (hM : Measurable M)
    (hjoint : P.map (fun ω => (N ω, M ω)) =
      (P.map N) ⊗ₘ (Kernel.const ℝ≥0 (bernoulliMeasure true false p)).marking)
    (b : Bool)
    (hzero : r * (if b then unitInterval.toNNReal p else 1 - unitInterval.toNNReal p) = 0) :
    (∀ᵐ ω ∂P, ((M ω).restrict (univ ×ˢ {b})).map Prod.fst = 0) ∧
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0, ⌊(M ω (Ioc 0 t ×ˢ {b})).toNNReal⌋₊ = 0) := by
  have : IsLocallyFiniteMeasure ((r : ℝ≥0∞) • Λ) :=
    Λ.isLocallyFiniteMeasure_smul ENNReal.coe_ne_top
  have hzero' : (r : ℝ≥0∞) *
      ((if b then unitInterval.toNNReal p else 1 - unitInterval.toNNReal p : ℝ≥0) : ℝ≥0∞) = 0 := by
    rw [← ENNReal.coe_mul, hzero, ENNReal.coe_zero]
  have hmeas : ∀ᵐ ω ∂P, ((M ω).restrict (univ ×ˢ {b})).map Prod.fst = 0 :=
    (h.ae_map_fst_restrict_singleton_eq_zero_and_not_eq_of_const_bernoulliMeasure hM hjoint b
      (by rw [smul_apply, smul_eq_mul, mul_right_comm, hzero', zero_mul])).1
  have hPM := (h.of_map_prod_eq_compProd_marking_const hM hjoint).1
  refine ⟨hmeas, hPM.ae_nat_count_prod_eq_zero_of_smul_prod_of_mul_eq_zero ?_⟩
  rw [← Kernel.bernoulli_apply (X := Unit) true false (p := fun _ => p) measurable_const (),
    Kernel.bernoulli_apply_singleton_bool, apply_ite unitInterval.toNNReal,
    unitInterval.toNNReal_symm, hzero']

end BernoulliBoundary

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
  have hM : IsPoissonRandomMeasure P' Prod.snd (Λ ⊗ₘ κ) :=
    h.isPoissonRandomMeasure_compProd_marking
  have hproj : ∀ᵐ q ∂P', q.2.map Prod.fst = N q.1 :=
    h.ae_map_fst_compProd_marking
  obtain ⟨hind, htrue, hfalse, hadd⟩ :=
    hM.indepFun_and_isPoissonRandomMeasure_of_compProd_bernoulli hproj
  have hcount : ∀ᵐ q ∂P', ∀ t : ℝ≥0,
      ⌊(N q.1 (Ioc 0 t)).toNNReal⌋₊ =
        ⌊(q.2 (Ioc 0 t ×ˢ {true})).toNNReal⌋₊ +
          ⌊(q.2 (Ioc 0 t ×ˢ {false})).toNNReal⌋₊ := by
    simpa only [Bool.compl_singleton, Bool.not_true] using
      hM.ae_nat_count_eq_add_compl_of_ae_map_fst hproj (measurableSet_singleton true)
        (Λ.compProd_Ioc_prod_lt_top κ univ 0)
  exact ⟨P', hmp, hind, hM.indepFun_nat_count_prod_singleton_bool, htrue, hfalse, hadd, hcount⟩

/-- **Independent constant `p`-thinning of an uncoloured temporal Poisson random measure.**
Any Poisson random measure `N` on `ℝ≥0` with locally finite intensity `Λ` and any retention
probability `p : unitInterval` (including `p = 0, 1`) admit a measure-preserving extension
carrying two independent Poisson random measures with intensities `p • Λ` and `(1 - p) • Λ`,
independent complete count paths, almost-sure measure additivity, and simultaneous natural
count-path additivity at every time `t : ℝ≥0`. -/
theorem exists_independent_temporal_thinning_const [IsLocallyFiniteMeasure Λ]
    (h : IsPoissonRandomMeasure P N Λ) (p : unitInterval) :
    ∃ P' : Measure (Ω × Measure (ℝ≥0 × Bool)),
      MeasurePreserving Prod.fst P' P ∧
      IndepFun (fun q => (q.2.restrict (univ ×ˢ {true})).map Prod.fst)
        (fun q => (q.2.restrict (univ ×ˢ {false})).map Prod.fst) P' ∧
      IndepFun (fun q (t : ℝ≥0) => ⌊(q.2 (Ioc 0 t ×ˢ {true})).toNNReal⌋₊)
        (fun q (t : ℝ≥0) => ⌊(q.2 (Ioc 0 t ×ˢ {false})).toNNReal⌋₊) P' ∧
      IsPoissonRandomMeasure P' (fun q => (q.2.restrict (univ ×ˢ {true})).map Prod.fst)
        ((unitInterval.toNNReal p : ℝ≥0∞) • Λ) ∧
      IsPoissonRandomMeasure P' (fun q => (q.2.restrict (univ ×ˢ {false})).map Prod.fst)
        (((1 - unitInterval.toNNReal p : ℝ≥0) : ℝ≥0∞) • Λ) ∧
      (∀ᵐ q ∂P',
        ((q.2.restrict (univ ×ˢ {true})).map Prod.fst) +
          ((q.2.restrict (univ ×ˢ {false})).map Prod.fst) = N q.1) ∧
      (∀ᵐ q ∂P', ∀ t : ℝ≥0,
        ⌊(N q.1 (Ioc 0 t)).toNNReal⌋₊ =
          ⌊(q.2 (Ioc 0 t ×ˢ {true})).toNNReal⌋₊ +
            ⌊(q.2 (Ioc 0 t ×ˢ {false})).toNNReal⌋₊) := by
  obtain ⟨P', hmp, hind, hindc, htrue, hfalse, hadd, hcount⟩ :=
    h.exists_independent_temporal_thinning (p := fun _ => p) measurable_const
  rw [withDensity_const] at htrue hfalse
  rw [unitInterval.toNNReal_symm] at hfalse
  exact ⟨P', hmp, hind, hindc, htrue, hfalse, hadd, hcount⟩

/-- **Independent constant `p`-thinning of a scaled temporal Poisson random measure.** Any Poisson
random measure `N` on `ℝ≥0` of intensity `r • Λ` with locally finite `Λ` (in particular
homogeneous `r • nnvolume`, including `r = 0`) and any retention probability `p : unitInterval`
(including `p = 0, 1`) admit a measure-preserving extension carrying two independent Poisson random
measures of intensities `(r * p) • Λ` and `(r * (1 - p)) • Λ` with independent complete count
paths, almost-sure measure additivity, and simultaneous natural count-path additivity at every
time `t : ℝ≥0`. -/
theorem exists_independent_temporal_thinning_smul [IsLocallyFiniteMeasure Λ] {r : ℝ≥0}
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • Λ)) (p : unitInterval) :
    ∃ P' : Measure (Ω × Measure (ℝ≥0 × Bool)),
      MeasurePreserving Prod.fst P' P ∧
      IndepFun (fun q => (q.2.restrict (univ ×ˢ {true})).map Prod.fst)
        (fun q => (q.2.restrict (univ ×ˢ {false})).map Prod.fst) P' ∧
      IndepFun (fun q (t : ℝ≥0) => ⌊(q.2 (Ioc 0 t ×ˢ {true})).toNNReal⌋₊)
        (fun q (t : ℝ≥0) => ⌊(q.2 (Ioc 0 t ×ˢ {false})).toNNReal⌋₊) P' ∧
      IsPoissonRandomMeasure P' (fun q => (q.2.restrict (univ ×ˢ {true})).map Prod.fst)
        (((r * unitInterval.toNNReal p : ℝ≥0) : ℝ≥0∞) • Λ) ∧
      IsPoissonRandomMeasure P' (fun q => (q.2.restrict (univ ×ˢ {false})).map Prod.fst)
        (((r * (1 - unitInterval.toNNReal p) : ℝ≥0) : ℝ≥0∞) • Λ) ∧
      (∀ᵐ q ∂P',
        ((q.2.restrict (univ ×ˢ {true})).map Prod.fst) +
          ((q.2.restrict (univ ×ˢ {false})).map Prod.fst) = N q.1) ∧
      (∀ᵐ q ∂P', ∀ t : ℝ≥0,
        ⌊(N q.1 (Ioc 0 t)).toNNReal⌋₊ =
          ⌊(q.2 (Ioc 0 t ×ˢ {true})).toNNReal⌋₊ +
            ⌊(q.2 (Ioc 0 t ×ˢ {false})).toNNReal⌋₊) := by
  have : IsLocallyFiniteMeasure ((r : ℝ≥0∞) • Λ) :=
    Λ.isLocallyFiniteMeasure_smul ENNReal.coe_ne_top
  obtain ⟨P', hmp, hind, hindc, htrue, hfalse, hadd, hcount⟩ :=
    h.exists_independent_temporal_thinning_const p
  rw [smul_smul, ← ENNReal.coe_mul, mul_comm] at htrue hfalse
  exact ⟨P', hmp, hind, hindc, htrue, hfalse, hadd, hcount⟩

end Existential

end TauCeti.Probability.IsPoissonRandomMeasure
