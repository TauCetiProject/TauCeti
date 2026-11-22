/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Bernoulli
public import TauCeti.MeasureTheory.Measure.NNReal
public import TauCeti.Probability.PointProcess.Poisson.Independence
public import TauCeti.Probability.PointProcess.Poisson.Marking
public import TauCeti.Probability.PointProcess.Poisson.Splitting
import Mathlib.Data.Bool.Set
import Mathlib.Probability.Independence.InfinitePi
import TauCeti.MeasureTheory.MeasurableSpace.Embedding
import TauCeti.MeasureTheory.Measure.Measurability
import TauCeti.MeasureTheory.Measure.Prod
import TauCeti.Probability.Distributions.Bernoulli.Measurability
import TauCeti.Probability.Independence.Map
import TauCeti.Probability.Kernel.Composition.MeasureCompProd
import TauCeti.Probability.PointProcess.Poisson.IntegerValued
import TauCeti.Topology.UnitInterval.NNReal

/-!
# Independent thinning of Poisson random measures and temporal processes

Selecting occurrences from a marked Poisson random measure on `X × E` according to disjoint
measurable subsets produces mutually independent random measures on `X`; for composition-product
intensities `Λ ⊗ₘ κ`, each projected slice is a Poisson random measure whose intensity weights `Λ`
by the corresponding section masses. Combining this splitting mechanism with the Poisson Marking
Theorem yields independent thinning of an uncoloured Poisson random measure `N` on a standard
Borel space:

* For a Markov kernel `κ : Kernel X ι` into a countable discrete colour space `ι`, marking
  occurrences of `N` with `κ` and projecting each singleton colour slice produces a
  realization-level Markov kernel `η : Kernel (Measure X) (ι → Measure X)` whose output coordinates
  under `P ⊗ₘ η.comap N hN.measurable` are mutually independent Poisson random measures with
  intensities `Λ.withDensity (fun x ↦ κ x {i})` that superpose to `N` almost surely
  (`IsPoissonRandomMeasure.exists_categorical_thinning`).
* Specializing to `ι = Bool` and `Ber(true, false, p x)` yields location-dependent `p`-thinning
  (`IsPoissonRandomMeasure.exists_bernoulli_thinning_of_measurable`) and constant-probability
  Bernoulli thinning (`IsPoissonRandomMeasure.exists_bernoulli_thinning`), including `p = 0, 1` and
  zero ground intensity `Λ = 0`, as well as homogeneous temporal thinning
  (`IsPoissonRandomMeasure.exists_bernoulli_thinning_smul_nnvolume`).
* Connecting the general marking and thinning results in `Poisson.Marking` with the temporal
  count-splitting API in `Poisson.Splitting` yields simultaneous count-path additivity,
  interval and increment Poisson count laws, zero-rate boundary vanishing, and existential
  temporal thinning bundles (`exists_independent_temporal_thinning`,
  `exists_independent_temporal_thinning_const`, `exists_independent_temporal_thinning_smul`)
  carrying independent complete natural count paths and simultaneous all-time count-path
  additivity.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Chapter 5 (Corollaries 5.8–5.9, independent thinning) and Chapter 7 (Poisson processes on
  the half-line).
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

/-- For any marked temporal Poisson random measure `M` of composition-product intensity `Λ ⊗ₘ κ`
with locally finite `Λ` and finite kernel `κ` whose ground projection equals `N` almost surely,
the cumulative natural count paths of a measurable mark set `B` and its complement `Bᶜ` add to the
ground count path of `N` simultaneously at every time `t : ℝ≥0` on a single full-measure event. -/
theorem ae_nat_count_eq_add_compl_of_compProd [IsLocallyFiniteMeasure Λ] [IsFiniteKernel κ]
    (hM : IsPoissonRandomMeasure P M (Λ ⊗ₘ κ)) (hproj : ∀ᵐ ω ∂P, (M ω).map Prod.fst = N ω)
    {B : Set E} (hB : MeasurableSet B) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ⌊(N ω (Ioc 0 t)).toNNReal⌋₊ =
        ⌊(M ω (Ioc 0 t ×ˢ B)).toNNReal⌋₊ +
          ⌊(M ω (Ioc 0 t ×ˢ Bᶜ)).toNNReal⌋₊ :=
  hM.ae_nat_count_eq_add_compl_of_ae_map_fst hproj hB (Λ.compProd_Ioc_prod_lt_top κ univ 0)

/-- Each measurable mark-set interval count of a temporal Poisson random measure with
composition-product intensity `Λ ⊗ₘ κ` has Poisson law with parameter `∫⁻ x in Ioc s t, κ x B ∂Λ`,
including empty intervals and atomic intensities. -/
theorem hasLaw_nat_count_Ioc_of_compProd [IsLocallyFiniteMeasure Λ] [IsFiniteKernel κ]
    (hM : IsPoissonRandomMeasure P M (Λ ⊗ₘ κ)) {B : Set E} (hB : MeasurableSet B) (s t : ℝ≥0) :
    HasLaw (fun ω => ⌊(M ω (Ioc s t ×ˢ B)).toNNReal⌋₊)
      (poissonMeasure (∫⁻ x in Ioc s t, κ x B ∂Λ).toNNReal) P := by
  simpa only [Measure.compProd_apply_prod measurableSet_Ioc hB] using
    hM.hasLaw_nat_count_prod_Ioc_of_lt_top hB s t (Λ.compProd_Ioc_prod_lt_top κ B s t)

/-- Each measurable mark-set count increment over `(s, t]` of a temporal Poisson random measure
with composition-product intensity `Λ ⊗ₘ κ` has Poisson law with parameter
`∫⁻ x in Ioc s t, κ x B ∂Λ`. -/
theorem hasLaw_nat_count_sub_of_compProd [IsLocallyFiniteMeasure Λ] [IsFiniteKernel κ]
    (hM : IsPoissonRandomMeasure P M (Λ ⊗ₘ κ)) {B : Set E} (hB : MeasurableSet B)
    {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω => ⌊(M ω (Ioc 0 t ×ˢ B)).toNNReal⌋₊ -
      ⌊(M ω (Ioc 0 s ×ˢ B)).toNNReal⌋₊)
      (poissonMeasure (∫⁻ x in Ioc s t, κ x B ∂Λ).toNNReal) P := by
  simpa only [Measure.compProd_apply_prod measurableSet_Ioc hB] using
    hM.hasLaw_nat_count_prod_sub_of_measure_Ioc_prod_lt_top hB hst
      (Λ.compProd_Ioc_prod_lt_top κ B 0 t)

end CoupledTemporal

section BernoulliBoundary

/-- Zero-intensity boundary case for an arbitrary marked temporal Poisson random measure: whenever
the selected cylinder `univ ×ˢ B` has zero intensity, the `B`-projection vanishes almost surely and
its cumulative count path is identically zero simultaneously at all times. -/
theorem ae_map_fst_restrict_univ_prod_and_nat_count_eq_zero
    {E : Type*} [MeasurableSpace E] {Γ : Measure (ℝ≥0 × E)} {M : Ω → Measure (ℝ≥0 × E)}
    (hM : IsPoissonRandomMeasure P M Γ) {B : Set E} (hzero : Γ (univ ×ˢ B) = 0) :
    (∀ᵐ ω ∂P, ((M ω).restrict (univ ×ˢ B)).map Prod.fst = 0) ∧
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0, ⌊(M ω (Ioc 0 t ×ˢ B)).toNNReal⌋₊ = 0) :=
  ⟨hM.ae_map_fst_restrict_univ_prod_eq_zero hzero,
    hM.ae_nat_count_prod_eq_zero (measure_mono_null (prod_mono (subset_univ _) Subset.rfl) hzero)⟩

/-- Zero-rate constant-Bernoulli boundary case for any scaled intensity `r • Λ` (in particular
homogeneous `r • nnvolume`): whenever the effective rate of colour `b` vanishes (covering `r = 0`,
`b = true` with `p = 0`, and `b = false` with `p = 1`), the `b`-projection vanishes almost surely
and its cumulative count path is identically zero simultaneously at all times. -/
theorem ae_map_fst_restrict_singleton_and_nat_count_eq_zero_of_const_bernoulliMeasure_smul
    {r : ℝ≥0} {p : unitInterval} {M : Ω → Measure (ℝ≥0 × Bool)}
    (hM : IsPoissonRandomMeasure P M
      (((r : ℝ≥0∞) • Λ).prod (bernoulliMeasure true false p)))
    (b : Bool)
    (hzero : r * (if b then unitInterval.toNNReal p else 1 - unitInterval.toNNReal p) = 0) :
    (∀ᵐ ω ∂P, ((M ω).restrict (univ ×ˢ {b})).map Prod.fst = 0) ∧
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0, ⌊(M ω (Ioc 0 t ×ˢ {b})).toNNReal⌋₊ = 0) := by
  apply hM.ae_map_fst_restrict_univ_prod_and_nat_count_eq_zero
  rw [Measure.prod_prod, smul_apply, smul_eq_mul, bernoulliMeasure_apply_singleton_bool]
  rcases mul_eq_zero.mp hzero with h | h <;> simp [h]

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
  have hfin : ∀ n, Λ (compactCovering ℝ≥0 n) < ∞ :=
    fun n => (isCompact_compactCovering ℝ≥0 n).measure_lt_top
  have hM : IsPoissonRandomMeasure P' Prod.snd (Λ ⊗ₘ κ) :=
    h.isPoissonRandomMeasure_compProd_marking hfin
  have hproj : ∀ᵐ q ∂P', q.2.map Prod.fst = N q.1 :=
    h.ae_map_fst_compProd_marking hfin
  obtain ⟨hind, htrue, hfalse, hadd⟩ :=
    hM.indepFun_and_isPoissonRandomMeasure_of_compProd_bernoulli hproj
  have hcount : ∀ᵐ q ∂P', ∀ t : ℝ≥0,
      ⌊(N q.1 (Ioc 0 t)).toNNReal⌋₊ =
        ⌊(q.2 (Ioc 0 t ×ˢ {true})).toNNReal⌋₊ +
          ⌊(q.2 (Ioc 0 t ×ˢ {false})).toNNReal⌋₊ := by
    simpa only [Bool.compl_singleton, Bool.not_true] using
      hM.ae_nat_count_eq_add_compl_of_compProd hproj (measurableSet_singleton true)
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

namespace TauCeti.Probability

section CategoricalAndBernoulliThinning

private def sliceFamily {X ι : Type*} [MeasurableSpace X] [MeasurableSpace ι] :
    Measure (X × ι) → ι → Measure X :=
  fun μ i ↦ ((μ.restrict (univ ×ˢ {i})).map Prod.fst)

private theorem measurable_sliceFamily {X ι : Type*} [MeasurableSpace X] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] : Measurable (sliceFamily (X := X) (ι := ι)) :=
  measurable_pi_iff.2 fun i ↦
    (Measure.measurable_map _ measurable_fst).comp
      (Measure.measurable_restrict (MeasurableSet.univ.prod (measurableSet_singleton i)))

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [StandardBorelSpace X]
  {P : Measure Ω} {N : Ω → Measure X} {Λ : Measure X} [SigmaFinite Λ]

/-- **Countable categorical thinning of an uncoloured Poisson random measure** (Last–Penrose,
Corollary 5.9). Independently classifying occurrences of `N` with a Markov kernel
`κ : Kernel X ι` into a countable discrete colour space `ι` yields a realization-level Markov kernel
`η : Kernel (Measure X) (ι → Measure X)` whose colour components under
`P ⊗ₘ η.comap N hN.measurable` are mutually independent Poisson random measures with intensities
`Λ.withDensity (fun x ↦ κ x {i})` that superpose to `N` almost surely. -/
theorem IsPoissonRandomMeasure.exists_categorical_thinning {ι : Type*} [Countable ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (hN : IsPoissonRandomMeasure P N Λ) (κ : Kernel X ι) [IsMarkovKernel κ] :
    ∃ η : Kernel (Measure X) (ι → Measure X),
      IsMarkovKernel η ∧
      (∀ i, IsPoissonRandomMeasure (P ⊗ₘ η.comap N hN.measurable) (fun z ↦ z.2 i)
        (Λ.withDensity fun x ↦ κ x {i})) ∧
      ProbabilityTheory.iIndepFun (fun i z ↦ z.2 i) (P ⊗ₘ η.comap N hN.measurable) ∧
      ∀ᵐ z ∂(P ⊗ₘ η.comap N hN.measurable), Measure.sum z.2 = N z.1 := by
  let := hN.isProbabilityMeasure
  obtain ⟨η₀, _, hM₀, hproj⟩ := hN.exists_isMarkovKernel_marking κ
  have hη : IsMarkovKernel (η₀.map (sliceFamily (X := X) (ι := ι))) :=
    Kernel.IsMarkovKernel.map η₀ measurable_sliceFamily
  have hΦ : Measurable (Prod.map (id : Ω → Ω) (sliceFamily (X := X) (ι := ι))) :=
    measurable_id.prodMap measurable_sliceFamily
  have hmap :=
    Measure.compProd_comap_map P η₀ hN.measurable (measurable_sliceFamily (X := X) (ι := ι))
  have hslice (i : ι) := hM₀.map_fst_restrict_univ_prod_compProd (measurableSet_singleton i)
  have hind₀ := hM₀.iIndepFun_map_fst_restrict_univ_prod
    (fun i : ι ↦ measurableSet_singleton i) (fun _ _ hij ↦ Set.disjoint_singleton.mpr hij)
  have hcoord (i : ι) : Measurable (fun z : Ω × (ι → Measure X) ↦ z.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  -- Push the marked Poisson law, slice independence, and ground recovery forward via `hmap`.
  refine ⟨η₀.map sliceFamily, hη, fun i ↦ ?_, ?_, ?_⟩
  · refine (hslice i).of_identDistrib (hcoord i)
      ⟨(hslice i).measurable.aemeasurable, (hcoord i).aemeasurable, ?_⟩
    rw [hmap, Measure.map_map (hcoord i) hΦ]
    simp only [Function.comp_def, Prod.map_snd, sliceFamily]
  · refine (iIndepFun_iff_map_fun_eq_infinitePi_map hcoord).2 ?_
    rw [hmap, Measure.map_map (measurable_pi_iff.2 hcoord) hΦ]
    simp_rw [Measure.map_map (hcoord _) hΦ]
    exact hind₀.map_fun_eq_infinitePi_map fun i ↦ (hslice i).measurable
  · refine (hN.compProd_fst _).ae_eq_of_forall_ae_eq fun A hA ↦ ?_
    have hEA : MeasurableSet {z : Ω × (ι → Measure X) | Measure.sum z.2 A = N z.1 A} :=
      measurableSet_eq_fun
        ((Measure.measurable_coe hA).comp (Measure.measurable_sum.comp measurable_snd))
        ((Measure.measurable_coe hA).comp (hN.measurable.comp measurable_fst))
    rw [hmap]
    refine (ae_map_iff hΦ.aemeasurable hEA).2 ?_
    filter_upwards [hproj] with w hw
    dsimp only [Prod.map_fst, Prod.map_snd, id_eq]
    unfold sliceFamily
    rw [Measure.sum_map_fst_restrict_univ_prod_singleton, hw]

/-- Homogeneous categorical thinning specialization of
`IsPoissonRandomMeasure.exists_categorical_thinning` for a fixed colour distribution `Q`: each
colour `i` receives intensity `(Q {i}) • Λ`. -/
theorem IsPoissonRandomMeasure.exists_categorical_thinning_const {ι : Type*} [Countable ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (hN : IsPoissonRandomMeasure P N Λ) (Q : Measure ι) [IsProbabilityMeasure Q] :
    ∃ η : Kernel (Measure X) (ι → Measure X),
      IsMarkovKernel η ∧
      (∀ i, IsPoissonRandomMeasure (P ⊗ₘ η.comap N hN.measurable) (fun z ↦ z.2 i) (Q {i} • Λ)) ∧
      ProbabilityTheory.iIndepFun (fun i z ↦ z.2 i) (P ⊗ₘ η.comap N hN.measurable) ∧
      ∀ᵐ z ∂(P ⊗ₘ η.comap N hN.measurable), Measure.sum z.2 = N z.1 := by
  obtain ⟨η, hη, hP, hind, hsum⟩ := hN.exists_categorical_thinning (Kernel.const X Q)
  simp only [Kernel.const_apply, withDensity_const] at hP
  exact ⟨η, hη, hP, hind, hsum⟩

/-- Binary specialization of `IsPoissonRandomMeasure.exists_categorical_thinning` transporting the
`Bool`-indexed output along `MeasurableEquiv.boolArrowEquivProd` into `(true, false)` order. -/
private theorem exists_bool_thinning
    (hN : IsPoissonRandomMeasure P N Λ) (κ : Kernel X Bool) [IsMarkovKernel κ] :
    ∃ η : Kernel (Measure X) (Measure X × Measure X),
      IsMarkovKernel η ∧
      IsPoissonRandomMeasure (P ⊗ₘ η.comap N hN.measurable) (fun z ↦ z.2.1)
        (Λ.withDensity fun x ↦ κ x {true}) ∧
      IsPoissonRandomMeasure (P ⊗ₘ η.comap N hN.measurable) (fun z ↦ z.2.2)
        (Λ.withDensity fun x ↦ κ x {false}) ∧
      IndepFun (fun z ↦ z.2.1) (fun z ↦ z.2.2) (P ⊗ₘ η.comap N hN.measurable) ∧
      ∀ᵐ z ∂(P ⊗ₘ η.comap N hN.measurable), z.2.1 + z.2.2 = N z.1 := by
  let := hN.isProbabilityMeasure
  obtain ⟨η₀, _, hP, hind, hsum⟩ := hN.exists_categorical_thinning κ
  let e := (MeasurableEquiv.boolArrowEquivProd (Measure X)).trans .prodComm
  let E := MeasurableEquiv.prodCongr (.refl Ω) e
  have hE_fst (w : Ω × (Bool → Measure X)) : (E w).1 = w.1 := by simp [E]
  have hE_snd_fst (w : Ω × (Bool → Measure X)) : (E w).2.1 = w.2 true := by simp [E, e]
  have hE_snd_snd (w : Ω × (Bool → Measure X)) : (E w).2.2 = w.2 false := by simp [E, e]
  -- Push the `Bool`-indexed thinning kernel forward to `Measure X × Measure X` via `e`.
  have hη : IsMarkovKernel (η₀.map e) := Kernel.IsMarkovKernel.map η₀ e.measurable
  have hmap : P ⊗ₘ (η₀.map e).comap N hN.measurable =
      (P ⊗ₘ η₀.comap N hN.measurable).map E := by
    simp only [E, MeasurableEquiv.coe_prodCongr, MeasurableEquiv.coe_refl,
      Measure.compProd_comap_map P η₀ hN.measurable e.measurable]
  refine ⟨η₀.map e, hη, ?_, ?_, ?_, ?_⟩
  -- Transfer the `true` and `false` Poisson laws, independence, and almost-sure sum along `E`.
  · refine (hP true).of_identDistrib measurable_snd.fst
      ⟨(hP true).measurable.aemeasurable, measurable_snd.fst.aemeasurable, ?_⟩
    rw [hmap, Measure.map_map measurable_snd.fst E.measurable]
    exact congrArg ((P ⊗ₘ η₀.comap N hN.measurable).map) (funext fun w ↦ (hE_snd_fst w).symm)
  · refine (hP false).of_identDistrib measurable_snd.snd
      ⟨(hP false).measurable.aemeasurable, measurable_snd.snd.aemeasurable, ?_⟩
    rw [hmap, Measure.map_map measurable_snd.snd E.measurable]
    exact congrArg ((P ⊗ₘ η₀.comap N hN.measurable).map) (funext fun w ↦ (hE_snd_snd w).symm)
  · rw [hmap, indepFun_map_iff_comp E.measurable.aemeasurable
      measurable_snd.fst.aemeasurable measurable_snd.snd.aemeasurable]
    have hc₁ : ((fun z : Ω × (Measure X × Measure X) ↦ z.2.1) ∘ E) = fun w ↦ w.2 true :=
      funext hE_snd_fst
    have hc₂ : ((fun z : Ω × (Measure X × Measure X) ↦ z.2.2) ∘ E) = fun w ↦ w.2 false :=
      funext hE_snd_snd
    rw [hc₁, hc₂]
    exact hind.indepFun (i := true) (j := false) (by decide)
  · rw [hmap, E.measurableEmbedding.ae_map_iff]
    filter_upwards [hsum] with w hw
    rw [hE_snd_fst, hE_snd_snd, hE_fst, ← Measure.sum_bool]
    exact hw

/-- **Independent `p`-thinning of an uncoloured Poisson random measure** (Last–Penrose,
Corollary 5.8). For a measurable retention probability `p : X → unitInterval`, independently
marking occurrences of `N` with `Ber(true, false, p x)` and splitting by the mark produces a
realization-level Markov kernel `η : Kernel (Measure X) (Measure X × Measure X)` whose two output
coordinates under `P ⊗ₘ η.comap N hN.measurable` are independent Poisson random measures with
intensities weighted by `p` and `1 - p` that sum to `N` almost surely. -/
theorem IsPoissonRandomMeasure.exists_bernoulli_thinning_of_measurable
    (hN : IsPoissonRandomMeasure P N Λ) {p : X → unitInterval} (hp : Measurable p) :
    ∃ η : Kernel (Measure X) (Measure X × Measure X),
      IsMarkovKernel η ∧
      IsPoissonRandomMeasure (P ⊗ₘ η.comap N hN.measurable) (fun z ↦ z.2.1)
        (Λ.withDensity fun x ↦ (unitInterval.toNNReal (p x) : ℝ≥0∞)) ∧
      IsPoissonRandomMeasure (P ⊗ₘ η.comap N hN.measurable) (fun z ↦ z.2.2)
        (Λ.withDensity fun x ↦ ((1 - unitInterval.toNNReal (p x) : ℝ≥0) : ℝ≥0∞)) ∧
      IndepFun (fun z ↦ z.2.1) (fun z ↦ z.2.2) (P ⊗ₘ η.comap N hN.measurable) ∧
      ∀ᵐ z ∂(P ⊗ₘ η.comap N hN.measurable), z.2.1 + z.2.2 = N z.1 := by
  obtain ⟨η, hη, h₁, h₂, hind, hadd⟩ := exists_bool_thinning hN (Kernel.bernoulli true false hp)
  have htrue : (fun x ↦ Kernel.bernoulli true false hp x {true}) =
      fun x ↦ (unitInterval.toNNReal (p x) : ℝ≥0∞) :=
    funext fun x ↦
      Kernel.bernoulli_apply_singleton_left (measurableSet_singleton true) (by decide) hp x
  have hfalse : (fun x ↦ Kernel.bernoulli true false hp x {false}) =
      fun x ↦ ((1 - unitInterval.toNNReal (p x) : ℝ≥0) : ℝ≥0∞) :=
    funext fun x ↦ by
      rw [Kernel.bernoulli_apply_singleton_right (measurableSet_singleton false) (by decide) hp x,
        unitInterval.toNNReal_symm]
  exact ⟨η, hη, htrue ▸ h₁, hfalse ▸ h₂, hind, hadd⟩

/-- **Constant-probability Bernoulli thinning of an uncoloured Poisson random measure**, including
the boundary probabilities `p = 0` and `p = 1` and zero ground intensity `Λ = 0`. -/
theorem IsPoissonRandomMeasure.exists_bernoulli_thinning
    (hN : IsPoissonRandomMeasure P N Λ) (p : unitInterval) :
    ∃ η : Kernel (Measure X) (Measure X × Measure X),
      IsMarkovKernel η ∧
      IsPoissonRandomMeasure (P ⊗ₘ η.comap N hN.measurable) (fun z ↦ z.2.1)
        ((unitInterval.toNNReal p : ℝ≥0∞) • Λ) ∧
      IsPoissonRandomMeasure (P ⊗ₘ η.comap N hN.measurable) (fun z ↦ z.2.2)
        (((1 - unitInterval.toNNReal p : ℝ≥0) : ℝ≥0∞) • Λ) ∧
      IndepFun (fun z ↦ z.2.1) (fun z ↦ z.2.2) (P ⊗ₘ η.comap N hN.measurable) ∧
      ∀ᵐ z ∂(P ⊗ₘ η.comap N hN.measurable), z.2.1 + z.2.2 = N z.1 := by
  obtain ⟨η, hη, h₁, h₂, hind, hadd⟩ :=
    hN.exists_bernoulli_thinning_of_measurable (measurable_const : Measurable fun _ : X ↦ p)
  simp only [withDensity_const] at h₁ h₂
  exact ⟨η, hη, h₁, h₂, hind, hadd⟩

end CategoricalAndBernoulliThinning

section Temporal

/-- **Bernoulli thinning of a homogeneous temporal Poisson process on `ℝ≥0`**, including boundary
probabilities `p = 0, 1` and zero rate `r = 0`. Thinning a Poisson random measure of rate `r` with
success probability `p` produces a realization-level Markov kernel
`η : Kernel (Measure ℝ≥0) (Measure ℝ≥0 × Measure ℝ≥0)` whose two outputs under
`P ⊗ₘ η.comap N hN.measurable` are independent homogeneous Poisson random measures of rates
`p * r` and `(1 - p) * r` that sum to `N` almost surely; combined with
`ProbabilityTheory.IndepFun.natFloor_toNNReal` and
`IsPoissonRandomMeasure.ae_forall_nat_count_add_eq`, their cumulative-count paths are independent
and add to the original count path simultaneously for all `t : ℝ≥0`. -/
theorem IsPoissonRandomMeasure.exists_bernoulli_thinning_smul_nnvolume {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {N : Ω → Measure ℝ≥0} {r : ℝ≥0}
    (hN : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (p : unitInterval) :
    ∃ η : Kernel (Measure ℝ≥0) (Measure ℝ≥0 × Measure ℝ≥0),
      IsMarkovKernel η ∧
      IsPoissonRandomMeasure (P ⊗ₘ η.comap N hN.measurable) (fun z ↦ z.2.1)
        (((unitInterval.toNNReal p * r : ℝ≥0) : ℝ≥0∞) • nnvolume) ∧
      IsPoissonRandomMeasure (P ⊗ₘ η.comap N hN.measurable) (fun z ↦ z.2.2)
        ((((1 - unitInterval.toNNReal p) * r : ℝ≥0) : ℝ≥0∞) • nnvolume) ∧
      IndepFun (fun z ↦ z.2.1) (fun z ↦ z.2.2) (P ⊗ₘ η.comap N hN.measurable) ∧
      ∀ᵐ z ∂(P ⊗ₘ η.comap N hN.measurable), z.2.1 + z.2.2 = N z.1 := by
  obtain ⟨η, hη, h₁, h₂, hind, hadd⟩ := hN.exists_bernoulli_thinning p
  rw [smul_smul, ← ENNReal.coe_mul] at h₁ h₂
  exact ⟨η, hη, h₁, h₂, hind, hadd⟩

end Temporal

end TauCeti.Probability
