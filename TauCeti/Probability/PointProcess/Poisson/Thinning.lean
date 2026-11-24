/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Bernoulli
public import TauCeti.MeasureTheory.Measure.NNReal
public import TauCeti.Probability.Distributions.Bernoulli.Measurability
public import TauCeti.Probability.PointProcess.Poisson.Independence
public import TauCeti.Probability.PointProcess.Poisson.Marking
public import TauCeti.Probability.PointProcess.Poisson.Splitting
import Mathlib.Probability.Independence.InfinitePi
import TauCeti.MeasureTheory.MeasurableSpace.Embedding
import TauCeti.MeasureTheory.Measure.Measurability
import TauCeti.MeasureTheory.Measure.Prod
import TauCeti.Probability.Distributions.Bernoulli.Basic
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
* On any sigma-compact Hausdorff standard Borel space with intensity finite on compact sets,
  canonical cover-free marking via `(Kernel.bernoulli true false hp).marking` yields explicit
  thinned Poisson slices (`IsPoissonRandomMeasure.acceptance_bernoulli_marking`) with almost-sure
  additivity (`IsPoissonRandomMeasure.ae_add_bernoulli_marking`) and boundary vanishing for
  `p = 0`, `p = 1`, and `Λ = 0`.
* On `ℝ≥0` with locally finite intensity `Λ`, canonical Bernoulli marking connects `Poisson.Marking`
  with `Poisson.Splitting` to give independent colour count paths with independent Poisson
  increments, interval and increment Poisson laws, simultaneous all-time count-path additivity, and
  boundary count-path vanishing (`p = 0`, `p = 1`, `Λ (Ioi 0) = 0`).

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Chapter 5 (Corollaries 5.8–5.9, independent thinning) and Chapter 7 (Poisson processes on
  the half-line).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

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
  simp only [Kernel.bernoulli_apply, bernoulliMeasure_apply_singleton_bool, ↓reduceIte] at h₁ h₂
  exact ⟨η, hη, h₁, h₂, hind, hadd⟩

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

section BernoulliMarking

variable {Ω X : Type*} [MeasurableSpace Ω]
  [TopologicalSpace X] [T2Space X] [SigmaCompactSpace X]
  [MeasurableSpace X] [OpensMeasurableSpace X] [StandardBorelSpace X]
  {P : Measure Ω} {N : Ω → Measure X} {Λ : Measure X} [IsFiniteMeasureOnCompacts Λ]

/-- Under canonical cover-free marking of `N` by `Kernel.bernoulli true false hp`, projecting
occurrences with colour `b` yields a Poisson random measure with intensity weighted by `p`
(for `true`) or `unitInterval.symm ∘ p` (for `false`). -/
theorem IsPoissonRandomMeasure.acceptance_bernoulli_marking
    (hN : IsPoissonRandomMeasure P N Λ) {p : X → unitInterval} (hp : Measurable p) (b : Bool) :
    IsPoissonRandomMeasure (P ⊗ₘ ((Kernel.bernoulli true false hp).marking.comap N hN.measurable))
      (fun z ↦ ((z.2).restrict (univ ×ˢ {b})).map Prod.fst)
      (Λ.withDensity fun x ↦
        (unitInterval.toNNReal (if b then p x else unitInterval.symm (p x)) : ℝ≥0∞)) :=
  (hN.compProd_marking (Kernel.bernoulli true false hp)).acceptance_compProd_bernoulli b

/-- Under canonical cover-free Bernoulli marking of `N`, the retained (`true`) and rejected
(`false`) projected measures sum to `N` almost surely. -/
theorem IsPoissonRandomMeasure.ae_add_bernoulli_marking
    (hN : IsPoissonRandomMeasure P N Λ) {p : X → unitInterval} (hp : Measurable p) :
    ∀ᵐ z ∂(P ⊗ₘ ((Kernel.bernoulli true false hp).marking.comap N hN.measurable)),
      ((z.2).restrict (univ ×ˢ {true})).map Prod.fst +
        ((z.2).restrict (univ ×ˢ {false})).map Prod.fst = N z.1 := by
  filter_upwards [hN.ae_map_fst_compProd_marking (Kernel.bernoulli true false hp)] with z hz
  rw [← hz, ← (z.2).sum_map_fst_restrict_univ_prod_singleton, Measure.sum_bool]

/-- **Boundary vanishing at `p = 0` almost everywhere.** If `p x = 0` for `Λ`-almost every `x`,
then under canonical Bernoulli marking, the retained (`true`) slice vanishes almost surely. -/
theorem IsPoissonRandomMeasure.ae_bernoulli_marking_true_eq_zero_of_ae_eq_zero
    (hN : IsPoissonRandomMeasure P N Λ) {p : X → unitInterval} (hp : Measurable p)
    (hp0 : ∀ᵐ x ∂Λ, p x = 0) :
    ∀ᵐ z ∂(P ⊗ₘ ((Kernel.bernoulli true false hp).marking.comap N hN.measurable)),
      ((z.2).restrict (univ ×ˢ {true})).map Prod.fst = 0 := by
  have hzero : (Λ ⊗ₘ Kernel.bernoulli true false hp) (univ ×ˢ {true}) = 0 := by
    rw [Measure.compProd_apply_prod MeasurableSet.univ (measurableSet_singleton true),
      setLIntegral_univ]
    simp only [Kernel.bernoulli_apply, bernoulliMeasure_apply_singleton_bool, ↓reduceIte]
    exact (lintegral_eq_zero_iff' (by fun_prop)).2 (hp0.mono fun x hx ↦ by simp [hx])
  exact (hN.compProd_marking (Kernel.bernoulli true false hp)).ae_map_fst_restrict_univ_prod_eq_zero
    hzero

/-- **Boundary vanishing at `p = 1` almost everywhere.** If `p x = 1` for `Λ`-almost every `x`,
then under canonical Bernoulli marking, the rejected (`false`) slice vanishes almost surely. -/
theorem IsPoissonRandomMeasure.ae_bernoulli_marking_false_eq_zero_of_ae_eq_one
    (hN : IsPoissonRandomMeasure P N Λ) {p : X → unitInterval} (hp : Measurable p)
    (hp1 : ∀ᵐ x ∂Λ, p x = 1) :
    ∀ᵐ z ∂(P ⊗ₘ ((Kernel.bernoulli true false hp).marking.comap N hN.measurable)),
      ((z.2).restrict (univ ×ˢ {false})).map Prod.fst = 0 := by
  have hzero : (Λ ⊗ₘ Kernel.bernoulli true false hp) (univ ×ˢ {false}) = 0 := by
    rw [Measure.compProd_apply_prod MeasurableSet.univ (measurableSet_singleton false),
      setLIntegral_univ]
    simp only [Kernel.bernoulli_apply, bernoulliMeasure_apply_singleton_bool, Bool.false_eq_true,
      ↓reduceIte]
    exact (lintegral_eq_zero_iff' (by fun_prop)).2 (hp1.mono fun x hx ↦ by simp [hx])
  exact (hN.compProd_marking (Kernel.bernoulli true false hp)).ae_map_fst_restrict_univ_prod_eq_zero
    hzero

/-- **Zero-intensity boundary vanishing.** Under canonical Bernoulli marking of a zero-intensity
Poisson random measure, both colour slices vanish almost surely. -/
theorem IsPoissonRandomMeasure.ae_bernoulli_marking_eq_zero_of_intensity_eq_zero
    (hN : IsPoissonRandomMeasure P N (0 : Measure X))
    {p : X → unitInterval} (hp : Measurable p) (b : Bool) :
    ∀ᵐ z ∂(P ⊗ₘ ((Kernel.bernoulli true false hp).marking.comap N hN.measurable)),
      ((z.2).restrict (univ ×ˢ {b})).map Prod.fst = 0 :=
  (hN.compProd_marking (Kernel.bernoulli true false hp)).ae_map_fst_restrict_univ_prod_eq_zero
    (by simp)

end BernoulliMarking

section Temporal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : Ω → Measure ℝ≥0}
  {Λ : Measure ℝ≥0} [IsLocallyFiniteMeasure Λ]

/-- Under canonical Bernoulli marking of a temporal Poisson random measure on `ℝ≥0`, the
`true` and `false` natural cumulative count paths are independent. -/
theorem IsPoissonRandomMeasure.indepFun_nat_count_bernoulli_marking
    (hN : IsPoissonRandomMeasure P N Λ) {p : ℝ≥0 → unitInterval} (hp : Measurable p) :
    IndepFun (fun z (t : ℝ≥0) ↦ ⌊(z.2 (Ioc 0 t ×ˢ {true})).toNNReal⌋₊)
      (fun z (t : ℝ≥0) ↦ ⌊(z.2 (Ioc 0 t ×ˢ {false})).toNNReal⌋₊)
      (P ⊗ₘ ((Kernel.bernoulli true false hp).marking.comap N hN.measurable)) :=
  (hN.compProd_marking (Kernel.bernoulli true false hp)).indepFun_nat_count_prod_singleton_bool

/-- Each colour count path of canonical temporal Bernoulli marking has independent increments
whenever the ground intensity `Λ` is locally finite. -/
theorem IsPoissonRandomMeasure.hasIndepIncrements_nat_count_bernoulli_marking
    (hN : IsPoissonRandomMeasure P N Λ) {p : ℝ≥0 → unitInterval} (hp : Measurable p) (b : Bool) :
    HasIndepIncrements (fun t z ↦ ⌊(z.2 (Ioc 0 t ×ˢ {b})).toNNReal⌋₊)
      (P ⊗ₘ ((Kernel.bernoulli true false hp).marking.comap N hN.measurable)) :=
  (hN.compProd_marking
    (Kernel.bernoulli true false hp)).hasIndepIncrements_nat_count_prod_of_measure_Ioc_prod_lt_top
    (measurableSet_singleton b) (Λ.compProd_Ioc_prod_lt_top _ {b} 0)

/-- Each colour interval count over `(s, t]` under canonical temporal Bernoulli marking has
Poisson law with parameter `∫⁻ x in Ioc s t, p x ∂Λ` (or `1 - p x` for `false`). -/
theorem IsPoissonRandomMeasure.hasLaw_nat_count_Ioc_bernoulli_marking
    (hN : IsPoissonRandomMeasure P N Λ) {p : ℝ≥0 → unitInterval} (hp : Measurable p)
    (b : Bool) (s t : ℝ≥0) :
    HasLaw (fun z ↦ ⌊(z.2 (Ioc s t ×ˢ {b})).toNNReal⌋₊)
      (poissonMeasure (∫⁻ x in Ioc s t,
        (unitInterval.toNNReal (if b then p x else unitInterval.symm (p x)) : ℝ≥0∞) ∂Λ).toNNReal)
      (P ⊗ₘ ((Kernel.bernoulli true false hp).marking.comap N hN.measurable)) := by
  simpa only [Kernel.bernoulli_apply, bernoulliMeasure_apply_singleton_bool,
    ← unitInterval.toNNReal_symm, apply_ite unitInterval.toNNReal] using
    (hN.compProd_marking (Kernel.bernoulli true false hp)).hasLaw_nat_count_prod_Ioc_of_compProd
      (measurableSet_singleton b) s t

/-- Each colour count increment over `(s, t]` under canonical temporal Bernoulli marking has
Poisson law with parameter `∫⁻ x in Ioc s t, p x ∂Λ` (or `1 - p x` for `false`). -/
theorem IsPoissonRandomMeasure.hasLaw_nat_count_sub_bernoulli_marking
    (hN : IsPoissonRandomMeasure P N Λ) {p : ℝ≥0 → unitInterval} (hp : Measurable p)
    (b : Bool) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun z ↦ ⌊(z.2 (Ioc 0 t ×ˢ {b})).toNNReal⌋₊ -
      ⌊(z.2 (Ioc 0 s ×ˢ {b})).toNNReal⌋₊)
      (poissonMeasure (∫⁻ x in Ioc s t,
        (unitInterval.toNNReal (if b then p x else unitInterval.symm (p x)) : ℝ≥0∞) ∂Λ).toNNReal)
      (P ⊗ₘ ((Kernel.bernoulli true false hp).marking.comap N hN.measurable)) := by
  simpa only [Kernel.bernoulli_apply, bernoulliMeasure_apply_singleton_bool,
    ← unitInterval.toNNReal_symm, apply_ite unitInterval.toNNReal] using
    (hN.compProd_marking (Kernel.bernoulli true false hp)).hasLaw_nat_count_prod_sub_of_compProd
      (measurableSet_singleton b) hst

/-- Under canonical temporal Bernoulli marking, the `true` and `false` natural cumulative count
paths add to the ground count path of `N` simultaneously at all times `t : ℝ≥0` on one event of
full probability. -/
theorem IsPoissonRandomMeasure.ae_nat_count_eq_add_bernoulli_marking
    (hN : IsPoissonRandomMeasure P N Λ) {p : ℝ≥0 → unitInterval} (hp : Measurable p) :
    ∀ᵐ z ∂(P ⊗ₘ ((Kernel.bernoulli true false hp).marking.comap N hN.measurable)), ∀ t : ℝ≥0,
      ⌊(N z.1 (Ioc 0 t)).toNNReal⌋₊ =
        ⌊(z.2 (Ioc 0 t ×ˢ {true})).toNNReal⌋₊ + ⌊(z.2 (Ioc 0 t ×ˢ {false})).toNNReal⌋₊ := by
  simpa only [Bool.compl_singleton, Bool.not_true] using
    (hN.compProd_marking (Kernel.bernoulli true false hp)).ae_nat_count_eq_add_compl_of_compProd
      (hN.ae_map_fst_compProd_marking (Kernel.bernoulli true false hp))
      (measurableSet_singleton true)

/-- When `p = 0` `Λ`-almost everywhere, the retained (`true`) natural count path vanishes
simultaneously at all times `t : ℝ≥0` almost surely. -/
theorem IsPoissonRandomMeasure.ae_nat_count_bernoulli_marking_eq_zero_of_ae_eq_zero
    (hN : IsPoissonRandomMeasure P N Λ) {p : ℝ≥0 → unitInterval} (hp : Measurable p)
    (hp0 : ∀ᵐ x ∂Λ, p x = 0) :
    ∀ᵐ z ∂(P ⊗ₘ ((Kernel.bernoulli true false hp).marking.comap N hN.measurable)), ∀ t : ℝ≥0,
      ⌊(z.2 (Ioc 0 t ×ˢ {true})).toNNReal⌋₊ = 0 := by
  have hz := (hN.acceptance_bernoulli_marking hp true).ae_forall_nat_count_eq_zero (by
    rw [withDensity_apply _ measurableSet_Ioi]
    exact (setLIntegral_eq_zero_iff' measurableSet_Ioi (by fun_prop)).2
      (hp0.mono fun x hx _ ↦ by simp [hx]))
  filter_upwards [hz] with z hz t
  simpa only [Measure.map_fst_restrict_prod_apply _ _ _ measurableSet_Ioc, inter_univ] using hz t

/-- When `p = 1` `Λ`-almost everywhere, the rejected (`false`) natural count path vanishes
simultaneously at all times `t : ℝ≥0` almost surely. -/
theorem IsPoissonRandomMeasure.ae_nat_count_bernoulli_marking_eq_zero_of_ae_eq_one
    (hN : IsPoissonRandomMeasure P N Λ) {p : ℝ≥0 → unitInterval} (hp : Measurable p)
    (hp1 : ∀ᵐ x ∂Λ, p x = 1) :
    ∀ᵐ z ∂(P ⊗ₘ ((Kernel.bernoulli true false hp).marking.comap N hN.measurable)), ∀ t : ℝ≥0,
      ⌊(z.2 (Ioc 0 t ×ˢ {false})).toNNReal⌋₊ = 0 := by
  have hz := (hN.acceptance_bernoulli_marking hp false).ae_forall_nat_count_eq_zero (by
    rw [withDensity_apply _ measurableSet_Ioi]
    exact (setLIntegral_eq_zero_iff' measurableSet_Ioi (by fun_prop)).2
      (hp1.mono fun x hx _ ↦ by simp [hx]))
  filter_upwards [hz] with z hz t
  simpa only [Measure.map_fst_restrict_prod_apply _ _ _ measurableSet_Ioc, inter_univ] using hz t

/-- When the ground intensity vanishes on `(0, ∞)` (in particular for `0 • nnvolume`), both colour
count paths under canonical Bernoulli marking vanish simultaneously at all times `t : ℝ≥0` almost
surely. -/
theorem IsPoissonRandomMeasure.ae_nat_count_bernoulli_marking_eq_zero_of_intensity_Ioi_eq_zero
    (hN : IsPoissonRandomMeasure P N Λ) {p : ℝ≥0 → unitInterval} (hp : Measurable p)
    (hΛ : Λ (Ioi 0) = 0) (b : Bool) :
    ∀ᵐ z ∂(P ⊗ₘ ((Kernel.bernoulli true false hp).marking.comap N hN.measurable)), ∀ t : ℝ≥0,
      ⌊(z.2 (Ioc 0 t ×ˢ {b})).toNNReal⌋₊ = 0 := by
  have hz := (hN.acceptance_bernoulli_marking hp b).ae_forall_nat_count_eq_zero (by
    rw [withDensity_apply _ measurableSet_Ioi]
    exact setLIntegral_measure_zero _ _ hΛ)
  filter_upwards [hz] with z hz t
  simpa only [Measure.map_fst_restrict_prod_apply _ _ _ measurableSet_Ioc, inter_univ] using hz t

end Temporal

section HomogeneousTemporal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Bernoulli thinning of a homogeneous temporal Poisson process on `ℝ≥0`**, including boundary
probabilities `p = 0, 1` and zero rate `r = 0`. Thinning a Poisson random measure of rate `r` with
success probability `p` produces a realization-level Markov kernel
`η : Kernel (Measure ℝ≥0) (Measure ℝ≥0 × Measure ℝ≥0)` whose two outputs under
`P ⊗ₘ η.comap N hN.measurable` are independent homogeneous Poisson random measures of rates
`p * r` and `(1 - p) * r` that sum to `N` almost surely; combined with
`ProbabilityTheory.IndepFun.natFloor_toNNReal` and
`IsPoissonRandomMeasure.ae_forall_nat_count_add_eq`, their cumulative-count paths are independent
and add to the original count path simultaneously for all `t : ℝ≥0`. -/
theorem IsPoissonRandomMeasure.exists_bernoulli_thinning_smul_nnvolume
    {N : Ω → Measure ℝ≥0} {r : ℝ≥0}
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

end HomogeneousTemporal

end TauCeti.Probability
