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
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.Lemmas
import TauCeti.MeasureTheory.Measure.Measurability
import TauCeti.MeasureTheory.Measure.Prod
import TauCeti.Probability.Distributions.Bernoulli.Measurability
import TauCeti.Probability.Independence.Map
import TauCeti.Probability.Kernel.Composition.MeasureCompProd
import TauCeti.Probability.PointProcess.Poisson.IntegerValued

/-!
# Independent thinning of Poisson random measures and temporal processes

Selecting occurrences from a marked Poisson random measure on `X × E` according to disjoint
measurable subsets produces mutually independent random measures on `X`; for composition-product
intensities `Λ ⊗ₘ κ`, each projected slice is a Poisson random measure whose intensity weights `Λ`
by the corresponding section masses. Combining this splitting mechanism with the Poisson Marking
Theorem (`IsPoissonRandomMeasure.exists_isMarkovKernel_marking`) yields independent thinning of an
uncoloured Poisson random measure `N` on a standard Borel space via realization-level Markov
kernels:

* For a Markov kernel `κ : Kernel X ι` into a countable discrete colour space `ι`, marking
  occurrences of `N` with `κ` and projecting each singleton colour slice produces a
  realization-level Markov kernel `η : Kernel (Measure X) (ι → Measure X)` whose output coordinates
  under `P ⊗ₘ η.comap N hN.measurable` are mutually independent Poisson random measures with
  intensities `Λ.withDensity (fun x ↦ κ x {i})` that superpose to `N` almost surely
  (`IsPoissonRandomMeasure.exists_categorical_thinning`).
* Specializing to `ι = Bool` and `Ber(true, false, p x)` yields location-dependent `p`-thinning
  (`IsPoissonRandomMeasure.exists_bernoulli_thinning_of_measurable`) and constant-probability
  Bernoulli thinning (`IsPoissonRandomMeasure.exists_bernoulli_thinning`), including `p = 0, 1` and
  zero ground intensity `Λ = 0`.
* Specializing to homogeneous temporal intensity `r • nnvolume` on `ℝ≥0` (including zero rate
  `r = 0` and boundary probabilities `p = 0, 1`) yields a realization-level Markov kernel
  `η : Kernel (Measure ℝ≥0) (Measure ℝ≥0 × Measure ℝ≥0)` producing independent Poisson random
  measures of rates `p * r` and `(1 - p) * r` that sum to `N` almost surely
  (`IsPoissonRandomMeasure.exists_bernoulli_thinning_smul_nnvolume`).

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Chapter 5 (Corollaries 5.8–5.9, independent thinning) and Chapter 7 (Poisson processes on
  the half-line).
-/

public section

noncomputable section

open Function MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

section MarkedProjection

variable {Ω X E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace E]
  {P : Measure Ω} {Λ : Measure X} {κ : Kernel X E} {M : Ω → Measure (X × E)}

/-- Restricting a Poisson random measure with composition-product intensity `Λ ⊗ₘ κ` to a
measurable set `A` and projecting onto `X` gives a Poisson random measure whose intensity weights
`Λ` by the section masses `x ↦ κ x (Prod.mk x ⁻¹' A)`. -/
theorem IsPoissonRandomMeasure.map_fst_restrict_compProd [SFinite Λ] [IsSFiniteKernel κ]
    (hM : IsPoissonRandomMeasure P M (Λ ⊗ₘ κ)) {A : Set (X × E)} (hA : MeasurableSet A) :
    IsPoissonRandomMeasure P (fun ω ↦ ((M ω).restrict A).map Prod.fst)
      (Λ.withDensity fun x ↦ κ x (Prod.mk x ⁻¹' A)) := by
  simpa only [Measure.map_fst_restrict_compProd_eq_withDensity Λ κ hA] using
    (hM.restrict hA).map measurable_fst

/-- Projecting occurrences whose marks fall in a measurable mark set `B` produces a Poisson random
measure on `X` with intensity `Λ.withDensity (fun x ↦ κ x B)`. -/
theorem IsPoissonRandomMeasure.map_fst_restrict_univ_prod_compProd [SFinite Λ] [IsSFiniteKernel κ]
    (hM : IsPoissonRandomMeasure P M (Λ ⊗ₘ κ)) {B : Set E} (hB : MeasurableSet B) :
    IsPoissonRandomMeasure P (fun ω ↦ ((M ω).restrict (univ ×ˢ B)).map Prod.fst)
      (Λ.withDensity fun x ↦ κ x B) := by
  simpa using hM.map_fst_restrict_compProd (MeasurableSet.univ.prod hB)

/-- For any Poisson random measure on `X × E` (with arbitrary intensity `Γ`), projecting the
restrictions to pairwise-disjoint measurable subsets `A i` of `X × E` yields mutually independent
random measures on `X`. -/
theorem IsPoissonRandomMeasure.iIndepFun_map_fst_restrict {Γ : Measure (X × E)}
    (hM : IsPoissonRandomMeasure P M Γ) {A : ι → Set (X × E)} (hA : ∀ i, MeasurableSet (A i))
    (hd : Pairwise (Disjoint on A)) :
    ProbabilityTheory.iIndepFun (fun i ω ↦ ((M ω).restrict (A i)).map Prod.fst) P :=
  (hM.iIndepFun_restrict hA hd).comp
    (fun _ μ ↦ μ.map Prod.fst) (fun _ ↦ Measure.measurable_map _ measurable_fst)

/-- Binary specialization of `IsPoissonRandomMeasure.iIndepFun_map_fst_restrict`: ground projections
of restrictions to two disjoint measurable subsets of `X × E` are independent random measures. -/
theorem IsPoissonRandomMeasure.indepFun_map_fst_restrict {Γ : Measure (X × E)}
    (hM : IsPoissonRandomMeasure P M Γ) {A₁ A₂ : Set (X × E)} (hA₁ : MeasurableSet A₁)
    (hA₂ : MeasurableSet A₂) (hd : Disjoint A₁ A₂) :
    IndepFun (fun ω ↦ ((M ω).restrict A₁).map Prod.fst)
      (fun ω ↦ ((M ω).restrict A₂).map Prod.fst) P :=
  (hM.indepFun_restrict hA₁ hA₂ hd).comp
    (Measure.measurable_map _ measurable_fst) (Measure.measurable_map _ measurable_fst)

/-- For any Poisson random measure on `X × E` (with arbitrary intensity `Γ`), projecting the
restrictions to pairwise-disjoint measurable mark sets `B i` yields mutually independent random
measures on `X`. -/
theorem IsPoissonRandomMeasure.iIndepFun_map_fst_restrict_univ_prod {Γ : Measure (X × E)}
    (hM : IsPoissonRandomMeasure P M Γ) {B : ι → Set E} (hB : ∀ i, MeasurableSet (B i))
    (hd : Pairwise (Disjoint on B)) :
    ProbabilityTheory.iIndepFun (fun i ω ↦ ((M ω).restrict (univ ×ˢ B i)).map Prod.fst) P :=
  hM.iIndepFun_map_fst_restrict (fun i ↦ MeasurableSet.univ.prod (hB i))
    (fun _ _ hij ↦ (hd hij).set_prod_right _ _)

/-- Binary specialization of `IsPoissonRandomMeasure.iIndepFun_map_fst_restrict_univ_prod`:
ground projections of two disjoint measurable mark sets are independent random measures. -/
theorem IsPoissonRandomMeasure.indepFun_map_fst_restrict_univ_prod {Γ : Measure (X × E)}
    (hM : IsPoissonRandomMeasure P M Γ) {B₁ B₂ : Set E} (hB₁ : MeasurableSet B₁)
    (hB₂ : MeasurableSet B₂) (hd : Disjoint B₁ B₂) :
    IndepFun (fun ω ↦ ((M ω).restrict (univ ×ˢ B₁)).map Prod.fst)
      (fun ω ↦ ((M ω).restrict (univ ×ˢ B₂)).map Prod.fst) P :=
  hM.indepFun_map_fst_restrict (MeasurableSet.univ.prod hB₁) (MeasurableSet.univ.prod hB₂)
    (hd.set_prod_right _ _)

end MarkedProjection

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

private theorem sum_eq_of_compProd_map_sliceFamily {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (hN : IsPoissonRandomMeasure P N Λ) {η₀ : Kernel Ω (Measure (X × ι))} [IsMarkovKernel η₀]
    (hproj : ∀ᵐ w ∂(P ⊗ₘ η₀), w.2.map Prod.fst = N w.1) :
    ∀ᵐ z ∂(P ⊗ₘ η₀.map (sliceFamily (X := X) (ι := ι))), Measure.sum z.2 = N z.1 := by
  let := hN.isProbabilityMeasure
  have : IsMarkovKernel (η₀.map (sliceFamily (X := X) (ι := ι))) :=
    Kernel.IsMarkovKernel.map η₀ measurable_sliceFamily
  have hΦ : Measurable (Prod.map (id : Ω → Ω) (sliceFamily (X := X) (ι := ι))) :=
    measurable_id.prodMap measurable_sliceFamily
  refine (hN.compProd_fst _).ae_eq_of_forall_ae_eq fun A hA ↦ ?_
  have hEA : MeasurableSet {z : Ω × (ι → Measure X) | Measure.sum z.2 A = N z.1 A} :=
    measurableSet_eq_fun
      ((Measure.measurable_coe hA).comp (Measure.measurable_sum.comp measurable_snd))
      ((Measure.measurable_coe hA).comp (hN.measurable.comp measurable_fst))
  rw [Measure.compProd_map measurable_sliceFamily]
  refine (ae_map_iff hΦ.aemeasurable hEA).2 ?_
  filter_upwards [hproj] with w hw
  dsimp only [Prod.map_fst, Prod.map_snd, id_eq]
  unfold sliceFamily
  rw [Measure.sum_map_fst_restrict_univ_prod_singleton, hw]

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
  have hcomap : (η₀.map (sliceFamily (X := X) (ι := ι))).comap N hN.measurable =
      (η₀.comap N hN.measurable).map sliceFamily :=
    Kernel.comap_map_comm η₀ hN.measurable measurable_sliceFamily
  have hmap : P ⊗ₘ (η₀.map (sliceFamily (X := X) (ι := ι))).comap N hN.measurable =
      (P ⊗ₘ η₀.comap N hN.measurable).map (Prod.map id sliceFamily) := by
    rw [hcomap, Measure.compProd_map measurable_sliceFamily]
  have hslice (i : ι) := hM₀.map_fst_restrict_univ_prod_compProd (measurableSet_singleton i)
  have hind₀ := hM₀.iIndepFun_map_fst_restrict_univ_prod
    (fun i : ι ↦ measurableSet_singleton i) (fun _ _ hij ↦ Set.disjoint_singleton.mpr hij)
  have hcoord (i : ι) : Measurable (fun z : Ω × (ι → Measure X) ↦ z.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  refine ⟨η₀.map sliceFamily, hη, fun i ↦ ?_, ?_, ?_⟩
  · refine (hslice i).of_identDistrib (hcoord i)
      ⟨(hslice i).measurable.aemeasurable, (hcoord i).aemeasurable, ?_⟩
    rw [hmap, Measure.map_map (hcoord i) hΦ]
    simp only [Function.comp_def, Prod.map_snd, sliceFamily]
  · refine (iIndepFun_iff_map_fun_eq_infinitePi_map hcoord).2 ?_
    rw [hmap, Measure.map_map (measurable_pi_iff.2 hcoord) hΦ]
    simp_rw [Measure.map_map (hcoord _) hΦ]
    exact hind₀.map_fun_eq_infinitePi_map fun i ↦ (hslice i).measurable
  · rw [hcomap]
    exact sum_eq_of_compProd_map_sliceFamily hN hproj

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

/-- Measurable equivalence identifying `Bool → α` with `α × α` in `(f true, f false)` order. -/
private def boolArrowTrueFalseEquivProd (α : Type*) [MeasurableSpace α] :
    (Bool → α) ≃ᵐ α × α :=
  ((MeasurableEquiv.arrowCongr' finTwoEquiv.symm (.refl α)).trans
    MeasurableEquiv.finTwoArrow).trans MeasurableEquiv.prodComm

private theorem boolArrowTrueFalseEquivProd_fst {α : Type*} [MeasurableSpace α] (f : Bool → α) :
    (boolArrowTrueFalseEquivProd α f).1 = f true := by
  simp [boolArrowTrueFalseEquivProd, MeasurableEquiv.arrowCongr', Equiv.arrowCongr',
    MeasurableEquiv.prodComm, finTwoEquiv]

private theorem boolArrowTrueFalseEquivProd_snd {α : Type*} [MeasurableSpace α] (f : Bool → α) :
    (boolArrowTrueFalseEquivProd α f).2 = f false := by
  simp [boolArrowTrueFalseEquivProd, MeasurableEquiv.arrowCongr', Equiv.arrowCongr',
    MeasurableEquiv.prodComm, finTwoEquiv]

/-- Binary specialization of `IsPoissonRandomMeasure.exists_categorical_thinning` transporting the
`Bool`-indexed output along `boolArrowTrueFalseEquivProd` into a pair of random measures. -/
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
  let e := boolArrowTrueFalseEquivProd (Measure X)
  let E := MeasurableEquiv.prodCongr (.refl Ω) e
  have hE_fst (w : Ω × (Bool → Measure X)) : (E w).1 = w.1 := by
    simp [E, MeasurableEquiv.prodCongr]
  have hE_snd_fst (w : Ω × (Bool → Measure X)) : (E w).2.1 = w.2 true := by
    simp [E, e, MeasurableEquiv.prodCongr, boolArrowTrueFalseEquivProd_fst]
  have hE_snd_snd (w : Ω × (Bool → Measure X)) : (E w).2.2 = w.2 false := by
    simp [E, e, MeasurableEquiv.prodCongr, boolArrowTrueFalseEquivProd_snd]
  -- Push the `Bool`-indexed thinning kernel forward to `Measure X × Measure X` via `e`.
  have hη : IsMarkovKernel (η₀.map e) := Kernel.IsMarkovKernel.map η₀ e.measurable
  have hmap : P ⊗ₘ (η₀.map e).comap N hN.measurable =
      (P ⊗ₘ η₀.comap N hN.measurable).map E := by
    rw [Kernel.comap_map_comm η₀ hN.measurable e.measurable, Measure.compProd_map e.measurable]
    rfl
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
  let κ : Kernel X Bool := ⟨fun x ↦ bernoulliMeasure true false (p x), by fun_prop⟩
  have : IsMarkovKernel κ := ⟨fun x ↦ by dsimp [κ]; infer_instance⟩
  obtain ⟨η, hη, h₁, h₂, hind, hadd⟩ := exists_bool_thinning hN κ
  have htrue : (fun x ↦ κ x {true}) = fun x ↦ (unitInterval.toNNReal (p x) : ℝ≥0∞) :=
    funext fun x ↦ bernoulliMeasure_apply_of_mem_of_notMem (p x)
      (measurableSet_singleton true) rfl (by simp)
  have hfalse : (fun x ↦ κ x {false}) =
      fun x ↦ ((1 - unitInterval.toNNReal (p x) : ℝ≥0) : ℝ≥0∞) :=
    funext fun x ↦ by
      simp only [κ, Kernel.coe_mk]
      rw [bernoulliMeasure_apply_of_notMem_of_mem (p x) (measurableSet_singleton false)
          (by simp) rfl,
        ← unitInterval.toNNReal_add_toNNReal_symm (p x), add_tsub_cancel_left]
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
`ProbabilityTheory.IndepFun.natFloor_toNNReal_Ioc` and
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
  have : IsLocallyFiniteMeasure ((r : ℝ≥0∞) • nnvolume) :=
    nnvolume.isLocallyFiniteMeasure_smul ENNReal.coe_ne_top
  obtain ⟨η, hη, h₁, h₂, hind, hadd⟩ := hN.exists_bernoulli_thinning p
  rw [smul_smul, ← ENNReal.coe_mul] at h₁ h₂
  exact ⟨η, hη, h₁, h₂, hind, hadd⟩

end Temporal

end TauCeti.Probability
