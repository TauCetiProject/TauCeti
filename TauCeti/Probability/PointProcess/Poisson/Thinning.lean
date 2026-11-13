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
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.Composition.Lemmas
import TauCeti.MeasureTheory.Measure.Measurability
import TauCeti.Probability.Distributions.Bernoulli.Measurability
import TauCeti.Probability.Kernel.Composition.MeasureCompProd
import TauCeti.Probability.PointProcess.Poisson.IntegerValued
import TauCeti.Probability.RandomMeasure.AeEq

/-!
# Independent thinning of Poisson random measures and temporal processes

Selecting occurrences from a marked Poisson random measure on `X × E` according to disjoint
measurable mark sets produces mutually independent Poisson random measures on `X` whose intensities
are weighted by the corresponding mark probabilities. Combining this splitting mechanism with the
Poisson Marking Theorem (`IsPoissonRandomMeasure.exists_markovKernel_marking`) yields independent
thinning of an uncoloured Poisson random measure `N` on a standard Borel space:

* For a Markov kernel `κ : Kernel X ι` into a countable discrete colour space `ι`, marking
  occurrences of `N` with `κ` and projecting each singleton colour slice produces a Markov kernel
  `η : Kernel Ω (ι → Measure X)` whose output coordinates under `P ⊗ₘ η` are mutually independent
  Poisson random measures with intensities `Λ.withDensity (fun x ↦ κ x {i})` that superpose to `N`
  almost surely (`IsPoissonRandomMeasure.exists_categorical_thinning`).
* Specializing to `ι = Bool` and `Ber(true, false, p x)` yields location-dependent `p`-thinning
  (`IsPoissonRandomMeasure.exists_bernoulli_thinning_of_measurable`) and constant-probability
  Bernoulli thinning (`IsPoissonRandomMeasure.exists_bernoulli_thinning`), including `p = 0, 1` and
  zero ground intensity `Λ = 0`.
* Specializing to homogeneous temporal intensity `r • nnvolume` on `ℝ≥0` (including zero rate
  `r = 0` and boundary probabilities `p = 0, 1`) yields independent Poisson random measures of
  rates `p * r` and `(1 - p) * r`
  (`IsPoissonRandomMeasure.exists_bernoulli_thinning_smul_nnvolume`), mutually independent
  cumulative-count paths in `ℝ≥0 → ℕ`, simultaneous all-time count additivity, and simultaneous
  all-time vanishing at zero intensity.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Chapter 5 (Corollaries 5.8–5.9, independent thinning) and Chapter 7 (Poisson processes on
  the half-line).
-/

public section

noncomputable section

open Function MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MeasureTheory.Measure

/-- Partitioning a measure on `X × ι` (for a countable discrete mark space `ι`) into singleton mark
slices and projecting onto `X` recovers `μ.map Prod.fst` for every measure `μ`. -/
theorem sum_map_fst_restrict_singleton {X ι : Type*} [MeasurableSpace X] [Countable ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (μ : Measure (X × ι)) :
    (Measure.sum fun i : ι ↦ ((μ.restrict (univ ×ˢ {i})).map Prod.fst)) = μ.map Prod.fst := by
  have hunion : (⋃ i : ι, (univ ×ˢ ({i} : Set ι) : Set (X × ι))) = univ := by
    ext ⟨_, i⟩
    simp
  have hd : Pairwise (Disjoint on fun i : ι ↦ (univ ×ˢ ({i} : Set ι) : Set (X × ι))) :=
    fun _ _ hij ↦ (Set.disjoint_singleton.mpr hij).set_prod_right _ _
  rw [← Measure.map_sum measurable_fst.aemeasurable,
    ← Measure.restrict_iUnion hd (fun i ↦ MeasurableSet.univ.prod (measurableSet_singleton i)),
    hunion, Measure.restrict_univ]

/-- Partitioning a measure on `X × Bool` into `true` and `false` mark slices and projecting onto
`X` recovers `μ.map Prod.fst` for every measure `μ`. -/
@[simp]
theorem map_fst_restrict_true_add_false {X : Type*} [MeasurableSpace X] (μ : Measure (X × Bool)) :
    ((μ.restrict (univ ×ˢ {true})).map Prod.fst) +
      ((μ.restrict (univ ×ˢ {false})).map Prod.fst) = μ.map Prod.fst := by
  simpa only [Measure.sum_bool] using μ.sum_map_fst_restrict_singleton

end MeasureTheory.Measure

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
restrictions to pairwise-disjoint measurable mark sets `B i` yields mutually independent random
measures on `X`. -/
theorem IsPoissonRandomMeasure.iIndepFun_map_fst_restrict_univ_prod {Γ : Measure (X × E)}
    (hM : IsPoissonRandomMeasure P M Γ) {B : ι → Set E} (hB : ∀ i, MeasurableSet (B i))
    (hd : Pairwise (Disjoint on B)) :
    ProbabilityTheory.iIndepFun (fun i ω ↦ ((M ω).restrict (univ ×ˢ B i)).map Prod.fst) P := by
  have hrect (i : ι) : MeasurableSet (univ ×ˢ B i : Set (X × E)) := MeasurableSet.univ.prod (hB i)
  have hd_rect : Pairwise (Disjoint on fun i ↦ (univ ×ˢ B i : Set (X × E))) :=
    fun _ _ hij ↦ (hd hij).set_prod_right _ _
  exact (hM.iIndepFun_restrict hrect hd_rect).comp
    (fun _ μ ↦ μ.map Prod.fst) (fun _ ↦ Measure.measurable_map _ measurable_fst)

/-- Binary specialization of `IsPoissonRandomMeasure.iIndepFun_map_fst_restrict_univ_prod`:
ground projections of two disjoint measurable mark sets are independent random measures. -/
theorem IsPoissonRandomMeasure.indepFun_map_fst_restrict_univ_prod {Γ : Measure (X × E)}
    (hM : IsPoissonRandomMeasure P M Γ) {B₁ B₂ : Set E} (hB₁ : MeasurableSet B₁)
    (hB₂ : MeasurableSet B₂) (hd : Disjoint B₁ B₂) :
    IndepFun (fun ω ↦ ((M ω).restrict (univ ×ˢ B₁)).map Prod.fst)
      (fun ω ↦ ((M ω).restrict (univ ×ˢ B₂)).map Prod.fst) P := by
  let B : Bool → Set E := fun b ↦ cond b B₁ B₂
  have hB (b : Bool) : MeasurableSet (B b) := by cases b <;> assumption
  have hdB : Pairwise (Disjoint on B) := pairwise_disjoint_on_bool.mpr hd
  exact (hM.iIndepFun_map_fst_restrict_univ_prod hB hdB).indepFun
    (i := true) (j := false) (by decide)

end MarkedProjection

section CategoricalAndBernoulliThinning

private def sliceFamily {X ι : Type*} [MeasurableSpace X] [MeasurableSpace ι] :
    Measure (X × ι) → ι → Measure X :=
  fun μ i ↦ ((μ.restrict (univ ×ˢ {i})).map Prod.fst)

private theorem measurable_sliceFamily {X ι : Type*} [MeasurableSpace X] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] : Measurable (sliceFamily (X := X) (ι := ι)) := by
  refine measurable_pi_iff.2 fun i ↦ (Measure.measurable_map _ measurable_fst).comp ?_
  refine Measure.measurable_measure.mpr fun A hA ↦ ?_
  simpa only [Measure.restrict_apply hA] using
    Measure.measurable_coe (hA.inter (MeasurableSet.univ.prod (measurableSet_singleton i)))

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [StandardBorelSpace X]
  {P : Measure Ω} {N : Ω → Measure X} {Λ : Measure X} [SigmaFinite Λ]

private theorem sum_eq_of_compProd_map_sliceFamily {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [IsProbabilityMeasure P]
    (hN : IsPoissonRandomMeasure P N Λ) {η₀ : Kernel Ω (Measure (X × ι))} [IsMarkovKernel η₀]
    (hproj : ∀ᵐ w ∂(P ⊗ₘ η₀), w.2.map Prod.fst = N w.1) :
    ∀ᵐ z ∂(P ⊗ₘ η₀.map (sliceFamily (X := X) (ι := ι))), Measure.sum z.2 = N z.1 := by
  have : IsMarkovKernel (η₀.map (sliceFamily (X := X) (ι := ι))) :=
    Kernel.IsMarkovKernel.map η₀ measurable_sliceFamily
  have hΦ : Measurable (Prod.map (id : Ω → Ω) (sliceFamily (X := X) (ι := ι))) :=
    measurable_id.prodMap measurable_sliceFamily
  have hfin (n : ℕ) :
      ∀ᵐ z ∂(P ⊗ₘ η₀.map (sliceFamily (X := X) (ι := ι))), N z.1 (spanningSets Λ n) ≠ ∞ := by
    have hm : MeasurableSet {ω : Ω | N ω (spanningSets Λ n) ≠ ∞} :=
      (measurableSet_eq_fun
        ((Measure.measurable_coe (measurableSet_spanningSets Λ n)).comp hN.measurable)
        measurable_const).compl
    exact Measure.ae_compProd_of_ae_fst (η₀.map sliceFamily) hm
      ((hN.ae_lt_top (measurableSet_spanningSets Λ n)
        (measure_spanningSets_lt_top Λ n)).mono fun _ h ↦ h.ne)
  refine (Measure.ae_eq_of_forall_ae_eq_of_cover (measurableSet_spanningSets Λ)
    (iUnion_spanningSets Λ) hfin fun A hA ↦ ?_).symm
  have hEA : MeasurableSet {z : Ω × (ι → Measure X) | N z.1 A = Measure.sum z.2 A} :=
    measurableSet_eq_fun ((Measure.measurable_coe hA).comp (hN.measurable.comp measurable_fst))
      ((Measure.measurable_coe hA).comp (Measure.measurable_sum.comp measurable_snd))
  rw [Measure.compProd_map measurable_sliceFamily]
  refine (ae_map_iff hΦ.aemeasurable hEA).2 ?_
  filter_upwards [hproj] with w hw
  have hsum : N w.1 A = Measure.sum (sliceFamily w.2) A := by
    rw [← hw, ← w.2.sum_map_fst_restrict_singleton]
    rfl
  exact hsum

/-- **Countable categorical thinning of an uncoloured Poisson random measure** (Last–Penrose,
Corollary 5.9). Independently classifying occurrences of `N` with a Markov kernel
`κ : Kernel X ι` into a countable discrete colour space `ι` yields a Markov kernel
`η : Kernel Ω (ι → Measure X)` whose colour components under `P ⊗ₘ η` are mutually independent
Poisson random measures with intensities `Λ.withDensity (fun x ↦ κ x {i})` that superpose to `N`
almost surely. -/
theorem IsPoissonRandomMeasure.exists_categorical_thinning {ι : Type*} [Countable ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (hN : IsPoissonRandomMeasure P N Λ) (κ : Kernel X ι) [IsMarkovKernel κ] :
    ∃ η : Kernel Ω (ι → Measure X),
      IsMarkovKernel η ∧
      (∀ i, IsPoissonRandomMeasure (P ⊗ₘ η) (fun z ↦ z.2 i)
        (Λ.withDensity fun x ↦ κ x {i})) ∧
      ProbabilityTheory.iIndepFun (fun i z ↦ z.2 i) (P ⊗ₘ η) ∧
      ∀ᵐ z ∂(P ⊗ₘ η), Measure.sum z.2 = N z.1 := by
  let := hN.isProbabilityMeasure
  obtain ⟨η₀, _, hM₀, hproj⟩ := hN.exists_markovKernel_marking κ
  have hη : IsMarkovKernel (η₀.map (sliceFamily (X := X) (ι := ι))) :=
    Kernel.IsMarkovKernel.map η₀ measurable_sliceFamily
  have hΦ : Measurable (Prod.map (id : Ω → Ω) (sliceFamily (X := X) (ι := ι))) :=
    measurable_id.prodMap measurable_sliceFamily
  have hmap : P ⊗ₘ η₀.map (sliceFamily (X := X) (ι := ι)) =
      (P ⊗ₘ η₀).map (Prod.map id sliceFamily) :=
    Measure.compProd_map measurable_sliceFamily
  have hslice (i : ι) := hM₀.map_fst_restrict_univ_prod_compProd (measurableSet_singleton i)
  have hind₀ := hM₀.iIndepFun_map_fst_restrict_univ_prod
    (fun i : ι ↦ measurableSet_singleton i) (fun _ _ hij ↦ Set.disjoint_singleton.mpr hij)
  have hcoord (i : ι) : Measurable (fun z : Ω × (ι → Measure X) ↦ z.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  refine ⟨η₀.map sliceFamily, hη, fun i ↦ ?_, ?_, sum_eq_of_compProd_map_sliceFamily hN hproj⟩
  · exact (hslice i).of_identDistrib (hcoord i)
      ⟨(hslice i).measurable.aemeasurable, (hcoord i).aemeasurable,
        by rw [hmap, Measure.map_map (hcoord i) hΦ]; rfl⟩
  · refine (iIndepFun_iff_map_fun_eq_infinitePi_map hcoord).2 ?_
    rw [hmap, Measure.map_map (measurable_pi_iff.2 hcoord) hΦ]
    simp_rw [Measure.map_map (hcoord _) hΦ]
    exact hind₀.map_fun_eq_infinitePi_map fun i ↦ (hslice i).measurable

/-- Homogeneous categorical thinning specialization of
`IsPoissonRandomMeasure.exists_categorical_thinning` for a fixed colour distribution `Q`: each
colour `i` receives intensity `(Q {i}) • Λ`. -/
theorem IsPoissonRandomMeasure.exists_categorical_thinning_const {ι : Type*} [Countable ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (hN : IsPoissonRandomMeasure P N Λ) (Q : Measure ι) [IsProbabilityMeasure Q] :
    ∃ η : Kernel Ω (ι → Measure X),
      IsMarkovKernel η ∧
      (∀ i, IsPoissonRandomMeasure (P ⊗ₘ η) (fun z ↦ z.2 i) (Q {i} • Λ)) ∧
      ProbabilityTheory.iIndepFun (fun i z ↦ z.2 i) (P ⊗ₘ η) ∧
      ∀ᵐ z ∂(P ⊗ₘ η), Measure.sum z.2 = N z.1 := by
  obtain ⟨η, hη, hP, hind, hsum⟩ := hN.exists_categorical_thinning (Kernel.const X Q)
  simp only [Kernel.const_apply, withDensity_const] at hP
  exact ⟨η, hη, hP, hind, hsum⟩

/-- **Independent `p`-thinning of an uncoloured Poisson random measure** (Last–Penrose,
Corollary 5.8). For a measurable retention probability `p : X → unitInterval`, independently
marking occurrences of `N` with `Ber(true, false, p x)` and splitting by the mark produces a
Markov kernel `η : Kernel Ω (Measure X × Measure X)` whose two output coordinates under `P ⊗ₘ η`
are independent Poisson random measures with intensities weighted by `p` and `1 - p` that sum to
`N` almost surely. -/
theorem IsPoissonRandomMeasure.exists_bernoulli_thinning_of_measurable
    (hN : IsPoissonRandomMeasure P N Λ) {p : X → unitInterval} (hp : Measurable p) :
    ∃ η : Kernel Ω (Measure X × Measure X),
      IsMarkovKernel η ∧
      IsPoissonRandomMeasure (P ⊗ₘ η) (fun z ↦ z.2.1)
        (Λ.withDensity fun x ↦ (unitInterval.toNNReal (p x) : ℝ≥0∞)) ∧
      IsPoissonRandomMeasure (P ⊗ₘ η) (fun z ↦ z.2.2)
        (Λ.withDensity fun x ↦ ((1 - unitInterval.toNNReal (p x) : ℝ≥0) : ℝ≥0∞)) ∧
      IndepFun (fun z ↦ z.2.1) (fun z ↦ z.2.2) (P ⊗ₘ η) ∧
      ∀ᵐ z ∂(P ⊗ₘ η), z.2.1 + z.2.2 = N z.1 := by
  let := hN.isProbabilityMeasure
  let κ : Kernel X Bool := ⟨fun x ↦ bernoulliMeasure true false (p x), by fun_prop⟩
  have : IsMarkovKernel κ := ⟨fun x ↦ by dsimp [κ]; infer_instance⟩
  obtain ⟨η₀, _, hP, hind, hsum⟩ := hN.exists_categorical_thinning κ
  let e : (Bool → Measure X) ≃ᵐ Measure X × Measure X :=
    ((MeasurableEquiv.arrowCongr' finTwoEquiv.symm (.refl _)).trans .finTwoArrow).trans .prodComm
  let E := (MeasurableEquiv.refl Ω).prodCongr e
  have hη : IsMarkovKernel (η₀.map e) := Kernel.IsMarkovKernel.map η₀ e.measurable
  have hmap : P ⊗ₘ η₀.map e = (P ⊗ₘ η₀).map E := Measure.compProd_map e.measurable
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
  refine ⟨η₀.map e, hη, ?_, ?_, ?_, ?_⟩
  · exact (htrue ▸ hP true).of_identDistrib measurable_snd.fst
      ⟨(hP true).measurable.aemeasurable, measurable_snd.fst.aemeasurable,
        by rw [hmap, Measure.map_map measurable_snd.fst E.measurable]; rfl⟩
  · exact (hfalse ▸ hP false).of_identDistrib measurable_snd.snd
      ⟨(hP false).measurable.aemeasurable, measurable_snd.snd.aemeasurable,
        by rw [hmap, Measure.map_map measurable_snd.snd E.measurable]; rfl⟩
  · refine (indepFun_iff_map_prod_eq_prod_map_map
      measurable_snd.fst.aemeasurable measurable_snd.snd.aemeasurable).2 ?_
    rw [hmap, Measure.map_map (measurable_snd.fst.prodMk measurable_snd.snd) E.measurable,
      Measure.map_map measurable_snd.fst E.measurable,
      Measure.map_map measurable_snd.snd E.measurable]
    exact (hind.indepFun (i := true) (j := false) (by decide)).map_prod_eq_prod_map_map
      (hP true).measurable.aemeasurable (hP false).measurable.aemeasurable
  · rw [hmap, E.measurableEmbedding.ae_map_iff]
    filter_upwards [hsum] with w hw
    rw [Measure.sum_bool] at hw
    exact hw

/-- **Constant-probability Bernoulli thinning of an uncoloured Poisson random measure**, including
the boundary probabilities `p = 0` and `p = 1` and zero ground intensity `Λ = 0`. -/
theorem IsPoissonRandomMeasure.exists_bernoulli_thinning
    (hN : IsPoissonRandomMeasure P N Λ) (p : unitInterval) :
    ∃ η : Kernel Ω (Measure X × Measure X),
      IsMarkovKernel η ∧
      IsPoissonRandomMeasure (P ⊗ₘ η) (fun z ↦ z.2.1)
        ((unitInterval.toNNReal p : ℝ≥0∞) • Λ) ∧
      IsPoissonRandomMeasure (P ⊗ₘ η) (fun z ↦ z.2.2)
        (((1 - unitInterval.toNNReal p : ℝ≥0) : ℝ≥0∞) • Λ) ∧
      IndepFun (fun z ↦ z.2.1) (fun z ↦ z.2.2) (P ⊗ₘ η) ∧
      ∀ᵐ z ∂(P ⊗ₘ η), z.2.1 + z.2.2 = N z.1 := by
  obtain ⟨η, hη, h₁, h₂, hind, hadd⟩ :=
    hN.exists_bernoulli_thinning_of_measurable (measurable_const : Measurable fun _ : X ↦ p)
  simp only [withDensity_const] at h₁ h₂
  exact ⟨η, hη, h₁, h₂, hind, hadd⟩

end CategoricalAndBernoulliThinning

end TauCeti.Probability

namespace ProbabilityTheory

/-- Mutually independent random measures on `ℝ≥0` induce mutually independent natural-valued
cumulative-count processes in `ℝ≥0 → ℕ`. -/
theorem iIndepFun.nat_count {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {M : ι → Ω → Measure ℝ≥0} (h : iIndepFun M P) :
    iIndepFun (fun i ω t ↦ ⌊(M i ω (Ioc 0 t)).toNNReal⌋₊) P := by
  have hm : Measurable (fun μ : Measure ℝ≥0 ↦ fun t : ℝ≥0 ↦ ⌊(μ (Ioc 0 t)).toNNReal⌋₊) :=
    measurable_pi_iff.2 fun t ↦
      (Measure.measurable_coe measurableSet_Ioc).ennreal_toNNReal.nat_floor
  exact h.comp (fun _ ↦ _) (fun _ ↦ hm)

/-- Independent random measures on `ℝ≥0` induce independent natural-valued cumulative-count
processes in `ℝ≥0 → ℕ`. -/
theorem IndepFun.nat_count {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {M₁ M₂ : Ω → Measure ℝ≥0} (h : IndepFun M₁ M₂ P) :
    IndepFun (fun ω t ↦ ⌊(M₁ ω (Ioc 0 t)).toNNReal⌋₊)
      (fun ω t ↦ ⌊(M₂ ω (Ioc 0 t)).toNNReal⌋₊) P := by
  have hm : Measurable (fun μ : Measure ℝ≥0 ↦ fun t : ℝ≥0 ↦ ⌊(μ (Ioc 0 t)).toNNReal⌋₊) :=
    measurable_pi_iff.2 fun t ↦
      (Measure.measurable_coe measurableSet_Ioc).ennreal_toNNReal.nat_floor
  exact h.comp hm hm

end ProbabilityTheory

namespace TauCeti.Probability

section ZeroAndTemporal

/-- Any Poisson random measure with zero intensity vanishes almost surely as a measure, with no
assumptions on the ground measurable space. This covers both zero-rate drivers and `p = 0` or
`p = 1` outputs of Bernoulli thinning. -/
theorem IsPoissonRandomMeasure.ae_eq_zero {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {P : Measure Ω} {N : Ω → Measure X} (hN : IsPoissonRandomMeasure P N 0) :
    N =ᵐ[P] 0 := by
  have hlaw := hN.hasLaw MeasurableSet.univ (by simp)
  have hmap : (P.map fun ω ↦ N ω univ) = Measure.dirac 0 := by
    simpa [poissonMeasure_zero] using hlaw.map_eq
  have huniv : ∀ᵐ ω ∂P, N ω univ = 0 := by
    refine (ae_map_iff hlaw.aemeasurable (measurableSet_singleton 0)).1 ?_
    rw [hmap]
    simp
  filter_upwards [huniv] with ω hω
  exact Measure.measure_univ_eq_zero.mp hω

/-- If two temporal Poisson random measures with locally finite intensities sum almost surely to
`M₀`, then their natural cumulative counts add to those of `M₀` simultaneously at all times `t` on
a single event of full probability. -/
theorem IsPoissonRandomMeasure.ae_forall_nat_count_add_eq {Ω : Type*} [MeasurableSpace Ω]
    {Q : Measure Ω} {M₁ M₂ M₀ : Ω → Measure ℝ≥0} {Λ₁ Λ₂ : Measure ℝ≥0}
    [IsLocallyFiniteMeasure Λ₁] [IsLocallyFiniteMeasure Λ₂]
    (h₁ : IsPoissonRandomMeasure Q M₁ Λ₁) (h₂ : IsPoissonRandomMeasure Q M₂ Λ₂)
    (hadd : ∀ᵐ z ∂Q, M₁ z + M₂ z = M₀ z) :
    ∀ᵐ z ∂Q, ∀ t : ℝ≥0,
      ⌊(M₁ z (Ioc 0 t)).toNNReal⌋₊ + ⌊(M₂ z (Ioc 0 t)).toNNReal⌋₊ =
        ⌊(M₀ z (Ioc 0 t)).toNNReal⌋₊ := by
  have hfin₁ : ∀ᵐ z ∂Q, ∀ n : ℕ, M₁ z (Ioc 0 (n : ℝ≥0)) < ∞ :=
    ae_all_iff.2 fun n ↦ h₁.ae_lt_top measurableSet_Ioc measure_Ioc_lt_top
  have hfin₂ : ∀ᵐ z ∂Q, ∀ n : ℕ, M₂ z (Ioc 0 (n : ℝ≥0)) < ∞ :=
    ae_all_iff.2 fun n ↦ h₂.ae_lt_top measurableSet_Ioc measure_Ioc_lt_top
  filter_upwards [h₁.ae_isIntegerValued, h₂.ae_isIntegerValued, hfin₁, hfin₂, hadd] with
    z hint₁ hint₂ hb₁ hb₂ hsum t
  have ht₁ : M₁ z (Ioc 0 t) < ∞ :=
    (measure_mono (Ioc_subset_Ioc_right (Nat.le_ceil t))).trans_lt (hb₁ ⌈t⌉₊)
  have ht₂ : M₂ z (Ioc 0 t) < ∞ :=
    (measure_mono (Ioc_subset_Ioc_right (Nat.le_ceil t))).trans_lt (hb₂ ⌈t⌉₊)
  obtain ⟨k₁, hk₁⟩ := hint₁.exists_eq_natCast measurableSet_Ioc ht₁
  obtain ⟨k₂, hk₂⟩ := hint₂.exists_eq_natCast measurableSet_Ioc ht₂
  have ht₀ : M₀ z (Ioc 0 t) = ((k₁ + k₂ : ℕ) : ℝ≥0∞) := by
    rw [← hsum, add_apply, hk₁, hk₂, Nat.cast_add]
  rw [hk₁, hk₂, ht₀]
  simp only [ENNReal.toNNReal_natCast, Nat.floor_natCast]

/-- Any temporal Poisson random measure with zero intensity has identically zero cumulative counts
simultaneously at all times `t` on a single event of probability one. -/
theorem IsPoissonRandomMeasure.ae_forall_nat_count_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {M : Ω → Measure ℝ≥0} (hM : IsPoissonRandomMeasure P M 0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, ⌊(M ω (Ioc 0 t)).toNNReal⌋₊ = 0 := by
  filter_upwards [hM.ae_eq_zero] with ω hω t
  simp [hω]

/-- **Bernoulli thinning of a homogeneous temporal Poisson process on `ℝ≥0`**, including boundary
probabilities `p = 0, 1` and zero rate `r = 0`. Thinning a Poisson random measure of rate `r` with
success probability `p` produces a Markov kernel `η : Kernel Ω (Measure ℝ≥0 × Measure ℝ≥0)` whose
two outputs under `P ⊗ₘ η` are independent homogeneous Poisson random measures of rates `p * r`
and `(1 - p) * r` that sum to `N` almost surely; by `ProbabilityTheory.IndepFun.nat_count` and
`IsPoissonRandomMeasure.ae_forall_nat_count_add_eq`, their cumulative-count paths are independent
and add to the original count path simultaneously for all `t : ℝ≥0`. -/
theorem IsPoissonRandomMeasure.exists_bernoulli_thinning_smul_nnvolume {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {N : Ω → Measure ℝ≥0} {r : ℝ≥0}
    (hN : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (p : unitInterval) :
    ∃ η : Kernel Ω (Measure ℝ≥0 × Measure ℝ≥0),
      IsMarkovKernel η ∧
      IsPoissonRandomMeasure (P ⊗ₘ η) (fun z ↦ z.2.1)
        (((unitInterval.toNNReal p * r : ℝ≥0) : ℝ≥0∞) • nnvolume) ∧
      IsPoissonRandomMeasure (P ⊗ₘ η) (fun z ↦ z.2.2)
        ((((1 - unitInterval.toNNReal p) * r : ℝ≥0) : ℝ≥0∞) • nnvolume) ∧
      IndepFun (fun z ↦ z.2.1) (fun z ↦ z.2.2) (P ⊗ₘ η) ∧
      ∀ᵐ z ∂(P ⊗ₘ η), z.2.1 + z.2.2 = N z.1 := by
  have : IsLocallyFiniteMeasure ((r : ℝ≥0∞) • nnvolume) :=
    nnvolume.isLocallyFiniteMeasure_smul ENNReal.coe_ne_top
  obtain ⟨η, hη, h₁, h₂, hind, hadd⟩ := hN.exists_bernoulli_thinning p
  rw [smul_smul, ← ENNReal.coe_mul] at h₁ h₂
  exact ⟨η, hη, h₁, h₂, hind, hadd⟩

end ZeroAndTemporal

end TauCeti.Probability
