/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.Marking.Measure
public import TauCeti.Probability.PointProcess.Poisson.Independence
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.MeasureTheory.Constructions.UnitInterval
import TauCeti.Probability.PointProcess.Poisson.IntegerValued
import TauCeti.Probability.PointProcess.Poisson.Laplace
import TauCeti.Probability.PointProcess.Poisson.LaplaceCharacterization
import TauCeti.Probability.Distributions.Bernoulli.Measurability
import TauCeti.Probability.Kernel.Composition.MeasureCompProd
import TauCeti.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub

/-!
# The Poisson marking theorem and independent thinning

Independently marking the occurrences of a Poisson random measure `N` of intensity `Λ` using a
Markov kernel `κ : Kernel X E` produces a Poisson random measure on `X × E` with intensity
`Λ ⊗ₘ κ`, whose ground projection recovers `N` almost surely.

The theorem is proved at three levels of generality:

* Given any measurable optional occurrence enumeration of `N`, marking via
  `Kernel.optionalTupleMarking` yields a Poisson random measure of intensity `Λ ⊗ₘ κ` for any
  s-finite intensity `Λ`, with no separation or topological assumption on `X`.
* On any standard Borel space `X` with sigma-finite intensity `Λ`, intrinsic marking via
  `Kernel.markingOfCover` gives the marked law, the joint realization on `Ω × Measure (X × E)`
  with almost-sure ground projection `p.2.map Prod.fst = N p.1`, and transfer to any
  realization on an arbitrary probability space with that joint or marginal law.
* On a sigma-compact Hausdorff standard Borel space with intensity finite on compact sets, the
  canonical cover-free `Kernel.marking` applies directly; for constant mark kernel
  `Kernel.const X Q`, the intensity reduces to `Λ.prod Q`.

Projecting a measurable acceptance region of a Poisson random measure of intensity `Λ ⊗ₘ κ`
gives a Poisson random measure weighted by the kernel section masses. Applying this to a
location-dependent Bernoulli mark kernel `Kernel.bernoulli` yields independent thinning: an
uncoloured Poisson random measure splits into two independent Poisson random measures with
intensities `Λ.withDensity p` and `Λ.withDensity (1 - p)` summing to `N` almost surely,
including constant thinning and boundary probabilities `0` and `1`.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Theorem 5.2 (Marking Theorem) and Corollary 5.9 (Thinning).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

section General

variable {Ω X E : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace E]
  {P : Measure Ω} {N : Ω → Measure X} {Λ : Measure X} {κ : Kernel X E}

/-- **Poisson marking theorem for an enumerated realization.** Independently marking any
measurable optional occurrence enumeration of a Poisson random measure of s-finite intensity `Λ`
produces a Poisson random measure of intensity `Λ ⊗ₘ κ`. No separation or topological
assumption on `X` is required. -/
theorem IsPoissonRandomMeasure.isPoissonRandomMeasure_comp_optionalTupleMarking
    [SFinite Λ] [IsMarkovKernel κ]
    (h : IsPoissonRandomMeasure P N Λ) {ι : Type*} [Countable ι]
    {e : Ω → ι → Option X} (he : Measurable e)
    (hrep : ∀ᵐ ω ∂P, N ω = Measure.sum fun i => (e ω i).elim 0 Measure.dirac) :
    IsPoissonRandomMeasure
      (((κ.optionalTupleMarking ι).comap e he) ∘ₘ P) id (Λ ⊗ₘ κ) := by
  let := h.isProbabilityMeasure
  let K : Kernel Ω (Measure (X × E)) := (κ.optionalTupleMarking ι).comap e he
  apply isPoissonRandomMeasure_of_laplaceFunctional measurable_id
  intro f hf
  let p : X → ℝ≥0∞ := fun a => ∫⁻ y, (ENNReal.expNeg (f (a, y)) : ℝ≥0∞) ∂κ a
  let g : X → ℝ≥0∞ := fun a => (-ENNReal.log (p a)).toENNReal
  have hp_meas : Measurable p :=
    (measurable_coe_nnreal_ennreal.comp
      (ENNReal.measurable_expNeg.comp hf)).lintegral_kernel_prod_right'
  have hg_meas : Measurable g :=
    ((ENNReal.continuous_log.measurable.comp hp_meas).neg).ereal_toENNReal
  have hp_le (a : X) : p a ≤ 1 := by
    calc
      p a ≤ ∫⁻ _ : E, (1 : ℝ≥0∞) ∂κ a := lintegral_mono fun y =>
        ENNReal.coe_le_one_iff.mpr (ENNReal.expNeg_le_one _)
      _ = 1 := by simp
  have hexp_g (a : X) : (ENNReal.expNeg (g a) : ℝ≥0∞) = p a := by
    have hnonneg : 0 ≤ -ENNReal.log (p a) :=
      EReal.neg_nonneg.mpr (by simpa using ENNReal.log_le_log_iff.mpr (hp_le a))
    rw [ENNReal.coe_expNeg, EReal.coe_toENNReal hnonneg, neg_neg, ENNReal.exp_log]
  have hsub (a : X) :
      1 - p a = ∫⁻ y, 1 - (ENNReal.expNeg (f (a, y)) : ℝ≥0∞) ∂κ a := by
    have hfa : Measurable (fun y : E => (ENNReal.expNeg (f (a, y)) : ℝ≥0∞)) :=
      measurable_coe_nnreal_ennreal.comp
        (ENNReal.measurable_expNeg.comp (hf.comp measurable_prodMk_left))
    have hfin : p a ≠ ∞ := (hp_le a).trans_lt ENNReal.one_lt_top |>.ne
    have hle : (fun y : E => (ENNReal.expNeg (f (a, y)) : ℝ≥0∞)) ≤ᵐ[κ a]
        (fun _ => (1 : ℝ≥0∞)) :=
      ae_of_all _ fun y => ENNReal.coe_le_one_iff.mpr (ENNReal.expNeg_le_one _)
    rw [lintegral_sub hfa hfin hle, lintegral_const, one_mul, measure_univ]
  have hL : (K ∘ₘ P).laplaceFunctional id f = P.laplaceFunctional N g := by
    have hexp_meas := Measure.measurable_expNeg_lintegral (N := (id : Measure (X × E) → _))
      measurable_id hf
    rw [Measure.laplaceFunctional_def, Measure.lintegral_bind K.aemeasurable hexp_meas.aemeasurable]
    calc
      ∫⁻ ω, ∫⁻ μ, (ENNReal.expNeg (∫⁻ q, f q ∂μ) : ℝ≥0∞) ∂K ω ∂P
          = ∫⁻ ω, (ENNReal.expNeg (∫⁻ a, g a ∂(Measure.sum fun i =>
              (e ω i).elim 0 Measure.dirac)) : ℝ≥0∞) ∂P := by
        refine lintegral_congr fun ω => ?_
        simpa only [K, Kernel.comap_apply, Measure.laplaceFunctional_def, id_eq] using
          κ.laplaceFunctional_optionalTupleMarking (e ω) hf
      _ = ∫⁻ ω, (ENNReal.expNeg (∫⁻ a, g a ∂N ω) : ℝ≥0∞) ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hrep] with ω hω
        rw [hω]
      _ = P.laplaceFunctional N g := (Measure.laplaceFunctional_def P N g).symm
  rw [hL, h.laplaceFunctional_eq_expNeg hg_meas]
  congr 2
  have hsub_meas : Measurable (fun q : X × E => 1 - (ENNReal.expNeg (f q) : ℝ≥0∞)) :=
    measurable_const.sub (measurable_coe_nnreal_ennreal.comp (ENNReal.measurable_expNeg.comp hf))
  rw [Measure.lintegral_compProd (f := fun q : X × E => 1 - (ENNReal.expNeg (f q) : ℝ≥0∞))
    hsub_meas]
  refine lintegral_congr fun a => ?_
  rw [hexp_g a, hsub a]

/-- Joint product-space form of the enumerated Poisson marking theorem. -/
theorem IsPoissonRandomMeasure.isPoissonRandomMeasure_compProd_optionalTupleMarking
    [SFinite Λ] [IsMarkovKernel κ]
    (h : IsPoissonRandomMeasure P N Λ) {ι : Type*} [Countable ι]
    {e : Ω → ι → Option X} (he : Measurable e)
    (hrep : ∀ᵐ ω ∂P, N ω = Measure.sum fun i => (e ω i).elim 0 Measure.dirac) :
    IsPoissonRandomMeasure (P ⊗ₘ ((κ.optionalTupleMarking ι).comap e he))
      Prod.snd (Λ ⊗ₘ κ) := by
  let := h.isProbabilityMeasure
  have hsnd : IdentDistrib Prod.snd (id : Measure (X × E) → Measure (X × E))
      (P ⊗ₘ ((κ.optionalTupleMarking ι).comap e he))
      (((κ.optionalTupleMarking ι).comap e he) ∘ₘ P) := by
    refine ⟨measurable_snd.aemeasurable, measurable_id.aemeasurable, ?_⟩
    rw [Measure.map_id, ← Measure.snd, Measure.snd_compProd]
  exact (h.isPoissonRandomMeasure_comp_optionalTupleMarking he hrep).of_identDistrib
    measurable_snd hsnd.symm

/-- Projecting a measurable acceptance region of a Poisson random measure with kernel intensity
`Λ ⊗ₘ κ` gives a Poisson random measure weighted by the kernel section masses. -/
theorem IsPoissonRandomMeasure.acceptance_compProd [SFinite Λ] [IsSFiniteKernel κ]
    {M : Ω → Measure (X × E)} (hM : IsPoissonRandomMeasure P M (Λ ⊗ₘ κ))
    {A : Set (X × E)} (hA : MeasurableSet A) :
    IsPoissonRandomMeasure P (fun ω => ((M ω).restrict A).map Prod.fst)
      (Λ.withDensity fun x => κ x (Prod.mk x ⁻¹' A)) := by
  simpa only [Measure.map_fst_restrict_compProd_eq_withDensity Λ κ hA] using
    (hM.restrict hA).map measurable_fst

/-- Selecting a measurable mark set from a Poisson random measure with kernel intensity
`Λ ⊗ₘ κ` and projecting onto the ground space weights `Λ` by `x ↦ κ x B`. -/
theorem IsPoissonRandomMeasure.acceptance_compProd_univ_prod [SFinite Λ] [IsSFiniteKernel κ]
    {M : Ω → Measure (X × E)} (hM : IsPoissonRandomMeasure P M (Λ ⊗ₘ κ))
    {B : Set E} (hB : MeasurableSet B) :
    IsPoissonRandomMeasure P (fun ω => ((M ω).restrict (univ ×ˢ B)).map Prod.fst)
      (Λ.withDensity fun x => κ x B) := by
  simpa only [mk_preimage_prod_right (mem_univ _)] using
    hM.acceptance_compProd (MeasurableSet.univ.prod hB)

private theorem map_fst_eq_of_cover_piSystem {C : Set (Set X)}
    (hgen : ‹MeasurableSpace X› = MeasurableSpace.generateFrom C)
    (hpi : IsPiSystem C) (huniv : univ ∈ C)
    {s : ℕ → Set X} (hs : ∀ n, MeasurableSet (s n)) (hcover : ⋃ n, s n = univ)
    {μ : Measure X} {ν : Measure (X × E)} (hfin : ∀ n, μ (s n) < ∞)
    (heq : ∀ n, ∀ A ∈ C, ν ((A ∩ s n) ×ˢ univ) = μ (A ∩ s n)) :
    ν.map Prod.fst = μ := by
  have hCmeas : ∀ A ∈ C, MeasurableSet A := fun A hA => by
    rw [hgen]
    exact MeasurableSpace.measurableSet_generateFrom hA
  symm
  refine Measure.ext_of_generateFrom_of_cover hgen (countable_range s) hpi
    (by rwa [sUnion_range]) (by rintro _ ⟨n, rfl⟩; exact (hfin n).ne)
    (by
      rintro _ ⟨n, rfl⟩ A hA
      rw [Measure.map_apply measurable_fst ((hCmeas A hA).inter (hs n)), ← prod_univ]
      exact (heq n A hA).symm)
    (by
      rintro _ ⟨n, rfl⟩
      have h := heq n univ huniv
      rw [univ_inter] at h
      rw [Measure.map_apply measurable_fst (hs n), ← prod_univ]
      exact h.symm)

end General

section StandardBorel

variable {Ω Ω' X E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace E]
  {P : Measure Ω} {P' : Measure Ω'} {N : Ω → Measure X} {Λ : Measure X} {κ : Kernel X E}

private theorem ae_map_fst_compProd_markingOfCover_aux [IsMarkovKernel κ]
    {hN : Measurable N} {s : ℕ → Set X}
    (hs : ∀ n, MeasurableSet (s n)) (hcover : ⋃ n, s n = univ)
    (hint : ∀ᵐ ω ∂P, (N ω).IsIntegerValued)
    (hfin : ∀ n, ∀ᵐ ω ∂P, N ω (s n) < ∞) :
    ∀ᵐ p ∂(P ⊗ₘ ((κ.markingOfCover hs hcover).comap N hN)),
      p.2.map Prod.fst = N p.1 := by
  classical
  obtain ⟨C, hcount, hpi, huniv, hgen⟩ :=
    MeasurableSpace.exists_countable_isPiSystem_generateFrom (α := X)
  have hCmeas : ∀ A ∈ C, MeasurableSet A := fun A hA => by
    rw [hgen]
    exact MeasurableSpace.measurableSet_generateFrom hA
  let Egood : Set (Ω × Measure (X × E)) :=
    {p | (∀ n, N p.1 (s n) < ∞) ∧
      ∀ n, ∀ A ∈ C, p.2 ((A ∩ s n) ×ˢ univ) = N p.1 (A ∩ s n)}
  have hEgood_meas : MeasurableSet Egood := by
    have h1 : MeasurableSet {p : Ω × Measure (X × E) | ∀ n, N p.1 (s n) < ∞} := by
      have : {p : Ω × Measure (X × E) | ∀ n, N p.1 (s n) < ∞} =
          ⋂ n, {p : Ω × Measure (X × E) | N p.1 (s n) < ∞} := by ext; simp
      rw [this]
      exact MeasurableSet.iInter fun n =>
        measurableSet_lt ((Measure.measurable_coe (hs n)).comp (hN.comp measurable_fst))
          measurable_const
    have h2 : MeasurableSet {p : Ω × Measure (X × E) |
        ∀ n, ∀ A ∈ C, p.2 ((A ∩ s n) ×ˢ univ) = N p.1 (A ∩ s n)} := by
      have : {p : Ω × Measure (X × E) |
            ∀ n, ∀ A ∈ C, p.2 ((A ∩ s n) ×ˢ univ) = N p.1 (A ∩ s n)} =
          ⋂ n, ⋂ A ∈ C, {p : Ω × Measure (X × E) |
            p.2 ((A ∩ s n) ×ˢ univ) = N p.1 (A ∩ s n)} := by ext; simp
      rw [this]
      refine MeasurableSet.iInter fun n => MeasurableSet.biInter hcount fun A hA => ?_
      exact measurableSet_eq_fun
        ((Measure.measurable_coe (((hCmeas A hA).inter (hs n)).prod MeasurableSet.univ)).comp
          measurable_snd)
        ((Measure.measurable_coe ((hCmeas A hA).inter (hs n))).comp (hN.comp measurable_fst))
    exact h1.inter h2
  have hae : ∀ᵐ p ∂(P ⊗ₘ ((κ.markingOfCover hs hcover).comap N hN)), p ∈ Egood := by
    refine Measure.ae_compProd_of_ae_ae hEgood_meas ?_
    filter_upwards [hint, ae_all_iff.mpr hfin] with ω hωint hωfin
    have hproj : ((κ.markingOfCover hs hcover) (N ω)).map (fun ν => ν.map Prod.fst) =
        Measure.dirac (N ω) :=
      κ.map_map_fst_markingOfCover hs hcover hωint (fun n => (hωfin n).ne)
    have hcoord (n : ℕ) (A : Set X) (hA : A ∈ C) :
        ∀ᵐ ν ∂((κ.markingOfCover hs hcover) (N ω)),
          ν ((A ∩ s n) ×ˢ univ) = N ω (A ∩ s n) := by
      have hm : MeasurableSet (A ∩ s n) := (hCmeas A hA).inter (hs n)
      have heval :
          ((κ.markingOfCover hs hcover) (N ω)).map (fun ν => ν ((A ∩ s n) ×ˢ univ)) =
            Measure.dirac (N ω (A ∩ s n)) := by
        have hcomp : (fun ν : Measure (X × E) => ν ((A ∩ s n) ×ˢ univ)) =
            (fun μ : Measure X => μ (A ∩ s n)) ∘
              (fun ν : Measure (X × E) => ν.map Prod.fst) := by
          funext ν
          simp only [Function.comp_apply, Measure.map_apply measurable_fst hm, ← prod_univ]
        rw [hcomp, ← Measure.map_map (Measure.measurable_coe hm)
          (Measure.measurable_map _ measurable_fst), hproj,
          Measure.map_dirac' (Measure.measurable_coe hm)]
      have hlaw : HasLaw (fun ν : Measure (X × E) => ν ((A ∩ s n) ×ˢ univ))
          (Measure.dirac (N ω (A ∩ s n))) ((κ.markingOfCover hs hcover) (N ω)) :=
        ⟨(Measure.measurable_coe (hm.prod MeasurableSet.univ)).aemeasurable, heval⟩
      exact hlaw.ae_eq_of_dirac
    have hall : ∀ᵐ ν ∂((κ.markingOfCover hs hcover) (N ω)),
        ∀ n, ∀ A ∈ C, ν ((A ∩ s n) ×ˢ univ) = N ω (A ∩ s n) :=
      ae_all_iff.mpr fun n => (ae_ball_iff hcount).mpr fun A hA => hcoord n A hA
    filter_upwards [hall] with ν hν
    exact ⟨hωfin, hν⟩
  exact hae.mono fun _ ⟨hωfin, hωeq⟩ =>
    map_fst_eq_of_cover_piSystem hgen hpi huniv hs hcover hωfin hωeq

/-- **Poisson marking theorem via `Kernel.markingOfCover`.** On a standard Borel space,
independently marking a Poisson random measure of sigma-finite intensity `Λ` using any
finite-intensity measurable cover produces a Poisson random measure of intensity `Λ ⊗ₘ κ`. -/
theorem IsPoissonRandomMeasure.isPoissonRandomMeasure_comp_markingOfCover
    [SigmaFinite Λ] [IsMarkovKernel κ] (h : IsPoissonRandomMeasure P N Λ)
    {s : ℕ → Set X} (hs : ∀ n, MeasurableSet (s n)) (hcover : ⋃ n, s n = univ)
    (hΛ : ∀ n, Λ (s n) < ∞) :
    IsPoissonRandomMeasure ((κ.markingOfCover hs hcover) ∘ₘ (P.map N)) id (Λ ⊗ₘ κ) := by
  let := h.isProbabilityMeasure
  let e : Measure X → ℕ → Option X :=
    (Measure.exists_occurrence_enumeration_of_cover hs hcover).choose
  have he : Measurable e :=
    (Measure.exists_occurrence_enumeration_of_cover hs hcover).choose_spec.1
  have hrep : ∀ᵐ ω ∂P, N ω = Measure.sum fun n => (e (N ω) n).elim 0 Measure.dirac := by
    have hfin : ∀ n, ∀ᵐ ω ∂P, N ω (s n) < ∞ := fun n => h.ae_lt_top (hs n) (hΛ n)
    filter_upwards [h.ae_isIntegerValued, ae_all_iff.mpr hfin] with ω hωint hωfin
    exact (Measure.exists_occurrence_enumeration_of_cover hs hcover).choose_spec.2.1
      (N ω) hωint (fun n => (hωfin n).ne)
  have hcomp : (κ.markingOfCover hs hcover) ∘ₘ (P.map N) =
      ((κ.optionalTupleMarking ℕ).comap (e ∘ N) (he.comp h.measurable)) ∘ₘ P := by
    ext A hA
    rw [Measure.bind_apply hA (κ.markingOfCover hs hcover).aemeasurable,
      Measure.bind_apply hA (Kernel.aemeasurable _),
      lintegral_map ((κ.markingOfCover hs hcover).measurable_coe hA) h.measurable]
    refine lintegral_congr_ae ?_
    have hfin : ∀ n, ∀ᵐ ω ∂P, N ω (s n) < ∞ := fun n => h.ae_lt_top (hs n) (hΛ n)
    filter_upwards [h.ae_isIntegerValued, ae_all_iff.mpr hfin, hrep] with ω hωint hωfin hωrep
    simp only [Kernel.comap_apply, Function.comp_apply]
    rw [κ.markingOfCover_eq_optionalTupleMarking hs hcover hωint (fun n => (hωfin n).ne) hωrep]
  rw [hcomp]
  exact h.isPoissonRandomMeasure_comp_optionalTupleMarking (he.comp h.measurable) hrep

/-- Joint realization of independent marking on `Ω × Measure (X × E)` via `markingOfCover`:
the second coordinate is a Poisson random measure of intensity `Λ ⊗ₘ κ`. -/
theorem IsPoissonRandomMeasure.isPoissonRandomMeasure_compProd_markingOfCover
    [SigmaFinite Λ] [IsMarkovKernel κ] (h : IsPoissonRandomMeasure P N Λ)
    {s : ℕ → Set X} (hs : ∀ n, MeasurableSet (s n)) (hcover : ⋃ n, s n = univ)
    (hΛ : ∀ n, Λ (s n) < ∞) :
    IsPoissonRandomMeasure (P ⊗ₘ ((κ.markingOfCover hs hcover).comap N h.measurable))
      Prod.snd (Λ ⊗ₘ κ) := by
  let := h.isProbabilityMeasure
  have hmap : (P ⊗ₘ ((κ.markingOfCover hs hcover).comap N h.measurable)).map Prod.snd =
      (κ.markingOfCover hs hcover) ∘ₘ (P.map N) := by
    rw [← Measure.snd, Measure.snd_compProd]
    ext A hA
    rw [Measure.bind_apply hA (Kernel.aemeasurable _),
      Measure.bind_apply hA (κ.markingOfCover hs hcover).aemeasurable,
      lintegral_map ((κ.markingOfCover hs hcover).measurable_coe hA) h.measurable]
    rfl
  have hid : IdentDistrib Prod.snd (id : Measure (X × E) → Measure (X × E))
      (P ⊗ₘ ((κ.markingOfCover hs hcover).comap N h.measurable))
      ((κ.markingOfCover hs hcover) ∘ₘ (P.map N)) :=
    ⟨measurable_snd.aemeasurable, measurable_id.aemeasurable, by rw [Measure.map_id, hmap]⟩
  exact (h.isPoissonRandomMeasure_comp_markingOfCover hs hcover hΛ).of_identDistrib
    measurable_snd hid.symm

/-- On the joint marking space `Ω × Measure (X × E)`, forgetting marks almost surely recovers
the original Poisson realization `N`. -/
theorem IsPoissonRandomMeasure.ae_map_fst_compProd_markingOfCover
    [SigmaFinite Λ] [IsMarkovKernel κ] (h : IsPoissonRandomMeasure P N Λ)
    {s : ℕ → Set X} (hs : ∀ n, MeasurableSet (s n)) (hcover : ⋃ n, s n = univ)
    (hΛ : ∀ n, Λ (s n) < ∞) :
    ∀ᵐ p ∂(P ⊗ₘ ((κ.markingOfCover hs hcover).comap N h.measurable)),
      p.2.map Prod.fst = N p.1 :=
  ae_map_fst_compProd_markingOfCover_aux hs hcover h.ae_isIntegerValued
    (fun n => h.ae_lt_top (hs n) (hΛ n))

/-- Any measurable random measure whose law equals the independently marked law of `N` is a
Poisson random measure with intensity `Λ ⊗ₘ κ`. -/
theorem IsPoissonRandomMeasure.isPoissonRandomMeasure_of_hasLaw_comp_markingOfCover
    [SigmaFinite Λ] [IsMarkovKernel κ] (h : IsPoissonRandomMeasure P N Λ)
    {s : ℕ → Set X} (hs : ∀ n, MeasurableSet (s n)) (hcover : ⋃ n, s n = univ)
    (hΛ : ∀ n, Λ (s n) < ∞) {M : Ω' → Measure (X × E)} (hM : Measurable M)
    (hLaw : HasLaw M ((κ.markingOfCover hs hcover) ∘ₘ (P.map N)) P') :
    IsPoissonRandomMeasure P' M (Λ ⊗ₘ κ) := by
  have hid : IdentDistrib (id : Measure (X × E) → Measure (X × E)) M
      ((κ.markingOfCover hs hcover) ∘ₘ (P.map N)) P' :=
    ⟨measurable_id.aemeasurable, hM.aemeasurable, by rw [Measure.map_id, hLaw.map_eq]⟩
  exact (h.isPoissonRandomMeasure_comp_markingOfCover hs hcover hΛ).of_identDistrib hM hid

/-- If `(N, M)` on an arbitrary probability space has joint law `(P.map N) ⊗ₘ κ.markingOfCover`,
then `M` is a Poisson random measure of intensity `Λ ⊗ₘ κ` and its ground projection equals
`N` almost surely. -/
theorem IsPoissonRandomMeasure.of_map_prod_eq_compProd_markingOfCover
    [SigmaFinite Λ] [IsMarkovKernel κ] (h : IsPoissonRandomMeasure P N Λ)
    {s : ℕ → Set X} (hs : ∀ n, MeasurableSet (s n)) (hcover : ⋃ n, s n = univ)
    (hΛ : ∀ n, Λ (s n) < ∞) {M : Ω → Measure (X × E)} (hM : Measurable M)
    (hjoint : P.map (fun ω => (N ω, M ω)) = (P.map N) ⊗ₘ (κ.markingOfCover hs hcover)) :
    IsPoissonRandomMeasure P M (Λ ⊗ₘ κ) ∧ ∀ᵐ ω ∂P, (M ω).map Prod.fst = N ω := by
  let := h.isProbabilityMeasure
  have hlaw : HasLaw M ((κ.markingOfCover hs hcover) ∘ₘ (P.map N)) P := by
    refine ⟨hM.aemeasurable, ?_⟩
    have hcomp : M = Prod.snd ∘ (fun ω => (N ω, M ω)) := rfl
    rw [hcomp, ← Measure.map_map measurable_snd (h.measurable.prodMk hM), hjoint,
      ← Measure.snd, Measure.snd_compProd]
  refine ⟨h.isPoissonRandomMeasure_of_hasLaw_comp_markingOfCover hs hcover hΛ hM hlaw, ?_⟩
  classical
  obtain ⟨C, hcount, hpi, huniv, hgen⟩ :=
    MeasurableSpace.exists_countable_isPiSystem_generateFrom (α := X)
  have hCmeas : ∀ A ∈ C, MeasurableSet A := fun A hA => by
    rw [hgen]
    exact MeasurableSpace.measurableSet_generateFrom hA
  have hfin : ∀ n, ∀ᵐ ω ∂P, N ω (s n) < ∞ := fun n => h.ae_lt_top (hs n) (hΛ n)
  have hcomp_proj : ∀ᵐ p ∂((P.map N) ⊗ₘ (κ.markingOfCover hs hcover)),
      p.2.map Prod.fst = p.1 := by
    have hNid : IsPoissonRandomMeasure (P.map N) id Λ :=
      h.of_identDistrib measurable_id
        ⟨h.measurable.aemeasurable, measurable_id.aemeasurable, by rw [Measure.map_id]⟩
    have htmp := hNid.ae_map_fst_compProd_markingOfCover (κ := κ) hs hcover hΛ
    rwa [Kernel.comap_id] at htmp
  have hcoord (n : ℕ) (A : Set X) (hA : A ∈ C) :
      ∀ᵐ ω ∂P, M ω ((A ∩ s n) ×ˢ univ) = N ω (A ∩ s n) := by
    have hm : MeasurableSet (A ∩ s n) := (hCmeas A hA).inter (hs n)
    have hset : MeasurableSet {p : Measure X × Measure (X × E) |
        p.2 ((A ∩ s n) ×ˢ univ) = p.1 (A ∩ s n)} :=
      measurableSet_eq_fun
        ((Measure.measurable_coe (hm.prod MeasurableSet.univ)).comp measurable_snd)
        ((Measure.measurable_coe hm).comp measurable_fst)
    have hpair : ∀ᵐ p ∂(P.map fun ω => (N ω, M ω)),
        p.2 ((A ∩ s n) ×ˢ univ) = p.1 (A ∩ s n) := by
      rw [hjoint]
      filter_upwards [hcomp_proj] with p hp
      rw [← hp, Measure.map_apply measurable_fst hm, ← prod_univ]
    exact (ae_map_iff (h.measurable.prodMk hM).aemeasurable hset).mp hpair
  filter_upwards [ae_all_iff.mpr hfin,
    ae_all_iff.mpr fun n => (ae_ball_iff hcount).mpr fun A hA => hcoord n A hA] with ω hωfin hωeq
  exact map_fst_eq_of_cover_piSystem hgen hpi huniv hs hcover hωfin hωeq

/-- **Existence of a joint independent marking** of any Poisson random measure on a standard Borel
space with sigma-finite intensity `Λ`, without topological or local-finiteness hypotheses. -/
theorem IsPoissonRandomMeasure.exists_independent_marking [SigmaFinite Λ] [IsMarkovKernel κ]
    (h : IsPoissonRandomMeasure P N Λ) :
    ∃ P' : Measure (Ω × Measure (X × E)),
      MeasurePreserving Prod.fst P' P ∧
      IsPoissonRandomMeasure P' Prod.snd (Λ ⊗ₘ κ) ∧
      ∀ᵐ p ∂P', p.2.map Prod.fst = N p.1 := by
  let := h.isProbabilityMeasure
  let hs := measurableSet_spanningSets Λ
  let hcover := iUnion_spanningSets Λ
  let hΛ := measure_spanningSets_lt_top Λ
  refine ⟨P ⊗ₘ ((κ.markingOfCover hs hcover).comap N h.measurable),
    ⟨measurable_fst,
      Measure.fst_compProd P ((κ.markingOfCover hs hcover).comap N h.measurable)⟩,
    h.isPoissonRandomMeasure_compProd_markingOfCover hs hcover hΛ,
    h.ae_map_fst_compProd_markingOfCover hs hcover hΛ⟩

/-- **Independent location-dependent `p`-thinning (Last–Penrose Corollary 5.9).** Any Poisson
random measure of sigma-finite intensity `Λ` on a standard Borel space splits on a
measure-preserving extension into two independent Poisson random measures with densities `p` and
`1 - p` summing to `N` almost surely. Endpoint values `0` and `1` and zero intensity are allowed. -/
theorem IsPoissonRandomMeasure.exists_independent_thinning [SigmaFinite Λ]
    (h : IsPoissonRandomMeasure P N Λ) {p : X → unitInterval} (hp : Measurable p) :
    ∃ P' : Measure (Ω × Measure (X × Bool)),
      MeasurePreserving Prod.fst P' P ∧
      IndepFun (fun q => (q.2.restrict (univ ×ˢ {true})).map Prod.fst)
        (fun q => (q.2.restrict (univ ×ˢ {false})).map Prod.fst) P' ∧
      IsPoissonRandomMeasure P' (fun q => (q.2.restrict (univ ×ˢ {true})).map Prod.fst)
        (Λ.withDensity fun x => (unitInterval.toNNReal (p x) : ℝ≥0∞)) ∧
      IsPoissonRandomMeasure P' (fun q => (q.2.restrict (univ ×ˢ {false})).map Prod.fst)
        (Λ.withDensity fun x => (unitInterval.toNNReal (unitInterval.symm (p x)) : ℝ≥0∞)) ∧
      ∀ᵐ q ∂P',
        ((q.2.restrict (univ ×ˢ {true})).map Prod.fst) +
          ((q.2.restrict (univ ×ˢ {false})).map Prod.fst) = N q.1 := by
  obtain ⟨P', hmp, hM, hproj⟩ :=
    h.exists_independent_marking (κ := Kernel.bernoulli true false hp)
  have hcompl : ({true}ᶜ : Set Bool) = {false} := by ext b; cases b <;> simp
  have htrue : IsPoissonRandomMeasure P' (fun q => (q.2.restrict (univ ×ˢ {true})).map Prod.fst)
      (Λ.withDensity fun x => (unitInterval.toNNReal (p x) : ℝ≥0∞)) := by
    simpa [Kernel.bernoulli_apply] using
      hM.acceptance_compProd_univ_prod (B := {true}) (measurableSet_singleton true)
  have hfalse : IsPoissonRandomMeasure P' (fun q => (q.2.restrict (univ ×ˢ {false})).map Prod.fst)
      (Λ.withDensity fun x => (unitInterval.toNNReal (unitInterval.symm (p x)) : ℝ≥0∞)) := by
    simpa [Kernel.bernoulli_apply] using
      hM.acceptance_compProd_univ_prod (B := {false}) (measurableSet_singleton false)
  refine ⟨P', hmp,
    hM.indepFun_map_fst_restrict_univ_prod (measurableSet_singleton true)
      (measurableSet_singleton false) (disjoint_singleton.mpr (by decide)),
    htrue, hfalse, ?_⟩
  filter_upwards [hproj] with q hq
  have hsum := q.2.map_fst_restrict_univ_prod_add_compl (measurableSet_singleton true)
  rw [hcompl, hq] at hsum
  exact hsum

/-- **Independent constant `p`-thinning** of a Poisson random measure on a standard Borel space
with sigma-finite intensity `Λ`, including `p = 0`, `p = 1`, and `Λ = 0`. -/
theorem IsPoissonRandomMeasure.exists_independent_thinning_const [SigmaFinite Λ]
    (h : IsPoissonRandomMeasure P N Λ) (p : unitInterval) :
    ∃ P' : Measure (Ω × Measure (X × Bool)),
      MeasurePreserving Prod.fst P' P ∧
      IndepFun (fun q => (q.2.restrict (univ ×ˢ {true})).map Prod.fst)
        (fun q => (q.2.restrict (univ ×ˢ {false})).map Prod.fst) P' ∧
      IsPoissonRandomMeasure P' (fun q => (q.2.restrict (univ ×ˢ {true})).map Prod.fst)
        ((unitInterval.toNNReal p : ℝ≥0∞) • Λ) ∧
      IsPoissonRandomMeasure P' (fun q => (q.2.restrict (univ ×ˢ {false})).map Prod.fst)
        (((1 - unitInterval.toNNReal p : ℝ≥0) : ℝ≥0∞) • Λ) ∧
      ∀ᵐ q ∂P',
        ((q.2.restrict (univ ×ˢ {true})).map Prod.fst) +
          ((q.2.restrict (univ ×ˢ {false})).map Prod.fst) = N q.1 := by
  obtain ⟨P', hmp, hind, htrue, hfalse, hsum⟩ :=
    h.exists_independent_thinning (p := fun _ => p) measurable_const
  have hsymm : unitInterval.toNNReal (unitInterval.symm p) = 1 - unitInterval.toNNReal p :=
    eq_tsub_of_add_eq (unitInterval.toNNReal_symm_add_toNNReal p)
  rw [withDensity_const] at htrue hfalse
  rw [hsymm] at hfalse
  exact ⟨P', hmp, hind, htrue, hfalse, hsum⟩

end StandardBorel

section CompactCovering

variable {Ω Ω' X E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  [TopologicalSpace X] [T2Space X] [SigmaCompactSpace X]
  [MeasurableSpace X] [OpensMeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace E] {P : Measure Ω} {P' : Measure Ω'}
  {N : Ω → Measure X} {Λ : Measure X} {κ : Kernel X E}

/-- Canonical cover-free Poisson marking theorem on a sigma-compact Hausdorff standard Borel
space for any intensity finite on compact sets. -/
theorem IsPoissonRandomMeasure.isPoissonRandomMeasure_comp_marking
    [IsFiniteMeasureOnCompacts Λ] [IsMarkovKernel κ]
    (h : IsPoissonRandomMeasure P N Λ) :
    IsPoissonRandomMeasure (κ.marking ∘ₘ (P.map N)) id (Λ ⊗ₘ κ) := by
  rw [κ.marking_eq_markingOfCover_compactCovering]
  exact h.isPoissonRandomMeasure_comp_markingOfCover
    (fun n => (isCompact_compactCovering X n).measurableSet) (iUnion_compactCovering X)
    (fun n => (isCompact_compactCovering X n).measure_lt_top)

/-- Canonical joint marking on `Ω × Measure (X × E)` using `Kernel.marking`. -/
theorem IsPoissonRandomMeasure.isPoissonRandomMeasure_compProd_marking
    [IsFiniteMeasureOnCompacts Λ] [IsMarkovKernel κ]
    (h : IsPoissonRandomMeasure P N Λ) :
    IsPoissonRandomMeasure
      (P ⊗ₘ (κ.marking.comap N h.measurable)) Prod.snd (Λ ⊗ₘ κ) := by
  rw [κ.marking_eq_markingOfCover_compactCovering]
  exact h.isPoissonRandomMeasure_compProd_markingOfCover
    (fun n => (isCompact_compactCovering X n).measurableSet) (iUnion_compactCovering X)
    (fun n => (isCompact_compactCovering X n).measure_lt_top)

/-- On the canonical joint marking space, forgetting marks recovers `N` almost surely. -/
theorem IsPoissonRandomMeasure.ae_map_fst_compProd_marking
    [IsFiniteMeasureOnCompacts Λ] [IsMarkovKernel κ]
    (h : IsPoissonRandomMeasure P N Λ) :
    ∀ᵐ p ∂(P ⊗ₘ (κ.marking.comap N h.measurable)), p.2.map Prod.fst = N p.1 := by
  rw [κ.marking_eq_markingOfCover_compactCovering]
  exact h.ae_map_fst_compProd_markingOfCover
    (fun n => (isCompact_compactCovering X n).measurableSet) (iUnion_compactCovering X)
    (fun n => (isCompact_compactCovering X n).measure_lt_top)

/-- Any measurable random measure with law `κ.marking ∘ₘ (P.map N)` is Poisson with intensity
`Λ ⊗ₘ κ`. -/
theorem IsPoissonRandomMeasure.isPoissonRandomMeasure_of_hasLaw_comp_marking
    [IsFiniteMeasureOnCompacts Λ] [IsMarkovKernel κ]
    (h : IsPoissonRandomMeasure P N Λ) {M : Ω' → Measure (X × E)} (hM : Measurable M)
    (hLaw : HasLaw M (κ.marking ∘ₘ (P.map N)) P') :
    IsPoissonRandomMeasure P' M (Λ ⊗ₘ κ) := by
  rw [κ.marking_eq_markingOfCover_compactCovering] at hLaw
  exact h.isPoissonRandomMeasure_of_hasLaw_comp_markingOfCover
    (fun n => (isCompact_compactCovering X n).measurableSet) (iUnion_compactCovering X)
    (fun n => (isCompact_compactCovering X n).measure_lt_top) hM hLaw

/-- If `(N, M)` has joint law `(P.map N) ⊗ₘ κ.marking`, then `M` is a Poisson random measure of
intensity `Λ ⊗ₘ κ` whose ground projection equals `N` almost surely. -/
theorem IsPoissonRandomMeasure.of_map_prod_eq_compProd_marking
    [IsFiniteMeasureOnCompacts Λ] [IsMarkovKernel κ]
    (h : IsPoissonRandomMeasure P N Λ) {M : Ω → Measure (X × E)} (hM : Measurable M)
    (hjoint : P.map (fun ω => (N ω, M ω)) = (P.map N) ⊗ₘ κ.marking) :
    IsPoissonRandomMeasure P M (Λ ⊗ₘ κ) ∧ ∀ᵐ ω ∂P, (M ω).map Prod.fst = N ω := by
  rw [κ.marking_eq_markingOfCover_compactCovering] at hjoint
  exact h.of_map_prod_eq_compProd_markingOfCover
    (fun n => (isCompact_compactCovering X n).measurableSet) (iUnion_compactCovering X)
    (fun n => (isCompact_compactCovering X n).measure_lt_top) hM hjoint

/-- Independent i.i.d. marking with mark distribution `Q` produces product intensity `Λ.prod Q`. -/
theorem IsPoissonRandomMeasure.isPoissonRandomMeasure_compProd_marking_const
    [IsFiniteMeasureOnCompacts Λ] {Q : Measure E} [IsProbabilityMeasure Q]
    (h : IsPoissonRandomMeasure P N Λ) :
    IsPoissonRandomMeasure (P ⊗ₘ ((Kernel.const X Q).marking.comap N h.measurable))
      Prod.snd (Λ.prod Q) := by
  simpa only [Measure.compProd_const] using
    h.isPoissonRandomMeasure_compProd_marking (κ := Kernel.const X Q)

/-- On the canonical joint marking space `P' := P ⊗ₘ (κ.marking.comap N h.measurable)`, the
pair `(N ∘ Prod.fst, Prod.snd)` has joint law `(P'.map (N ∘ Prod.fst)) ⊗ₘ κ.marking`. -/
theorem IsPoissonRandomMeasure.map_prod_compProd_marking [IsMarkovKernel κ]
    (h : IsPoissonRandomMeasure P N Λ) :
    (P ⊗ₘ (κ.marking.comap N h.measurable)).map (fun q => (N q.1, q.2)) =
      ((P ⊗ₘ (κ.marking.comap N h.measurable)).map (N ∘ Prod.fst)) ⊗ₘ κ.marking := by
  let := h.isProbabilityMeasure
  have hf : (P ⊗ₘ (κ.marking.comap N h.measurable)).map (N ∘ Prod.fst) = P.map N := by
    rw [← Measure.map_map h.measurable measurable_fst, ← Measure.fst, Measure.fst_compProd]
  rw [hf]
  exact P.map_prodMap_compProd_comap κ.marking h.measurable

end CompactCovering

end TauCeti.Probability
