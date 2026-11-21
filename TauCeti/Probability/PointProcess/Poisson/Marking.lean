/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import TauCeti.Probability.PointProcess.Marking.Measure
public import TauCeti.Probability.PointProcess.Marking.Optional
public import TauCeti.Probability.PointProcess.Poisson.Acceptance
public import TauCeti.Probability.PointProcess.Poisson.Basic
public import TauCeti.Probability.PointProcess.Poisson.Independence
import Mathlib.Data.Bool.Set
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Mathlib.Probability.Kernel.MeasurableLIntegral
import TauCeti.MeasureTheory.Integral.Lebesgue.ExpNeg
import TauCeti.MeasureTheory.Measure.IntegerValued.Enumeration.LocallyFinite
import TauCeti.Probability.PointProcess.Poisson.IntegerValued
import TauCeti.Probability.PointProcess.Poisson.Laplace
import TauCeti.Probability.PointProcess.Poisson.LaplaceCharacterization
import TauCeti.Topology.UnitInterval.NNReal

/-!
# The Poisson marking theorem and independent thinning

Independently marking the occurrences of a Poisson random measure `N` of intensity `Λ` using a
Markov kernel `κ : Kernel X E` produces a Poisson random measure on `X × E` with intensity
`Λ ⊗ₘ κ`, whose ground projection recovers `N` almost surely.

The theorem is proved at three levels of generality:

* Given any measurable optional occurrence enumeration `e : Ω → ι → Option X` representing `N`
  almost everywhere, `IsPoissonRandomMeasure.compProd_optionalTupleMarking` and
  `IsPoissonRandomMeasure.bind_optionalTupleMarking` yield a Poisson random measure of intensity
  `Λ ⊗ₘ κ` for any s-finite intensity `Λ`, with no separation or topological assumption on `X`.
* On any standard Borel space `X` with sigma-finite intensity `Λ`,
  `IsPoissonRandomMeasure.exists_isMarkovKernel_marking` gives an existential realization-level
  marking kernel, while intrinsic marking via `Kernel.markingOfCover` gives the marked law,
  the joint realization on `Ω × Measure (X × E)` with almost-sure ground projection
  `p.2.map Prod.fst = N p.1`, and transfer to any realization on an arbitrary probability space
  with that joint or marginal law.
* On a sigma-compact Hausdorff standard Borel space with intensity finite on compact sets, the
  canonical cover-free `Kernel.marking` applies directly; for constant mark kernel
  `Kernel.const X Q`, the intensity reduces to `Λ.prod Q`.

Combining independent marking with the acceptance-region and disjoint-mark independence APIs
(`Poisson.Acceptance`, `Poisson.Independence`) yields independent Bernoulli thinning: an uncoloured
Poisson random measure splits into two independent Poisson random measures with intensities
`Λ.withDensity p` and `Λ.withDensity (1 - p)` summing to `N` almost surely, including constant
thinning and explicit boundary characterizations when a colour or mark set has zero intensity
(covering `p = 0`, `p = 1`, and `Λ = 0`).

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Theorem 5.6 (Marking Theorem) and Corollary 5.9 (Thinning).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

section Enumeration

variable {Ω X E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace E]
  [Countable ι] {P : Measure Ω} {N : Ω → Measure X} {Λ : Measure X}

/-- **Enumeration-relative Poisson Marking Theorem.** Independently marking an almost-everywhere
optional occurrence enumeration of a Poisson random measure with s-finite intensity `Λ` by a
Markov kernel `κ` produces a Poisson random measure with intensity `Λ ⊗ₘ κ`. Neither standard
Borel structure on `X` nor simplicity of `N` is required. -/
theorem IsPoissonRandomMeasure.compProd_optionalTupleMarking [SFinite Λ]
    (hN : IsPoissonRandomMeasure P N Λ) (κ : Kernel X E) [IsMarkovKernel κ]
    {e : Ω → ι → Option X} (he : Measurable e)
    (hae : ∀ᵐ ω ∂P, N ω = Measure.sum (fun i ↦ (e ω i).elim 0 Measure.dirac)) :
    IsPoissonRandomMeasure (P ⊗ₘ (κ.optionalTupleMarking ι).comap e he) Prod.snd (Λ ⊗ₘ κ) := by
  let := hN.isProbabilityMeasure
  refine isPoissonRandomMeasure_of_laplaceFunctional measurable_snd fun f hf ↦ ?_
  rw [Measure.laplaceFunctional_def, Measure.lintegral_compProd (by fun_prop)]
  simp_rw [Kernel.comap_apply,
    Kernel.lintegral_expNeg_optionalTupleMarking_eq_expNeg_lintegral κ _ hf]
  rw [lintegral_congr_ae (hae.mono fun ω hω ↦ by rw [← hω]),
    ← Measure.laplaceFunctional_def, hN.laplaceFunctional_eq_expNeg (by fun_prop),
    Measure.lintegral_compProd (by fun_prop)]
  congr 2
  refine lintegral_congr fun a ↦ ?_
  have hle := lintegral_coe_expNeg_le_one (μ := κ a) fun b ↦ f (a, b)
  rw [ENNReal.coe_expNeg_toENNReal_neg_log hle,
    lintegral_sub (by fun_prop) (hle.trans_lt ENNReal.one_lt_top).ne
      (ae_of_all _ fun _ ↦ ENNReal.coe_le_one_iff.mpr (ENNReal.expNeg_le_one _)),
    lintegral_const, measure_univ, one_mul]

/-- Marginal form of `IsPoissonRandomMeasure.compProd_optionalTupleMarking`: the mixture of
marked laws over `P` along an almost-everywhere measurable optional enumeration is a canonical
Poisson random measure on `Measure (X × E)` with intensity `Λ ⊗ₘ κ`. -/
theorem IsPoissonRandomMeasure.bind_optionalTupleMarking [SFinite Λ]
    (hN : IsPoissonRandomMeasure P N Λ) (κ : Kernel X E) [IsMarkovKernel κ]
    {e : Ω → ι → Option X} (he : AEMeasurable e P)
    (hae : ∀ᵐ ω ∂P, N ω = Measure.sum (fun i ↦ (e ω i).elim 0 Measure.dirac)) :
    IsPoissonRandomMeasure (P.bind fun ω ↦ κ.optionalTupleMarking ι (e ω)) id (Λ ⊗ₘ κ) := by
  let := hN.isProbabilityMeasure
  have hbind : (P.bind fun ω ↦ κ.optionalTupleMarking ι (e ω)) =
      P.bind fun ω ↦ κ.optionalTupleMarking ι (he.mk e ω) :=
    Measure.bind_congr_right (he.ae_eq_mk.mono fun _ hω ↦ congrArg (κ.optionalTupleMarking ι) hω)
  rw [hbind]
  let η := (κ.optionalTupleMarking ι).comap (he.mk e) he.measurable_mk
  have hmap : (P ⊗ₘ η).map Prod.snd = P.bind (fun ω ↦ κ.optionalTupleMarking ι (he.mk e ω)) := by
    rw [← Measure.snd, Measure.snd_compProd]
    simp only [η, Kernel.coe_comap, Function.comp_def]
  have hae' : ∀ᵐ ω ∂P, N ω = Measure.sum (fun i ↦ (he.mk e ω i).elim 0 Measure.dirac) := by
    filter_upwards [hae, he.ae_eq_mk] with ω hω hmk
    simpa only [← hmk] using hω
  exact (hN.compProd_optionalTupleMarking κ he.measurable_mk hae').of_identDistrib measurable_id
    ⟨measurable_snd.aemeasurable, measurable_id.aemeasurable, by rw [Measure.map_id, hmap]⟩

/-- On a countably generated ground space with σ-finite intensity `Λ`, projecting an optional-tuple
marked realization onto the first coordinate recovers the entire ground realization `N z.1` almost
surely. -/
theorem IsPoissonRandomMeasure.ae_map_fst_compProd_optionalTupleMarking
    [MeasurableSpace.CountablyGenerated X] [SigmaFinite Λ]
    (hN : IsPoissonRandomMeasure P N Λ) (κ : Kernel X E) [IsMarkovKernel κ]
    {e : Ω → ι → Option X} (he : Measurable e)
    (hae : ∀ᵐ ω ∂P, N ω = Measure.sum (fun i ↦ (e ω i).elim 0 Measure.dirac)) :
    ∀ᵐ z ∂(P ⊗ₘ (κ.optionalTupleMarking ι).comap e he), z.2.map Prod.fst = N z.1 :=
  κ.ae_map_fst_compProd_optionalTupleMarking he hae (measurableSet_spanningSets Λ)
    (iUnion_spanningSets Λ) hN.ae_ne_top_spanningSets

end Enumeration

section General

variable {Ω X E : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace E]
  {P : Measure Ω} {N : Ω → Measure X} {Λ : Measure X} {κ : Kernel X E}

/-- **Independent location-dependent Bernoulli thinning from a marked Poisson realization.**
Given any Poisson random measure `M` on `X × Bool` with intensity
`Λ ⊗ₘ Kernel.bernoulli true false hp` whose ground projection recovers `N` almost surely, its
`true` and `false` projections are independent Poisson random measures with intensities
`Λ.withDensity p` and `Λ.withDensity (unitInterval.symm ∘ p)` summing to `N` almost surely. -/
theorem IsPoissonRandomMeasure.indepFun_and_isPoissonRandomMeasure_of_compProd_bernoulli
    [SFinite Λ] {M : Ω → Measure (X × Bool)} {p : X → unitInterval} {hp : Measurable p}
    (hM : IsPoissonRandomMeasure P M (Λ ⊗ₘ Kernel.bernoulli true false hp))
    (hproj : ∀ᵐ ω ∂P, (M ω).map Prod.fst = N ω) :
    IndepFun (fun ω => ((M ω).restrict (univ ×ˢ {true})).map Prod.fst)
      (fun ω => ((M ω).restrict (univ ×ˢ {false})).map Prod.fst) P ∧
    IsPoissonRandomMeasure P (fun ω => ((M ω).restrict (univ ×ˢ {true})).map Prod.fst)
      (Λ.withDensity fun x => (unitInterval.toNNReal (p x) : ℝ≥0∞)) ∧
    IsPoissonRandomMeasure P (fun ω => ((M ω).restrict (univ ×ˢ {false})).map Prod.fst)
      (Λ.withDensity fun x => (unitInterval.toNNReal (unitInterval.symm (p x)) : ℝ≥0∞)) ∧
    ∀ᵐ ω ∂P,
      ((M ω).restrict (univ ×ˢ {true})).map Prod.fst +
        ((M ω).restrict (univ ×ˢ {false})).map Prod.fst = N ω :=
  ⟨hM.indepFun_map_fst_restrict_univ_prod (measurableSet_singleton true)
      (measurableSet_singleton false) (disjoint_singleton.mpr (by decide)),
    hM.acceptance_compProd_bernoulli_left (by decide),
    hM.acceptance_compProd_bernoulli_right (by decide),
    hproj.mono fun ω hω => by
      simpa only [Bool.compl_singleton, Bool.not_true, hω] using
        (M ω).map_fst_restrict_univ_prod_add_compl (measurableSet_singleton true)⟩

/-- **Independent constant Bernoulli thinning from a marked Poisson realization.** Given any
Poisson random measure `M` on `X × Bool` with product intensity
`Λ.prod (bernoulliMeasure true false p)` whose ground projection recovers `N` almost surely, its
`true` and `false` projections are independent Poisson random measures with intensities `p • Λ`
and `(1 - p) • Λ` summing to `N` almost surely. No s-finiteness assumption on `Λ` is required. -/
theorem IsPoissonRandomMeasure.indepFun_and_isPoissonRandomMeasure_of_prod_bernoulliMeasure
    {M : Ω → Measure (X × Bool)} {p : unitInterval}
    (hM : IsPoissonRandomMeasure P M (Λ.prod (bernoulliMeasure true false p)))
    (hproj : ∀ᵐ ω ∂P, (M ω).map Prod.fst = N ω) :
    IndepFun (fun ω => ((M ω).restrict (univ ×ˢ {true})).map Prod.fst)
      (fun ω => ((M ω).restrict (univ ×ˢ {false})).map Prod.fst) P ∧
    IsPoissonRandomMeasure P (fun ω => ((M ω).restrict (univ ×ˢ {true})).map Prod.fst)
      ((unitInterval.toNNReal p : ℝ≥0∞) • Λ) ∧
    IsPoissonRandomMeasure P (fun ω => ((M ω).restrict (univ ×ˢ {false})).map Prod.fst)
      (((1 - unitInterval.toNNReal p : ℝ≥0) : ℝ≥0∞) • Λ) ∧
    ∀ᵐ ω ∂P,
      ((M ω).restrict (univ ×ˢ {true})).map Prod.fst +
        ((M ω).restrict (univ ×ˢ {false})).map Prod.fst = N ω :=
  ⟨hM.indepFun_map_fst_restrict_univ_prod (measurableSet_singleton true)
      (measurableSet_singleton false) (disjoint_singleton.mpr (by decide)),
    by simpa only [↓reduceIte] using hM.acceptance_univ_prod_singleton_of_bernoulliMeasure true,
    by simpa only [Bool.false_eq_true, ↓reduceIte] using
      hM.acceptance_univ_prod_singleton_of_bernoulliMeasure false,
    hproj.mono fun ω hω => by
      simpa only [Bool.compl_singleton, Bool.not_true, hω] using
        (M ω).map_fst_restrict_univ_prod_add_compl (measurableSet_singleton true)⟩

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
  -- Lift the base finiteness events `N ω (s n) < ∞` to the composition-product.
  have hfin_prod (n : ℕ) :
      ∀ᵐ p ∂(P ⊗ₘ ((κ.markingOfCover hs hcover).comap N hN)), N p.1 (s n) < ∞ :=
    Measure.ae_compProd_of_ae_ae
      (measurableSet_lt ((Measure.measurable_coe (hs n)).comp (hN.comp measurable_fst))
        measurable_const)
      ((hfin n).mono fun _ hω => ae_of_all _ fun _ => hω)
  -- Verify a.s. equality on each cylinder `(A ∩ s n) ×ˢ univ` (`A ∈ C`) by disintegrating along
  -- `ω` and reading off the point mass from `map_map_fst_markingOfCover`.
  refine Measure.ae_map_fst_eq_of_generateFrom_of_cover hcount hgen hpi huniv hs hcover
    hfin_prod fun n A hA => ?_
  have hm : MeasurableSet (A ∩ s n) :=
    (MeasurableSpace.measurableSet_of_eq_generateFrom hgen hA).inter (hs n)
  refine Measure.ae_compProd_of_ae_ae
    (measurableSet_eq_fun
      ((Measure.measurable_coe (hm.prod MeasurableSet.univ)).comp measurable_snd)
      ((Measure.measurable_coe hm).comp (hN.comp measurable_fst))) ?_
  filter_upwards [hint, ae_all_iff.mpr hfin] with ω hωint hωfin
  have hproj : ((κ.markingOfCover hs hcover) (N ω)).map (fun ν => ν.map Prod.fst) =
      Measure.dirac (N ω) :=
    κ.map_map_fst_markingOfCover hs hcover hωint (fun k => (hωfin k).ne)
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
  exact HasLaw.ae_eq_of_dirac
    ⟨(Measure.measurable_coe (hm.prod MeasurableSet.univ)).aemeasurable, heval⟩

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
  exact h.bind_optionalTupleMarking κ (he.comp h.measurable).aemeasurable hrep

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
    exact lintegral_congr fun ω => by simp only [Kernel.comap_apply]
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
  have hcomp_proj : ∀ᵐ p ∂((P.map N) ⊗ₘ (κ.markingOfCover hs hcover)),
      p.2.map Prod.fst = p.1 := by
    have hNid : IsPoissonRandomMeasure (P.map N) id Λ :=
      h.of_identDistrib measurable_id
        ⟨h.measurable.aemeasurable, measurable_id.aemeasurable, by rw [Measure.map_id]⟩
    have htmp := hNid.ae_map_fst_compProd_markingOfCover (κ := κ) hs hcover hΛ
    rwa [Kernel.comap_id] at htmp
  refine Measure.ae_map_fst_eq_of_generateFrom_of_cover hcount hgen hpi huniv hs hcover
    (fun n => h.ae_lt_top (hs n) (hΛ n)) fun n A hA => ?_
  have hm : MeasurableSet (A ∩ s n) :=
    (MeasurableSpace.measurableSet_of_eq_generateFrom hgen hA).inter (hs n)
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
  exact ⟨P', hmp, hM.indepFun_and_isPoissonRandomMeasure_of_compProd_bernoulli hproj⟩

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
  obtain ⟨P', hmp, hM, hproj⟩ :=
    h.exists_independent_marking (κ := Kernel.const X (bernoulliMeasure true false p))
  rw [Measure.compProd_const] at hM
  exact ⟨P', hmp, hM.indepFun_and_isPoissonRandomMeasure_of_prod_bernoulliMeasure hproj⟩

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

/-- If `(N, M)` has joint law `(P.map N) ⊗ₘ (Kernel.const X Q).marking`, then `M` is a Poisson
random measure of product intensity `Λ.prod Q` whose ground projection equals `N` almost surely. -/
theorem IsPoissonRandomMeasure.of_map_prod_eq_compProd_marking_const
    [IsFiniteMeasureOnCompacts Λ] {Q : Measure E} [IsProbabilityMeasure Q]
    (h : IsPoissonRandomMeasure P N Λ) {M : Ω → Measure (X × E)} (hM : Measurable M)
    (hjoint : P.map (fun ω => (N ω, M ω)) = (P.map N) ⊗ₘ (Kernel.const X Q).marking) :
    IsPoissonRandomMeasure P M (Λ.prod Q) ∧ ∀ᵐ ω ∂P, (M ω).map Prod.fst = N ω := by
  simpa only [Measure.compProd_const] using h.of_map_prod_eq_compProd_marking hM hjoint

namespace IsPoissonRandomMeasure

/-- For any coupled marking `(N, M)` with joint law `(P.map N) ⊗ₘ κ.marking` and any measurable
mark set `B`, projecting `M` restricted to `B` and `Bᶜ` recovers `N` as a sum almost surely. -/
theorem ae_map_fst_restrict_univ_prod_add_compl_of_map_prod_eq_compProd_marking
    [IsFiniteMeasureOnCompacts Λ] [IsMarkovKernel κ]
    (h : IsPoissonRandomMeasure P N Λ) {M : Ω → Measure (X × E)} (hM : Measurable M)
    (hjoint : P.map (fun ω => (N ω, M ω)) = (P.map N) ⊗ₘ κ.marking)
    {B : Set E} (hB : MeasurableSet B) :
    ∀ᵐ ω ∂P,
      ((M ω).restrict (univ ×ˢ B)).map Prod.fst +
        ((M ω).restrict (univ ×ˢ Bᶜ)).map Prod.fst = N ω := by
  filter_upwards [(h.of_map_prod_eq_compProd_marking hM hjoint).2] with ω hω
  rw [(M ω).map_fst_restrict_univ_prod_add_compl hB, hω]

/-- Zero-intensity mark boundary case: for any coupled marking `(N, M)` with joint law
`(P.map N) ⊗ₘ κ.marking` and any measurable mark set `B` with `(Λ ⊗ₘ κ) (univ ×ˢ B) = 0`, the
`B`-component vanishes almost surely and the `Bᶜ`-component equals `N` almost surely. -/
theorem ae_map_fst_restrict_univ_prod_eq_zero_and_compl_eq_of_map_prod_eq_compProd_marking
    [IsFiniteMeasureOnCompacts Λ] [IsMarkovKernel κ]
    (h : IsPoissonRandomMeasure P N Λ) {M : Ω → Measure (X × E)} (hM : Measurable M)
    (hjoint : P.map (fun ω => (N ω, M ω)) = (P.map N) ⊗ₘ κ.marking)
    {B : Set E} (hB : MeasurableSet B) (hzero : (Λ ⊗ₘ κ) (univ ×ˢ B) = 0) :
    (∀ᵐ ω ∂P, ((M ω).restrict (univ ×ˢ B)).map Prod.fst = 0) ∧
    (∀ᵐ ω ∂P, ((M ω).restrict (univ ×ˢ Bᶜ)).map Prod.fst = N ω) := by
  have hzero' : ∀ᵐ ω ∂P, ((M ω).restrict (univ ×ˢ B)).map Prod.fst = 0 :=
    (h.of_map_prod_eq_compProd_marking hM hjoint).1.ae_map_fst_restrict_univ_prod_eq_zero hzero
  refine ⟨hzero', ?_⟩
  filter_upwards [hzero',
    h.ae_map_fst_restrict_univ_prod_add_compl_of_map_prod_eq_compProd_marking hM hjoint hB]
    with ω hz hsum
  simpa only [hz, zero_add] using hsum

/-- Constant Bernoulli boundary case for any colour `b : Bool`: whenever the effective mass of
colour `b` vanishes (covering `Λ = 0`, `b = true` with `p = 0`, and `b = false` with `p = 1`),
the `b`-component vanishes almost surely and the `!b`-component equals `N` almost surely. -/
theorem ae_map_fst_restrict_singleton_eq_zero_and_not_eq_of_const_bernoulliMeasure
    [IsFiniteMeasureOnCompacts Λ] (h : IsPoissonRandomMeasure P N Λ)
    {p : unitInterval} {M : Ω → Measure (X × Bool)} (hM : Measurable M)
    (hjoint : P.map (fun ω => (N ω, M ω)) =
      (P.map N) ⊗ₘ (Kernel.const X (bernoulliMeasure true false p)).marking)
    (b : Bool)
    (hzero : Λ univ *
      ((if b then unitInterval.toNNReal p else 1 - unitInterval.toNNReal p : ℝ≥0) : ℝ≥0∞) = 0) :
    (∀ᵐ ω ∂P, ((M ω).restrict (univ ×ˢ {b})).map Prod.fst = 0) ∧
    (∀ᵐ ω ∂P, ((M ω).restrict (univ ×ˢ {!b})).map Prod.fst = N ω) := by
  have hcomp : (Λ ⊗ₘ Kernel.const X (bernoulliMeasure true false p)) (univ ×ˢ {b}) = 0 := by
    rw [Measure.compProd_const, Measure.prod_prod, ← Kernel.bernoulli_apply (X := Unit) true false
      (p := fun _ => p) measurable_const (), Kernel.bernoulli_apply_singleton_bool,
      apply_ite unitInterval.toNNReal, unitInterval.toNNReal_symm, hzero]
  simpa only [Bool.compl_singleton] using
    h.ae_map_fst_restrict_univ_prod_eq_zero_and_compl_eq_of_map_prod_eq_compProd_marking
      hM hjoint (measurableSet_singleton b) hcomp

/-- Constant Bernoulli boundary case with success probability `0`: the `true` projection vanishes
almost surely and the `false` projection equals `N` almost surely. -/
theorem ae_map_fst_restrict_true_eq_zero_and_false_eq_of_const_bernoulliMeasure_zero
    [IsFiniteMeasureOnCompacts Λ] (h : IsPoissonRandomMeasure P N Λ)
    {M : Ω → Measure (X × Bool)} (hM : Measurable M)
    (hjoint : P.map (fun ω => (N ω, M ω)) =
      (P.map N) ⊗ₘ (Kernel.const X (bernoulliMeasure true false 0)).marking) :
    (∀ᵐ ω ∂P, ((M ω).restrict (univ ×ˢ {true})).map Prod.fst = 0) ∧
    (∀ᵐ ω ∂P, ((M ω).restrict (univ ×ˢ {false})).map Prod.fst = N ω) :=
  h.ae_map_fst_restrict_singleton_eq_zero_and_not_eq_of_const_bernoulliMeasure
    hM hjoint true (by simp)

/-- Constant Bernoulli boundary case with success probability `1`: the `false` projection vanishes
almost surely and the `true` projection equals `N` almost surely. -/
theorem ae_map_fst_restrict_false_eq_zero_and_true_eq_of_const_bernoulliMeasure_one
    [IsFiniteMeasureOnCompacts Λ] (h : IsPoissonRandomMeasure P N Λ)
    {M : Ω → Measure (X × Bool)} (hM : Measurable M)
    (hjoint : P.map (fun ω => (N ω, M ω)) =
      (P.map N) ⊗ₘ (Kernel.const X (bernoulliMeasure true false 1)).marking) :
    (∀ᵐ ω ∂P, ((M ω).restrict (univ ×ˢ {false})).map Prod.fst = 0) ∧
    (∀ᵐ ω ∂P, ((M ω).restrict (univ ×ˢ {true})).map Prod.fst = N ω) :=
  h.ae_map_fst_restrict_singleton_eq_zero_and_not_eq_of_const_bernoulliMeasure
    hM hjoint false (by simp)

end IsPoissonRandomMeasure

end CompactCovering

section StandardBorelExists

variable {Ω X E : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace E] {P : Measure Ω} {N : Ω → Measure X} {Λ : Measure X} [SigmaFinite Λ]

/-- **The Poisson Marking Theorem** (Last–Penrose, Theorem 5.6). For any Poisson random measure `N`
with σ-finite intensity `Λ` on a standard Borel space `X` and any Markov kernel `κ : Kernel X E`,
there exists a realization-level Markov kernel `η : Kernel (Measure X) (Measure (X × E))` such that
under `P ⊗ₘ η.comap N hN.measurable`, the second coordinate is a Poisson random measure with
intensity `Λ ⊗ₘ κ` whose ground projection almost surely equals `N`. Because `η` acts on `Measure X`
alone, the marked realization is conditionally independent of `Ω` given `N`. Atomic intensities and
multiple occurrences at one location are allowed. -/
theorem IsPoissonRandomMeasure.exists_isMarkovKernel_marking
    (hN : IsPoissonRandomMeasure P N Λ) (κ : Kernel X E) [IsMarkovKernel κ] :
    ∃ η : Kernel (Measure X) (Measure (X × E)),
      IsMarkovKernel η ∧
      IsPoissonRandomMeasure (P ⊗ₘ η.comap N hN.measurable) Prod.snd (Λ ⊗ₘ κ) ∧
      ∀ᵐ z ∂(P ⊗ₘ η.comap N hN.measurable), z.2.map Prod.fst = N z.1 := by
  have hN' : IsPoissonRandomMeasure (P.map N) id Λ :=
    hN.of_identDistrib measurable_id
      ⟨hN.measurable.aemeasurable, measurable_id.aemeasurable, Measure.map_id.symm⟩
  obtain ⟨e, he, hae⟩ := measurable_id.aemeasurable.exists_ae_occurrence_enumeration_of_cover
    hN'.ae_isIntegerValued (spanningSets Λ) (measurableSet_spanningSets Λ) (iUnion_spanningSets Λ)
    hN'.ae_ne_top_spanningSets
  have haeN : ∀ᵐ ω ∂P, N ω = Measure.sum (fun i ↦ (e (N ω) i).elim 0 Measure.dirac) :=
    ae_of_ae_map hN.measurable.aemeasurable hae
  refine ⟨(κ.optionalTupleMarking ℕ).comap e he, inferInstance, ?_, ?_⟩
  · rw [← Kernel.comap_comp_right]
    exact hN.compProd_optionalTupleMarking κ (he.comp hN.measurable) haeN
  · rw [← Kernel.comap_comp_right]
    exact hN.ae_map_fst_compProd_optionalTupleMarking κ (he.comp hN.measurable) haeN

/-- Independent i.i.d. marking specialization of
`IsPoissonRandomMeasure.exists_isMarkovKernel_marking`: attaching independent marks with common
probability law `Q` via a realization-level Markov kernel produces a Poisson random measure with
product intensity `Λ.prod Q` whose ground projection recovers `N` almost surely. -/
theorem IsPoissonRandomMeasure.exists_isMarkovKernel_marking_prod
    (hN : IsPoissonRandomMeasure P N Λ) (Q : Measure E) [IsProbabilityMeasure Q] :
    ∃ η : Kernel (Measure X) (Measure (X × E)),
      IsMarkovKernel η ∧
      IsPoissonRandomMeasure (P ⊗ₘ η.comap N hN.measurable) Prod.snd (Λ.prod Q) ∧
      ∀ᵐ z ∂(P ⊗ₘ η.comap N hN.measurable), z.2.map Prod.fst = N z.1 := by
  let := hN.isProbabilityMeasure
  obtain ⟨η, hη, hP, hproj⟩ := hN.exists_isMarkovKernel_marking (Kernel.const X Q)
  rw [Measure.compProd_const] at hP
  exact ⟨η, hη, hP, hproj⟩

end StandardBorelExists

end TauCeti.Probability
