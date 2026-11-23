/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import TauCeti.Probability.PointProcess.Marking.Measure
public import TauCeti.Probability.PointProcess.Marking.Optional
public import TauCeti.Probability.PointProcess.Poisson.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Mathlib.Probability.Kernel.MeasurableLIntegral
import TauCeti.MeasureTheory.Integral.Lebesgue.ExpNeg
import TauCeti.MeasureTheory.Measure.IntegerValued.Enumeration.LocallyFinite
import TauCeti.Probability.PointProcess.Poisson.IntegerValued
import TauCeti.Probability.PointProcess.Poisson.Laplace
import TauCeti.Probability.PointProcess.Poisson.LaplaceCharacterization

/-!
# The Poisson marking theorem

Independently marking the occurrences of a Poisson random measure `N` of intensity `Λ` using a
Markov kernel `κ : Kernel X E` produces a Poisson random measure on `X × E` with intensity
`Λ ⊗ₘ κ`, whose ground projection recovers `N` almost surely.

The theorem is proved at two main levels of generality:

* Given any measurable optional occurrence enumeration `e : Ω → ι → Option X` representing `N`
  almost everywhere, `IsPoissonRandomMeasure.compProd_optionalTupleMarking` and
  `IsPoissonRandomMeasure.bind_optionalTupleMarking` yield a Poisson random measure of intensity
  `Λ ⊗ₘ κ` for any s-finite intensity `Λ`, with no separation or topological assumption on `X`.
* On any standard Borel space `X` with sigma-finite intensity `Λ`,
  `IsPoissonRandomMeasure.exists_isMarkovKernel_marking` gives an existential realization-level
  marking kernel, while intrinsic marking via `Kernel.markingOfCover` gives the marked law,
  the joint realization on `Ω × Measure (X × E)` with almost-sure ground projection
  `p.2.map Prod.fst = N p.1`, and transfer to any realization on an arbitrary probability space
  with that joint law (`IsPoissonRandomMeasure.of_map_prod_eq_compProd_markingOfCover`). For a
  constant mark kernel `Kernel.const X Q`, the intensity reduces to `Λ.prod Q`
  (`IsPoissonRandomMeasure.exists_isMarkovKernel_marking_prod`).

We also record `ae_map_fst_restrict_univ_prod_add_compl_of_ae_map_fst`, splitting a marked
realization recovering `N` along a measurable mark set and its complement.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Theorem 5.6 (Marking Theorem).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

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

/-- For any marked random measure `M` whose ground projection equals `N` almost surely and any
measurable mark set `B`, projecting `M` restricted to `B` and `Bᶜ` recovers `N` as a sum almost
surely. -/
theorem ae_map_fst_restrict_univ_prod_add_compl_of_ae_map_fst
    {M : Ω → Measure (X × E)} (hproj : ∀ᵐ ω ∂P, (M ω).map Prod.fst = N ω)
    {B : Set E} (hB : MeasurableSet B) :
    ∀ᵐ ω ∂P,
      ((M ω).restrict (univ ×ˢ B)).map Prod.fst +
        ((M ω).restrict (univ ×ˢ Bᶜ)).map Prod.fst = N ω := by
  filter_upwards [hproj] with ω hω
  rw [Set.univ_prod, Set.univ_prod, Set.preimage_compl,
    ← Measure.map_add _ _ measurable_fst, Measure.restrict_add_restrict_compl (measurable_snd hB),
    hω]

end General

section StandardBorel

variable {Ω X E : Type*} [MeasurableSpace Ω]
  [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace E]
  {P : Measure Ω} {N : Ω → Measure X} {Λ : Measure X} {κ : Kernel X E}

private theorem ae_eq_sum_markingOfCover_enumeration [SigmaFinite Λ]
    (h : IsPoissonRandomMeasure P N Λ) {s : ℕ → Set X}
    (hs : ∀ n, MeasurableSet (s n)) (hΛ : ∀ n, Λ (s n) < ∞)
    {e : Measure X → ℕ → Option X}
    (hrec : ∀ μ : Measure X, μ.IsIntegerValued → (∀ n, μ (s n) ≠ ∞) →
      μ = Measure.sum fun n => (e μ n).elim 0 Measure.dirac) :
    ∀ᵐ ω ∂P, N ω = Measure.sum fun n => (e (N ω) n).elim 0 Measure.dirac := by
  have hfin : ∀ n, ∀ᵐ ω ∂P, N ω (s n) ≠ ∞ :=
    fun n => (h.ae_lt_top (hs n) (hΛ n)).mono fun _ hω => hω.ne
  filter_upwards [h.ae_isIntegerValued, ae_all_iff.mpr hfin] with ω hωint hωfin
  exact hrec (N ω) hωint hωfin

/-- **Poisson marking theorem via `Kernel.markingOfCover`.** On a standard Borel space,
independently marking a Poisson random measure whose intensity `Λ` is finite on a countable
measurable cover produces a Poisson random measure of intensity `Λ ⊗ₘ κ`. -/
theorem IsPoissonRandomMeasure.isPoissonRandomMeasure_comp_markingOfCover
    [IsMarkovKernel κ] (h : IsPoissonRandomMeasure P N Λ)
    {s : ℕ → Set X} (hs : ∀ n, MeasurableSet (s n)) (hcover : ⋃ n, s n = univ)
    (hΛ : ∀ n, Λ (s n) < ∞) :
    IsPoissonRandomMeasure ((κ.markingOfCover hs hcover) ∘ₘ (P.map N)) id (Λ ⊗ₘ κ) := by
  let := h.isProbabilityMeasure
  have : SigmaFinite Λ :=
    Measure.sigmaFinite_of_countable
      (countable_range s) (forall_mem_range.2 hΛ) (by rwa [sUnion_range])
  obtain ⟨e, he, hrec, hmark⟩ := κ.exists_enumeration_markingOfCover hs hcover
  have hrep := ae_eq_sum_markingOfCover_enumeration h hs hΛ hrec
  rw [hmark, Measure.bind_map h.measurable.aemeasurable
    ((κ.optionalTupleMarking ℕ).comap e he).aemeasurable]
  simpa only [Kernel.comap_apply, Function.comp_apply] using
    h.bind_optionalTupleMarking κ (he.comp h.measurable).aemeasurable hrep

/-- Joint realization of independent marking on `Ω × Measure (X × E)` via `markingOfCover`:
the second coordinate is a Poisson random measure of intensity `Λ ⊗ₘ κ`. -/
theorem IsPoissonRandomMeasure.isPoissonRandomMeasure_compProd_markingOfCover
    [IsMarkovKernel κ] (h : IsPoissonRandomMeasure P N Λ)
    {s : ℕ → Set X} (hs : ∀ n, MeasurableSet (s n)) (hcover : ⋃ n, s n = univ)
    (hΛ : ∀ n, Λ (s n) < ∞) :
    IsPoissonRandomMeasure (P ⊗ₘ ((κ.markingOfCover hs hcover).comap N h.measurable))
      Prod.snd (Λ ⊗ₘ κ) := by
  have : SigmaFinite Λ :=
    Measure.sigmaFinite_of_countable
      (countable_range s) (forall_mem_range.2 hΛ) (by rwa [sUnion_range])
  obtain ⟨e, he, hrec, hmark⟩ := κ.exists_enumeration_markingOfCover hs hcover
  have hrep := ae_eq_sum_markingOfCover_enumeration h hs hΛ hrec
  rw [hmark, ← Kernel.comap_comp_right]
  exact h.compProd_optionalTupleMarking κ (he.comp h.measurable) hrep

/-- On the joint marking space `Ω × Measure (X × E)`, forgetting marks almost surely recovers
the original Poisson realization `N`. -/
theorem IsPoissonRandomMeasure.ae_map_fst_compProd_markingOfCover
    [IsMarkovKernel κ] (h : IsPoissonRandomMeasure P N Λ)
    {s : ℕ → Set X} (hs : ∀ n, MeasurableSet (s n)) (hcover : ⋃ n, s n = univ)
    (hΛ : ∀ n, Λ (s n) < ∞) :
    ∀ᵐ p ∂(P ⊗ₘ ((κ.markingOfCover hs hcover).comap N h.measurable)),
      p.2.map Prod.fst = N p.1 := by
  have : SigmaFinite Λ :=
    Measure.sigmaFinite_of_countable
      (countable_range s) (forall_mem_range.2 hΛ) (by rwa [sUnion_range])
  obtain ⟨e, he, hrec, hmark⟩ := κ.exists_enumeration_markingOfCover hs hcover
  have hrep := ae_eq_sum_markingOfCover_enumeration h hs hΛ hrec
  rw [hmark, ← Kernel.comap_comp_right]
  exact h.ae_map_fst_compProd_optionalTupleMarking κ (he.comp h.measurable) hrep

/-- If `(N, M)` on an arbitrary probability space has joint law `(P.map N) ⊗ₘ κ.markingOfCover`,
then `M` is a Poisson random measure of intensity `Λ ⊗ₘ κ` and its ground projection equals
`N` almost surely. -/
theorem IsPoissonRandomMeasure.of_map_prod_eq_compProd_markingOfCover
    [IsMarkovKernel κ] (h : IsPoissonRandomMeasure P N Λ)
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
  refine ⟨(h.isPoissonRandomMeasure_comp_markingOfCover hs hcover hΛ).of_identDistrib hM
    (HasLaw.id.identDistrib hlaw), ?_⟩
  have hcomp_proj : ∀ᵐ p ∂((P.map N) ⊗ₘ (κ.markingOfCover hs hcover)),
      p.2.map Prod.fst = p.1 := by
    have hNid : IsPoissonRandomMeasure (P.map N) id Λ :=
      h.of_identDistrib measurable_id
        ((hasLaw_map h.measurable.aemeasurable).identDistrib HasLaw.id)
    have htmp := hNid.ae_map_fst_compProd_markingOfCover (κ := κ) hs hcover hΛ
    rwa [Kernel.comap_id] at htmp
  rw [← hjoint] at hcomp_proj
  exact ae_of_ae_map (h.measurable.prodMk hM).aemeasurable hcomp_proj

end StandardBorel

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
      ∀ᵐ z ∂(P ⊗ₘ η.comap N hN.measurable), z.2.map Prod.fst = N z.1 :=
  ⟨κ.markingOfCover (measurableSet_spanningSets Λ) (iUnion_spanningSets Λ), inferInstance,
    hN.isPoissonRandomMeasure_compProd_markingOfCover (measurableSet_spanningSets Λ)
      (iUnion_spanningSets Λ) (measure_spanningSets_lt_top Λ),
    hN.ae_map_fst_compProd_markingOfCover (measurableSet_spanningSets Λ)
      (iUnion_spanningSets Λ) (measure_spanningSets_lt_top Λ)⟩

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
