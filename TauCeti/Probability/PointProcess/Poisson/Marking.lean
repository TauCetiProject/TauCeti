/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import TauCeti.Probability.PointProcess.Marking.Tuple
public import TauCeti.Probability.PointProcess.Poisson.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableLIntegral
import TauCeti.MeasureTheory.Measure.IntegerValued.Enumeration.LocallyFinite
import TauCeti.Probability.PointProcess.Poisson.IntegerValued
import TauCeti.Probability.PointProcess.Poisson.Laplace
import TauCeti.Probability.PointProcess.Poisson.LaplaceCharacterization
import TauCeti.Probability.RandomMeasure.AeEq

/-!
# The Poisson Marking Theorem

Attaching mutually independent marks with location-dependent Markov kernel `κ : Kernel X E` to the
occurrences of a Poisson random measure `N` with intensity `Λ` yields a Poisson random measure on
`X × E` with composition-product intensity `Λ ⊗ₘ κ`, whose ground projection recovers `N` almost
surely.

Two levels of generality are provided:

* Given a measurable optional occurrence enumeration `e : Ω → ι → Option X` representing `N`
  almost everywhere, `IsPoissonRandomMeasure.compProd_optionalTupleMarking` constructs the marked
  Poisson random measure directly on `P ⊗ₘ (κ.optionalTupleMarking ι).comap e he` for any s-finite
  intensity `Λ` on an arbitrary measurable space `X`, with no standard Borel or simplicity
  assumption.
* On a standard Borel ground space `X` with σ-finite intensity `Λ`,
  `IsPoissonRandomMeasure.exists_isMarkovKernel_marking` constructs a realization-level Markov
  kernel `η : Kernel (Measure X) (Measure (X × E))` (without assuming an enumeration in advance) by
  combining almost-sure integrality and measurable occurrence enumeration on the spanning sets of
  `Λ`, applied to `(Ω, P)` via `P ⊗ₘ η.comap N hN.measurable`. Atomic intensities and repeated
  occurrences at one location are allowed.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Chapter 5, Theorem 5.6 (Marking Theorem).
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
  let g : X → ℝ≥0∞ := fun a ↦
    (-ENNReal.log (∫⁻ b, (ENNReal.expNeg (f (a, b)) : ℝ≥0∞) ∂κ a)).toENNReal
  have hg : Measurable g := by fun_prop
  have hle (a : X) : ∫⁻ b, (ENNReal.expNeg (f (a, b)) : ℝ≥0∞) ∂κ a ≤ 1 := by
    calc ∫⁻ b, (ENNReal.expNeg (f (a, b)) : ℝ≥0∞) ∂κ a
        ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂κ a :=
          lintegral_mono fun _ ↦ ENNReal.coe_le_one_iff.mpr (ENNReal.expNeg_le_one _)
      _ = 1 := by simp
  rw [Measure.laplaceFunctional_def, Measure.lintegral_compProd (by fun_prop)]
  simp_rw [Kernel.comap_apply,
    Kernel.lintegral_expNeg_optionalTupleMarking_eq_expNeg_lintegral κ _ hf]
  rw [lintegral_congr_ae (hae.mono fun ω hω ↦ by rw [← hω]),
    ← Measure.laplaceFunctional_def, hN.laplaceFunctional_eq_expNeg hg,
    Measure.lintegral_compProd (by fun_prop)]
  congr 2
  refine lintegral_congr fun a ↦ ?_
  rw [ENNReal.coe_expNeg_toENNReal_neg_log (hle a),
    lintegral_sub (by fun_prop) ((hle a).trans_lt ENNReal.one_lt_top).ne
      (ae_of_all _ fun _ ↦ ENNReal.coe_le_one_iff.mpr (ENNReal.expNeg_le_one _)),
    lintegral_const, measure_univ, one_mul]

/-- Independently marking a total countable occurrence enumeration of a Poisson random measure with
s-finite intensity `Λ` produces a Poisson random measure with intensity `Λ ⊗ₘ κ`. -/
theorem IsPoissonRandomMeasure.compProd_tupleMarking [SFinite Λ]
    (hN : IsPoissonRandomMeasure P N Λ) (κ : Kernel X E) [IsMarkovKernel κ]
    {e : Ω → ι → X} (he : Measurable e)
    (hae : ∀ᵐ ω ∂P, N ω = Measure.sum (fun i ↦ Measure.dirac (e ω i))) :
    IsPoissonRandomMeasure (P ⊗ₘ (κ.tupleMarking ι).comap e he) Prod.snd (Λ ⊗ₘ κ) := by
  rw [Kernel.tupleMarking_def, ← Kernel.comap_comp_right]
  exact hN.compProd_optionalTupleMarking κ _
    (by simpa only [Function.comp_apply, Option.elim_some] using hae)

/-- Marginal form of `IsPoissonRandomMeasure.compProd_optionalTupleMarking`: the mixture of
marked laws over `P` is a canonical Poisson random measure on `Measure (X × E)` with intensity
`Λ ⊗ₘ κ`. -/
theorem IsPoissonRandomMeasure.bind_optionalTupleMarking [SFinite Λ]
    (hN : IsPoissonRandomMeasure P N Λ) (κ : Kernel X E) [IsMarkovKernel κ]
    {e : Ω → ι → Option X} (he : Measurable e)
    (hae : ∀ᵐ ω ∂P, N ω = Measure.sum (fun i ↦ (e ω i).elim 0 Measure.dirac)) :
    IsPoissonRandomMeasure (P.bind fun ω ↦ κ.optionalTupleMarking ι (e ω)) id (Λ ⊗ₘ κ) := by
  let := hN.isProbabilityMeasure
  let η := (κ.optionalTupleMarking ι).comap e he
  have hmap : (P ⊗ₘ η).map Prod.snd = P.bind (fun ω ↦ κ.optionalTupleMarking ι (e ω)) := by
    rw [← Measure.snd, Measure.snd_compProd]
    simp only [η, Kernel.coe_comap, Function.comp_def]
  exact (hN.compProd_optionalTupleMarking κ he hae).of_identDistrib measurable_id
    ⟨measurable_snd.aemeasurable, measurable_id.aemeasurable, by rw [Measure.map_id, hmap]⟩

/-- Marginal form of `IsPoissonRandomMeasure.compProd_tupleMarking`: the mixture of marked tuple
laws over `P` is a canonical Poisson random measure on `Measure (X × E)` with intensity
`Λ ⊗ₘ κ`. -/
theorem IsPoissonRandomMeasure.bind_tupleMarking [SFinite Λ]
    (hN : IsPoissonRandomMeasure P N Λ) (κ : Kernel X E) [IsMarkovKernel κ]
    {e : Ω → ι → X} (he : Measurable e)
    (hae : ∀ᵐ ω ∂P, N ω = Measure.sum (fun i ↦ Measure.dirac (e ω i))) :
    IsPoissonRandomMeasure (P.bind fun ω ↦ κ.tupleMarking ι (e ω)) id (Λ ⊗ₘ κ) := by
  simpa only [Kernel.optionalTupleMarking_some] using
    hN.bind_optionalTupleMarking κ (e := fun ω i ↦ some (e ω i))
      (Measurable.of_eval fun i ↦ Option.measurable_some.comp ((measurable_pi_apply i).comp he))
      (by simpa only [Option.elim_some] using hae)

/-- On a countably generated ground space with σ-finite intensity `Λ`, setwise almost-everywhere
equality of a random measure `M` on `P ⊗ₘ η` with the ground realization `N z.1` upgrades to
almost-everywhere equality of measures. -/
theorem IsPoissonRandomMeasure.ae_eq_compProd_of_forall_ae_eq {β : Type*} [MeasurableSpace β]
    [MeasurableSpace.CountablyGenerated X] [SigmaFinite Λ]
    (hN : IsPoissonRandomMeasure P N Λ) {η : Kernel Ω β} [IsMarkovKernel η]
    {M : Ω × β → Measure X}
    (heq : ∀ A, MeasurableSet A → ∀ᵐ z ∂(P ⊗ₘ η), M z A = N z.1 A) :
    ∀ᵐ z ∂(P ⊗ₘ η), M z = N z.1 := by
  let := hN.isProbabilityMeasure
  have hfin (n : ℕ) : ∀ᵐ z ∂(P ⊗ₘ η), N z.1 (spanningSets Λ n) ≠ ∞ :=
    ae_of_ae_map measurable_fst.aemeasurable
      ((Measure.fst_compProd P η).symm ▸
        (hN.ae_lt_top (measurableSet_spanningSets Λ n)
          (measure_spanningSets_lt_top Λ n)).mono fun _ ↦ ne_of_lt)
  exact (Measure.ae_eq_of_forall_ae_eq_of_cover (measurableSet_spanningSets Λ)
    (iUnion_spanningSets Λ) hfin fun A hA ↦ (heq A hA).mono fun _ h ↦ h.symm).symm

/-- On a countably generated ground space with σ-finite intensity `Λ`, projecting an optional-tuple
marked realization onto the first coordinate recovers the entire ground realization `N z.1` almost
surely. -/
theorem IsPoissonRandomMeasure.ae_map_fst_compProd_optionalTupleMarking
    [MeasurableSpace.CountablyGenerated X] [SigmaFinite Λ]
    (hN : IsPoissonRandomMeasure P N Λ) (κ : Kernel X E) [IsMarkovKernel κ]
    {e : Ω → ι → Option X} (he : Measurable e)
    (hae : ∀ᵐ ω ∂P, N ω = Measure.sum (fun i ↦ (e ω i).elim 0 Measure.dirac)) :
    ∀ᵐ z ∂(P ⊗ₘ (κ.optionalTupleMarking ι).comap e he), z.2.map Prod.fst = N z.1 :=
  hN.ae_eq_compProd_of_forall_ae_eq fun _ hA ↦
    κ.ae_map_fst_apply_compProd_optionalTupleMarking he hae hA

/-- On a countably generated ground space with σ-finite intensity `Λ`, projecting a total-tuple
marked realization onto the first coordinate recovers the entire ground realization `N z.1` almost
surely. -/
theorem IsPoissonRandomMeasure.ae_map_fst_compProd_tupleMarking
    [MeasurableSpace.CountablyGenerated X] [SigmaFinite Λ]
    (hN : IsPoissonRandomMeasure P N Λ) (κ : Kernel X E) [IsMarkovKernel κ]
    {e : Ω → ι → X} (he : Measurable e)
    (hae : ∀ᵐ ω ∂P, N ω = Measure.sum (fun i ↦ Measure.dirac (e ω i))) :
    ∀ᵐ z ∂(P ⊗ₘ (κ.tupleMarking ι).comap e he), z.2.map Prod.fst = N z.1 :=
  hN.ae_eq_compProd_of_forall_ae_eq fun _ hA ↦
    κ.ae_map_fst_apply_compProd_tupleMarking he hae hA

end Enumeration

section StandardBorel

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
    (fun n ↦ (hN'.ae_lt_top (measurableSet_spanningSets Λ n)
      (measure_spanningSets_lt_top Λ n)).mono fun _ ↦ ne_of_lt)
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

end StandardBorel

end TauCeti.Probability
