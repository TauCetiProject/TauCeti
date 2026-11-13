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
  `IsPoissonRandomMeasure.exists_markovKernel_marking` constructs a Markov kernel
  `η : Kernel Ω (Measure (X × E))` from the realizations of `N` alone (without assuming an
  enumeration in advance) by combining almost-sure integrality and measurable occurrence
  enumeration on the spanning sets of `Λ`. Atomic intensities and repeated occurrences at one
  location are allowed.

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
  have he' : Measurable (fun ω i ↦ some (e ω i)) := by fun_prop
  have hker : (κ.tupleMarking ι).comap e he = (κ.optionalTupleMarking ι).comap _ he' := by
    ext ω s _
    simp only [Kernel.comap_apply, ← Kernel.optionalTupleMarking_some]
  rw [hker]
  exact hN.compProd_optionalTupleMarking κ he' (by simpa only [Option.elim_some] using hae)

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
    ext s hs
    rw [Measure.map_apply measurable_snd hs, Measure.compProd_apply (hs.preimage measurable_snd),
      Measure.bind_apply hs (by fun_prop)]
    rfl
  exact (hN.compProd_optionalTupleMarking κ he hae).of_identDistrib measurable_id
    ⟨measurable_snd.aemeasurable, measurable_id.aemeasurable, by rw [Measure.map_id, hmap]⟩

/-- Setwise ground-projection recovery for optional tuple marking on an arbitrary measurable space:
on any fixed measurable set `A`, projecting the marked realization back to `X` almost surely
recovers `N z.1 A`. -/
theorem IsPoissonRandomMeasure.ae_map_fst_apply_compProd_optionalTupleMarking
    (hN : IsPoissonRandomMeasure P N Λ) (κ : Kernel X E) [IsMarkovKernel κ]
    {e : Ω → ι → Option X} (he : Measurable e)
    (hae : ∀ᵐ ω ∂P, N ω = Measure.sum (fun i ↦ (e ω i).elim 0 Measure.dirac))
    {A : Set X} (hA : MeasurableSet A) :
    ∀ᵐ z ∂(P ⊗ₘ (κ.optionalTupleMarking ι).comap e he), z.2.map Prod.fst A = N z.1 A := by
  let := hN.isProbabilityMeasure
  have hp : MeasurableSet {z : Ω × Measure (X × E) | z.2.map Prod.fst A = N z.1 A} :=
    measurableSet_eq_fun
      ((Measure.measurable_coe hA).comp
        ((Measure.measurable_map _ measurable_fst).comp measurable_snd))
      ((Measure.measurable_coe hA).comp (hN.measurable.comp measurable_fst))
  rw [Measure.ae_compProd_iff hp]
  filter_upwards [hae] with ω hω
  simpa only [Kernel.comap_apply, ← hω] using
    Kernel.ae_map_fst_apply_optionalTupleMarking κ (e ω) hA

/-- On a countably generated ground space with σ-finite intensity `Λ`, projecting the marked
realization onto the first coordinate recovers the entire ground realization `N z.1` almost
surely. -/
theorem IsPoissonRandomMeasure.ae_map_fst_compProd_optionalTupleMarking
    [MeasurableSpace.CountablyGenerated X] [SigmaFinite Λ]
    (hN : IsPoissonRandomMeasure P N Λ) (κ : Kernel X E) [IsMarkovKernel κ]
    {e : Ω → ι → Option X} (he : Measurable e)
    (hae : ∀ᵐ ω ∂P, N ω = Measure.sum (fun i ↦ (e ω i).elim 0 Measure.dirac)) :
    ∀ᵐ z ∂(P ⊗ₘ (κ.optionalTupleMarking ι).comap e he), z.2.map Prod.fst = N z.1 := by
  let := hN.isProbabilityMeasure
  let η := (κ.optionalTupleMarking ι).comap e he
  have hfin (n : ℕ) : ∀ᵐ z ∂(P ⊗ₘ η), N z.1 (spanningSets Λ n) ≠ ∞ := by
    have hm : MeasurableSet {ω : Ω | N ω (spanningSets Λ n) ≠ ∞} :=
      (measurableSet_eq_fun
        ((Measure.measurable_coe (measurableSet_spanningSets Λ n)).comp hN.measurable)
        measurable_const).compl
    exact Measure.ae_compProd_of_ae_fst η hm
      ((hN.ae_lt_top (measurableSet_spanningSets Λ n)
        (measure_spanningSets_lt_top Λ n)).mono fun _ h ↦ h.ne)
  exact (Measure.ae_eq_of_forall_ae_eq_of_cover (measurableSet_spanningSets Λ)
    (iUnion_spanningSets Λ) hfin fun A hA ↦
      (hN.ae_map_fst_apply_compProd_optionalTupleMarking κ he hae hA).mono fun _ h ↦ h.symm).symm

end Enumeration

section StandardBorel

variable {Ω X E : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace E] {P : Measure Ω} {N : Ω → Measure X} {Λ : Measure X} [SigmaFinite Λ]

/-- **The Poisson Marking Theorem** (Last–Penrose, Theorem 5.6). For any Poisson random measure `N`
with σ-finite intensity `Λ` on a standard Borel space `X` and any Markov kernel `κ : Kernel X E`,
there exists a Markov kernel `η : Kernel Ω (Measure (X × E))` such that under `P ⊗ₘ η`, the second
coordinate is a Poisson random measure with intensity `Λ ⊗ₘ κ` whose ground projection almost
surely equals `N`. Atomic intensities and multiple occurrences at one location are allowed. -/
theorem IsPoissonRandomMeasure.exists_markovKernel_marking
    (hN : IsPoissonRandomMeasure P N Λ) (κ : Kernel X E) [IsMarkovKernel κ] :
    ∃ η : Kernel Ω (Measure (X × E)),
      IsMarkovKernel η ∧
      IsPoissonRandomMeasure (P ⊗ₘ η) Prod.snd (Λ ⊗ₘ κ) ∧
      ∀ᵐ z ∂(P ⊗ₘ η), z.2.map Prod.fst = N z.1 := by
  obtain ⟨e, he, hae⟩ := hN.measurable.aemeasurable.exists_ae_occurrence_enumeration_of_cover
    hN.ae_isIntegerValued (spanningSets Λ) (measurableSet_spanningSets Λ) (iUnion_spanningSets Λ)
    (fun n ↦ (hN.ae_lt_top (measurableSet_spanningSets Λ n)
      (measure_spanningSets_lt_top Λ n)).mono fun _ h ↦ h.ne)
  exact ⟨(κ.optionalTupleMarking ℕ).comap e he, inferInstance,
    hN.compProd_optionalTupleMarking κ he hae,
    hN.ae_map_fst_compProd_optionalTupleMarking κ he hae⟩

/-- Independent i.i.d. marking specialization of
`IsPoissonRandomMeasure.exists_markovKernel_marking`: attaching independent marks with common
probability law `Q` produces a Poisson random measure with product intensity `Λ.prod Q` whose
ground projection recovers `N` almost surely. -/
theorem IsPoissonRandomMeasure.exists_markovKernel_marking_prod
    (hN : IsPoissonRandomMeasure P N Λ) (Q : Measure E) [IsProbabilityMeasure Q] :
    ∃ η : Kernel Ω (Measure (X × E)),
      IsMarkovKernel η ∧
      IsPoissonRandomMeasure (P ⊗ₘ η) Prod.snd (Λ.prod Q) ∧
      ∀ᵐ z ∂(P ⊗ₘ η), z.2.map Prod.fst = N z.1 := by
  let := hN.isProbabilityMeasure
  obtain ⟨η, hη, hP, hproj⟩ := hN.exists_markovKernel_marking (Kernel.const X Q)
  rw [Measure.compProd_const] at hP
  exact ⟨η, hη, hP, hproj⟩

end StandardBorel

end TauCeti.Probability
