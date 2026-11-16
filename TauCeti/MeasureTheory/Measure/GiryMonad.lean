/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Random measures and algebraic properties of the Giry monad

The measurable space on measures is induced by the map of all measurable-set evaluations.
Consequently, any measure-valued map generates the same σ-algebra as its joint evaluations,
without a measurability assumption. These identities let laws and independence of random
measures be checked through their evaluation processes.

A random measure with sigma-finite average is almost surely sigma-finite. More precisely,
one fixed measurable exhaustion of the average has finite mass for almost every realization,
simultaneously on all its sets. No topology or probability normalization is required.
We also construct a measurable version whose values are all sigma-finite, by replacing the
exceptional realizations by zero. This permits constructions on sigma-finite measures to be
applied everywhere without changing the law of the random measure. The conclusion is not
almost-sure absolute continuity with respect to the average: a uniformly located Dirac
measure is a counterexample to that stronger assertion.

For `MeasureTheory.Measure.join` and `MeasureTheory.Measure.bind`, this file also records
monotonicity, binary and `Finset`-sum additivity in the mixing measure, and the singleton
lower bound `μ {x} * f x s ≤ (μ.bind f) s`. Since composition `κ ∘ₘ μ` of a kernel with a
measure is `μ.bind κ`, these properties apply directly to kernel pushforwards of measures.

## References

* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge University
  Press, 2018, Chapters 2–3, on random measures and sigma-finite Poisson intensities.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal

namespace MeasureTheory.Measure

section RandomMeasures

variable {X : Type*} [MeasurableSpace X]

/-- The measurable space on measures is induced by the joint evaluation map on all
measurable sets. -/
theorem measurableSpace_eq_comap_eval :
    (Measure.instMeasurableSpace : MeasurableSpace (Measure X)) =
      MeasurableSpace.comap
        (fun (μ : Measure X) (A : {A : Set X // MeasurableSet A}) ↦ μ A.val)
        MeasurableSpace.pi := by
  let e : Measure X → ({A : Set X // MeasurableSet A} → ℝ≥0∞) := fun μ A ↦ μ A.val
  apply le_antisymm
  · have hid : Measurable[MeasurableSpace.comap e inferInstance]
        (id : Measure X → Measure X) :=
      measurable_of_measurable_coe _ fun A hA ↦
        (measurable_pi_apply (⟨A, hA⟩ : {A : Set X // MeasurableSet A})).comp
          (comap_measurable e)
    simpa only [MeasurableSpace.comap_id] using hid.comap_le
  · exact (Measurable.of_eval fun A ↦ measurable_coe A.property).comap_le

/-- A measure-valued map generates the same measurable space as its joint evaluations
on all measurable sets. No measurability assumption on the map is needed. -/
theorem measurableSpace_comap_eq_comap_eval {Ω : Type*} (N : Ω → Measure X) :
    MeasurableSpace.comap N inferInstance =
      MeasurableSpace.comap
        (fun ω (A : {A : Set X // MeasurableSet A}) ↦ N ω A.val)
        MeasurableSpace.pi := by
  rw [measurableSpace_eq_comap_eval, MeasurableSpace.comap_comp, Function.comp_def]

variable {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : Ω → Measure X}

/-- On any countable family of sets with finite average mass, almost every realization has finite
mass on every set in that family. -/
theorem ae_forall_measure_lt_top_of_bind [Countable ι]
    (hN : AEMeasurable N P) {s : ι → Set X}
    (hfinite : ∀ i, P.bind N (s i) < ∞) :
    ∀ᵐ ω ∂P, ∀ i, N ω (s i) < ∞ := by
  rw [ae_all_iff]
  intro i
  have hs := measurableSet_toMeasurable (P.bind N) (s i)
  have h : ∀ᵐ ω ∂P, N ω (toMeasurable (P.bind N) (s i)) < ∞ := by
    apply ae_lt_top' (f := fun ω => N ω (toMeasurable (P.bind N) (s i)))
      ((Measure.measurable_coe hs).comp_aemeasurable hN)
    rw [← bind_apply hs hN, measure_toMeasurable]
    exact (hfinite i).ne
  filter_upwards [h] with ω hω
  exact (measure_mono (subset_toMeasurable (P.bind N) (s i))).trans_lt hω

/-- A random measure whose average is sigma-finite is almost surely sigma-finite.
The sample measure need not be finite, and no topology on either space is needed. -/
theorem ae_sigmaFinite_of_bind (hN : AEMeasurable N P) [SigmaFinite (P.bind N)] :
    ∀ᵐ ω ∂P, SigmaFinite (N ω) := by
  filter_upwards [ae_forall_measure_lt_top_of_bind hN
    (measure_spanningSets_lt_top (P.bind N))]
    with ω hω
  let S : (N ω).FiniteSpanningSetsIn {s | MeasurableSet s} :=
    ⟨spanningSets (P.bind N), measurableSet_spanningSets (P.bind N), hω,
      iUnion_spanningSets (P.bind N)⟩
  exact S.sigmaFinite

/-- An almost-everywhere measurable random measure with sigma-finite average admits a
measurable version with sigma-finite values everywhere, without changing its law. -/
theorem exists_measurable_ae_eq_sigmaFinite_of_bind (hN : AEMeasurable N P)
    [SigmaFinite (P.bind N)] :
    ∃ M : Ω → Measure X, Measurable M ∧ M =ᵐ[P] N ∧ ∀ ω, SigmaFinite (M ω) := by
  classical
  let N' := hN.mk N
  have hm : Measurable N' := hN.measurable_mk
  have hbind : P.bind N' = P.bind N := bind_congr_right hN.ae_eq_mk.symm
  let s := spanningSets (P.bind N)
  let good := {ω | ∀ n, N' ω (s n) < ∞}
  have hs : ∀ n, MeasurableSet (s n) := measurableSet_spanningSets (P.bind N)
  have hgood : MeasurableSet good := by
    simp only [good, ofPred_forall]
    exact MeasurableSet.iInter fun n => measurableSet_lt
      ((Measure.measurable_coe (hs n)).comp hm) measurable_const
  have hae : ∀ᵐ ω ∂P, ω ∈ good :=
    ae_forall_measure_lt_top_of_bind hm.aemeasurable fun n => by
      rw [hbind]
      exact measure_spanningSets_lt_top (P.bind N) n
  refine ⟨good.indicator N', hm.indicator hgood, ?_, ?_⟩
  · filter_upwards [hae, hN.ae_eq_mk] with ω hω heq
    exact (indicator_of_mem hω N').trans heq.symm
  · intro ω
    by_cases hω : ω ∈ good
    · rw [indicator_of_mem hω]
      let S : (N' ω).FiniteSpanningSetsIn {s | MeasurableSet s} :=
        ⟨s, hs, hω, iUnion_spanningSets (P.bind N)⟩
      exact S.sigmaFinite
    · rw [indicator_of_notMem hω]
      infer_instance

end RandomMeasures

section OrderAndAdditivity

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- `Measure.join` is monotone in the measure on measures. -/
@[gcongr]
theorem join_mono {m₁ m₂ : Measure (Measure α)} (h : m₁ ≤ m₂) : m₁.join ≤ m₂.join :=
  le_iff.2 fun _ hs => by
    rw [join_apply hs, join_apply hs]
    exact lintegral_mono' h le_rfl

/-- `Measure.join` distributes over binary addition of measures. -/
@[simp]
theorem join_add (m₁ m₂ : Measure (Measure α)) : (m₁ + m₂).join = m₁.join + m₂.join := by
  ext s hs
  simp [hs]

/-- `Measure.bind` is monotone in both the mixing measure and the kernel family. -/
theorem bind_mono {μ ν : Measure α} {f g : α → Measure β} (hμν : μ ≤ ν)
    (hfg : ∀ᵐ x ∂μ, f x ≤ g x) (hf : AEMeasurable f μ) (hg : AEMeasurable g ν) :
    μ.bind f ≤ ν.bind g :=
  le_iff.2 fun s hs => by
    rw [bind_apply hs hf, bind_apply hs hg]
    exact (lintegral_mono_ae (hfg.mono fun _ hx => hx s)).trans (lintegral_mono' hμν le_rfl)

/-- `Measure.bind` is monotone in the mixing measure. -/
theorem bind_mono_left {μ ν : Measure α} {f : α → Measure β} (hf : AEMeasurable f ν) (h : μ ≤ ν) :
    μ.bind f ≤ ν.bind f :=
  bind_mono h (Filter.Eventually.of_forall fun _ => le_rfl) (hf.mono_measure h) hf

/-- `Measure.bind` distributes over binary addition in the mixing measure. -/
theorem bind_add {μ ν : Measure α} {f : α → Measure β} (hf : AEMeasurable f (μ + ν)) :
    (μ + ν).bind f = μ.bind f + ν.bind f := by
  ext s hs
  rw [bind_apply hs hf, add_apply,
    bind_apply hs (hf.mono_measure (Measure.le_add_right le_rfl)),
    bind_apply hs (hf.mono_measure (Measure.le_add_left le_rfl)), lintegral_add_measure]

/-- `Measure.bind` distributes over `Finset` sums in the mixing measure. -/
theorem bind_finset_sum {ι : Type*} (s : Finset ι) (μ : ι → Measure α) {f : α → Measure β}
    (hf : AEMeasurable f (∑ i ∈ s, μ i)) :
    (∑ i ∈ s, μ i).bind f = ∑ i ∈ s, (μ i).bind f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha] at hf ⊢
    rw [bind_add hf, ih (hf.mono_measure (Measure.le_add_left le_rfl)), Finset.sum_insert ha]

/-- **Singleton lower bound for `Measure.bind`.** Restricting the mixture integral to a single
input point `x` bounds `(μ.bind f) s` below by `μ {x} * f x s`, without requiring `s` to be
measurable. -/
theorem singleton_mul_apply_le_bind_apply (μ : Measure α) {f : α → Measure β}
    (hf : AEMeasurable f μ) (x : α) {s : Set β} :
    μ {x} * f x s ≤ (μ.bind f) s := by
  by_cases hx : μ {x} = 0
  · simp [hx]
  · let g := hf.mk f
    have hg : Measurable g := hf.measurable_mk
    have hfx : f x = g x := by
      by_contra hne
      have hnull : μ {a | f a ≠ g a} = 0 := ae_iff.mp hf.ae_eq_mk
      exact hx (measure_mono_null (singleton_subset_iff.mpr hne) hnull)
    let t := toMeasurable (μ.bind g) s
    have ht : MeasurableSet t := measurableSet_toMeasurable (μ.bind g) s
    rw [bind_congr_right hf.ae_eq_mk, hfx]
    calc
      μ {x} * g x s ≤ μ {x} * g x t := by
        gcongr; exact subset_toMeasurable (μ.bind g) s
      _ = ∫⁻ a in {x}, g a t ∂μ := by
        rw [mul_comm]
        exact (lintegral_singleton' (f := fun a => g a t) ((measurable_coe ht).comp hg) x).symm
      _ ≤ ∫⁻ a, g a t ∂μ := setLIntegral_le_lintegral _ _
      _ = (μ.bind g) t := (bind_apply ht hg.aemeasurable).symm
      _ = (μ.bind g) s := measure_toMeasurable s

end OrderAndAdditivity

end MeasureTheory.Measure
