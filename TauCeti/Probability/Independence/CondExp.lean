/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.ConditionalLExpectation
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Conditioning a function of a known and an independent variable

Let `m` be a sub-σ-algebra, `X` an `m`-measurable random variable and `Y` a random variable
independent of `m`. Given the information in `m`, the value of `X` is known while `Y` keeps its
law, so the conditional expectation of `f (X, Y)` is obtained by freezing `X` and integrating `Y`
out:

`E[f (X, Y) | m] = (fun x ↦ E[f (x, Y)]) ∘ X`  almost everywhere.

This is the computation behind every Markov property of a process with independent increments:
the state at a later time is a function of the present state, which is known, and of an increment
independent of the past.

The proof checks the defining property on each event `A` of `m`: restricted to `A`, the joint law
of `X` and `Y` is the product of the restricted law of `X` and the law of `Y`, and Tonelli's or
Fubini's theorem integrates `Y` out. Both the unnormalized restricted-measure integral formulas
(including null events `μ A = 0` and the joint-independence hypothesis relative to `σ(A, X)`) and
the `condLExp` / `condExp` freezing identities are provided.

## Main declarations

* `TauCeti.Probability.map_restrict_prodMk_eq_prod_of_indep`: on an event of `m`, the joint law
  of `X` and `Y` is a product measure.
* `TauCeti.Probability.setLIntegral_comp_prodMk_eq_setLIntegral_lintegral_of_map_restrict_eq_prod`,
  `TauCeti.Probability.setLIntegral_comp_prodMk_eq_lintegral_of_indep`,
  `TauCeti.Probability.setLIntegral_comp_prodMk_eq_lintegral_of_indep_generateFrom_sup`:
  Tonelli formulas on a restricted event `A` against `(μ.restrict A).map X` and the fiber law.
* `TauCeti.Probability.condLExp_comp_prodMk_ae_eq_lintegral_of_indep`: the nonnegative conditional
  expectation `μ⁻[f (X, Y) | m]`.
* `TauCeti.Probability.setIntegral_comp_prodMk_eq_setIntegral_integral_of_map_restrict_eq_prod`,
  `TauCeti.Probability.setIntegral_comp_prodMk_eq_integral_of_indep`,
  `TauCeti.Probability.setIntegral_comp_prodMk_eq_integral_of_indep_generateFrom_sup`:
  Fubini formulas under `IntegrableOn (fun ω ↦ f (X ω, Y ω)) A μ`, together with product
  integrability `TauCeti.Probability.integrable_prod_of_integrableOn_comp_prodMk_of_indep`.
* `TauCeti.Probability.condExp_comp_prodMk_ae_eq_integral_of_indep`: the Bochner conditional
  expectation `μ[f (X, Y) | m]`.
* `ProbabilityTheory.Indep.condExp_eq_of_le_of_stronglyMeasurable_sup`: extra information
  independent of the future does not change the conditional prediction of a past/future observable.

## References

* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer, 2004,
  Lemma 2.3.4 (the Independence Lemma).
* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition, Springer,
  1991, Chapter 2, §6.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace TauCeti.Probability

variable {Ω α β E : Type*} {m mΩ : MeasurableSpace Ω} {mα : MeasurableSpace α}
  {mβ : MeasurableSpace β} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → α} {Y : Ω → β}

/-- Restricted to an event `A` of `m`, the joint law of an `m`-measurable `X` and of a `Y`
independent of `m` is the product of the law of `X` under `μ.restrict A` and the law of `Y`. -/
theorem map_restrict_prodMk_eq_prod_of_indep (hm : m ≤ mΩ) (hX : Measurable[m] X)
    (hY : Measurable Y) (hindep : Indep (mβ.comap Y) m μ) {A : Set Ω} (hA : MeasurableSet[m] A) :
    (μ.restrict A).map (fun ω ↦ (X ω, Y ω)) = ((μ.restrict A).map X).prod (μ.map Y) := by
  have hX' : Measurable X := hX.mono hm le_rfl
  refine (Measure.prod_eq fun s t hs ht ↦ ?_).symm
  simp only [Measure.map_apply (hX'.prodMk hY) (hs.prod ht), Measure.map_apply hX' hs,
    Measure.map_apply hY ht, Measure.restrict_apply' (hm A hA), Set.mk_preimage_prod]
  -- The event `{X ∈ s} ∩ A` lies in `m`, so it is independent of `{Y ∈ t}`.
  rw [mul_comm, ← (Indep_iff _ _ μ).1 hindep _ _ ⟨t, ht, rfl⟩ ((hX hs).inter hA)]
  congr 1
  ac_rfl

/-- **Restricted Tonelli factorization under independence.** On an `m`-measurable event `A`, the
Lebesgue integral of `f (X, Y)` factors as an iterated integral against the unnormalized
restricted image measure `(μ.restrict A).map X` and `μ.map Y`, including when `μ A = 0`. -/
theorem setLIntegral_comp_prodMk_eq_lintegral_of_indep (hm : m ≤ mΩ) (hX : Measurable[m] X)
    (hY : Measurable Y) (hindep : Indep (mβ.comap Y) m μ) {f : α × β → ℝ≥0∞}
    (hf : Measurable f) {A : Set Ω} (hA : MeasurableSet[m] A) :
    ∫⁻ ω in A, f (X ω, Y ω) ∂μ =
      ∫⁻ y, ∫⁻ x, f (x, y) ∂((μ.restrict A).map X) ∂(μ.map Y) := by
  have hX' : Measurable X := hX.mono hm le_rfl
  have hprod := map_restrict_prodMk_eq_prod_of_indep hm hX hY hindep hA
  rw [← lintegral_map hf (hX'.prodMk hY), hprod, lintegral_prod_symm _ hf.aemeasurable]

omit [IsFiniteMeasure μ] in
/-- Given a restricted product-measure factorization
`(μ.restrict A).map (X, Y) = ((μ.restrict A).map X).prod ν`, integrating `f (X, Y)` over `A` equals
integrating `ω ↦ ∫⁻ y, f (X ω, y) ∂ν` over `A`. -/
theorem setLIntegral_comp_prodMk_eq_setLIntegral_lintegral_of_map_restrict_eq_prod
    {ν : Measure β} [SFinite ν] (hX : Measurable X) (hY : Measurable Y) {A : Set Ω}
    (hprod : (μ.restrict A).map (fun ω ↦ (X ω, Y ω)) = ((μ.restrict A).map X).prod ν)
    {f : α × β → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω in A, f (X ω, Y ω) ∂μ = ∫⁻ ω in A, ∫⁻ y, f (X ω, y) ∂ν ∂μ := by
  rw [← lintegral_map hf (hX.prodMk hY), hprod, lintegral_prod _ hf.aemeasurable,
    lintegral_map hf.lintegral_prod_right' hX]

/-- On an `m`-measurable event `A`, integrating `f (X, Y)` equals integrating the frozen fiber
integral `ω ↦ ∫⁻ y, f (X ω, y) ∂(μ.map Y)` over `A`. -/
theorem setLIntegral_comp_prodMk_eq_setLIntegral_lintegral_of_indep (hm : m ≤ mΩ)
    (hX : Measurable[m] X) (hY : Measurable Y) (hindep : Indep (mβ.comap Y) m μ)
    {f : α × β → ℝ≥0∞} (hf : Measurable f) {A : Set Ω} (hA : MeasurableSet[m] A) :
    ∫⁻ ω in A, f (X ω, Y ω) ∂μ = ∫⁻ ω in A, ∫⁻ y, f (X ω, y) ∂(μ.map Y) ∂μ :=
  setLIntegral_comp_prodMk_eq_setLIntegral_lintegral_of_map_restrict_eq_prod (hX.mono hm le_rfl) hY
    (map_restrict_prodMk_eq_prod_of_indep hm hX hY hindep hA) hf

/-- **Nonnegative freezing under independence.** If `X` is `m`-measurable and `Y` is independent
of `m`, the nonnegative conditional expectation of `f (X, Y)` given `m` is almost everywhere
`ω ↦ ∫⁻ y, f (X ω, y) ∂(μ.map Y)`, with no finiteness assumption on `f`. -/
theorem condLExp_comp_prodMk_ae_eq_lintegral_of_indep (hm : m ≤ mΩ) (hX : Measurable[m] X)
    (hY : Measurable Y) (hindep : Indep (mβ.comap Y) m μ) {f : α × β → ℝ≥0∞}
    (hf : Measurable f) :
    μ⁻[fun ω ↦ f (X ω, Y ω) | m] =ᵐ[μ] fun ω ↦ ∫⁻ y, f (X ω, y) ∂(μ.map Y) :=
  (ae_eq_condLExp hm μ _ (hf.lintegral_prod_right'.comp hX) fun _ hA ↦
    (setLIntegral_comp_prodMk_eq_setLIntegral_lintegral_of_indep hm hX hY hindep hf hA).symm).symm

/-- If `Y` is jointly independent of `σ(A, X)`, the Lebesgue integral of `f (X, Y)` over `A`
factors through `(μ.restrict A).map X` and `μ.map Y`. -/
theorem setLIntegral_comp_prodMk_eq_lintegral_of_indep_generateFrom_sup
    {A : Set Ω} (hA : MeasurableSet A) (hX : Measurable X) (hY : Measurable Y)
    (hindep : Indep (mβ.comap Y) (MeasurableSpace.generateFrom {A} ⊔ mα.comap X) μ)
    {f : α × β → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω in A, f (X ω, Y ω) ∂μ =
      ∫⁻ y, ∫⁻ x, f (x, y) ∂((μ.restrict A).map X) ∂(μ.map Y) :=
  setLIntegral_comp_prodMk_eq_lintegral_of_indep
    (sup_le (MeasurableSpace.generateFrom_le (by rintro _ rfl; exact hA)) hX.comap_le)
    ((comap_measurable X).mono le_sup_right le_rfl) hY hindep hf
    ((le_sup_left : MeasurableSpace.generateFrom {A} ≤ _) A
      (MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton A)))

omit [NormedSpace ℝ E] in
/-- Integrability of `f (X, Y)` on an `m`-measurable event `A` transfers to product integrability
of `f` under `((μ.restrict A).map X).prod (μ.map Y)`. -/
theorem integrable_prod_of_integrableOn_comp_prodMk_of_indep (hm : m ≤ mΩ) (hX : Measurable[m] X)
    (hY : Measurable Y) (hindep : Indep (mβ.comap Y) m μ) {f : α × β → E}
    (hf : StronglyMeasurable f) {A : Set Ω} (hA : MeasurableSet[m] A)
    (hint : IntegrableOn (fun ω ↦ f (X ω, Y ω)) A μ) :
    Integrable f (((μ.restrict A).map X).prod (μ.map Y)) := by
  have hXY : Measurable fun ω ↦ (X ω, Y ω) := (hX.mono hm le_rfl).prodMk hY
  rw [← map_restrict_prodMk_eq_prod_of_indep hm hX hY hindep hA,
    integrable_map_measure hf.aestronglyMeasurable hXY.aemeasurable]
  exact hint

/-- **Restricted Fubini factorization under independence.** Under `IntegrableOn` on `A ∈ m`,
the Bochner integral of `f (X, Y)` over `A` equals the iterated integral against
`(μ.restrict A).map X` and `μ.map Y`, including when `μ A = 0`. -/
theorem setIntegral_comp_prodMk_eq_integral_of_indep (hm : m ≤ mΩ) (hX : Measurable[m] X)
    (hY : Measurable Y) (hindep : Indep (mβ.comap Y) m μ) {f : α × β → E}
    (hf : StronglyMeasurable f) {A : Set Ω} (hA : MeasurableSet[m] A)
    (hint : IntegrableOn (fun ω ↦ f (X ω, Y ω)) A μ) :
    ∫ ω in A, f (X ω, Y ω) ∂μ =
      ∫ y, ∫ x, f (x, y) ∂((μ.restrict A).map X) ∂(μ.map Y) := by
  have hXY : Measurable fun ω ↦ (X ω, Y ω) := (hX.mono hm le_rfl).prodMk hY
  have hprod := map_restrict_prodMk_eq_prod_of_indep hm hX hY hindep hA
  have hfi := integrable_prod_of_integrableOn_comp_prodMk_of_indep hm hX hY hindep hf hA hint
  rw [← integral_map hXY.aemeasurable hf.aestronglyMeasurable, hprod, integral_prod_symm _ hfi]

/-- Given a restricted product-measure factorization
`(μ.restrict A).map (X, Y) = ((μ.restrict A).map X).prod ν`, an integrable `f (X, Y)` on `A` has
integrable frozen fiber integral `ω ↦ ∫ y, f (X ω, y) ∂ν` with the same set integral over `A`. -/
theorem setIntegral_comp_prodMk_eq_setIntegral_integral_of_map_restrict_eq_prod
    {ν : Measure β} [SigmaFinite ν] (hX : Measurable X) (hY : Measurable Y) {A : Set Ω}
    (hprod : (μ.restrict A).map (fun ω ↦ (X ω, Y ω)) = ((μ.restrict A).map X).prod ν)
    {f : α × β → E} (hf : StronglyMeasurable f)
    (hint : IntegrableOn (fun ω ↦ f (X ω, Y ω)) A μ) :
    IntegrableOn (fun ω ↦ ∫ y, f (X ω, y) ∂ν) A μ ∧
      ∫ ω in A, ∫ y, f (X ω, y) ∂ν ∂μ = ∫ ω in A, f (X ω, Y ω) ∂μ := by
  have hXY : Measurable fun ω ↦ (X ω, Y ω) := hX.prodMk hY
  have hg : StronglyMeasurable fun x ↦ ∫ y, f (x, y) ∂ν := hf.integral_prod_right'
  have hfi : Integrable f (((μ.restrict A).map X).prod ν) := by
    rwa [← hprod, integrable_map_measure hf.aestronglyMeasurable hXY.aemeasurable]
  refine ⟨(integrable_map_measure hg.aestronglyMeasurable hX.aemeasurable).1
    hfi.integral_prod_left, ?_⟩
  rw [← integral_map hXY.aemeasurable hf.aestronglyMeasurable, hprod, integral_prod _ hfi,
    integral_map hX.aemeasurable hg.aestronglyMeasurable]

/-- On an `m`-measurable event `A`, an integrable `f (X, Y)` has the same set integral as its
frozen fiber integral `ω ↦ ∫ y, f (X ω, y) ∂(μ.map Y)`, which is itself integrable on `A`. -/
theorem setIntegral_comp_prodMk_eq_setIntegral_integral_of_indep (hm : m ≤ mΩ)
    (hX : Measurable[m] X) (hY : Measurable Y) (hindep : Indep (mβ.comap Y) m μ)
    {f : α × β → E} (hf : StronglyMeasurable f) {A : Set Ω} (hA : MeasurableSet[m] A)
    (hint : IntegrableOn (fun ω ↦ f (X ω, Y ω)) A μ) :
    IntegrableOn (fun ω ↦ ∫ y, f (X ω, y) ∂(μ.map Y)) A μ ∧
      ∫ ω in A, ∫ y, f (X ω, y) ∂(μ.map Y) ∂μ = ∫ ω in A, f (X ω, Y ω) ∂μ :=
  setIntegral_comp_prodMk_eq_setIntegral_integral_of_map_restrict_eq_prod (hX.mono hm le_rfl) hY
    (map_restrict_prodMk_eq_prod_of_indep hm hX hY hindep hA) hf hint

/-- If `Y` is jointly independent of `σ(A, X)` and `f (X, Y)` is integrable on `A`, then `f` is
integrable for `((μ.restrict A).map X).prod (μ.map Y)` and its set integral over `A` factors
through `(μ.restrict A).map X` and `μ.map Y`. -/
theorem setIntegral_comp_prodMk_eq_integral_of_indep_generateFrom_sup
    {A : Set Ω} (hA : MeasurableSet A) (hX : Measurable X) (hY : Measurable Y)
    (hindep : Indep (mβ.comap Y) (MeasurableSpace.generateFrom {A} ⊔ mα.comap X) μ)
    {f : α × β → E} (hf : StronglyMeasurable f)
    (hint : IntegrableOn (fun ω ↦ f (X ω, Y ω)) A μ) :
    Integrable f (((μ.restrict A).map X).prod (μ.map Y)) ∧
      ∫ ω in A, f (X ω, Y ω) ∂μ =
        ∫ y, ∫ x, f (x, y) ∂((μ.restrict A).map X) ∂(μ.map Y) := by
  have hm : MeasurableSpace.generateFrom {A} ⊔ mα.comap X ≤ mΩ :=
    sup_le (MeasurableSpace.generateFrom_le (by rintro _ rfl; exact hA)) hX.comap_le
  have hXm : Measurable[MeasurableSpace.generateFrom {A} ⊔ mα.comap X] X :=
    (comap_measurable X).mono le_sup_right le_rfl
  have hAm : MeasurableSet[MeasurableSpace.generateFrom {A} ⊔ mα.comap X] A :=
    (le_sup_left : MeasurableSpace.generateFrom {A} ≤ _) A
      (MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton A))
  exact ⟨integrable_prod_of_integrableOn_comp_prodMk_of_indep hm hXm hY hindep hf hAm hint,
    setIntegral_comp_prodMk_eq_integral_of_indep hm hXm hY hindep hf hAm hint⟩

/-- **Freezing the known variable.** If `X` is `m`-measurable and `Y` is independent of `m`, the
conditional expectation of `f (X, Y)` given `m` is almost everywhere the integral of
`y ↦ f (X ω, y)` against the law of `Y`. -/
theorem condExp_comp_prodMk_ae_eq_integral_of_indep [CompleteSpace E] (hm : m ≤ mΩ)
    (hX : Measurable[m] X) (hY : Measurable Y) (hindep : Indep (mβ.comap Y) m μ) {f : α × β → E}
    (hf : StronglyMeasurable f) (hint : Integrable (fun ω ↦ f (X ω, Y ω)) μ) :
    μ[fun ω ↦ f (X ω, Y ω) | m] =ᵐ[μ] fun ω ↦ ∫ y, f (X ω, y) ∂(μ.map Y) := by
  have hg : StronglyMeasurable fun x ↦ ∫ y, f (x, y) ∂(μ.map Y) := hf.integral_prod_right'
  exact (ae_eq_condExp_of_forall_setIntegral_eq (g := fun ω ↦ ∫ y, f (X ω, y) ∂(μ.map Y)) hm hint
    (fun A hA _ ↦ (setIntegral_comp_prodMk_eq_setIntegral_integral_of_indep hm hX hY hindep hf hA
      hint.integrableOn).1)
    (fun A hA _ ↦ (setIntegral_comp_prodMk_eq_setIntegral_integral_of_indep hm hX hY hindep hf hA
      hint.integrableOn).2)
    (hg.comp_measurable hX).aestronglyMeasurable).symm

end TauCeti.Probability

namespace ProbabilityTheory.Indep

variable {Ω E : Type*} {m₁ m₂ m₃ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsFiniteMeasure μ] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- If `m₂` is independent of `m₃`, then an integrable observable of `m₁ ⊔ m₃`, with
`m₁ ≤ m₂`, has the same conditional expectation given `m₂` as given `m₁`.
Thus the extra information in `m₂` does not help predict such an observable. -/
theorem condExp_eq_of_le_of_stronglyMeasurable_sup (h : Indep m₂ m₃ μ)
    (h₁₂ : m₁ ≤ m₂) (h₂ : m₂ ≤ mΩ) (h₃ : m₃ ≤ mΩ) {f : Ω → E}
    (hf : StronglyMeasurable[m₁ ⊔ m₃] f) (hint : Integrable f μ) :
    μ[f | m₂] =ᵐ[μ] μ[f | m₁] := by
  -- Factor through the diagonal into m₁.prod m₃, not the ambient product σ-algebra.
  let : MeasurableSpace (Ω × Ω) := m₁.prod m₃
  have hdiag : (m₁.prod m₃).comap (fun ω => (ω, ω)) = m₁ ⊔ m₃ := by
    simpa only [MeasurableSpace.comap_id, id_eq] using
      (MeasurableSpace.comap_prodMk (mβ := m₁) (mγ := m₃) id id)
  have hf' : StronglyMeasurable[(m₁.prod m₃).comap (fun ω => (ω, ω))] f :=
    hdiag.symm ▸ hf
  obtain ⟨g, hg, rfl⟩ := hf'.exists_eq_measurable_comp
  have hY : @Measurable Ω Ω mΩ m₃ id := measurable_id.mono h₃ le_rfl
  have hX : @Measurable Ω Ω m₂ m₁ id := measurable_id.mono h₁₂ le_rfl
  have hbig := TauCeti.Probability.condExp_comp_prodMk_ae_eq_integral_of_indep
    (mα := m₁) (mβ := m₃) h₂ hX hY (by simpa using h.symm) hg
    (by simpa only [Function.comp_def, id_eq] using hint)
  have hsmall := TauCeti.Probability.condExp_comp_prodMk_ae_eq_integral_of_indep
    (mα := m₁) (mβ := m₃) (h₁₂.trans h₂) measurable_id hY
    (by simpa using indep_of_indep_of_le_left h h₁₂ |>.symm) hg
    (by simpa only [Function.comp_def, id_eq] using hint)
  exact hbig.trans hsmall.symm

end ProbabilityTheory.Indep
