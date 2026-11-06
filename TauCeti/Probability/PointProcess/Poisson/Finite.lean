/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.Integration
public import TauCeti.Probability.Distributions.Poisson.Basic
public import TauCeti.Probability.Distributions.Poisson.Measurability
public import TauCeti.MeasureTheory.Measure.ProductKernel

/-!
# Finite Poisson sampling laws

Sample a Poisson number of independent locations with probability law `Q`, retaining repeated
locations as separate Dirac occurrences. The resulting law on `Measure X` has intensity `r • Q`.
Its exponential formula is the finite-intensity building block for countable superposition
constructions of Poisson random measures. No topology or atomlessness is required.

The construction follows Last–Penrose, *Lectures on the Poisson Process* (2018), Theorem 3.6.
The exponential formula uses Mathlib's extended exponential `EReal.exp`, so infinite test
values are allowed and contribute a zero factor.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {X : Type*} [MeasurableSpace X]

private noncomputable def poissonSample (p : ℕ × (ℕ → X)) : Measure X :=
  ∑ i ∈ Finset.range p.1, Measure.dirac (p.2 i)

private theorem measurable_poissonSample : Measurable (poissonSample (X := X)) := by
  apply measurable_from_prod_countable_right
  intro n
  simpa only [poissonSample, Function.comp_def] using
    (Finset.measurable_sum (Finset.range n) fun i _ => Measure.measurable_dirac.comp
      (measurable_pi_apply i : Measurable fun x : ℕ → X => x i))

/-- The law of a Poisson number of independent locations of law `Q`, with multiplicities. -/
noncomputable def finitePoissonLaw (r : ℝ≥0) (Q : Measure X) : Measure (Measure X) :=
  ((poissonMeasure r).prod (Measure.infinitePi fun _ : ℕ => Q)).map poissonSample

/-- The sampling representation of the finite Poisson law. -/
theorem finitePoissonLaw_def (r : ℝ≥0) (Q : Measure X) :
    finitePoissonLaw r Q =
      ((poissonMeasure r).prod (Measure.infinitePi fun _ : ℕ => Q)).map
        (fun p : ℕ × (ℕ → X) => ∑ i ∈ Finset.range p.1, Measure.dirac (p.2 i)) := (rfl)

instance (r : ℝ≥0) (Q : Measure X) [IsProbabilityMeasure Q] :
    IsProbabilityMeasure (finitePoissonLaw r Q) := by
  rw [finitePoissonLaw]
  exact Measure.isProbabilityMeasure_map_iff measurable_poissonSample.aemeasurable |>.2
    inferInstance

/-- Integration against the sampling law is a Poisson mixture of finite independent samples. -/
theorem lintegral_finitePoissonLaw (r : ℝ≥0) (Q : Measure X) [IsProbabilityMeasure Q]
    {g : Measure X → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ξ, g ξ ∂finitePoissonLaw r Q =
      ∫⁻ n, ∫⁻ x, g (∑ i ∈ Finset.range n, Measure.dirac (x i))
        ∂Measure.infinitePi (fun _ : ℕ => Q) ∂poissonMeasure r := by
  rw [finitePoissonLaw, lintegral_map hg measurable_poissonSample]
  exact lintegral_prod _ (hg.comp measurable_poissonSample).aemeasurable

/-- The total number of occurrences has the Poisson law, even when locations coincide. -/
@[simp] theorem map_mass_finitePoissonLaw (r : ℝ≥0) (Q : Measure X) [IsProbabilityMeasure Q] :
    (finitePoissonLaw r Q).map (fun ξ => ξ univ) =
      (poissonMeasure r).map (Nat.cast : ℕ → ℝ≥0∞) := by
  rw [finitePoissonLaw, Measure.map_map (Measure.measurable_coe MeasurableSet.univ)
    measurable_poissonSample]
  have h : (fun p : ℕ × (ℕ → X) => poissonSample p univ) =
      (fun p => (p.1 : ℝ≥0∞)) := by
    funext p
    simp [poissonSample, sum_apply]
  rw [Function.comp_def, h, ← Function.comp_def (f := (Nat.cast : ℕ → ℝ≥0∞)),
    ← Measure.map_map (by fun_prop) measurable_fst, Measure.map_fst_prod]
  simp

private theorem exp_neg_lintegral_poissonSample {f : X → ℝ≥0∞} (hf : Measurable f)
    (n : ℕ) (x : ℕ → X) :
    EReal.exp (-((∫⁻ y, f y ∂poissonSample (n, x)).toEReal)) =
      ∏ i ∈ Finset.range n, EReal.exp (-(f (x i)).toEReal) := by
  induction n with
  | zero => simp [poissonSample]
  | succ n ih =>
    simp only [poissonSample, Finset.range_add_one, Finset.sum_insert (Finset.notMem_range_self),
      lintegral_add_measure, lintegral_dirac' _ hf, EReal.coe_ennreal_add,
      EReal.neg_add (.inl (EReal.coe_ennreal_ne_bot _))
        (.inr (EReal.coe_ennreal_ne_bot _)), sub_eq_add_neg, EReal.exp_add,
      Finset.prod_insert (Finset.notMem_range_self)]
    exact congrArg (EReal.exp (-(f (x n)).toEReal) * ·) ih

/-- The exponential formula for the finite Poisson sampling law, including infinite tests.
The right side is `exp (r * (∫ exp(-f) dQ - 1))`. -/
theorem lintegral_exp_neg_finitePoissonLaw (r : ℝ≥0) (Q : Measure X)
    [IsProbabilityMeasure Q] {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ξ, EReal.exp (-(∫⁻ x, f x ∂ξ).toEReal) ∂finitePoissonLaw r Q =
      ENNReal.ofReal (Real.exp ((r : ℝ) *
        ((∫⁻ x, EReal.exp (-(f x).toEReal) ∂Q).toReal - 1))) := by
  have hm : Measurable fun x => EReal.exp (-(f x).toEReal) := by fun_prop
  have hM : Measurable fun ξ : Measure X => EReal.exp (-(∫⁻ x, f x ∂ξ).toEReal) := by
    fun_prop
  rw [lintegral_finitePoissonLaw r Q hM]
  have heq (n : ℕ) (x : ℕ → X) := exp_neg_lintegral_poissonSample hf n x
  simp only [poissonSample] at heq
  simp_rw [heq]
  have hprod (n : ℕ) :
      ∫⁻ x, ∏ i ∈ Finset.range n, EReal.exp (-(f (x i)).toEReal)
        ∂Measure.infinitePi (fun _ : ℕ => Q) =
      (∫⁻ x, EReal.exp (-(f x).toEReal) ∂Q) ^ n := by
    rw [lintegral_prod_eq_prod_lintegral_of_indepFun (Finset.range n) _
      (iIndepFun_infinitePi (fun _ => hm)) (fun i => hm.comp (measurable_pi_apply i))]
    simp only [(measurePreserving_eval_infinitePi (fun _ : ℕ => Q) _).lintegral_comp hm,
      Finset.prod_const, Finset.card_range]
  simp_rw [hprod]
  generalize haeq : (∫⁻ x, EReal.exp (-(f x).toEReal) ∂Q) = a
  have ha : a ≤ 1 := by
    rw [← haeq]
    calc
      (∫⁻ x, EReal.exp (-(f x).toEReal) ∂Q) ≤ ∫⁻ _ : X, (1 : ℝ≥0∞) ∂Q :=
        lintegral_mono fun x =>
        EReal.exp_le_one_iff.mpr (EReal.neg_le_zero.mpr (EReal.coe_ennreal_nonneg _))
      _ = 1 := by simp
  have hpow (n : ℕ) : a ^ n = ENNReal.ofReal (a.toReal ^ n) := by
    rw [ENNReal.ofReal_pow (ENNReal.toReal_nonneg), ENNReal.ofReal_toReal (ne_top_of_le_ne_top
      ENNReal.one_ne_top ha)]
  simp_rw [hpow]
  convert lintegral_ofReal_poissonMeasure (fun n => by positivity) r
    (hasSum_pow_poissonMeasure r a.toReal) using 1
  congr 2
  ring

/-- Set probabilities can be computed directly from the independent sample representation. -/
theorem finitePoissonLaw_apply (r : ℝ≥0) (Q : Measure X) [IsProbabilityMeasure Q]
    {s : Set (Measure X)} (hs : MeasurableSet s) :
    finitePoissonLaw r Q s = ∫⁻ n,
      Measure.infinitePi (fun _ : ℕ => Q)
        {x | (∑ i ∈ Finset.range n, Measure.dirac (x i)) ∈ s} ∂poissonMeasure r := by
  rw [← lintegral_indicator_one hs, lintegral_finitePoissonLaw r Q
    (measurable_one.indicator hs)]
  apply lintegral_congr
  intro n
  exact lintegral_indicator_one (hs.preimage (by
    exact Finset.measurable_sum _ fun i _ => Measure.measurable_dirac.comp
      (measurable_pi_apply i : Measurable fun x : ℕ → X => x i)))

/-- The sampling law is jointly measurable in its rate and probability distribution. -/
@[fun_prop] theorem measurable_finitePoissonLaw :
    Measurable fun p : ℝ≥0 × ProbabilityMeasure X => finitePoissonLaw p.1 (p.2 : Measure X) := by
  have hr : Measurable fun p : ℝ≥0 × ProbabilityMeasure X =>
      (⟨poissonMeasure p.1, inferInstance⟩ : ProbabilityMeasure ℕ) :=
    (measurable_poissonMeasure.comp measurable_fst).subtype_mk
  have hQ : Measurable fun p : ℝ≥0 × ProbabilityMeasure X =>
      (⟨Measure.infinitePi (fun _ : ℕ => (p.2 : Measure X)), inferInstance⟩ :
        ProbabilityMeasure (ℕ → X)) :=
    (TauCeti.MeasureTheory.measurable_infinitePi_const.comp measurable_snd).subtype_mk
  exact (Measure.measurable_map _ measurable_poissonSample).comp
    (ProbabilityMeasure.measurable_fun_prod.comp (hr.prodMk hQ))

/-- The mean random measure of the sampling construction is `r • Q`. -/
@[simp] theorem join_finitePoissonLaw (r : ℝ≥0) (Q : Measure X) [IsProbabilityMeasure Q] :
    (finitePoissonLaw r Q).join = (r : ℝ≥0∞) • Q := by
  ext s hs
  rw [Measure.join_apply hs, lintegral_finitePoissonLaw r Q (Measure.measurable_coe hs)]
  have hmean (n : ℕ) :
      (∫⁻ x : ℕ → X, (∑ i ∈ Finset.range n, Measure.dirac (x i)) s
        ∂Measure.infinitePi (fun _ : ℕ => Q)) = (n : ℝ≥0∞) * Q s := by
    simp only [sum_apply, Measure.dirac_apply' _ hs]
    have hm (i : ℕ) : Measurable fun x : ℕ → X => s.indicator (1 : X → ℝ≥0∞) (x i) :=
      (measurable_one.indicator hs).comp (measurable_pi_apply i)
    rw [lintegral_finsetSum _ (fun i _ => hm i)]
    simp only [(measurePreserving_eval_infinitePi (fun _ : ℕ => Q) _).lintegral_comp
      (measurable_one.indicator hs), lintegral_indicator_one hs, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
  simp_rw [hmean]
  rw [lintegral_mul_const _ (by fun_prop)]
  have hcount : (∫⁻ n : ℕ, (n : ℝ≥0∞) ∂poissonMeasure r) = r := by
    have hsum := hasSum_descFactorial_poissonMeasure r 1
    simp only [Nat.descFactorial_one, pow_one] at hsum
    simpa only [ENNReal.ofReal_natCast, ENNReal.ofReal_coe_nnreal]
      using lintegral_ofReal_poissonMeasure (fun n => Nat.cast_nonneg n) r hsum
  simp [hcount]

/-- Zero rate produces the empty configuration, independently of the location law. -/
@[simp] theorem finitePoissonLaw_zero (Q : Measure X) [IsProbabilityMeasure Q] :
    finitePoissonLaw 0 Q = Measure.dirac 0 := by
  ext s hs
  rw [finitePoissonLaw_apply 0 Q hs, poissonMeasure_zero,
    lintegral_dirac' _ (measurable_of_countable _)]
  simp only [Finset.range_zero, Finset.sum_empty]
  by_cases h : (0 : Measure X) ∈ s <;> simp [h, Measure.dirac_apply' _ hs]

/-- The sampling law is carried by finite measures. -/
theorem ae_isFiniteMeasure_finitePoissonLaw (r : ℝ≥0) (Q : Measure X) :
    ∀ᵐ ξ ∂finitePoissonLaw r Q, IsFiniteMeasure ξ := by
  rw [finitePoissonLaw, ae_map_iff measurable_poissonSample.aemeasurable (by
    simpa only [isFiniteMeasure_iff] using
      (measurableSet_lt (Measure.measurable_coe MeasurableSet.univ) measurable_const))]
  exact Filter.Eventually.of_forall fun p => by
    dsimp only [poissonSample]
    infer_instance

/-- Concentrating all locations at one point retains a Poisson multiplicity at that point. -/
@[simp] theorem finitePoissonLaw_dirac (r : ℝ≥0) (x : X) :
    finitePoissonLaw r (Measure.dirac x) =
      (poissonMeasure r).map (fun n => n • Measure.dirac x) := by
  rw [finitePoissonLaw, Measure.infinitePi_dirac, Measure.prod_dirac,
    Measure.map_map measurable_poissonSample (by fun_prop)]
  congr 1
  funext n
  simp [poissonSample]

/-- Mapping the locations maps the whole sampling law, with no injectivity requirement. -/
theorem map_finitePoissonLaw {Y : Type*} [MeasurableSpace Y] (r : ℝ≥0)
    (Q : Measure X) [IsProbabilityMeasure Q] {f : X → Y} (hf : Measurable f) :
    (finitePoissonLaw r Q).map (fun ξ => ξ.map f) = finitePoissonLaw r (Q.map f) := by
  have hp := Measure.map_prod_map (poissonMeasure r) (Measure.infinitePi (fun _ : ℕ => Q))
    measurable_id (Measurable.of_eval fun i => hf.comp
      (measurable_pi_apply i : Measurable fun x : ℕ → X => x i))
  simp only [Measure.map_id, Function.comp_def] at hp
  rw [finitePoissonLaw, Measure.map_map (Measure.measurable_map f hf) measurable_poissonSample,
    finitePoissonLaw, ← Measure.infinitePi_map_pi _ (fun _ => hf), hp,
    Measure.map_map measurable_poissonSample (by fun_prop)]
  congr 1
  funext p
  simp [poissonSample, Measure.map_finset_sum hf.aemeasurable, Measure.map_dirac' hf]

end TauCeti.Probability
