/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.Integration
public import TauCeti.Probability.Distributions.CompoundPoisson.RandomSum
public import TauCeti.Probability.Distributions.Poisson.SizeBias

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

private theorem measurable_sum_dirac (n : ℕ) :
    Measurable fun x : ℕ → X => ∑ i ∈ Finset.range n, Measure.dirac (x i) :=
  Finset.measurable_sum _ fun i _ => Measure.measurable_dirac.comp (measurable_pi_apply i)

/-- The law of a Poisson number of independent locations with probability law `Q`, retaining
multiplicities; `r` is the mean of the Poisson count. It specializes `compoundPoissonMeasure`
to Dirac-measure jumps. For non-probability `Q`, this still denotes the convolution-power mixture,
not necessarily a probability measure. -/
noncomputable def finitePoissonLaw (r : ℝ≥0) (Q : Measure X) : Measure (Measure X) :=
  compoundPoissonMeasure r (Q.map Measure.dirac)

/-- The finite Poisson law is the compound Poisson law with Dirac-measure jumps. -/
theorem finitePoissonLaw_eq_compoundPoissonMeasure (r : ℝ≥0) (Q : Measure X) :
    finitePoissonLaw r Q = compoundPoissonMeasure r (Q.map Measure.dirac) := (rfl)

instance (r : ℝ≥0) (Q : Measure X) [IsProbabilityMeasure Q] :
    IsProbabilityMeasure (finitePoissonLaw r Q) := by
  rw [finitePoissonLaw]
  infer_instance

/-- The sampling representation of the finite Poisson law. -/
theorem finitePoissonLaw_eq_map_prod_infinitePi (r : ℝ≥0) (Q : Measure X) [IsProbabilityMeasure Q] :
    finitePoissonLaw r Q =
      ((poissonMeasure r).prod (Measure.infinitePi fun _ : ℕ => Q)).map
        (fun p : ℕ × (ℕ → X) => ∑ i ∈ Finset.range p.1, Measure.dirac (p.2 i)) := by
  rw [finitePoissonLaw, ← map_sum_range_prod_poissonMeasure,
    ← Measure.infinitePi_map_pi _ (fun _ => Measure.measurable_dirac)]
  have hp := Measure.map_prod_map (poissonMeasure r) (Measure.infinitePi (fun _ : ℕ => Q))
    measurable_id (Measurable.of_eval fun i => Measure.measurable_dirac.comp
      (measurable_pi_apply i : Measurable fun x : ℕ → X => x i))
  simp only [Measure.map_id, Function.comp_def] at hp
  rw [hp, Measure.map_map (measurable_from_prod_countable_right fun n =>
    Finset.measurable_sum (Finset.range n) fun i _ => measurable_pi_apply i) (by fun_prop)]
  rfl

/-- Integration against the sampling law is a Poisson mixture of finite independent samples. -/
theorem lintegral_finitePoissonLaw (r : ℝ≥0) (Q : Measure X) [IsProbabilityMeasure Q]
    {g : Measure X → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ξ, g ξ ∂finitePoissonLaw r Q =
      ∫⁻ n, ∫⁻ x, g (∑ i ∈ Finset.range n, Measure.dirac (x i))
        ∂Measure.infinitePi (fun _ : ℕ => Q) ∂poissonMeasure r := by
  have hm : Measurable fun p : ℕ × (ℕ → X) =>
      ∑ i ∈ Finset.range p.1, Measure.dirac (p.2 i) :=
    measurable_from_prod_countable_right fun n => measurable_sum_dirac n
  rw [finitePoissonLaw_eq_map_prod_infinitePi, lintegral_map hg hm]
  exact lintegral_prod _ (hg.comp hm).aemeasurable

/-- The total number of occurrences has the Poisson law, even when locations coincide. -/
@[simp] theorem map_mass_finitePoissonLaw (r : ℝ≥0) (Q : Measure X) [IsProbabilityMeasure Q] :
    (finitePoissonLaw r Q).map (fun ξ => ξ univ) =
      (poissonMeasure r).map (Nat.cast : ℕ → ℝ≥0∞) := by
  let mass : Measure X →+ ℝ≥0∞ :=
    { toFun := fun ξ => ξ univ
      map_zero' := by simp
      map_add' := fun _ _ => by simp }
  -- Present the evaluation map as a bundled homomorphism for the transport theorem.
  change (compoundPoissonMeasure r (Q.map Measure.dirac)).map mass = _
  rw [map_compoundPoissonMeasure r _ mass (Measure.measurable_coe MeasurableSet.univ),
    -- Keep the bundled map explicit so rewriting matches its coercion.
    Measure.map_map (show Measurable mass from Measure.measurable_coe MeasurableSet.univ)
      Measure.measurable_dirac]
  have h : mass ∘ Measure.dirac = fun _ : X => (1 : ℝ≥0∞) := by
    funext x
    simp [mass]
  rw [h, Measure.map_const, measure_univ, one_smul, compoundPoissonMeasure_dirac]
  simp

private theorem exp_neg_lintegral_sum_dirac {f : X → ℝ≥0∞} (hf : Measurable f)
    (n : ℕ) (x : ℕ → X) :
    EReal.exp (-((∫⁻ y, f y ∂(∑ i ∈ Finset.range n, Measure.dirac (x i))).toEReal)) =
      ∏ i ∈ Finset.range n, EReal.exp (-(f (x i)).toEReal) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.range_add_one, Finset.sum_insert (Finset.notMem_range_self),
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
  simp_rw [exp_neg_lintegral_sum_dirac hf]
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
  exact lintegral_indicator_one (hs.preimage (measurable_sum_dirac n))

/-- The sampling law is jointly measurable in its rate and probability distribution. -/
@[fun_prop] theorem measurable_finitePoissonLaw :
    Measurable fun p : ℝ≥0 × ProbabilityMeasure X => finitePoissonLaw p.1 (p.2 : Measure X) := by
  have hQ : Measurable fun p : ℝ≥0 × ProbabilityMeasure X =>
      (⟨(p.2 : Measure X).map Measure.dirac, inferInstance⟩ : ProbabilityMeasure (Measure X)) :=
    ((Measure.measurable_map _ Measure.measurable_dirac).comp
      (measurable_subtype_coe.comp measurable_snd)).subtype_mk
  exact measurable_compoundPoissonMeasure_probability.comp (measurable_fst.prodMk hQ)

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
  simp

/-- Zero rate produces the empty configuration, independently of the location law. -/
@[simp] theorem finitePoissonLaw_zero (Q : Measure X) :
    finitePoissonLaw 0 Q = Measure.dirac 0 :=
  compoundPoissonMeasure_zero _

/-- The sampling law is carried by finite measures. -/
theorem ae_isFiniteMeasure_finitePoissonLaw (r : ℝ≥0) (Q : Measure X) :
    ∀ᵐ ξ ∂finitePoissonLaw r Q, IsFiniteMeasure ξ := by
  have hs : MeasurableSet {ξ : Measure X | IsFiniteMeasure ξ} := by
    simpa only [isFiniteMeasure_iff] using
      (measurableSet_lt (Measure.measurable_coe MeasurableSet.univ) measurable_const)
  have hQ : ∀ᵐ ξ ∂Q.map Measure.dirac, IsFiniteMeasure ξ :=
    (ae_map_iff Measure.measurable_dirac.aemeasurable hs).2
      (Filter.Eventually.of_forall fun _ => inferInstance)
  -- Work with null sets directly: Q need not even be s-finite.
  have hpow (n : ℕ) : ∀ᵐ ξ ∂(Q.map Measure.dirac).convolutionPower n, IsFiniteMeasure ξ := by
    induction n with
    | zero => simpa only [Measure.convolutionPower_zero, ae_dirac_iff hs] using
        (inferInstance : IsFiniteMeasure (0 : Measure X))
    | succ n ih =>
      rw [Measure.convolutionPower_succ, Measure.conv, ae_map_iff measurable_add.aemeasurable hs,
        ae_iff]
      apply Measure.measure_prod_null_of_ae_null (hs.preimage measurable_add).compl
      filter_upwards [ih] with ξ hξ
      have h : ∀ᵐ η ∂Q.map Measure.dirac, IsFiniteMeasure (ξ + η) := hQ.mono fun η hη => by
        let := hξ
        let := hη
        infer_instance
      exact h
  rw [finitePoissonLaw, compoundPoissonMeasure_def, ae_iff]
  -- Express the exceptional set as a complement to match the measurable-set bind formula.
  change ((poissonMeasure r).bind (Q.map Measure.dirac).convolutionPower)
    {ξ | IsFiniteMeasure ξ}ᶜ = 0
  rw [Measure.bind_apply hs.compl Measurable.of_discrete.aemeasurable]
  exact lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall hpow)

/-- Concentrating all locations at one point retains a Poisson multiplicity at that point. -/
@[simp] theorem finitePoissonLaw_dirac (r : ℝ≥0) (x : X) :
    finitePoissonLaw r (Measure.dirac x) =
      (poissonMeasure r).map (fun n => n • Measure.dirac x) := by
  rw [finitePoissonLaw, Measure.map_dirac' Measure.measurable_dirac]
  exact compoundPoissonMeasure_dirac r (Measure.dirac x)

/-- Mapping the locations maps the whole sampling law, with no injectivity requirement. -/
theorem map_finitePoissonLaw {Y : Type*} [MeasurableSpace Y] (r : ℝ≥0)
    (Q : Measure X) [IsProbabilityMeasure Q] {f : X → Y} (hf : Measurable f) :
    (finitePoissonLaw r Q).map (fun ξ => ξ.map f) = finitePoissonLaw r (Q.map f) := by
  let F : Measure X →+ Measure Y :=
    { toFun := fun ξ => ξ.map f
      map_zero' := Measure.map_zero f
      map_add' := fun _ _ => Measure.map_add _ _ hf }
  -- Present the pushforward as a bundled homomorphism for the transport theorem.
  change (compoundPoissonMeasure r (Q.map Measure.dirac)).map F = _
  rw [map_compoundPoissonMeasure r _ F (Measure.measurable_map f hf)]
  -- Unbundle only the local homomorphism so the map-composition lemma matches.
  change compoundPoissonMeasure r ((Q.map Measure.dirac).map (fun ξ => ξ.map f)) = _
  simp only [finitePoissonLaw,
    Measure.map_map (Measure.measurable_map f hf) Measure.measurable_dirac,
    Measure.map_map Measure.measurable_dirac hf, Function.comp_def, Measure.map_dirac' hf]

end TauCeti.Probability
