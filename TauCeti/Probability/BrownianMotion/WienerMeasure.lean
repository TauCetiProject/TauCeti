/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Process.Kolmogorov
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.MetricSpace.Holder

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import TauCeti.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import TauCeti.Probability.BrownianMotion.Countable
import TauCeti.Probability.Process.Indistinguishable
import TauCeti.Probability.Process.Kolmogorov
import TauCeti.Probability.Process.Kolmogorov.Chentsov

/-!
# Construction, uniqueness, and local Hölder regularity of Wiener measure

Combine countable-skeleton Brownian Gaussian families
(`TauCeti.exists_measurePreserving_brownianRealProjectiveFamily_isKolmogorovProcess_of_countable`)
with the metric-parameter Kolmogorov–Chentsov extension and modification theorems on `ℝ≥0`
(`ProbabilityTheory.IsAEKolmogorovProcess.exists_continuous_holderOnWith_of_dense_nnreal` and
`exists_continuous_holderOnWith_modification_nnreal`) to construct Wiener measure on `C(ℝ≥0, ℝ)`
and establish almost-sure local `< 1 / 2`-Hölder sample-path regularity for Brownian motion.

## Main results

* `ProbabilityTheory.IsPreBrownianReal.isAEKolmogorovProcess`: every pre-Brownian motion satisfies
  the positive even-moment Kolmogorov bound `IsAEKolmogorovProcess B P (2 * n) n (2 * n - 1)‼` for
  all `n ≠ 0`.
* `ProbabilityTheory.IsPreBrownianReal.exists_continuous_modification`: every pre-Brownian motion
  admits a coordinatewise measurable, everywhere continuous modification (hence a Brownian motion).
* `ProbabilityTheory.IsBrownianReal.ae_holderOnWith` and `ae_holderOnWith_Icc`: almost every path
  of any real Brownian motion is `γ`-Hölder on any bounded subset of `ℝ≥0` (in particular `[0, T]`)
  for every `γ < 1 / 2`.
* `TauCeti.isPreBrownianReal_of_dense` and `TauCeti.isBrownianReal_of_dense`: an a.e.-continuous
  process agreeing a.e. on a dense subset `S ⊆ ℝ≥0` with a Brownian Gaussian skeleton is Brownian.
* `TauCeti.exists_wienerMeasure`: there exists a probability measure `W` on `C(ℝ≥0, ℝ)` under which
  the coordinate evaluation process `(t, ω) ↦ ω t` satisfies `IsBrownianReal`.
* `TauCeti.eq_of_isPreBrownianReal_eval`: Wiener measure on `C(ℝ≥0, ℝ)` is uniquely determined by
  its pre-Brownian coordinate evaluation laws.

See Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, second edition, Theorem 2.2.8, and
Lalley, *Brownian Motion*, Theorem 1.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Matrix NNReal Nat RealInnerProductSpace Topology

namespace ProbabilityTheory

namespace IsPreBrownianReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Every pre-Brownian motion satisfies the even-moment `IsAEKolmogorovProcess` bound of order
`2 * n` with time exponent `n` and constant `(2 * n - 1)‼` for each `n ≠ 0`. -/
theorem isAEKolmogorovProcess (hB : IsPreBrownianReal B P) {n : ℕ} (hn : n ≠ 0) :
    IsAEKolmogorovProcess B P (2 * n : ℕ) n (2 * n - 1)‼ := by
  let B' : ℝ≥0 → Ω → ℝ := fun t ↦ (hB.aemeasurable t).mk (B t)
  have hB'_meas (t : ℝ≥0) : Measurable (B' t) := (hB.aemeasurable t).measurable_mk
  have hB'_eq (t : ℝ≥0) : B t =ᵐ[P] B' t := (hB.aemeasurable t).ae_eq_mk
  have hsub (s t : ℝ≥0) : HasLaw (fun ω ↦ B' s ω - B' t ω) (gaussianReal 0 (nndist s t)) P := by
    refine (hB.hasLaw_sub s t).congr ?_
    filter_upwards [hB'_eq s, hB'_eq t] with ω hs ht using by simp [hs, ht]
  exact ⟨B', isKolmogorovProcess_of_hasLaw_sub_gaussianReal hB'_meas hsub hn, hB'_eq⟩

/-- Every pre-Brownian motion admits a coordinatewise measurable modification whose sample paths
are everywhere continuous, and which is therefore a Brownian motion. -/
theorem exists_continuous_modification (hB : IsPreBrownianReal B P) :
    ∃ B' : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (B' t)) ∧ (∀ ω, Continuous (B' · ω)) ∧
      IsBrownianReal B' P ∧ ∀ t, B' t =ᵐ[P] B t := by
  have hK := hB.isAEKolmogorovProcess (n := 2) two_ne_zero
  obtain ⟨B', hB'_meas, hB'_cont, _, hB'_eq⟩ :=
    hK.exists_continuous_holderOnWith_modification_nnreal one_lt_two
  exact ⟨B', hB'_meas, hB'_cont,
    ⟨hB.congr fun t ↦ (hB'_eq t).symm, Eventually.of_forall hB'_cont⟩, hB'_eq⟩

end IsPreBrownianReal

namespace IsBrownianReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Almost every sample path of a real Brownian motion is `γ`-Hölder on any bounded set
`A ⊆ ℝ≥0` for every exponent `γ < 1 / 2`. -/
theorem ae_holderOnWith (hB : IsBrownianReal B P) {A : Set ℝ≥0} (hA : Bornology.IsBounded A)
    {γ : ℝ≥0} (hγ : γ < 1 / 2) :
    ∀ᵐ ω ∂P, ∃ K, HolderOnWith K γ (B · ω) A := by
  have hγ_real : (γ : ℝ) < 1 / 2 := by exact_mod_cast hγ
  have hpos : 0 < 1 - 2 * (γ : ℝ) := by linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / (1 - 2 * (γ : ℝ)))
  let n : ℕ := max 2 m
  have hn_zero : n ≠ 0 := by positivity
  have hn_one : (1 : ℝ) < (n : ℕ) := by
    have : (2 : ℝ) ≤ (n : ℕ) := by exact_mod_cast le_max_left 2 m
    linarith
  have hn_exp : 1 + (2 * n : ℕ) * (γ : ℝ) < (n : ℕ) := by
    have hmn : (m : ℝ) ≤ (n : ℕ) := by exact_mod_cast le_max_right 2 m
    have hstep : 1 < (n : ℝ) * (1 - 2 * (γ : ℝ)) := (div_lt_iff₀ hpos).mp (hm.trans_le hmn)
    push_cast
    linarith
  obtain ⟨B', _, hB'_cont, hB'_hold, hB'_eq⟩ :=
    (hB.isAEKolmogorovProcess hn_zero).exists_continuous_holderOnWith_modification_nnreal hn_one
  have hind : B ≡ᵐ[P] B' :=
    TauCeti.indist_of_ae_continuous hB.cont (Eventually.of_forall hB'_cont)
      fun t ↦ (hB'_eq t).symm
  filter_upwards [hind] with ω hω
  obtain ⟨K, hK⟩ := hB'_hold hA hn_exp ω
  exact ⟨K, by simpa [funext hω] using hK⟩

/-- Almost every sample path of a real Brownian motion is `γ`-Hölder on `[0, T]` for every `T` and
every `γ < 1 / 2`. -/
theorem ae_holderOnWith_Icc (hB : IsBrownianReal B P) (T : ℝ≥0) {γ : ℝ≥0} (hγ : γ < 1 / 2) :
    ∀ᵐ ω ∂P, ∃ K, HolderOnWith K γ (B · ω) (Icc 0 T) :=
  hB.ae_holderOnWith (Metric.isBounded_Icc 0 T) hγ

end IsBrownianReal

end ProbabilityTheory

namespace TauCeti

private lemma integral_exp_sum_mul_I_brownianReal {S : Set ℝ≥0}
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} {X : S → Ω → ℝ}
    (hGP : IsGaussianProcess X P)
    (hX : ∀ (I : Finset ℝ≥0) (hI : (I : Set ℝ≥0) ⊆ S),
      HasLaw (fun ω (i : I) ↦ X ⟨i.1, hI i.2⟩ ω) (BrownianReal.projectiveFamily I) P)
    (hBX : ∀ s : S, B s =ᵐ[P] X s) {ι : Type*} [Fintype ι] (θ : ι → ℝ) (u : ι → S) :
    ∫ ω, Complex.exp (((∑ i : ι, θ i * B (u i) ω : ℝ) : ℂ) * Complex.I) ∂P =
      Complex.exp (-((∑ i : ι, ∑ j : ι, θ i * (θ j * min (u i : ℝ) (u j : ℝ)) : ℝ) / 2)) := by
  have : IsProbabilityMeasure P := hGP.isProbabilityMeasure
  let U (ω : Ω) : ℝ := ∑ i : ι, θ i * B (u i) ω
  let V (ω : Ω) : ℝ := ∑ i : ι, θ i * X (u i) ω
  have hUV : U =ᵐ[P] V := by
    filter_upwards [ae_all_iff.2 fun i : ι ↦ hBX (u i)] with ω hω
    exact Finset.sum_congr rfl fun i _ ↦ by simp [hω i]
  have hVg : HasGaussianLaw V P := ((hGP.comp_right u).smul θ).hasGaussianLaw_fun_sum
  have hmean : P[V] = 0 := by
    rw [integral_finsetSum _ fun i _ ↦ ((hGP.hasGaussianLaw_eval _).integrable).const_mul _]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [integral_const_mul,
      (hasLaw_gaussianReal_of_hasLaw_brownianRealProjectiveFamily hX (u i)).integral_eq,
      integral_id_gaussianReal, mul_zero]
  have hvar : Var[V; P] = ∑ i : ι, ∑ j : ι, θ i * (θ j * min (u i : ℝ) (u j : ℝ)) := by
    rw [variance_fun_sum fun i ↦ ((hGP.hasGaussianLaw_eval _).memLp_two).const_mul _]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [covariance_const_mul_left, covariance_const_mul_right,
      covariance_eq_min_of_hasLaw_brownianRealProjectiveFamily hX]
  have hc := hVg.charFun_map_eq (1 : ℝ)
  rw [charFun_apply_real, integral_map hVg.aemeasurable (by fun_prop)] at hc
  have hc' : ∫ ω, Complex.exp ((V ω : ℝ) * Complex.I) ∂P =
      Complex.exp ((P[V] : ℝ) * Complex.I - Var[V; P] / 2) := by
    simpa [one_mul] using hc
  have hcongr : (fun ω ↦ Complex.exp ((U ω : ℝ) * Complex.I)) =ᵐ[P]
      fun ω ↦ Complex.exp ((V ω : ℝ) * Complex.I) :=
    hUV.mono fun ω hω ↦ by simp [hω]
  rw [show (fun ω ↦ Complex.exp (((∑ i : ι, θ i * B (u i) ω : ℝ) : ℂ) * Complex.I)) =
    fun ω ↦ Complex.exp ((U ω : ℝ) * Complex.I) from rfl, integral_congr_ae hcongr, hc', hmean,
    hvar]
  simp

private lemma tendsto_exp_brownianReal_covMatrix (I : Finset ℝ≥0) (θ : EuclideanSpace ℝ I)
    {s : I → ℕ → ℝ≥0} (hs_tend : ∀ i, Tendsto (s i) atTop (𝓝 i.1)) :
    Tendsto (fun n ↦ Complex.exp
        (-((∑ i : I, ∑ j : I, θ i * (θ j * min (s i n : ℝ) (s j n : ℝ)) : ℝ) / 2))) atTop
      (𝓝 (charFun (multivariateGaussian 0 (BrownianReal.covMatrix I)) θ)) := by
  rw [charFun_multivariateGaussian (BrownianReal.posSemidef_covMatrix I)]
  have hquad : (θ ⬝ᵥ BrownianReal.covMatrix I *ᵥ θ : ℝ) =
      ∑ i : I, ∑ j : I, θ i * (θ j * min (i.1 : ℝ) (j.1 : ℝ)) := by
    simp only [dotProduct, Matrix.mulVec, BrownianReal.covMatrix_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [NNReal.coe_min]
    ring
  have hexp : Complex.exp (⟪θ, (0 : EuclideanSpace ℝ I)⟫ * Complex.I -
        (θ ⬝ᵥ BrownianReal.covMatrix I *ᵥ θ : ℝ) / 2) =
      Complex.exp (-((∑ i : I, ∑ j : I, θ i * (θ j * min (i.1 : ℝ) (j.1 : ℝ)) : ℝ) / 2)) := by
    simp [hquad]
  rw [hexp]
  have hcov_tend : Tendsto (fun n ↦
      ∑ i : I, ∑ j : I, θ i * (θ j * min (s i n : ℝ) (s j n : ℝ))) atTop
      (𝓝 (∑ i : I, ∑ j : I, θ i * (θ j * min (i.1 : ℝ) (j.1 : ℝ)))) :=
    tendsto_finsetSum _ fun i _ ↦ tendsto_finsetSum _ fun j _ ↦
      (((NNReal.continuous_coe.tendsto _).comp (hs_tend i)).min
        ((NNReal.continuous_coe.tendsto _).comp (hs_tend j))).const_mul (θ j)
        |>.const_mul (θ i)
  exact (Complex.continuous_exp.tendsto _).comp
    (((Complex.continuous_ofReal.tendsto _).comp hcov_tend).div_const 2 |>.neg)

/-- If `S ⊆ ℝ≥0` is dense, `X : S → Ω → ℝ` has the Brownian finite-dimensional Gaussian laws on
`S`, and `B : ℝ≥0 → Ω → ℝ` is coordinatewise a.e.-measurable with a.e.-continuous sample paths and
agrees `P`-a.e. with `X` on `S`, then `B` is pre-Brownian. -/
theorem isPreBrownianReal_of_dense {S : Set ℝ≥0} (hS : Dense S)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB_meas : ∀ t, AEMeasurable (B t) P) (hB_cont : ∀ᵐ ω ∂P, Continuous (B · ω))
    {X : S → Ω → ℝ}
    (hX : ∀ (I : Finset ℝ≥0) (hI : (I : Set ℝ≥0) ⊆ S),
      HasLaw (fun ω (i : I) ↦ X ⟨i.1, hI i.2⟩ ω) (BrownianReal.projectiveFamily I) P)
    (hBX : ∀ s : S, B s =ᵐ[P] X s) :
    IsPreBrownianReal B P where
  hasLaw I := by
    have hGP : IsGaussianProcess X P :=
      isGaussianProcess_of_hasLaw_brownianRealProjectiveFamily hX
    have : IsProbabilityMeasure P := hGP.isProbabilityMeasure
    have h_pi : AEMeasurable (fun ω ↦ I.restrict (B · ω)) P :=
      aemeasurable_pi_iff.2 fun i ↦ hB_meas i.1
    refine ⟨h_pi, ?_⟩
    apply (MeasurableEquiv.toLp 2 (I → ℝ)).map_measurableEquiv_injective
    let Z : Ω → EuclideanSpace ℝ I := fun ω ↦ WithLp.toLp 2 (I.restrict (B · ω))
    have hZ : AEMeasurable Z P := (MeasurableEquiv.toLp 2 (I → ℝ)).measurable.comp_aemeasurable h_pi
    rw [MeasurableEquiv.coe_toLp, (BrownianReal.measurePreserving_toLp_projectiveFamily I).map_eq,
      AEMeasurable.map_map_of_aemeasurable (by fun_prop) h_pi]
    have : IsProbabilityMeasure (P.map Z) :=
      (Measure.isProbabilityMeasure_map_iff hZ).2 inferInstance
    apply Measure.ext_of_charFun
    ext θ
    choose s hs_mem hs_tend using fun i : I ↦ mem_closure_iff_seq_limit.mp (hS i.1)
    let u (n : ℕ) (i : I) : S := ⟨s i n, hs_mem i n⟩
    let U (n : ℕ) (ω : Ω) : ℝ := ∑ i : I, θ i * B (u n i) ω
    have hlhs : Tendsto (fun n ↦ ∫ ω, Complex.exp ((U n ω : ℝ) * Complex.I) ∂P) atTop
        (𝓝 (charFun (P.map Z) θ)) := by
      rw [charFun_apply, integral_map hZ (by fun_prop)]
      refine tendsto_integral_of_dominated_convergence (fun _ ↦ (1 : ℝ))
        (fun n ↦ ?_) (integrable_const 1)
        (fun n ↦ Eventually.of_forall fun ω ↦ (Complex.norm_exp_ofReal_mul_I _).le) ?_
      · have hUn : AEMeasurable (U n) P :=
          Finset.aemeasurable_fun_sum _ fun i _ ↦ (hB_meas _).const_mul _
        exact (Complex.continuous_exp.comp
          (Complex.continuous_ofReal.mul continuous_const)).comp_aestronglyMeasurable
          hUn.aestronglyMeasurable
      · filter_upwards [hB_cont] with ω hω
        have hsum : Tendsto (fun n ↦ U n ω) atTop (𝓝 ⟪Z ω, θ⟫) := by
          have heq : ⟪Z ω, θ⟫ = ∑ i : I, θ i * B i.1 ω := by
            simp [Z, PiLp.inner_apply, Finset.restrict_def]
          rw [heq]
          exact tendsto_finsetSum _ fun i _ ↦
            ((hω.tendsto i.1).comp (hs_tend i)).const_mul (θ i)
        exact (Complex.continuous_exp.tendsto _).comp
          (((Complex.continuous_ofReal.tendsto _).comp hsum).mul_const Complex.I)
    exact tendsto_nhds_unique hlhs ((tendsto_exp_brownianReal_covMatrix I θ hs_tend).congr fun n ↦
      (integral_exp_sum_mul_I_brownianReal hGP hX hBX (fun i ↦ θ i) (u n)).symm)

/-- If `S ⊆ ℝ≥0` is dense, `X : S → Ω → ℝ` has the Brownian finite-dimensional Gaussian laws on
`S`, and `B : ℝ≥0 → Ω → ℝ` is coordinatewise a.e.-measurable with a.e.-continuous sample paths and
agrees `P`-a.e. with `X` on `S`, then `B` is a real Brownian motion. -/
theorem isBrownianReal_of_dense {S : Set ℝ≥0} (hS : Dense S)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB_meas : ∀ t, AEMeasurable (B t) P) (hB_cont : ∀ᵐ ω ∂P, Continuous (B · ω))
    {X : S → Ω → ℝ}
    (hX : ∀ (I : Finset ℝ≥0) (hI : (I : Set ℝ≥0) ⊆ S),
      HasLaw (fun ω (i : I) ↦ X ⟨i.1, hI i.2⟩ ω) (BrownianReal.projectiveFamily I) P)
    (hBX : ∀ s : S, B s =ᵐ[P] X s) :
    IsBrownianReal B P :=
  ⟨isPreBrownianReal_of_dense hS hB_meas hB_cont hX hBX, hB_cont⟩

/-- **Existence of Wiener measure on `C(ℝ≥0, ℝ)`.**
There exists a probability measure `W` on the space `C(ℝ≥0, ℝ)` of continuous paths such that the
coordinate evaluation process `(t, ω) ↦ ω t` is a standard real Brownian motion. -/
theorem exists_wienerMeasure :
    ∃ W : Measure C(ℝ≥0, ℝ), IsProbabilityMeasure W ∧
      IsBrownianReal (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t) W := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have : Countable S := hSc.to_subtype
  obtain ⟨P, hP_prob, hP_proj, hP_kolm⟩ :=
    exists_measurePreserving_brownianRealProjectiveFamily_isKolmogorovProcess_of_countable S
  have hK := (hP_kolm (n := 2) two_ne_zero).IsAEKolmogorovProcess
  obtain ⟨B, hB_meas, hB_cont, _, hB_eq⟩ :=
    hK.exists_continuous_holderOnWith_of_dense_nnreal hSd one_lt_two
  have hB : IsBrownianReal B P :=
    isBrownianReal_of_dense hSd (fun t ↦ (hB_meas t).aemeasurable)
      (Eventually.of_forall hB_cont) (fun I hI ↦ (hP_proj I hI).hasLaw) hB_eq
  let Φ : (S → ℝ) → C(ℝ≥0, ℝ) := fun ω ↦ ⟨fun t ↦ B t ω, hB_cont ω⟩
  have hΦ : Measurable Φ := ContinuousMap.measurable_iff_eval.2 hB_meas
  refine ⟨P.map Φ, (Measure.isProbabilityMeasure_map_iff hΦ.aemeasurable).2 inferInstance,
    ⟨⟨fun I ↦ ?_⟩, ?_⟩⟩
  · have hm : Measurable (fun (ω : C(ℝ≥0, ℝ)) ↦ I.restrict ω) :=
      measurable_pi_iff.2 fun i ↦ ContinuousMap.measurable_eval i.1
    refine ⟨hm.aemeasurable, ?_⟩
    rw [Measure.map_map hm hΦ]
    exact (hB.hasLaw I).map_eq
  · exact Eventually.of_forall fun ω ↦ ω.continuous

/-- **Uniqueness of Wiener measure on `C(ℝ≥0, ℝ)`.**
Any two Borel measures on `C(ℝ≥0, ℝ)` under which the coordinate evaluation process is pre-Brownian
are equal. -/
theorem eq_of_isPreBrownianReal_eval {W₁ W₂ : Measure C(ℝ≥0, ℝ)}
    (h₁ : IsPreBrownianReal (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t) W₁)
    (h₂ : IsPreBrownianReal (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t) W₂) :
    W₁ = W₂ := by
  have : IsProbabilityMeasure W₁ := h₁.isGaussianProcess.isProbabilityMeasure
  exact measure_eq_of_finset_eval_map_eq fun I ↦
    (h₁.hasLaw I).map_eq.trans (h₂.hasLaw I).map_eq.symm

end TauCeti
