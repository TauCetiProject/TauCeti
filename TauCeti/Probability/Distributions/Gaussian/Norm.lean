/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Group.SeparationQuotient
import Mathlib.Analysis.Normed.Module.Seminorm.Norm
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gaussian.Fernique
import TauCeti.Probability.Distributions.Gaussian.Maximum
import TauCeti.Probability.Distributions.Rademacher.Norm
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Expected norms and seminorms of Gaussian vector sums

Let `g i` be independent centered real Gaussian random variables and `v i` fixed vectors in a real
vector space `E` carrying a seminorm `p`. Because each `g i` is symmetric, the tuple `(η i * g i)`
has the same joint law as `(g i)` for every deterministic sign vector `η` with `|η i| = 1`.
Introducing an independent Rademacher tuple, swapping the expectations by Fubini's theorem, and
applying the Rademacher convexity inequality pointwise gives the unconditional lower bound

`∫ ω, sup_i |g i ω| * p (v i) ∂P ≤ ∫ ω, p (∑ i, g i ω • v i) ∂P`.

When the `g i` are standard Gaussian and every `p (v i) ≥ c ≥ 0`, combining this inequality with
the expected-maximum estimate `√(log m) / 32 ≤ 𝔼 max_i |g i|` from
`TauCeti.Probability.Distributions.Gaussian.Maximum` yields

`c * √(log m) / 32 ≤ ∫ ω, p (∑ i, g i ω • v i) ∂P`,

and hence `c * √(log (finrank ℝ E)) / 32 ≤ ∫ x, p x ∂stdGaussian E` whenever `E` admits an
orthonormal basis on which `p` is bounded below by `c`. Specializing `p` to `normSeminorm` or to
`(normSeminorm ℝ F).comp T` gives the corresponding norm estimates without requiring completeness or
finite-dimensionality of the target space.

## Main results

* `ProbabilityTheory.iIndepFun.hasLaw_pi_mul_gaussianReal_of_abs_eq_one`: multiplying independent
  centered Gaussian variables by deterministic signs preserves their joint product law.
* `TauCeti.Probability.integral_sup'_mul_seminorm_le_integral_seminorm_sum_smul_gaussianReal`:
  expected seminorm of a centered Gaussian sum bounds the expected maximum summand seminorm.
* `TauCeti.Probability.mul_sqrt_log_card_div_le_integral_seminorm_sum_smul_gaussianReal`:
  logarithmic lower bound `c * √(log m) / 32` for standard Gaussian sums.
* `TauCeti.Probability.mul_sqrt_log_finrank_div_le_integral_seminorm_stdGaussian`: logarithmic
  lower bound for the standard Gaussian expectation of a seminorm on a finite-dimensional inner
  product space.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §13.3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal

namespace ProbabilityTheory

/-- Multiplying a centered real Gaussian random variable by a scalar of unit modulus preserves its
law. -/
theorem HasLaw.gaussianReal_const_mul_of_abs_eq_one {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) P)
    {c : ℝ} (hc : |c| = 1) :
    HasLaw (fun ω ↦ c * X ω) (gaussianReal 0 v) P := by
  have hc2 : NNReal.mk (c ^ 2) (sq_nonneg c) = 1 :=
    NNReal.eq (by simp [← sq_abs, hc])
  simpa [hc2] using gaussianReal_const_mul hX c

/-- Multiplying independent centered real Gaussian random variables by deterministic signs `η i`
with `|η i| = 1` preserves their joint product law. -/
theorem iIndepFun.hasLaw_pi_mul_gaussianReal_of_abs_eq_one {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] {P : Measure Ω} {g : ι → Ω → ℝ} {σ : ι → ℝ≥0}
    (hindep : iIndepFun g P) (hlaw : ∀ i, HasLaw (g i) (gaussianReal 0 (σ i)) P)
    {η : ι → ℝ} (hη : ∀ i, |η i| = 1) :
    HasLaw (fun ω i ↦ η i * g i ω) (Measure.pi fun i ↦ gaussianReal 0 (σ i)) P :=
  (hindep.comp (fun i x ↦ η i * x) fun _ ↦ by fun_prop).hasLaw_pi fun i ↦
    (hlaw i).gaussianReal_const_mul_of_abs_eq_one (hη i)

end ProbabilityTheory

namespace TauCeti.Probability

section Integrability

variable {Ω ι E : Type*} [MeasurableSpace Ω] {P : Measure Ω} {g : ι → Ω → ℝ}
  {μ : ι → ℝ} {σ : ι → ℝ≥0}

/-- A finite Gaussian linear combination of fixed vectors in a normed space is integrable, even
without completeness or independence. -/
theorem integrable_sum_smul_gaussianReal [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ι) (v : ι → E)
    (hlaw : ∀ i ∈ s, HasLaw (g i) (gaussianReal (μ i) (σ i)) P) :
    Integrable (fun ω ↦ ∑ i ∈ s, g i ω • v i) P :=
  integrable_finsetSum s fun i hi ↦
    ((hlaw i hi).integrable IsGaussian.integrable_id).smul_const (v i)

/-- A real seminorm evaluated on a finite Gaussian linear combination of fixed vectors is
integrable. -/
theorem integrable_seminorm_sum_smul_gaussianReal [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) (s : Finset ι) (v : ι → E)
    (hlaw : ∀ i ∈ s, HasLaw (g i) (gaussianReal (μ i) (σ i)) P) :
    Integrable (fun ω ↦ p (∑ i ∈ s, g i ω • v i)) P := by
  let : SeminormedAddCommGroup E := p.toSeminormedAddCommGroup
  let : NormedSpace ℝ E := { norm_smul_le := fun a x ↦ (map_smul_eq_mul p a x).le }
  let q := SeparationQuotient.mkCLM ℝ E
  have hq (ω : Ω) : ‖∑ i ∈ s, g i ω • q (v i)‖ = p (∑ i ∈ s, g i ω • v i) := by
    simp_rw [← map_smul, ← map_sum]
    exact SeparationQuotient.norm_mk _
  simpa only [hq] using (integrable_sum_smul_gaussianReal s (fun i ↦ q (v i)) hlaw).norm

/-- The norm of a finite Gaussian linear combination of fixed vectors in a seminormed space is
integrable. -/
theorem integrable_norm_sum_smul_gaussianReal [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ι) (v : ι → E)
    (hlaw : ∀ i ∈ s, HasLaw (g i) (gaussianReal (μ i) (σ i)) P) :
    Integrable (fun ω ↦ ‖∑ i ∈ s, g i ω • v i‖) P :=
  integrable_seminorm_sum_smul_gaussianReal (normSeminorm ℝ E) s v hlaw

/-- The pointwise maximum of weighted absolute values of a nonempty finite Gaussian family is
integrable, even without independence. -/
theorem integrable_sup'_abs_mul_gaussianReal {s : Finset ι} (hs : s.Nonempty) (c : ι → ℝ)
    (hlaw : ∀ i ∈ s, HasLaw (g i) (gaussianReal (μ i) (σ i)) P) :
    Integrable (fun ω ↦ s.sup' hs fun i ↦ |g i ω| * c i) P := by
  rw [show (fun ω ↦ s.sup' hs fun i ↦ |g i ω| * c i) = s.sup' hs fun i ω ↦ |g i ω| * c i from
    funext fun ω ↦ (Finset.sup'_apply hs (fun i ω ↦ |g i ω| * c i) ω).symm]
  exact Finset.sup'_induction (p := fun f ↦ Integrable f P) hs (fun i ω ↦ |g i ω| * c i)
    (fun _ hf _ hg ↦ Integrable.sup hf hg) fun i hi ↦
      ((hlaw i hi).integrable IsGaussian.integrable_id).abs.mul_const (c i)

/-- The pointwise maximum of the absolute values of a nonempty finite Gaussian family is
integrable, even without independence. -/
theorem integrable_sup'_abs_gaussianReal {s : Finset ι} (hs : s.Nonempty)
    (hlaw : ∀ i ∈ s, HasLaw (g i) (gaussianReal (μ i) (σ i)) P) :
    Integrable (fun ω ↦ s.sup' hs fun i ↦ |g i ω|) P := by
  simpa using integrable_sup'_abs_mul_gaussianReal hs (fun _ ↦ 1) hlaw

end Integrability

section Comparison

variable {Ω ι E : Type*} [MeasurableSpace Ω] {P : Measure Ω} {g : ι → Ω → ℝ} {σ : ι → ℝ≥0}

/-- Coordinate-space Rademacher comparison for a product of centered Gaussian laws. -/
private theorem integral_sup'_mul_seminorm_le_integral_pi_gaussianReal [Fintype ι] [Nonempty ι]
    [AddCommGroup E] [Module ℝ E] (p : Seminorm ℝ E) (v : ι → E) (σ : ι → ℝ≥0) :
    ∫ x, Finset.univ.sup' Finset.univ_nonempty (fun i ↦ |x i| * p (v i))
        ∂Measure.pi (fun i ↦ gaussianReal 0 (σ i)) ≤
      ∫ x, p (∑ i, x i • v i) ∂Measure.pi (fun i ↦ gaussianReal 0 (σ i)) := by
  let L : (ι → ℝ) →ₗ[ℝ] E := ∑ i, (LinearMap.proj i).smulRight (v i)
  let q : Seminorm ℝ (ι → ℝ) := p.comp L
  have hq_apply (x : ι → ℝ) : q x = p (∑ i, x i • v i) := by simp [q, L, LinearMap.sum_apply]
  have hq_cont : Continuous q := q.continuous_of_finiteDimensional
  have hq_le (x : ι → ℝ) : q x ≤ ∑ i, |x i| * p (v i) :=
    calc q x = p (∑ i, x i • v i) := hq_apply x
      _ ≤ ∑ i, p (x i • v i) :=
        Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _
      _ = ∑ i, |x i| * p (v i) := by simp [map_smul_eq_mul]
  set μG : Measure (ι → ℝ) := Measure.pi fun i ↦ gaussianReal 0 (σ i)
  set μR : Measure (ι → ℝ) := Measure.pi fun _ : ι ↦ rademacherMeasure
  have hlawG (i : ι) : HasLaw (fun x : ι → ℝ ↦ x i) (gaussianReal 0 (σ i)) μG :=
    (measurePreserving_eval (fun j ↦ gaussianReal 0 (σ j)) i).hasLaw
  have hlawR (i : ι) : HasLaw (fun η : ι → ℝ ↦ η i) rademacherMeasure μR :=
    (measurePreserving_eval (fun _ : ι ↦ rademacherMeasure) i).hasLaw
  have hF_int : Integrable (fun z : (ι → ℝ) × (ι → ℝ) ↦ q (fun i ↦ z.1 i * z.2 i))
      (μR.prod μG) := by
    refine (integrable_finsetSum Finset.univ fun i _ ↦
      ((hlawR i).integrable_comp (integrable_rademacherMeasure abs)).mul_prod
        (((hlawG i).integrable IsGaussian.integrable_id).abs.mul_const (p (v i)))).mono'
      (hq_cont.comp (by fun_prop)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (apply_nonneg q _)]
    exact (hq_le _).trans_eq (by simp [abs_mul, mul_assoc])
  have hη_abs : ∀ᵐ η ∂μR, ∀ i, |η i| = 1 :=
    Filter.eventually_all.2 fun i ↦
      ((hlawR i).ae_iff (by fun_prop : Measurable fun t : ℝ ↦ |t| = 1)).2
        (by simp [rademacherMeasure_eq])
  have hlhs : ∫ η, (∫ x, q (fun i ↦ η i * x i) ∂μG) ∂μR = ∫ x, q x ∂μG := by
    have hcongr : (fun η : ι → ℝ ↦ ∫ x, q (fun i ↦ η i * x i) ∂μG) =ᵐ[μR]
        fun _ ↦ ∫ x, q x ∂μG := by
      filter_upwards [hη_abs] with η hη
      exact ((iIndepFun_pi (X := fun _ ↦ (id : ℝ → ℝ)) fun _ ↦ aemeasurable_id)
        |>.hasLaw_pi_mul_gaussianReal_of_abs_eq_one hlawG hη).integral_comp
        hq_cont.aestronglyMeasurable
    rw [integral_congr_ae hcongr, integral_const, probReal_univ, one_smul]
  have hM_int : Integrable
      (fun x : ι → ℝ ↦ Finset.univ.sup' Finset.univ_nonempty fun i ↦ |x i| * p (v i)) μG :=
    integrable_sup'_abs_mul_gaussianReal Finset.univ_nonempty (fun i ↦ p (v i)) fun i _ ↦ hlawG i
  have hpt (x : ι → ℝ) :
      Finset.univ.sup' Finset.univ_nonempty (fun i ↦ |x i| * p (v i)) ≤
        ∫ η, q (fun i ↦ η i * x i) ∂μR := by
    have hε_indep : iIndepFun (fun (i : ι) (η : ι → ℝ) ↦ η i) μR :=
      iIndepFun_pi (X := fun _ ↦ (id : ℝ → ℝ)) fun _ ↦ aemeasurable_id
    have hrad := Finset.sup'_seminorm_le_integral_seminorm_sum_smul_rademacher p Finset.univ
      Finset.univ_nonempty (fun i ↦ x i • v i) (fun i _ ↦ hlawR i)
      (fun i _ j _ hij ↦ hε_indep.indepFun hij)
    simpa [hq_apply, map_smul_eq_mul, mul_smul] using hrad
  simp_rw [← hq_apply]
  rw [← hlhs, integral_integral_swap hF_int]
  exact integral_mono hM_int hF_int.integral_prod_right hpt

/-- **Unconditional comparison for centered Gaussian sums (seminorm form).** For independent
centered real Gaussian variables `g i` and any real seminorm `p`, the expected seminorm of
`∑ i ∈ s, g i ω • v i` bounds the expected largest summand seminorm `sup_{i ∈ s} |g i ω| * p (v i)`.
-/
theorem integral_sup'_mul_seminorm_le_integral_seminorm_sum_smul_gaussianReal
    [AddCommGroup E] [Module ℝ E] (p : Seminorm ℝ E) {s : Finset ι} (hs : s.Nonempty) (v : ι → E)
    (hindep : iIndepFun g P) (hlaw : ∀ i ∈ s, HasLaw (g i) (gaussianReal 0 (σ i)) P) :
    ∫ ω, s.sup' hs (fun i ↦ |g i ω| * p (v i)) ∂P ≤
      ∫ ω, p (∑ i ∈ s, g i ω • v i) ∂P := by
  let _ : Nonempty s := hs.coe_sort
  let μG : Measure (s → ℝ) := Measure.pi fun i : s ↦ gaussianReal 0 (σ i)
  have hG : HasLaw (fun ω (i : s) ↦ g i ω) μG P :=
    (hindep.restrict s).hasLaw_pi fun i ↦ hlaw i i.2
  let q : Seminorm ℝ (s → ℝ) := p.comp (∑ i : s, (LinearMap.proj i).smulRight (v i))
  have hsup (ω : Ω) : s.sup' hs (fun i ↦ |g i ω| * p (v i)) =
      Finset.univ.sup' Finset.univ_nonempty (fun i : s ↦ |g i ω| * p (v i)) :=
    le_antisymm
      (Finset.sup'_le hs _ fun i hi ↦
        Finset.le_sup' (fun j : s ↦ |g j ω| * p (v j)) (Finset.mem_univ ⟨i, hi⟩))
      (Finset.sup'_le Finset.univ_nonempty _ fun i _ ↦
        Finset.le_sup' (fun j ↦ |g j ω| * p (v j)) i.2)
  have hsum (ω : Ω) : p (∑ i ∈ s, g i ω • v i) = q (fun i : s ↦ g i ω) := by
    simp [q, LinearMap.sum_apply, ← Finset.sum_coe_sort s]
  have hM_cont : Continuous
      (fun x : s → ℝ ↦ Finset.univ.sup' Finset.univ_nonempty fun i : s ↦ |x i| * p (v i)) :=
    Continuous.finset_sup'_apply Finset.univ_nonempty
      (f := fun (i : s) (x : s → ℝ) ↦ |x i| * p (v i)) fun i _ ↦ by fun_prop
  have hM_eq : (∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i : s ↦ |g i ω| * p (v i)) ∂P) =
      ∫ x, Finset.univ.sup' Finset.univ_nonempty (fun i : s ↦ |x i| * p (v i)) ∂μG :=
    hG.integral_comp hM_cont.aestronglyMeasurable
  have hq_eq : (∫ ω, q (fun i : s ↦ g i ω) ∂P) = ∫ x, q x ∂μG :=
    hG.integral_comp q.continuous_of_finiteDimensional.aestronglyMeasurable
  simp_rw [hsup, hsum, hM_eq, hq_eq]
  simpa [q, LinearMap.sum_apply] using
    integral_sup'_mul_seminorm_le_integral_pi_gaussianReal p (fun i : s ↦ v i) (fun i : s ↦ σ i)

/-- **Unconditional comparison for centered Gaussian sums (norm form).** For independent centered
real Gaussian variables `g i`, the expected norm of `∑ i ∈ s, g i ω • v i` bounds the expected
maximum summand norm `sup_{i ∈ s} |g i ω| * ‖v i‖`. -/
theorem integral_sup'_mul_norm_le_integral_norm_sum_smul_gaussianReal
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] {s : Finset ι} (hs : s.Nonempty) (v : ι → E)
    (hindep : iIndepFun g P) (hlaw : ∀ i ∈ s, HasLaw (g i) (gaussianReal 0 (σ i)) P) :
    ∫ ω, s.sup' hs (fun i ↦ |g i ω| * ‖v i‖) ∂P ≤
      ∫ ω, ‖∑ i ∈ s, g i ω • v i‖ ∂P := by
  simpa using integral_sup'_mul_seminorm_le_integral_seminorm_sum_smul_gaussianReal
    (normSeminorm ℝ E) hs v hindep hlaw

end Comparison

section StandardGaussian

variable {Ω ι E : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι] {P : Measure Ω}
  {g : ι → Ω → ℝ}

/-- **Logarithmic lower bound for standard Gaussian vector sums (seminorm form).** If `g i` are
`m` independent standard Gaussian variables and `p (v i) ≥ c ≥ 0` for every `i`, then
`c * √(log m) / 32 ≤ ∫ ω, p (∑ i, g i ω • v i) ∂P`. -/
theorem mul_sqrt_log_card_div_le_integral_seminorm_sum_smul_gaussianReal
    [AddCommGroup E] [Module ℝ E] (p : Seminorm ℝ E) (v : ι → E)
    (hindep : iIndepFun g P) (hlaw : ∀ i, HasLaw (g i) (gaussianReal 0 1) P)
    {c : ℝ} (hc : 0 ≤ c) (hv : ∀ i, c ≤ p (v i)) :
    c * √(Real.log (Fintype.card ι)) / 32 ≤ ∫ ω, p (∑ i, g i ω • v i) ∂P := by
  have hM_int : Integrable
      (fun ω ↦ Finset.univ.sup' Finset.univ_nonempty fun i ↦ |g i ω|) P :=
    integrable_sup'_abs_gaussianReal Finset.univ_nonempty fun i _ ↦ hlaw i
  have hMv_int : Integrable
      (fun ω ↦ Finset.univ.sup' Finset.univ_nonempty fun i ↦ |g i ω| * p (v i)) P :=
    integrable_sup'_abs_mul_gaussianReal Finset.univ_nonempty (fun i ↦ p (v i)) fun i _ ↦ hlaw i
  calc c * √(Real.log (Fintype.card ι)) / 32
      = c * (√(Real.log (Fintype.card ι)) / 32) := mul_div_assoc _ _ _
    _ ≤ c * ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i ↦ |g i ω|) ∂P :=
        mul_le_mul_of_nonneg_left (sqrt_log_card_div_le_integral_sup'_abs hindep hlaw) hc
    _ = ∫ ω, c * Finset.univ.sup' Finset.univ_nonempty (fun i ↦ |g i ω|) ∂P :=
        (integral_const_mul c _).symm
    _ ≤ ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i ↦ |g i ω| * p (v i)) ∂P := by
        refine integral_mono (hM_int.const_mul c) hMv_int fun ω ↦ ?_
        rw [Finset.apply_sup'_eq_sup'_comp Finset.univ_nonempty (g := (c * ·))
          (fun a b ↦ mul_max_of_nonneg a b hc)]
        exact Finset.sup'_le _ _ fun i _ ↦
          calc c * |g i ω| = |g i ω| * c := mul_comm _ _
            _ ≤ |g i ω| * p (v i) := mul_le_mul_of_nonneg_left (hv i) (abs_nonneg _)
            _ ≤ Finset.univ.sup' Finset.univ_nonempty fun j ↦ |g j ω| * p (v j) :=
                Finset.le_sup' (fun j ↦ |g j ω| * p (v j)) (Finset.mem_univ i)
    _ ≤ ∫ ω, p (∑ i, g i ω • v i) ∂P :=
        integral_sup'_mul_seminorm_le_integral_seminorm_sum_smul_gaussianReal p
          Finset.univ_nonempty v hindep fun i _ ↦ hlaw i

/-- **Logarithmic lower bound for standard Gaussian vector sums (norm form).** If `g i` are `m`
independent standard Gaussian variables and `‖v i‖ ≥ c ≥ 0` for every `i`, then
`c * √(log m) / 32 ≤ ∫ ω, ‖∑ i, g i ω • v i‖ ∂P`. -/
theorem mul_sqrt_log_card_div_le_integral_norm_sum_smul_gaussianReal
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] (v : ι → E)
    (hindep : iIndepFun g P) (hlaw : ∀ i, HasLaw (g i) (gaussianReal 0 1) P)
    {c : ℝ} (hc : 0 ≤ c) (hv : ∀ i, c ≤ ‖v i‖) :
    c * √(Real.log (Fintype.card ι)) / 32 ≤ ∫ ω, ‖∑ i, g i ω • v i‖ ∂P :=
  mul_sqrt_log_card_div_le_integral_seminorm_sum_smul_gaussianReal
    (normSeminorm ℝ E) v hindep hlaw hc hv

end StandardGaussian

section StdGaussian

variable {ι E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Every real seminorm on a finite-dimensional real inner product space is integrable under the
standard Gaussian law. -/
theorem integrable_seminorm_stdGaussian (p : Seminorm ℝ E) :
    Integrable p (stdGaussian E) := by
  obtain ⟨C, _, hC⟩ := p.bound_of_continuous_normedSpace p.continuous_of_finiteDimensional
  refine (IsGaussian.integrable_id.norm.const_mul C).mono'
    p.continuous_of_finiteDimensional.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (apply_nonneg p x)]
  exact hC x

/-- If an orthonormal basis `b` of `E` satisfies `c ≤ p (b i)` for every `i`, then the expected
value of `p` under `stdGaussian E` is at least `c * √(log (finrank ℝ E)) / 32`. -/
theorem mul_sqrt_log_finrank_div_le_integral_seminorm_stdGaussian [Fintype ι] [Nonempty ι]
    (p : Seminorm ℝ E) (b : OrthonormalBasis ι ℝ E) {c : ℝ} (hc : 0 ≤ c)
    (hb : ∀ i, c ≤ p (b i)) :
    c * √(Real.log (Module.finrank ℝ E)) / 32 ≤ ∫ x, p x ∂stdGaussian E := by
  rw [Module.finrank_eq_card_basis b.toBasis, stdGaussian_eq_map_pi_orthonormalBasis b,
    integral_map (Continuous.aemeasurable (by fun_prop))
      p.continuous_of_finiteDimensional.aestronglyMeasurable]
  exact mul_sqrt_log_card_div_le_integral_seminorm_sum_smul_gaussianReal p b
    (iIndepFun_pi (X := fun _ ↦ (id : ℝ → ℝ)) fun _ ↦ aemeasurable_id)
    (fun i ↦ (measurePreserving_eval (fun _ : ι ↦ gaussianReal 0 1) i).hasLaw) hc hb

/-- If an orthonormal basis `b` of `E` satisfies `c ≤ ‖T (b i)‖` for every `i`, then the expected
norm of `T x` under `stdGaussian E` is at least `c * √(log (finrank ℝ E)) / 32`. -/
theorem mul_sqrt_log_finrank_div_le_integral_norm_comp_stdGaussian [Fintype ι] [Nonempty ι]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F] (T : E →ₗ[ℝ] F) (b : OrthonormalBasis ι ℝ E)
    {c : ℝ} (hc : 0 ≤ c) (hb : ∀ i, c ≤ ‖T (b i)‖) :
    c * √(Real.log (Module.finrank ℝ E)) / 32 ≤ ∫ x, ‖T x‖ ∂stdGaussian E :=
  mul_sqrt_log_finrank_div_le_integral_seminorm_stdGaussian ((normSeminorm ℝ F).comp T) b hc hb

end StdGaussian

end TauCeti.Probability
