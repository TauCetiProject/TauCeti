/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Topology.ContinuousMap.Algebra
public import TauCeti.MeasureTheory.Measure.ContinuousMap
public import TauCeti.Probability.Process.KolmogorovChentsov
import Mathlib.Data.NNRat.Encodable
import Mathlib.Data.NNRat.Floor
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import TauCeti.MeasureTheory.Measure.ProjectiveLimit.Countable
import TauCeti.Probability.Distributions.Gaussian.Continuity
import TauCeti.Probability.Distributions.Gaussian.Moments
import TauCeti.Probability.Distributions.Gaussian.PolynomialMemLp
import TauCeti.Topology.MetricSpace.Holder

/-!
# Wiener measure on continuous path space

We construct **Wiener measure** (`TauCeti.wienerMeasure`) on the space `C(ℝ≥0, ℝ)` of continuous
real-valued paths and prove that it is the unique Borel probability measure under which the
coordinate evaluation process `t ↦ (ω ↦ ω t)` is a standard real Brownian motion
(`ProbabilityTheory.IsBrownianReal`).

The construction proceeds in three stages:

1. **Pre-Brownian moment bounds and regularization.** Every pre-Brownian motion satisfies the
   Kolmogorov moment condition of exponents `(2 m, m)` with constant `(2 m - 1)‼` for every
   `m ≥ 1` (`ProbabilityTheory.IsPreBrownianReal.isAEKolmogorovProcess_two_mul`). Applying the
   one-dimensional Kolmogorov–Chentsov theorem yields an all-paths continuous, coordinatewise
   measurable modification (`ProbabilityTheory.IsPreBrownianReal.exists_continuous_modification`)
   and local `< 1 / 2`-Hölder regularity for any `IsBrownianReal` process
   (`ProbabilityTheory.IsBrownianReal.ae_holderOnWith`).
2. **Projective limit on rational times and dyadic extension.** Pulling back
   `ProbabilityTheory.BrownianReal.projectiveFamily` to `ℚ≥0` and applying Kolmogorov's countable
   extension theorem (`TauCeti.Measure.exists_isProjectiveLimit_of_countable`) produces a
   probability law on `ℚ≥0 → ℝ`. Its fourth increment moments equal `3 * |r - s| ^ 2`, so
   `TauCeti.exists_continuous_extension_of_nnrat` extends the rational coordinate process to an
   all-paths continuous, coordinatewise measurable process on `ℝ≥0`. Passing to the dyadic limit via
   weak continuity of multivariate Gaussian laws (`Continuous.multivariateGaussian`) shows that the
   extended process satisfies `IsPreBrownianReal`.
3. **Pushforward to `C(ℝ≥0, ℝ)`, uniqueness, scaling invariance, and marginal checks.** Pushing
   forward along the measurable path map into `C(ℝ≥0, ℝ)` defines `TauCeti.wienerMeasure`,
   establishes `TauCeti.exists_wienerMeasure`, characterizes `wienerMeasure` uniquely via
   evaluation-generated Borel uniqueness (`TauCeti.eq_wienerMeasure_iff_isBrownianReal`), proves
   invariance under negation and diffusive Brownian rescaling `ω ↦ (t ↦ (√c)⁻¹ * ω (c * t))`, and
   records marginal/increment variances distinguishing Wiener measure from degenerate and
   unnormalized laws.

## Main definitions and results

* `ProbabilityTheory.IsPreBrownianReal.isAEKolmogorovProcess_two_mul`: `(2 m, m)` Kolmogorov moment
  condition for pre-Brownian motion (`m ≥ 1`).
* `ProbabilityTheory.IsPreBrownianReal.exists_continuous_modification`: every pre-Brownian motion
  admits an all-paths continuous, coordinatewise measurable Brownian modification.
* `ProbabilityTheory.IsBrownianReal.ae_holderOnWith`: almost every path of a Brownian motion is
  `γ`-Hölder continuous on `[0, T]` for every `γ < 1 / 2`.
* `TauCeti.wienerMeasure`: Wiener measure on `C(ℝ≥0, ℝ)`.
* `TauCeti.exists_wienerMeasure`: existence of a Borel probability measure on `C(ℝ≥0, ℝ)` whose
  coordinate process satisfies `IsBrownianReal`.
* `TauCeti.eq_wienerMeasure_iff_isBrownianReal` and
  `TauCeti.eq_wienerMeasure_iff_isPreBrownianReal`: uniqueness of Wiener measure on `C(ℝ≥0, ℝ)`.
* `TauCeti.map_scale_wienerMeasure`, `TauCeti.map_shift_wienerMeasure`,
  `TauCeti.map_neg_wienerMeasure`, and `TauCeti.map_smul_eq_wienerMeasure_iff`: diffusive scaling,
  increment-shift, reflection, and scalar-rescaling characterizations of Wiener measure.

## References

* S. P. Lalley, *Brownian Motion*, University of Chicago lecture notes, Theorem 1.
* O. Kallenberg, *Foundations of Modern Probability*, 3rd ed., Springer, 2021, Theorem 14.2.
* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer, 1991,
  §2.2.
-/

public section

noncomputable section

open Filter MeasureTheory Metric ProbabilityTheory ProbabilityTheory.BrownianReal Set WithLp
open scoped ENNReal Nat NNReal Topology

namespace ProbabilityTheory

section Regularity

variable {Ω : Type*} {_ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Every even moment `(B s - B t) ^ (2 m)` of a pre-Brownian increment equals
`(2 m - 1)‼ * dist s t ^ m`, regardless of the order of `s` and `t`. -/
theorem IsPreBrownianReal.integral_pow_two_mul_sub (hB : IsPreBrownianReal B P)
    (s t : ℝ≥0) (m : ℕ) :
    ∫ ω, (B s ω - B t ω) ^ (2 * m) ∂P = (2 * m - 1 : ℕ)‼ * dist s t ^ m := by
  have h := (hB.hasLaw_sub s t).integral_comp (f := fun x : ℝ ↦ x ^ (2 * m)) (by fun_prop)
  have hm := TauCeti.Probability.integral_sub_pow_two_mul_gaussianReal 0 (nndist s.1 t.1) m
  simp only [Function.comp_apply, Pi.sub_apply] at h
  simp only [sub_zero, coe_nndist] at hm
  have hdist : dist s.1 t.1 = dist s t := rfl
  rw [h, hm, hdist, mul_comm]

/-- For every `m ≥ 1`, a pre-Brownian motion satisfies `IsAEKolmogorovProcess` with exponents
`p = 2 m`, `q = m`, and constant `(2 m - 1)‼`. -/
theorem IsPreBrownianReal.isAEKolmogorovProcess_two_mul (hB : IsPreBrownianReal B P)
    {m : ℕ} (hm : 1 ≤ m) :
    IsAEKolmogorovProcess B P (2 * m) m (2 * m - 1)‼ := by
  let Y : ℝ≥0 → Ω → ℝ := fun t ↦ (hB.aemeasurable t).mk (B t)
  have hY_meas (t : ℝ≥0) : Measurable (Y t) := (hB.aemeasurable t).measurable_mk
  have hY_ae (t : ℝ≥0) : B t =ᵐ[P] Y t := (hB.aemeasurable t).ae_eq_mk
  have hY_pre : IsPreBrownianReal Y P := hB.congr hY_ae
  have hpow (s t : ℝ≥0) (ω : Ω) :
      dist (Y s ω) (Y t ω) ^ (2 * (m : ℝ)) = (Y s ω - Y t ω) ^ (2 * m) := by
    have hcast : (2 * (m : ℝ)) = ((2 * m : ℕ) : ℝ) := by push_cast; rfl
    rw [hcast, Real.rpow_natCast, Real.dist_eq, pow_mul, pow_mul, sq_abs]
  refine ⟨Y, IsKolmogorovProcess.of_secondCountableTopology_integral_dist_rpow_le hY_meas
    (fun s t ↦ ?_) (fun s t ↦ ?_) (by positivity) (by positivity), hY_ae⟩
  · have hint : Integrable (fun ω ↦ (Y s ω - Y t ω) ^ (2 * m)) P := by
      simpa only [Function.comp_def, Pi.sub_apply] using
        (hY_pre.hasLaw_sub s t).integrable_comp
          (TauCeti.integrable_pow_gaussianReal 0 (nndist (s : ℝ) (t : ℝ)) (2 * m))
    exact hint.congr (ae_of_all _ fun ω ↦ (hpow s t ω).symm)
  · simp_rw [hpow s t, hY_pre.integral_pow_two_mul_sub s t m, Real.rpow_natCast,
      NNReal.coe_natCast]
    exact le_rfl

/-- Every pre-Brownian motion admits a coordinatewise measurable, all-paths continuous Brownian
modification. -/
theorem IsPreBrownianReal.exists_continuous_modification (hB : IsPreBrownianReal B P) :
    ∃ W : ℝ≥0 → Ω → ℝ,
      (∀ t : ℝ≥0, Measurable (W t)) ∧
      (∀ ω : Ω, Continuous (W · ω)) ∧
      IsBrownianReal W P ∧
      (∀ t : ℝ≥0, W t =ᵐ[P] B t) := by
  have hkol : IsAEKolmogorovProcess B P 4 2 3 := by
    convert hB.isAEKolmogorovProcess_two_mul (m := 2) (by omega) <;> norm_num
  obtain ⟨W, hW_meas, hW_cont, hW_ae, _⟩ := hkol.exists_continuous_modification one_lt_two
  exact ⟨W, hW_meas, hW_cont,
    { toIsPreBrownianReal := hB.congr fun t ↦ (hW_ae t).symm
      cont := ae_of_all _ hW_cont },
    hW_ae⟩

/-- **Lévy–Kolmogorov local Hölder regularity of Brownian motion.** For every `γ < 1 / 2` and
compact horizon `T : ℝ≥0`, almost every sample path of a real Brownian motion is `γ`-Hölder
continuous on `Iic T`. -/
theorem IsBrownianReal.ae_holderOnWith (hB : IsBrownianReal B P) {γ : ℝ≥0}
    (hγ : (γ : ℝ) < 1 / 2) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ C : ℝ≥0, HolderOnWith C γ (B · ω) (Iic T) := by
  rcases eq_zero_or_pos γ with rfl | hγ_pos
  · have hcomp : IsCompact (Iic T) := by
      have hIic : Iic T = Icc 0 T := by ext x; simp
      exact hIic ▸ isCompact_Icc
    filter_upwards [hB.cont] with ω hω
    obtain ⟨r, hr_pos, hr⟩ := (hcomp.image hω).isBounded.subset_closedBall_lt 0 0
    refine ⟨⟨2 * r, by positivity⟩, HolderOnWith.of_dist_le fun s hs t ht ↦ ?_⟩
    have hs_le : dist (B s ω) 0 ≤ r := mem_closedBall.mp (hr (mem_image_of_mem _ hs))
    have ht_le : dist 0 (B t ω) ≤ r := by
      rw [dist_comm]
      exact mem_closedBall.mp (hr (mem_image_of_mem _ ht))
    calc dist (B s ω) (B t ω)
        ≤ dist (B s ω) 0 + dist 0 (B t ω) := dist_triangle ..
      _ ≤ 2 * r := by linarith
      _ = (⟨2 * r, by positivity⟩ : ℝ≥0) * dist s t ^ ((0 : ℝ≥0) : ℝ) := by simp
  · have hgap : 0 < 1 - 2 * (γ : ℝ) := by linarith
    let m : ℕ := max 2 (⌊(1 - 2 * (γ : ℝ))⁻¹⌋₊ + 1)
    have hm2 : 2 ≤ m := le_max_left _ _
    have hm1 : 1 < (m : ℝ) := by exact_mod_cast (by omega : 1 < m)
    have hγ_lt : (γ : ℝ) < ((m : ℝ) - 1) / (2 * (m : ℝ)) := by
      have hle_m : ⌊(1 - 2 * (γ : ℝ))⁻¹⌋₊ + 1 ≤ m := le_max_right _ _
      have hinv_lt : (1 - 2 * (γ : ℝ))⁻¹ < m :=
        (Nat.lt_floor_add_one _).trans_le (by exact_mod_cast hle_m)
      have hmul : 1 < (m : ℝ) * (1 - 2 * (γ : ℝ)) := (inv_lt_iff_one_lt_mul₀ hgap).mp hinv_lt
      rw [lt_div_iff₀ (by positivity)]
      linarith
    obtain ⟨W, _, hW_cont, hWB, hW_holder⟩ :=
      (hB.toIsPreBrownianReal.isAEKolmogorovProcess_two_mul (m := m) (by omega))
        |>.exists_continuous_modification hm1
    have hind : W ≡ᵐ[P] B := TauCeti.indist_of_ae_continuous (ae_of_all _ hW_cont) hB.cont hWB
    filter_upwards [hind, hW_holder γ hγ_pos hγ_lt T] with ω hω ⟨C, hC⟩
    refine ⟨C, ?_⟩
    have heq : (B · ω) = (W · ω) := funext fun t ↦ (hω t).symm
    rwa [heq]

/-- If `X` is a coordinatewise measurable, all-paths continuous pre-Brownian motion, then pushing
`P` forward to `C(ℝ≥0, ℝ)` yields a probability measure under which coordinate evaluation is
`IsBrownianReal`. -/
theorem IsPreBrownianReal.isBrownianReal_eval_map {X : ℝ≥0 → Ω → ℝ}
    (hX : IsPreBrownianReal X P) (hmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hcont : ∀ ω : Ω, Continuous (X · ω)) :
    IsBrownianReal (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t)
      (P.map fun ω ↦ (⟨fun t ↦ X t ω, hcont ω⟩ : C(ℝ≥0, ℝ))) := by
  have hpath_meas : Measurable fun ω ↦ (⟨fun t ↦ X t ω, hcont ω⟩ : C(ℝ≥0, ℝ)) :=
    ContinuousMap.measurable_iff_eval.mpr hmeas
  refine
    { hasLaw := fun I ↦ ?_
      cont := ae_of_all _ fun ω ↦ ω.continuous }
  have hres_meas : Measurable fun ω : C(ℝ≥0, ℝ) ↦ I.restrict (ω ·) :=
    measurable_pi_iff.mpr fun i ↦ ContinuousMap.measurable_eval i.1
  refine ⟨hres_meas.aemeasurable, ?_⟩
  rw [Measure.map_map hres_meas hpath_meas]
  exact (hX.hasLaw I).map_eq

end Regularity

end ProbabilityTheory

namespace TauCeti

section Construction

/-- Order-embedding of nonnegative rationals into `ℝ≥0`. -/
private def nnratCastEmb : ℚ≥0 ↪ ℝ≥0 := ⟨(↑), NNRat.cast_injective⟩

/-- Continuous linear reindexing between a finite set in `ℚ≥0` and its cast image in `ℝ≥0`. -/
private def nnratPiEquiv (J : Finset ℚ≥0) : (J.map nnratCastEmb → ℝ) ≃L[ℝ] (J → ℝ) where
  toFun x j := x (J.equivMap nnratCastEmb j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun y i := y ((J.equivMap nnratCastEmb).symm i)
  left_inv x := funext fun i ↦ congrArg x ((J.equivMap nnratCastEmb).apply_symm_apply i)
  right_inv y := funext fun j ↦ congrArg y ((J.equivMap nnratCastEmb).symm_apply_apply j)
  continuous_toFun := continuous_pi fun _ ↦ continuous_apply _
  continuous_invFun := continuous_pi fun _ ↦ continuous_apply _

@[simp]
private lemma nnratPiEquiv_apply (J : Finset ℚ≥0) (x : J.map nnratCastEmb → ℝ) (j : J) :
    nnratPiEquiv J x j = x (J.equivMap nnratCastEmb j) := rfl

/-- Finite-dimensional Brownian Gaussian marginals restricted to nonnegative rational times. -/
private def nnratProjectiveFamily (J : Finset ℚ≥0) : Measure (J → ℝ) :=
  (projectiveFamily (J.map nnratCastEmb)).map (nnratPiEquiv J)

private instance (J : Finset ℚ≥0) : IsProbabilityMeasure (nnratProjectiveFamily J) := by
  rw [nnratProjectiveFamily]
  infer_instance

private lemma isProjectiveMeasureFamily_nnratProjectiveFamily :
    IsProjectiveMeasureFamily (α := fun _ : ℚ≥0 ↦ ℝ) nnratProjectiveFamily := by
  intro I J hJI
  have hmap : J.map nnratCastEmb ⊆ I.map nnratCastEmb := Finset.map_subset_map.mpr hJI
  rw [nnratProjectiveFamily, nnratProjectiveFamily,
    isProjectiveMeasureFamily_projectiveFamily (I.map nnratCastEmb) (J.map nnratCastEmb) hmap,
    Measure.map_map (nnratPiEquiv J).continuous.measurable
      (Finset.measurable_restrict₂ (X := fun _ : ℝ≥0 ↦ ℝ) hmap)]
  have hcomm :
      (nnratPiEquiv J ∘ Finset.restrict₂ (π := fun _ : ℝ≥0 ↦ ℝ) hmap :
        (I.map nnratCastEmb → ℝ) → (J → ℝ)) =
      Finset.restrict₂ (π := fun _ : ℚ≥0 ↦ ℝ) hJI ∘ nnratPiEquiv I := by
    funext x j
    simp only [Function.comp_apply, Finset.restrict₂_def, nnratPiEquiv_apply]
    congr 1
  rw [hcomm]
  exact (Measure.map_map (Finset.measurable_restrict₂ (X := fun _ : ℚ≥0 ↦ ℝ) hJI)
    (nnratPiEquiv I).continuous.measurable).symm

private theorem exists_nnratBrownianMeasure :
    ∃ μ : Measure (ℚ≥0 → ℝ), IsProbabilityMeasure μ ∧ IsProjectiveLimit μ nnratProjectiveFamily :=
  TauCeti.Measure.exists_isProjectiveLimit_of_countable (X := fun _ : ℚ≥0 ↦ ℝ)
    nnratProjectiveFamily isProjectiveMeasureFamily_nnratProjectiveFamily

/-- Projective-limit probability measure of Brownian marginals on `ℚ≥0 → ℝ`. -/
private def nnratBrownianMeasure : Measure (ℚ≥0 → ℝ) :=
  exists_nnratBrownianMeasure.choose

private instance : IsProbabilityMeasure nnratBrownianMeasure :=
  exists_nnratBrownianMeasure.choose_spec.1

private lemma isProjectiveLimit_nnratBrownianMeasure :
    IsProjectiveLimit nnratBrownianMeasure nnratProjectiveFamily :=
  exists_nnratBrownianMeasure.choose_spec.2

private lemma hasLaw_restrict_nnratBrownianMeasure (J : Finset ℚ≥0) :
    HasLaw J.restrict (nnratProjectiveFamily J) nnratBrownianMeasure :=
  ⟨(Finset.measurable_restrict J).aemeasurable, isProjectiveLimit_nnratBrownianMeasure J⟩

private lemma hasLaw_comp_nnratPiEquiv (J : Finset ℚ≥0) :
    HasLaw (nnratPiEquiv J) (nnratProjectiveFamily J)
      (projectiveFamily (J.map nnratCastEmb)) :=
  ⟨(nnratPiEquiv J).continuous.measurable.aemeasurable, rfl⟩

private lemma hasGaussianLaw_restrict_nnratBrownianMeasure (J : Finset ℚ≥0) :
    HasGaussianLaw J.restrict nnratBrownianMeasure := by
  have hg : HasGaussianLaw (nnratPiEquiv J) (projectiveFamily (J.map nnratCastEmb)) :=
    IsGaussian.hasGaussianLaw_id.map_equiv (nnratPiEquiv J)
  have : IsGaussian (nnratProjectiveFamily J) := hg.isGaussian_map
  exact (hasLaw_restrict_nnratBrownianMeasure J).hasGaussianLaw

private lemma hasLaw_eval_nnratBrownianMeasure (r : ℚ≥0) :
    HasLaw (fun ω : ℚ≥0 → ℝ ↦ ω r) (gaussianReal 0 r) nnratBrownianMeasure := by
  let J : Finset ℚ≥0 := {r}
  let r' : J := ⟨r, Finset.mem_singleton_self r⟩
  have h1 : HasLaw (fun y : J → ℝ ↦ y r') (gaussianReal 0 r) (nnratProjectiveFamily J) := by
    refine ⟨(measurable_pi_apply r').aemeasurable, ?_⟩
    rw [nnratProjectiveFamily,
      Measure.map_map (measurable_pi_apply r') (nnratPiEquiv J).continuous.measurable]
    exact (measurePreserving_eval_projectiveFamily (I := J.map nnratCastEmb)
      (J.equivMap nnratCastEmb r')).map_eq
  simpa [Function.comp_def, r'] using h1.comp (hasLaw_restrict_nnratBrownianMeasure J)

private lemma hasLaw_sub_nnratBrownianMeasure (r s : ℚ≥0) :
    HasLaw (fun ω : ℚ≥0 → ℝ ↦ ω r - ω s)
      (gaussianReal 0 (nndist (r : ℝ≥0) (s : ℝ≥0))) nnratBrownianMeasure := by
  let J : Finset ℚ≥0 := {r, s}
  let r' : J := ⟨r, by simp [J]⟩
  let s' : J := ⟨s, by simp [J]⟩
  have hmeas : Measurable (fun y : J → ℝ ↦ y r' - y s') :=
    (measurable_pi_apply r').sub (measurable_pi_apply s')
  have h1 : HasLaw (fun y : J → ℝ ↦ y r' - y s')
      (gaussianReal 0 (nndist (r : ℝ≥0) (s : ℝ≥0))) (nnratProjectiveFamily J) := by
    refine ⟨hmeas.aemeasurable, ?_⟩
    rw [nnratProjectiveFamily, Measure.map_map hmeas (nnratPiEquiv J).continuous.measurable]
    exact (measurePreserving_eval_sub_eval_projectiveFamily (J.map nnratCastEmb)
      (J.equivMap nnratCastEmb r') (J.equivMap nnratCastEmb s')).map_eq
  simpa [Function.comp_def, r', s'] using h1.comp (hasLaw_restrict_nnratBrownianMeasure J)

private lemma covariance_eval_nnratBrownianMeasure (r s : ℚ≥0) :
    cov[fun ω : ℚ≥0 → ℝ ↦ ω r, fun ω : ℚ≥0 → ℝ ↦ ω s; nnratBrownianMeasure] =
      min ((r : ℝ≥0) : ℝ) ((s : ℝ≥0) : ℝ) := by
  let J : Finset ℚ≥0 := {r, s}
  let r' : J := ⟨r, by simp [J]⟩
  let s' : J := ⟨s, by simp [J]⟩
  have h1 := (hasLaw_restrict_nnratBrownianMeasure J).covariance_fun_comp
    (f := fun y : J → ℝ ↦ y r') (g := fun y : J → ℝ ↦ y s')
    (measurable_pi_apply r').aemeasurable (measurable_pi_apply s').aemeasurable
  have h2 := (hasLaw_comp_nnratPiEquiv J).covariance_fun_comp
    (f := fun y : J → ℝ ↦ y r') (g := fun y : J → ℝ ↦ y s')
    (measurable_pi_apply r').aemeasurable (measurable_pi_apply s').aemeasurable
  exact h1.trans (h2.symm.trans (covariance_eval_projectiveFamily (J.map nnratCastEmb)
    (J.equivMap nnratCastEmb r') (J.equivMap nnratCastEmb s')))

/-- For any finite tuple `u : ι → ℝ≥0`, the Brownian covariance matrix `min (u i) (u j)` is
positive semidefinite. -/
private lemma posSemidef_matrix_min {ι : Type*} (u : ι → ℝ≥0) :
    (Matrix.of fun i j : ι ↦ min (u i : ℝ) (u j : ℝ)).PosSemidef := by
  have heq : (Matrix.of fun i j : ι ↦ min (u i : ℝ) (u j : ℝ)) =
      .of fun i j : ι ↦ volume.real (Icc 0 (u i : ℝ) ∩ Icc 0 (u j : ℝ)) := by
    ext; simp [Icc_inter_Icc]
  rw [heq]
  exact posSemidef_matrix_measure_inter (fun _ ↦ measurableSet_Icc)
    (fun _ ↦ isCompact_Icc.measure_ne_top)

/-- Any finite tuple of rational evaluations `(ω (v i))_{i : ι}` has the centered multivariate
Gaussian law with covariance matrix `min (v i) (v j)`, even when `v` has repeated entries. -/
private lemma hasLaw_toLp_nnratBrownianMeasure {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℚ≥0) :
    HasLaw (fun ω : ℚ≥0 → ℝ ↦ toLp 2 (fun i : ι ↦ ω (v i)))
      (multivariateGaussian 0
        (Matrix.of fun i j : ι ↦ min ((v i : ℝ≥0) : ℝ) ((v j : ℝ≥0) : ℝ)))
      nnratBrownianMeasure := by
  let J : Finset ℚ≥0 := Finset.univ.image v
  let L : (J → ℝ) →L[ℝ] (ι → ℝ) :=
    ContinuousLinearMap.pi fun i ↦
      ContinuousLinearMap.proj (R := ℝ) (⟨v i, Finset.mem_image_of_mem v (Finset.mem_univ i)⟩ : J)
  have hgauss_pi : HasGaussianLaw (fun ω : ℚ≥0 → ℝ ↦ fun i : ι ↦ ω (v i))
      nnratBrownianMeasure := (hasGaussianLaw_restrict_nnratBrownianMeasure J).map L
  have hgauss : HasGaussianLaw (fun ω : ℚ≥0 → ℝ ↦ toLp 2 (fun i : ι ↦ ω (v i)))
      nnratBrownianMeasure := hgauss_pi.toLp_pi 2
  refine ⟨hgauss.aemeasurable, ?_⟩
  have : IsGaussian (nnratBrownianMeasure.map fun ω ↦ toLp 2 (fun i : ι ↦ ω (v i))) :=
    hgauss.isGaussian_map
  have hPSD := posSemidef_matrix_min fun i : ι ↦ (v i : ℝ≥0)
  apply IsGaussian.ext
  · rw [integral_map hgauss.aemeasurable aestronglyMeasurable_id]
    simp only [id_eq, integral_id_multivariateGaussian]
    let e : EuclideanSpace ℝ ι ≃L[ℝ] (ι → ℝ) :=
      PiLp.continuousLinearEquiv 2 ℝ fun _ : ι ↦ ℝ
    have heq_fn : (fun x : ℚ≥0 → ℝ ↦ toLp 2 fun i ↦ x (v i)) =
        fun x : ℚ≥0 → ℝ ↦ e.symm (fun i : ι ↦ x (v i)) := rfl
    rw [heq_fn, e.symm.integral_comp_comm, ← map_zero e.symm]
    congr 1
    ext i
    rw [eval_integral (fun j ↦ (hgauss_pi.eval j).integrable),
      (hasLaw_eval_nnratBrownianMeasure (v i)).integral_eq, integral_id_gaussianReal, Pi.zero_apply]
  · rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun ι ℝ).toBasis fun i j ↦ ?_
    rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
      covarianceBilin_apply_eq_cov, covariance_map,
      covarianceBilin_multivariateGaussian hPSD]
    · have hproj (k : ι) :
          (fun u : EuclideanSpace ℝ ι ↦
            inner ℝ ((EuclideanSpace.basisFun ι ℝ).toBasis k) u) ∘
            (fun ω : ℚ≥0 → ℝ ↦ toLp 2 (fun l : ι ↦ ω (v l))) =
          fun ω : ℚ≥0 → ℝ ↦ ω (v k) := by
        ext ω; simp [PiLp.inner_apply]
      rw [hproj i, hproj j, covariance_eval_nnratBrownianMeasure]
      simp [EuclideanSpace.basisFun_apply]
    · exact (continuous_const.inner continuous_id).measurable.aestronglyMeasurable
    · exact (continuous_const.inner continuous_id).measurable.aestronglyMeasurable
    · exact hgauss.aemeasurable
    · exact IsGaussian.hasGaussianLaw_id.memLp_two

/-- Fourth-moment Kolmogorov bound for the rational Brownian coordinate process. -/
private lemma lintegral_edist_pow_four_nnratBrownianMeasure (r s : ℚ≥0) :
    ∫⁻ ω, edist (ω r) (ω s) ^ (4 : ℝ) ∂nnratBrownianMeasure ≤
      (3 : ℝ≥0) * edist (r : ℝ≥0) (s : ℝ≥0) ^ (2 : ℝ) := by
  have hpow (ω : ℚ≥0 → ℝ) : dist (ω r) (ω s) ^ (4 : ℝ) = (ω r - ω s) ^ 4 := by
    have h4 : (4 : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
    have h22 : (4 : ℕ) = 2 * 2 := rfl
    rw [h4, Real.rpow_natCast, Real.dist_eq, h22, pow_mul, pow_mul, sq_abs]
  have hint_pow : Integrable (fun ω : ℚ≥0 → ℝ ↦ (ω r - ω s) ^ 4) nnratBrownianMeasure := by
    simpa only [Function.comp_def] using
      (hasLaw_sub_nnratBrownianMeasure r s).integrable_comp
        (TauCeti.integrable_pow_gaussianReal 0 (nndist ((r : ℝ≥0) : ℝ) ((s : ℝ≥0) : ℝ)) 4)
  have heq (ω : ℚ≥0 → ℝ) :
      edist (ω r) (ω s) ^ (4 : ℝ) = ENNReal.ofReal ((ω r - ω s) ^ 4) := by
    rw [edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by norm_num), hpow]
  simp_rw [heq]
  rw [← ofReal_integral_eq_lintegral_ofReal hint_pow (ae_of_all _ fun _ ↦ by positivity)]
  have h := (hasLaw_sub_nnratBrownianMeasure r s).integral_comp
    (f := fun x : ℝ ↦ x ^ 4) (by fun_prop)
  have hm := TauCeti.Probability.integral_sub_pow_two_mul_gaussianReal
    0 (nndist (r : ℝ≥0) (s : ℝ≥0)) 2
  simp only [Function.comp_apply] at h
  simp only [sub_zero, Nat.reduceMul, Nat.add_one_sub_one, coe_nndist] at hm
  have h3 : ((3‼ : ℕ) : ℝ) = 3 := by norm_num [Nat.doubleFactorial]
  rw [h, hm, h3, mul_comm, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
    edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg zero_le_two, Real.rpow_two,
    ENNReal.coe_ofNat]

private theorem exists_rawBrownian :
    ∃ B₀ : ℝ≥0 → (ℚ≥0 → ℝ) → ℝ,
      (∀ t : ℝ≥0, Measurable (B₀ t)) ∧
      (∀ ω : ℚ≥0 → ℝ, Continuous (B₀ · ω)) ∧
      (∀ r : ℚ≥0, B₀ r =ᵐ[nnratBrownianMeasure] fun ω ↦ ω r) := by
  obtain ⟨B₀, hmeas, hcont, hae, _⟩ :=
    exists_continuous_extension_of_nnrat (P := nnratBrownianMeasure)
      (X := fun (r : ℚ≥0) (ω : ℚ≥0 → ℝ) ↦ ω r) (M := fun _ ↦ 3)
      (by norm_num : (0 : ℝ) < 4) one_lt_two
      (fun r s ↦ by
        rw [← Prod.borelSpace.measurable_eq]
        exact (measurable_pi_apply r).prodMk (measurable_pi_apply s))
      (fun _ r s _ _ ↦ lintegral_edist_pow_four_nnratBrownianMeasure r s)
  exact ⟨B₀, hmeas, hcont, hae⟩

/-- Canonical all-paths continuous Brownian process on `ℚ≥0 → ℝ` constructed by dyadic extension. -/
private def rawBrownian : ℝ≥0 → (ℚ≥0 → ℝ) → ℝ := exists_rawBrownian.choose

private lemma measurable_rawBrownian (t : ℝ≥0) : Measurable (rawBrownian t) :=
  exists_rawBrownian.choose_spec.1 t

private lemma continuous_rawBrownian (ω : ℚ≥0 → ℝ) : Continuous (rawBrownian · ω) :=
  exists_rawBrownian.choose_spec.2.1 ω

private lemma ae_eq_rawBrownian (r : ℚ≥0) :
    rawBrownian r =ᵐ[nnratBrownianMeasure] fun ω ↦ ω r :=
  exists_rawBrownian.choose_spec.2.2 r

/-- The extended process `rawBrownian` has the finite-dimensional laws of Brownian motion. -/
private lemma tendsto_dyadicFloor (t : ℝ≥0) :
    Tendsto (fun n : ℕ ↦ ((((⌊(t : ℝ) * 2 ^ n⌋₊ : ℚ≥0) / 2 ^ n : ℚ≥0) : ℝ≥0))) atTop (𝓝 t) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (g := fun n ↦ (2 : ℝ)⁻¹ ^ n) (fun _ ↦ dist_nonneg) (fun n ↦ ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  have hle : ((((⌊(t : ℝ) * 2 ^ n⌋₊ : ℚ≥0) / 2 ^ n : ℚ≥0) : ℝ≥0) : ℝ) ≤ t := by
    simp only [NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_pow, NNRat.cast_ofNat,
      NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat]
    exact (div_le_iff₀ (by positivity)).2 (Nat.floor_le (by positivity))
  have hlt : (t : ℝ) < ((⌊(t : ℝ) * 2 ^ n⌋₊ : ℝ) + 1) / 2 ^ n :=
    (lt_div_iff₀ (by positivity)).2 (Nat.lt_floor_add_one _)
  rw [NNReal.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hle)]
  simp only [NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_pow, NNRat.cast_ofNat,
    NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat, inv_pow]
  linarith [add_div (⌊(t : ℝ) * 2 ^ n⌋₊ : ℝ) 1 ((2 : ℝ) ^ n), one_div ((2 : ℝ) ^ n)]

private lemma isPreBrownianReal_rawBrownian :
    IsPreBrownianReal rawBrownian nnratBrownianMeasure where
  hasLaw I := by
    let v (n : ℕ) (i : I) : ℚ≥0 := (⌊(i.1 : ℝ) * 2 ^ n⌋₊ : ℚ≥0) / 2 ^ n
    have hv_tendsto (i : I) : Tendsto (fun n ↦ (v n i : ℝ≥0)) atTop (𝓝 i.1) :=
      tendsto_dyadicFloor i.1
    let Z (n : ℕ) (ω : ℚ≥0 → ℝ) : EuclideanSpace ℝ I :=
      toLp 2 fun i : I ↦ rawBrownian (v n i) ω
    let Zlim (ω : ℚ≥0 → ℝ) : EuclideanSpace ℝ I :=
      toLp 2 (I.restrict (rawBrownian · ω))
    have hZ_meas (n : ℕ) : Measurable (Z n) :=
      (MeasurableEquiv.toLp 2 (I → ℝ)).measurable.comp
        (measurable_pi_iff.mpr fun i ↦ measurable_rawBrownian (v n i))
    have hZlim_meas : Measurable Zlim :=
      (MeasurableEquiv.toLp 2 (I → ℝ)).measurable.comp
        (measurable_pi_iff.mpr fun i ↦ measurable_rawBrownian i.1)
    have hZ_tendsto (ω : ℚ≥0 → ℝ) : Tendsto (fun n ↦ Z n ω) atTop (𝓝 (Zlim ω)) :=
      (PiLp.continuous_toLp 2 _).tendsto _ |>.comp
        (tendsto_pi_nhds.mpr fun i ↦ ((continuous_rawBrownian ω).tendsto i.1).comp (hv_tendsto i))
    let S (u : I → ℝ≥0) : Matrix I I ℝ := Matrix.of fun i j : I ↦ min (u i : ℝ) (u j : ℝ)
    have hPSD (u : I → ℝ≥0) : (S u).PosSemidef := posSemidef_matrix_min u
    have hZ_law (n : ℕ) :
        HasLaw (Z n) (multivariateGaussian 0 (S fun i ↦ (v n i : ℝ≥0))) nnratBrownianMeasure := by
      refine (hasLaw_toLp_nnratBrownianMeasure (v n)).congr ?_
      have hall : ∀ᵐ ω ∂nnratBrownianMeasure, ∀ i : I, rawBrownian (v n i) ω = ω (v n i) :=
        ae_all_iff.mpr fun i ↦ ae_eq_rawBrownian (v n i)
      filter_upwards [hall] with ω hω
      ext i
      exact hω i
    have hd := tendstoInDistribution_of_ae_tendsto (μ' := nnratBrownianMeasure)
      (fun n ↦ (hZ_meas n).aemeasurable) hZlim_meas.aemeasurable
      (ae_of_all nnratBrownianMeasure hZ_tendsto)
    have hlim := hd.tendsto
    have hlaw_pm (n : ℕ) :
        (⟨nnratBrownianMeasure.map (Z n), inferInstance⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ I)) =
        (multivariateGaussian 0 (S fun i ↦ (v n i : ℝ≥0))).toProbabilityMeasure :=
      Subtype.ext (hZ_law n).map_eq
    simp only [hlaw_pm] at hlim
    have hc : Continuous (fun u : I → ℝ≥0 ↦
        (multivariateGaussian 0 (S u)).toProbabilityMeasure) :=
      Continuous.multivariateGaussian (m := fun _ ↦ 0) continuous_const (by fun_prop) hPSD
    have hu_tendsto : Tendsto (fun n ↦ fun i : I ↦ (v n i : ℝ≥0)) atTop (𝓝 fun i : I ↦ i.1) :=
      tendsto_pi_nhds.mpr hv_tendsto
    have hZlim_eq : nnratBrownianMeasure.map Zlim = multivariateGaussian 0 (covMatrix I) := by
      simpa [S, covMatrix] using congrArg ProbabilityMeasure.toMeasure
        (tendsto_nhds_unique hlim ((hc.tendsto _).comp hu_tendsto))
    have hZlim_law : HasLaw Zlim (multivariateGaussian 0 (covMatrix I)) nnratBrownianMeasure :=
      ⟨hZlim_meas.aemeasurable, hZlim_eq⟩
    have hequiv_law : HasLaw (MeasurableEquiv.toLp 2 (I → ℝ)).symm
        (projectiveFamily I) (multivariateGaussian 0 (covMatrix I)) :=
      ⟨(MeasurableEquiv.toLp 2 (I → ℝ)).symm.measurable.aemeasurable, rfl⟩
    simpa [Zlim, Function.comp_def] using hequiv_law.comp hZlim_law

end Construction

/-! ### Wiener measure and its universal properties -/

/-- **Wiener measure** on the continuous path space `C(ℝ≥0, ℝ)`: the unique Borel probability
measure under which the coordinate evaluation process `t ↦ (ω ↦ ω t)` is a standard real Brownian
motion (`ProbabilityTheory.IsBrownianReal`). -/
def wienerMeasure : Measure C(ℝ≥0, ℝ) :=
  nnratBrownianMeasure.map fun ω ↦ ⟨fun t ↦ rawBrownian t ω, continuous_rawBrownian ω⟩

instance : IsProbabilityMeasure wienerMeasure := by
  rw [wienerMeasure]
  infer_instance

/-- Under `wienerMeasure`, coordinate evaluation `t ↦ (ω ↦ ω t)` is a standard real Brownian
motion. -/
theorem isBrownianReal_eval_wienerMeasure :
    IsBrownianReal (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t) wienerMeasure :=
  isPreBrownianReal_rawBrownian.isBrownianReal_eval_map
    measurable_rawBrownian continuous_rawBrownian

/-- Under `wienerMeasure`, coordinate evaluation `t ↦ (ω ↦ ω t)` is pre-Brownian. -/
theorem isPreBrownianReal_eval_wienerMeasure :
    IsPreBrownianReal (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t) wienerMeasure :=
  isBrownianReal_eval_wienerMeasure.toIsPreBrownianReal

/-- **Existence of Wiener measure** (Lalley, Theorem 1): there exists a Borel probability measure
on `C(ℝ≥0, ℝ)` whose coordinate process satisfies `IsBrownianReal`. -/
theorem exists_wienerMeasure :
    ∃ W : Measure C(ℝ≥0, ℝ), IsProbabilityMeasure W ∧
      IsBrownianReal (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t) W :=
  ⟨wienerMeasure, inferInstance, isBrownianReal_eval_wienerMeasure⟩

/-- **Uniqueness of Wiener measure:** any measure on `C(ℝ≥0, ℝ)` whose coordinate process satisfies
`IsPreBrownianReal` is equal to `wienerMeasure`. -/
theorem eq_wienerMeasure_of_isPreBrownianReal {μ : Measure C(ℝ≥0, ℝ)}
    (hμ : IsPreBrownianReal (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t) μ) :
    μ = wienerMeasure := by
  have : IsProbabilityMeasure μ := (hμ.hasLaw_eval 0).isProbabilityMeasure
  exact measure_continuousMap_eq_of_forall_finset_map_restrict_eq fun I ↦
    (hμ.hasLaw I).map_eq.trans (isPreBrownianReal_eval_wienerMeasure.hasLaw I).map_eq.symm

/-- A measure on `C(ℝ≥0, ℝ)` equals `wienerMeasure` if and only if coordinate evaluation is
pre-Brownian under it. -/
theorem eq_wienerMeasure_iff_isPreBrownianReal {μ : Measure C(ℝ≥0, ℝ)} :
    μ = wienerMeasure ↔ IsPreBrownianReal (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t) μ :=
  ⟨fun h ↦ h ▸ isPreBrownianReal_eval_wienerMeasure, eq_wienerMeasure_of_isPreBrownianReal⟩

/-- A measure on `C(ℝ≥0, ℝ)` equals `wienerMeasure` if and only if coordinate evaluation is a
standard real Brownian motion under it. -/
theorem eq_wienerMeasure_iff_isBrownianReal {μ : Measure C(ℝ≥0, ℝ)} :
    μ = wienerMeasure ↔ IsBrownianReal (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t) μ :=
  ⟨fun h ↦ h ▸ isBrownianReal_eval_wienerMeasure,
    fun h ↦ eq_wienerMeasure_of_isPreBrownianReal h.toIsPreBrownianReal⟩

/-- The path-space law of any coordinatewise measurable, all-paths continuous pre-Brownian motion
is `wienerMeasure`. -/
theorem _root_.ProbabilityTheory.IsPreBrownianReal.map_mkContinuous_eq_wienerMeasure
    {Ω : Type*} {_ : MeasurableSpace Ω} {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : IsPreBrownianReal X P) (hmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hcont : ∀ ω : Ω, Continuous (X · ω)) :
    (P.map fun ω ↦ (⟨fun t ↦ X t ω, hcont ω⟩ : C(ℝ≥0, ℝ))) = wienerMeasure :=
  eq_wienerMeasure_of_isPreBrownianReal (hX.isBrownianReal_eval_map hmeas hcont).toIsPreBrownianReal

/-! ### Symmetry, scaling invariance, and path regularity of Wiener measure -/

/-- Wiener measure is invariant under path negation `ω ↦ -ω`. -/
@[simp]
theorem map_neg_wienerMeasure :
    wienerMeasure.map (-· : C(ℝ≥0, ℝ) → C(ℝ≥0, ℝ)) = wienerMeasure :=
  isPreBrownianReal_eval_wienerMeasure.neg.map_mkContinuous_eq_wienerMeasure
    (fun t ↦ (ContinuousMap.measurable_eval t).neg) (fun _ ↦ by fun_prop)

/-- **Brownian scaling invariance of Wiener measure:** for every `c ≠ 0`, pushing `wienerMeasure`
forward along `ω ↦ (t ↦ (√c)⁻¹ * ω (c * t))` recovers `wienerMeasure`. -/
theorem map_scale_wienerMeasure {c : ℝ≥0} (hc : c ≠ 0) :
    wienerMeasure.map
      (fun ω : C(ℝ≥0, ℝ) ↦ (⟨fun t ↦ (√(c : ℝ))⁻¹ * ω (c * t), by fun_prop⟩ : C(ℝ≥0, ℝ))) =
      wienerMeasure :=
  (isPreBrownianReal_eval_wienerMeasure.smul hc).map_mkContinuous_eq_wienerMeasure
    (fun t ↦ measurable_const.mul (ContinuousMap.measurable_eval (c * t)))
    (fun _ ↦ by fun_prop)

/-- **Increment-shift invariance of Wiener measure:** for every `t₀ : ℝ≥0`, pushing `wienerMeasure`
forward along `ω ↦ (t ↦ ω (t₀ + t) - ω t₀)` recovers `wienerMeasure`. -/
theorem map_shift_wienerMeasure (t₀ : ℝ≥0) :
    wienerMeasure.map
      (fun ω : C(ℝ≥0, ℝ) ↦ (⟨fun t ↦ ω (t₀ + t) - ω t₀, by fun_prop⟩ : C(ℝ≥0, ℝ))) =
      wienerMeasure :=
  (isPreBrownianReal_eval_wienerMeasure.shift t₀).map_mkContinuous_eq_wienerMeasure
    (fun t ↦ (ContinuousMap.measurable_eval (t₀ + t)).sub (ContinuousMap.measurable_eval t₀))
    (fun _ ↦ by fun_prop)

/-- Under `wienerMeasure`, almost every path is `γ`-Hölder continuous on `Iic T` for every
`γ < 1 / 2` and `T : ℝ≥0`. -/
theorem ae_holderOnWith_wienerMeasure {γ : ℝ≥0} (hγ : (γ : ℝ) < 1 / 2) (T : ℝ≥0) :
    ∀ᵐ (ω : C(ℝ≥0, ℝ)) ∂wienerMeasure, ∃ C : ℝ≥0, HolderOnWith C γ ω (Iic T) :=
  isBrownianReal_eval_wienerMeasure.ae_holderOnWith hγ T

/-! ### Marginals, covariances, variances, and nondegeneracy -/

/-- Under `wienerMeasure`, evaluation at time `t` has law `gaussianReal 0 t`. -/
theorem hasLaw_eval_wienerMeasure (t : ℝ≥0) :
    HasLaw (fun ω : C(ℝ≥0, ℝ) ↦ ω t) (gaussianReal 0 t) wienerMeasure :=
  isPreBrownianReal_eval_wienerMeasure.hasLaw_eval t

/-- Under `wienerMeasure`, the increment `ω s - ω t` has law `gaussianReal 0 (nndist s t)`. -/
theorem hasLaw_eval_sub_wienerMeasure (s t : ℝ≥0) :
    HasLaw (fun ω : C(ℝ≥0, ℝ) ↦ ω s - ω t) (gaussianReal 0 (nndist s.1 t.1)) wienerMeasure :=
  isPreBrownianReal_eval_wienerMeasure.hasLaw_sub s t

/-- Under `wienerMeasure`, almost every path starts at `0`. -/
theorem ae_eval_zero_wienerMeasure : ∀ᵐ ω ∂wienerMeasure, ω 0 = 0 :=
  isPreBrownianReal_eval_wienerMeasure.eval_zero_ae_eq_zero

/-- Expectation of coordinate evaluation at time `t` under `wienerMeasure`: `∫ ω, ω t = 0`. -/
@[simp]
theorem integral_eval_wienerMeasure (t : ℝ≥0) :
    ∫ ω : C(ℝ≥0, ℝ), ω t ∂wienerMeasure = 0 :=
  isPreBrownianReal_eval_wienerMeasure.integral_eval t

/-- Covariance of coordinate evaluations under `wienerMeasure`: `cov[ω s, ω t] = min s t`. -/
@[simp]
theorem covariance_eval_wienerMeasure (s t : ℝ≥0) :
    cov[fun ω : C(ℝ≥0, ℝ) ↦ ω s, fun ω : C(ℝ≥0, ℝ) ↦ ω t; wienerMeasure] = min (s : ℝ) (t : ℝ) :=
  isPreBrownianReal_eval_wienerMeasure.covariance_eval s t

/-- Variance of coordinate evaluation at time `t` under `wienerMeasure`: `Var[ω t] = t`. -/
@[simp]
theorem variance_eval_wienerMeasure (t : ℝ≥0) :
    Var[fun ω : C(ℝ≥0, ℝ) ↦ ω t; wienerMeasure] = t := by
  rw [(hasLaw_eval_wienerMeasure t).variance_eq, variance_id_gaussianReal]

/-- Variance of a coordinate increment under `wienerMeasure`: `Var[ω s - ω t] = dist s t`. -/
theorem variance_eval_sub_wienerMeasure (s t : ℝ≥0) :
    Var[fun ω : C(ℝ≥0, ℝ) ↦ ω s - ω t; wienerMeasure] = dist (s : ℝ) (t : ℝ) := by
  rw [(hasLaw_eval_sub_wienerMeasure s t).variance_eq, variance_id_gaussianReal, coe_nndist]
  rfl

/-- Wiener measure is non-atomic on single paths: it never equals a Dirac mass `Measure.dirac f`. -/
@[simp]
theorem wienerMeasure_ne_dirac (f : C(ℝ≥0, ℝ)) : wienerMeasure ≠ Measure.dirac f := by
  intro h
  have h1 : Var[fun ω : C(ℝ≥0, ℝ) ↦ ω 1; wienerMeasure] = 1 := by simp
  rw [h, variance_dirac f] at h1
  norm_num at h1

/-- Scalar path rescaling `ω ↦ c • ω` (without time rescaling) preserves `wienerMeasure` if and only
if `c = 1` or `c = -1`. -/
@[simp]
theorem map_smul_eq_wienerMeasure_iff {c : ℝ} :
    wienerMeasure.map (c • · : C(ℝ≥0, ℝ) → C(ℝ≥0, ℝ)) = wienerMeasure ↔ c = 1 ∨ c = -1 := by
  constructor
  · intro h
    have hsmul_meas : Measurable (c • · : C(ℝ≥0, ℝ) → C(ℝ≥0, ℝ)) :=
      ContinuousMap.measurable_iff_eval.mpr fun t ↦
        measurable_const.mul (ContinuousMap.measurable_eval t)
    have hvar : Var[fun ω : C(ℝ≥0, ℝ) ↦ ω 1;
        wienerMeasure.map (c • · : C(ℝ≥0, ℝ) → C(ℝ≥0, ℝ))] = c ^ 2 := by
      rw [variance_map (ContinuousMap.measurable_eval 1).aemeasurable hsmul_meas.aemeasurable]
      have hcomp : ((fun ω : C(ℝ≥0, ℝ) ↦ ω 1) ∘ (c • · : C(ℝ≥0, ℝ) → C(ℝ≥0, ℝ))) =
          fun ω : C(ℝ≥0, ℝ) ↦ c * ω 1 := rfl
      rw [hcomp, variance_const_mul, variance_eval_wienerMeasure, NNReal.coe_one, mul_one]
    rw [h, variance_eval_wienerMeasure, NNReal.coe_one] at hvar
    exact sq_eq_one_iff.mp hvar.symm
  · rintro (rfl | rfl) <;> simp

end TauCeti
