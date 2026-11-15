/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Process.Indistinguishable
public import Mathlib.Topology.MetricSpace.Holder
public import Mathlib.Topology.MetricSpace.ProperSpace.Real

import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import TauCeti.Probability.BrownianMotion.Countable
import TauCeti.Probability.Distributions.Gaussian.Continuity
import TauCeti.Probability.Process.Indistinguishable
import TauCeti.Probability.Process.Kolmogorov
import TauCeti.Probability.Process.Kolmogorov.Continuity

/-!
# Continuous modifications of Brownian motion and Wiener measure on `C(ℝ≥0, ℝ)`

This file constructs continuous and locally `< 1 / 2`-Hölder modifications of pre-Brownian
motions, proves sample-path Hölder regularity and indistinguishability of continuous
representatives for Brownian motion, and constructs and characterizes Wiener measure on the
continuous path space `C(ℝ≥0, ℝ)` endowed with the compact-open Borel `σ`-algebra.

Starting from a countable dense subset `D ⊆ ℝ≥0`, the Gaussian skeleton from
`TauCeti.exists_measurePreserving_brownianRealProjectiveFamily_isKolmogorovProcess_of_countable`
satisfies all even-moment Kolmogorov bounds. Extending it to `ℝ≥0` via the one-dimensional
Kolmogorov–Chentsov theorem (`exists_continuous_extension_of_dense_nnreal`) yields an
everywhere-continuous process whose finite linear combinations inherit centered Gaussian laws by
almost-sure convergence and weak continuity of `gaussianReal`, giving `IsBrownianReal`. Pushing the
law forward along the continuous-path map produces Wiener measure on `C(ℝ≥0, ℝ)`, and cylinder
generation of the compact-open Borel `σ`-algebra yields uniqueness of Wiener measure.

## Main statements

* `TauCeti.isBrownianReal_of_dense_brownianRealProjectiveFamily`: an almost-surely continuous,
  coordinatewise a.e.-measurable process agreeing almost everywhere on a dense time set with a
  process having `BrownianReal.projectiveFamily` laws is a Brownian motion (`IsBrownianReal`).
* `ProbabilityTheory.IsPreBrownianReal.exists_continuous_modification`: every pre-Brownian motion
  admits an all-paths continuous, coordinatewise-measurable modification vanishing everywhere at
  `0` whose sample paths are `γ`-Hölder on `[0, T]` for every `T : ℝ≥0` and `γ < 1 / 2`.
* `ProbabilityTheory.IsBrownianReal.ae_holderOnWith_Icc`: almost every sample path of a Brownian
  motion is `γ`-Hölder on `[0, T]` simultaneously for all `T : ℝ≥0` and all `γ < 1 / 2`.
* `ProbabilityTheory.IsBrownianReal.exists_continuous_indist`: every Brownian motion is
  indistinguishable from an all-paths continuous, coordinatewise-measurable Brownian motion
  vanishing everywhere at `0` with `< 1 / 2`-Hölder sample paths on compact intervals.
* `ProbabilityTheory.IsPreBrownianReal.isBrownianReal_map_continuousMap`: pushing forward a
  pre-Brownian motion with everywhere-continuous paths to `C(ℝ≥0, ℝ)` yields Wiener measure.
* `TauCeti.eq_of_isPreBrownianReal_continuousMap`: any two measures on `C(ℝ≥0, ℝ)` under which the
  coordinate process is pre-Brownian are equal.
* `TauCeti.existsUnique_wienerMeasure`, `TauCeti.exists_wienerMeasure`: existence and uniqueness of
  Wiener measure on `C(ℝ≥0, ℝ)`.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Chapter 2, §2.
* S. P. Lalley, *Brownian Motion*, University of Chicago lecture notes, Theorem 1.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped ENNReal NNReal Nat Topology

namespace TauCeti

section DenseExtension

private lemma hasLaw_sum_of_dense_brownianRealProjectiveFamily
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {D : Set ℝ≥0} (hD : Dense D) {X : D → Ω → ℝ}
    (hX : ∀ (I : Finset ℝ≥0) (hI : (I : Set ℝ≥0) ⊆ D),
      HasLaw (fun ω (i : I) ↦ X ⟨i.1, hI i.2⟩ ω) (BrownianReal.projectiveFamily I) P)
    {B : ℝ≥0 → Ω → ℝ}
    (hB_meas : ∀ t, AEMeasurable (B t) P)
    (hB_cont : ∀ᵐ ω ∂P, Continuous (B · ω))
    (hB_ae : ∀ d : D, B d.1 =ᵐ[P] X d)
    {ι : Type*} [Fintype ι] (τ : ι → ℝ≥0) (c : ι → ℝ) :
    HasLaw (fun ω ↦ ∑ i : ι, c i * B (τ i) ω)
      (gaussianReal 0 (∑ i : ι, ∑ j : ι, c i * c j * min (τ i : ℝ) (τ j : ℝ)).toNNReal) P := by
  classical
  have hX_gauss : IsGaussianProcess X P :=
    isGaussianProcess_of_hasLaw_brownianRealProjectiveFamily hX
  have : IsProbabilityMeasure P := hX_gauss.isProbabilityMeasure
  have hseq : ∀ i : ι, ∃ u : ℕ → ℝ≥0, (∀ m, u m ∈ D) ∧ Tendsto u atTop (𝓝 (τ i)) :=
    fun i ↦ mem_closure_iff_seq_limit.1 (hD (τ i))
  choose u huD hu_tend using hseq
  let d : ι → ℕ → D := fun i m ↦ ⟨u i m, huD i m⟩
  let W : ℕ → Ω → ℝ := fun m ω ↦ ∑ i : ι, c i * X (d i m) ω
  let Z : ℕ → Ω → ℝ := fun m ω ↦ ∑ i : ι, c i * B (d i m).1 ω
  let Z_lim : Ω → ℝ := fun ω ↦ ∑ i : ι, c i * B (τ i) ω
  have hZ_meas : ∀ m, AEMeasurable (Z m) P := fun m ↦
    Finset.aemeasurable_fun_sum Finset.univ fun i _ ↦ (hB_meas (d i m).1).const_mul (c i)
  have hZ_lim_meas : AEMeasurable Z_lim P :=
    Finset.aemeasurable_fun_sum Finset.univ fun i _ ↦ (hB_meas (τ i)).const_mul (c i)
  have hZW_ae : ∀ m, Z m =ᵐ[P] W m := by
    intro m
    have hall : ∀ᵐ ω ∂P, ∀ i : ι, B (d i m).1 ω = X (d i m) ω :=
      ae_all_iff.2 fun i ↦ hB_ae (d i m)
    filter_upwards [hall] with ω hω
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hω i]
  have hW_gauss : ∀ m, HasGaussianLaw (W m) P := by
    intro m
    let J : Finset D := Finset.univ.image fun i ↦ d i m
    let L : (J → ℝ) →L[ℝ] ℝ :=
      ∑ i : ι, c i • ContinuousLinearMap.proj (R := ℝ)
        (⟨d i m, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩ : J)
    have hcomp : W m = L ∘ fun ω (j : J) ↦ X j.1 ω := by
      funext ω
      simp [W, L, smul_eq_mul]
    rw [hcomp]
    exact (hX_gauss.hasGaussianLaw J).map L
  have hW_mean : ∀ m, P[W m] = 0 := by
    intro m
    rw [integral_finsetSum _ fun i _ ↦
      (hX_gauss.hasGaussianLaw_eval (d i m)).integrable.const_mul (c i)]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [integral_const_mul,
      (hasLaw_gaussianReal_of_hasLaw_brownianRealProjectiveFamily hX (d i m)).integral_eq,
      integral_id_gaussianReal, mul_zero]
  have hW_var : ∀ m,
      Var[W m; P] = ∑ i : ι, ∑ j : ι, c i * c j * min ((d i m).1 : ℝ) ((d j m).1 : ℝ) := by
    intro m
    rw [← covariance_self (hW_gauss m).aemeasurable]
    change cov[fun ω ↦ ∑ i : ι, c i * X (d i m) ω, fun ω ↦ ∑ j : ι, c j * X (d j m) ω; P] = _
    rw [covariance_fun_sum_fun_sum
      (fun i ↦ (hX_gauss.hasGaussianLaw_eval (d i m)).memLp_two.const_mul (c i))
      (fun j ↦ (hX_gauss.hasGaussianLaw_eval (d j m)).memLp_two.const_mul (c j))]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [covariance_const_mul_left, covariance_const_mul_right,
      covariance_eq_min_of_hasLaw_brownianRealProjectiveFamily hX]
    ring
  let vSeq : ℕ → ℝ≥0 := fun m ↦
    (∑ i : ι, ∑ j : ι, c i * c j * min ((d i m).1 : ℝ) ((d j m).1 : ℝ)).toNNReal
  let vLim : ℝ≥0 :=
    (∑ i : ι, ∑ j : ι, c i * c j * min (τ i : ℝ) (τ j : ℝ)).toNNReal
  have hZ_map : ∀ m, P.map (Z m) = gaussianReal 0 (vSeq m) := by
    intro m
    rw [Measure.map_congr (hZW_ae m), (hW_gauss m).map_eq_gaussianReal, hW_mean m, hW_var m]
  have hZ_tendsto : ∀ᵐ ω ∂P, Tendsto (fun m ↦ Z m ω) atTop (𝓝 (Z_lim ω)) := by
    filter_upwards [hB_cont] with ω hω
    exact tendsto_finsetSum _ fun i _ ↦
      ((hω.tendsto (τ i)).comp (hu_tend i)).const_mul (c i)
  have hdist := tendstoInDistribution_of_ae_tendsto hZ_meas hZ_lim_meas hZ_tendsto
  have hparam_tend : Tendsto vSeq atTop (𝓝 vLim) := by
    refine (continuous_real_toNNReal.tendsto _).comp ?_
    refine tendsto_finsetSum _ fun i _ ↦ tendsto_finsetSum _ fun j _ ↦ ?_
    exact tendsto_const_nhds.mul
      (((NNReal.continuous_coe.tendsto (τ i)).comp (hu_tend i)).min
        ((NNReal.continuous_coe.tendsto (τ j)).comp (hu_tend j)))
  have hgauss_tend : Tendsto
      (fun m ↦ (gaussianReal 0 (vSeq m)).toProbabilityMeasure) atTop
      (𝓝 (gaussianReal 0 vLim).toProbabilityMeasure) := by
    have hcont := Continuous.gaussianReal (m := fun _ : ℝ≥0 ↦ (0 : ℝ)) (v := id)
      continuous_const continuous_id
    exact (hcont.tendsto _).comp hparam_tend
  have hseq_eq :
      (fun m ↦ (⟨P.map (Z m), (Measure.isProbabilityMeasure_map_iff (hZ_meas m)).2 inferInstance⟩ :
        ProbabilityMeasure ℝ)) =
      fun m ↦ (gaussianReal 0 (vSeq m)).toProbabilityMeasure := by
    funext m
    ext1
    exact hZ_map m
  have hlim_eq := tendsto_nhds_unique (hseq_eq ▸ hdist.tendsto) hgauss_tend
  refine ⟨hZ_lim_meas, ?_⟩
  simpa [vLim] using congrArg ProbabilityMeasure.toMeasure hlim_eq

/-- An almost-surely continuous, coordinatewise a.e.-measurable process on `ℝ≥0` that agrees
almost everywhere on a dense time set `D` with a process having `BrownianReal.projectiveFamily`
finite-dimensional laws is a real Brownian motion (`IsBrownianReal`). -/
theorem isBrownianReal_of_dense_brownianRealProjectiveFamily
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {D : Set ℝ≥0} (hD : Dense D) {X : D → Ω → ℝ}
    (hX : ∀ (I : Finset ℝ≥0) (hI : (I : Set ℝ≥0) ⊆ D),
      HasLaw (fun ω (i : I) ↦ X ⟨i.1, hI i.2⟩ ω) (BrownianReal.projectiveFamily I) P)
    {B : ℝ≥0 → Ω → ℝ}
    (hB_meas : ∀ t, AEMeasurable (B t) P)
    (hB_cont : ∀ᵐ ω ∂P, Continuous (B · ω))
    (hB_ae : ∀ d : D, B d.1 =ᵐ[P] X d) :
    IsBrownianReal B P := by
  have hX_gauss : IsGaussianProcess X P :=
    isGaussianProcess_of_hasLaw_brownianRealProjectiveFamily hX
  have : IsProbabilityMeasure P := hX_gauss.isProbabilityMeasure
  have hB_gauss : IsGaussianProcess B P := by
    refine ⟨fun I ↦ ?_⟩
    have hI_meas : AEMeasurable (fun ω ↦ I.restrict (B · ω)) P :=
      AEMeasurable.of_eval fun i ↦ hB_meas i.1
    refine ⟨hI_meas, isGaussian_of_map_eq_gaussianReal fun L ↦ ?_⟩
    classical
    let c : I → ℝ := fun i ↦ L (Pi.single i 1)
    have hL_eq : L ∘ (fun ω ↦ I.restrict (B · ω)) = fun ω ↦ ∑ i : I, c i * B i.1 ω := by
      funext ω
      have hpi : I.restrict (B · ω) = ∑ i : I, B i.1 ω • Pi.single i (1 : ℝ) := by
        ext j
        simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [Function.comp_apply, hpi, map_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [L.map_smul, smul_eq_mul, mul_comm]
    have hlaw := hasLaw_sum_of_dense_brownianRealProjectiveFamily hD hX hB_meas hB_cont hB_ae
      (fun i : I ↦ i.1) c
    refine ⟨0, (∑ i : I, ∑ j : I, c i * c j * min (i.1 : ℝ) (j.1 : ℝ)).toNNReal, ?_⟩
    rw [AEMeasurable.map_map_of_aemeasurable L.continuous.aemeasurable hI_meas, hL_eq]
    exact hlaw.map_eq
  have hB_eval_law : ∀ t : ℝ≥0, HasLaw (B t) (gaussianReal 0 t) P := by
    intro t
    have h := hasLaw_sum_of_dense_brownianRealProjectiveFamily hD hX hB_meas hB_cont hB_ae
      (fun _ : Fin 1 ↦ t) (fun _ ↦ 1)
    simpa [Real.toNNReal_coe] using h
  have hB_mean : ∀ t : ℝ≥0, P[B t] = 0 := fun t ↦ by
    rw [(hB_eval_law t).integral_eq, integral_id_gaussianReal]
  have hB_var : ∀ t : ℝ≥0, Var[B t; P] = t := fun t ↦ by
    rw [(hB_eval_law t).variance_eq, variance_id_gaussianReal]
  have hB_cov : ∀ s t : ℝ≥0, s ≤ t → cov[B s, B t; P] = s := by
    intro s t hst
    have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
    have h := hasLaw_sum_of_dense_brownianRealProjectiveFamily hD hX hB_meas hB_cont hB_ae
      ![t, s] ![1, -1]
    have hsum_fun : (fun ω ↦ ∑ i : Fin 2, (![1, -1] : Fin 2 → ℝ) i * B (![t, s] i) ω) =
        B t - B s := by
      funext ω
      simp [Fin.sum_univ_two, sub_eq_add_neg]
    have hsum_var :
        (∑ i : Fin 2, ∑ j : Fin 2,
          (![1, -1] : Fin 2 → ℝ) i * (![1, -1] : Fin 2 → ℝ) j *
            min ((![t, s] i : ℝ≥0) : ℝ) ((![t, s] j : ℝ≥0) : ℝ)) = (t : ℝ) - s := by
      simp [Fin.sum_univ_two, min_eq_right hst', min_eq_left hst']
      ring
    rw [hsum_fun, hsum_var] at h
    have hvar_sub : Var[B t - B s; P] = (t : ℝ) - s := by
      rw [h.variance_eq, variance_id_gaussianReal, Real.coe_toNNReal _ (sub_nonneg.2 hst')]
    have hBt_L2 : MemLp (B t) 2 P := (hB_gauss.hasGaussianLaw_eval t).memLp_two
    have hBs_L2 : MemLp (B s) 2 P := (hB_gauss.hasGaussianLaw_eval s).memLp_two
    have hexpand : Var[B t - B s; P] =
        Var[B t; P] - 2 * cov[B s, B t; P] + Var[B s; P] := by
      rw [← covariance_self (hBt_L2.sub hBs_L2).aemeasurable,
        covariance_sub_sub hBt_L2 hBs_L2 hBt_L2 hBs_L2,
        covariance_self hBt_L2.aemeasurable, covariance_self hBs_L2.aemeasurable,
        covariance_comm (B t) (B s)]
      ring
    linarith [hB_var t, hB_var s]
  exact ⟨hB_gauss.isPreBrownianReal_of_covariance hB_mean hB_cov, hB_cont⟩

end DenseExtension

end TauCeti

namespace ProbabilityTheory

section Modification

private lemma edist_le_of_mem_Icc_zero {T : ℝ≥0} {x y : ℝ≥0}
    (hx : x ∈ Icc 0 T) (hy : y ∈ Icc 0 T) : edist x y ≤ T := by
  rw [edist_nndist, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nndist, NNReal.dist_eq]
  have hx0 : (0 : ℝ) ≤ x := x.coe_nonneg
  have hy0 : (0 : ℝ) ≤ y := y.coe_nonneg
  have hxT : (x : ℝ) ≤ T := by exact_mod_cast hx.2
  have hyT : (y : ℝ) ≤ T := by exact_mod_cast hy.2
  exact abs_le.2 ⟨by linarith, by linarith⟩

private lemma exists_holderOnWith_modification_fixed
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : IsPreBrownianReal X P) {γ : ℝ≥0} (hγ : γ < 1 / 2) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable (Y t)) ∧
      (∀ ω, Continuous (Y · ω)) ∧
      (∀ (T : ℝ≥0) ω, ∃ L : ℝ≥0, HolderOnWith L γ (Y · ω) (Icc 0 T)) ∧
      ∀ t, Y t =ᵐ[P] X t := by
  let γ' : ℝ≥0 := max γ (1 / 4)
  have hγ'0 : 0 < γ' := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1 / 4) (le_max_right _ _)
  have hγ'_lt : (γ' : ℝ) < 1 / 2 := by
    exact_mod_cast max_lt hγ (by norm_num : (1 / 4 : ℝ≥0) < 1 / 2)
  have hgap : 0 < 1 - 2 * (γ' : ℝ) := by linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / (1 - 2 * (γ' : ℝ)))
  let n : ℕ := k + 1
  have hn0 : n ≠ 0 := Nat.succ_ne_zero k
  have hn_gt : 1 / (1 - 2 * (γ' : ℝ)) < (n : ℝ) := hk.trans (by exact_mod_cast Nat.lt_succ_self k)
  have hkol_exp : 1 + ((2 * n : ℕ) : ℝ) * (γ' : ℝ) < (n : ℝ) := by
    have hmul : 1 < (n : ℝ) * (1 - 2 * (γ' : ℝ)) := (div_lt_iff₀ hgap).1 hn_gt
    push_cast
    linarith
  let X' : ℝ≥0 → Ω → ℝ := fun t ↦ (hX.aemeasurable t).mk (X t)
  have hX'_ae : ∀ t, X t =ᵐ[P] X' t := fun t ↦ (hX.aemeasurable t).ae_eq_mk
  have hX'_pre : IsPreBrownianReal X' P := hX.congr hX'_ae
  have hX'_kol : IsKolmogorovProcess X' P (2 * n : ℕ) n (2 * n - 1)‼ :=
    isKolmogorovProcess_of_hasLaw_sub_gaussianReal
      (fun t ↦ (hX.aemeasurable t).measurable_mk) hX'_pre.hasLaw_sub hn0
  have hX_aekol : IsAEKolmogorovProcess X P (2 * n : ℕ) n (2 * n - 1)‼ :=
    ⟨X', hX'_kol, hX'_ae⟩
  obtain ⟨Y, hY_kol, hY_cont, hY_holder, hY_ae⟩ :=
    hX_aekol.exists_continuous_modification_nnreal hγ'0 hkol_exp
  refine ⟨Y, hY_kol.measurable, hY_cont, fun T ω ↦ ?_, hY_ae⟩
  obtain ⟨L, hL⟩ := hY_holder T ω
  exact ⟨L * T ^ ((γ' : ℝ) - γ),
    hL.of_le (fun _ hx _ hy ↦ edist_le_of_mem_Icc_zero hx hy) (le_max_left γ (1 / 4))⟩

/-- Almost every sample path of a real Brownian motion is locally `γ`-Hölder on `[0, T]`
simultaneously for all compact horizons `T : ℝ≥0` and all Hölder exponents `γ < 1 / 2`. -/
theorem IsBrownianReal.ae_holderOnWith_Icc
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0) ⦃γ : ℝ≥0⦄, γ < 1 / 2 →
      ∃ L : ℝ≥0, HolderOnWith L γ (B · ω) (Icc 0 T) := by
  let γSeq : ℕ → ℝ≥0 := fun m ↦
    ⟨1 / 2 - 1 / (m + 3 : ℝ), by
      have hm : (3 : ℝ) ≤ m + 3 := by linarith [Nat.cast_nonneg (α := ℝ) m]
      have hinv : 1 / (m + 3 : ℝ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hm
      linarith⟩
  have hγSeq_lt : ∀ m, γSeq m < 1 / 2 := by
    intro m
    rw [← NNReal.coe_lt_coe]
    change 1 / 2 - 1 / (m + 3 : ℝ) < (1 / 2 : ℝ≥0)
    have hpos : 0 < 1 / (m + 3 : ℝ) := by positivity
    push_cast
    linarith
  have hae_m : ∀ m : ℕ, ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      ∃ L : ℝ≥0, HolderOnWith L (γSeq m) (B · ω) (Icc 0 T) := by
    intro m
    obtain ⟨Y, -, hY_cont, hY_holder, hY_ae⟩ :=
      exists_holderOnWith_modification_fixed hB.toIsPreBrownianReal (hγSeq_lt m)
    have hind : Y ≡ᵐ[P] B :=
      TauCeti.indist_of_ae_continuous (Eventually.of_forall hY_cont) hB.cont hY_ae
    filter_upwards [hind] with ω hω T
    obtain ⟨L, hL⟩ := hY_holder T ω
    refine ⟨L, fun x hx y hy ↦ ?_⟩
    dsimp only
    rw [← hω x, ← hω y]
    exact hL x hx y hy
  filter_upwards [ae_all_iff.2 hae_m] with ω hω T γ hγ
  have hgap : 0 < 1 / 2 - (γ : ℝ) := by
    have hγ' : (γ : ℝ) < 1 / 2 := by exact_mod_cast hγ
    linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / (1 / 2 - (γ : ℝ)))
  have hm3 : 1 / (1 / 2 - (γ : ℝ)) < (m + 3 : ℝ) := hm.trans (by linarith)
  have hle : γ ≤ γSeq m := by
    rw [← NNReal.coe_le_coe]
    change (γ : ℝ) ≤ 1 / 2 - 1 / (m + 3 : ℝ)
    have hinv : 1 / (m + 3 : ℝ) < 1 / 2 - (γ : ℝ) :=
      (one_div_lt (by positivity) hgap).2 hm3
    linarith
  obtain ⟨L, hL⟩ := hω m T
  exact ⟨L * T ^ ((γSeq m : ℝ) - γ),
    hL.of_le (fun _ hx _ hy ↦ edist_le_of_mem_Icc_zero hx hy) hle⟩

/-- **Continuous modification of a pre-Brownian motion.** Every real pre-Brownian motion admits an
all-paths continuous, coordinatewise Borel-measurable Brownian modification `Y` that vanishes
identically at `0` and whose every sample path is `γ`-Hölder on `[0, T]` for all `T : ℝ≥0` and all
`γ < 1 / 2`. -/
theorem IsPreBrownianReal.exists_continuous_modification
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}
    (hX : IsPreBrownianReal X P) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      IsBrownianReal Y P ∧
      (∀ t, Measurable (Y t)) ∧
      (∀ ω, Continuous (Y · ω)) ∧
      (∀ ω, Y 0 ω = 0) ∧
      (∀ (T : ℝ≥0) ⦃γ : ℝ≥0⦄, γ < 1 / 2 → ∀ ω,
        ∃ L : ℝ≥0, HolderOnWith L γ (Y · ω) (Icc 0 T)) ∧
      ∀ t, Y t =ᵐ[P] X t := by
  classical
  obtain ⟨Y₀, hY₀_meas, hY₀_cont, -, hY₀_ae⟩ :=
    exists_holderOnWith_modification_fixed hX (by norm_num : (1 / 4 : ℝ≥0) < 1 / 2)
  have hY₀_pre : IsPreBrownianReal Y₀ P := hX.congr fun t ↦ (hY₀_ae t).symm
  have hY₀_B : IsBrownianReal Y₀ P := ⟨hY₀_pre, Eventually.of_forall hY₀_cont⟩
  let S : Set Ω := {ω | Y₀ 0 ω = 0 ∧
    ∀ (T : ℝ≥0) ⦃γ : ℝ≥0⦄, γ < 1 / 2 → ∃ L : ℝ≥0, HolderOnWith L γ (Y₀ · ω) (Icc 0 T)}
  have hS_ae : ∀ᵐ ω ∂P, ω ∈ S := by
    filter_upwards [hY₀_B.eval_zero_ae_eq_zero, hY₀_B.ae_holderOnWith_Icc] with ω h0 hH
    exact ⟨h0, hH⟩
  have hSc_null : P Sᶜ = 0 := ae_iff.1 hS_ae
  let N : Set Ω := toMeasurable P Sᶜ
  have hN_meas : MeasurableSet N := measurableSet_toMeasurable P Sᶜ
  have hSc_sub : Sᶜ ⊆ N := subset_toMeasurable P Sᶜ
  have hN_null : P N = 0 := by rw [measure_toMeasurable, hSc_null]
  let Y : ℝ≥0 → Ω → ℝ := fun t ω ↦ if ω ∈ N then 0 else Y₀ t ω
  have hYY₀_ae : ∀ t, Y t =ᵐ[P] Y₀ t := by
    intro t
    filter_upwards [compl_mem_ae_iff.2 hN_null] with ω hω
    have hω' : ω ∉ N := hω
    simp [Y, hω']
  have hY_ae : ∀ t, Y t =ᵐ[P] X t := fun t ↦ (hYY₀_ae t).trans (hY₀_ae t)
  have hY_B : IsBrownianReal Y P :=
    ⟨hX.congr fun t ↦ (hY_ae t).symm, Eventually.of_forall fun ω ↦ by
      by_cases hω : ω ∈ N <;> simp [Y, hω, continuous_const, hY₀_cont ω]⟩
  refine ⟨Y, hY_B, fun t ↦ Measurable.ite hN_meas measurable_const (hY₀_meas t),
    fun ω ↦ ?_, fun ω ↦ ?_, fun T γ hγ ω ↦ ?_, hY_ae⟩
  · by_cases hω : ω ∈ N <;> simp [Y, hω, continuous_const, hY₀_cont ω]
  · by_cases hω : ω ∈ N
    · simp [Y, hω]
    · have hωS : ω ∈ S := by
        by_contra hc
        exact hω (hSc_sub hc)
      simpa [Y, hω] using hωS.1
  · by_cases hω : ω ∈ N
    · exact ⟨0, fun x _ y _ ↦ by simp [Y, hω]⟩
    · have hωS : ω ∈ S := by
        by_contra hc
        exact hω (hSc_sub hc)
      obtain ⟨L, hL⟩ := hωS.2 T hγ
      exact ⟨L, by simpa [Y, hω] using hL⟩

/-- Every real Brownian motion is indistinguishable from an all-paths continuous, coordinatewise
Borel-measurable Brownian motion vanishing everywhere at `0` whose sample paths are locally
`γ`-Hölder for every `γ < 1 / 2`. -/
theorem IsBrownianReal.exists_continuous_indist
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      IsBrownianReal Y P ∧
      (∀ t, Measurable (Y t)) ∧
      (∀ ω, Continuous (Y · ω)) ∧
      (∀ ω, Y 0 ω = 0) ∧
      (∀ (T : ℝ≥0) ⦃γ : ℝ≥0⦄, γ < 1 / 2 → ∀ ω,
        ∃ L : ℝ≥0, HolderOnWith L γ (Y · ω) (Icc 0 T)) ∧
      Y ≡ᵐ[P] B := by
  obtain ⟨Y, hY_B, hY_meas, hY_cont, hY_zero, hY_holder, hY_ae⟩ :=
    hB.toIsPreBrownianReal.exists_continuous_modification
  exact ⟨Y, hY_B, hY_meas, hY_cont, hY_zero, hY_holder,
    TauCeti.indist_of_ae_continuous (Eventually.of_forall hY_cont) hB.cont hY_ae⟩

end Modification

section WienerSpace

private lemma aemeasurable_continuousMap_of_aemeasurable_eval
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hmeas : ∀ t, AEMeasurable (B t) P) (hcont : ∀ ω, Continuous (B · ω)) :
    AEMeasurable (fun ω ↦ (⟨fun t ↦ B t ω, hcont ω⟩ : C(ℝ≥0, ℝ))) P := by
  obtain ⟨D, hD_count, hD_dense⟩ := exists_countable_dense ℝ≥0
  have : Countable D := hD_count.to_subtype
  let res : C(ℝ≥0, ℝ) → (D → ℝ) := fun f d ↦ f d.1
  have hres_inj : Function.Injective res := by
    intro f₁ f₂ h
    ext t
    exact congrFun (f₁.continuous.ext_on hD_dense f₂.continuous fun s hs ↦ congrFun h ⟨s, hs⟩) t
  have hcomap : MeasurableSpace.comap res inferInstance = ContinuousMap.measurableSpace := by
    apply le_antisymm
    · rw [← measurable_iff_comap_le]
      exact measurable_pi_iff.2 fun d ↦ ContinuousMap.measurable_eval d.1
    · rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval, iSup_le_iff]
      intro t
      rw [← measurable_iff_comap_le]
      obtain ⟨u, huD, hu_tend⟩ := mem_closure_iff_seq_limit.1 (hD_dense t)
      refine @measurable_of_tendsto_metrizable C(ℝ≥0, ℝ) ℝ
        (MeasurableSpace.comap res inferInstance) _ _ _ _
        (fun n f ↦ res f ⟨u n, huD n⟩) (fun f ↦ f t) (fun n ↦ ?_)
        (tendsto_pi_nhds.2 fun f ↦ (f.continuous.tendsto t).comp hu_tend)
      exact (measurable_pi_apply ⟨u n, huD n⟩).comp (comap_measurable res)
  let Φ : Ω → C(ℝ≥0, ℝ) := fun ω ↦ ⟨fun t ↦ B t ω, hcont ω⟩
  have hcomp : AEMeasurable (res ∘ Φ) P := aemeasurable_pi_iff.2 fun d ↦ hmeas d.1
  have hcomap_ae : @AEMeasurable Ω C(ℝ≥0, ℝ) (MeasurableSpace.comap res _) mΩ Φ P :=
    (aemeasurable_comap_iff hres_inj).2 hcomp
  rwa [hcomap] at hcomap_ae

/-- Pushing the ambient measure forward along the continuous-path map of an everywhere-continuous
real pre-Brownian motion yields a probability measure on `C(ℝ≥0, ℝ)` under which coordinate
evaluation is a Brownian motion (`IsBrownianReal`). -/
theorem IsPreBrownianReal.isBrownianReal_map_continuousMap
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hcont : ∀ ω, Continuous (B · ω)) :
    IsProbabilityMeasure (P.map fun ω ↦ (⟨fun t ↦ B t ω, hcont ω⟩ : C(ℝ≥0, ℝ))) ∧
      IsBrownianReal (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t)
        (P.map fun ω ↦ (⟨fun t ↦ B t ω, hcont ω⟩ : C(ℝ≥0, ℝ))) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let Φ : Ω → C(ℝ≥0, ℝ) := fun ω ↦ ⟨fun t ↦ B t ω, hcont ω⟩
  have hΦ : AEMeasurable Φ P :=
    aemeasurable_continuousMap_of_aemeasurable_eval hB.aemeasurable hcont
  refine ⟨(Measure.isProbabilityMeasure_map_iff hΦ).2 inferInstance,
    ⟨⟨fun I ↦ ?_⟩, Eventually.of_forall fun ω ↦ ω.continuous⟩⟩
  have hres_meas : Measurable (fun ω : C(ℝ≥0, ℝ) ↦ I.restrict (fun t ↦ ω t)) :=
    measurable_pi_iff.2 fun i ↦ ContinuousMap.measurable_eval i.1
  refine ⟨hres_meas.aemeasurable, ?_⟩
  rw [AEMeasurable.map_map_of_aemeasurable hres_meas.aemeasurable hΦ]
  exact (hB.hasLaw I).map_eq

end WienerSpace

end ProbabilityTheory

namespace TauCeti

/-- **Uniqueness of Wiener measure on `C(ℝ≥0, ℝ)`.** Any two Borel measures on `C(ℝ≥0, ℝ)` under
which the coordinate evaluation process is pre-Brownian are equal. -/
theorem eq_of_isPreBrownianReal_continuousMap {W₁ W₂ : Measure C(ℝ≥0, ℝ)}
    (hW₁ : IsPreBrownianReal (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t) W₁)
    (hW₂ : IsPreBrownianReal (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t) W₂) :
    W₁ = W₂ := by
  have : IsProbabilityMeasure W₁ := hW₁.isGaussianProcess.isProbabilityMeasure
  have : IsProbabilityMeasure W₂ := hW₂.isGaussianProcess.isProbabilityMeasure
  have hgen : (ContinuousMap.measurableSpace : MeasurableSpace C(ℝ≥0, ℝ)) =
      MeasurableSpace.generateFrom
        (Set.preimage (DFunLike.coe : C(ℝ≥0, ℝ) → (ℝ≥0 → ℝ)) ''
          measurableCylinders (fun _ : ℝ≥0 ↦ ℝ)) := by
    rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval, ← MeasurableSpace.comap_generateFrom,
      generateFrom_measurableCylinders]
    dsimp only [MeasurableSpace.pi]
    simp_rw [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
    rfl
  refine ext_of_generate_finite _ hgen
    (isPiSystem_measurableCylinders.comap _) ?_ (by simp)
  rintro _ ⟨c, hc, rfl⟩
  obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders c).1 hc
  have hmeas : Measurable (fun ω : C(ℝ≥0, ℝ) ↦ I.restrict (fun t ↦ ω t)) :=
    measurable_pi_iff.2 fun i ↦ ContinuousMap.measurable_eval i.1
  change W₁ ((fun ω : C(ℝ≥0, ℝ) ↦ I.restrict (fun t ↦ ω t)) ⁻¹' S) =
    W₂ ((fun ω : C(ℝ≥0, ℝ) ↦ I.restrict (fun t ↦ ω t)) ⁻¹' S)
  rw [← Measure.map_apply hmeas hS, ← Measure.map_apply hmeas hS,
    (hW₁.hasLaw I).map_eq, (hW₂.hasLaw I).map_eq]

/-- **Wiener measure on continuous paths** (Lalley, Theorem 1): there exists a probability measure
`W` on `C(ℝ≥0, ℝ)` whose coordinate evaluation process satisfies `IsBrownianReal`. -/
theorem exists_wienerMeasure :
    ∃ W : Measure C(ℝ≥0, ℝ), IsProbabilityMeasure W ∧
      IsBrownianReal (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t) W := by
  obtain ⟨D, hD_count, hD_dense⟩ := exists_countable_dense ℝ≥0
  have : Countable D := hD_count.to_subtype
  obtain ⟨P, -, hP_proj, hP_kol⟩ :=
    exists_measurePreserving_brownianRealProjectiveFamily_isKolmogorovProcess_of_countable D
  have hkol4 :
      IsKolmogorovProcess (fun (t : D) (x : D → ℝ) ↦ x t) P (2 * 2 : ℕ) 2 (2 * 2 - 1)‼ :=
    hP_kol (by decide : (2 : ℕ) ≠ 0)
  obtain ⟨B, hB_kol, hB_cont, -, hB_ae⟩ :=
    hkol4.IsAEKolmogorovProcess.exists_continuous_extension_of_dense_nnreal hD_dense
      (γ := 1 / 8) (by norm_num) (by norm_num)
  have hB_brownian : IsBrownianReal B P :=
    isBrownianReal_of_dense_brownianRealProjectiveFamily hD_dense
      (fun I hI ↦ (hP_proj I hI).hasLaw)
      (fun t ↦ (hB_kol.measurable t).aemeasurable)
      (Eventually.of_forall hB_cont) hB_ae
  exact ⟨P.map fun ω ↦ ⟨fun t ↦ B t ω, hB_cont ω⟩,
    hB_brownian.toIsPreBrownianReal.isBrownianReal_map_continuousMap hB_cont⟩

/-- **Existence and uniqueness of Wiener measure on `C(ℝ≥0, ℝ)`.** There is a unique Borel measure
on `C(ℝ≥0, ℝ)` under which the coordinate process is a Brownian motion (`IsBrownianReal`). -/
theorem existsUnique_wienerMeasure :
    ∃! W : Measure C(ℝ≥0, ℝ), IsBrownianReal (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t) W := by
  obtain ⟨W, -, hW⟩ := exists_wienerMeasure
  exact ⟨W, hW, fun W' hW' ↦
    eq_of_isPreBrownianReal_continuousMap hW'.toIsPreBrownianReal hW.toIsPreBrownianReal⟩

end TauCeti
