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

import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import TauCeti.MeasureTheory.Measure.ContinuousMap
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
law forward along the continuous-path map produces Wiener measure on `C(ℝ≥0, ℝ)`, and
finite-dimensional determination of laws on `C(ℝ≥0, ℝ)`
(`TauCeti.continuousMap_measure_ext_of_forall_finset_map_restrict_eq`) yields uniqueness of Wiener
measure.

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

/-- Finite linear combinations of a process on `D ⊆ ℝ≥0` with `BrownianReal.projectiveFamily`
marginals have centered Gaussian laws with the Brownian bilinear variance. -/
private lemma hasLaw_sum_of_hasLaw_brownianRealProjectiveFamily
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {D : Set ℝ≥0} {X : D → Ω → ℝ}
    (hX : ∀ (I : Finset ℝ≥0) (hI : (I : Set ℝ≥0) ⊆ D),
      HasLaw (fun ω (i : I) ↦ X ⟨i.1, hI i.2⟩ ω) (BrownianReal.projectiveFamily I) P)
    {ι : Type*} [Fintype ι] (d : ι → D) (c : ι → ℝ) :
    HasLaw (fun ω ↦ ∑ i : ι, c i * X (d i) ω)
      (gaussianReal 0 (∑ i : ι, ∑ j : ι, c i * c j * min ((d i).1 : ℝ) ((d j).1 : ℝ)).toNNReal)
      P := by
  classical
  have hX_gauss : IsGaussianProcess X P :=
    isGaussianProcess_of_hasLaw_brownianRealProjectiveFamily hX
  have : IsProbabilityMeasure P := hX_gauss.isProbabilityMeasure
  let J : Finset D := Finset.univ.image d
  let L : (J → ℝ) →L[ℝ] ℝ := ∑ i : ι, c i • ContinuousLinearMap.proj (R := ℝ)
    (⟨d i, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩ : J)
  have hW_gauss : HasGaussianLaw (fun ω ↦ ∑ i : ι, c i * X (d i) ω) P := by
    have hcomp : (fun ω ↦ ∑ i : ι, c i * X (d i) ω) = L ∘ fun ω (j : J) ↦ X j.1 ω := by
      funext ω; simp [L, smul_eq_mul]
    exact hcomp ▸ (hX_gauss.hasGaussianLaw J).map L
  have hmean : P[fun ω ↦ ∑ i : ι, c i * X (d i) ω] = 0 := by
    rw [integral_finsetSum _ fun i _ ↦
      (hX_gauss.hasGaussianLaw_eval (d i)).integrable.const_mul (c i)]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [integral_const_mul,
      (hasLaw_gaussianReal_of_hasLaw_brownianRealProjectiveFamily hX (d i)).integral_eq,
      integral_id_gaussianReal, mul_zero]
  have hvar : Var[fun ω ↦ ∑ i : ι, c i * X (d i) ω; P] =
      ∑ i : ι, ∑ j : ι, c i * c j * min ((d i).1 : ℝ) ((d j).1 : ℝ) := by
    rw [← covariance_self hW_gauss.aemeasurable, covariance_fun_sum_fun_sum
      (fun i ↦ (hX_gauss.hasGaussianLaw_eval (d i)).memLp_two.const_mul (c i))
      (fun j ↦ (hX_gauss.hasGaussianLaw_eval (d j)).memLp_two.const_mul (c j))]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [covariance_const_mul_left, covariance_const_mul_right,
      covariance_eq_min_of_hasLaw_brownianRealProjectiveFamily hX]
    ring
  refine ⟨hW_gauss.aemeasurable, ?_⟩
  rw [hW_gauss.map_eq_gaussianReal, hmean, hvar]

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
  have : IsProbabilityMeasure P :=
    (isGaussianProcess_of_hasLaw_brownianRealProjectiveFamily hX).isProbabilityMeasure
  choose u huD hu_tend using fun i : ι ↦ mem_closure_iff_seq_limit.1 (hD (τ i))
  let d : ι → ℕ → D := fun i m ↦ ⟨u i m, huD i m⟩
  let Z : ℕ → Ω → ℝ := fun m ω ↦ ∑ i : ι, c i * B (d i m).1 ω
  let Z_lim : Ω → ℝ := fun ω ↦ ∑ i : ι, c i * B (τ i) ω
  have hZ_meas : ∀ m, AEMeasurable (Z m) P := fun m ↦
    Finset.aemeasurable_fun_sum Finset.univ fun i _ ↦ (hB_meas (d i m).1).const_mul (c i)
  have hZ_lim_meas : AEMeasurable Z_lim P :=
    Finset.aemeasurable_fun_sum Finset.univ fun i _ ↦ (hB_meas (τ i)).const_mul (c i)
  let vSeq : ℕ → ℝ≥0 := fun m ↦
    (∑ i : ι, ∑ j : ι, c i * c j * min ((d i m).1 : ℝ) ((d j m).1 : ℝ)).toNNReal
  let vLim : ℝ≥0 := (∑ i : ι, ∑ j : ι, c i * c j * min (τ i : ℝ) (τ j : ℝ)).toNNReal
  have hZ_map : ∀ m, P.map (Z m) = gaussianReal 0 (vSeq m) := fun m ↦ by
    have hZW : Z m =ᵐ[P] fun ω ↦ ∑ i : ι, c i * X (d i m) ω := by
      filter_upwards [ae_all_iff.2 fun i ↦ hB_ae (d i m)] with ω hω
      exact Finset.sum_congr rfl fun i _ ↦ by rw [hω i]
    rw [Measure.map_congr hZW]
    exact (hasLaw_sum_of_hasLaw_brownianRealProjectiveFamily hX (fun i ↦ d i m) c).map_eq
  have hZ_tend : ∀ᵐ ω ∂P, Tendsto (fun m ↦ Z m ω) atTop (𝓝 (Z_lim ω)) := by
    filter_upwards [hB_cont] with ω hω
    exact tendsto_finsetSum _ fun i _ ↦ ((hω.tendsto (τ i)).comp (hu_tend i)).const_mul (c i)
  have hdist := tendstoInDistribution_of_ae_tendsto hZ_meas hZ_lim_meas hZ_tend
  have hparam_tend : Tendsto vSeq atTop (𝓝 vLim) :=
    (continuous_real_toNNReal.tendsto _).comp <| tendsto_finsetSum _ fun i _ ↦
      tendsto_finsetSum _ fun j _ ↦ tendsto_const_nhds.mul
        (((NNReal.continuous_coe.tendsto (τ i)).comp (hu_tend i)).min
          ((NNReal.continuous_coe.tendsto (τ j)).comp (hu_tend j)))
  have hgauss_tend := ((Continuous.gaussianReal (m := fun _ : ℝ≥0 ↦ (0 : ℝ)) (v := id)
    continuous_const continuous_id).tendsto _).comp hparam_tend
  have hseq_eq :
      (fun m ↦ (⟨P.map (Z m), (Measure.isProbabilityMeasure_map_iff (hZ_meas m)).2 inferInstance⟩ :
        ProbabilityMeasure ℝ)) =
      fun m ↦ (gaussianReal 0 (vSeq m)).toProbabilityMeasure := by
    funext m; ext1; exact hZ_map m
  refine ⟨hZ_lim_meas, ?_⟩
  have hlim_eq := congrArg ProbabilityMeasure.toMeasure
    (tendsto_nhds_unique (hseq_eq ▸ hdist.tendsto) hgauss_tend)
  exact (ProbabilityMeasure.coe_mk _ _).symm.trans (hlim_eq.trans (by simp [vLim]))

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
  have : IsProbabilityMeasure P :=
    (isGaussianProcess_of_hasLaw_brownianRealProjectiveFamily hX).isProbabilityMeasure
  have hB_gauss : IsGaussianProcess B P := ⟨fun I ↦ by
    have hI_meas : AEMeasurable (fun ω ↦ I.restrict (B · ω)) P :=
      AEMeasurable.of_eval fun i ↦ hB_meas i.1
    refine ⟨hI_meas, isGaussian_of_map_eq_gaussianReal fun L ↦ ?_⟩
    classical
    let c : I → ℝ := fun i ↦ L (Pi.single i 1)
    have hL_eq : L ∘ (fun ω ↦ I.restrict (B · ω)) = fun ω ↦ ∑ i : I, c i * B i.1 ω := by
      funext ω
      have hpi : I.restrict (B · ω) = ∑ i : I, B i.1 ω • Pi.single i (1 : ℝ) := by
        ext j; simp [Finset.sum_apply, Pi.single_apply]
      rw [Function.comp_apply, hpi, map_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by rw [L.map_smul, smul_eq_mul, mul_comm]
    refine ⟨0, (∑ i : I, ∑ j : I, c i * c j * min (i.1 : ℝ) (j.1 : ℝ)).toNNReal, ?_⟩
    rw [AEMeasurable.map_map_of_aemeasurable L.continuous.aemeasurable hI_meas, hL_eq]
    exact (hasLaw_sum_of_dense_brownianRealProjectiveFamily hD hX hB_meas hB_cont hB_ae
      Subtype.val c).map_eq⟩
  have hB_eval : ∀ t : ℝ≥0, HasLaw (B t) (gaussianReal 0 t) P := fun t ↦ by
    simpa [Real.toNNReal_coe] using hasLaw_sum_of_dense_brownianRealProjectiveFamily hD hX
      hB_meas hB_cont hB_ae (fun _ : Fin 1 ↦ t) (fun _ ↦ 1)
  have hB_mean : ∀ t : ℝ≥0, P[B t] = 0 := fun t ↦ by
    rw [(hB_eval t).integral_eq, integral_id_gaussianReal]
  have hB_var : ∀ t : ℝ≥0, Var[B t; P] = t := fun t ↦ by
    rw [(hB_eval t).variance_eq, variance_id_gaussianReal]
  have hB_cov : ∀ s t : ℝ≥0, s ≤ t → cov[B s, B t; P] = s := fun s t hst ↦ by
    have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
    have h := hasLaw_sum_of_dense_brownianRealProjectiveFamily hD hX hB_meas hB_cont hB_ae
      ![t, s] ![1, -1]
    have hfun : (fun ω ↦ ∑ i : Fin 2, (![1, -1] : Fin 2 → ℝ) i * B (![t, s] i) ω) = B t - B s := by
      funext ω; simp [Fin.sum_univ_two, sub_eq_add_neg]
    have hv : (∑ i : Fin 2, ∑ j : Fin 2, (![1, -1] : Fin 2 → ℝ) i * (![1, -1] : Fin 2 → ℝ) j *
        min ((![t, s] i : ℝ≥0) : ℝ) ((![t, s] j : ℝ≥0) : ℝ)) = (t : ℝ) - s := by
      simp [Fin.sum_univ_two, min_eq_right hst', min_eq_left hst']; ring
    rw [hfun, hv] at h
    have hvar_sub : Var[B t - B s; P] = (t : ℝ) - s := by
      rw [h.variance_eq, variance_id_gaussianReal, Real.coe_toNNReal _ (sub_nonneg.2 hst')]
    have hBt := (hB_gauss.hasGaussianLaw_eval t).memLp_two
    have hBs := (hB_gauss.hasGaussianLaw_eval s).memLp_two
    have hexpand : Var[B t - B s; P] = Var[B t; P] - 2 * cov[B s, B t; P] + Var[B s; P] := by
      rw [← covariance_self (hBt.sub hBs).aemeasurable, covariance_sub_sub hBt hBs hBt hBs,
        covariance_self hBt.aemeasurable, covariance_self hBs.aemeasurable,
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
  have hxT : (x : ℝ) ≤ T := by exact_mod_cast hx.2
  have hyT : (y : ℝ) ≤ T := by exact_mod_cast hy.2
  exact abs_le.2 ⟨by linarith [x.coe_nonneg], by linarith [y.coe_nonneg]⟩

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
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / (1 - 2 * (γ' : ℝ)))
  let n : ℕ := k + 1
  have hkol_exp : 1 + ((2 * n : ℕ) : ℝ) * (γ' : ℝ) < (n : ℝ) := by
    have hn_gt : 1 / (1 - 2 * (γ' : ℝ)) < (n : ℝ) := hk.trans (by exact_mod_cast Nat.lt_succ_self k)
    have hmul : 1 < (n : ℝ) * (1 - 2 * (γ' : ℝ)) := (div_lt_iff₀ (by linarith)).1 hn_gt
    push_cast; linarith
  let X' : ℝ≥0 → Ω → ℝ := fun t ↦ (hX.aemeasurable t).mk (X t)
  have hX'_ae : ∀ t, X t =ᵐ[P] X' t := fun t ↦ (hX.aemeasurable t).ae_eq_mk
  have hX_aekol : IsAEKolmogorovProcess X P (2 * n : ℕ) n (2 * n - 1)‼ :=
    ⟨X', isKolmogorovProcess_of_hasLaw_sub_gaussianReal
      (fun t ↦ (hX.aemeasurable t).measurable_mk) (hX.congr hX'_ae).hasLaw_sub
      (Nat.succ_ne_zero k), hX'_ae⟩
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
  let γSeq : ℕ → ℝ≥0 := fun m ↦ (1 / 2 : ℝ≥0) - ((m + 3 : ℕ) : ℝ≥0)⁻¹
  have hγSeq_lt : ∀ m, γSeq m < 1 / 2 := fun m ↦
    tsub_lt_self (by norm_num) (inv_pos.2 (by exact_mod_cast Nat.succ_pos (m + 2)))
  have hae_m : ∀ m : ℕ, ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      ∃ L : ℝ≥0, HolderOnWith L (γSeq m) (B · ω) (Icc 0 T) := fun m ↦ by
    obtain ⟨Y, -, hY_cont, hY_holder, hY_ae⟩ :=
      exists_holderOnWith_modification_fixed hB.toIsPreBrownianReal (hγSeq_lt m)
    filter_upwards [TauCeti.indist_of_ae_continuous (Eventually.of_forall hY_cont) hB.cont hY_ae]
      with ω hω T
    obtain ⟨L, hL⟩ := hY_holder T ω
    exact ⟨L, fun x hx y hy ↦ by simpa only [← hω x, ← hω y] using hL x hx y hy⟩
  filter_upwards [ae_all_iff.2 hae_m] with ω hω T γ hγ
  have hgap : 0 < 1 / 2 - (γ : ℝ) := by
    have hγ' : (γ : ℝ) < 1 / 2 := by exact_mod_cast hγ
    linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / (1 / 2 - (γ : ℝ)))
  have hle : γ ≤ γSeq m := by
    have hinv_le : ((m + 3 : ℕ) : ℝ≥0)⁻¹ ≤ 1 / 2 := by
      have h3 : (2 : ℝ≥0) ≤ (m + 3 : ℕ) := by exact_mod_cast (by omega : 2 ≤ m + 3)
      simpa only [one_div] using inv_anti₀ (by norm_num) h3
    rw [← NNReal.coe_le_coe, NNReal.coe_sub hinv_le]
    have hinv : (((m + 3 : ℕ) : ℝ≥0)⁻¹ : ℝ) < 1 / 2 - (γ : ℝ) := by
      simpa only [NNReal.coe_inv, NNReal.coe_natCast, ← one_div] using
        (one_div_lt (by positivity) hgap).2 (hm.trans (by push_cast; linarith))
    push_cast at hinv ⊢; linarith
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
  have hY₀_B : IsBrownianReal Y₀ P :=
    ⟨hX.congr fun t ↦ (hY₀_ae t).symm, Eventually.of_forall hY₀_cont⟩
  obtain ⟨N, hN_sub, hN_meas, hN_null⟩ := exists_measurable_superset_of_null
    (hY₀_B.eval_zero_ae_eq_zero.and hY₀_B.ae_holderOnWith_Icc)
  let Y : ℝ≥0 → Ω → ℝ := fun t ω ↦ if ω ∈ N then 0 else Y₀ t ω
  have hY_ae : ∀ t, Y t =ᵐ[P] X t := fun t ↦ by
    filter_upwards [compl_mem_ae_iff.2 hN_null, hY₀_ae t] with ω (hωN : ω ∉ N) hω0
    exact (ite_eq_right hωN).trans hω0
  have hY_cont : ∀ ω, Continuous (Y · ω) := fun ω ↦ by
    by_cases hω : ω ∈ N <;> simp [Y, hω, continuous_const, hY₀_cont ω]
  refine ⟨Y, ⟨hX.congr fun t ↦ (hY_ae t).symm, Eventually.of_forall hY_cont⟩,
    fun t ↦ Measurable.ite hN_meas measurable_const (hY₀_meas t), hY_cont,
    fun ω ↦ ?_, fun T γ hγ ω ↦ ?_, hY_ae⟩
  · by_cases hω : ω ∈ N
    · simp [Y, hω]
    · simpa [Y, hω] using (not_not.1 fun h ↦ hω (hN_sub h)).1
  · by_cases hω : ω ∈ N
    · exact ⟨0, fun _ _ _ _ ↦ by simp [Y, hω]⟩
    · obtain ⟨L, hL⟩ := (not_not.1 fun h ↦ hω (hN_sub h)).2 T hγ
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
  have hΦ : AEMeasurable Φ P := ContinuousMap.aemeasurable_iff_eval.2 hB.aemeasurable
  refine ⟨(Measure.isProbabilityMeasure_map_iff hΦ).2 inferInstance,
    ⟨⟨fun I ↦ ⟨(ContinuousMap.measurable_finsetRestrict I).aemeasurable, ?_⟩⟩,
      Eventually.of_forall fun ω ↦ ω.continuous⟩⟩
  rw [AEMeasurable.map_map_of_aemeasurable
    (ContinuousMap.measurable_finsetRestrict I).aemeasurable hΦ]
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
  have : IsProbabilityMeasure W₂ := hW₂.isGaussianProcess.isProbabilityMeasure
  exact continuousMap_measure_ext_of_forall_finset_map_restrict_eq fun I ↦
    (hW₁.hasLaw I).map_eq.trans (hW₂.hasLaw I).map_eq.symm

/-- **Wiener measure on continuous paths** (Lalley, Theorem 1): there exists a probability measure
`W` on `C(ℝ≥0, ℝ)` whose coordinate evaluation process satisfies `IsBrownianReal`. -/
theorem exists_wienerMeasure :
    ∃ W : Measure C(ℝ≥0, ℝ), IsProbabilityMeasure W ∧
      IsBrownianReal (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t) W := by
  obtain ⟨D, hD_count, hD_dense⟩ := exists_countable_dense ℝ≥0
  have : Countable D := hD_count.to_subtype
  obtain ⟨P, -, hP_proj, hP_kol⟩ :=
    exists_measurePreserving_brownianRealProjectiveFamily_isKolmogorovProcess_of_countable D
  have hkol4 := hP_kol (by decide : (2 : ℕ) ≠ 0)
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
