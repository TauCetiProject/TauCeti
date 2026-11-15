/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Process.Indistinguishable
public import Mathlib.Probability.Process.Kolmogorov
public import Mathlib.Topology.MetricSpace.Holder

import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import TauCeti.MeasureTheory.Measure.ContinuousMap
import TauCeti.Probability.BrownianMotion.Countable
import TauCeti.Probability.Process.Indistinguishable
import TauCeti.Probability.Process.Kolmogorov
import TauCeti.Probability.Process.Kolmogorov.Continuity
import TauCeti.Topology.MetricSpace.CoveringNumbers
import TauCeti.Topology.MetricSpace.Holder

/-!
# Continuous modifications of pre-Brownian motion and Wiener measure

Every pre-Brownian motion (`ProbabilityTheory.IsPreBrownianReal`) satisfies the Kolmogorov moment
bounds of all positive even orders and therefore admits a modification with everywhere continuous,
locally `γ`-Hölder sample paths for every `γ < 1 / 2` (`ProbabilityTheory.IsPreBrownianReal.mk`).
Consequently, every Brownian motion (`ProbabilityTheory.IsBrownianReal`) has almost-surely locally
`γ`-Hölder sample paths for every `γ < 1 / 2`.

Combining a Gaussian skeleton on a countable dense subset of `ℝ≥0` with the Kolmogorov–Chentsov
theorem constructs **Wiener measure** `TauCeti.wienerMeasure : Measure C(ℝ≥0, ℝ)`, the unique Borel
measure on continuous path space `C(ℝ≥0, ℝ)` under which coordinate evaluation is a real Brownian
motion.

## Main definitions

* `ProbabilityTheory.IsPreBrownianReal.mk`: canonical everywhere-continuous modification of a
  pre-Brownian motion.
* `TauCeti.wienerMeasure`: Wiener measure on `C(ℝ≥0, ℝ)`.

## Main results

* `ProbabilityTheory.IsPreBrownianReal.isAEKolmogorovProcess`: every pre-Brownian motion satisfies
  `IsAEKolmogorovProcess X P (2 * n) n (2 * n - 1)‼` for all `n ≠ 0`.
* `ProbabilityTheory.IsPreBrownianReal.exists_holderOnWith_Icc_modification`: every pre-Brownian
  motion admits a modification that is a Brownian motion with everywhere continuous paths that are
  `γ`-Hölder on `[0, R]` for all `R` (when `0 < γ < 1 / 2`).
* `ProbabilityTheory.IsBrownianReal.ae_holderOnWith_Icc`: sample paths of any Brownian motion are
  almost surely `γ`-Hölder on `[0, R]` for every `γ < 1 / 2`.
* `TauCeti.exists_wienerMeasure`: existence of a probability measure `W` on `C(ℝ≥0, ℝ)` under which
  coordinate evaluation `(fun t ω => ω t)` satisfies `IsBrownianReal`.
* `TauCeti.eq_wienerMeasure_of_isPreBrownianReal_eval` and `TauCeti.existsUnique_wienerMeasure`:
  uniqueness of Wiener measure on `C(ℝ≥0, ℝ)`.

## References

* Ioannis Karatzas and Steven E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §2.2 and §2.4.
* Olav Kallenberg, *Foundations of Modern Probability*, third edition, Springer, 2021, Theorem 14.2.
-/

public section

open Filter MeasureTheory Metric Set TopologicalSpace WithLp
open scoped ENNReal NNReal Nat RealInnerProductSpace Topology

namespace ProbabilityTheory

section Modification

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B X : ℝ≥0 → Ω → ℝ}

/-- Every pre-Brownian motion satisfies the positive even-moment Kolmogorov condition up to
coordinatewise modification, with exponents `2 * n` and `n` and constant `(2 * n - 1)‼`. -/
theorem IsPreBrownianReal.isAEKolmogorovProcess (hX : IsPreBrownianReal X P) {n : ℕ} (hn : n ≠ 0) :
    IsAEKolmogorovProcess X P (2 * n : ℕ) n (2 * n - 1)‼ := by
  let Y : ℝ≥0 → Ω → ℝ := fun t ↦ (hX.aemeasurable t).mk (X t)
  have hXY (t : ℝ≥0) : X t =ᵐ[P] Y t := (hX.aemeasurable t).ae_eq_mk
  have hY : IsPreBrownianReal Y P := hX.congr hXY
  refine ⟨Y, isKolmogorovProcess_of_hasLaw_sub_gaussianReal
    (fun t ↦ (hX.aemeasurable t).measurable_mk) (fun s t ↦ ?_) hn, hXY⟩
  exact hY.hasLaw_sub s t

/-- Every pre-Brownian motion admits a modification with measurable coordinates and everywhere
continuous sample paths that are `γ`-Hölder on `[0, R]` for every `R : ℝ≥0`, for any
`0 < γ < 1 / 2`. -/
theorem IsPreBrownianReal.exists_holderOnWith_Icc_modification (hX : IsPreBrownianReal X P)
    {γ : ℝ≥0} (hγ₀ : 0 < γ) (hγ : (γ : ℝ) < 1 / 2) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      IsBrownianReal Y P ∧
      (∀ t, Measurable (Y t)) ∧
      (∀ ω, Continuous (Y · ω)) ∧
      (∀ ω (R : ℝ≥0), ∃ K : ℝ≥0, HolderOnWith K γ (Y · ω) (Icc 0 R)) ∧
      ∀ t, Y t =ᵐ[P] X t := by
  have hsub_pos : 0 < 1 - 2 * (γ : ℝ) := by linarith
  let n : ℕ := ⌊(1 - 2 * (γ : ℝ))⁻¹⌋₊ + 1
  have hn : n ≠ 0 := Nat.succ_ne_zero _
  have hγ_kol : 1 + ((2 * n : ℕ) : ℝ) * (γ : ℝ) < (n : ℝ) := by
    have hlt : (1 - 2 * (γ : ℝ))⁻¹ < (n : ℝ) := by
      simpa [n] using Nat.lt_floor_add_one (1 - 2 * (γ : ℝ))⁻¹
    have hmul : 1 < (n : ℝ) * (1 - 2 * (γ : ℝ)) := (inv_lt_iff_one_lt_mul₀ hsub_pos).mp hlt
    push_cast
    linarith
  obtain ⟨Y, hY_kol, hY_cont, hY_hold, hY_mod⟩ :=
    (hX.isAEKolmogorovProcess hn).exists_modification_holderOnWith_Icc_nnreal hγ₀ hγ_kol
  exact ⟨Y, ⟨hX.congr fun t ↦ (hY_mod t).symm, Eventually.of_forall hY_cont⟩,
    fun t ↦ hY_kol.measurable t, hY_cont, hY_hold, hY_mod⟩

private theorem IsPreBrownianReal.exists_mk (hX : IsPreBrownianReal X P) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      IsBrownianReal Y P ∧
      (∀ t, Measurable (Y t)) ∧
      (∀ ω, Continuous (Y · ω)) ∧
      (∀ ω (R : ℝ≥0), ∃ K : ℝ≥0, HolderOnWith K (1 / 4) (Y · ω) (Icc 0 R)) ∧
      ∀ t, Y t =ᵐ[P] X t :=
  hX.exists_holderOnWith_Icc_modification (γ := 1 / 4) (by norm_num) (by push_cast; norm_num)

/-- A canonical everywhere-continuous modification of a pre-Brownian motion `X`, obtained by
applying `IsPreBrownianReal.exists_holderOnWith_Icc_modification` at Hölder exponent `1 / 4`. -/
protected noncomputable def IsPreBrownianReal.mk (X : ℝ≥0 → Ω → ℝ)
    (hX : IsPreBrownianReal X P) : ℝ≥0 → Ω → ℝ :=
  hX.exists_mk.choose

/-- Every sample path of `hX.mk X` is continuous on `ℝ≥0`. -/
theorem IsPreBrownianReal.continuous_mk (hX : IsPreBrownianReal X P) (ω : Ω) :
    Continuous (hX.mk X · ω) :=
  hX.exists_mk.choose_spec.2.2.1 ω

/-- Each coordinate of `hX.mk X` is measurable. -/
theorem IsPreBrownianReal.measurable_mk (hX : IsPreBrownianReal X P) (t : ℝ≥0) :
    Measurable (hX.mk X t) :=
  hX.exists_mk.choose_spec.2.1 t

/-- The canonical continuous modification `hX.mk X` of a pre-Brownian motion is a Brownian
motion. -/
theorem IsPreBrownianReal.isBrownianReal_mk (hX : IsPreBrownianReal X P) :
    IsBrownianReal (hX.mk X) P :=
  hX.exists_mk.choose_spec.1

/-- `hX.mk X` is a modification of `X`. -/
theorem IsPreBrownianReal.ae_eq_mk (hX : IsPreBrownianReal X P) (t : ℝ≥0) :
    X t =ᵐ[P] hX.mk X t :=
  (hX.exists_mk.choose_spec.2.2.2.2 t).symm

/-- A process indistinguishable from a Brownian motion is itself a Brownian motion. -/
theorem IsBrownianReal.congr (hB : IsBrownianReal B P) (h : B ≡ᵐ[P] X) :
    IsBrownianReal X P where
  toIsPreBrownianReal := hB.toIsPreBrownianReal.congr fun t ↦ h.ae_eq_eval t
  cont := by
    filter_upwards [hB.cont, h] with ω hc heq
    exact hc.congr heq

/-- Sample paths of a Brownian motion are almost surely `γ`-Hölder on `[0, R]` for every `R : ℝ≥0`
and every `γ < 1 / 2`. -/
theorem IsBrownianReal.ae_holderOnWith_Icc (hB : IsBrownianReal B P) (R : ℝ≥0)
    {γ : ℝ≥0} (hγ : (γ : ℝ) < 1 / 2) :
    ∀ᵐ ω ∂P, ∃ K : ℝ≥0, HolderOnWith K γ (B · ω) (Icc 0 R) := by
  rcases eq_or_lt_of_le (zero_le : 0 ≤ γ) with rfl | hγ₀
  · obtain ⟨Y, hY, -, -, hY_hold, hY_mod⟩ := hB.toIsPreBrownianReal.exists_mk
    filter_upwards [indist_of_ae_continuous hY.cont hB.cont hY_mod] with ω hω
    obtain ⟨K, hK⟩ := hY_hold ω R
    refine ⟨K * R ^ (1 / 4 : ℝ), fun s hs t ht ↦ ?_⟩
    have heq_s : B s ω = Y s ω := (hω s).symm
    have heq_t : B t ω = Y t ω := (hω t).symm
    dsimp only
    rw [heq_s, heq_t]
    have hed : edist s t ≤ R := by
      rw [edist_nndist, NNReal.nndist_eq]
      exact_mod_cast max_le (tsub_le_self.trans hs.2) (tsub_le_self.trans ht.2)
    have h14 : ((1 / 4 : ℝ≥0) : ℝ) = 1 / 4 := by push_cast; norm_num
    calc edist (Y s ω) (Y t ω)
        ≤ K * edist s t ^ ((1 / 4 : ℝ≥0) : ℝ) := hK s hs t ht
      _ = K * edist s t ^ (1 / 4 : ℝ) := by rw [h14]
      _ ≤ K * (R : ℝ≥0∞) ^ (1 / 4 : ℝ) := by gcongr
      _ = ((K * R ^ (1 / 4 : ℝ) : ℝ≥0) : ℝ≥0∞) * edist s t ^ ((0 : ℝ≥0) : ℝ) := by
          rw [ENNReal.coe_mul, ← ENNReal.coe_rpow_of_nonneg _ (by positivity)]
          simp
  · obtain ⟨Y, hY, -, -, hY_hold, hY_mod⟩ :=
      hB.toIsPreBrownianReal.exists_holderOnWith_Icc_modification hγ₀ hγ
    filter_upwards [indist_of_ae_continuous hY.cont hB.cont hY_mod] with ω hω
    obtain ⟨K, hK⟩ := hY_hold ω R
    refine ⟨K, fun s hs t ht ↦ ?_⟩
    dsimp only
    rw [← hω s, ← hω t]
    exact hK s hs t ht

end Modification

end ProbabilityTheory

namespace TauCeti

open ProbabilityTheory

/-- If a real process `B` on `ℝ≥0` has measurable coordinates, everywhere continuous sample paths,
and the Brownian finite-dimensional Gaussian laws along a dense set `D ⊆ ℝ≥0`, then `B` is a
Brownian motion. -/
private theorem isBrownianReal_of_dense_hasLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {D : Set ℝ≥0} (hDd : Dense D) {B : ℝ≥0 → Ω → ℝ}
    (hB_meas : ∀ t, Measurable (B t)) (hB_cont : ∀ ω, Continuous (B · ω))
    (hD_law : ∀ I : Finset ℝ≥0, (I : Set ℝ≥0) ⊆ D →
      HasLaw (fun ω (i : I) ↦ B i.1 ω) (BrownianReal.projectiveFamily I) P) :
    IsBrownianReal B P where
  cont := Eventually.of_forall hB_cont
  hasLaw I := by
    classical
    have hrest_meas : Measurable (fun ω ↦ I.restrict (B · ω)) :=
      measurable_pi_iff.mpr fun i ↦ hB_meas i.1
    refine ⟨hrest_meas.aemeasurable, ?_⟩
    apply (MeasurableEquiv.toLp 2 (I → ℝ)).map_measurableEquiv_injective
    rw [MeasurableEquiv.coe_toLp, (BrownianReal.measurePreserving_toLp_projectiveFamily I).map_eq,
      Measure.map_map (by fun_prop) hrest_meas]
    let Z : Ω → EuclideanSpace ℝ I := fun ω ↦ toLp 2 (fun i : I ↦ B i.1 ω)
    change P.map Z = multivariateGaussian 0 (BrownianReal.covMatrix I)
    have hZ_meas : Measurable Z :=
      (MeasurableEquiv.toLp 2 (I → ℝ)).measurable.comp hrest_meas
    apply Measure.ext_of_charFun (E := EuclideanSpace ℝ I)
    ext x
    have hex (i : I) : ∃ u : ℕ → D, Tendsto (fun k ↦ (u k).1) atTop (𝓝 i.1) := by
      obtain ⟨u, hu_mem, hu_lim⟩ := mem_closure_iff_seq_limit.mp (hDd i.1)
      exact ⟨fun k ↦ ⟨u k, hu_mem k⟩, hu_lim⟩
    choose u hu using hex
    let Z_seq (k : ℕ) : Ω → EuclideanSpace ℝ I := fun ω ↦ toLp 2 (fun i : I ↦ B (u i k).1 ω)
    have hZk_meas (k : ℕ) : Measurable (Z_seq k) :=
      (MeasurableEquiv.toLp 2 (I → ℝ)).measurable.comp
        (measurable_pi_iff.mpr fun i ↦ hB_meas (u i k).1)
    have hlim_dist : Tendsto (fun k ↦ charFun (P.map (Z_seq k)) x) atTop
        (𝓝 (charFun (P.map Z) x)) := by
      refine (tendstoInDistribution_of_ae_tendsto (fun k ↦ (hZk_meas k).aemeasurable)
        hZ_meas.aemeasurable ?_).tendsto_charFun x
      refine Eventually.of_forall fun ω ↦ ?_
      exact (PiLp.continuous_toLp 2 fun _ : I ↦ ℝ).tendsto _ |>.comp
        (tendsto_pi_nhds.mpr fun i ↦ ((hB_cont ω).tendsto i.1).comp (hu i))
    have hBD_gauss : IsGaussianProcess (fun d : D ↦ B d.1) P :=
      isGaussianProcess_of_hasLaw_brownianRealProjectiveFamily (X := fun d : D ↦ B d.1) hD_law
    have hZk_gauss (k : ℕ) : HasGaussianLaw (Z_seq k) P := by
      let J : Finset ℝ≥0 := Finset.univ.image fun i : I ↦ (u i k).1
      have hJ : (J : Set ℝ≥0) ⊆ D := by
        intro t ht
        rcases Finset.mem_image.mp ht with ⟨i, -, rfl⟩
        exact (u i k).2
      let L : (J → ℝ) →L[ℝ] EuclideanSpace ℝ I :=
        (PiLp.continuousLinearEquiv 2 ℝ fun _ : I ↦ ℝ).symm.toContinuousLinearMap.comp
          (ContinuousLinearMap.pi fun i : I ↦ ContinuousLinearMap.proj (R := ℝ)
            ⟨(u i k).1, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩)
      convert (hD_law J hJ).hasGaussianLaw.map L using 1
      ext ω i
      rfl
    have hchar_k (k : ℕ) : charFun (P.map (Z_seq k)) x =
        Complex.exp (-((∑ i : I, ∑ j : I,
          x i * x j * min ((u i k).1 : ℝ) ((u j k).1 : ℝ) : ℝ) : ℂ) / 2) := by
      have : IsGaussian (P.map (Z_seq k)) := (hZk_gauss k).isGaussian_map
      rw [IsGaussian.charFun_eq']
      have hmean : ∫ z, z ∂P.map (Z_seq k) = 0 := by
        rw [integral_map (hZk_meas k).aemeasurable (by fun_prop)]
        ext i
        rw [PiLp.zero_apply, eval_integral_piLp
          (fun j ↦ (hBD_gauss.hasGaussianLaw_eval (u j k)).integrable) i]
        have hlaw_d := hasLaw_gaussianReal_of_hasLaw_brownianRealProjectiveFamily
          (X := fun d : D ↦ B d.1) hD_law (u i k)
        simpa [Z_seq] using hlaw_d.integral_eq.trans integral_id_gaussianReal
      have hcov : covarianceBilin (P.map (Z_seq k)) x x =
          ∑ i : I, ∑ j : I, x i * x j * min ((u i k).1 : ℝ) ((u j k).1 : ℝ) := by
        rw [covarianceBilin_apply_pi (X := fun i : I ↦ B (u i k).1)
          fun i ↦ (hBD_gauss.hasGaussianLaw_eval (u i k)).memLp_two]
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
        have hcov_ij := covariance_eq_min_of_hasLaw_brownianRealProjectiveFamily
          (X := fun d : D ↦ B d.1) hD_law (u i k) (u j k)
        exact congrArg ((x i * x j) * ·) hcov_ij
      simp [hmean, hcov, neg_div]
    have hchar_target : charFun (multivariateGaussian 0 (BrownianReal.covMatrix I)) x =
        Complex.exp (-((∑ i : I, ∑ j : I, x i * x j * min (i.1 : ℝ) (j.1 : ℝ) : ℝ) : ℂ) / 2) := by
      rw [charFun_multivariateGaussian (BrownianReal.posSemidef_covMatrix I) x]
      simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub, neg_div]
      congr 3
      norm_cast
      simp only [dotProduct, Matrix.mulVec, BrownianReal.covMatrix_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      ring
    have hlim_gauss : Tendsto (fun k ↦ charFun (P.map (Z_seq k)) x) atTop
        (𝓝 (charFun (multivariateGaussian 0 (BrownianReal.covMatrix I)) x)) := by
      simp_rw [hchar_k, hchar_target]
      have hsum_lim : Tendsto (fun k ↦ ∑ i : I, ∑ j : I,
          x i * x j * min ((u i k).1 : ℝ) ((u j k).1 : ℝ)) atTop
          (𝓝 (∑ i : I, ∑ j : I, x i * x j * min (i.1 : ℝ) (j.1 : ℝ))) :=
        tendsto_finsetSum _ fun i _ ↦ tendsto_finsetSum _ fun j _ ↦
          tendsto_const_nhds.mul <|
            (NNReal.continuous_coe.tendsto _ |>.comp (hu i)).min
              (NNReal.continuous_coe.tendsto _ |>.comp (hu j))
      exact (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.neg).div_const 2)).tendsto _ |>.comp hsum_lim
    exact tendsto_nhds_unique hlim_dist hlim_gauss

/-- **Existence of Wiener measure.** There exists a Borel probability measure `W` on continuous
path space `C(ℝ≥0, ℝ)` under which coordinate evaluation `(fun t ω => ω t)` is a real Brownian
motion. -/
theorem exists_wienerMeasure :
    ∃ W : Measure C(ℝ≥0, ℝ), IsProbabilityMeasure W ∧
      IsBrownianReal (fun t (ω : C(ℝ≥0, ℝ)) => ω t) W := by
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense ℝ≥0
  have : Countable D := hDc.to_subtype
  obtain ⟨P, hP_prob, hP_mp, hP_kol⟩ :=
    exists_measurePreserving_brownianRealProjectiveFamily_isKolmogorovProcess_of_countable D
  let U (m : ℕ) : Set D := {d : D | d.1 < (m : ℝ≥0) + 1}
  have hU_mono : Monotone U := fun m n hmn d hd ↦
    lt_of_lt_of_le hd (add_le_add_left (Nat.cast_le.mpr hmn) 1)
  have hU_open (m : ℕ) : IsOpen (U m) := isOpen_Iio.preimage continuous_subtype_val
  have hU_cov : ⋃ m, U m = univ := eq_univ_of_forall fun d ↦
    mem_iUnion.mpr ⟨⌊d.1⌋₊, Nat.lt_floor_add_one d.1⟩
  have hU_hasCov (m : ℕ) :
      HasCoveringExponent (U m) (2 ^ (1 : ℝ) * (4 * (((m : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞))) 1 := by
    rw [← Isometry.hasCoveringExponent_image_iff (f := (Subtype.val : D → ℝ≥0)) (fun _ _ ↦ rfl)]
    exact (hasCoveringExponent_Iio_nnreal ((m : ℝ≥0) + 1)).subset
      (image_preimage_subset Subtype.val (Iio ((m : ℝ≥0) + 1))) zero_le_one
  have hc (m : ℕ) : (2 : ℝ≥0∞) ^ (1 : ℝ) * (4 * (((m : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞)) ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top)
  have hkol4 : IsKolmogorovProcess (fun (t : D) (ω : D → ℝ) ↦ ω t) P 4 2 3 := by
    simpa using hP_kol (n := 2) (by decide)
  obtain ⟨Y, hY_kol, hY_cont, hY_hold, hY_mod⟩ :=
    hkol4.IsAEKolmogorovProcess.exists_modification_holderOnWith_of_isOpen_cover
      hU_mono hU_open hU_cov hc zero_le_one hU_hasCov (γ := 1 / 8) (by norm_num)
      (by push_cast; norm_num)
  let di := hDd.isDenseInducing_val
  let B (t : ℝ≥0) (ω : D → ℝ) : ℝ := di.extend (Y · ω) t
  have hB_on_D (d : D) (ω : D → ℝ) : B d.1 ω = Y d ω :=
    di.extend_eq (hY_cont ω) d
  have hB_cont (ω : D → ℝ) : Continuous (B · ω) := by
    classical
    rw [continuous_iff_continuousAt]
    intro t
    let m : ℕ := ⌊t⌋₊
    let V : Set ℝ≥0 := Iio ((m : ℝ≥0) + 1)
    have htV : t ∈ V := Nat.lt_floor_add_one t
    let S : Set V := ((↑) : V → ℝ≥0) ⁻¹' D
    have hS_dense : Dense S := hDd.preimage isOpen_Iio.isOpenMap_subtype_val
    obtain ⟨K, hK⟩ := hY_hold ω m
    let f₀ : V → ℝ := fun v ↦ if hv : v.1 ∈ D then Y ⟨v.1, hv⟩ ω else 0
    have hf₀_hold : HolderOnWith K (1 / 8) f₀ S := by
      intro a ha b hb
      have haD : a.1 ∈ D := ha
      have hbD : b.1 ∈ D := hb
      simp only [f₀, haD, hbD, ↓reduceDIte]
      exact hK ⟨a.1, haD⟩ a.2 ⟨b.1, hbD⟩ b.2
    obtain ⟨g, hg_hold, hg_eq⟩ := hf₀_hold.extend_of_dense hS_dense
    have hg_cont : Continuous g := hg_hold.continuous (by norm_num)
    let g_ext : ℝ≥0 → ℝ := fun s ↦ if hs : s ∈ V then g ⟨s, hs⟩ else 0
    have hg_ext_contAt (s : ℝ≥0) (hs : s ∈ V) : ContinuousAt g_ext s := by
      refine ContinuousOn.continuousAt ?_ (isOpen_Iio.mem_nhds hs)
      rw [continuousOn_iff_continuous_domRestrict]
      have hdom : V.domRestrict g_ext = g := by
        ext ⟨u, hu⟩
        simp [Set.domRestrict, g_ext, hu]
      rwa [hdom]
    have hB_eq_V (s : ℝ≥0) (hs : s ∈ V) : B s ω = g_ext s := by
      refine di.extend_unique_at ?_ (hg_ext_contAt s hs)
      filter_upwards [preimage_mem_comap (isOpen_Iio.mem_nhds hs)] with d hd
      have hdV : d.1 ∈ V := hd
      have hgd : g ⟨d.1, hdV⟩ = f₀ ⟨d.1, hdV⟩ := (hg_eq d.2).symm
      simp [g_ext, hdV, hgd, f₀, d.2]
    exact (hg_ext_contAt t htV).congr_of_eventuallyEq
      (eventually_of_mem (isOpen_Iio.mem_nhds htV) fun s hs ↦ hB_eq_V s hs)
  have hB_meas (t : ℝ≥0) : Measurable (B t) := by
    obtain ⟨u, hu_mem, hu_lim⟩ := mem_closure_iff_seq_limit.mp (hDd t)
    refine measurable_of_tendsto_metrizable (f := fun k ω ↦ B (u k) ω)
      (fun k ↦ ?_) (tendsto_pi_nhds.mpr fun ω ↦ ((hB_cont ω).tendsto t).comp hu_lim)
    have hfun : (fun ω ↦ B (u k) ω) = Y ⟨u k, hu_mem k⟩ := funext (hB_on_D ⟨u k, hu_mem k⟩)
    rw [hfun]
    exact hY_kol.measurable ⟨u k, hu_mem k⟩
  have hD_law (I : Finset ℝ≥0) (hI : (I : Set ℝ≥0) ⊆ D) :
      HasLaw (fun ω (i : I) ↦ B i.1 ω) (BrownianReal.projectiveFamily I) P := by
    refine (hP_mp I hI).hasLaw.congr ?_
    have hae : ∀ᵐ ω ∂P, ∀ i : I, B i.1 ω = ω ⟨i.1, hI i.2⟩ := by
      refine ae_all_iff.mpr fun i ↦ ?_
      filter_upwards [hY_mod ⟨i.1, hI i.2⟩] with ω hω
      exact (hB_on_D ⟨i.1, hI i.2⟩ ω).trans hω
    filter_upwards [hae] with ω hω using funext hω
  have hB_bm : IsBrownianReal B P := isBrownianReal_of_dense_hasLaw hDd hB_meas hB_cont hD_law
  let Φ : (D → ℝ) → C(ℝ≥0, ℝ) := fun ω ↦ ⟨fun t ↦ B t ω, hB_cont ω⟩
  have hΦ_meas : Measurable Φ := ContinuousMap.measurable_iff_eval.mpr hB_meas
  let W : Measure C(ℝ≥0, ℝ) := P.map Φ
  refine ⟨W, inferInstance, ⟨⟨fun I ↦ ?_⟩, Eventually.of_forall fun ω ↦ ω.continuous⟩⟩
  refine ⟨(ContinuousMap.measurable_finsetRestrict I).aemeasurable, ?_⟩
  rw [Measure.map_map (ContinuousMap.measurable_finsetRestrict I) hΦ_meas]
  exact (hB_bm.hasLaw I).map_eq

/-- **Wiener measure** on continuous path space `C(ℝ≥0, ℝ)`, the probability law of a real Brownian
motion realized as a random continuous path. -/
noncomputable def wienerMeasure : Measure C(ℝ≥0, ℝ) :=
  exists_wienerMeasure.choose

instance instIsProbabilityMeasureWienerMeasure : IsProbabilityMeasure wienerMeasure :=
  exists_wienerMeasure.choose_spec.1

/-- Coordinate evaluation `(fun t ω => ω t)` on `C(ℝ≥0, ℝ)` is a real Brownian motion under
`wienerMeasure`. -/
theorem isBrownianReal_eval_wienerMeasure :
    IsBrownianReal (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t) wienerMeasure :=
  exists_wienerMeasure.choose_spec.2

/-- Restriction of a continuous path to any finite set of times `I : Finset ℝ≥0` has law
`BrownianReal.projectiveFamily I` under `wienerMeasure`. -/
theorem hasLaw_restrict_wienerMeasure (I : Finset ℝ≥0) :
    HasLaw (fun ω : C(ℝ≥0, ℝ) ↦ I.restrict (ω : ℝ≥0 → ℝ))
      (BrownianReal.projectiveFamily I) wienerMeasure :=
  isBrownianReal_eval_wienerMeasure.hasLaw I

/-- Coordinate evaluation at time `t : ℝ≥0` has law `gaussianReal 0 t` under `wienerMeasure`. -/
theorem hasLaw_eval_wienerMeasure (t : ℝ≥0) :
    HasLaw (fun ω : C(ℝ≥0, ℝ) ↦ ω t) (gaussianReal 0 t) wienerMeasure :=
  isBrownianReal_eval_wienerMeasure.hasLaw_eval t

/-- Almost every path under `wienerMeasure` starts at `0` at time `0`. -/
theorem ae_eval_zero_wienerMeasure :
    ∀ᵐ ω ∂wienerMeasure, ω 0 = 0 :=
  isBrownianReal_eval_wienerMeasure.eval_zero_ae_eq_zero

/-- **Uniqueness of Wiener measure.** Any Borel measure `μ` on `C(ℝ≥0, ℝ)` under which coordinate
evaluation is a pre-Brownian motion equals `wienerMeasure`. -/
theorem eq_wienerMeasure_of_isPreBrownianReal_eval {μ : Measure C(ℝ≥0, ℝ)}
    (hμ : IsPreBrownianReal (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t) μ) :
    μ = wienerMeasure :=
  continuousMap_measure_ext_of_forall_finset_map_restrict_eq fun I ↦
    (hμ.hasLaw I).map_eq.trans (hasLaw_restrict_wienerMeasure I).map_eq.symm

/-- `wienerMeasure` is the unique Borel measure on `C(ℝ≥0, ℝ)` under which coordinate evaluation is
a real Brownian motion. -/
theorem existsUnique_wienerMeasure :
    ∃! W : Measure C(ℝ≥0, ℝ), IsBrownianReal (fun t (ω : C(ℝ≥0, ℝ)) ↦ ω t) W :=
  ⟨wienerMeasure, isBrownianReal_eval_wienerMeasure,
    fun _ hW ↦ eq_wienerMeasure_of_isPreBrownianReal_eval hW.toIsPreBrownianReal⟩

end TauCeti
