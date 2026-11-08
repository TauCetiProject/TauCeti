/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.Dual
public import TauCeti.NumberTheory.Padics.Distribution.Amice.Isometry
public import TauCeti.NumberTheory.Padics.Distribution.Amice.Norm
public import TauCeti.NumberTheory.Padics.Distribution.Amice.Transition

/-!
# The Amice transform of locally analytic distributions

The Amice transform sends a locally analytic distribution `μ` to the formal series whose
`n`-th coefficient is `μ (x ↦ (x choose n))`. Amice's isometry identifies its restriction to
level `h` with the bounded family `⌊n / pʰ⌋! * μ (x ↦ (x choose n))`. Thus its stage norm is
`TauCeti.amiceDualNorm p h`, and the transform identifies distributions with the native
`PowerSeries.OnOpenDisc.subring K 1` of series converging on the open unit disc.

The inverse constructs a bounded functional at each stage from the weighted coefficients.
These functionals agree under re-expansion, so descend to the algebraic direct limit. No
topology on the space of distributions is introduced. On continuous measures the transform
agrees with Mathlib's `AbstractMeasure.amiceTransform`.

## References

* Y. Amice, *Interpolation p-adique*, Bull. Soc. Math. France 92 (1964), 117–180.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §II.2.
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §3,
  Theorem 3.43.
-/

public section

open scoped ZeroAtInfty
open ZeroAtInftyContinuousMap

namespace TauCeti

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [NontriviallyNormedField K]
  [NormedAlgebra ℚ_[p] K] [Algebra ℤ_[p] K] [IsBoundedSMul ℤ_[p] K]
  [IsUltrametricDist K] [CompleteSpace K]

namespace LocallyAnalytic

variable (p K) in
/-- The binomial polynomial `x ↦ (x choose n)` as a locally analytic function, represented
at level zero by the normalised Amice polynomial. -/
noncomputable def mahler (n : ℕ) : LocallyAnalytic p K K :=
  (n.factorial : K)⁻¹ • ofStage K 0 (AnalyticStage.amiceTerm p 0 n (1 : K))

/-- Evaluation of the locally analytic binomial polynomial is the usual Mahler function. -/
@[simp]
theorem eval_mahler (n : ℕ) :
    eval K (mahler p K n) = PadicInt.mahlerTerm (1 : K) n := by
  let : CharZero K := Algebra.charZero_of_charZero ℚ_[p] K
  simp only [mahler, map_smul, eval_ofStage, AnalyticStage.eval_amiceTerm,
    pow_zero, Nat.div_one, ← Nat.cast_smul_eq_nsmul K]
  simp [PadicInt.mahlerTerm_eq_smul, smul_smul, Nat.factorial_ne_zero]

/-- At any level the Amice polynomial represents the factorial multiple of the binomial
polynomial in the algebraic direct limit. -/
theorem ofStage_amiceTerm (h n : ℕ) :
    ofStage K h (AnalyticStage.amiceTerm p h n (1 : K)) =
      ((n / p ^ h).factorial : K) • mahler p K n := by
  let : CharZero K := Algebra.charZero_of_charZero ℚ_[p] K
  have hreg : IsSMulRegular K (p : ℤ_[p]) := by
    intro x y hxy
    have hxy' : (p : K) * x = (p : K) * y := by
      simpa only [Nat.cast_smul_eq_nsmul, nsmul_eq_mul] using hxy
    exact mul_left_cancel₀ (by exact_mod_cast hp.out.ne_zero : (p : K) ≠ 0) hxy'
  apply eval_injective K hreg
  simp only [eval_ofStage, AnalyticStage.eval_amiceTerm, map_smul, eval_mahler,
    ← Nat.cast_smul_eq_nsmul K]
  simp [PadicInt.mahlerTerm_eq_smul]

end LocallyAnalytic

namespace LocallyAnalyticDistribution

open AnalyticStage

/-- The Amice transform of a locally analytic distribution: its coefficients are its values
on the binomial polynomials. -/
noncomputable def amiceTransform : LocallyAnalyticDistribution p K →ₗ[K] PowerSeries K where
  toFun μ := PowerSeries.mk fun n ↦ (μ : Module.Dual K _) (LocallyAnalytic.mahler p K n)
  map_add' μ ν := by ext n; simp
  map_smul' a μ := by ext n; simp

omit [NormedAlgebra ℚ_[p] K] in
/-- The coefficients of the Amice transform are the binomial moments. -/
@[simp]
theorem coeff_amiceTransform (μ : LocallyAnalyticDistribution p K) (n : ℕ) :
    (amiceTransform μ).coeff n = (μ : Module.Dual K _) (LocallyAnalytic.mahler p K n) := by
  simp [amiceTransform]

/-- The values of a stage functional on Amice's basis are its factorial-weighted moments. -/
theorem stage_amiceTerm (μ : LocallyAnalyticDistribution p K) (h n : ℕ) :
    stage h μ (amiceTerm p h n (1 : K)) =
      ((n / p ^ h).factorial : K) * (amiceTransform μ).coeff n := by
  rw [stage_apply, LocallyAnalytic.ofStage_amiceTerm, map_smul, coeff_amiceTransform, smul_eq_mul]

/-- The Amice transform determines the distribution, since Amice polynomials span each stage
densely. -/
theorem amiceTransform_injective :
    Function.Injective (amiceTransform (p := p) (K := K)) := by
  intro μ ν hμν
  apply ext
  intro h
  apply continuousLinearMap_ext_amiceTerm
  intro n
  simp only [stage_amiceTerm, hμν]

/-- A distribution evaluates an analytic-stage vector by pairing its Amice coordinates with
the factorial-weighted moments. The sum is unconditional. -/
theorem hasSum_amiceEquiv_symm_mul_coeff_amiceTransform
    (μ : LocallyAnalyticDistribution p K) {h : ℕ} (c : AnalyticStage p h K) :
    HasSum (fun n ↦ (amiceEquiv p h K).symm c n *
      (((n / p ^ h).factorial : K) * (amiceTransform μ).coeff n)) (stage h μ c) := by
  convert ((hasSum_amiceMap K ((amiceEquiv p h K).symm c)).mapL (stage h μ)) using 1
  · ext n
    rw [← stage_amiceTerm, ← smul_eq_mul, ← map_smul, ← amiceTerm_smul]
    simp
  · simp only [← amiceEquiv_apply, LinearIsometryEquiv.apply_symm_apply]

/-- The weighted moments at every level are bounded by the stage operator norm. -/
theorem norm_factorial_mul_coeff_amiceTransform_le (μ : LocallyAnalyticDistribution p K)
    (h n : ℕ) :
    ‖((n / p ^ h).factorial : K) * (amiceTransform μ).coeff n‖ ≤ ‖stage h μ‖ := by
  rw [← stage_amiceTerm]
  exact ((stage h μ).le_opNorm _).trans <| by
    simpa using mul_le_mul_of_nonneg_left
      (norm_amiceTerm_le n (1 : K)) (norm_nonneg (stage h μ))

/-- The Amice transform of a distribution converges on the open unit disc. -/
theorem onOpenDisc_amiceTransform (μ : LocallyAnalyticDistribution p K) :
    (amiceTransform μ).OnOpenDisc 1 := by
  rw [onOpenDisc_iff_forall_bddAbove_norm_coeff_mul_norm_factorial (p := p)]
  intro h
  refine ⟨‖stage h μ‖, Set.forall_mem_range.mpr fun n ↦ ?_⟩
  simpa only [norm_mul, ← map_natCast (algebraMap ℚ_[p] K), norm_algebraMap', mul_comm] using
    norm_factorial_mul_coeff_amiceTransform_le μ h n

/-- The transform extends Mathlib's Amice transform on continuous measures. -/
@[simp]
theorem amiceTransform_ofMeasure (μ : AbstractMeasure ℤ_[p] K K) :
    amiceTransform (ofMeasure μ) = μ.amiceTransform := by
  ext n
  rw [coeff_amiceTransform, coe_ofMeasure_apply, LocallyAnalytic.eval_mahler,
    AbstractMeasure.coeff_amiceTransform, PadicInt.mahlerTerm_eq_smul, one_smul]

/-- The stage functional with prescribed weighted binomial moments. -/
private noncomputable def seriesStage {F : PowerSeries K} (hF : F.OnOpenDisc 1) (h : ℕ) :
    AnalyticStage p h K →L[K] K :=
  linearCombination K
    ⟨fun n ↦ ((n / p ^ h).factorial : K) * F.coeff n,
      memℓp_infty (by
        simpa only [norm_mul, ← map_natCast (algebraMap ℚ_[p] K), norm_algebraMap', mul_comm] using
          (onOpenDisc_iff_forall_bddAbove_norm_coeff_mul_norm_factorial (p := p)).mp hF h)⟩ ∘L
    (amiceEquiv p h K).symm.toContinuousLinearEquiv.toContinuousLinearMap

private theorem seriesStage_amiceTerm {F : PowerSeries K} (hF : F.OnOpenDisc 1) (h n : ℕ) :
    seriesStage hF h (amiceTerm p h n (1 : K)) =
      ((n / p ^ h).factorial : K) * F.coeff n := by
  rw [← amiceMap_single K, ← amiceEquiv_apply]
  simp [seriesStage]

private theorem seriesStage_comp_transition {F : PowerSeries K} (hF : F.OnOpenDisc 1) (h : ℕ) :
    seriesStage (p := p) hF (h + 1) ∘L transition K = seriesStage hF h := by
  apply continuousLinearMap_ext_amiceTerm
  intro n
  rw [ContinuousLinearMap.comp_apply, transition_amiceTerm, ← IsScalarTower.algebraMap_smul K,
    amiceTerm_smul, map_smul, seriesStage_amiceTerm, seriesStage_amiceTerm]
  have hf := congrArg (algebraMap ℤ_[p] K) (factorial_mul_amiceTransitionCoeff (p := p) h n)
  simp only [map_mul, map_natCast] at hf
  simpa only [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
    congrArg (fun a : K ↦ a * F.coeff n) hf

/-- The distribution associated to a series on the open unit disc. Its stage functionals pair
Amice coordinates with the factorial-weighted coefficients. -/
noncomputable def ofSeries {F : PowerSeries K} (hF : F.OnOpenDisc 1) :
    LocallyAnalyticDistribution p K :=
  stagesEquiv.symm ⟨seriesStage hF,
    mem_compatibleStageFunctionals_iff.mpr (seriesStage_comp_transition hF)⟩

private theorem stage_ofSeries {F : PowerSeries K} (hF : F.OnOpenDisc 1) (h : ℕ) :
    stage h (ofSeries (p := p) hF) = seriesStage hF h := by
  rw [ofSeries, stage_stagesEquiv_symm]

/-- The distribution constructed from a series has precisely its coefficients as moments. -/
@[simp]
theorem amiceTransform_ofSeries {F : PowerSeries K} (hF : F.OnOpenDisc 1) :
    amiceTransform (ofSeries (p := p) hF) = F := by
  let : CharZero K := Algebra.charZero_of_charZero ℚ_[p] K
  ext n
  have h := seriesStage_amiceTerm (p := p) hF 0 n
  rw [← stage_ofSeries, stage_amiceTerm] at h
  exact mul_left_cancel₀ (by simp [Nat.factorial_ne_zero]) h

/-- Reconstructing a distribution from its transform returns the original distribution. -/
@[simp]
theorem ofSeries_amiceTransform (μ : LocallyAnalyticDistribution p K) :
    ofSeries (onOpenDisc_amiceTransform μ) = μ :=
  amiceTransform_injective (amiceTransform_ofSeries _)

/-- A formal series is an Amice transform of a locally analytic distribution exactly when
it converges on the open unit disc. -/
theorem mem_range_amiceTransform_iff {F : PowerSeries K} :
    F ∈ LinearMap.range (amiceTransform (p := p)) ↔ F.OnOpenDisc 1 :=
  ⟨fun ⟨μ, hμ⟩ ↦ hμ ▸ onOpenDisc_amiceTransform μ,
    fun hF ↦ ⟨ofSeries hF, amiceTransform_ofSeries hF⟩⟩

/-- The Amice bijection between locally analytic distributions and the native open-unit-disc
series algebra, bundled additively. The forward transform is also `K`-linear. -/
noncomputable def amiceTransformEquiv :
    LocallyAnalyticDistribution p K ≃+ _root_.PowerSeries.OnOpenDisc.subring K 1 where
  toFun μ := ⟨amiceTransform μ, _root_.PowerSeries.OnOpenDisc.mem_subring.mpr
    (onOpenDisc_amiceTransform μ)⟩
  invFun F := ofSeries (_root_.PowerSeries.OnOpenDisc.mem_subring.mp F.2)
  left_inv := ofSeries_amiceTransform
  right_inv F := Subtype.ext (amiceTransform_ofSeries
    (_root_.PowerSeries.OnOpenDisc.mem_subring.mp F.2))
  map_add' μ ν := Subtype.ext (map_add amiceTransform μ ν)

/-- The bijection has the usual Amice transform as its underlying formal series. -/
@[simp]
theorem coe_amiceTransformEquiv (μ : LocallyAnalyticDistribution p K) :
    (amiceTransformEquiv μ : PowerSeries K) = amiceTransform μ := (rfl)

/-- The inverse bijection constructs the distribution from the given open-disc series. -/
@[simp]
theorem amiceTransformEquiv_symm_apply (F : _root_.PowerSeries.OnOpenDisc.subring K 1) :
    amiceTransformEquiv.symm F = ofSeries (p := p)
      (_root_.PowerSeries.OnOpenDisc.mem_subring.mp F.2) := (rfl)

private theorem norm_seriesStage {F : PowerSeries K} (hF : F.OnOpenDisc 1) (h : ℕ) :
    ‖seriesStage (p := p) hF h‖ = amiceDualNorm p h F := by
  rw [seriesStage, ContinuousLinearMap.opNorm_comp_linearIsometryEquiv,
    opNorm_linearCombination, lp.norm_eq_ciSup, amiceDualNorm_def]
  simp only [norm_mul, ← map_natCast (algebraMap ℚ_[p] K), norm_algebraMap', mul_comm]

/-- The stage operator norm is the supremum of the factorial-weighted binomial moments. -/
theorem norm_stage_eq_amiceDualNorm (μ : LocallyAnalyticDistribution p K) (h : ℕ) :
    ‖stage h μ‖ = amiceDualNorm p h (amiceTransform μ) := by
  rw [← norm_seriesStage (onOpenDisc_amiceTransform μ), ← stage_ofSeries,
    ofSeries_amiceTransform]

/-- The Gauss norm of the transform at `r_h` is bounded by the level-`h` stage norm. -/
theorem gaussNorm_amiceTransform_le (μ : LocallyAnalyticDistribution p K) (h : ℕ) :
    (amiceTransform μ).gaussNorm norm (amiceRadius p h) ≤ ‖stage h μ‖ := by
  rw [norm_stage_eq_amiceDualNorm]
  exact gaussNorm_amiceRadius_le_amiceDualNorm
    ((onOpenDisc_iff_forall_bddAbove_norm_coeff_mul_norm_factorial (p := p)).mp
      (onOpenDisc_amiceTransform μ) h)

/-- The level-`h` stage norm is bounded by `p` times the Gauss norm at `r_(h+1)`. -/
theorem norm_stage_le_mul_gaussNorm_amiceTransform (μ : LocallyAnalyticDistribution p K)
    (h : ℕ) :
    ‖stage h μ‖ ≤ p * (amiceTransform μ).gaussNorm norm (amiceRadius p (h + 1)) := by
  rw [norm_stage_eq_amiceDualNorm]
  exact amiceDualNorm_le_mul_gaussNorm_amiceRadius_succ
    ((onOpenDisc_iff_forall_hasGaussNorm_amiceRadius (p := p)).mp
      (onOpenDisc_amiceTransform μ) (h + 1))

/-- The logarithm is the transform of a distribution which is not induced by a continuous
measure. Thus passing from measures to distributions strictly enlarges the transform range. -/
theorem ofSeries_log_notMem_range_ofMeasure :
    ofSeries (p := p) (_root_.PowerSeries.onOpenDisc_log (K := ℚ_[p])) ∉
      LinearMap.range (ofMeasure (p := p) (K := ℚ_[p])) := by
  rintro ⟨μ, hμ⟩
  apply log_notMem_range_amiceTransform (p := p)
  refine ⟨μ, ?_⟩
  rw [← amiceTransform_ofMeasure, hμ, amiceTransform_ofSeries]

end LocallyAnalyticDistribution

end TauCeti
