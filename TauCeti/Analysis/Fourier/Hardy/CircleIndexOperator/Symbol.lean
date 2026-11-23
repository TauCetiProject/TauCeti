/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Hardy.CircleIndexOperator
public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical
import TauCeti.Analysis.Fredholm.FiniteRank
import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Diagonal

/-!
# Classical symbols for the circle Fourier index operator

In period-one coordinates the Fourier mode of index `n` has angular frequency `2πn`.
`circleHardyProjectionSymbol` is the cutoff of the positive-frequency branch, and
`circleFourierIndexSymbol` has principal branches given by the first character on the positive
axis and the identity on the negative axis. Its full symbol is periodic in position and its
principal symbol is elliptic.

The samples of the full projection symbol give the orthogonal projection onto the strictly
positive modes. The operator `circleFourierIndexSymbolOperator` realizes the full circle index
symbol on every Fourier mode. Its difference from the original operator is supported on the
constant input mode, and the finite-rank perturbation preserves the index `-1`.

The circle projection and operator come from Atiyah–Singer, *The Index of Elliptic Operators: I*,
§8, pp. 525–526. The homogeneous branch arguments are adapted from `PeriodicFourierSymbol.lean`
and `CircleFourierPseudodifferential.lean` in the Lean-Atiyah-Singer formalization by Alpha Squared
Labs and Codex.
[Atiyah–Singer I](https://doi.org/10.2307/1970715)
[Lean-Atiyah-Singer](https://github.com/alpha-squared-labs/Lean-Atiyah-Singer)
-/

public section

noncomputable section

open MeasureTheory
open scoped ContDiff ENNReal

namespace TauCeti

local notation "ι" => OrthonormalBasis.repr (OrthonormalBasis.singleton (Fin 1) ℝ)
local notation "L²" => Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))

/-- The homogeneous positive-frequency branch with a prescribed spatial coefficient. -/
private def circleHardyPositiveBranch (g : CoordinateSpace 1 → ℂ) (hg : ContDiff ℝ ∞ g) :
    HomogeneousSymbol (CoordinateSpace 1) (CoordinateSpace 1) ℂ ℂ 0 where
  coefficient p := if 0 < (ι).symm p.2 then g p.1 • ContinuousLinearMap.id ℂ ℂ else 0
  zero_covector _ := by rw [(ι).symm.map_zero]; simp
  contDiffOn_coefficient := by
    intro p hp
    have hcoord : Continuous (fun q : CoordinateSpace 1 × CoordinateSpace 1 ↦ (ι).symm q.2) :=
      (ι).symm.continuous.comp continuous_snd
    have hne : (ι).symm p.2 ≠ 0 := mt (ι).symm.map_eq_zero_iff.mp hp
    rcases hne.lt_or_gt with hneg | hpos
    · apply ContDiffAt.contDiffWithinAt
      apply (contDiffAt_const (c := (0 : ℂ →L[ℂ] ℂ))).congr_of_eventuallyEq
      filter_upwards [hcoord.continuousAt (Iio_mem_nhds hneg)] with q hq
      have hq' : (ι).symm q.2 < 0 := hq
      exact ite_eq_right (not_lt_of_ge hq'.le)
    · have hg' : ContDiff ℝ ∞
          (fun q : CoordinateSpace 1 × CoordinateSpace 1 ↦ g q.1 • ContinuousLinearMap.id ℂ ℂ) :=
        (hg.comp contDiff_fst).smul contDiff_const
      apply ContDiffAt.contDiffWithinAt
      apply hg'.contDiffAt.congr_of_eventuallyEq
      filter_upwards [hcoord.continuousAt (Ioi_mem_nhds hpos)] with q hq
      exact ite_eq_left hq
  homogeneous x ξ t ht := by
    rw [(ι).symm.map_smul, smul_eq_mul]
    simp only [mul_pos_iff_of_pos_left ht, Real.rpow_zero, one_smul]

/-- The classical order-zero Hardy projection symbol obtained by cutting off the positive branch. -/
def circleHardyProjectionSymbol (ρ : FrequencyCutoff (CoordinateSpace 1)) :
    ClassicalSymbol 1 ℂ ℂ 0 :=
  ClassicalSymbol.ofHomogeneous ρ (circleHardyPositiveBranch (fun _ ↦ 1) contDiff_const)

/-- The classical order-zero symbol of the circle index operator with a smooth frequency cutoff. -/
def circleFourierIndexSymbol (ρ : FrequencyCutoff (CoordinateSpace 1)) : ClassicalSymbol 1 ℂ ℂ 0 :=
  ClassicalSymbol.ofSpatial (fun _ ↦ ContinuousLinearMap.id ℂ ℂ) contDiff_const +
    ClassicalSymbol.ofHomogeneous ρ (circleHardyPositiveBranch
      (fun x ↦ fourier (T := 1) 1 ↑((ι).symm x) - 1) (by
        simp only [fourier_coe_apply, Int.cast_one, Complex.ofReal_one, mul_one, div_one]
        exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
          (ι).symm.toContinuousLinearEquiv.contDiff)).cexp.sub contDiff_const))

/-- The full Hardy projection symbol is the cutoff on positive frequencies and zero elsewhere. -/
@[simp]
theorem coefficient_toSymbol_circleHardyProjectionSymbol (ρ : FrequencyCutoff (CoordinateSpace 1))
    (x ξ : CoordinateSpace 1) : (circleHardyProjectionSymbol ρ).toSymbol.coefficient (x, ξ) =
      (if 0 < (ι).symm ξ then (ρ ξ : ℂ) else 0) • ContinuousLinearMap.id ℂ ℂ := by
  simp only [circleHardyProjectionSymbol, ClassicalSymbol.toSymbol_ofHomogeneous,
    HomogeneousSymbol.coefficient_cutoffSymbol, circleHardyPositiveBranch]
  ext1
  split_ifs <;> simp [Complex.real_smul]

/-- The full circle index symbol is the identity plus the cutoff positive branch of `z - 1`. -/
@[simp]
theorem coefficient_toSymbol_circleFourierIndexSymbol (ρ : FrequencyCutoff (CoordinateSpace 1))
    (x ξ : CoordinateSpace 1) : (circleFourierIndexSymbol ρ).toSymbol.coefficient (x, ξ) =
      (1 + (fourier (T := 1) 1 ↑((ι).symm x) - 1) *
        (if 0 < (ι).symm ξ then (ρ ξ : ℂ) else 0)) • ContinuousLinearMap.id ℂ ℂ := by
  simp only [circleFourierIndexSymbol, ClassicalSymbol.toSymbol_add, Symbol.coefficient_add,
    Pi.add_apply, ClassicalSymbol.toSymbol_ofSpatial, Symbol.coefficient_ofSpatial,
    ClassicalSymbol.toSymbol_ofHomogeneous, HomogeneousSymbol.coefficient_cutoffSymbol,
    circleHardyPositiveBranch]
  ext1
  split_ifs
  · simp [Complex.real_smul]
    ring
  · simp

/-- The full Hardy projection symbol is periodic in position with period one. -/
theorem periodic_coefficient_toSymbol_circleHardyProjectionSymbol
    (ρ : FrequencyCutoff (CoordinateSpace 1)) (s : ℝ) :
    Function.Periodic (fun x : ℝ ↦ (circleHardyProjectionSymbol ρ).toSymbol.coefficient
      (ι x, ι s)) 1 := by
  intro x
  simp only [coefficient_toSymbol_circleHardyProjectionSymbol]

/-- The full circle index symbol is periodic in position with period one. -/
theorem periodic_coefficient_toSymbol_circleFourierIndexSymbol
    (ρ : FrequencyCutoff (CoordinateSpace 1)) (s : ℝ) :
    Function.Periodic (fun x : ℝ ↦ (circleFourierIndexSymbol ρ).toSymbol.coefficient
      (ι x, ι s)) 1 := by
  intro x
  simp only [coefficient_toSymbol_circleFourierIndexSymbol, LinearIsometryEquiv.symm_apply_apply,
    AddCircle.coe_add_period]

/-- The principal Hardy projection symbol is the identity on the positive frequency branch. -/
@[simp]
theorem coefficient_principal_circleHardyProjectionSymbol
    (ρ : FrequencyCutoff (CoordinateSpace 1)) (x ξ : CoordinateSpace 1) :
    (circleHardyProjectionSymbol ρ).principal.coefficient (x, ξ) =
      (if 0 < (ι).symm ξ then ContinuousLinearMap.id ℂ ℂ else 0) := by
  simp [circleHardyProjectionSymbol, circleHardyPositiveBranch]

/-- The principal circle index symbol multiplies by `z` on the positive axis and by one on the
negative axis. Its value at the zero covector is zero. -/
@[simp]
theorem coefficient_principal_circleFourierIndexSymbol
    (ρ : FrequencyCutoff (CoordinateSpace 1)) (x ξ : CoordinateSpace 1) :
    (circleFourierIndexSymbol ρ).principal.coefficient (x, ξ) =
      if ξ = 0 then 0 else
        (if 0 < (ι).symm ξ then fourier (T := 1) 1 ↑((ι).symm x) else 1) •
          ContinuousLinearMap.id ℂ ℂ := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp
  simp only [hξ, ite_false, circleFourierIndexSymbol, ClassicalSymbol.principal_add,
    HomogeneousSymbol.coefficient_add, Pi.add_apply, ClassicalSymbol.coefficient_principal_ofSpatial
      _ _ hξ, ClassicalSymbol.principal_ofHomogeneous, circleHardyPositiveBranch]
  ext1
  split_ifs <;> simp

/-- The classical circle index symbol is elliptic for every choice of cutoff. -/
theorem isElliptic_circleFourierIndexSymbol (ρ : FrequencyCutoff (CoordinateSpace 1)) :
    (circleFourierIndexSymbol ρ).IsElliptic := by
  rw [ClassicalSymbol.isElliptic_iff_bijective]
  intro x ξ hξ
  simp only [coefficient_principal_circleFourierIndexSymbol, hξ, ite_false]
  split_ifs
  · exact (LinearEquiv.smulOfNeZero ℂ ℂ _ (fourier_apply_ne_zero 1 ↑((ι).symm x))).bijective
  · rw [one_smul]
    exact Function.bijective_id

/-- The sample at angular frequency `2πn` of the full Hardy projection symbol, applied to one. -/
def circleHardyProjectionSample (ρ : FrequencyCutoff (CoordinateSpace 1)) (n : ℤ) : ℂ :=
  (circleHardyProjectionSymbol ρ).toSymbol.coefficient (0, ι (2 * Real.pi * (n : ℝ))) 1

/-- The sample evaluates the full projection symbol at zero position and angular frequency `2πn`. -/
theorem circleHardyProjectionSample_def (ρ : FrequencyCutoff (CoordinateSpace 1)) (n : ℤ) :
    circleHardyProjectionSample ρ n =
      (circleHardyProjectionSymbol ρ).toSymbol.coefficient (0, ι (2 * Real.pi * (n : ℝ))) 1 :=
  (rfl)

private theorem circleHardyProjectionSample_eq_cutoff
    (ρ : FrequencyCutoff (CoordinateSpace 1)) (n : ℤ) :
    circleHardyProjectionSample ρ n =
      if 0 < 2 * Real.pi * (n : ℝ) then (ρ (ι (2 * Real.pi * (n : ℝ))) : ℂ) else 0 := by
  rw [circleHardyProjectionSample_def, coefficient_toSymbol_circleHardyProjectionSymbol,
    LinearIsometryEquiv.symm_apply_apply]
  split_ifs <;> simp

/-- Sampling the full Hardy projection symbol on the Fourier lattice gives the strict step. -/
@[simp]
theorem circleHardyProjectionSample_eq (ρ : FrequencyCutoff (CoordinateSpace 1)) (n : ℤ) :
    circleHardyProjectionSample ρ n = if 0 < n then 1 else 0 := by
  rw [circleHardyProjectionSample_eq_cutoff]
  by_cases hn : 0 < n
  · have hn₁ : 1 ≤ n := by omega
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn₁
    have hπ : (2 : ℝ) ≤ 2 * Real.pi := by linarith [Real.two_le_pi]
    have hω : 2 ≤ 2 * Real.pi * (n : ℝ) := hπ.trans
      (le_mul_of_one_le_right (by positivity) hnR)
    have hpos : 0 < 2 * Real.pi * (n : ℝ) := lt_of_lt_of_le (by norm_num) hω
    have hnorm : 2 ≤ ‖ι (2 * Real.pi * (n : ℝ))‖ := calc
      2 ≤ ‖2 * Real.pi * (n : ℝ)‖ := by simpa only [Real.norm_eq_abs, abs_of_pos hpos] using hω
      _ = ‖ι (2 * Real.pi * (n : ℝ))‖ := ((ι).norm_map _).symm
    simp [hn, hpos, ρ.apply_eq_one_of_two_le_norm hnorm]
  · have hn₀ : (n : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_gt hn)
    have hω := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 2 * Real.pi) hn₀
    simp [hn, not_lt_of_ge hω]

/-- The bounded Fourier multiplier obtained from the sampled Hardy projection symbol. -/
def circleHardySampledProjection (ρ : FrequencyCutoff (CoordinateSpace 1)) : L² →L[ℂ] L² :=
  (fourierBasis (T := 1)).diagonal ⟨circleHardyProjectionSample ρ, by
    refine memℓp_infty ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    by_cases hn : 0 < n <;> simp [circleHardyProjectionSample_eq, hn]⟩

-- Evaluate the coefficient before simplification expands the projection on a mode.
/-- The sampled Hardy projection multiplies Fourier coefficients by the symbol samples. -/
@[simp↓]
theorem fourierCoeff_circleHardySampledProjection (ρ : FrequencyCutoff (CoordinateSpace 1))
    (f : L²) (n : ℤ) :
    fourierCoeff (circleHardySampledProjection ρ f) n =
      circleHardyProjectionSample ρ n * fourierCoeff f n := by
  rw [← fourierBasis_repr, ← fourierBasis_repr, circleHardySampledProjection,
    HilbertBasis.repr_diagonal]

/-- The sampled Hardy projection acts diagonally on the Fourier basis. -/
@[simp]
theorem circleHardySampledProjection_fourierLp (ρ : FrequencyCutoff (CoordinateSpace 1))
    (n : ℤ) : circleHardySampledProjection ρ (fourierLp (T := 1) 2 n) =
      circleHardyProjectionSample ρ n • fourierLp (T := 1) 2 n := by
  rw [← coe_fourierBasis]
  exact (fourierBasis (T := 1)).diagonal_apply_self _ n

/-- The bounded operator associated to the cutoff circle index symbol on the Fourier lattice. -/
def circleFourierIndexSymbolOperator (ρ : FrequencyCutoff (CoordinateSpace 1)) : L² →L[ℂ] L² :=
  (Lp.multiplicationOperator (E := ℂ) (fourierLp (T := 1) ∞ 1) ∘L
    circleHardySampledProjection ρ) +
  (ContinuousLinearMap.id ℂ _ - circleHardySampledProjection ρ)

/-- Apply the cutoff circle index operator using multiplication and the sampled projection. -/
theorem circleFourierIndexSymbolOperator_apply (ρ : FrequencyCutoff (CoordinateSpace 1))
    (f : L²) : circleFourierIndexSymbolOperator ρ f =
      fourierLp (T := 1) ∞ 1 • circleHardySampledProjection ρ f +
        (f - circleHardySampledProjection ρ f) := by
  simp only [circleFourierIndexSymbolOperator, add_apply, ContinuousLinearMap.comp_apply,
    sub_apply, ContinuousLinearMap.id_apply, Lp.multiplicationOperator_apply]

/-- The continuous representative of the symbol action on the Fourier mode of index `n`. -/
def circleFourierIndexSymbolMode (ρ : FrequencyCutoff (CoordinateSpace 1)) (n : ℤ) :
    C(AddCircle (1 : ℝ), ℂ) :=
  (1 - circleHardyProjectionSample ρ n) • fourier n +
    circleHardyProjectionSample ρ n • fourier (n + 1)

/-- Evaluate the continuous representative as a linear combination of consecutive modes. -/
@[simp]
theorem circleFourierIndexSymbolMode_apply (ρ : FrequencyCutoff (CoordinateSpace 1)) (n : ℤ)
    (x : AddCircle (1 : ℝ)) : circleFourierIndexSymbolMode ρ n x =
      (1 - circleHardyProjectionSample ρ n) * fourier n x +
        circleHardyProjectionSample ρ n * fourier (n + 1) x := by
  simp only [circleFourierIndexSymbolMode, ContinuousMap.add_apply, ContinuousMap.smul_apply,
    smul_eq_mul]

/-- At each real position the continuous mode representative is obtained by evaluating the full
symbol at the corresponding angular frequency. -/
theorem circleFourierIndexSymbolMode_coe_apply (ρ : FrequencyCutoff (CoordinateSpace 1))
    (n : ℤ) (x : ℝ) : circleFourierIndexSymbolMode ρ n ↑x =
      (circleFourierIndexSymbol ρ).toSymbol.coefficient (ι x, ι (2 * Real.pi * (n : ℝ)))
        (fourier (T := 1) n ↑x) := by
  rw [circleFourierIndexSymbolMode_apply, coefficient_toSymbol_circleFourierIndexSymbol]
  simp only [LinearIsometryEquiv.symm_apply_apply]
  rw [← circleHardyProjectionSample_eq_cutoff, fourier_add]
  simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
  ring

/-- The L² class of the symbol action shifts the strictly positive modes and fixes the others. -/
@[simp]
theorem toLp_circleFourierIndexSymbolMode (ρ : FrequencyCutoff (CoordinateSpace 1))
    (n : ℤ) : ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (circleFourierIndexSymbolMode ρ n) =
      fourierLp (T := 1) 2 (if 0 < n then n + 1 else n) := by
  simp only [circleFourierIndexSymbolMode, map_add, map_smul, fourierLp,
    circleHardyProjectionSample_eq]
  split_ifs <;> simp

/-- On every Fourier mode the cutoff operator is the `L²` class of the symbol evaluation. -/
@[simp]
theorem circleFourierIndexSymbolOperator_fourierLp (ρ : FrequencyCutoff (CoordinateSpace 1))
    (n : ℤ) : circleFourierIndexSymbolOperator ρ (fourierLp (T := 1) 2 n) =
      ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (circleFourierIndexSymbolMode ρ n) := by
  rw [circleFourierIndexSymbolOperator_apply, circleHardySampledProjection_fourierLp,
    toLp_circleFourierIndexSymbolMode]
  by_cases hn : 0 < n
  · simp [hn, fourierLp_smul_fourierLp, add_comm 1 n]
  · simp [hn]

/-- The original circle operator acts by the cutoff symbol on every nonconstant mode and sends
the constant mode to the first mode. -/
theorem circleFourierIndexOperator_fourierBasis_eq_toLp_add
    (ρ : FrequencyCutoff (CoordinateSpace 1)) (n : ℤ) :
    circleFourierIndexOperator (fourierBasis (T := 1) n) =
      ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (circleFourierIndexSymbolMode ρ n) +
        (if n = 0 then fourierBasis (T := 1) 1 - fourierBasis (T := 1) 0 else 0) := by
  rw [toLp_circleFourierIndexSymbolMode, coe_fourierBasis, circleFourierIndexOperator_fourierLp]
  by_cases hn : n = 0
  · simp [hn]
  · have hsign : 0 ≤ n ↔ 0 < n := by omega
    simp only [hn, ite_false, add_zero, hsign]
    split_ifs <;> rfl

/-- The exact and sampled Hardy projections differ by the projection onto constants. -/
theorem hardySubmodule_starProjection_sub_circleHardySampledProjection
    (ρ : FrequencyCutoff (CoordinateSpace 1)) :
    hardySubmodule.starProjection - circleHardySampledProjection ρ =
      InnerProductSpace.rankOne ℂ (fourierBasis (T := 1) 0) (fourierBasis (T := 1) 0) := by
  ext1 f
  apply (fourierBasis (T := 1)).repr.injective
  apply lp.ext
  funext n
  rw [sub_apply, map_sub, InnerProductSpace.rankOne_apply, inner_fourierBasis_left, map_smul,
    HilbertBasis.repr_self]
  simp only [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, fourierBasis_repr,
    fourierCoeff_hardySubmodule_starProjection, fourierCoeff_circleHardySampledProjection,
    circleHardyProjectionSample_eq, lp.coeFn_single]
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · simp [hn.ne, not_le.mpr hn, not_lt.mpr hn.le]
  · simp
  · simp [hn, hn.ne', hn.le]

/-- The difference of the original circle operator and the sampled symbol operator is rank one. -/
theorem circleFourierIndexOperator_sub_circleFourierIndexSymbolOperator
    (ρ : FrequencyCutoff (CoordinateSpace 1)) :
    circleFourierIndexOperator - circleFourierIndexSymbolOperator ρ =
      InnerProductSpace.rankOne ℂ (fourierBasis (T := 1) 1 - fourierBasis (T := 1) 0)
        (fourierBasis (T := 1) 0) := by
  apply (fourierBasis (T := 1)).ext_continuousLinearMap
  intro n
  rw [sub_apply, circleFourierIndexOperator_fourierBasis_eq_toLp_add,
    InnerProductSpace.rankOne_apply, inner_fourierBasis_left, coe_fourierBasis,
    circleFourierIndexSymbolOperator_fourierLp, add_sub_cancel_left, fourierCoeff_fourierLp]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn, Ne.symm hn]

/-- The original operator minus the sampled operator sends each input to its zeroth Fourier
coefficient times the difference between the first and constant modes. -/
theorem circleFourierIndexOperator_sub_circleFourierIndexSymbolOperator_apply
    (ρ : FrequencyCutoff (CoordinateSpace 1)) (f : L²) :
    (circleFourierIndexOperator - circleFourierIndexSymbolOperator ρ) f =
      fourierCoeff f 0 • (fourierBasis (T := 1) 1 - fourierBasis (T := 1) 0) := by
  rw [circleFourierIndexOperator_sub_circleFourierIndexSymbolOperator,
    InnerProductSpace.rankOne_apply, inner_fourierBasis_left]

/-- The difference of the original and cutoff circle index operators has complex rank one. -/
theorem rank_circleFourierIndexOperator_sub_circleFourierIndexSymbolOperator
    (ρ : FrequencyCutoff (CoordinateSpace 1)) :
    (circleFourierIndexOperator - circleFourierIndexSymbolOperator ρ).rank = 1 := by
  rw [circleFourierIndexOperator_sub_circleFourierIndexSymbolOperator]
  have hb : Orthonormal ℂ (fourierBasis (T := 1)) := (fourierBasis (T := 1)).orthonormal
  exact InnerProductSpace.rank_rankOne
    (sub_ne_zero.mpr (hb.linearIndependent.injective.ne (by decide))) (hb.ne_zero 0)

/-- The difference of the original operator and the cutoff operator has finite range. -/
theorem hasFiniteRange_circleFourierIndexOperator_sub_circleFourierIndexSymbolOperator
    (ρ : FrequencyCutoff (CoordinateSpace 1)) :
    (circleFourierIndexOperator -
      circleFourierIndexSymbolOperator ρ).toLinearMap.HasFiniteRange := by
  have h : (circleFourierIndexOperator - circleFourierIndexSymbolOperator ρ).rank <
      Cardinal.aleph0 := by
    rw [rank_circleFourierIndexOperator_sub_circleFourierIndexSymbolOperator]
    exact Cardinal.one_lt_aleph0
  have := Module.rank_lt_aleph0_iff.mp h
  exact Submodule.FG.of_finite

/-- The cutoff circle index operator is Fredholm. -/
theorem isFredholm_circleFourierIndexSymbolOperator (ρ : FrequencyCutoff (CoordinateSpace 1)) :
    (circleFourierIndexSymbolOperator ρ).IsFredholm := by
  have h := (hasFiniteRange_circleFourierIndexOperator_sub_circleFourierIndexSymbolOperator ρ).neg
  simpa [neg_sub] using isFredholm_circleFourierIndexOperator.add_hasFiniteRange
    (v := -(circleFourierIndexOperator - circleFourierIndexSymbolOperator ρ)) h

/-- The cutoff circle index operator has Fredholm index `-1` for every cutoff. -/
theorem index_circleFourierIndexSymbolOperator (ρ : FrequencyCutoff (CoordinateSpace 1)) :
    (circleFourierIndexSymbolOperator ρ).index = -1 := by
  have h := (hasFiniteRange_circleFourierIndexOperator_sub_circleFourierIndexSymbolOperator ρ).neg
  have heq := ContinuousLinearMap.index_add_of_hasFiniteRange
    (K := -(circleFourierIndexOperator - circleFourierIndexSymbolOperator ρ))
    isFredholm_circleFourierIndexOperator h
  simpa [neg_sub, index_circleFourierIndexOperator] using heq

end TauCeti
