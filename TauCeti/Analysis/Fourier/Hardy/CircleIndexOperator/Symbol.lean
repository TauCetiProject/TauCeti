/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Hardy.CircleIndexOperator.Basic
public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical
import TauCeti.Analysis.Fourier.Uniqueness
import TauCeti.Analysis.Fredholm.FiniteRank

/-!
# Classical symbols for the circle Fourier index operator

In period-one coordinates the Fourier mode of index `n` has angular frequency `2πn`.
`circleHardyProjectionSymbol` is the cutoff of the positive-frequency branch, and
`circleFourierIndexSymbol` has principal branches given by the first character on the positive
axis and the identity on the negative axis. Its full symbol is periodic in position and its
principal symbol is elliptic.

The samples of the full Hardy symbol at `2πn` are the indicator of the positive integers.
The corresponding multiplier is the projection onto the strictly positive Fourier modes.
For every cutoff the full circle index symbol sends mode `n` to mode `n + 1` for `n > 0`
and fixes the other modes. The operator `circleFourierIndexSymbolOperator` realizes this action
on the Fourier basis. Its output coefficient at frequency `1` vanishes for every input.
Its difference from the original operator is supported on the constant input mode, and the
finite-rank perturbation preserves the index `-1`.

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
local notation "Q" => HilbertBasis.projection (fourierBasis (T := 1)) (Set.Ioi (0 : ℤ))

private theorem coefficient_circlePositiveBranch (g : CoordinateSpace 1 → ℂ →L[ℂ] ℂ)
    (hg : ContDiff ℝ ∞ g) (x ξ : CoordinateSpace 1) :
    ((HomogeneousSymbol.ofPositiveBranch g hg).compProdMap (ContinuousLinearMap.id ℝ _)
      (ι).symm.toContinuousLinearEquiv).coefficient (x, ξ) = if 0 < (ι).symm ξ then g x else 0 := by
  simp only [HomogeneousSymbol.coefficient_compProdMap,
    HomogeneousSymbol.coefficient_ofPositiveBranch, ContinuousLinearMap.id_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]

/-- The classical order-zero Hardy projection symbol obtained by cutting off the positive branch. -/
def circleHardyProjectionSymbol (ρ : FrequencyCutoff (CoordinateSpace 1)) :
    ClassicalSymbol 1 ℂ ℂ 0 :=
  let branch := HomogeneousSymbol.ofPositiveBranch
    (fun _ : CoordinateSpace 1 ↦ ContinuousLinearMap.id ℂ ℂ) contDiff_const
  ClassicalSymbol.ofHomogeneous ρ
    (branch.compProdMap (ContinuousLinearMap.id ℝ _) (ι).symm.toContinuousLinearEquiv)

/-- The classical order-zero symbol of the circle index operator with a smooth frequency cutoff. -/
def circleFourierIndexSymbol (ρ : FrequencyCutoff (CoordinateSpace 1)) : ClassicalSymbol 1 ℂ ℂ 0 :=
  let branch := HomogeneousSymbol.ofPositiveBranch
    (fun x : CoordinateSpace 1 ↦
      (fourier (T := 1) 1 ↑((ι).symm x) - 1) • ContinuousLinearMap.id ℂ ℂ) (by
      simp only [fourier_coe_apply, Int.cast_one, Complex.ofReal_one, mul_one, div_one]
      exact ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
        (ι).symm.toContinuousLinearEquiv.contDiff)).cexp.sub contDiff_const).smul contDiff_const)
  ClassicalSymbol.ofSpatial (fun _ ↦ ContinuousLinearMap.id ℂ ℂ) contDiff_const +
    ClassicalSymbol.ofHomogeneous ρ
      (branch.compProdMap (ContinuousLinearMap.id ℝ _) (ι).symm.toContinuousLinearEquiv)

/-- All lower-order homogeneous terms of the Hardy projection symbol vanish. -/
@[simp]
theorem term_circleHardyProjectionSymbol_succ (ρ : FrequencyCutoff (CoordinateSpace 1)) (j : ℕ) :
    (circleHardyProjectionSymbol ρ).term (j + 1) = 0 := by
  simp [circleHardyProjectionSymbol]

/-- All lower-order homogeneous terms of the circle index symbol vanish. -/
@[simp]
theorem term_circleFourierIndexSymbol_succ (ρ : FrequencyCutoff (CoordinateSpace 1)) (j : ℕ) :
    (circleFourierIndexSymbol ρ).term (j + 1) = 0 := by
  simp [circleFourierIndexSymbol]

/-- The full Hardy projection symbol is the cutoff on positive frequencies and zero elsewhere. -/
@[simp]
theorem coefficient_toSymbol_circleHardyProjectionSymbol (ρ : FrequencyCutoff (CoordinateSpace 1))
    (x ξ : CoordinateSpace 1) : (circleHardyProjectionSymbol ρ).toSymbol.coefficient (x, ξ) =
      (if 0 < (ι).symm ξ then (ρ ξ : ℂ) else 0) • ContinuousLinearMap.id ℂ ℂ := by
  simp only [circleHardyProjectionSymbol, ClassicalSymbol.toSymbol_ofHomogeneous,
    HomogeneousSymbol.coefficient_cutoffSymbol, coefficient_circlePositiveBranch]
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
    coefficient_circlePositiveBranch]
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
  simp only [circleHardyProjectionSymbol, ClassicalSymbol.principal_ofHomogeneous,
    coefficient_circlePositiveBranch]

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
      _ _ hξ, ClassicalSymbol.principal_ofHomogeneous, coefficient_circlePositiveBranch]
  ext1
  split_ifs <;> simp

/-- The classical circle index symbol is elliptic for every choice of cutoff. -/
theorem isElliptic_circleFourierIndexSymbol (ρ : FrequencyCutoff (CoordinateSpace 1)) :
    (circleFourierIndexSymbol ρ).IsElliptic := by
  rw [ClassicalSymbol.isElliptic_iff_bijective]
  intro x ξ hξ
  simp only [coefficient_principal_circleFourierIndexSymbol, hξ, ite_false]
  split_ifs
  · let z := fourier (T := 1) 1 ↑((ι).symm x)
    have happ : ⇑(z • ContinuousLinearMap.id ℂ ℂ) = (z * ·) := by
      funext w
      simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    rw [happ]
    exact mulLeft_bijective₀ _ (fourier_apply_ne_zero 1 _)
  · rw [one_smul, ContinuousLinearMap.coe_id']
    exact Function.bijective_id

/-- The sample at angular frequency `2πn` of the full Hardy projection symbol, applied to one. -/
def circleHardyProjectionSample (ρ : FrequencyCutoff (CoordinateSpace 1)) (n : ℤ) : ℂ :=
  (circleHardyProjectionSymbol ρ).toSymbol.coefficient (0, ι (2 * Real.pi * (n : ℝ))) 1

/-- At angular frequency `2πn`, the sample is the cutoff value on the positive branch and zero
on the nonpositive branch. -/
theorem circleHardyProjectionSample_eq_cutoff
    (ρ : FrequencyCutoff (CoordinateSpace 1)) (n : ℤ) :
    circleHardyProjectionSample ρ n =
      if 0 < 2 * Real.pi * (n : ℝ) then (ρ (ι (2 * Real.pi * (n : ℝ))) : ℂ) else 0 := by
  rw [circleHardyProjectionSample, coefficient_toSymbol_circleHardyProjectionSymbol,
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

/-- The lattice samples form the indicator of the strictly positive Fourier modes. -/
theorem circleHardyProjectionSample_eq_indicator (ρ : FrequencyCutoff (CoordinateSpace 1)) :
    circleHardyProjectionSample ρ = (Set.Ioi (0 : ℤ)).indicator 1 := by
  funext n
  simp [Set.indicator_apply]

/-- The full Hardy symbol samples form a bounded sequence. -/
theorem memℓp_circleHardyProjectionSample (ρ : FrequencyCutoff (CoordinateSpace 1)) :
    Memℓp (circleHardyProjectionSample ρ) ∞ := by
  rw [circleHardyProjectionSample_eq_indicator]
  exact one_memℓp_infty.mono fun n ↦ by
    simpa using norm_indicator_le_norm_self (s := Set.Ioi (0 : ℤ)) (1 : ℤ → ℂ) n

/-- The positive Fourier projection is the diagonal multiplier with the full symbol samples. -/
theorem fourierBasis_projection_Ioi_eq_diagonal_circleHardyProjectionSample
    (ρ : FrequencyCutoff (CoordinateSpace 1)) :
    Q = (fourierBasis (T := 1)).diagonal
      ⟨circleHardyProjectionSample ρ, memℓp_circleHardyProjectionSample ρ⟩ := by
  have h := memℓp_circleHardyProjectionSample ρ
  rw [circleHardyProjectionSample_eq_indicator] at h
  rw [HilbertBasis.projection_eq_diagonal _ _ h]
  exact congrArg _ (Subtype.ext (circleHardyProjectionSample_eq_indicator ρ).symm)

/-- At angular frequency `2πn` the full index symbol sends the character of index `n` to
the next character for `n > 0` and fixes it for `n ≤ 0`. -/
@[simp↓]
theorem coefficient_toSymbol_circleFourierIndexSymbol_apply_fourier
    (ρ : FrequencyCutoff (CoordinateSpace 1)) (n : ℤ) (x : ℝ) :
    (circleFourierIndexSymbol ρ).toSymbol.coefficient (ι x, ι (2 * Real.pi * (n : ℝ)))
      (fourier (T := 1) n ↑x) = fourier (T := 1) (if 0 < n then n + 1 else n) ↑x := by
  rw [coefficient_toSymbol_circleFourierIndexSymbol]
  simp only [LinearIsometryEquiv.symm_apply_apply]
  rw [← circleHardyProjectionSample_eq_cutoff, circleHardyProjectionSample_eq]
  simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
  by_cases hn : 0 < n
  · simp only [ite_eq_left hn, fourier_add]
    ring
  · simp [hn]

/-- The bounded operator realizing the circle index symbol on the Fourier lattice.
It multiplies the strictly positive projection by the first character and fixes its complement. -/
def circleFourierIndexSymbolOperator : L² →L[ℂ] L² :=
  (Lp.multiplicationOperator (E := ℂ) (fourierLp (T := 1) ∞ 1) ∘L Q) +
    (ContinuousLinearMap.id ℂ _ - Q)

/-- Apply the circle index symbol operator to a function using its positive-frequency part. -/
theorem circleFourierIndexSymbolOperator_apply (f : L²) :
    circleFourierIndexSymbolOperator f = fourierLp (T := 1) ∞ 1 • Q f + (f - Q f) := by
  simp [circleFourierIndexSymbolOperator, Lp.multiplicationOperator_apply]

/-- The circle index symbol operator shifts strictly positive Fourier modes and fixes the others. -/
@[simp]
theorem circleFourierIndexSymbolOperator_fourierLp (n : ℤ) :
    circleFourierIndexSymbolOperator (fourierLp (T := 1) 2 n) =
      fourierLp (T := 1) 2 (if 0 < n then n + 1 else n) := by
  rw [circleFourierIndexSymbolOperator_apply, fourierBasis_projection_fourierLp]
  by_cases hn : 0 < n <;> simp [hn, fourierLp_smul_fourierLp, add_comm 1 n]

/-- On any circle `L²` input, the sampled operator preserves nonpositive Fourier coefficients
and shifts the positive coefficients up by one. The output coefficient at frequency `1` is zero. -/
@[simp]
theorem fourierCoeff_circleFourierIndexSymbolOperator (f : L²) (n : ℤ) :
    fourierCoeff (circleFourierIndexSymbolOperator f) n =
      if n ≤ 0 then fourierCoeff f n else if n = 1 then 0 else fourierCoeff f (n - 1) := by
  rw [circleFourierIndexSymbolOperator_apply, ← inner_fourierBasis_left _ n]
  simp only [inner_add_right, inner_sub_right, inner_fourierBasis_left, fourierCoeff_fourierLp_smul,
    fourierCoeff_fourierBasis_projection, Set.indicator_apply, Set.mem_Ioi]
  split_ifs <;> first | omega | simp

/-- The Hardy projection and the strictly positive projection differ by the constant mode. -/
theorem hardySubmodule_starProjection_sub_fourierBasis_projection_Ioi :
    hardySubmodule.starProjection - Q =
      InnerProductSpace.rankOne ℂ (fourierBasis (T := 1) 0) (fourierBasis (T := 1) 0) := by
  ext1 f
  apply Lp.ext
  apply Integrable.ae_eq_of_forall_fourierCoeff_eq
    ((Lp.memLp _).integrable (by norm_num)) ((Lp.memLp _).integrable (by norm_num))
  intro n
  rw [← inner_fourierBasis_left _ n, ← inner_fourierBasis_left _ n, sub_apply,
    InnerProductSpace.rankOne_apply, inner_sub_right, inner_smul_right]
  simp only [inner_fourierBasis_left, fourierCoeff_hardySubmodule_starProjection,
    fourierCoeff_fourierBasis_projection, Set.indicator_apply, Set.mem_Ioi]
  rw [coe_fourierBasis, fourierCoeff_fourierLp]
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · simp [hn.ne, not_le.mpr hn, not_lt.mpr hn.le]
  · simp
  · simp [hn, hn.ne', hn.le]

/-- The difference of the original circle operator and the sampled symbol operator is rank one. -/
theorem circleFourierIndexOperator_sub_circleFourierIndexSymbolOperator :
    circleFourierIndexOperator - circleFourierIndexSymbolOperator =
      InnerProductSpace.rankOne ℂ (fourierBasis (T := 1) 1 - fourierBasis (T := 1) 0)
        (fourierBasis (T := 1) 0) := by
  let M := Lp.multiplicationOperator (E := ℂ) (fourierLp (T := 1) ∞ 1) (p := 2)
  calc
    _ = (M - ContinuousLinearMap.id ℂ _) ∘L
        (hardySubmodule.starProjection - Q) := by
      rw [ContinuousLinearMap.comp_sub]
      ext1 f
      simp only [sub_apply, circleFourierIndexOperator_apply,
        circleFourierIndexSymbolOperator_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply, M, Lp.multiplicationOperator_apply]
      abel
    _ = _ := by
      rw [hardySubmodule_starProjection_sub_fourierBasis_projection_Ioi,
        InnerProductSpace.comp_rankOne]
      simp only [sub_apply, M, Lp.multiplicationOperator_apply, fourierLp_smul_fourierBasis,
        add_zero, ContinuousLinearMap.id_apply]

/-- The original operator minus the sampled operator sends each input to its zeroth Fourier
coefficient times the difference between the first and constant modes. -/
theorem circleFourierIndexOperator_sub_circleFourierIndexSymbolOperator_apply (f : L²) :
    (circleFourierIndexOperator - circleFourierIndexSymbolOperator) f =
      fourierCoeff f 0 • (fourierBasis (T := 1) 1 - fourierBasis (T := 1) 0) := by
  rw [circleFourierIndexOperator_sub_circleFourierIndexSymbolOperator,
    InnerProductSpace.rankOne_apply, inner_fourierBasis_left]

/-- The difference of the original and sampled circle index operators has complex rank one. -/
theorem rank_circleFourierIndexOperator_sub_circleFourierIndexSymbolOperator :
    (circleFourierIndexOperator - circleFourierIndexSymbolOperator).rank = 1 := by
  rw [circleFourierIndexOperator_sub_circleFourierIndexSymbolOperator]
  have hb : Orthonormal ℂ (fourierBasis (T := 1)) := (fourierBasis (T := 1)).orthonormal
  exact InnerProductSpace.rank_rankOne
    (sub_ne_zero.mpr (hb.linearIndependent.injective.ne (by decide))) (hb.ne_zero 0)

/-- The difference of the original and sampled circle index operators has finite range. -/
theorem hasFiniteRange_circleFourierIndexOperator_sub_circleFourierIndexSymbolOperator :
    (circleFourierIndexOperator - circleFourierIndexSymbolOperator).toLinearMap.HasFiniteRange := by
  have h : (circleFourierIndexOperator - circleFourierIndexSymbolOperator).rank <
      Cardinal.aleph0 := by
    rw [rank_circleFourierIndexOperator_sub_circleFourierIndexSymbolOperator]
    exact Cardinal.one_lt_aleph0
  have := Module.rank_lt_aleph0_iff.mp h
  exact Submodule.FG.of_finite

/-- The sampled circle index operator is Fredholm. -/
theorem isFredholm_circleFourierIndexSymbolOperator :
    circleFourierIndexSymbolOperator.IsFredholm := by
  have h := hasFiniteRange_circleFourierIndexOperator_sub_circleFourierIndexSymbolOperator.neg
  simpa [neg_sub] using isFredholm_circleFourierIndexOperator.add_hasFiniteRange
    (v := -(circleFourierIndexOperator - circleFourierIndexSymbolOperator)) h

/-- The sampled circle index operator has Fredholm index `-1`. -/
theorem index_circleFourierIndexSymbolOperator : circleFourierIndexSymbolOperator.index = -1 := by
  have h := hasFiniteRange_circleFourierIndexOperator_sub_circleFourierIndexSymbolOperator.neg
  have heq := ContinuousLinearMap.index_add_of_hasFiniteRange
    (K := -(circleFourierIndexOperator - circleFourierIndexSymbolOperator))
    isFredholm_circleFourierIndexOperator h
  simpa [neg_sub, index_circleFourierIndexOperator] using heq

end TauCeti
