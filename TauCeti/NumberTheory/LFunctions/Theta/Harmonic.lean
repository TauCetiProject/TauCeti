/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import TauCeti.Analysis.SpecialFunctions.Gaussian.Harmonic
public import TauCeti.NumberTheory.LFunctions.Theta.Inversion
public import TauCeti.NumberTheory.LFunctions.Theta.Surface.Haar
public import TauCeti.NumberTheory.NumberField.Global.InfinityType.IdentityComponent
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.MellinTransform
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.Basic

/-!
# Harmonic polynomials, Hecke's Fourier lemma, and weighted gamma integrals

A continuous infinity type `t` on a number field `K` determines an archimedean harmonic polynomial
`t.harmonicFactor` on `mixedSpace K`: `x_w ^ (t.realParity w).val` at each real place `w`, and the
signed monomial `conj(z_w) ^ k_w` (`k_w ≥ 0`) or `z_w ^ (-k_w)` (`k_w < 0`) of degree
`|k_w| = |t.complexAngularFrequency w|` at each complex place `w`. Because these depend only on
`realParity` and `complexAngularFrequency`, they apply uniformly to algebraic Hecke characters,
ray class characters, and general continuous infinity types.

For positive parameters `y`, `t.harmonicFactor * archGaussian y` lies in Schwartz space and
transforms under `mixedFourier K` into itself at `y⁻¹` with scalar
`(-i) ^ t.harmonicDegree * N(y) ^ (-1/2) * ∏_w y_w ^ (-P_w)`. Poisson summation on any full lattice
`L` transforms shifted harmonic-theta sums over `L` into dual sums over `mixedDual K L`, and
integrating against `t.archWeight y * N(y)^(s/2)` over `archHaar K` produces the shifted gamma
product `∏_w Γ_ℝ(mult w * s + P_w)` on `∀ w, 0 < mult w * Re s + P_w`.

## Main definitions

* `TauCeti.GlobalNumberFields.ContinuousInfinityType.harmonicExponent`, `harmonicDegree`,
  `harmonicFactor`, `archWeight`: local/total harmonic degrees, harmonic polynomial, and weight.
* `TauCeti.LFunctions.harmonicArchGaussianSchwartz`: `t.harmonicFactor * archGaussian y` in Schwartz
  space.

## Main results

* `TauCeti.LFunctions.mixedFourier_harmonicFactor_mul_archGaussian`: Hecke's Fourier eigenfunction
  lemma on `mixedSpace K`.
* `TauCeti.LFunctions.tsum_harmonicFactor_mul_archGaussian_add_eq_mixedDual` and
  `TauCeti.LFunctions.tsum_harmonicFactor_mul_archGaussian_eq_mixedDual`: twisted Poisson summation.
* `TauCeti.LFunctions.integral_archGaussian_mul_archWeight_mul_archNorm_cpow`: the weighted
  archimedean gamma integral.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §§3, 7–8.
-/

public noncomputable section

open Complex ComplexConjugate MeasureTheory NumberField NumberField.InfinitePlace
  NumberField.mixedEmbedding TauCeti.NumberField.mixedEmbedding
open scoped ContDiff FourierTransform Real RealInnerProductSpace SchwartzMap

namespace TauCeti.GlobalNumberFields.ContinuousInfinityType

section Field

variable {K : Type*} [Field K]

open scoped Classical in
/-- The local harmonic degree `P_w` of a continuous infinity type `t` at an infinite place `w`:
`(t.realParity w).val ∈ {0, 1}` at a real place and `|t.complexAngularFrequency w|` at a complex
place. -/
def harmonicExponent (t : ContinuousInfinityType K) (w : InfinitePlace K) : ℕ :=
  if h : w.IsReal then (t.realParity ⟨w, h⟩).val
  else (t.complexAngularFrequency ⟨w, not_isReal_iff_isComplex.mp h⟩).natAbs

open scoped Classical in
/-- The defining formula of `harmonicExponent`. -/
theorem harmonicExponent_def (t : ContinuousInfinityType K) (w : InfinitePlace K) :
    t.harmonicExponent w =
      if h : w.IsReal then (t.realParity ⟨w, h⟩).val
      else (t.complexAngularFrequency ⟨w, not_isReal_iff_isComplex.mp h⟩).natAbs := (rfl)

@[simp]
theorem harmonicExponent_of_isReal (t : ContinuousInfinityType K) {w : InfinitePlace K}
    (hw : w.IsReal) : t.harmonicExponent w = (t.realParity ⟨w, hw⟩).val := by
  simp [harmonicExponent_def, hw]

@[simp]
theorem harmonicExponent_of_isComplex (t : ContinuousInfinityType K) {w : InfinitePlace K}
    (hw : w.IsComplex) :
    t.harmonicExponent w = (t.complexAngularFrequency ⟨w, hw⟩).natAbs := by
  simp [harmonicExponent_def, not_isReal_iff_isComplex.mpr hw]

/-- At a real place, the harmonic exponent is at most `1`. -/
theorem harmonicExponent_le_one_of_isReal (t : ContinuousInfinityType K) {w : InfinitePlace K}
    (hw : w.IsReal) : t.harmonicExponent w ≤ 1 := by
  rw [harmonicExponent_of_isReal t hw]
  exact Nat.lt_succ_iff.mp (t.realParity ⟨w, hw⟩).val_lt

@[simp]
theorem zero_harmonicExponent (w : InfinitePlace K) :
    (0 : ContinuousInfinityType K).harmonicExponent w = 0 := by
  rcases w.isReal_or_isComplex with hw | hw <;> simp [hw]

@[simp]
theorem neg_harmonicExponent (t : ContinuousInfinityType K) (w : InfinitePlace K) :
    (-t).harmonicExponent w = t.harmonicExponent w := by
  rcases w.isReal_or_isComplex with hw | hw
  · simp only [harmonicExponent_of_isReal _ hw, neg_realParity, Pi.neg_apply]
    generalize t.realParity ⟨w, hw⟩ = ε; revert ε; decide
  · simp [hw]

/-- At a complex place, `harmonicExponent` depends only on the restriction to the identity
component. -/
theorem harmonicExponent_eq_of_agreesOnIdentityComponent {t u : ContinuousInfinityType K}
    (h : t.AgreesOnIdentityComponent u) {w : InfinitePlace K} (hw : w.IsComplex) :
    t.harmonicExponent w = u.harmonicExponent w := by
  simp [hw, ((t.agreesOnIdentityComponent_iff u).mp h).2.2]

/-- At a complex place `w`, the harmonic exponent of `AlgebraicInfinityType.toContinuous n` is
`|n w.embedding - n (conj w.embedding)|`. -/
theorem toContinuous_harmonicExponent_of_isComplex (n : AlgebraicInfinityType K)
    {w : InfinitePlace K} (hw : w.IsComplex) :
    (AlgebraicInfinityType.toContinuous n).harmonicExponent w =
      (n w.embedding - n (ComplexEmbedding.conjugate w.embedding)).natAbs := by
  simp [hw]

end Field

section NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The total degree `Tr(p) = ∑_w P_w` of the harmonic polynomial of `t`. -/
def harmonicDegree (t : ContinuousInfinityType K) : ℕ :=
  ∑ w : InfinitePlace K, t.harmonicExponent w

/-- The defining equation of `harmonicDegree`. -/
theorem harmonicDegree_def (t : ContinuousInfinityType K) :
    t.harmonicDegree = ∑ w : InfinitePlace K, t.harmonicExponent w := (rfl)

open scoped Classical in
/-- `harmonicDegree` splits into the sum of real parities plus the sum of absolute complex angular
frequencies. -/
theorem harmonicDegree_eq_sum_add_sum (t : ContinuousInfinityType K) :
    t.harmonicDegree =
      (∑ w : {w : InfinitePlace K // w.IsReal}, (t.realParity w).val) +
        ∑ w : {w : InfinitePlace K // w.IsComplex}, (t.complexAngularFrequency w).natAbs := by
  rw [harmonicDegree_def, InfinitePlace.sum_eq_sum_add_sum]
  exact congrArg₂ _ (Finset.sum_congr rfl fun w _ ↦ t.harmonicExponent_of_isReal w.property)
    (Finset.sum_congr rfl fun w _ ↦ t.harmonicExponent_of_isComplex w.property)

@[simp]
theorem zero_harmonicDegree : (0 : ContinuousInfinityType K).harmonicDegree = 0 := by
  simp [harmonicDegree_def]

@[simp]
theorem neg_harmonicDegree (t : ContinuousInfinityType K) :
    (-t).harmonicDegree = t.harmonicDegree := by
  simp [harmonicDegree_def]

/-- The total harmonic degree vanishes precisely when every real parity and every complex angular
frequency vanishes. -/
theorem harmonicDegree_eq_zero_iff (t : ContinuousInfinityType K) :
    t.harmonicDegree = 0 ↔ t.realParity = 0 ∧ t.complexAngularFrequency = 0 := by
  rw [harmonicDegree_def, Finset.sum_eq_zero_iff, funext_iff, funext_iff]
  refine ⟨fun h ↦ ⟨fun w ↦ ?_, fun w ↦ ?_⟩, fun ⟨hr, hc⟩ w _ ↦ ?_⟩
  · simpa [t.harmonicExponent_of_isReal w.property] using h w.val (Finset.mem_univ _)
  · simpa [t.harmonicExponent_of_isComplex w.property] using h w.val (Finset.mem_univ _)
  · exact w.isReal_or_isComplex.elim (fun hw ↦ by simp [hw, hr ⟨w, hw⟩])
      fun hw ↦ by simp [hw, hc ⟨w, hw⟩]

open scoped Classical in
/-- **The archimedean harmonic polynomial** attached to a continuous infinity type `t` on
`mixedSpace K`: `x_w ^ (t.realParity w).val` at each real place and
`TauCeti.complexHarmonicMonomial (t.complexAngularFrequency w) (x.2 w)` at each complex place. -/
def harmonicFactor (t : ContinuousInfinityType K) (x : mixedSpace K) : ℂ :=
  (∏ w : {w : InfinitePlace K // w.IsReal}, ((x.1 w : ℝ) : ℂ) ^ (t.realParity w).val) *
    ∏ w : {w : InfinitePlace K // w.IsComplex},
      TauCeti.complexHarmonicMonomial (t.complexAngularFrequency w) (x.2 w)

open scoped Classical in
/-- The defining formula of `harmonicFactor`. -/
theorem harmonicFactor_def (t : ContinuousInfinityType K) (x : mixedSpace K) :
    t.harmonicFactor x =
      (∏ w : {w : InfinitePlace K // w.IsReal}, ((x.1 w : ℝ) : ℂ) ^ (t.realParity w).val) *
        ∏ w : {w : InfinitePlace K // w.IsComplex},
          TauCeti.complexHarmonicMonomial (t.complexAngularFrequency w) (x.2 w) := (rfl)

@[simp]
theorem zero_harmonicFactor (x : mixedSpace K) :
    (0 : ContinuousInfinityType K).harmonicFactor x = 1 := by classical simp [harmonicFactor_def]

@[simp]
theorem harmonicFactor_one (t : ContinuousInfinityType K) : t.harmonicFactor 1 = 1 := by
  classical simp [harmonicFactor_def]

/-- When the total harmonic degree vanishes, the harmonic polynomial is the constant `1`. -/
theorem harmonicFactor_eq_one_of_harmonicDegree_eq_zero (t : ContinuousInfinityType K)
    (h : t.harmonicDegree = 0) (x : mixedSpace K) : t.harmonicFactor x = 1 := by
  classical
  obtain ⟨hr, hc⟩ := t.harmonicDegree_eq_zero_iff.mp h
  simp [harmonicFactor_def, hr, hc, TauCeti.complexHarmonicMonomial_zero]

/-- `harmonicFactor` is completely multiplicative on the commutative ring `mixedSpace K`. -/
theorem harmonicFactor_mul (t : ContinuousInfinityType K) (x z : mixedSpace K) :
    t.harmonicFactor (x * z) = t.harmonicFactor x * t.harmonicFactor z := by
  classical
  simp only [harmonicFactor_def, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, ofReal_mul, mul_pow,
    TauCeti.complexHarmonicMonomial_mul, Finset.prod_mul_distrib]
  ring

/-- Negating the infinity type conjugates `harmonicFactor` at every point of `mixedSpace K`. -/
theorem neg_harmonicFactor (t : ContinuousInfinityType K) (x : mixedSpace K) :
    (-t).harmonicFactor x = conj (t.harmonicFactor x) := by
  classical
  simp only [harmonicFactor_def, neg_realParity, Pi.neg_apply, neg_complexAngularFrequency,
    TauCeti.complexHarmonicMonomial_neg, map_mul, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  have hval : (-t.realParity w).val = (t.realParity w).val := by
    generalize t.realParity w = ε; revert ε; decide
  rw [hval, map_pow, conj_ofReal]

/-- At `0`, `harmonicFactor` takes the value `1` if `t.harmonicDegree = 0` and `0` otherwise. -/
theorem harmonicFactor_zero_right (t : ContinuousInfinityType K) :
    t.harmonicFactor 0 = if t.harmonicDegree = 0 then 1 else 0 := by
  classical
  by_cases hd : t.harmonicDegree = 0
  · obtain ⟨hr, hc⟩ := t.harmonicDegree_eq_zero_iff.mp hd
    simp [harmonicFactor_def, hd, hr, hc]
  · obtain ⟨w, -, hw⟩ : ∃ w ∈ Finset.univ, t.harmonicExponent w ≠ 0 := by
      simpa [harmonicDegree_def] using hd
    rw [ite_eq_right_iff.mpr fun h ↦ (hd h).elim, harmonicFactor_def]
    rcases w.isReal_or_isComplex with hwr | hwc
    · rw [t.harmonicExponent_of_isReal hwr] at hw
      exact mul_eq_zero_of_left
        (Finset.prod_eq_zero (Finset.mem_univ ⟨w, hwr⟩) (by simp [zero_pow hw])) _
    · rw [t.harmonicExponent_of_isComplex hwc, Int.natAbs_ne_zero] at hw
      exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ ⟨w, hwc⟩)
        (by simp [TauCeti.complexHarmonicMonomial_zero_right, hw]))

/-- The norm of `t.harmonicFactor x` is `∏_w normAtPlace w x ^ t.harmonicExponent w`. -/
theorem norm_harmonicFactor (t : ContinuousInfinityType K) (x : mixedSpace K) :
    ‖t.harmonicFactor x‖ = ∏ w : InfinitePlace K, normAtPlace w x ^ t.harmonicExponent w := by
  classical
  rw [harmonicFactor_def, norm_mul, norm_prod, norm_prod, InfinitePlace.prod_eq_prod_mul_prod]
  refine congrArg₂ _ (Finset.prod_congr rfl fun w _ ↦ ?_) (Finset.prod_congr rfl fun w _ ↦ ?_)
  · rw [norm_pow, Complex.norm_real, ← normAtPlace_apply_of_isReal w.property,
      t.harmonicExponent_of_isReal w.property]
  · rw [TauCeti.norm_complexHarmonicMonomial, ← normAtPlace_apply_of_isComplex w.property,
      t.harmonicExponent_of_isComplex w.property]

/-- On `mixedSpaceOfRealSpace r`, `harmonicFactor` evaluates to `∏_w r_w ^ P_w`. -/
theorem harmonicFactor_mixedSpaceOfRealSpace (t : ContinuousInfinityType K) (r : realSpace K) :
    t.harmonicFactor (mixedSpaceOfRealSpace r) =
      ((∏ w : InfinitePlace K, r w ^ t.harmonicExponent w : ℝ) : ℂ) := by
  classical
  rw [harmonicFactor_def, InfinitePlace.prod_eq_prod_mul_prod, ofReal_mul, ofReal_prod, ofReal_prod]
  refine congrArg₂ _ (Finset.prod_congr rfl fun w _ ↦ ?_) (Finset.prod_congr rfl fun w _ ↦ ?_)
  · simp [mixedSpaceOfRealSpace_apply, t.harmonicExponent_of_isReal w.property]
  · simp [mixedSpaceOfRealSpace_apply, t.harmonicExponent_of_isComplex w.property]

/-- Scaling by `mixedSpaceOfRealSpace r` multiplies `harmonicFactor` by `∏_w r_w ^ P_w`. -/
theorem harmonicFactor_mixedSpaceOfRealSpace_mul (t : ContinuousInfinityType K)
    (r : realSpace K) (x : mixedSpace K) :
    t.harmonicFactor (mixedSpaceOfRealSpace r * x) =
      ((∏ w : InfinitePlace K, r w ^ t.harmonicExponent w : ℝ) : ℂ) * t.harmonicFactor x := by
  rw [harmonicFactor_mul, harmonicFactor_mixedSpaceOfRealSpace]

/-- The action of a unit `u` on `mixedSpace K` multiplies `harmonicFactor` by its value at
`mixedEmbedding K u`. -/
theorem harmonicFactor_unit_smul (t : ContinuousInfinityType K) (u : (𝓞 K)ˣ)
    (x : mixedSpace K) :
    t.harmonicFactor (u • x) = t.harmonicFactor (mixedEmbedding K u) * t.harmonicFactor x := by
  rw [unitSMul_smul, harmonicFactor_mul]

open scoped Classical in
@[fun_prop]
theorem hasTemperateGrowth_harmonicFactor (t : ContinuousInfinityType K) :
    (t.harmonicFactor : mixedSpace K → ℂ).HasTemperateGrowth := by
  have hreal (w : {w : InfinitePlace K // w.IsReal}) :
      (fun x : mixedSpace K ↦ ((x.1 w : ℝ) : ℂ) ^ (t.realParity w).val).HasTemperateGrowth := by
    let L : mixedSpace K →L[ℝ] ℂ :=
      ofRealCLM.comp ((ContinuousLinearMap.proj w).comp (ContinuousLinearMap.fst ℝ _ _))
    exact L.hasTemperateGrowth.pow _
  have hcomp (w : {w : InfinitePlace K // w.IsComplex}) :
      (fun x : mixedSpace K ↦
        TauCeti.complexHarmonicMonomial
          (t.complexAngularFrequency w) (x.2 w)).HasTemperateGrowth := by
    let L : mixedSpace K →L[ℝ] ℂ :=
      (ContinuousLinearMap.proj w).comp (ContinuousLinearMap.snd ℝ _ _)
    exact (TauCeti.hasTemperateGrowth_complexHarmonicMonomial _).comp L.hasTemperateGrowth
  rw [funext t.harmonicFactor_def]
  exact (Function.HasTemperateGrowth.prod Finset.univ fun w _ ↦ hreal w).fun_mul
    (Function.HasTemperateGrowth.prod Finset.univ fun w _ ↦ hcomp w)

open scoped Classical in
@[fun_prop]
theorem contDiff_harmonicFactor (t : ContinuousInfinityType K) {n : WithTop ℕ∞} :
    ContDiff ℝ n t.harmonicFactor := by
  rw [funext t.harmonicFactor_def]
  refine ContDiff.mul (contDiff_prod fun w _ ↦ ?_) (contDiff_prod fun w _ ↦ by fun_prop)
  let L : mixedSpace K →L[ℝ] ℂ :=
    ofRealCLM.comp ((ContinuousLinearMap.proj w).comp (ContinuousLinearMap.fst ℝ _ _))
  exact L.contDiff.pow _

@[fun_prop]
theorem continuous_harmonicFactor (t : ContinuousInfinityType K) :
    Continuous t.harmonicFactor := by
  classical exact (t.contDiff_harmonicFactor (n := 0)).continuous

/-! ### The archimedean parameter weight -/

/-- The archimedean parameter weight `∏_w y_w ^ (P_w / 2)` of Neukirch VII (8.2)–(8.3). -/
def archWeight (t : ContinuousInfinityType K) (y : realSpace K) : ℝ :=
  ∏ w : InfinitePlace K, y w ^ ((t.harmonicExponent w : ℝ) / 2)

/-- The defining equation of `archWeight`. -/
theorem archWeight_def (t : ContinuousInfinityType K) (y : realSpace K) :
    t.archWeight y = ∏ w : InfinitePlace K, y w ^ ((t.harmonicExponent w : ℝ) / 2) := (rfl)

@[simp]
theorem zero_archWeight (y : realSpace K) : (0 : ContinuousInfinityType K).archWeight y = 1 := by
  simp [archWeight_def]

@[simp]
theorem neg_archWeight (t : ContinuousInfinityType K) (y : realSpace K) :
    (-t).archWeight y = t.archWeight y := by simp [archWeight_def]

@[simp]
theorem archWeight_one (t : ContinuousInfinityType K) : t.archWeight 1 = 1 := by
  simp [archWeight_def]

/-- For nonnegative parameters, `archWeight` is nonnegative. -/
theorem archWeight_nonneg (t : ContinuousInfinityType K) {y : realSpace K}
    (hy : ∀ w, 0 ≤ y w) : 0 ≤ t.archWeight y :=
  Finset.prod_nonneg fun w _ ↦ Real.rpow_nonneg (hy w) _

/-- For positive parameters, `archWeight` is strictly positive. -/
theorem archWeight_pos (t : ContinuousInfinityType K) {y : realSpace K}
    (hy : ∀ w, 0 < y w) : 0 < t.archWeight y :=
  Finset.prod_pos fun w _ ↦ Real.rpow_pos_of_pos (hy w) _

/-- `archWeight` distributes over a product whose first factor is nonnegative, with no sign
condition on the second factor. -/
theorem archWeight_mul (t : ContinuousInfinityType K) {y : realSpace K}
    (hy : ∀ w, 0 ≤ y w) (z : realSpace K) :
    t.archWeight (y * z) = t.archWeight y * t.archWeight z := by
  simp only [archWeight_def, Pi.mul_apply, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun w _ ↦ Real.mul_rpow_of_nonneg_left (hy w) (z w) _

/-- `archWeight` commutes with coordinatewise parameter inversion. -/
theorem archWeight_inv (t : ContinuousInfinityType K) (y : realSpace K) :
    t.archWeight y⁻¹ = (t.archWeight y)⁻¹ := by
  simp only [archWeight_def, Pi.inv_apply, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  rcases le_or_gt 0 (y w) with hx | hx
  · exact Real.inv_rpow hx _
  · rcases (t.harmonicExponent w).even_or_odd with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [hk, Nat.cast_add, add_self_div_two, Real.rpow_natCast, Real.rpow_natCast, inv_pow]
    · have hcos : Real.cos ((t.harmonicExponent w : ℝ) / 2 * π) = 0 :=
        Real.cos_eq_zero_iff.mpr ⟨k, by rw [hk]; push_cast; ring⟩
      simp [Real.rpow_def_of_neg (inv_lt_zero.mpr hx), Real.rpow_def_of_neg hx, hcos]

/-- For nonnegative parameters, squaring `archWeight y` gives `∏_w y_w ^ P_w`. -/
theorem archWeight_sq (t : ContinuousInfinityType K) {y : realSpace K} (hy : ∀ w, 0 ≤ y w) :
    t.archWeight y ^ 2 = ∏ w : InfinitePlace K, y w ^ t.harmonicExponent w := by
  rw [sq, ← t.archWeight_mul hy y, archWeight_def]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  rw [Pi.mul_apply, ← sq, Real.sq_rpow_div_two (hy w), Real.rpow_natCast]

/-- Upon rescaling each parameter by the square of a local absolute value, the
archimedean weight gains the absolute value of the harmonic factor. -/
theorem archWeight_mul_sq_normAtPlace (t : ContinuousInfinityType K) (a : mixedSpace K)
    (y : realSpace K) :
    t.archWeight (fun w ↦ normAtPlace w a ^ 2 * y w) = ‖t.harmonicFactor a‖ * t.archWeight y := by
  simp only [archWeight_def, norm_harmonicFactor, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  rw [Real.mul_rpow_of_nonneg_left (sq_nonneg _),
    Real.sq_rpow_div_two (normAtPlace_nonneg w a), Real.rpow_natCast]

/-- Under `TauCeti.LFunctions.unitScale u`, `archWeight` multiplies by
`∏_w normAtPlace w (mixedEmbedding K u) ^ P_w`. -/
theorem archWeight_unitScale (t : ContinuousInfinityType K) (u : (𝓞 K)ˣ) (y : realSpace K) :
    t.archWeight (TauCeti.LFunctions.unitScale u y) =
      (∏ w : InfinitePlace K, normAtPlace w (mixedEmbedding K u) ^ t.harmonicExponent w) *
        t.archWeight y := by
  have h : TauCeti.LFunctions.unitScale u y =
      fun w ↦ normAtPlace w (mixedEmbedding K (u : K)) ^ 2 * y w := by
    ext w
    rw [TauCeti.LFunctions.unitScale_apply, normAtPlace_apply]
  rw [h, t.archWeight_mul_sq_normAtPlace, norm_harmonicFactor]

end NumberField

end TauCeti.GlobalNumberFields.ContinuousInfinityType

namespace TauCeti.LFunctions

open TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-! ### Schwartz packaging and lattice summability -/

open scoped Classical in
/-- The harmonic-weighted archimedean Gaussian `x ↦ t.harmonicFactor x * archGaussian y x` as a
Schwartz function on `mixedSpace K`, for positive parameters `y`. -/
def harmonicArchGaussianSchwartz (t : ContinuousInfinityType K) (y : realSpace K)
    (hy : ∀ w, 0 < y w) : 𝓢(mixedSpace K, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ t.harmonicFactor (archGaussianSchwartz y hy)

open scoped Classical in
/-- The defining equation of `harmonicArchGaussianSchwartz`. -/
theorem harmonicArchGaussianSchwartz_def (t : ContinuousInfinityType K) (y : realSpace K)
    (hy : ∀ w, 0 < y w) :
    harmonicArchGaussianSchwartz t y hy =
      SchwartzMap.smulLeftCLM ℂ t.harmonicFactor (archGaussianSchwartz y hy) := (rfl)

open scoped Classical in
@[simp]
theorem harmonicArchGaussianSchwartz_apply (t : ContinuousInfinityType K) (y : realSpace K)
    (hy : ∀ w, 0 < y w) (x : mixedSpace K) :
    harmonicArchGaussianSchwartz t y hy x = t.harmonicFactor x * archGaussian y x := by
  rw [harmonicArchGaussianSchwartz_def,
    SchwartzMap.smulLeftCLM_apply_apply t.hasTemperateGrowth_harmonicFactor,
    archGaussianSchwartz_apply, smul_eq_mul]

open scoped Classical in
@[simp]
theorem harmonicArchGaussianSchwartz_zero (y : realSpace K) (hy : ∀ w, 0 < y w) :
    harmonicArchGaussianSchwartz 0 y hy = archGaussianSchwartz y hy := by ext x; simp

/-- For positive parameters `y`, a shifted harmonic-weighted archimedean Gaussian is summable over
any discrete `ℤ`-submodule of `mixedSpace K`. -/
theorem summable_harmonicFactor_mul_archGaussian_add (t : ContinuousInfinityType K)
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] (y : realSpace K) (hy : ∀ w, 0 < y w)
    (v : mixedSpace K) :
    Summable fun x : L ↦ t.harmonicFactor (v + x) * archGaussian y (v + x) := by
  classical simpa using ZLattice.summable_poisson_left L (harmonicArchGaussianSchwartz t y hy) v

/-- For positive parameters `y`, `t.harmonicFactor x * archGaussian y x` is summable over any
discrete `ℤ`-submodule of `mixedSpace K`. -/
theorem summable_harmonicFactor_mul_archGaussian (t : ContinuousInfinityType K)
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] (y : realSpace K) (hy : ∀ w, 0 < y w) :
    Summable fun x : L ↦ t.harmonicFactor x * archGaussian y x := by
  simpa using summable_harmonicFactor_mul_archGaussian_add t L y hy 0

/-- For positive parameters `y`, `‖t.harmonicFactor x * archGaussian y x‖` is summable over any
discrete `ℤ`-submodule of `mixedSpace K`. -/
theorem summable_norm_harmonicFactor_mul_archGaussian (t : ContinuousInfinityType K)
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] (y : realSpace K) (hy : ∀ w, 0 < y w) :
    Summable fun x : L ↦ ‖t.harmonicFactor x * archGaussian y x‖ :=
  summable_norm_iff.mpr (summable_harmonicFactor_mul_archGaussian t L y hy)

/-! ### Hecke's Fourier eigenfunction lemma -/

open scoped Classical in
/-- At `y = 1`, `archGaussian 1 x` factors into one standard Gaussian `exp (-π ‖x_w‖²)` per real
and complex place. -/
private theorem archGaussian_one_eq_prod_mul_prod (x : mixedSpace K) :
    archGaussian 1 x =
      (∏ w : {w : InfinitePlace K // w.IsReal}, cexp (-π * ‖x.1 w‖ ^ 2)) *
        ∏ w : {w : InfinitePlace K // w.IsComplex}, cexp (-π * ‖x.2 w‖ ^ 2) := by
  rw [archGaussian_apply, InfinitePlace.sum_eq_sum_add_sum]
  simp only [Pi.one_apply, one_mul, mul_add, Real.exp_add, ofReal_mul, Finset.mul_sum,
    Real.exp_sum, ofReal_prod, ofReal_exp]
  refine congrArg₂ _ (Finset.prod_congr rfl fun w _ ↦ ?_) (Finset.prod_congr rfl fun w _ ↦ ?_)
  · rw [normAtPlace_apply_of_isReal w.property]; push_cast; ring_nf
  · rw [normAtPlace_apply_of_isComplex w.property]; push_cast; ring_nf

open scoped Classical in
/-- At `y = 1`, the Fourier integrand on `mixedSpace K` splits into the product of its real-place
and complex-place Fourier integrands. -/
private theorem mixedFourier_integrand_one_eq_prod_mul_prod (t : ContinuousInfinityType K)
    (x ξ : mixedSpace K) :
    𝐞 (-mixedInner K x ξ) • (t.harmonicFactor x * archGaussian 1 x) =
      (∏ w : {w : InfinitePlace K // w.IsReal},
          𝐞 (-(x.1 w * ξ.1 w)) • (((x.1 w : ℝ) : ℂ) ^ (t.realParity w).val *
            cexp (-π * ‖x.1 w‖ ^ 2))) *
        ∏ w : {w : InfinitePlace K // w.IsComplex},
          𝐞 (-⟪x.2 w, ξ.2 w⟫) •
            (TauCeti.complexHarmonicMonomial (t.complexAngularFrequency w) (x.2 w) *
              cexp (-π * ‖x.2 w‖ ^ 2)) := by
  have hinner (w : {w : InfinitePlace K // w.IsComplex}) :
      (x.2 w * conj (ξ.2 w)).re = ⟪x.2 w, ξ.2 w⟫ := by
    simp only [real_inner_eq_re_inner ℂ, RCLike.inner_apply, RCLike.re_to_complex,
      Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring
  have hchar : (𝐞 (-mixedInner K x ξ) : ℂ) =
      (∏ w : {w : InfinitePlace K // w.IsReal}, (𝐞 (-(x.1 w * ξ.1 w)) : ℂ)) *
        ∏ w : {w : InfinitePlace K // w.IsComplex}, (𝐞 (-⟪x.2 w, ξ.2 w⟫) : ℂ) := by
    simp only [Real.fourierChar_apply, mixedInner_def, hinner]; push_cast
    rw [neg_add, mul_add, add_mul, Complex.exp_add]
    congr 1 <;> rw [← Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul, Complex.exp_sum]
  simp only [Circle.smul_def, smul_eq_mul, hchar, t.harmonicFactor_def,
    archGaussian_one_eq_prod_mul_prod]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib]
  ring

/-- **Hecke's Fourier eigenfunction lemma at parameter `1`**: on `mixedSpace K`, the harmonic
polynomial `t.harmonicFactor` times `archGaussian 1` transforms under `mixedFourier K` into
`(-i) ^ t.harmonicDegree` times itself. -/
theorem mixedFourier_harmonicFactor_mul_archGaussian_one (t : ContinuousInfinityType K)
    (ξ : mixedSpace K) :
    mixedFourier K (fun x ↦ t.harmonicFactor x * archGaussian 1 x) ξ =
      (-I) ^ t.harmonicDegree * t.harmonicFactor ξ * archGaussian 1 ξ := by
  classical
  have hb : 0 < (π : ℂ).re := by simpa using Real.pi_pos
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hdiv (r : ℂ) : -(π : ℂ) ^ 2 * r / π = -π * r := by field_simp
  rw [mixedFourier_apply]
  simp_rw [mixedFourier_integrand_one_eq_prod_mul_prod]
  rw [Measure.volume_eq_prod,
    MeasureTheory.integral_prod_mul
      (fun xr : {w : InfinitePlace K // w.IsReal} → ℝ ↦
        ∏ w, 𝐞 (-(xr w * ξ.1 w)) • (((xr w : ℝ) : ℂ) ^ (t.realParity w).val *
          cexp (-π * ‖xr w‖ ^ 2)))
      (fun xc : {w : InfinitePlace K // w.IsComplex} → ℂ ↦
        ∏ w, 𝐞 (-⟪xc w, ξ.2 w⟫) •
          (TauCeti.complexHarmonicMonomial (t.complexAngularFrequency w) (xc w) *
            cexp (-π * ‖xc w‖ ^ 2))),
    MeasureTheory.integral_fintype_prod_volume_eq_prod
      (f := fun w (u : ℝ) ↦
        𝐞 (-(u * ξ.1 w)) • (((u : ℝ) : ℂ) ^ (t.realParity w).val * cexp (-π * ‖u‖ ^ 2))),
    MeasureTheory.integral_fintype_prod_volume_eq_prod
      (f := fun w (z : ℂ) ↦ 𝐞 (-⟪z, ξ.2 w⟫) •
        (TauCeti.complexHarmonicMonomial (t.complexAngularFrequency w) z * cexp (-π * ‖z‖ ^ 2)))]
  have hreal (w : {w : InfinitePlace K // w.IsReal}) :
      ∫ u : ℝ, 𝐞 (-(u * ξ.1 w)) • (((u : ℝ) : ℂ) ^ (t.realParity w).val * cexp (-π * ‖u‖ ^ 2)) =
        (-I) ^ (t.realParity w).val * ((ξ.1 w : ℝ) : ℂ) ^ (t.realParity w).val *
          cexp (-π * ‖ξ.1 w‖ ^ 2) := by
    have he : (t.realParity w).val ≤ 1 := by
      simpa [t.harmonicExponent_of_isReal w.property] using t.harmonicExponent_le_one_of_isReal
          w.property
    rw [← Real.fourier_real_eq, TauCeti.fourier_pow_mul_cexp_neg_mul_norm_sq_real hb he,
      div_self hpi, one_cpow, one_mul, hdiv]
  have hcomp (w : {w : InfinitePlace K // w.IsComplex}) :
      ∫ z : ℂ, 𝐞 (-⟪z, ξ.2 w⟫) •
          (TauCeti.complexHarmonicMonomial (t.complexAngularFrequency w) z * cexp (-π * ‖z‖ ^ 2)) =
        (-I) ^ (t.complexAngularFrequency w).natAbs *
          TauCeti.complexHarmonicMonomial (t.complexAngularFrequency w) (ξ.2 w) *
          cexp (-π * ‖ξ.2 w‖ ^ 2) := by
    rw [← Real.fourier_eq, TauCeti.fourier_complexHarmonicMonomial_mul_cexp_neg_mul_norm_sq hb,
      div_self hpi, one_pow, one_mul, hdiv]
  simp_rw [hreal, hcomp, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [t.harmonicDegree_eq_sum_add_sum, pow_add, t.harmonicFactor_def,
    archGaussian_one_eq_prod_mul_prod]
  ring

/-- **Hecke's Fourier eigenfunction lemma** (Neukirch VII (3.5)–(3.6) on the imaginary axis): for
every continuous infinity type `t` and positive parameter vector `y`,
`t.harmonicFactor * archGaussian y` transforms under `mixedFourier K` into
`t.harmonicFactor * archGaussian y⁻¹` multiplied by
`(-i) ^ t.harmonicDegree * N(y)^(-1/2) * ∏_w y_w^(-P_w)`. -/
theorem mixedFourier_harmonicFactor_mul_archGaussian (t : ContinuousInfinityType K)
    (y : realSpace K) (hy : ∀ w, 0 < y w) (ξ : mixedSpace K) :
    mixedFourier K (fun x ↦ t.harmonicFactor x * archGaussian y x) ξ =
      (-I) ^ t.harmonicDegree * (((√(archNorm y))⁻¹ : ℝ) : ℂ) *
        ((∏ w : InfinitePlace K, (y w)⁻¹ ^ t.harmonicExponent w : ℝ) : ℂ) *
        t.harmonicFactor ξ * archGaussian y⁻¹ ξ := by
  classical
  have hy' : ∀ w, 0 < y⁻¹ w := fun w ↦ inv_pos.mpr (hy w)
  set c : mixedSpace K := mixedSpaceOfRealSpace fun w ↦ √(y w)
  set c' : mixedSpace K := mixedSpaceOfRealSpace fun w ↦ √(y⁻¹ w)
  have hcc' : c * c' = 1 := by
    ext w <;> simp [c, c', mixedSpaceOfRealSpace_apply, (Real.sqrt_pos.mpr (hy _)).ne']
  have hc'sq : c' * c' = mixedSpaceOfRealSpace y⁻¹ := by
    ext w <;>
    · simp only [c', Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, mixedSpaceOfRealSpace_apply]
      exact_mod_cast Real.mul_self_sqrt (hy' w).le
  have hc : mixedEmbedding.norm c = √(archNorm y) :=
    norm_mixedSpaceOfRealSpace_sqrt fun w ↦ (hy w).le
  have hint (x : mixedSpace K) :
      𝐞 (-mixedInner K x ξ) • (t.harmonicFactor x * archGaussian y x) =
        t.harmonicFactor c' * (𝐞 (-mixedInner K (c * x) (c' * ξ)) •
          (t.harmonicFactor (c * x) * archGaussian 1 (c * x))) := by
    have hx : c' * (c * x) = x := by rw [← mul_assoc, mul_comm c' c, hcc', one_mul]
    conv_lhs => rw [← hx]
    rw [mixedInner_mixedSpaceOfRealSpace_mul, t.harmonicFactor_mul c' (c * x), hx,
      ← archGaussian_one_archGaussianDilation y hy, archGaussianDilation_apply]
    simp only [Circle.smul_def, c, c']; ring
  rw [mixedFourier_apply]
  simp_rw [hint]
  rw [MeasureTheory.integral_const_mul,
    integral_comp_mul_left
      (fun z ↦ 𝐞 (-mixedInner K z (c' * ξ)) • (t.harmonicFactor z * archGaussian 1 z)) c,
    ← mixedFourier_apply, mixedFourier_harmonicFactor_mul_archGaussian_one,
    t.harmonicFactor_mul c' ξ, ← archGaussianDilation_apply y⁻¹ hy',
    archGaussian_one_archGaussianDilation, hc, Complex.real_smul]
  have hprod : t.harmonicFactor c' * t.harmonicFactor c' =
      ((∏ w : InfinitePlace K, (y w)⁻¹ ^ t.harmonicExponent w : ℝ) : ℂ) := by
    rw [← t.harmonicFactor_mul, hc'sq, t.harmonicFactor_mixedSpaceOfRealSpace]; rfl
  calc t.harmonicFactor c' * ((((√(archNorm y))⁻¹ : ℝ) : ℂ) *
          ((-I) ^ t.harmonicDegree * (t.harmonicFactor c' * t.harmonicFactor ξ) *
            archGaussian y⁻¹ ξ))
      = (-I) ^ t.harmonicDegree * (((√(archNorm y))⁻¹ : ℝ) : ℂ) *
          (t.harmonicFactor c' * t.harmonicFactor c') * t.harmonicFactor ξ *
          archGaussian y⁻¹ ξ := by ring
    _ = _ := by rw [hprod]

/-! ### Twisted Poisson summation on a full lattice -/

open scoped Classical in
private theorem exists_injective_forall_normAtPlace_bounds
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] [IsZLattice ℝ L]
    (v : mixedSpace K) (w₀ : InfinitePlace K) :
    ∃ (B : ℝ) (q : ℕ → L), Function.Injective q ∧
      (∀ n w, 1 ≤ normAtPlace w (v + (q n : mixedSpace K))) ∧
      ∀ n w, w ≠ w₀ → normAtPlace w (v + (q n : mixedSpace K)) ≤ B := by
  let b₀ := Module.Free.chooseBasis ℤ L
  let b := b₀.ofZLatticeBasis ℝ
  let M : ℝ := ∑ i, ‖b i‖
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  let r (n : ℕ) : realSpace K :=
    fun w ↦ if w = w₀ then (n + 1 : ℝ) * (2 * M + 2) else M + 1
  have hr (n : ℕ) (w : InfinitePlace K) : 0 ≤ r n w := by dsimp [r]; split_ifs <;> positivity
  let z (n : ℕ) : mixedSpace K := mixedSpaceOfRealSpace (r n)
  let q (n : ℕ) : L := ⟨ZSpan.floor b (z n - v), (b₀.ofZLatticeBasis_span ℝ).le
    (ZSpan.floor b (z n - v)).property⟩
  have hdist (n : ℕ) (w : InfinitePlace K) :
      |r n w - normAtPlace w (v + (q n : mixedSpace K))| ≤ M := by
    have hz : normAtPlace w (z n) = r n w := normAtPlace_mixedSpaceOfRealSpace (hr n w)
    have hsub : z n - (v + (q n : mixedSpace K)) = ZSpan.fract b (z n - v) := by
      rw [ZSpan.fract_apply]; abel
    exact hz ▸ (abs_normAtPlace_sub_normAtPlace_le_norm w (z n) (v + (q n : mixedSpace K))).trans
      (hsub ▸ ZSpan.norm_fract_le b (z n - v))
  refine ⟨2 * M + 1, q, fun m n hmn ↦ ?_, fun n w ↦ ?_, fun n w hw ↦ ?_⟩
  · by_contra hne
    wlog hlt : m < n generalizing m n
    · exact this n m hmn.symm (Ne.symm hne) (Nat.lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne))
    have hm := (abs_le.mp (hdist m w₀)).1
    have hn := (abs_le.mp (hdist n w₀)).2
    simp only [r, ↓reduceIte, hmn] at hm hn
    have hmn1 : (m : ℝ) + 2 ≤ n + 1 := by exact_mod_cast (by omega : m + 2 ≤ n + 1)
    nlinarith
  · have h1 := (abs_le.mp (hdist n w)).2
    dsimp [r] at h1; split_ifs at h1 <;> nlinarith [Nat.cast_nonneg (α := ℝ) n]
  · have h2 := (abs_le.mp (hdist n w)).1
    dsimp [r] at h2; rw [ite_eq_right_iff.mpr fun h ↦ (hw h).elim] at h2; linarith

open scoped Classical in
private theorem not_summable_norm_harmonicFactor_mul_archGaussian_add
    (t : ContinuousInfinityType K) (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L]
    [IsZLattice ℝ L] {y : realSpace K} (hy : ¬ ∀ w, 0 < y w) (v : mixedSpace K) :
    ¬ Summable fun ℓ : L ↦ ‖t.harmonicFactor (v + ℓ) * archGaussian y (v + ℓ)‖ := by
  push Not at hy
  obtain ⟨w₀, hw₀⟩ := hy
  obtain ⟨B, q, hq, hge1, hleB⟩ := exists_injective_forall_normAtPlace_bounds L v w₀
  intro hsum
  have htend := (hsum.comp_injective hq).tendsto_atTop_zero
  let C : ℝ := ∑ w : InfinitePlace K, |y w| * B ^ 2
  have hlow (n : ℕ) : Real.exp (-(π * C)) ≤
      ‖t.harmonicFactor (v + q n) * archGaussian y (v + q n)‖ := by
    have h1 : 1 ≤ ‖t.harmonicFactor (v + q n)‖ :=
      t.norm_harmonicFactor _ ▸ Finset.one_le_prod₀ fun w _ ↦ one_le_pow₀ (hge1 n w)
    have hsum_le : ∑ w, y w * normAtPlace w (v + q n) ^ 2 ≤ C := by
      refine Finset.sum_le_sum fun w _ ↦ ?_
      by_cases hw : w = w₀
      · exact hw ▸ (mul_nonpos_of_nonpos_of_nonneg hw₀ (sq_nonneg _)).trans (by positivity)
      · exact (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)).trans
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (normAtPlace_nonneg w _) (hleB n w hw) 2) (abs_nonneg _))
    have hexp : Real.exp (-(π * C)) ≤ ‖archGaussian y (v + q n)‖ := by
      rw [archGaussian_apply, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (by linarith [mul_le_mul_of_nonneg_left hsum_le Real.pi_pos.le])
    simpa [norm_mul] using mul_le_mul h1 hexp (Real.exp_pos _).le (norm_nonneg _)
  obtain ⟨n, hn⟩ := (htend.eventually (gt_mem_nhds (Real.exp_pos (-(π * C))))).exists
  exact (not_le_of_gt hn) (hlow n)

open scoped Classical in
/-- Over a full lattice `L` of `mixedSpace K`, the shifted harmonic-weighted archimedean Gaussian is
summable if and only if every parameter coordinate `y w` is positive. -/
theorem summable_harmonicFactor_mul_archGaussian_add_iff (t : ContinuousInfinityType K)
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] [IsZLattice ℝ L]
    (y : realSpace K) (v : mixedSpace K) :
    (Summable fun x : L ↦ t.harmonicFactor (v + x) * archGaussian y (v + x)) ↔ ∀ w, 0 < y w :=
  ⟨fun h ↦ by_contra fun hy ↦
      not_summable_norm_harmonicFactor_mul_archGaussian_add t L hy v h.norm,
    fun hy ↦ summable_harmonicFactor_mul_archGaussian_add t L y hy v⟩

open scoped Classical in
/-- Over a full lattice `L` of `mixedSpace K`, `t.harmonicFactor x * archGaussian y x` is summable
if and only if every parameter coordinate `y w` is positive. -/
theorem summable_harmonicFactor_mul_archGaussian_iff (t : ContinuousInfinityType K)
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] [IsZLattice ℝ L] (y : realSpace K) :
    (Summable fun x : L ↦ t.harmonicFactor x * archGaussian y x) ↔ ∀ w, 0 < y w := by
  simpa using summable_harmonicFactor_mul_archGaussian_add_iff t L y 0

open scoped Classical in
/-- **Shifted Poisson summation for a harmonic-weighted archimedean Gaussian** over a full lattice
`L` of `mixedSpace K`: transforms the shifted sum over `v + L` into a dual sum over
`mixedDual K L` (when any coordinate `y w ≤ 0`, both series fail to converge absolutely and vanish).
-/
theorem tsum_harmonicFactor_mul_archGaussian_add_eq_mixedDual (t : ContinuousInfinityType K)
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] [IsZLattice ℝ L]
    (y : realSpace K) (v : mixedSpace K) :
    ∑' ℓ : L, t.harmonicFactor (v + ℓ) * archGaussian y (v + ℓ) =
      (ZLattice.covolume L : ℂ)⁻¹ * (-I) ^ t.harmonicDegree * (((√(archNorm y))⁻¹ : ℝ) : ℂ) *
        ((∏ w : InfinitePlace K, (y w)⁻¹ ^ t.harmonicExponent w : ℝ) : ℂ) *
        ∑' m : mixedDual K L,
          t.harmonicFactor m * archGaussian y⁻¹ m * cexp (2 * π * I * mixedInner K v m) := by
  by_cases hy : ∀ w, 0 < y w
  · have hF : mixedFourier K (harmonicArchGaussianSchwartz t y hy) =
        mixedFourier K (fun x ↦ t.harmonicFactor x * archGaussian y x) :=
      congrArg _ (funext (harmonicArchGaussianSchwartz_apply t y hy))
    have h := tsum_eq_tsum_mixedDual_mixedFourier K L (harmonicArchGaussianSchwartz t y hy) v
    simp only [harmonicArchGaussianSchwartz_apply, hF,
      mixedFourier_harmonicFactor_mul_archGaussian t y hy] at h
    have hpull (m : mixedDual K L) :
        (-I) ^ t.harmonicDegree * (((√(archNorm y))⁻¹ : ℝ) : ℂ) *
            ((∏ w : InfinitePlace K, (y w)⁻¹ ^ t.harmonicExponent w : ℝ) : ℂ) *
            t.harmonicFactor (m : mixedSpace K) * archGaussian y⁻¹ m *
            cexp (2 * π * I * mixedInner K v m) =
          ((-I) ^ t.harmonicDegree * (((√(archNorm y))⁻¹ : ℝ) : ℂ) *
            ((∏ w : InfinitePlace K, (y w)⁻¹ ^ t.harmonicExponent w : ℝ) : ℂ)) *
            (t.harmonicFactor (m : mixedSpace K) * archGaussian y⁻¹ m *
              cexp (2 * π * I * mixedInner K v m)) := by ring
    simp_rw [hpull, tsum_mul_left] at h
    rw [h]; ring
  · have hlhs : ¬ Summable fun ℓ : L ↦ t.harmonicFactor (v + ℓ) * archGaussian y (v + ℓ) :=
      (summable_harmonicFactor_mul_archGaussian_add_iff t L y v).not.mpr hy
    have hy' : ¬ ∀ w, 0 < y⁻¹ w := fun h ↦ hy fun w ↦ inv_pos.mp (h w)
    have hrhs : ¬ Summable fun m : mixedDual K L ↦
        t.harmonicFactor (m : mixedSpace K) * archGaussian y⁻¹ m *
          cexp (2 * π * I * mixedInner K v m) := fun hsum ↦
      not_summable_norm_harmonicFactor_mul_archGaussian_add t (mixedDual K L) hy' 0 <|
        hsum.norm.congr fun m ↦ by
          simp [Complex.norm_exp]
    rw [tsum_eq_zero_of_not_summable hlhs, tsum_eq_zero_of_not_summable hrhs, mul_zero]

open scoped Classical in
/-- **Poisson summation for a harmonic-weighted archimedean Gaussian** over a full lattice `L` of
`mixedSpace K` at shift `0`. -/
theorem tsum_harmonicFactor_mul_archGaussian_eq_mixedDual (t : ContinuousInfinityType K)
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] [IsZLattice ℝ L]
    (y : realSpace K) :
    ∑' ℓ : L, t.harmonicFactor ℓ * archGaussian y ℓ =
      (ZLattice.covolume L : ℂ)⁻¹ * (-I) ^ t.harmonicDegree * (((√(archNorm y))⁻¹ : ℝ) : ℂ) *
        ((∏ w : InfinitePlace K, (y w)⁻¹ ^ t.harmonicExponent w : ℝ) : ℂ) *
        ∑' m : mixedDual K L, t.harmonicFactor m * archGaussian y⁻¹ m := by
  simpa [← mixedInnerBilin_apply] using
    tsum_harmonicFactor_mul_archGaussian_add_eq_mixedDual t L y 0

/-! ### The weighted archimedean gamma integral -/

/-- On the positive orthant, `archGaussian y x * t.archWeight y * archNorm y ^ (s / 2)` splits into
one factor per infinite place. -/
private theorem archGaussian_mul_archWeight_mul_archNorm_cpow_eq_prod
    (t : ContinuousInfinityType K) {y : realSpace K} (hy : ∀ w, 0 < y w) (x : mixedSpace K)
    (s : ℂ) :
    archGaussian y x * (t.archWeight y : ℂ) * (archNorm y : ℂ) ^ (s / 2) =
      ∏ w, (y w : ℂ) ^ (((mult w : ℂ) * s + t.harmonicExponent w) / 2) *
        (Real.exp (-(π * normAtPlace w x ^ 2 * y w)) : ℂ) := by
  have hnorm : ((archNorm y : ℝ) : ℂ) ^ (s / 2) = ∏ w, (y w : ℂ) ^ ((mult w : ℂ) * s / 2) := by
    rw [archNorm_apply, TauCeti.ofReal_prod_cpow _ fun w _ ↦ pow_nonneg (hy w).le _]
    refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [ofReal_pow, TauCeti.ofReal_pow_cpow (hy w).le, mul_div_assoc]
  have hweight : (t.archWeight y : ℂ) = ∏ w, (y w : ℂ) ^ ((t.harmonicExponent w : ℂ) / 2) := by
    rw [t.archWeight_def, ofReal_prod]
    exact Finset.prod_congr rfl fun w _ ↦ by rw [ofReal_cpow (hy w).le]; push_cast; rfl
  rw [archGaussian_apply, Finset.mul_sum, Real.exp_sum, ofReal_prod, hweight, hnorm,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  rw [add_div, cpow_add _ _ (ofReal_ne_zero.mpr (hy w).ne')]; ring_nf

/-- For `x` of nonzero norm and `s` in the local convergence half-plane
`∀ w, 0 < mult w * Re s + P_w`, the weighted archimedean Gaussian
`archGaussian y x * t.archWeight y * N(y)^(s / 2)` is integrable over `archHaar K`. -/
theorem integrable_archGaussian_mul_archWeight_mul_archNorm_cpow (t : ContinuousInfinityType K)
    {x : mixedSpace K} (hx : mixedEmbedding.norm x ≠ 0) {s : ℂ}
    (hs : ∀ w : InfinitePlace K, 0 < (mult w : ℝ) * s.re + t.harmonicExponent w) :
    Integrable (fun y ↦ archGaussian y x * (t.archWeight y : ℂ) * (archNorm y : ℂ) ^ (s / 2))
      (archHaar K) := by
  have ha (w : InfinitePlace K) : 0 < normAtPlace w x :=
    (normAtPlace_nonneg w x).lt_of_ne' (mixedEmbedding.norm_ne_zero_iff.mp hx w)
  have hre (w : InfinitePlace K) : 0 < ((mult w : ℂ) * s + t.harmonicExponent w).re := by
    simpa using hs w
  have hint := Integrable.fintype_prod (μ := fun _ : InfinitePlace K ↦ multHaar)
    fun w ↦ integrable_multHaar_cpow_div_two_mul_exp_neg_pi_mul_sq (ha w).ne' (hre w)
  rw [← archHaar_def] at hint
  refine hint.congr ?_
  filter_upwards [ae_archHaar_pos] with y hy
  exact (archGaussian_mul_archWeight_mul_archNorm_cpow_eq_prod t hy x s).symm

private theorem integral_archGaussian_mul_archWeight_mul_archNorm_cpow_of_ne_zero
    (t : ContinuousInfinityType K) {x : mixedSpace K} (hx : mixedEmbedding.norm x ≠ 0) {s : ℂ}
    (hs : ∀ w : InfinitePlace K, 0 < (mult w : ℝ) * s.re + t.harmonicExponent w) :
    (∏ w, ∫ u, (u : ℂ) ^ (((mult w : ℂ) * s + t.harmonicExponent w) / 2) *
        (Real.exp (-(π * normAtPlace w x ^ 2 * u)) : ℂ) ∂multHaar) =
      (∏ w : InfinitePlace K, Gammaℝ (mult w * s + t.harmonicExponent w)) *
        ((∏ w : InfinitePlace K, normAtPlace w x ^ t.harmonicExponent w : ℝ) : ℂ)⁻¹ *
        (mixedEmbedding.norm x : ℂ) ^ (-s) := by
  have ha (w : InfinitePlace K) : 0 < normAtPlace w x :=
    (normAtPlace_nonneg w x).lt_of_ne' (mixedEmbedding.norm_ne_zero_iff.mp hx w)
  have hre (w : InfinitePlace K) : 0 < ((mult w : ℂ) * s + t.harmonicExponent w).re := by
    simpa using hs w
  have hsplit (w : InfinitePlace K) :
      (normAtPlace w x : ℂ) ^ (-((mult w : ℂ) * s + t.harmonicExponent w)) =
        ((normAtPlace w x ^ t.harmonicExponent w : ℝ) : ℂ)⁻¹ *
          (normAtPlace w x : ℂ) ^ ((mult w : ℂ) * -s) := by
    rw [neg_add, add_comm, ← mul_neg, cpow_add _ _ (ofReal_ne_zero.mpr (ha w).ne'), cpow_neg,
      cpow_natCast, ofReal_pow]
  have hnorm : ((mixedEmbedding.norm x : ℝ) : ℂ) ^ (-s) =
      ∏ w, (normAtPlace w x : ℂ) ^ ((mult w : ℂ) * -s) := by
    rw [mixedEmbedding.norm_apply, TauCeti.ofReal_prod_cpow _ fun w _ ↦ pow_nonneg (ha w).le _]
    exact Finset.prod_congr rfl fun w _ ↦ by rw [ofReal_pow, TauCeti.ofReal_pow_cpow (ha w).le]
  calc (∏ w, ∫ u, (u : ℂ) ^ (((mult w : ℂ) * s + t.harmonicExponent w) / 2) *
          (Real.exp (-(π * normAtPlace w x ^ 2 * u)) : ℂ) ∂multHaar)
      = ∏ w, Gammaℝ (mult w * s + t.harmonicExponent w) *
          (normAtPlace w x : ℂ) ^ (-((mult w : ℂ) * s + t.harmonicExponent w)) := by
        refine Finset.prod_congr rfl fun w _ ↦ ?_
        rw [integral_multHaar_cpow_div_two_mul_exp_neg_pi_mul_sq _ (hre w), abs_of_pos (ha w)]
    _ = _ := by
        simp_rw [hsplit]
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ofReal_prod, Finset.prod_inv_distrib,
          hnorm, mul_assoc]

/-- **The weighted archimedean gamma integral**: on the half-plane `∀ w, 0 < mult w * Re s + P_w`,
integrating `archGaussian y x * t.archWeight y * N(y)^(s / 2)` over `archHaar K` yields
`(∏_w Γ_ℝ(mult w * s + P_w)) * (∏_w |x_w|^P_w)⁻¹ * |N(x)|^(-s)` (when `mixedEmbedding.norm x = 0`,
both sides vanish). -/
theorem integral_archGaussian_mul_archWeight_mul_archNorm_cpow (t : ContinuousInfinityType K)
    (x : mixedSpace K) {s : ℂ}
    (hs : ∀ w : InfinitePlace K, 0 < (mult w : ℝ) * s.re + t.harmonicExponent w) :
    ∫ y, archGaussian y x * (t.archWeight y : ℂ) * (archNorm y : ℂ) ^ (s / 2) ∂archHaar K =
      (∏ w : InfinitePlace K, Gammaℝ (mult w * s + t.harmonicExponent w)) *
        ((∏ w : InfinitePlace K, normAtPlace w x ^ t.harmonicExponent w : ℝ) : ℂ)⁻¹ *
        (mixedEmbedding.norm x : ℂ) ^ (-s) := by
  have hprod :
      ∫ y, archGaussian y x * (t.archWeight y : ℂ) * (archNorm y : ℂ) ^ (s / 2) ∂archHaar K =
        ∏ w, ∫ u, (u : ℂ) ^ (((mult w : ℂ) * s + t.harmonicExponent w) / 2) *
          (Real.exp (-(π * normAtPlace w x ^ 2 * u)) : ℂ) ∂multHaar := by
    calc ∫ y, archGaussian y x * (t.archWeight y : ℂ) * (archNorm y : ℂ) ^ (s / 2) ∂archHaar K
        = ∫ y, ∏ w, (y w : ℂ) ^ (((mult w : ℂ) * s + t.harmonicExponent w) / 2) *
            (Real.exp (-(π * normAtPlace w x ^ 2 * y w)) : ℂ) ∂archHaar K :=
          integral_congr_ae (ae_archHaar_pos.mono fun y hy ↦
            archGaussian_mul_archWeight_mul_archNorm_cpow_eq_prod t hy x s)
      _ = _ := by
          rw [archHaar_def]
          exact integral_fintype_prod_eq_prod fun w (u : ℝ) ↦
            (u : ℂ) ^ (((mult w : ℂ) * s + t.harmonicExponent w) / 2) *
              (Real.exp (-(π * normAtPlace w x ^ 2 * u)) : ℂ)
  rw [hprod]
  by_cases hx : mixedEmbedding.norm x = 0
  · obtain ⟨w₀, hw₀⟩ : ∃ w₀ : InfinitePlace K, normAtPlace w₀ x = 0 := by
      by_contra! hall; exact (mixedEmbedding.norm_ne_zero_iff.mpr hall) hx
    rw [Finset.prod_eq_zero (Finset.mem_univ w₀) (by simp [hw₀, integral_multHaar_cpow_eq_zero])]
    rcases eq_or_ne s 0 with rfl | hs0
    · have hP : t.harmonicExponent w₀ ≠ 0 := by simpa using (hs w₀).ne'
      have hp0 : (∏ w : InfinitePlace K, normAtPlace w x ^ t.harmonicExponent w) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ w₀) (by simp [hw₀, zero_pow hP])
      simp [hp0]
    · simp [hx, zero_cpow (neg_ne_zero.mpr hs0)]
  · exact integral_archGaussian_mul_archWeight_mul_archNorm_cpow_of_ne_zero t hx hs

end TauCeti.LFunctions
