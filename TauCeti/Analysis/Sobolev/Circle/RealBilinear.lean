/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import TauCeti.Analysis.Normed.Operator.ComplexLinearPart
public import TauCeti.Analysis.Sobolev.Circle.Basic
import Mathlib.Tactic.Module
import TauCeti.Analysis.Normed.Lp.DiscreteConvolution
import TauCeti.Analysis.Normed.Module.RCLike.Basic
import TauCeti.Analysis.Sobolev.Circle.Algebra
import TauCeti.Analysis.Sobolev.Circle.Duality

/-!
# Real-linear maps and real-bilinear convolutions on circle Sobolev spaces

Nonlinear differential calculus on the circle Sobolev spaces `H^s(E)` — Fréchet derivatives over
`ℝ`, Hadamard segment averages, and the chain rule `(f ∘ u)' = df(u) u'` — requires continuous
*real*-linear operators and *real*-bilinear products extending `CircleSobolev.mapCLM` and
`CircleSobolev.convolution`. Decomposing `Ψ : E →L[ℝ] F` into complex-linear and antilinear parts
yields `TauCeti.CircleSobolev.mapRealCLM`; decomposing `L : E →L[ℝ] E' →L[ℝ] F` into its four
`(ℂ, ℂ)`-sesquilinear parts yields `TauCeti.CircleSobolev.realConvolution` (`s > 1/2`) and
`TauCeti.CircleSobolev.realConvolutionAsym` (`0 ≤ t`, `t + 1/2 < r`, `H^r(E) × H^t(E') → H^t(F)`).

## Main definitions and statements

* `TauCeti.CircleSobolev.mapRealCLM`, `mapRealCLM_id`, `mapRealCLM_comp`, and
  `toContinuousMap_mapRealCLM_apply`: functorial real-linear postcomposition on `H^s`.
* `TauCeti.CircleSobolev.realConvolution`, `realConvolutionAsym`,
  `toContinuousMap_realConvolution_apply`, `norm_realConvolutionAsym_le`, and
  `coeff_realConvolutionAsym`: pointwise evaluation, norm bounds, and Fourier-coefficient formulas.

## References

* M. E. Taylor, *Partial Differential Equations III*, Chapter 13, Section 3.
* T. Runst and W. Sickel, *Sobolev Spaces of Fractional Order, Nemytskij Operators, and Nonlinear
  Partial Differential Equations*, de Gruyter, 1996, Chapter 4.
-/

public section

noncomputable section

open Complex
open scoped DiscreteConvolution ENNReal

open DiscreteConvolution (AddConvolutionExists AddConvolutionExistsAt addConvolution_single_apply
  addFiberEquivSub enorm_addConvolution_le single_addConvolution_apply
  tsum_sq_mul_addRingConvolution_le_of_le_mul')

namespace TauCeti
namespace CircleSobolev

variable {s t r : ℝ} {E E' F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E'] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

private theorem i_smul_i_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (v : V) :
    I • I • v = -v := by rw [smul_smul, I_mul_I, neg_one_smul]

/-! ### Real-linear postcomposition -/

section RealLinear

private theorem weight_mul_norm_complexAntilinearPart_le (Ψ : E →L[ℝ] F) (a : CircleSobolev s E)
    (n : ℤ) : weight s n * ‖Ψ.complexAntilinearPart (a.coeff (-n))‖ ≤
      ‖Ψ‖ * (weight s n * ‖(reflect a).coeff n‖) := by
  have h : ‖Ψ.complexAntilinearPart (a.coeff (-n))‖ ≤ ‖Ψ‖ * ‖a.coeff (-n)‖ := by
    rw [Ψ.complexAntilinearPart_apply]; exact norm_two_inv_smul_add_le (𝕜 := ℝ) (Ψ.le_opNorm _)
      (by simpa [norm_smul] using Ψ.le_opNorm (I • a.coeff (-n)))
  simpa [mul_left_comm] using mul_le_mul_of_nonneg_left h (weight_nonneg s n)

private def mapAntilinearAux (Ψ : E →L[ℝ] F) (a : CircleSobolev s E) : CircleSobolev s F :=
  ⟨fun n ↦ Ψ.complexAntilinearPart (a.coeff (-n)),
    memℓp_of_forall_le (weight_mul_norm_complexAntilinearPart_le Ψ a)⟩

@[simp] private theorem coeff_mapAntilinearAux (Ψ : E →L[ℝ] F) (a : CircleSobolev s E) (n : ℤ) :
    (mapAntilinearAux Ψ a).coeff n = Ψ.complexAntilinearPart (a.coeff (-n)) := rfl

private def mapRealAux (Ψ : E →L[ℝ] F) (a : CircleSobolev s E) : CircleSobolev s F :=
  mapCLM Ψ.complexLinearPart a + mapAntilinearAux Ψ a

private theorem norm_mapRealAux_le (Ψ : E →L[ℝ] F) (a : CircleSobolev s E) :
    ‖mapRealAux Ψ a‖ ≤ (2 * ‖Ψ‖) * ‖a‖ := by
  have hlin : ‖mapCLM Ψ.complexLinearPart a‖ ≤ ‖Ψ‖ * ‖a‖ := norm_le_of_forall_le fun n ↦ by
    have h : ‖Ψ.complexLinearPart (a.coeff n)‖ ≤ ‖Ψ‖ * ‖a.coeff n‖ := by
      rw [Ψ.complexLinearPart_apply, sub_eq_add_neg]; exact norm_two_inv_smul_add_le (𝕜 := ℝ)
        (Ψ.le_opNorm _) (by simpa [norm_smul] using Ψ.le_opNorm (I • a.coeff n))
    simpa only [coeff_mapCLM, mul_left_comm] using mul_le_mul_of_nonneg_left h (weight_nonneg s n)
  have hanti : ‖mapAntilinearAux Ψ a‖ ≤ ‖Ψ‖ * ‖a‖ := by
    simpa using norm_le_of_forall_le (a := reflect a) (b := mapAntilinearAux Ψ a)
      (weight_mul_norm_complexAntilinearPart_le Ψ a)
  rw [mapRealAux]; linarith [norm_add_le (mapCLM Ψ.complexLinearPart a) (mapAntilinearAux Ψ a)]

/-- Action of a continuous real-linear operator `Ψ : E →L[ℝ] F` on `H^s`, sending `a` to the
element with `n`-th coefficient `Ψ.complexLinearPart (a.coeff n) +
Ψ.complexAntilinearPart (a.coeff (-n))`. On continuous representatives (`s > 1/2`) this is
pointwise application `x ↦ Ψ (a x)` (`toContinuousMap_mapRealCLM_apply`). -/
def mapRealCLM : (E →L[ℝ] F) →L[ℝ] CircleSobolev s E →L[ℝ] CircleSobolev s F :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ mapRealAux
      (fun _ _ _ ↦ by
        ext n; simp only [mapRealAux, coeff_add, Pi.add_apply, coeff_mapCLM, coeff_mapAntilinearAux,
          ContinuousLinearMap.complexLinearPart_add, ContinuousLinearMap.complexAntilinearPart_add,
          add_apply]; abel)
      (fun _ _ _ ↦ by
        ext n; simp only [mapRealAux, coeff_add, coeff_real_smul, Pi.add_apply, Pi.smul_apply,
          coeff_mapCLM, coeff_mapAntilinearAux, ContinuousLinearMap.complexLinearPart_smul,
          ContinuousLinearMap.complexAntilinearPart_smul, smul_apply, smul_add])
      (fun _ _ _ ↦ by
        ext n; simp only [mapRealAux, coeff_add, Pi.add_apply, coeff_mapCLM, coeff_mapAntilinearAux,
          map_add]; abel)
      (fun c _ _ ↦ by
        ext n; simp only [mapRealAux, ← Complex.coe_smul c, smul_add, map_smul, coeff_add,
          coeff_smul, Pi.add_apply, Pi.smul_apply, coeff_mapAntilinearAux, map_smulₛₗ,
          Complex.conj_ofReal]))
    2 fun Ψ a ↦ by simpa only [LinearMap.mk₂_apply, mul_assoc] using norm_mapRealAux_le Ψ a

@[simp] theorem coeff_mapRealCLM (Ψ : E →L[ℝ] F) (a : CircleSobolev s E) (n : ℤ) :
    (mapRealCLM Ψ a).coeff n =
      Ψ.complexLinearPart (a.coeff n) + Ψ.complexAntilinearPart (a.coeff (-n)) := by
  simp [mapRealCLM, mapRealAux]

theorem norm_mapRealCLM_le (Ψ : E →L[ℝ] F) (a : CircleSobolev s E) :
    ‖mapRealCLM Ψ a‖ ≤ 2 * ‖Ψ‖ * ‖a‖ := norm_mapRealAux_le Ψ a

@[simp] theorem mapRealCLM_restrictScalars (L : E →L[ℂ] F) (a : CircleSobolev s E) :
    mapRealCLM (L.restrictScalars ℝ) a = mapCLM L a :=
  CircleSobolev.ext <| funext fun n ↦ by rw [coeff_mapRealCLM]; simp

/-- `mapRealCLM` sends the identity real-linear operator to the identity on `H^s`. -/
@[simp] theorem mapRealCLM_id (a : CircleSobolev s E) : mapRealCLM (.id ℝ E) a = a := by
  ext n; simp only [coeff_mapRealCLM, ContinuousLinearMap.complexLinearPart_apply,
    ContinuousLinearMap.complexAntilinearPart_apply, ContinuousLinearMap.id_apply, i_smul_i_smul]
  module

/-- `mapRealCLM` respects composition of continuous real-linear operators. -/
@[simp] theorem mapRealCLM_comp (Φ : F →L[ℝ] G) (Ψ : E →L[ℝ] F) (a : CircleSobolev s E) :
    mapRealCLM (Φ.comp Ψ) a = mapRealCLM Φ (mapRealCLM Ψ a) := by
  ext n; simp only [coeff_mapRealCLM, neg_neg, ContinuousLinearMap.complexLinearPart_apply,
    ContinuousLinearMap.complexAntilinearPart_apply, ContinuousLinearMap.comp_apply, map_add,
    map_sub, map_smul, map_neg, smul_add, smul_sub, smul_comm I (2⁻¹ : ℝ), i_smul_i_smul, smul_neg]
  module

@[simp] theorem mapRealCLM_inclusion (h : t ≤ s) (Ψ : E →L[ℝ] F) (a : CircleSobolev s E) :
    mapRealCLM Ψ (inclusion h a) = inclusion h (mapRealCLM Ψ a) :=
  CircleSobolev.ext <| funext fun _ ↦ by simp

@[simp] theorem mapRealCLM_single_zero (Ψ : E →L[ℝ] F) (v : E) :
    mapRealCLM Ψ (single (s := s) 0 v) = single 0 (Ψ v) := by
  ext n; rw [coeff_mapRealCLM]; rcases eq_or_ne n 0 with rfl | hn
  · simp only [coeff_single, Pi.single_eq_same, neg_zero,
      Ψ.complexLinearPart_add_complexAntilinearPart_apply]
  · simp [hn, neg_eq_zero.not.2 hn]

/-- **On continuous representatives `mapRealCLM` acts pointwise:** for `s > 1/2`, the continuous
function attached to `mapRealCLM Ψ a` is `x ↦ Ψ (a x)`. -/
@[simp] theorem toContinuousMap_mapRealCLM_apply (T : ℝ) [Fact (0 < T)] [CompleteSpace E]
    [CompleteSpace F] (hs : 1 / 2 < s) (Ψ : E →L[ℝ] F) (a : CircleSobolev s E) (x : AddCircle T) :
    toContinuousMap T hs (mapRealCLM Ψ a) x = Ψ (toContinuousMap T hs a x) := by
  have hsplit : mapRealCLM Ψ a = mapCLM Ψ.complexLinearPart a + mapAntilinearAux Ψ a :=
    CircleSobolev.ext <| funext fun n ↦ by simp [mapAntilinearAux]
  rw [hsplit, map_add, ContinuousMap.add_apply, toContinuousMap_mapCLM_apply,
    ← Ψ.complexLinearPart_add_complexAntilinearPart_apply (toContinuousMap T hs a x)]; congr 1
  have hA := (hasSum_toContinuousMap T hs a).mapL (ContinuousMap.evalCLM ℂ x)
  simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply', ContinuousMap.const_apply]
    at hA
  refine ((hasSum_toContinuousMap T hs (mapAntilinearAux Ψ a)).mapL
    (ContinuousMap.evalCLM ℂ x)).unique ?_
  convert ((Equiv.neg ℤ).hasSum_iff.2 hA).mapL Ψ.complexAntilinearPart using 1
  ext n; simp [mapAntilinearAux, ContinuousMap.smul_apply']

end RealLinear

/-! ### Real-bilinear coefficient convolutions (symmetric and asymmetric) -/

section CoeffConvolution

variable [CompleteSpace F]

private def coeffConvolution (hs : 1 / 2 < s) (B : G →L[ℝ] E' →L[ℝ] F) :
    CircleSobolev s G →L[ℝ] CircleSobolev s E' →L[ℝ] CircleSobolev s F :=
  mkCoeffConvolution (2 ^ (s + 1) * √(∑' n, weight (-(2 * s)) n)) B
    (addConvolutionExists_coeff hs B) (memℓp_weight_smul_addConvolution_coeff hs B)
    fun a b ↦ norm_le_of_coeff_eq_addConvolution hs B a b rfl

@[simp] private theorem coeff_coeffConvolution (hs : 1 / 2 < s) (B : G →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev s G) (b : CircleSobolev s E') :
    (coeffConvolution hs B a b).coeff = a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff :=
  coeff_mkCoeffConvolution _ _ _ _ _ a b

private theorem norm_coeffConvolution_le (hs : 1 / 2 < s) (B : G →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev s G) (b : CircleSobolev s E') :
    ‖coeffConvolution hs B a b‖ ≤
      2 ^ (s + 1) * √(∑' n, weight (-(2 * s)) n) * ‖B‖ * ‖a‖ * ‖b‖ :=
  norm_mkCoeffConvolution_le _ _ _ _ _ a b

private theorem addConvolutionExists_asym (hr : 0 ≤ r) (ht : 0 ≤ t) (B : G →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev r G) (b : CircleSobolev t E') :
    AddConvolutionExists B.toLinearMap₁₂ a.coeff b.coeff := fun n ↦ by
  unfold AddConvolutionExistsAt; rw [← (addFiberEquivSub n).summable_iff]
  have ha : Summable fun m : ℤ ↦ ‖a.coeff (n - m)‖ ^ 2 := by
    simpa [Function.comp_def, weight_zero_left] using (Equiv.subLeft n).summable_iff.2
      (hasSum_sq_weight_mul_norm_coeff (inclusion hr a)).summable
  have hb : Summable fun m : ℤ ↦ ‖b.coeff m‖ ^ 2 := by
    simpa [weight_zero_left] using (hasSum_sq_weight_mul_norm_coeff (inclusion ht b)).summable
  refine Summable.of_norm_bounded (((ha.add hb).mul_left (2⁻¹ : ℝ)).mul_left ‖B‖) fun m ↦ ?_
  simp only [Function.comp_apply, DiscreteConvolution.coe_addFiberEquivSub_apply,
    ContinuousLinearMap.toLinearMap₁₂_apply]
  refine (B.le_opNorm₂ _ _).trans ?_; rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (by nlinarith [sq_nonneg (‖a.coeff (n - m)‖ - ‖b.coeff m‖)]) (norm_nonneg B)

end CoeffConvolution

/-- Bound the `weight t`-weighted `ℓ¹` sum of `a : H^r` (`t + 1/2 < r`) in `ℝ≥0∞`. -/
private theorem tsum_ofReal_weight_mul_enorm_coeff_le (htr : t + 1 / 2 < r)
    (a : CircleSobolev r G) : ∑' n, ENNReal.ofReal (weight t n) * ‖a.coeff n‖ₑ ≤
      ENNReal.ofReal √(∑' n, weight (-(2 * (r - t))) n) * ‖a‖ₑ := by
  have hrt : 1 / 2 < r - t := by linarith
  let a' := weightEquiv r (r - t) G a
  have hterm (n : ℤ) :
      ENNReal.ofReal (weight t n) * ‖a.coeff n‖ₑ = ENNReal.ofReal ‖a'.coeff n‖ := by
    rw [coeff_weightEquiv, sub_sub_cancel, norm_smul, norm_weight,
      ENNReal.ofReal_mul (weight_nonneg t n), ofReal_norm]
  simp_rw [hterm, ← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ norm_nonneg _)
    (summable_norm_coeff hrt a'), ← ofReal_norm, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  exact ENNReal.ofReal_le_ofReal
    (by simpa only [LinearIsometryEquiv.norm_map, a'] using tsum_norm_coeff_le hrt a')

/-- Convert a real weighted square `(weight t n * ‖v‖) ^ 2` into `ℝ≥0∞`. -/
private theorem ofReal_sq_weight_mul_norm {X : Type*} [SeminormedAddCommGroup X] (t : ℝ) (n : ℤ)
    (v : X) : ENNReal.ofReal ((weight t n * ‖v‖) ^ 2) =
      (ENNReal.ofReal (weight t n) * ‖v‖ₑ) ^ 2 := by
  rw [ENNReal.ofReal_pow (mul_nonneg (weight_nonneg t n) (norm_nonneg v)),
    ENNReal.ofReal_mul (weight_nonneg t n), ofReal_norm]

/-- Unconditional `ℝ≥0∞` asymmetric weighted `ℓ²` bound for discrete bilinear convolution on `ℤ`. -/
private theorem tsum_sq_ofReal_weight_mul_enorm_addConvolution_asym_le (ht : 0 ≤ t)
    (B : G →L[ℝ] E' →L[ℝ] F) (f : ℤ → G) (g : ℤ → E') :
    ∑' n : ℤ, (ENNReal.ofReal (weight t n) * ‖(f ⋆₊[B.toLinearMap₁₂] g) n‖ₑ) ^ 2 ≤
      ‖B‖ₑ ^ 2 * (∑' m, ENNReal.ofReal (weight t m) * ‖f m‖ₑ) ^ 2 *
        ∑' k, (ENNReal.ofReal (weight t k) * ‖g k‖ₑ) ^ 2 := by
  set ω : ℤ → ℝ≥0∞ := fun n ↦ ENNReal.ofReal (weight t n)
  have hω (m k : ℤ) : ω (m + k) ≤ ω m * ω k := by
    simp only [ω, ← ENNReal.ofReal_mul (weight_nonneg t m)]
    exact ENNReal.ofReal_le_ofReal (by simpa [abs_of_nonneg ht] using weight_add_le t m k)
  calc ∑' n : ℤ, (ω n * ‖(f ⋆₊[B.toLinearMap₁₂] g) n‖ₑ) ^ 2
      ≤ ‖B‖ₑ ^ 2 * ∑' n, (ω n * ((‖f ·‖ₑ) ⋆ᵣ₊ (‖g ·‖ₑ)) n) ^ 2 := by
        rw [← ENNReal.tsum_mul_left]; refine _root_.tsum_le_tsum fun n ↦ ?_
        rw [← mul_pow, mul_left_comm]; gcongr; exact enorm_addConvolution_le B f g n
    _ ≤ ‖B‖ₑ ^ 2 * ((∑' m, ω m * ‖f m‖ₑ) ^ 2 * ∑' k, (ω k * ‖g k‖ₑ) ^ 2) := by
        gcongr; exact tsum_sq_mul_addRingConvolution_le_of_le_mul' hω _ _
    _ = _ := by ring

private theorem ofReal_tsum_sq_weight_mul_norm_addConvolution_asym_le (ht : 0 ≤ t)
    (htr : t + 1 / 2 < r) (B : G →L[ℝ] E' →L[ℝ] F) (a : CircleSobolev r G)
    (b : CircleSobolev t E') :
    ∑' n : ℤ, ENNReal.ofReal ((weight t n * ‖(a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff) n‖) ^ 2) ≤
      ENNReal.ofReal ((√(∑' n, weight (-(2 * (r - t))) n) * ‖B‖ * ‖a‖ * ‖b‖) ^ 2) := by
  -- Identify the weighted `ℓ²` coefficient sum of `b : H^t` with `‖b‖ₑ ^ 2` and combine bounds.
  have hb_eq : ∑' k, (ENNReal.ofReal (weight t k) * ‖b.coeff k‖ₑ) ^ 2 = ‖b‖ₑ ^ 2 := by
    simp_rw [← ofReal_sq_weight_mul_norm, ← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ sq_nonneg _)
      (hasSum_sq_weight_mul_norm_coeff b).summable, (hasSum_sq_weight_mul_norm_coeff b).tsum_eq,
      ENNReal.ofReal_pow (norm_nonneg b), ofReal_norm]
  have hRHS : ENNReal.ofReal ((√(∑' n, weight (-(2 * (r - t))) n) * ‖B‖ * ‖a‖ * ‖b‖) ^ 2) =
      ‖B‖ₑ ^ 2 * (ENNReal.ofReal √(∑' n, weight (-(2 * (r - t))) n) * ‖a‖ₑ) ^ 2 * ‖b‖ₑ ^ 2 := by
    simp (discharger := positivity) only [ENNReal.ofReal_pow, ENNReal.ofReal_mul, ofReal_norm]
    rw [eNorm_eq_nnNorm B, ENNReal.coe_nnreal_eq ‖B‖₊, coe_nnNorm B]; ring
  simp_rw [ofReal_sq_weight_mul_norm, hRHS]
  refine (tsum_sq_ofReal_weight_mul_enorm_addConvolution_asym_le ht B a.coeff b.coeff).trans ?_
  have := tsum_ofReal_weight_mul_enorm_coeff_le htr a
  rw [hb_eq]; gcongr

private theorem memℓp_asym (ht : 0 ≤ t) (htr : t + 1 / 2 < r) (B : G →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev r G) (b : CircleSobolev t E') :
    Memℓp (fun n ↦ weight t n • (a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff) n) 2 :=
  (memℓp_weight_smul_iff _).2 <| (ENNReal.summable_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (ofReal_tsum_sq_weight_mul_norm_addConvolution_asym_le ht htr B a b))).congr
    fun _ ↦ ENNReal.toReal_ofReal (sq_nonneg _)

private theorem norm_coeffConvolutionAsymAux_le (ht : 0 ≤ t) (htr : t + 1 / 2 < r)
    (B : G →L[ℝ] E' →L[ℝ] F) (a : CircleSobolev r G) (b : CircleSobolev t E') :
    ‖(⟨a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff, memℓp_asym ht htr B a b⟩ : CircleSobolev t F)‖ ≤
      √(∑' n, weight (-(2 * (r - t))) n) * ‖B‖ * ‖a‖ * ‖b‖ := by
  set w : CircleSobolev t F := ⟨_, memℓp_asym ht htr B a b⟩
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [← ENNReal.ofReal_le_ofReal_iff (sq_nonneg _), ← (hasSum_sq_weight_mul_norm_coeff w).tsum_eq,
    ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ sq_nonneg _)
      (hasSum_sq_weight_mul_norm_coeff w).summable]
  exact ofReal_tsum_sq_weight_mul_norm_addConvolution_asym_le ht htr B a b

private def coeffConvolutionAsym [CompleteSpace F] (ht : 0 ≤ t) (htr : t + 1 / 2 < r)
    (B : G →L[ℝ] E' →L[ℝ] F) :
    CircleSobolev r G →L[ℝ] CircleSobolev t E' →L[ℝ] CircleSobolev t F :=
  mkCoeffConvolution √(∑' n, weight (-(2 * (r - t))) n) B
    (addConvolutionExists_asym (by linarith) ht B) (memℓp_asym ht htr B)
    (norm_coeffConvolutionAsymAux_le ht htr B)

@[simp] private theorem coeff_coeffConvolutionAsym [CompleteSpace F] (ht : 0 ≤ t)
    (htr : t + 1 / 2 < r) (B : G →L[ℝ] E' →L[ℝ] F) (a : CircleSobolev r G)
    (b : CircleSobolev t E') :
    (coeffConvolutionAsym ht htr B a b).coeff = a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff :=
  coeff_mkCoeffConvolution _ _ _ _ _ a b

private theorem norm_coeffConvolutionAsym_le [CompleteSpace F] (ht : 0 ≤ t)
    (htr : t + 1 / 2 < r) (B : G →L[ℝ] E' →L[ℝ] F) (a : CircleSobolev r G)
    (b : CircleSobolev t E') :
    ‖coeffConvolutionAsym ht htr B a b‖ ≤
      √(∑' n, weight (-(2 * (r - t))) n) * ‖B‖ * ‖a‖ * ‖b‖ :=
  norm_mkCoeffConvolution_le _ _ _ _ _ a b

/-! ### Public real-bilinear convolutions via four-part sesquilinear decomposition -/

private def reflectRealCLM : CircleSobolev s G →L[ℝ] CircleSobolev s G :=
  (reflect : CircleSobolev s G ≃ₗᵢ[ℂ] CircleSobolev s G).toLinearIsometry.toContinuousLinearMap
    |>.restrictScalars ℝ
private def reflectIf (b : Bool) : CircleSobolev s G →L[ℝ] CircleSobolev s G :=
  if b then reflectRealCLM else .id ℝ _
private theorem norm_reflectIf (b : Bool) (a : CircleSobolev s G) : ‖reflectIf b a‖ = ‖a‖ := by
  cases b <;> simp [reflectIf, reflectRealCLM]
@[simp] private theorem coeff_reflectIf (b : Bool) (a : CircleSobolev s G) (n : ℤ) :
    (reflectIf b a).coeff n = a.coeff (if b then -n else n) := by
  cases b <;> simp [reflectIf, reflectRealCLM]
@[simp] private theorem reflectIf_single (b : Bool) (k : ℤ) (v : G) :
    reflectIf b (single (s := s) k v) = single (if b then -k else k) v :=
  CircleSobolev.ext <| funext fun _ ↦ by cases b <;> simp [Pi.single_apply, neg_eq_iff_eq_neg]
private theorem reflectIf_inclusion (b : Bool) (h : t ≤ s) (a : CircleSobolev s G) :
    reflectIf b (inclusion h a) = inclusion h (reflectIf b a) :=
  CircleSobolev.ext <| funext fun _ ↦ by simp
private theorem norm_sum_bool_prod_le (K : ℝ) (f : Bool × Bool → CircleSobolev s F)
    (hf : ∀ p, ‖f p‖ ≤ K) : ‖∑ p : Bool × Bool, f p‖ ≤ 4 * K :=
  (norm_sum_le _ _).trans <| (Finset.sum_le_sum fun p _ ↦ hf p).trans_eq (by simp)

section PublicConvolutions
variable [CompleteSpace F]

/-- **Symmetric real-bilinear product on `H^s`, `s > 1/2` (`x ↦ L (a x) (b x)`).** -/
def realConvolution (hs : 1 / 2 < s) (L : E →L[ℝ] E' →L[ℝ] F) :
    CircleSobolev s E →L[ℝ] CircleSobolev s E' →L[ℝ] CircleSobolev s F :=
  ∑ p : Bool × Bool, (((coeffConvolution hs (L.sesquiPart p.1 p.2)).comp
    (reflectIf p.1)).flip.comp (reflectIf p.2)).flip

private theorem realConvolution_apply (hs : 1 / 2 < s) (L : E →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev s E) (b : CircleSobolev s E') :
    realConvolution hs L a b = ∑ p : Bool × Bool,
      coeffConvolution hs (L.sesquiPart p.1 p.2) (reflectIf p.1 a) (reflectIf p.2 b) := by
  simp [realConvolution]

/-- **Product estimate for `realConvolution` on `H^s`, `s > 1/2`.** -/
theorem norm_realConvolution_le (hs : 1 / 2 < s) (L : E →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev s E) (b : CircleSobolev s E') :
    ‖realConvolution hs L a b‖ ≤
      2 ^ (s + 3) * √(∑' n, weight (-(2 * s)) n) * ‖L‖ * ‖a‖ * ‖b‖ := by
  rw [realConvolution_apply]
  refine (norm_sum_bool_prod_le (2 ^ (s + 1) * √(∑' n, weight (-(2 * s)) n) * ‖L‖ * ‖a‖ * ‖b‖) _
    fun p ↦ ?_).trans_eq ?_
  · refine (norm_coeffConvolution_le hs _ _ _).trans ?_
    rw [norm_reflectIf, norm_reflectIf]; have := L.norm_sesquiPart_le p.1 p.2; gcongr
  · have h22 : (4 : ℝ) = 2 ^ (2 : ℝ) := by norm_num
    have h4 : (4 : ℝ) * 2 ^ (s + 1) = 2 ^ (s + 3) := by
      rw [h22, ← Real.rpow_add two_pos]
      exact congrArg ((2 : ℝ) ^ ·) (by ring)
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, h4]

/-- **Asymmetric real-bilinear product `H^r(E) × H^t(E') → H^t(F)` (`0 ≤ t`, `t + 1/2 < r`).** -/
def realConvolutionAsym (ht : 0 ≤ t) (htr : t + 1 / 2 < r) (L : E →L[ℝ] E' →L[ℝ] F) :
    CircleSobolev r E →L[ℝ] CircleSobolev t E' →L[ℝ] CircleSobolev t F :=
  ∑ p : Bool × Bool, (((coeffConvolutionAsym ht htr (L.sesquiPart p.1 p.2)).comp
    (reflectIf p.1)).flip.comp (reflectIf p.2)).flip

private theorem realConvolutionAsym_apply (ht : 0 ≤ t) (htr : t + 1 / 2 < r)
    (L : E →L[ℝ] E' →L[ℝ] F) (a : CircleSobolev r E) (b : CircleSobolev t E') :
    realConvolutionAsym ht htr L a b = ∑ p : Bool × Bool,
      coeffConvolutionAsym ht htr (L.sesquiPart p.1 p.2) (reflectIf p.1 a) (reflectIf p.2 b) := by
  simp [realConvolutionAsym]

/-- **Product estimate for `realConvolutionAsym` on `H^r × H^t → H^t`.** -/
theorem norm_realConvolutionAsym_le (ht : 0 ≤ t) (htr : t + 1 / 2 < r) (L : E →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev r E) (b : CircleSobolev t E') :
    ‖realConvolutionAsym ht htr L a b‖ ≤
      4 * √(∑' n, weight (-(2 * (r - t))) n) * ‖L‖ * ‖a‖ * ‖b‖ := by
  rw [realConvolutionAsym_apply]
  refine (norm_sum_bool_prod_le (√(∑' n, weight (-(2 * (r - t))) n) * ‖L‖ * ‖a‖ * ‖b‖) _
    fun p ↦ ?_).trans_eq (by ring)
  refine (norm_coeffConvolutionAsym_le ht htr _ _ _).trans ?_
  rw [norm_reflectIf, norm_reflectIf]; have := L.norm_sesquiPart_le p.1 p.2; gcongr

private theorem hasSum_reflectIf (T : ℝ) [Fact (0 < T)] [CompleteSpace G] (hs : 1 / 2 < s)
    (b : Bool) (a : CircleSobolev s G) (x : AddCircle T) :
    HasSum (fun m : ℤ ↦ fourier (T := T) (if b then -m else m) x • (reflectIf b a).coeff m)
      (toContinuousMap T hs a x) := by
  have hA := (hasSum_toContinuousMap T hs a).mapL (ContinuousMap.evalCLM ℂ x)
  simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply', ContinuousMap.const_apply]
    at hA
  cases b
  · simpa [reflectIf] using hA
  · simpa [reflectIf, reflectRealCLM, Function.comp_def] using (Equiv.neg ℤ).hasSum_iff.2 hA

/-- **On continuous representatives `realConvolution` evaluates to `x ↦ L (a x) (b x)`.** -/
@[simp] theorem toContinuousMap_realConvolution_apply (T : ℝ) [Fact (0 < T)] [CompleteSpace E]
    [CompleteSpace E'] (hs : 1 / 2 < s) (L : E →L[ℝ] E' →L[ℝ] F) (a : CircleSobolev s E)
    (b : CircleSobolev s E') (x : AddCircle T) :
    toContinuousMap T hs (realConvolution hs L a b) x =
      L (toContinuousMap T hs a x) (toContinuousMap T hs b x) := by
  have hstar (b : Bool) (m : ℤ) :
      (if b then starRingEnd ℂ (fourier (T := T) (if b then -m else m) x : ℂ)
        else (fourier (T := T) (if b then -m else m) x : ℂ)) = fourier (T := T) m x := by
    cases b <;> simp
  rw [realConvolution_apply, map_sum, ContinuousMap.coe_sum, Finset.sum_apply,
    ← L.sum_sesquiPart_apply (toContinuousMap T hs a x) (toContinuousMap T hs b x)]
  refine Finset.sum_congr rfl fun p _ ↦ toContinuousMap_eq_of_coeff_eq_addConvolution T hs
    (L.sesquiPart p.1 p.2) (reflectIf p.1 a) (reflectIf p.2 b) (coeff_coeffConvolution hs _ _ _) x
    (hasSum_reflectIf T hs p.1 a x) (hasSum_reflectIf T hs p.2 b x) fun m k ↦ ?_
  rw [ContinuousLinearMap.sesquiPart_apply_smul, hstar, hstar, fourier_add]

/-- `realConvolution` commutes with the Sobolev inclusions `H^s → H^t`, `1/2 < t ≤ s`. -/
@[simp] theorem realConvolution_inclusion (ht : 1 / 2 < t) (h : t ≤ s) (L : E →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev s E) (b : CircleSobolev s E') :
    realConvolution ht L (inclusion h a) (inclusion h b) =
      inclusion h (realConvolution (ht.trans_le h) L a b) :=
  CircleSobolev.ext <| funext fun _ ↦ by
    simp [realConvolution_apply, map_sum, coeff_sum, reflectIf_inclusion]

/-- `realConvolutionAsym` agrees with `realConvolution` when the right factor lies in `H^r`. -/
@[simp] theorem realConvolutionAsym_inclusion_right (ht : 0 ≤ t) (htr : t + 1 / 2 < r)
    (L : E →L[ℝ] E' →L[ℝ] F) (a : CircleSobolev r E) (b : CircleSobolev r E') :
    realConvolutionAsym ht htr L a (inclusion (by linarith) b) =
      inclusion (by linarith) (realConvolution (by linarith) L a b) :=
  CircleSobolev.ext <| funext fun _ ↦ by
    simp [realConvolutionAsym_apply, realConvolution_apply, map_sum, coeff_sum, reflectIf_inclusion]

/-- `realConvolutionAsym` agrees with `realConvolution` on `H^s` factors (`r ≤ s`). -/
@[simp] theorem realConvolutionAsym_inclusion (ht : 0 ≤ t) (htr : t + 1 / 2 < r) (hrs : r ≤ s)
    (L : E →L[ℝ] E' →L[ℝ] F) (a : CircleSobolev s E) (b : CircleSobolev s E') :
    realConvolutionAsym ht htr L (inclusion hrs a) (inclusion (by linarith) b) =
      inclusion (by linarith) (realConvolution (by linarith) L a b) :=
  CircleSobolev.ext <| funext fun _ ↦ by
    simp [realConvolutionAsym_apply, realConvolution_apply, map_sum, coeff_sum, reflectIf_inclusion]

/-- For `1/2 < t`, `realConvolutionAsym` evaluates pointwise to `x ↦ L (a x) (b x)`. -/
@[simp] theorem toContinuousMap_realConvolutionAsym_apply (T : ℝ) [Fact (0 < T)] [CompleteSpace E]
    [CompleteSpace E'] (ht : 1 / 2 < t) (htr : t + 1 / 2 < r) (L : E →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev r E) (b : CircleSobolev t E') (x : AddCircle T) :
    toContinuousMap T ht (realConvolutionAsym (by linarith) htr L a b) x =
      L (toContinuousMap T (by linarith) a x) (toContinuousMap T ht b x) := by
  have h : realConvolutionAsym (by linarith) htr L a b =
      realConvolution ht L (inclusion (by linarith) a) b := CircleSobolev.ext <| funext fun _ ↦ by
    simp [realConvolutionAsym_apply, realConvolution_apply, coeff_sum, reflectIf_inclusion]
  rw [h, toContinuousMap_realConvolution_apply, toContinuousMap_inclusion]

open ContinuousLinearMap in
/-- Fourier-coefficient formula for `realConvolutionAsym` against `single k w`. -/
@[simp] theorem coeff_realConvolutionAsym_single_right (ht : 0 ≤ t) (htr : t + 1 / 2 < r)
    (L : E →L[ℝ] E' →L[ℝ] F) (a : CircleSobolev r E) (k n : ℤ) (w : E') :
    (realConvolutionAsym ht htr L a (single k w)).coeff n =
      (mapRealCLM (L.flip.complexLinearPart w) a).coeff (n - k) +
        (mapRealCLM (L.flip.complexAntilinearPart w) a).coeff (n + k) := by
  have hp (b₁ b₂ : Bool) (x : E) : L.sesquiPart b₁ b₂ x w =
      if b₂ then if b₁ then (L.flip.complexAntilinearPart w).complexAntilinearPart x
        else (L.flip.complexAntilinearPart w).complexLinearPart x
      else if b₁ then (L.flip.complexLinearPart w).complexAntilinearPart x
        else (L.flip.complexLinearPart w).complexLinearPart x := by
    cases b₁ <;> cases b₂ <;> simp only [Bool.false_eq_true, ↓reduceIte,
      ContinuousLinearMap.sesquiPart_apply, Bool.true_eq_false, one_smul, neg_smul,
      ContinuousLinearMap.complexLinearPart_apply, ContinuousLinearMap.complexAntilinearPart_apply,
      smul_apply, add_apply, sub_apply, ContinuousLinearMap.flip_apply, smul_add, smul_sub,
      smul_comm I (2⁻¹ : ℝ), i_smul_i_smul] <;> module
  rw [realConvolutionAsym_apply, coeff_sum]
  simp only [Finset.sum_apply, Fintype.sum_prod_type, Fintype.sum_bool, reflectIf_single, hp,
    Bool.false_eq_true, ↓reduceIte, coeff_coeffConvolutionAsym, coeff_single,
    addConvolution_single_apply, ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply,
    sub_neg_eq_add, coeff_reflectIf, coeff_mapRealCLM]
  abel

/-- Series expansion of the `n`-th Fourier coefficient of `realConvolutionAsym ht htr L a b` over
the Fourier modes `k : ℤ` of `b`, valid at every order `0 ≤ t` (including `t ≤ 1/2`). -/
theorem hasSum_coeff_realConvolutionAsym (ht : 0 ≤ t) (htr : t + 1 / 2 < r)
    (L : E →L[ℝ] E' →L[ℝ] F) (a : CircleSobolev r E) (b : CircleSobolev t E') (n : ℤ) :
    HasSum (fun k : ℤ ↦ (mapRealCLM (L.flip.complexLinearPart (b.coeff k)) a).coeff (n - k) +
      (mapRealCLM (L.flip.complexAntilinearPart (b.coeff k)) a).coeff (n + k))
      ((realConvolutionAsym ht htr L a b).coeff n) := by
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', coeffCLM_apply,
    coeff_realConvolutionAsym_single_right] using (hasSum_single b).mapL
      (((coeffCLM (s := t) (E := F) n).restrictScalars ℝ).comp (realConvolutionAsym ht htr L a))

/-- Fourier-coefficient characterization of `realConvolutionAsym ht htr L a b` at every order
`0 ≤ t` (`t + 1/2 < r`). -/
theorem coeff_realConvolutionAsym (ht : 0 ≤ t) (htr : t + 1 / 2 < r)
    (L : E →L[ℝ] E' →L[ℝ] F) (a : CircleSobolev r E) (b : CircleSobolev t E') (n : ℤ) :
    (realConvolutionAsym ht htr L a b).coeff n = ∑' k : ℤ,
      ((mapRealCLM (L.flip.complexLinearPart (b.coeff k)) a).coeff (n - k) +
        (mapRealCLM (L.flip.complexAntilinearPart (b.coeff k)) a).coeff (n + k)) :=
  (hasSum_coeff_realConvolutionAsym ht htr L a b n).tsum_eq.symm

/-- Against a constant right factor `single 0 w`, `realConvolutionAsym` reduces to `mapRealCLM`. -/
@[simp] theorem realConvolutionAsym_single_zero_right (ht : 0 ≤ t) (htr : t + 1 / 2 < r)
    (L : E →L[ℝ] E' →L[ℝ] F) (a : CircleSobolev r E) (w : E') :
    realConvolutionAsym ht htr L a (single 0 w) =
      inclusion (by linarith) (mapRealCLM (L.flip w) a) :=
  CircleSobolev.ext <| funext fun n ↦ by
    rw [coeff_realConvolutionAsym_single_right, sub_zero, add_zero, ← Pi.add_apply, ← coeff_add,
      ← add_apply, ← map_add, L.flip.complexLinearPart_add_complexAntilinearPart_apply,
      coeff_inclusion]

/-- Against a constant left multiplier `single 0 v`, `realConvolutionAsym` reduces to `mapRealCLM`
at every order `0 ≤ t` (including `t ≤ 1/2`). -/
@[simp] theorem realConvolutionAsym_single_zero_left (ht : 0 ≤ t) (htr : t + 1 / 2 < r)
    (L : E →L[ℝ] E' →L[ℝ] F) (v : E) (b : CircleSobolev t E') :
    realConvolutionAsym ht htr L (single 0 v) b = mapRealCLM (L v) b := by
  ext n; rw [realConvolutionAsym_apply, coeff_sum]
  simp only [Finset.sum_apply, Fintype.sum_prod_type, Fintype.sum_bool, reflectIf_single,
    neg_zero, ite_self, coeff_coeffConvolutionAsym, coeff_single, single_addConvolution_apply,
    ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, zero_add, coeff_reflectIf,
    Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, coeff_mapRealCLM,
    ContinuousLinearMap.complexLinearPart_apply, ContinuousLinearMap.complexAntilinearPart_apply,
    ContinuousLinearMap.sesquiPart_apply, one_smul, neg_smul]; module

end PublicConvolutions
end CircleSobolev
end TauCeti
