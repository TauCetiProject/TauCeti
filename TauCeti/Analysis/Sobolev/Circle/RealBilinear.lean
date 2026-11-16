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
import TauCeti.Analysis.Sobolev.Circle.Duality
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

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

open DiscreteConvolution (AddConvolutionExists AddConvolutionExistsAt addFiberEquivSub
  addConvolutionExists_and_summable_sq_one_add_abs_rpow_mul_norm_addConvolution
  enorm_addConvolution_le tsum_addRingConvolution_sq_le'
  tsum_sq_one_add_abs_rpow_mul_norm_addConvolution_le)

namespace TauCeti
namespace CircleSobolev

variable {s t r : ℝ} {E E' F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E'] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

private theorem i_smul_i_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (v : V) :
    I • I • v = -v := by rw [smul_smul, I_mul_I, neg_one_smul]

/-! ### Real-linear postcomposition -/

private theorem weight_mul_norm_complexAntilinearPart_le (Ψ : E →L[ℝ] F) (a : CircleSobolev s E)
    (n : ℤ) : weight s n * ‖Ψ.complexAntilinearPart (a.coeff (-n))‖ ≤
      ‖Ψ‖ * (weight s n * ‖(reflect a).coeff n‖) := by
  have h : ‖Ψ.complexAntilinearPart (a.coeff (-n))‖ ≤ ‖Ψ‖ * ‖a.coeff (-n)‖ := by
    rw [ContinuousLinearMap.complexAntilinearPart_apply]
    exact norm_two_inv_smul_add_le (𝕜 := ℝ) (Ψ.le_opNorm _)
      (by simpa [norm_smul] using Ψ.le_opNorm (I • a.coeff (-n)))
  simpa [mul_left_comm] using mul_le_mul_of_nonneg_left h (weight_nonneg s n)

private def mapAntilinearAux (Ψ : E →L[ℝ] F) (a : CircleSobolev s E) : CircleSobolev s F :=
  ⟨fun n ↦ Ψ.complexAntilinearPart (a.coeff (-n)),
    memℓp_of_forall_le (weight_mul_norm_complexAntilinearPart_le Ψ a)⟩

private def mapRealAux (Ψ : E →L[ℝ] F) (a : CircleSobolev s E) : CircleSobolev s F :=
  mapCLM Ψ.complexLinearPart a + mapAntilinearAux Ψ a

private theorem norm_mapRealAux_le (Ψ : E →L[ℝ] F) (a : CircleSobolev s E) :
    ‖mapRealAux Ψ a‖ ≤ (2 * ‖Ψ‖) * ‖a‖ := by
  have hlin : ‖mapCLM Ψ.complexLinearPart a‖ ≤ ‖Ψ‖ * ‖a‖ := norm_le_of_forall_le fun n ↦ by
    have h : ‖Ψ.complexLinearPart (a.coeff n)‖ ≤ ‖Ψ‖ * ‖a.coeff n‖ := by
      rw [ContinuousLinearMap.complexLinearPart_apply, sub_eq_add_neg]
      exact norm_two_inv_smul_add_le (𝕜 := ℝ) (Ψ.le_opNorm _)
        (by simpa [norm_smul] using Ψ.le_opNorm (I • a.coeff n))
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
      (fun _ _ _ ↦ CircleSobolev.ext <| funext fun _ ↦ by
        simp only [mapRealAux, coeff_add, Pi.add_apply, coeff_mapCLM, mapAntilinearAux,
          ContinuousLinearMap.complexLinearPart_add, ContinuousLinearMap.complexAntilinearPart_add,
          add_apply]; abel)
      (fun _ _ _ ↦ CircleSobolev.ext <| funext fun _ ↦ by
        simp only [mapRealAux, coeff_add, coeff_real_smul, Pi.add_apply, Pi.smul_apply,
          coeff_mapCLM, mapAntilinearAux, ContinuousLinearMap.complexLinearPart_smul,
          ContinuousLinearMap.complexAntilinearPart_smul, smul_apply, smul_add])
      (fun _ _ _ ↦ CircleSobolev.ext <| funext fun _ ↦ by
        simp only [mapRealAux, coeff_add, Pi.add_apply, coeff_mapCLM, mapAntilinearAux, map_add]
        abel)
      (fun c _ a ↦ CircleSobolev.ext <| funext fun n ↦ by
        simp only [mapRealAux, coeff_add, coeff_real_smul, Pi.add_apply, Pi.smul_apply,
          coeff_mapCLM, mapAntilinearAux]
        rw [← Complex.coe_smul c, ← Complex.coe_smul c (a.coeff (-n)), map_smul, map_smulₛₗ,
          Complex.conj_ofReal, Complex.coe_smul, Complex.coe_smul, smul_add]))
    2 fun Ψ a ↦ by simpa only [LinearMap.mk₂_apply, mul_assoc] using norm_mapRealAux_le Ψ a

@[simp] theorem coeff_mapRealCLM (Ψ : E →L[ℝ] F) (a : CircleSobolev s E) (n : ℤ) :
    (mapRealCLM Ψ a).coeff n =
      Ψ.complexLinearPart (a.coeff n) + Ψ.complexAntilinearPart (a.coeff (-n)) := by
  simp [mapRealCLM, mapRealAux, mapAntilinearAux]

theorem norm_mapRealCLM_le (Ψ : E →L[ℝ] F) (a : CircleSobolev s E) :
    ‖mapRealCLM Ψ a‖ ≤ 2 * ‖Ψ‖ * ‖a‖ := norm_mapRealAux_le Ψ a

@[simp] theorem mapRealCLM_restrictScalars (L : E →L[ℂ] F) (a : CircleSobolev s E) :
    mapRealCLM (L.restrictScalars ℝ) a = mapCLM L a :=
  CircleSobolev.ext <| funext fun n ↦ by rw [coeff_mapRealCLM]; simp

/-- `mapRealCLM` sends the identity real-linear operator to the identity on `H^s`. -/
@[simp] theorem mapRealCLM_id (a : CircleSobolev s E) : mapRealCLM (.id ℝ E) a = a :=
  CircleSobolev.ext <| funext fun n ↦ by
    simp only [coeff_mapRealCLM, ContinuousLinearMap.complexLinearPart_apply,
      ContinuousLinearMap.complexAntilinearPart_apply, ContinuousLinearMap.id_apply,
      i_smul_i_smul]; module

/-- `mapRealCLM` respects composition of continuous real-linear operators. -/
@[simp] theorem mapRealCLM_comp (Φ : F →L[ℝ] G) (Ψ : E →L[ℝ] F) (a : CircleSobolev s E) :
    mapRealCLM (Φ.comp Ψ) a = mapRealCLM Φ (mapRealCLM Ψ a) :=
  CircleSobolev.ext <| funext fun n ↦ by
    simp only [coeff_mapRealCLM, neg_neg, ContinuousLinearMap.complexLinearPart_apply,
      ContinuousLinearMap.complexAntilinearPart_apply, ContinuousLinearMap.comp_apply, map_add,
      map_sub, map_smul, map_neg, smul_add, smul_sub, smul_comm I (2⁻¹ : ℝ), i_smul_i_smul,
      smul_neg]
    module

@[simp] theorem mapRealCLM_inclusion (h : t ≤ s) (Ψ : E →L[ℝ] F) (a : CircleSobolev s E) :
    mapRealCLM Ψ (inclusion h a) = inclusion h (mapRealCLM Ψ a) :=
  CircleSobolev.ext <| funext fun _ ↦ by simp

@[simp] theorem mapRealCLM_single_zero (Ψ : E →L[ℝ] F) (v : E) :
    mapRealCLM Ψ (single (s := s) 0 v) = single 0 (Ψ v) :=
  CircleSobolev.ext <| funext fun n ↦ by
    rw [coeff_mapRealCLM]; rcases eq_or_ne n 0 with rfl | hn
    · simp only [coeff_single, neg_zero, Pi.single_eq_same,
        ContinuousLinearMap.complexLinearPart_add_complexAntilinearPart_apply]
    · simp [hn, neg_eq_zero.not.2 hn]

/-- **On continuous representatives `mapRealCLM` acts pointwise:** for `s > 1/2`, the continuous
function attached to `mapRealCLM Ψ a` is `x ↦ Ψ (a x)`. -/
@[simp] theorem toContinuousMap_mapRealCLM_apply (T : ℝ) [Fact (0 < T)] [CompleteSpace E]
    [CompleteSpace F] (hs : 1 / 2 < s) (Ψ : E →L[ℝ] F) (a : CircleSobolev s E) (x : AddCircle T) :
    toContinuousMap T hs (mapRealCLM Ψ a) x = Ψ (toContinuousMap T hs a x) := by
  have hsplit : mapRealCLM Ψ a = mapCLM Ψ.complexLinearPart a + mapAntilinearAux Ψ a :=
    CircleSobolev.ext <| funext fun n ↦ by simp [mapAntilinearAux]
  rw [hsplit, map_add, ContinuousMap.add_apply, toContinuousMap_mapCLM_apply,
    ← Ψ.complexLinearPart_add_complexAntilinearPart_apply (toContinuousMap T hs a x)]
  congr 1
  have hA := (hasSum_toContinuousMap T hs a).mapL (ContinuousMap.evalCLM ℂ x)
  simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply', ContinuousMap.const_apply]
    at hA
  refine ((hasSum_toContinuousMap T hs (mapAntilinearAux Ψ a)).mapL
    (ContinuousMap.evalCLM ℂ x)).unique ?_
  convert ((Equiv.neg ℤ).hasSum_iff.2 hA).mapL Ψ.complexAntilinearPart using 1
  ext n; simp [mapAntilinearAux, ContinuousMap.smul_apply']

/-! ### Real-bilinear coefficient convolutions (symmetric and asymmetric) -/

private def mkCoeffConvolution (K : ℝ) (B : G →L[ℝ] E' →L[ℝ] F)
    (hex : ∀ (a : CircleSobolev r G) (b : CircleSobolev t E'),
      AddConvolutionExists B.toLinearMap₁₂ a.coeff b.coeff)
    (hmem : ∀ (a : CircleSobolev r G) (b : CircleSobolev t E'),
      Memℓp (fun n ↦ weight t n • (a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff) n) 2)
    (hnorm : ∀ (a : CircleSobolev r G) (b : CircleSobolev t E'),
      ‖(⟨a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff, hmem a b⟩ : CircleSobolev t F)‖ ≤
        K * ‖B‖ * ‖a‖ * ‖b‖) :
    CircleSobolev r G →L[ℝ] CircleSobolev t E' →L[ℝ] CircleSobolev t F :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun a b ↦ ⟨a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff, hmem a b⟩)
      (fun a a' b ↦ CircleSobolev.ext <| (hex a b).add_distrib _ (hex a' b))
      (fun _ a b ↦ CircleSobolev.ext <| funext fun n ↦ by
        simp only [coeff_real_smul, Pi.smul_apply]; exact (hex a b n).vadd_convolution _)
      (fun a b b' ↦ CircleSobolev.ext <| (hex a b).distrib_add _ (hex a b'))
      (fun _ a b ↦ CircleSobolev.ext <| funext fun n ↦ by
        simp only [coeff_real_smul, Pi.smul_apply]; exact (hex a b n).convolution_vadd _))
    (K * ‖B‖) fun a b ↦ by simpa only [LinearMap.mk₂_apply] using hnorm a b

private theorem norm_mkCoeffConvolution_le {K : ℝ} {B : G →L[ℝ] E' →L[ℝ] F}
    {hex : ∀ (a : CircleSobolev r G) (b : CircleSobolev t E'),
      AddConvolutionExists B.toLinearMap₁₂ a.coeff b.coeff}
    {hmem : ∀ (a : CircleSobolev r G) (b : CircleSobolev t E'),
      Memℓp (fun n ↦ weight t n • (a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff) n) 2}
    (hnorm : ∀ (a : CircleSobolev r G) (b : CircleSobolev t E'),
      ‖(⟨a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff, hmem a b⟩ : CircleSobolev t F)‖ ≤
        K * ‖B‖ * ‖a‖ * ‖b‖)
    (a : CircleSobolev r G) (b : CircleSobolev t E') :
    ‖mkCoeffConvolution K B hex hmem hnorm a b‖ ≤ K * ‖B‖ * ‖a‖ * ‖b‖ := by
  have h : mkCoeffConvolution K B hex hmem hnorm a b = ⟨_, hmem a b⟩ := CircleSobolev.ext rfl
  exact h ▸ hnorm a b

section CoeffConvolution

variable [CompleteSpace F]

private theorem summable_sq_weight_mul_norm_coeff' (a : CircleSobolev s E) :
    Summable fun n : ℤ ↦ ((1 + |(n : ℝ)|) ^ s * ‖a.coeff n‖) ^ 2 := by
  simpa only [weight_def] using (hasSum_sq_weight_mul_norm_coeff a).summable

private theorem addConvolutionExists_and_memℓp_real (hs : 1 / 2 < s) (B : G →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev s G) (b : CircleSobolev s E') :
    AddConvolutionExists B.toLinearMap₁₂ a.coeff b.coeff ∧
      Memℓp (fun n ↦ weight s n • (a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff) n) 2 :=
  let ⟨h₁, h₂⟩ := addConvolutionExists_and_summable_sq_one_add_abs_rpow_mul_norm_addConvolution
    B hs (summable_sq_weight_mul_norm_coeff' a) (summable_sq_weight_mul_norm_coeff' b)
  ⟨h₁, (memℓp_weight_smul_iff _).2 (by simpa only [weight_def] using h₂)⟩

private theorem norm_coeffConvolutionAux_le (hs : 1 / 2 < s) (B : G →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev s G) (b : CircleSobolev s E') :
    ‖(⟨a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff,
      (addConvolutionExists_and_memℓp_real hs B a b).2⟩ : CircleSobolev s F)‖ ≤
      2 ^ (s + 1) * √(∑' n, weight (-(2 * s)) n) * ‖B‖ * ‖a‖ * ‖b‖ := by
  set w : CircleSobolev s F := ⟨_, (addConvolutionExists_and_memℓp_real hs B a b).2⟩
  have hcoeff : a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff = w.coeff := rfl
  have hK : 0 ≤ ∑' n, weight (-(2 * s)) n := tsum_nonneg fun n ↦ weight_nonneg _ n
  have h := tsum_sq_one_add_abs_rpow_mul_norm_addConvolution_le B hs
    (summable_sq_weight_mul_norm_coeff' a) (summable_sq_weight_mul_norm_coeff' b)
  simp only [hcoeff, neg_mul, ← weight_def] at h
  rw [(hasSum_sq_weight_mul_norm_coeff w).tsum_eq,
    (hasSum_sq_weight_mul_norm_coeff a).tsum_eq, (hasSum_sq_weight_mul_norm_coeff b).tsum_eq] at h
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 (h.trans_eq ?_)
  have h4 : ((2 : ℝ) ^ (s + 1)) ^ 2 = 4 ^ (s + 1) := by
    rw [sq, ← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
  simp only [mul_pow, Real.sq_sqrt hK, h4]; ring

private def coeffConvolution (hs : 1 / 2 < s) (B : G →L[ℝ] E' →L[ℝ] F) :
    CircleSobolev s G →L[ℝ] CircleSobolev s E' →L[ℝ] CircleSobolev s F :=
  mkCoeffConvolution (2 ^ (s + 1) * √(∑' n, weight (-(2 * s)) n)) B
    (fun a b ↦ (addConvolutionExists_and_memℓp_real hs B a b).1)
    (fun a b ↦ (addConvolutionExists_and_memℓp_real hs B a b).2) (norm_coeffConvolutionAux_le hs B)

@[simp] private theorem coeff_coeffConvolution (hs : 1 / 2 < s) (B : G →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev s G) (b : CircleSobolev s E') :
    (coeffConvolution hs B a b).coeff = a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff := (rfl)

private theorem norm_coeffConvolution_le (hs : 1 / 2 < s) (B : G →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev s G) (b : CircleSobolev s E') :
    ‖coeffConvolution hs B a b‖ ≤
      2 ^ (s + 1) * √(∑' n, weight (-(2 * s)) n) * ‖B‖ * ‖a‖ * ‖b‖ :=
  norm_mkCoeffConvolution_le (norm_coeffConvolutionAux_le hs B) a b

private theorem toContinuousMap_coeffConvolution_eq (T : ℝ) [Fact (0 < T)]
    (hs : 1 / 2 < s) (B : G →L[ℝ] E' →L[ℝ] F) (a : CircleSobolev s G)
    (c : CircleSobolev s E') (x : AddCircle T) {f₁ : ℤ → G} {u : G}
    (ha : HasSum f₁ u) {f₂ : ℤ → E'} {v : E'} (hf : HasSum f₂ v)
    (hterm : ∀ m k, fourier (T := T) (m + k) x • B (a.coeff m) (c.coeff k) =
      B (f₁ m) (f₂ k)) :
    toContinuousMap T hs (coeffConvolution hs B a c) x = B u v := by
  set g : ℤ × ℤ → F := fun p ↦ fourier (p.1 + p.2) x • B (a.coeff p.1) (c.coeff p.2) with hg
  have hgs : Summable g := Summable.of_norm_bounded
    (((summable_norm_coeff hs a).mul_of_nonneg (summable_norm_coeff hs c)
      (fun _ ↦ norm_nonneg _) fun _ ↦ norm_nonneg _).mul_left ‖B‖) fun p ↦ by
      simpa [hg, norm_smul, fourier_apply, mul_assoc] using B.le_opNorm₂ (a.coeff p.1) (c.coeff p.2)
  have hrow (m : ℤ) : HasSum (fun k ↦ g (m, k)) (B (f₁ m) v) := by
    convert hf.mapL (B (f₁ m)) using 1; exact funext fun k ↦ hterm m k
  have hgB : HasSum g (B u v) :=
    (ha.mapL (B.flip v)).unique (hgs.hasSum.prod_fiberwise hrow) ▸ hgs.hasSum
  let e : (Σ _ : ℤ, ℤ) ≃ ℤ × ℤ :=
    { toFun σ := (σ.1 - σ.2, σ.2), invFun p := ⟨p.1 + p.2, p.2⟩
      left_inv _ := by simp, right_inv _ := by simp }
  have hfib (n : ℤ) : HasSum (fun m ↦ (g ∘ e) ⟨n, m⟩)
      (fourier n x • (coeffConvolution hs B a c).coeff n) := by
    rw [coeff_coeffConvolution]
    convert (((addConvolutionExists_and_memℓp_real hs B a c).1 n).hasSum_sub).const_smul
      (fourier n x : ℂ) using 1
    ext m; simp only [Function.comp_apply, hg, e, Equiv.coe_fn_mk, sub_add_cancel]; rfl
  rw [toContinuousMap_apply]; exact ((e.hasSum_iff.2 hgB).sigma hfib).tsum_eq

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

private theorem tsum_mul_addRingConvolution_sq_le {ω α β : ℤ → ℝ≥0∞} {C : ℝ≥0∞}
    (hω : ∀ m k, ω (m + k) ≤ C * (ω m + ω k)) (h1ω : ∀ n, 1 ≤ ω n) :
    ∑' n, (ω n * (α ⋆ᵣ₊ β) n) ^ 2 ≤
      4 * C ^ 2 * ((∑' m, ω m * α m) ^ 2 * ∑' k, (ω k * β k) ^ 2) := by
  have hpt (n : ℤ) : ω n * (α ⋆ᵣ₊ β) n ≤
      C * (((fun m ↦ ω m * α m) ⋆ᵣ₊ β) n + (α ⋆ᵣ₊ fun k ↦ ω k * β k) n) := by
    simp_rw [DiscreteConvolution.addRingConvolution_eq_tsum_sub, ← _root_.tsum_add,
      ← ENNReal.tsum_mul_left]
    refine _root_.tsum_le_tsum fun k ↦ ?_
    calc ω n * (α (n - k) * β k)
        ≤ C * (ω (n - k) + ω k) * (α (n - k) * β k) := by gcongr; simpa using hω (n - k) k
      _ = C * (ω (n - k) * α (n - k) * β k + α (n - k) * (ω k * β k)) := by ring
  have hsq (x y : ℝ≥0∞) : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
    have h := ENNReal.rpow_add_le_mul_rpow_add_rpow x y one_le_two
    norm_num [ENNReal.rpow_two] at h; exact h
  have hα_le : ∑' m, α m ≤ ∑' m, ω m * α m :=
    _root_.tsum_le_tsum fun m ↦ le_mul_of_one_le_left' (h1ω m)
  have hβ_le : ∑' k, β k ^ 2 ≤ ∑' k, (ω k * β k) ^ 2 :=
    _root_.tsum_le_tsum fun k ↦ pow_le_pow_left' (le_mul_of_one_le_left' (h1ω k)) 2
  calc ∑' n, (ω n * (α ⋆ᵣ₊ β) n) ^ 2
      ≤ ∑' n, 2 * C ^ 2 * (((fun m ↦ ω m * α m) ⋆ᵣ₊ β) n ^ 2 +
          (α ⋆ᵣ₊ fun k ↦ ω k * β k) n ^ 2) :=
        _root_.tsum_le_tsum fun n ↦ by grw [hpt n, mul_pow, hsq]; exact le_of_eq (by ring)
    _ ≤ 2 * C ^ 2 * (((∑' m, ω m * α m) ^ 2 * ∑' k, β k ^ 2) +
          (∑' m, α m) ^ 2 * ∑' k, (ω k * β k) ^ 2) := by
        rw [ENNReal.tsum_mul_left, _root_.tsum_add]
        gcongr <;> exact tsum_addRingConvolution_sq_le' _ _
    _ ≤ 4 * C ^ 2 * ((∑' m, ω m * α m) ^ 2 * ∑' k, (ω k * β k) ^ 2) := by
        grw [hβ_le, hα_le]; exact le_of_eq (by ring)

/-- Convert a real weighted square `(weight t n * ‖v‖) ^ 2` into `ℝ≥0∞`. -/
private theorem ofReal_sq_weight_mul_norm {X : Type*} [SeminormedAddCommGroup X] (t : ℝ) (n : ℤ)
    (v : X) : ENNReal.ofReal ((weight t n * ‖v‖) ^ 2) =
      (ENNReal.ofReal (weight t n) * ‖v‖ₑ) ^ 2 := by
  rw [ENNReal.ofReal_pow (mul_nonneg (weight_nonneg t n) (norm_nonneg v)),
    ENNReal.ofReal_mul (weight_nonneg t n), ofReal_norm]

/-- Factor `ENNReal.ofReal` across the squared asymmetric Sobolev product bound. -/
private theorem ofReal_sq_two_rpow_add_one_mul_norm {K : ℝ} (hK : 0 ≤ K) (B : G →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev r G) (b : CircleSobolev t E') :
    ENNReal.ofReal ((2 ^ (t + 1) * K * ‖B‖ * ‖a‖ * ‖b‖) ^ 2) =
      4 * ENNReal.ofReal (2 ^ t) ^ 2 * ‖B‖ₑ ^ 2 * (ENNReal.ofReal K * ‖a‖ₑ) ^ 2 * ‖b‖ₑ ^ 2 := by
  rw [Real.rpow_add two_pos, Real.rpow_one]
  simp (discharger := positivity) only [ENNReal.ofReal_pow, ENNReal.ofReal_mul,
    ENNReal.ofReal_ofNat, ofReal_norm]
  rw [eNorm_eq_nnNorm B, ENNReal.coe_nnreal_eq ‖B‖₊, coe_nnNorm B]; ring

/-- Unconditional `ℝ≥0∞` asymmetric weighted `ℓ²` bound for discrete bilinear convolution on `ℤ`. -/
private theorem tsum_sq_ofReal_weight_mul_enorm_addConvolution_asym_le (ht : 0 ≤ t)
    (B : G →L[ℝ] E' →L[ℝ] F) (f : ℤ → G) (g : ℤ → E') :
    ∑' n : ℤ, (ENNReal.ofReal (weight t n) * ‖(f ⋆₊[B.toLinearMap₁₂] g) n‖ₑ) ^ 2 ≤
      4 * ENNReal.ofReal (2 ^ t) ^ 2 * ‖B‖ₑ ^ 2 *
        (∑' m, ENNReal.ofReal (weight t m) * ‖f m‖ₑ) ^ 2 *
        ∑' k, (ENNReal.ofReal (weight t k) * ‖g k‖ₑ) ^ 2 := by
  set ω : ℤ → ℝ≥0∞ := fun n ↦ ENNReal.ofReal (weight t n)
  have hω (m k : ℤ) : ω (m + k) ≤ ENNReal.ofReal (2 ^ t) * (ω m + ω k) := by
    simp only [ω, weight_def, ← Int.norm_eq_abs]
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (one_add_norm_add_rpow_le ht m k)
  have h1ω (n : ℤ) : 1 ≤ ω n := by simpa [ω] using ENNReal.ofReal_le_ofReal (one_le_weight ht n)
  calc ∑' n : ℤ, (ω n * ‖(f ⋆₊[B.toLinearMap₁₂] g) n‖ₑ) ^ 2
      ≤ ‖B‖ₑ ^ 2 * ∑' n, (ω n * ((‖f ·‖ₑ) ⋆ᵣ₊ (‖g ·‖ₑ)) n) ^ 2 := by
        rw [← ENNReal.tsum_mul_left]; refine _root_.tsum_le_tsum fun n ↦ ?_
        rw [← mul_pow, mul_left_comm]; gcongr; exact enorm_addConvolution_le B f g n
    _ ≤ ‖B‖ₑ ^ 2 * (4 * ENNReal.ofReal (2 ^ t) ^ 2 *
          ((∑' m, ω m * ‖f m‖ₑ) ^ 2 * ∑' k, (ω k * ‖g k‖ₑ) ^ 2)) := by
        gcongr; exact tsum_mul_addRingConvolution_sq_le hω h1ω
    _ = _ := by ring

private theorem ofReal_tsum_sq_weight_mul_norm_addConvolution_asym_le (ht : 0 ≤ t)
    (htr : t + 1 / 2 < r) (B : G →L[ℝ] E' →L[ℝ] F) (a : CircleSobolev r G)
    (b : CircleSobolev t E') :
    ∑' n : ℤ, ENNReal.ofReal ((weight t n * ‖(a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff) n‖) ^ 2) ≤
      ENNReal.ofReal
        ((2 ^ (t + 1) * √(∑' n, weight (-(2 * (r - t))) n) * ‖B‖ * ‖a‖ * ‖b‖) ^ 2) := by
  -- Identify the weighted `ℓ²` coefficient sum of `b : H^t` with `‖b‖ₑ ^ 2` and combine bounds.
  have hb_eq : ∑' k, (ENNReal.ofReal (weight t k) * ‖b.coeff k‖ₑ) ^ 2 = ‖b‖ₑ ^ 2 := by
    simp_rw [← ofReal_sq_weight_mul_norm, ← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ sq_nonneg _)
      (hasSum_sq_weight_mul_norm_coeff b).summable, (hasSum_sq_weight_mul_norm_coeff b).tsum_eq,
      ENNReal.ofReal_pow (norm_nonneg b), ofReal_norm]
  simp_rw [ofReal_sq_weight_mul_norm,
    ofReal_sq_two_rpow_add_one_mul_norm (Real.sqrt_nonneg _) B a b]
  refine (tsum_sq_ofReal_weight_mul_enorm_addConvolution_asym_le ht B a.coeff b.coeff).trans ?_
  have := tsum_ofReal_weight_mul_enorm_coeff_le htr a
  rw [hb_eq]; gcongr

private theorem memℓp_asym (ht : 0 ≤ t) (htr : t + 1 / 2 < r) (B : G →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev r G) (b : CircleSobolev t E') :
    Memℓp (fun n ↦ weight t n • (a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff) n) 2 :=
  (memℓp_weight_smul_iff _).2 <|
    (ENNReal.summable_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (ofReal_tsum_sq_weight_mul_norm_addConvolution_asym_le ht htr B a b))).congr
      fun _ ↦ ENNReal.toReal_ofReal (sq_nonneg _)

private theorem norm_coeffConvolutionAsymAux_le (ht : 0 ≤ t) (htr : t + 1 / 2 < r)
    (B : G →L[ℝ] E' →L[ℝ] F) (a : CircleSobolev r G) (b : CircleSobolev t E') :
    ‖(⟨a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff, memℓp_asym ht htr B a b⟩ : CircleSobolev t F)‖ ≤
      2 ^ (t + 1) * √(∑' n, weight (-(2 * (r - t))) n) * ‖B‖ * ‖a‖ * ‖b‖ := by
  set w : CircleSobolev t F := ⟨_, memℓp_asym ht htr B a b⟩
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [← ENNReal.ofReal_le_ofReal_iff (sq_nonneg _), ← (hasSum_sq_weight_mul_norm_coeff w).tsum_eq,
    ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ sq_nonneg _)
      (hasSum_sq_weight_mul_norm_coeff w).summable]
  exact ofReal_tsum_sq_weight_mul_norm_addConvolution_asym_le ht htr B a b

private def coeffConvolutionAsym [CompleteSpace F] (ht : 0 ≤ t) (htr : t + 1 / 2 < r)
    (B : G →L[ℝ] E' →L[ℝ] F) :
    CircleSobolev r G →L[ℝ] CircleSobolev t E' →L[ℝ] CircleSobolev t F :=
  mkCoeffConvolution (2 ^ (t + 1) * √(∑' n, weight (-(2 * (r - t))) n)) B
    (addConvolutionExists_asym (by linarith) ht B) (memℓp_asym ht htr B)
    (norm_coeffConvolutionAsymAux_le ht htr B)

@[simp] private theorem coeff_coeffConvolutionAsym [CompleteSpace F] (ht : 0 ≤ t)
    (htr : t + 1 / 2 < r) (B : G →L[ℝ] E' →L[ℝ] F) (a : CircleSobolev r G)
    (b : CircleSobolev t E') :
    (coeffConvolutionAsym ht htr B a b).coeff = a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff := (rfl)

private theorem norm_coeffConvolutionAsym_le [CompleteSpace F] (ht : 0 ≤ t) (htr : t + 1 / 2 < r)
    (B : G →L[ℝ] E' →L[ℝ] F) (a : CircleSobolev r G) (b : CircleSobolev t E') :
    ‖coeffConvolutionAsym ht htr B a b‖ ≤
      2 ^ (t + 1) * √(∑' n, weight (-(2 * (r - t))) n) * ‖B‖ * ‖a‖ * ‖b‖ :=
  norm_mkCoeffConvolution_le (norm_coeffConvolutionAsymAux_le ht htr B) a b

/-! ### Four-part sesquilinear decomposition and public real-bilinear convolutions -/

private def bilinearShift10 (L : E →L[ℝ] E' →L[ℝ] F) : E →L[ℝ] E' →L[ℝ] F :=
  ((ContinuousLinearMap.compL ℝ E' F F (Complex.smulIEquiv F : F →L[ℝ] F)).comp L).comp
    (Complex.smulIEquiv E : E →L[ℝ] E)

private def bilinearShift01 (L : E →L[ℝ] E' →L[ℝ] F) : E →L[ℝ] E' →L[ℝ] F :=
  (ContinuousLinearMap.compL ℝ E' F F (Complex.smulIEquiv F : F →L[ℝ] F)).comp
    (L.flip.comp (Complex.smulIEquiv E' : E' →L[ℝ] E')).flip

@[simp] private theorem bilinearShift10_apply (L : E →L[ℝ] E' →L[ℝ] F) (u : E) (v : E') :
    bilinearShift10 L u v = I • L (I • u) v := by simp [bilinearShift10]

@[simp] private theorem bilinearShift01_apply (L : E →L[ℝ] E' →L[ℝ] F) (u : E) (v : E') :
    bilinearShift01 L u v = I • L u (I • v) := by simp [bilinearShift01]

private theorem norm_bilinearShift10_le (L : E →L[ℝ] E' →L[ℝ] F) : ‖bilinearShift10 L‖ ≤ ‖L‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L) fun u ↦ ContinuousLinearMap.opNorm_le_bound
    _ (mul_nonneg (norm_nonneg L) (norm_nonneg u)) fun v ↦ by
      simpa [norm_smul] using L.le_opNorm₂ (I • u) v

private theorem norm_bilinearShift01_le (L : E →L[ℝ] E' →L[ℝ] F) : ‖bilinearShift01 L‖ ≤ ‖L‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L) fun u ↦ ContinuousLinearMap.opNorm_le_bound
    _ (mul_nonneg (norm_nonneg L) (norm_nonneg u)) fun v ↦ by
      simpa [norm_smul] using L.le_opNorm₂ u (I • v)

private def sesquiPart (b₁ b₂ : Bool) (L : E →L[ℝ] E' →L[ℝ] F) : E →L[ℝ] E' →L[ℝ] F :=
  let L₂ := (2⁻¹ : ℝ) • (if b₂ then L + bilinearShift01 L else L - bilinearShift01 L)
  (2⁻¹ : ℝ) • (if b₁ then L₂ + bilinearShift10 L₂ else L₂ - bilinearShift10 L₂)

private theorem norm_two_inv_clm_le (b : Bool) {L S : E →L[ℝ] E' →L[ℝ] F} (hS : ‖S‖ ≤ ‖L‖) :
    ‖(2⁻¹ : ℝ) • (if b then L + S else L - S)‖ ≤ ‖L‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L) fun u ↦ by
    have huS := (S.le_opNorm u).trans (mul_le_mul_of_nonneg_right hS (norm_nonneg u))
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, smul_apply, add_apply, sub_apply,
      norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2⁻¹)] <;>
      linarith [L.le_opNorm u, norm_sub_le (L u) (S u), norm_add_le (L u) (S u)]

private theorem norm_sesquiPart_le (b₁ b₂ : Bool) (L : E →L[ℝ] E' →L[ℝ] F) :
    ‖sesquiPart b₁ b₂ L‖ ≤ ‖L‖ :=
  (norm_two_inv_clm_le b₁ (norm_bilinearShift10_le _)).trans
    (norm_two_inv_clm_le b₂ (norm_bilinearShift01_le L))

private theorem sum_sesquiPart_apply (L : E →L[ℝ] E' →L[ℝ] F) (u : E) (v : E') :
    ∑ p : Bool × Bool, sesquiPart p.1 p.2 L u v = L u v := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, sesquiPart, Bool.false_eq_true, ↓reduceIte,
    smul_apply, add_apply, sub_apply]; module

private def conjIf (b : Bool) : ℂ → ℂ := if b then starRingEnd ℂ else id
private def signI (b : Bool) : ℂ := if b then -I else I

private theorem sesquiPart_left_smul_I (b₁ b₂ : Bool) (L : E →L[ℝ] E' →L[ℝ] F) (x : E) (y : E') :
    sesquiPart b₁ b₂ L (I • x) y = signI b₁ • sesquiPart b₁ b₂ L x y := by
  cases b₁ <;> simp only [sesquiPart, signI, Bool.false_eq_true, ↓reduceIte, smul_apply, add_apply,
    sub_apply, bilinearShift10_apply, i_smul_i_smul, map_neg, neg_apply, smul_neg, neg_smul,
    smul_comm I (2⁻¹ : ℝ), smul_add, smul_sub] <;> abel

private theorem sesquiPart_right_smul_I (b₁ b₂ : Bool) (L : E →L[ℝ] E' →L[ℝ] F) (x : E) (y : E') :
    sesquiPart b₁ b₂ L x (I • y) = signI b₂ • sesquiPart b₁ b₂ L x y := by
  cases b₁ <;> cases b₂ <;> simp only [sesquiPart, signI, Bool.false_eq_true, ↓reduceIte,
    smul_apply, add_apply, sub_apply, bilinearShift10_apply, bilinearShift01_apply, i_smul_i_smul,
    map_neg, smul_neg, neg_smul, smul_comm I (2⁻¹ : ℝ), smul_add, smul_sub] <;> abel

private theorem re_add_im_signI (b : Bool) (z : ℂ) : (z.re : ℂ) + z.im * signI b = conjIf b z := by
  cases b <;> apply Complex.ext <;> simp [signI, conjIf]

private theorem sesquiPart_smul (b₁ b₂ : Bool) (L : E →L[ℝ] E' →L[ℝ] F) (z w : ℂ) (u : E) (v : E') :
    sesquiPart b₁ b₂ L (z • u) (w • v) = (conjIf b₁ z * conjIf b₂ w) • sesquiPart b₁ b₂ L u v := by
  rw [← Complex.re_smul_add_im_smul z u, ← Complex.re_smul_add_im_smul w v]
  simp only [map_add, add_apply, map_smul, smul_apply, sesquiPart_right_smul_I,
    sesquiPart_left_smul_I]
  simp only [← Complex.coe_smul, ← re_add_im_signI b₁ z, ← re_add_im_signI b₂ w]; module

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
  CircleSobolev.ext <| funext fun n ↦ by cases b <;> simp [Pi.single_apply, neg_eq_iff_eq_neg]

private theorem reflectIf_inclusion (b : Bool) (h : t ≤ s) (a : CircleSobolev s G) :
    reflectIf b (inclusion h a) = inclusion h (reflectIf b a) :=
  CircleSobolev.ext <| funext fun _ ↦ by simp

private theorem addConvolution_single_right (B : G →L[ℝ] E' →L[ℝ] F) (f : ℤ → G) (k n : ℤ)
    (w : E') : (f ⋆₊[B.toLinearMap₁₂] Pi.single k w) n = B (f (n - k)) w := by
  rw [DiscreteConvolution.addConvolution_eq_tsum_sub,
    tsum_eq_single k fun m hm ↦ by simp [Pi.single_eq_of_ne hm]]; simp

private theorem single_addConvolution_left (B : G →L[ℝ] E' →L[ℝ] F) (v : G) (g : ℤ → E') (n : ℤ) :
    (Pi.single 0 v ⋆₊[B.toLinearMap₁₂] g) n = B v (g n) := by
  rw [DiscreteConvolution.addConvolution_eq_tsum_neg_add,
    tsum_eq_single 0 fun m hm ↦ by simp [Pi.single_eq_of_ne hm]]; simp

private theorem four_mul_two_rpow_add_one (u : ℝ) : (4 : ℝ) * 2 ^ (u + 1) = 2 ^ (u + 3) := by
  have h4 : (4 : ℝ) = 2 ^ (2 : ℝ) := by norm_num
  rw [h4, ← Real.rpow_add two_pos]; exact congrArg ((2 : ℝ) ^ ·) (by ring)

private theorem norm_sum_bool_prod_le (K : ℝ) (f : Bool × Bool → CircleSobolev s F)
    (hf : ∀ p, ‖f p‖ ≤ K) : ‖∑ p : Bool × Bool, f p‖ ≤ 4 * K :=
  (norm_sum_le _ _).trans <|
    (Finset.sum_le_sum fun p _ ↦ hf p).trans_eq (by simp [Fintype.card_prod])

section PublicConvolutions

variable [CompleteSpace F]

/-- **Symmetric real-bilinear product on `H^s`, `s > 1/2`.** A continuous real-bilinear map
`L : E →L[ℝ] E' →L[ℝ] F` induces a continuous real-bilinear map
`H^s(E) →L[ℝ] H^s(E') →L[ℝ] H^s(F)`. On continuous representatives it is the pointwise map
`x ↦ L (a x) (b x)` (`toContinuousMap_realConvolution_apply`). -/
def realConvolution (hs : 1 / 2 < s) (L : E →L[ℝ] E' →L[ℝ] F) :
    CircleSobolev s E →L[ℝ] CircleSobolev s E' →L[ℝ] CircleSobolev s F :=
  ∑ p : Bool × Bool,
    (((coeffConvolution hs (sesquiPart p.1 p.2 L)).comp (reflectIf p.1)).flip.comp
      (reflectIf p.2)).flip

private theorem realConvolution_apply (hs : 1 / 2 < s) (L : E →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev s E) (b : CircleSobolev s E') :
    realConvolution hs L a b = ∑ p : Bool × Bool,
      coeffConvolution hs (sesquiPart p.1 p.2 L) (reflectIf p.1 a) (reflectIf p.2 b) := by
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
    rw [norm_reflectIf, norm_reflectIf]; have := norm_sesquiPart_le p.1 p.2 L; gcongr
  · rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, four_mul_two_rpow_add_one]

/-- **Asymmetric real-bilinear product `H^r(E) × H^t(E') → H^t(F)` for `0 ≤ t` and
`t + 1/2 < r`.** Extends `realConvolution` (`realConvolutionAsym_inclusion_right`) so that an `H^r`
multiplier acts boundedly on `H^t` even when `t ≤ 1/2`. -/
def realConvolutionAsym (ht : 0 ≤ t) (htr : t + 1 / 2 < r) (L : E →L[ℝ] E' →L[ℝ] F) :
    CircleSobolev r E →L[ℝ] CircleSobolev t E' →L[ℝ] CircleSobolev t F :=
  ∑ p : Bool × Bool,
    (((coeffConvolutionAsym ht htr (sesquiPart p.1 p.2 L)).comp (reflectIf p.1)).flip.comp
      (reflectIf p.2)).flip

private theorem realConvolutionAsym_apply (ht : 0 ≤ t) (htr : t + 1 / 2 < r)
    (L : E →L[ℝ] E' →L[ℝ] F) (a : CircleSobolev r E) (b : CircleSobolev t E') :
    realConvolutionAsym ht htr L a b = ∑ p : Bool × Bool,
      coeffConvolutionAsym ht htr (sesquiPart p.1 p.2 L) (reflectIf p.1 a) (reflectIf p.2 b) := by
  simp [realConvolutionAsym]

/-- **Product estimate for `realConvolutionAsym` on `H^r × H^t → H^t`.** -/
theorem norm_realConvolutionAsym_le (ht : 0 ≤ t) (htr : t + 1 / 2 < r) (L : E →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev r E) (b : CircleSobolev t E') :
    ‖realConvolutionAsym ht htr L a b‖ ≤
      2 ^ (t + 3) * √(∑' n, weight (-(2 * (r - t))) n) * ‖L‖ * ‖a‖ * ‖b‖ := by
  rw [realConvolutionAsym_apply]
  refine (norm_sum_bool_prod_le
    (2 ^ (t + 1) * √(∑' n, weight (-(2 * (r - t))) n) * ‖L‖ * ‖a‖ * ‖b‖) _ fun p ↦ ?_).trans_eq ?_
  · refine (norm_coeffConvolutionAsym_le ht htr _ _ _).trans ?_
    rw [norm_reflectIf, norm_reflectIf]; have := norm_sesquiPart_le p.1 p.2 L; gcongr
  · rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, four_mul_two_rpow_add_one]

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

private theorem conjIf_fourier_ite (T : ℝ) (b : Bool) (m : ℤ) (x : AddCircle T) :
    conjIf b (fourier (T := T) (if b then -m else m) x : ℂ) = fourier (T := T) m x := by
  cases b <;> simp [conjIf]

/-- **On continuous representatives `realConvolution` is pointwise:** for `s > 1/2`, the continuous
function attached to `realConvolution hs L a b` is `x ↦ L (a x) (b x)`. -/
@[simp] theorem toContinuousMap_realConvolution_apply (T : ℝ) [Fact (0 < T)] [CompleteSpace E]
    [CompleteSpace E'] (hs : 1 / 2 < s) (L : E →L[ℝ] E' →L[ℝ] F) (a : CircleSobolev s E)
    (b : CircleSobolev s E') (x : AddCircle T) :
    toContinuousMap T hs (realConvolution hs L a b) x =
      L (toContinuousMap T hs a x) (toContinuousMap T hs b x) := by
  rw [realConvolution_apply, map_sum, ContinuousMap.coe_sum, Finset.sum_apply,
    ← sum_sesquiPart_apply L (toContinuousMap T hs a x) (toContinuousMap T hs b x)]
  refine Finset.sum_congr rfl fun p _ ↦
    toContinuousMap_coeffConvolution_eq T hs (sesquiPart p.1 p.2 L)
      (reflectIf p.1 a) (reflectIf p.2 b) x (hasSum_reflectIf T hs p.1 a x)
      (hasSum_reflectIf T hs p.2 b x) fun m k ↦ ?_
  rw [sesquiPart_smul, conjIf_fourier_ite, conjIf_fourier_ite, fourier_add]

/-- `realConvolution` commutes with the Sobolev inclusions `H^s → H^t`, `1/2 < t ≤ s`. -/
@[simp] theorem realConvolution_inclusion (ht : 1 / 2 < t) (h : t ≤ s) (L : E →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev s E) (b : CircleSobolev s E') :
    realConvolution ht L (inclusion h a) (inclusion h b) =
      inclusion h (realConvolution (ht.trans_le h) L a b) :=
  CircleSobolev.ext <| funext fun _ ↦ by
    simp [realConvolution_apply, map_sum, coeff_sum, reflectIf_inclusion]

/-- When the second factor also lies in `H^r`, `realConvolutionAsym` agrees with `realConvolution`
at order `r`. -/
@[simp] theorem realConvolutionAsym_inclusion_right (ht : 0 ≤ t) (htr : t + 1 / 2 < r)
    (L : E →L[ℝ] E' →L[ℝ] F) (a : CircleSobolev r E) (b : CircleSobolev r E') :
    realConvolutionAsym ht htr L a (inclusion (by linarith) b) =
      inclusion (by linarith) (realConvolution (by linarith) L a b) :=
  CircleSobolev.ext <| funext fun _ ↦ by
    simp [realConvolutionAsym_apply, realConvolution_apply, map_sum, coeff_sum, reflectIf_inclusion]

/-- When both factors come from `H^s` with `r ≤ s`, `realConvolutionAsym` agrees with
`realConvolution` at order `s`. -/
@[simp] theorem realConvolutionAsym_inclusion (ht : 0 ≤ t) (htr : t + 1 / 2 < r) (hrs : r ≤ s)
    (L : E →L[ℝ] E' →L[ℝ] F) (a : CircleSobolev s E) (b : CircleSobolev s E') :
    realConvolutionAsym ht htr L (inclusion hrs a) (inclusion (by linarith) b) =
      inclusion (by linarith) (realConvolution (by linarith) L a b) :=
  CircleSobolev.ext <| funext fun _ ↦ by
    simp [realConvolutionAsym_apply, realConvolution_apply, map_sum, coeff_sum, reflectIf_inclusion]

/-- For `1/2 < t`, `realConvolutionAsym` evaluates pointwise to `x ↦ L (a x) (b x)` on continuous
representatives. -/
@[simp] theorem toContinuousMap_realConvolutionAsym_apply (T : ℝ) [Fact (0 < T)] [CompleteSpace E]
    [CompleteSpace E'] (ht : 1 / 2 < t) (htr : t + 1 / 2 < r) (L : E →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev r E) (b : CircleSobolev t E') (x : AddCircle T) :
    toContinuousMap T ht (realConvolutionAsym (by linarith) htr L a b) x =
      L (toContinuousMap T (by linarith) a x) (toContinuousMap T ht b x) := by
  have h : realConvolutionAsym (by linarith) htr L a b =
      realConvolution ht L (inclusion (by linarith) a) b :=
    CircleSobolev.ext <| funext fun _ ↦ by
      simp [realConvolutionAsym_apply, realConvolution_apply, coeff_sum, reflectIf_inclusion]
  rw [h, toContinuousMap_realConvolution_apply, toContinuousMap_inclusion]

/-- Fourier-coefficient formula for `realConvolutionAsym` against a Fourier monomial `single k w` at
any order `0 ≤ t` (`t + 1/2 < r`). -/
@[simp] theorem coeff_realConvolutionAsym_single_right (ht : 0 ≤ t) (htr : t + 1 / 2 < r)
    (L : E →L[ℝ] E' →L[ℝ] F) (a : CircleSobolev r E) (k n : ℤ) (w : E') :
    (realConvolutionAsym ht htr L a (single k w)).coeff n =
      (mapRealCLM (L.flip.complexLinearPart w) a).coeff (n - k) +
        (mapRealCLM (L.flip.complexAntilinearPart w) a).coeff (n + k) := by
  have hp (b₁ b₂ : Bool) (x : E) : sesquiPart b₁ b₂ L x w =
      if b₂ then if b₁ then (L.flip.complexAntilinearPart w).complexAntilinearPart x
        else (L.flip.complexAntilinearPart w).complexLinearPart x
      else if b₁ then (L.flip.complexLinearPart w).complexAntilinearPart x
        else (L.flip.complexLinearPart w).complexLinearPart x := by
    cases b₁ <;> cases b₂ <;>
      simp [sesquiPart, smul_add, smul_sub, smul_comm I (2⁻¹ : ℝ)] <;> abel
  rw [realConvolutionAsym_apply, coeff_sum]
  simp only [Finset.sum_apply, Fintype.sum_prod_type, Fintype.sum_bool, reflectIf_single, hp,
    Bool.false_eq_true, ↓reduceIte, coeff_coeffConvolutionAsym, coeff_single,
    addConvolution_single_right, sub_neg_eq_add, coeff_reflectIf, coeff_mapRealCLM]
  abel

/-- Series expansion of the `n`-th Fourier coefficient of `realConvolutionAsym ht htr L a b` over
the Fourier modes `k : ℤ` of `b`, valid at every order `0 ≤ t` (including `t ≤ 1/2`). -/
theorem hasSum_coeff_realConvolutionAsym (ht : 0 ≤ t) (htr : t + 1 / 2 < r)
    (L : E →L[ℝ] E' →L[ℝ] F) (a : CircleSobolev r E) (b : CircleSobolev t E') (n : ℤ) :
    HasSum (fun k : ℤ ↦ (mapRealCLM (L.flip.complexLinearPart (b.coeff k)) a).coeff (n - k) +
      (mapRealCLM (L.flip.complexAntilinearPart (b.coeff k)) a).coeff (n + k))
      ((realConvolutionAsym ht htr L a b).coeff n) := by
  have h := (hasSum_single b).mapL
    (((coeffCLM (s := t) (E := F) n).restrictScalars ℝ).comp (realConvolutionAsym ht htr L a))
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', coeffCLM_apply,
    coeff_realConvolutionAsym_single_right] using h

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
    realConvolutionAsym ht htr L (single 0 v) b = mapRealCLM (L v) b :=
  CircleSobolev.ext <| funext fun n ↦ by
    rw [realConvolutionAsym_apply, coeff_sum]
    simp only [Finset.sum_apply, Fintype.sum_prod_type, Fintype.sum_bool, reflectIf_single,
      neg_zero, ite_self, coeff_coeffConvolutionAsym, coeff_single, single_addConvolution_left,
      coeff_reflectIf, Bool.false_eq_true, ↓reduceIte, coeff_mapRealCLM,
      ContinuousLinearMap.complexLinearPart_apply, ContinuousLinearMap.complexAntilinearPart_apply,
      sesquiPart, bilinearShift10_apply, bilinearShift01_apply, smul_apply, add_apply, sub_apply,
      smul_add, smul_sub, smul_comm I (2⁻¹ : ℝ), i_smul_i_smul, smul_neg]
    module

end PublicConvolutions
end CircleSobolev
end TauCeti
