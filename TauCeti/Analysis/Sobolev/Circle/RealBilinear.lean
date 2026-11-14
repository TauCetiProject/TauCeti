/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import TauCeti.Analysis.Normed.Operator.ComplexLinearPart
public import TauCeti.Analysis.Sobolev.Circle.Algebra
import Mathlib.Tactic.Module
import TauCeti.Analysis.Normed.Lp.DiscreteConvolution
import TauCeti.Analysis.Normed.Module.RCLike.Basic
import TauCeti.Analysis.Sobolev.Circle.Duality
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# Products, real-linear maps, and real-bilinear convolutions on circle Sobolev spaces

`TauCeti/Analysis/Sobolev/Circle/Basic.lean` and `TauCeti/Analysis/Sobolev/Circle/Algebra.lean`
set up the Fourier-coefficient Sobolev spaces `H^s(E)` on the circle as complex normed spaces and
construct the pointwise product along a continuous *complex*-bilinear map. Nonlinear differential
calculus on `H^s(E)` — Fréchet derivatives over `ℝ`, segment averages in `E × E`, and the chain
rule `(f ∘ u)' = df(u) u'` — requires the corresponding operations for product spaces, continuous
*real*-linear operators, and continuous *real*-bilinear maps.

A continuous real-linear operator `Ψ : E →L[ℝ] F` decomposes into its complex-linear and
complex-antilinear parts `Ψ = Ψ.complexLinearPart + Ψ.complexAntilinearPart`
(`ContinuousLinearMap.complexLinearPart_add_complexAntilinearPart_apply`). Since
`fourier (-n) x = conj (fourier n x)`, applying `Ψ` pointwise to the Fourier series
`∑ₙ eₙ(x) • aₙ` sends the `n`-th Fourier mode to
`Ψ.complexLinearPart aₙ + Ψ.complexAntilinearPart a₋ₙ`. Reflecting frequencies in the antilinear
summand therefore lifts `Ψ` to a bounded real-linear operator `H^s(E) →L[ℝ] H^s(F)` at every real
order `s` (`TauCeti.CircleSobolev.mapRealCLM`).

Similarly, a continuous real-bilinear map `L : E →L[ℝ] E' →L[ℝ] F` decomposes into four bounded
real-bilinear parts that are complex-linear or complex-antilinear in each variable. Convolving the
Fourier coefficients (or reflected Fourier coefficients) along these four parts yields two bounded
real-bilinear products:
* at symmetric supercritical orders `s > 1/2`, `TauCeti.CircleSobolev.realConvolution` maps
  `H^s(E) × H^s(E') → H^s(F)` and realizes `x ↦ L (a x) (b x)` on continuous representatives;
* at asymmetric orders `0 ≤ t` and `t + 1/2 < r`, `TauCeti.CircleSobolev.realConvolutionAsym` maps
  `H^r(E) × H^t(E') → H^t(F)`, allowing an `H^r` coefficient field such as `df ∘ u` to multiply a
  derivative `u' ∈ H^(s - 1)` even when `s - 1 ≤ 1/2`.

## Main definitions

* `TauCeti.CircleSobolev.mapCLM`: functorial action `(E →L[ℂ] F) →L[ℂ] H^s(E) →L[ℂ] H^s(F)` on
  Fourier coefficients.
* `TauCeti.CircleSobolev.prodEquiv`: canonical isomorphism `H^s(E × F) ≃L[ℂ] H^s(E) × H^s(F)`.
* `TauCeti.CircleSobolev.mapRealCLM`: action `(E →L[ℝ] F) →L[ℝ] H^s(E) →L[ℝ] H^s(F)` of a
  continuous real-linear operator, pointwise on continuous representatives when `s > 1/2`.
* `TauCeti.CircleSobolev.realConvolution`: for `s > 1/2`, the continuous real-bilinear map
  `H^s(E) →L[ℝ] H^s(E') →L[ℝ] H^s(F)` induced by `L : E →L[ℝ] E' →L[ℝ] F`.
* `TauCeti.CircleSobolev.realConvolutionAsym`: for `0 ≤ t` and `t + 1/2 < r`, the asymmetric
  continuous real-bilinear map `H^r(E) →L[ℝ] H^t(E') →L[ℝ] H^t(F)` induced by
  `L : E →L[ℝ] E' →L[ℝ] F`.

## Main statements

* `TauCeti.CircleSobolev.toContinuousMap_mapRealCLM_apply`: for `s > 1/2`, the continuous
  representative of `mapRealCLM Ψ a` is `x ↦ Ψ (a x)`.
* `TauCeti.CircleSobolev.toContinuousMap_realConvolution_apply`: for `s > 1/2`, the continuous
  representative of `realConvolution hs L a b` is `x ↦ L (a x) (b x)`.
* `TauCeti.CircleSobolev.realConvolutionAsym_inclusion_right` and
  `TauCeti.CircleSobolev.realConvolutionAsym_inclusion`: compatibility of `realConvolutionAsym`
  with `realConvolution` under Sobolev inclusions.

## References

* M. E. Taylor, *Partial Differential Equations III*, Chapter 13, Section 3 (tame and asymmetric
  Sobolev product estimates).
* T. Runst and W. Sickel, *Sobolev Spaces of Fractional Order, Nemytskij Operators, and Nonlinear
  Partial Differential Equations*, de Gruyter, 1996, Chapter 4 (products on fractional Sobolev
  spaces).
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

/-! ### Cross-space coefficient bounds -/

private theorem memℓp_of_forall_le_cross {a : CircleSobolev s E} {c : ℤ → F} {C : ℝ}
    (h : ∀ n, weight t n * ‖c n‖ ≤ C * (weight s n * ‖a.coeff n‖)) :
    Memℓp (fun n ↦ weight t n • c n) 2 := by
  refine (memℓp_weight_smul_iff _).2 <| Summable.of_nonneg_of_le (fun _ ↦ sq_nonneg _)
    (fun n ↦ ?_) ((hasSum_sq_weight_mul_norm_coeff a).summable.mul_left (|C| ^ 2))
  have habs : weight t n * ‖c n‖ ≤ |C| * (weight s n * ‖a.coeff n‖) :=
    (h n).trans (mul_le_mul_of_nonneg_right (le_abs_self C)
      (mul_nonneg (weight_nonneg s n) (norm_nonneg _)))
  rw [← mul_pow]
  exact pow_le_pow_left₀ (mul_nonneg (weight_nonneg t n) (norm_nonneg _)) habs 2

private theorem norm_le_of_forall_le_cross {a : CircleSobolev s E} {b : CircleSobolev t F} {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ n, weight t n * ‖b.coeff n‖ ≤ C * (weight s n * ‖a.coeff n‖)) :
    ‖b‖ ≤ C * ‖a‖ := by
  have hle : ‖b‖ ^ 2 ≤ (C * ‖a‖) ^ 2 := by
    rw [mul_pow]
    refine hasSum_le (fun n ↦ ?_) (hasSum_sq_weight_mul_norm_coeff b)
      ((hasSum_sq_weight_mul_norm_coeff a).mul_left (C ^ 2))
    rw [← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg (weight_nonneg t n) (norm_nonneg _)) (h n) 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg a)) two_ne_zero).1 hle

/-! ### Complex-linear postcomposition and product spaces -/

private theorem weight_mul_norm_apply_le (L : E →L[ℂ] F) (a : CircleSobolev s E) (n : ℤ) :
    weight s n * ‖L (a.coeff n)‖ ≤ ‖L‖ * (weight s n * ‖a.coeff n‖) := by
  calc weight s n * ‖L (a.coeff n)‖
      ≤ weight s n * (‖L‖ * ‖a.coeff n‖) :=
        mul_le_mul_of_nonneg_left (L.le_opNorm _) (weight_nonneg s n)
    _ = ‖L‖ * (weight s n * ‖a.coeff n‖) := by ring

private def mapCLMAux (L : E →L[ℂ] F) (a : CircleSobolev s E) : CircleSobolev s F where
  coeff n := L (a.coeff n)
  memℓp_weight_smul_coeff := memℓp_of_forall_le_cross (weight_mul_norm_apply_le L a)

/-- Functorial action of a continuous complex-linear map `L : E →L[ℂ] F` on the Fourier
coefficients of `H^s`, bundled as a continuous bilinear map. -/
def mapCLM : (E →L[ℂ] F) →L[ℂ] CircleSobolev s E →L[ℂ] CircleSobolev s F :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ mapCLMAux
      (fun _ _ _ ↦ CircleSobolev.ext <| funext fun _ ↦ rfl)
      (fun _ _ _ ↦ CircleSobolev.ext <| funext fun _ ↦ rfl)
      (fun L _ _ ↦ CircleSobolev.ext <| funext fun _ ↦ L.map_add _ _)
      (fun c L _ ↦ CircleSobolev.ext <| funext fun _ ↦ L.map_smul c _))
    1 fun L a ↦ by
      simpa only [LinearMap.mk₂_apply, one_mul] using
        norm_le_of_forall_le_cross (norm_nonneg L) (weight_mul_norm_apply_le L a)

@[simp]
theorem coeff_mapCLM (L : E →L[ℂ] F) (a : CircleSobolev s E) (n : ℤ) :
    (mapCLM L a).coeff n = L (a.coeff n) :=
  (rfl)

theorem norm_mapCLM_le (L : E →L[ℂ] F) (a : CircleSobolev s E) :
    ‖mapCLM L a‖ ≤ ‖L‖ * ‖a‖ :=
  norm_le_of_forall_le_cross (norm_nonneg L) (weight_mul_norm_apply_le L a)

@[simp]
theorem mapCLM_id (a : CircleSobolev s E) : mapCLM (.id ℂ E) a = a :=
  CircleSobolev.ext <| funext fun _ ↦ rfl

@[simp]
theorem mapCLM_comp (L : F →L[ℂ] G) (M : E →L[ℂ] F) (a : CircleSobolev s E) :
    mapCLM (L.comp M) a = mapCLM L (mapCLM M a) :=
  CircleSobolev.ext <| funext fun _ ↦ rfl

@[simp]
theorem mapCLM_single (L : E →L[ℂ] F) (n : ℤ) (v : E) :
    mapCLM L (single (s := s) n v) = single n (L v) :=
  CircleSobolev.ext <| funext fun m ↦ by
    rcases eq_or_ne m n with rfl | hm
    · simp
    · simp [hm]

@[simp]
theorem mapCLM_inclusion (h : t ≤ s) (L : E →L[ℂ] F) (a : CircleSobolev s E) :
    mapCLM L (inclusion h a) = inclusion h (mapCLM L a) :=
  CircleSobolev.ext <| funext fun _ ↦ by simp

@[simp]
theorem toContinuousMap_mapCLM_apply (T : ℝ) [Fact (0 < T)] [CompleteSpace E] [CompleteSpace F]
    (hs : 1 / 2 < s) (L : E →L[ℂ] F) (a : CircleSobolev s E) (x : AddCircle T) :
    toContinuousMap T hs (mapCLM L a) x = L (toContinuousMap T hs a x) := by
  have h := ((hasSum_toContinuousMap T hs a).mapL (ContinuousMap.evalCLM ℂ x)).mapL L
  simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply', ContinuousMap.const_apply] at h
  refine ((hasSum_toContinuousMap T hs (mapCLM L a)).mapL
    (ContinuousMap.evalCLM ℂ x)).unique ?_
  convert h using 1
  ext n
  simp [ContinuousMap.smul_apply']

/-- The canonical continuous linear equivalence `H^s(E × F) ≃L[ℂ] H^s(E) × H^s(F)` splitting
Fourier coefficients componentwise. -/
def prodEquiv : CircleSobolev s (E × F) ≃L[ℂ] CircleSobolev s E × CircleSobolev s F :=
  ContinuousLinearEquiv.equivOfInverse
    ((mapCLM (.fst ℂ E F)).prod (mapCLM (.snd ℂ E F)))
    ((mapCLM (.inl ℂ E F)).coprod (mapCLM (.inr ℂ E F)))
    (fun u ↦ CircleSobolev.ext <| funext fun n ↦ Prod.ext (by simp) (by simp))
    (fun p ↦ Prod.ext (CircleSobolev.ext <| funext fun n ↦ by simp)
      (CircleSobolev.ext <| funext fun n ↦ by simp))

@[simp]
theorem coeff_prodEquiv_fst (u : CircleSobolev s (E × F)) (n : ℤ) :
    (prodEquiv u).1.coeff n = (u.coeff n).1 := by
  simp [prodEquiv]

@[simp]
theorem coeff_prodEquiv_snd (u : CircleSobolev s (E × F)) (n : ℤ) :
    (prodEquiv u).2.coeff n = (u.coeff n).2 := by
  simp [prodEquiv]

@[simp]
theorem coeff_prodEquiv_symm (p : CircleSobolev s E × CircleSobolev s F) (n : ℤ) :
    (prodEquiv.symm p).coeff n = (p.1.coeff n, p.2.coeff n) := by
  change (mapCLM (.inl ℂ E F) p.1 + mapCLM (.inr ℂ E F) p.2).coeff n = _
  simp

@[simp]
theorem prodEquiv_symm_single_zero (v : E) (w : F) :
    prodEquiv.symm (single (s := s) 0 v, single (s := s) 0 w) = single 0 (v, w) :=
  CircleSobolev.ext <| funext fun n ↦ by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [hn]

@[simp]
theorem toContinuousMap_prodEquiv_fst (T : ℝ) [Fact (0 < T)] [CompleteSpace E] [CompleteSpace F]
    (hs : 1 / 2 < s) (u : CircleSobolev s (E × F)) (x : AddCircle T) :
    toContinuousMap T hs (prodEquiv u).1 x = (toContinuousMap T hs u x).1 :=
  toContinuousMap_mapCLM_apply T hs (.fst ℂ E F) u x

@[simp]
theorem toContinuousMap_prodEquiv_snd (T : ℝ) [Fact (0 < T)] [CompleteSpace E] [CompleteSpace F]
    (hs : 1 / 2 < s) (u : CircleSobolev s (E × F)) (x : AddCircle T) :
    toContinuousMap T hs (prodEquiv u).2 x = (toContinuousMap T hs u x).2 :=
  toContinuousMap_mapCLM_apply T hs (.snd ℂ E F) u x

@[simp]
theorem toContinuousMap_prodEquiv_symm_apply (T : ℝ) [Fact (0 < T)] [CompleteSpace E]
    [CompleteSpace F] (hs : 1 / 2 < s) (p : CircleSobolev s E × CircleSobolev s F)
    (x : AddCircle T) :
    toContinuousMap T hs (prodEquiv.symm p) x =
      (toContinuousMap T hs p.1 x, toContinuousMap T hs p.2 x) :=
  Prod.ext
    (by simpa using (toContinuousMap_prodEquiv_fst T hs (prodEquiv.symm p) x).symm)
    (by simpa using (toContinuousMap_prodEquiv_snd T hs (prodEquiv.symm p) x).symm)

/-! ### Real-linear postcomposition -/

private theorem norm_complexLinearPart_apply_le (Ψ : E →L[ℝ] F) (v : E) :
    ‖Ψ.complexLinearPart v‖ ≤ ‖Ψ‖ * ‖v‖ := by
  have hI : ‖Ψ (I • v)‖ ≤ ‖Ψ‖ * ‖v‖ := by
    simpa [norm_smul] using Ψ.le_opNorm (I • v)
  rw [ContinuousLinearMap.complexLinearPart_apply, sub_eq_add_neg]
  exact norm_two_inv_smul_add_le (𝕜 := ℝ) (Ψ.le_opNorm v) (by simpa [norm_smul] using hI)

private theorem norm_complexAntilinearPart_apply_le (Ψ : E →L[ℝ] F) (v : E) :
    ‖Ψ.complexAntilinearPart v‖ ≤ ‖Ψ‖ * ‖v‖ := by
  have hI : ‖Ψ (I • v)‖ ≤ ‖Ψ‖ * ‖v‖ := by
    simpa [norm_smul] using Ψ.le_opNorm (I • v)
  rw [ContinuousLinearMap.complexAntilinearPart_apply]
  exact norm_two_inv_smul_add_le (𝕜 := ℝ) (Ψ.le_opNorm v) (by simpa [norm_smul] using hI)

private theorem weight_mul_norm_complexAntilinearPart_le (Ψ : E →L[ℝ] F) (a : CircleSobolev s E)
    (n : ℤ) :
    weight s n * ‖Ψ.complexAntilinearPart (a.coeff (-n))‖ ≤
      ‖Ψ‖ * (weight s n * ‖(reflect a).coeff n‖) := by
  calc weight s n * ‖Ψ.complexAntilinearPart (a.coeff (-n))‖
      ≤ weight s n * (‖Ψ‖ * ‖a.coeff (-n)‖) :=
        mul_le_mul_of_nonneg_left (norm_complexAntilinearPart_apply_le Ψ _) (weight_nonneg s n)
    _ = ‖Ψ‖ * (weight s n * ‖(reflect a).coeff n‖) := by simp [mul_left_comm]

private def mapAntilinearAux (Ψ : E →L[ℝ] F) (a : CircleSobolev s E) : CircleSobolev s F where
  coeff n := Ψ.complexAntilinearPart (a.coeff (-n))
  memℓp_weight_smul_coeff := memℓp_of_forall_le_cross (weight_mul_norm_complexAntilinearPart_le Ψ a)

private theorem norm_mapAntilinearAux_le (Ψ : E →L[ℝ] F) (a : CircleSobolev s E) :
    ‖mapAntilinearAux Ψ a‖ ≤ ‖Ψ‖ * ‖a‖ := by
  simpa using norm_le_of_forall_le_cross (a := reflect a) (b := mapAntilinearAux Ψ a)
    (norm_nonneg Ψ) (weight_mul_norm_complexAntilinearPart_le Ψ a)

private def mapRealAux (Ψ : E →L[ℝ] F) (a : CircleSobolev s E) : CircleSobolev s F :=
  mapCLM Ψ.complexLinearPart a + mapAntilinearAux Ψ a

private theorem norm_mapRealAux_le (Ψ : E →L[ℝ] F) (a : CircleSobolev s E) :
    ‖mapRealAux Ψ a‖ ≤ (2 * ‖Ψ‖) * ‖a‖ := by
  have hlin : ‖mapCLM Ψ.complexLinearPart a‖ ≤ ‖Ψ‖ * ‖a‖ :=
    norm_le_of_forall_le_cross (norm_nonneg Ψ) fun n ↦ by
      calc weight s n * ‖Ψ.complexLinearPart (a.coeff n)‖
          ≤ weight s n * (‖Ψ‖ * ‖a.coeff n‖) :=
            mul_le_mul_of_nonneg_left (norm_complexLinearPart_apply_le Ψ _) (weight_nonneg s n)
        _ = ‖Ψ‖ * (weight s n * ‖a.coeff n‖) := by ring
  calc ‖mapRealAux Ψ a‖
      ≤ ‖mapCLM Ψ.complexLinearPart a‖ + ‖mapAntilinearAux Ψ a‖ := norm_add_le _ _
    _ ≤ ‖Ψ‖ * ‖a‖ + ‖Ψ‖ * ‖a‖ := add_le_add hlin (norm_mapAntilinearAux_le Ψ a)
    _ = (2 * ‖Ψ‖) * ‖a‖ := by ring

/-- Action of a continuous real-linear operator `Ψ : E →L[ℝ] F` on `H^s`, sending `a` to the
element with `n`-th coefficient `Ψ.complexLinearPart (a.coeff n) +
Ψ.complexAntilinearPart (a.coeff (-n))`. On continuous representatives (`s > 1/2`) this is
pointwise application `x ↦ Ψ (a x)` (`toContinuousMap_mapRealCLM_apply`). -/
def mapRealCLM : (E →L[ℝ] F) →L[ℝ] CircleSobolev s E →L[ℝ] CircleSobolev s F :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ mapRealAux
      (fun Ψ Φ a ↦ CircleSobolev.ext <| funext fun n ↦ by
        simp only [mapRealAux, coeff_add, Pi.add_apply, coeff_mapCLM, mapAntilinearAux,
          ContinuousLinearMap.complexLinearPart_add, ContinuousLinearMap.complexAntilinearPart_add,
          add_apply]
        abel)
      (fun c Ψ a ↦ CircleSobolev.ext <| funext fun n ↦ by
        simp only [mapRealAux, coeff_add, coeff_real_smul, Pi.add_apply, Pi.smul_apply,
          coeff_mapCLM, mapAntilinearAux, ContinuousLinearMap.complexLinearPart_smul,
          ContinuousLinearMap.complexAntilinearPart_smul, smul_apply, smul_add])
      (fun Ψ a b ↦ CircleSobolev.ext <| funext fun n ↦ by
        simp only [mapRealAux, coeff_add, Pi.add_apply, coeff_mapCLM, mapAntilinearAux, map_add]
        abel)
      (fun c Ψ a ↦ CircleSobolev.ext <| funext fun n ↦ by
        simp only [mapRealAux, coeff_add, coeff_real_smul, Pi.add_apply, Pi.smul_apply,
          coeff_mapCLM, mapAntilinearAux]
        rw [← Complex.coe_smul c, ← Complex.coe_smul c (a.coeff (-n)), map_smul, map_smulₛₗ,
          Complex.conj_ofReal, Complex.coe_smul, Complex.coe_smul, smul_add]))
    2 fun Ψ a ↦ by simpa only [LinearMap.mk₂_apply, mul_assoc] using norm_mapRealAux_le Ψ a

@[simp]
theorem coeff_mapRealCLM (Ψ : E →L[ℝ] F) (a : CircleSobolev s E) (n : ℤ) :
    (mapRealCLM Ψ a).coeff n =
      Ψ.complexLinearPart (a.coeff n) + Ψ.complexAntilinearPart (a.coeff (-n)) :=
  (rfl)

theorem norm_mapRealCLM_le (Ψ : E →L[ℝ] F) (a : CircleSobolev s E) :
    ‖mapRealCLM Ψ a‖ ≤ 2 * ‖Ψ‖ * ‖a‖ :=
  norm_mapRealAux_le Ψ a

@[simp]
theorem mapRealCLM_restrictScalars (L : E →L[ℂ] F) (a : CircleSobolev s E) :
    mapRealCLM (L.restrictScalars ℝ) a = mapCLM L a :=
  CircleSobolev.ext <| funext fun n ↦ by
    rw [coeff_mapRealCLM]
    simp

@[simp]
theorem mapRealCLM_inclusion (h : t ≤ s) (Ψ : E →L[ℝ] F) (a : CircleSobolev s E) :
    mapRealCLM Ψ (inclusion h a) = inclusion h (mapRealCLM Ψ a) :=
  CircleSobolev.ext <| funext fun n ↦ by
    rw [coeff_mapRealCLM, coeff_inclusion, coeff_inclusion, coeff_mapRealCLM]

@[simp]
theorem mapRealCLM_single_zero (Ψ : E →L[ℝ] F) (v : E) :
    mapRealCLM Ψ (single (s := s) 0 v) = single 0 (Ψ v) :=
  CircleSobolev.ext <| funext fun n ↦ by
    rw [coeff_mapRealCLM]
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [coeff_single, neg_zero, Pi.single_eq_same,
        ContinuousLinearMap.complexLinearPart_add_complexAntilinearPart_apply]
    · simp [hn, neg_eq_zero.not.2 hn]

/-- **On continuous representatives `mapRealCLM` acts pointwise:** for `s > 1/2`, the continuous
function attached to `mapRealCLM Ψ a` is `x ↦ Ψ (a x)`. -/
@[simp]
theorem toContinuousMap_mapRealCLM_apply (T : ℝ) [Fact (0 < T)] [CompleteSpace E] [CompleteSpace F]
    (hs : 1 / 2 < s) (Ψ : E →L[ℝ] F) (a : CircleSobolev s E) (x : AddCircle T) :
    toContinuousMap T hs (mapRealCLM Ψ a) x = Ψ (toContinuousMap T hs a x) := by
  have hsplit : mapRealCLM Ψ a = mapCLM Ψ.complexLinearPart a + mapAntilinearAux Ψ a := rfl
  rw [hsplit, map_add, ContinuousMap.add_apply, toContinuousMap_mapCLM_apply,
    ← Ψ.complexLinearPart_add_complexAntilinearPart_apply (toContinuousMap T hs a x)]
  congr 1
  have hA := (hasSum_toContinuousMap T hs a).mapL (ContinuousMap.evalCLM ℂ x)
  simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply', ContinuousMap.const_apply]
    at hA
  have hanti := ((Equiv.neg ℤ).hasSum_iff.2 hA).mapL Ψ.complexAntilinearPart
  refine ((hasSum_toContinuousMap T hs (mapAntilinearAux Ψ a)).mapL
    (ContinuousMap.evalCLM ℂ x)).unique ?_
  convert hanti using 1
  ext n
  simp [mapAntilinearAux, ContinuousMap.smul_apply']

/-! ### Real-bilinear coefficient convolutions (symmetric and asymmetric) -/

section CoeffConvolution

variable [CompleteSpace F]

private theorem summable_sq_weight_mul_norm_coeff' (a : CircleSobolev s E) :
    Summable fun n : ℤ ↦ ((1 + |(n : ℝ)|) ^ s * ‖a.coeff n‖) ^ 2 := by
  simpa only [weight_def] using (hasSum_sq_weight_mul_norm_coeff a).summable

private theorem addConvolutionExists_and_memℓp_real (hs : 1 / 2 < s) (B : G →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev s G) (b : CircleSobolev s E') :
    AddConvolutionExists B.toLinearMap₁₂ a.coeff b.coeff ∧
      Memℓp (fun n ↦ weight s n • (a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff) n) 2 := by
  obtain ⟨h₁, h₂⟩ := addConvolutionExists_and_summable_sq_one_add_abs_rpow_mul_norm_addConvolution
    B hs (summable_sq_weight_mul_norm_coeff' a) (summable_sq_weight_mul_norm_coeff' b)
  exact ⟨h₁, (memℓp_weight_smul_iff _).2 (by simpa only [weight_def] using h₂)⟩

private def coeffConvolutionAux (hs : 1 / 2 < s) (B : G →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev s G) (b : CircleSobolev s E') : CircleSobolev s F where
  coeff := a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff
  memℓp_weight_smul_coeff := (addConvolutionExists_and_memℓp_real hs B a b).2

private theorem norm_coeffConvolutionAux_le (hs : 1 / 2 < s) (B : G →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev s G) (b : CircleSobolev s E') :
    ‖coeffConvolutionAux hs B a b‖ ≤
      2 ^ (s + 1) * √(∑' n, weight (-(2 * s)) n) * ‖B‖ * ‖a‖ * ‖b‖ := by
  have hK : 0 ≤ ∑' n, weight (-(2 * s)) n := tsum_nonneg fun n ↦ weight_nonneg _ n
  have h := tsum_sq_one_add_abs_rpow_mul_norm_addConvolution_le B hs
    (summable_sq_weight_mul_norm_coeff' a) (summable_sq_weight_mul_norm_coeff' b)
  change ∑' n : ℤ, ((1 + |(n : ℝ)|) ^ s * ‖(coeffConvolutionAux hs B a b).coeff n‖) ^ 2 ≤ _ at h
  simp only [neg_mul, ← weight_def] at h
  rw [(hasSum_sq_weight_mul_norm_coeff _).tsum_eq, (hasSum_sq_weight_mul_norm_coeff _).tsum_eq,
    (hasSum_sq_weight_mul_norm_coeff _).tsum_eq] at h
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 (h.trans_eq ?_)
  have h4 : ((2 : ℝ) ^ (s + 1)) ^ 2 = 4 ^ (s + 1) := by
    rw [sq, ← Real.mul_rpow (by norm_num) (by norm_num)]
    norm_num
  simp only [mul_pow, Real.sq_sqrt hK, h4]
  ring

/-- Discrete convolution of Fourier coefficients along a continuous real-bilinear map at symmetric
order `s > 1/2`. -/
private def coeffConvolution (hs : 1 / 2 < s) (B : G →L[ℝ] E' →L[ℝ] F) :
    CircleSobolev s G →L[ℝ] CircleSobolev s E' →L[ℝ] CircleSobolev s F :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (coeffConvolutionAux hs B)
      (fun a a' b ↦ CircleSobolev.ext <|
        (addConvolutionExists_and_memℓp_real hs B a b).1.add_distrib _
          (addConvolutionExists_and_memℓp_real hs B a' b).1)
      (fun c a b ↦ CircleSobolev.ext <| funext fun n ↦ by
        change ((c • a).coeff ⋆₊[B.toLinearMap₁₂] b.coeff) n =
          (c • coeffConvolutionAux hs B a b).coeff n
        rw [coeff_real_smul, coeff_real_smul]
        exact ((addConvolutionExists_and_memℓp_real hs B a b).1 n).vadd_convolution
          B.toLinearMap₁₂)
      (fun a b b' ↦ CircleSobolev.ext <|
        (addConvolutionExists_and_memℓp_real hs B a b).1.distrib_add _
          (addConvolutionExists_and_memℓp_real hs B a b').1)
      (fun c a b ↦ CircleSobolev.ext <| funext fun n ↦ by
        change (a.coeff ⋆₊[B.toLinearMap₁₂] (c • b).coeff) n =
          (c • coeffConvolutionAux hs B a b).coeff n
        rw [coeff_real_smul, coeff_real_smul]
        exact ((addConvolutionExists_and_memℓp_real hs B a b).1 n).convolution_vadd
          B.toLinearMap₁₂))
    (2 ^ (s + 1) * √(∑' n, weight (-(2 * s)) n) * ‖B‖)
    (fun a b ↦ by simpa only [LinearMap.mk₂_apply] using norm_coeffConvolutionAux_le hs B a b)

@[simp]
private theorem coeff_coeffConvolution (hs : 1 / 2 < s) (B : G →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev s G) (b : CircleSobolev s E') :
    (coeffConvolution hs B a b).coeff = a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff :=
  (rfl)

private theorem toContinuousMap_coeffConvolution_eq (T : ℝ) [Fact (0 < T)]
    (hs : 1 / 2 < s) (B : G →L[ℝ] E' →L[ℝ] F) (a : CircleSobolev s G)
    (c : CircleSobolev s E') (x : AddCircle T) {f₁ : ℤ → G} {u : G}
    (ha : HasSum f₁ u) {f₂ : ℤ → E'} {v : E'} (hf : HasSum f₂ v)
    (hterm : ∀ m k, fourier (T := T) (m + k) x • B (a.coeff m) (c.coeff k) =
      B (f₁ m) (f₂ k)) :
    toContinuousMap T hs (coeffConvolution hs B a c) x = B u v := by
  set g : ℤ × ℤ → F := fun p ↦ fourier (p.1 + p.2) x • B (a.coeff p.1) (c.coeff p.2) with hg
  have hnorm (p : ℤ × ℤ) : ‖g p‖ ≤ ‖B‖ * (‖a.coeff p.1‖ * ‖c.coeff p.2‖) := by
    simpa [hg, norm_smul, fourier_apply, mul_assoc] using B.le_opNorm₂ (a.coeff p.1) (c.coeff p.2)
  have hgs : Summable g := Summable.of_norm_bounded
    (((summable_norm_coeff hs a).mul_of_nonneg (summable_norm_coeff hs c)
      (fun _ ↦ norm_nonneg _) fun _ ↦ norm_nonneg _).mul_left ‖B‖) hnorm
  have hrow (m : ℤ) : HasSum (fun k ↦ g (m, k)) (B (f₁ m) v) := by
    convert hf.mapL (B (f₁ m)) using 1
    exact funext fun k ↦ hterm m k
  have hgB : HasSum g (B u v) :=
    (ha.mapL (B.flip v)).unique (hgs.hasSum.prod_fiberwise hrow) ▸ hgs.hasSum
  let e : (Σ _ : ℤ, ℤ) ≃ ℤ × ℤ :=
    { toFun σ := (σ.1 - σ.2, σ.2)
      invFun p := ⟨p.1 + p.2, p.2⟩
      left_inv _ := by simp
      right_inv _ := by simp }
  have hfib (n : ℤ) : HasSum (fun m ↦ (g ∘ e) ⟨n, m⟩)
      (fourier n x • (coeffConvolution hs B a c).coeff n) := by
    convert (((addConvolutionExists_and_memℓp_real hs B a c).1 n).hasSum_sub).const_smul
      (fourier n x : ℂ) using 1
    · ext m
      simp only [Function.comp_apply, hg, e, Equiv.coe_fn_mk, sub_add_cancel]
      rfl
    · rfl
  rw [toContinuousMap_apply]
  exact ((e.hasSum_iff.2 hgB).sigma hfib).tsum_eq

/-- At asymmetric orders `0 ≤ t` and `0 ≤ r`, the discrete convolution `a.coeff ⋆₊[B] b.coeff`
converges absolutely at every frequency by `ℓ²` Cauchy–Schwarz. -/
private theorem addConvolutionExists_asym (hr : 0 ≤ r) (ht : 0 ≤ t) (B : G →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev r G) (b : CircleSobolev t E') :
    AddConvolutionExists B.toLinearMap₁₂ a.coeff b.coeff := by
  intro n
  unfold AddConvolutionExistsAt
  rw [← (addFiberEquivSub n).summable_iff]
  have ha : Summable fun m : ℤ ↦ ‖a.coeff (n - m)‖ ^ 2 := by
    have h0 := (hasSum_sq_weight_mul_norm_coeff (inclusion hr a)).summable
    simpa [Function.comp_def, weight_zero_left] using (Equiv.subLeft n).summable_iff.2 h0
  have hb : Summable fun m : ℤ ↦ ‖b.coeff m‖ ^ 2 := by
    simpa [weight_zero_left] using (hasSum_sq_weight_mul_norm_coeff (inclusion ht b)).summable
  refine Summable.of_norm_bounded (((ha.add hb).mul_left (2⁻¹ : ℝ)).mul_left ‖B‖) fun m ↦ ?_
  simp only [Function.comp_apply, DiscreteConvolution.coe_addFiberEquivSub_apply,
    ContinuousLinearMap.toLinearMap₁₂_apply]
  calc ‖B (a.coeff (n - m)) (b.coeff m)‖
      ≤ ‖B‖ * ‖a.coeff (n - m)‖ * ‖b.coeff m‖ := B.le_opNorm₂ _ _
    _ ≤ ‖B‖ * (2⁻¹ * (‖a.coeff (n - m)‖ ^ 2 + ‖b.coeff m‖ ^ 2)) := by
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg B)
      nlinarith [sq_nonneg (‖a.coeff (n - m)‖ - ‖b.coeff m‖)]

end CoeffConvolution

/-- Weighted `ℓ¹` bound for `a ∈ H^r` against `weight t` when `t + 1/2 < r`, obtained via the
isometry `weightEquiv r (r - t)`. -/
private theorem summable_and_tsum_weight_mul_norm_coeff_le (htr : t + 1 / 2 < r)
    (a : CircleSobolev r G) :
    Summable (fun n ↦ weight t n * ‖a.coeff n‖) ∧
      ∑' n, weight t n * ‖a.coeff n‖ ≤ √(∑' n, weight (-(2 * (r - t))) n) * ‖a‖ := by
  have hrt : 1 / 2 < r - t := by linarith
  let a' := weightEquiv r (r - t) G a
  have hcoeff (n : ℤ) : ‖a'.coeff n‖ = weight t n * ‖a.coeff n‖ := by
    rw [coeff_weightEquiv, sub_sub_cancel, norm_smul, norm_weight]
  refine ⟨(summable_norm_coeff hrt a').congr hcoeff, ?_⟩
  simpa only [← hcoeff, LinearIsometryEquiv.norm_map, a'] using tsum_norm_coeff_le hrt a'

/-- Asymmetric weighted `ℓ²` estimate for `ℝ≥0∞` discrete convolution under a submultiplicative
lower-bounded weight. -/
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
    norm_num [ENNReal.rpow_two] at h
    exact h
  have hα_le : ∑' m, α m ≤ ∑' m, ω m * α m :=
    _root_.tsum_le_tsum fun m ↦ le_mul_of_one_le_left' (h1ω m)
  have hβ_le : ∑' k, β k ^ 2 ≤ ∑' k, (ω k * β k) ^ 2 :=
    _root_.tsum_le_tsum fun k ↦ pow_le_pow_left' (le_mul_of_one_le_left' (h1ω k)) 2
  calc ∑' n, (ω n * (α ⋆ᵣ₊ β) n) ^ 2
      ≤ ∑' n, 2 * C ^ 2 *
          (((fun m ↦ ω m * α m) ⋆ᵣ₊ β) n ^ 2 + (α ⋆ᵣ₊ fun k ↦ ω k * β k) n ^ 2) :=
        _root_.tsum_le_tsum fun n ↦ by grw [hpt n, mul_pow, hsq]; exact le_of_eq (by ring)
    _ ≤ 2 * C ^ 2 *
          (((∑' m, ω m * α m) ^ 2 * ∑' k, β k ^ 2) +
            (∑' m, α m) ^ 2 * ∑' k, (ω k * β k) ^ 2) := by
        rw [ENNReal.tsum_mul_left, _root_.tsum_add]
        gcongr <;> exact tsum_addRingConvolution_sq_le' _ _
    _ ≤ 4 * C ^ 2 * ((∑' m, ω m * α m) ^ 2 * ∑' k, (ω k * β k) ^ 2) := by
        have hadd : (∑' m, ω m * α m) ^ 2 * (∑' k, β k ^ 2) +
            (∑' m, α m) ^ 2 * ∑' k, (ω k * β k) ^ 2 ≤
            2 * ((∑' m, ω m * α m) ^ 2 * ∑' k, (ω k * β k) ^ 2) := by
          rw [two_mul]; gcongr
        grw [hadd]
        exact le_of_eq (by ring)

private theorem tsum_ofReal_weight_mul_enorm_sq {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] (t : ℝ) (b : CircleSobolev t H) :
    ∑' k, (ENNReal.ofReal (weight t k) * ‖b.coeff k‖ₑ) ^ 2 = ENNReal.ofReal (‖b‖ ^ 2) := by
  rw [← (hasSum_sq_weight_mul_norm_coeff b).tsum_eq,
    ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ sq_nonneg _)
      (hasSum_sq_weight_mul_norm_coeff b).summable]
  exact tsum_congr fun k ↦ by
    simp [ENNReal.ofReal_pow (mul_nonneg (weight_nonneg t k) (norm_nonneg _)),
      ENNReal.ofReal_mul (weight_nonneg t k), ofReal_norm]

/-- Asymmetric weighted `ℓ²` convolution estimate in `ℝ≥0∞`: for `0 ≤ t` and `t + 1/2 < r`, an
`H^r` sequence convolves boundedly with an `H^t` sequence into `H^t`. -/
private theorem ofReal_tsum_sq_weight_mul_norm_addConvolution_asym_le (ht : 0 ≤ t)
    (htr : t + 1 / 2 < r) (B : G →L[ℝ] E' →L[ℝ] F) (a : CircleSobolev r G)
    (b : CircleSobolev t E') :
    ∑' n : ℤ, ENNReal.ofReal ((weight t n * ‖(a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff) n‖) ^ 2) ≤
      ENNReal.ofReal
        ((2 ^ (t + 1) * √(∑' n, weight (-(2 * (r - t))) n) * ‖B‖ * ‖a‖ * ‖b‖) ^ 2) := by
  set ω : ℤ → ℝ≥0∞ := fun n ↦ ENNReal.ofReal (weight t n)
  set α : ℤ → ℝ≥0∞ := fun n ↦ ‖a.coeff n‖ₑ
  set β : ℤ → ℝ≥0∞ := fun n ↦ ‖b.coeff n‖ₑ
  have hω (m k : ℤ) : ω (m + k) ≤ ENNReal.ofReal (2 ^ t) * (ω m + ω k) := by
    simp only [ω, weight_def, ← Int.norm_eq_abs]
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (one_add_norm_add_rpow_le ht m k)
  have h1ω (n : ℤ) : (1 : ℝ≥0∞) ≤ ω n := by
    simpa [ω] using ENNReal.ofReal_le_ofReal (one_le_weight ht n)
  obtain ⟨ha_sum, ha_le⟩ := summable_and_tsum_weight_mul_norm_coeff_le htr a
  have hωα_eq : ∑' m, ω m * α m = ENNReal.ofReal (∑' m, weight t m * ‖a.coeff m‖) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun m ↦ mul_nonneg (weight_nonneg t m) (norm_nonneg _))
      ha_sum]
    exact tsum_congr fun m ↦ by simp [ω, α, ENNReal.ofReal_mul (weight_nonneg t m), ofReal_norm]
  have hωβ_eq : ∑' k, (ω k * β k) ^ 2 = ENNReal.ofReal (‖b‖ ^ 2) :=
    tsum_ofReal_weight_mul_enorm_sq t b
  calc ∑' n : ℤ, ENNReal.ofReal ((weight t n * ‖(a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff) n‖) ^ 2)
      = ∑' n : ℤ, (ω n * ‖(a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff) n‖ₑ) ^ 2 :=
        tsum_congr fun n ↦ by
          simp [ω, ENNReal.ofReal_pow (mul_nonneg (weight_nonneg t n) (norm_nonneg _)),
            ENNReal.ofReal_mul (weight_nonneg t n), ofReal_norm]
    _ ≤ ‖B‖ₑ ^ 2 * ∑' n, (ω n * (α ⋆ᵣ₊ β) n) ^ 2 := by
        rw [← ENNReal.tsum_mul_left]
        refine _root_.tsum_le_tsum fun n ↦ ?_
        rw [← mul_pow, mul_left_comm]
        gcongr
        exact enorm_addConvolution_le B a.coeff b.coeff n
    _ ≤ ‖B‖ₑ ^ 2 * (4 * ENNReal.ofReal (2 ^ t) ^ 2 *
          ((∑' m, ω m * α m) ^ 2 * ∑' k, (ω k * β k) ^ 2)) := by
        gcongr
        exact tsum_mul_addRingConvolution_sq_le hω h1ω
    _ ≤ ENNReal.ofReal
          ((2 ^ (t + 1) * √(∑' n, weight (-(2 * (r - t))) n) * ‖B‖ * ‖a‖ * ‖b‖) ^ 2) := by
        rw [hωα_eq, hωβ_eq, ← ofReal_norm, ← ENNReal.ofReal_ofNat 4,
          ← ENNReal.ofReal_pow (norm_nonneg B), ← ENNReal.ofReal_pow (by positivity),
          ← ENNReal.ofReal_pow (tsum_nonneg fun m ↦ mul_nonneg (weight_nonneg t m) (norm_nonneg _)),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (sq_nonneg ‖B‖)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h2t : (4 : ℝ) * (2 ^ t) ^ 2 = (2 ^ (t + 1)) ^ 2 := by
          rw [Real.rpow_add two_pos, Real.rpow_one]
          ring
        have hsum_nn : 0 ≤ ∑' m, weight t m * ‖a.coeff m‖ :=
          tsum_nonneg fun m ↦ mul_nonneg (weight_nonneg t m) (norm_nonneg _)
        calc ‖B‖ ^ 2 * (4 * (2 ^ t) ^ 2 * ((∑' m, weight t m * ‖a.coeff m‖) ^ 2 * ‖b‖ ^ 2))
            ≤ ‖B‖ ^ 2 * ((2 ^ (t + 1)) ^ 2 *
                ((√(∑' n, weight (-(2 * (r - t))) n) * ‖a‖) ^ 2 * ‖b‖ ^ 2)) := by
              rw [h2t]
              gcongr
          _ = (2 ^ (t + 1) * √(∑' n, weight (-(2 * (r - t))) n) * ‖B‖ * ‖a‖ * ‖b‖) ^ 2 := by
              ring

private def coeffConvolutionAsymAux (ht : 0 ≤ t) (htr : t + 1 / 2 < r) (B : G →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev r G) (b : CircleSobolev t E') : CircleSobolev t F where
  coeff := a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff
  memℓp_weight_smul_coeff := (memℓp_weight_smul_iff _).2 <|
    (ENNReal.summable_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (ofReal_tsum_sq_weight_mul_norm_addConvolution_asym_le ht htr B a b))).congr
      fun _ ↦ ENNReal.toReal_ofReal (sq_nonneg _)

private theorem norm_coeffConvolutionAsymAux_le (ht : 0 ≤ t) (htr : t + 1 / 2 < r)
    (B : G →L[ℝ] E' →L[ℝ] F) (a : CircleSobolev r G) (b : CircleSobolev t E') :
    ‖coeffConvolutionAsymAux ht htr B a b‖ ≤
      2 ^ (t + 1) * √(∑' n, weight (-(2 * (r - t))) n) * ‖B‖ * ‖a‖ * ‖b‖ := by
  have hbound : 0 ≤ 2 ^ (t + 1) * √(∑' n, weight (-(2 * (r - t))) n) * ‖B‖ * ‖a‖ * ‖b‖ := by
    positivity
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) hbound two_ne_zero).1 ?_
  rw [← ENNReal.ofReal_le_ofReal_iff (sq_nonneg _),
    ← (hasSum_sq_weight_mul_norm_coeff (coeffConvolutionAsymAux ht htr B a b)).tsum_eq,
    ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ sq_nonneg _)
      (hasSum_sq_weight_mul_norm_coeff (coeffConvolutionAsymAux ht htr B a b)).summable]
  exact ofReal_tsum_sq_weight_mul_norm_addConvolution_asym_le ht htr B a b

/-- Discrete convolution of Fourier coefficients along a continuous real-bilinear map at asymmetric
orders `0 ≤ t` and `t + 1/2 < r`. -/
private def coeffConvolutionAsym [CompleteSpace F] (ht : 0 ≤ t) (htr : t + 1 / 2 < r)
    (B : G →L[ℝ] E' →L[ℝ] F) :
    CircleSobolev r G →L[ℝ] CircleSobolev t E' →L[ℝ] CircleSobolev t F :=
  have hr0 : 0 ≤ r := by linarith
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (coeffConvolutionAsymAux ht htr B)
      (fun a a' b ↦ CircleSobolev.ext <|
        (addConvolutionExists_asym hr0 ht B a b).add_distrib _
          (addConvolutionExists_asym hr0 ht B a' b))
      (fun c a b ↦ CircleSobolev.ext <| funext fun n ↦ by
        change ((c • a).coeff ⋆₊[B.toLinearMap₁₂] b.coeff) n =
          (c • coeffConvolutionAsymAux ht htr B a b).coeff n
        rw [coeff_real_smul, coeff_real_smul]
        exact ((addConvolutionExists_asym hr0 ht B a b) n).vadd_convolution B.toLinearMap₁₂)
      (fun a b b' ↦ CircleSobolev.ext <|
        (addConvolutionExists_asym hr0 ht B a b).distrib_add _
          (addConvolutionExists_asym hr0 ht B a b'))
      (fun c a b ↦ CircleSobolev.ext <| funext fun n ↦ by
        change (a.coeff ⋆₊[B.toLinearMap₁₂] (c • b).coeff) n =
          (c • coeffConvolutionAsymAux ht htr B a b).coeff n
        rw [coeff_real_smul, coeff_real_smul]
        exact ((addConvolutionExists_asym hr0 ht B a b) n).convolution_vadd B.toLinearMap₁₂))
    (2 ^ (t + 1) * √(∑' n, weight (-(2 * (r - t))) n) * ‖B‖)
    (fun a b ↦ by simpa only [LinearMap.mk₂_apply] using
      norm_coeffConvolutionAsymAux_le ht htr B a b)

@[simp]
private theorem coeff_coeffConvolutionAsym [CompleteSpace F] (ht : 0 ≤ t) (htr : t + 1 / 2 < r)
    (B : G →L[ℝ] E' →L[ℝ] F) (a : CircleSobolev r G) (b : CircleSobolev t E') :
    (coeffConvolutionAsym ht htr B a b).coeff = a.coeff ⋆₊[B.toLinearMap₁₂] b.coeff :=
  (rfl)

/-! ### Four-part sesquilinear decomposition and public real-bilinear convolutions -/

private def bilinearShift10 (L : E →L[ℝ] E' →L[ℝ] F) : E →L[ℝ] E' →L[ℝ] F :=
  ((ContinuousLinearMap.compL ℝ E' F F (Complex.smulIEquiv F : F →L[ℝ] F)).comp L).comp
    (Complex.smulIEquiv E : E →L[ℝ] E)

private def bilinearShift01 (L : E →L[ℝ] E' →L[ℝ] F) : E →L[ℝ] E' →L[ℝ] F :=
  (ContinuousLinearMap.compL ℝ E' F F (Complex.smulIEquiv F : F →L[ℝ] F)).comp
    (L.flip.comp (Complex.smulIEquiv E' : E' →L[ℝ] E')).flip

private def bilinearShift11 (L : E →L[ℝ] E' →L[ℝ] F) : E →L[ℝ] E' →L[ℝ] F :=
  ((L.comp (Complex.smulIEquiv E : E →L[ℝ] E)).flip.comp
    (Complex.smulIEquiv E' : E' →L[ℝ] E')).flip

@[simp]
private theorem bilinearShift10_apply (L : E →L[ℝ] E' →L[ℝ] F) (u : E) (v : E') :
    bilinearShift10 L u v = I • L (I • u) v := by
  simp [bilinearShift10]

@[simp]
private theorem bilinearShift01_apply (L : E →L[ℝ] E' →L[ℝ] F) (u : E) (v : E') :
    bilinearShift01 L u v = I • L u (I • v) := by
  simp [bilinearShift01]

@[simp]
private theorem bilinearShift11_apply (L : E →L[ℝ] E' →L[ℝ] F) (u : E) (v : E') :
    bilinearShift11 L u v = L (I • u) (I • v) := by
  simp [bilinearShift11]

private theorem norm_bilinearShift10_le (L : E →L[ℝ] E' →L[ℝ] F) : ‖bilinearShift10 L‖ ≤ ‖L‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L) fun u ↦
    ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg L) (norm_nonneg u)) fun v ↦ by
      simpa [norm_smul] using L.le_opNorm₂ (I • u) v

private theorem norm_bilinearShift01_le (L : E →L[ℝ] E' →L[ℝ] F) : ‖bilinearShift01 L‖ ≤ ‖L‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L) fun u ↦
    ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg L) (norm_nonneg u)) fun v ↦ by
      simpa [norm_smul] using L.le_opNorm₂ u (I • v)

private theorem norm_bilinearShift11_le (L : E →L[ℝ] E' →L[ℝ] F) : ‖bilinearShift11 L‖ ≤ ‖L‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L) fun u ↦
    ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg L) (norm_nonneg u)) fun v ↦ by
      simpa [norm_smul] using L.le_opNorm₂ (I • u) (I • v)

private def partLL (L : E →L[ℝ] E' →L[ℝ] F) : E →L[ℝ] E' →L[ℝ] F :=
  (4⁻¹ : ℝ) • (L - bilinearShift10 L - bilinearShift01 L - bilinearShift11 L)

private def partLA (L : E →L[ℝ] E' →L[ℝ] F) : E →L[ℝ] E' →L[ℝ] F :=
  (4⁻¹ : ℝ) • (L - bilinearShift10 L + bilinearShift01 L + bilinearShift11 L)

private def partAL (L : E →L[ℝ] E' →L[ℝ] F) : E →L[ℝ] E' →L[ℝ] F :=
  (4⁻¹ : ℝ) • (L + bilinearShift10 L - bilinearShift01 L + bilinearShift11 L)

private def partAA (L : E →L[ℝ] E' →L[ℝ] F) : E →L[ℝ] E' →L[ℝ] F :=
  (4⁻¹ : ℝ) • (L + bilinearShift10 L + bilinearShift01 L - bilinearShift11 L)

private theorem part_sum_apply (L : E →L[ℝ] E' →L[ℝ] F) (u : E) (v : E') :
    partLL L u v + partLA L u v + partAL L u v + partAA L u v = L u v := by
  simp only [partLL, partLA, partAL, partAA, smul_apply, add_apply, sub_apply]
  module

private theorem norm_four_inv_combo_le {M : ℝ} (hM : 0 ≤ M) {A B C D : E →L[ℝ] E' →L[ℝ] F}
    (hA : ‖A‖ ≤ M) (hB : ‖B‖ ≤ M) (hC : ‖C‖ ≤ M) (hD : ‖D‖ ≤ M) :
    ‖(4⁻¹ : ℝ) • (A + B + C + D)‖ ≤ M :=
  ContinuousLinearMap.opNorm_le_bound _ hM fun u ↦ by
    rw [smul_apply, norm_smul, Real.norm_of_nonneg (by positivity)]
    have h1 := norm_add_le ((A + B + C) u) (D u)
    have h2 := norm_add_le ((A + B) u) (C u)
    have h3 := norm_add_le (A u) (B u)
    have ha : ‖A u‖ ≤ M * ‖u‖ :=
      (A.le_opNorm u).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg u))
    have hb : ‖B u‖ ≤ M * ‖u‖ :=
      (B.le_opNorm u).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg u))
    have hc : ‖C u‖ ≤ M * ‖u‖ :=
      (C.le_opNorm u).trans (mul_le_mul_of_nonneg_right hC (norm_nonneg u))
    have hd : ‖D u‖ ≤ M * ‖u‖ :=
      (D.le_opNorm u).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg u))
    simp only [add_apply] at h1 h2 h3 ⊢
    linarith

private theorem norm_neg_clm_le {M : ℝ} (hM : 0 ≤ M) {B : E →L[ℝ] E' →L[ℝ] F} (hB : ‖B‖ ≤ M) :
    ‖-B‖ ≤ M :=
  ContinuousLinearMap.opNorm_le_bound _ hM fun u ↦ by
    rw [neg_apply, ContinuousLinearMap.opNorm_neg]
    exact (B.le_opNorm u).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg u))

private theorem norm_partLL_le (L : E →L[ℝ] E' →L[ℝ] F) : ‖partLL L‖ ≤ ‖L‖ := by
  rw [partLL, sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg]
  exact norm_four_inv_combo_le (norm_nonneg L) le_rfl
    (norm_neg_clm_le (norm_nonneg L) (norm_bilinearShift10_le L))
    (norm_neg_clm_le (norm_nonneg L) (norm_bilinearShift01_le L))
    (norm_neg_clm_le (norm_nonneg L) (norm_bilinearShift11_le L))

private theorem norm_partLA_le (L : E →L[ℝ] E' →L[ℝ] F) : ‖partLA L‖ ≤ ‖L‖ := by
  rw [partLA, sub_eq_add_neg]
  exact norm_four_inv_combo_le (norm_nonneg L) le_rfl
    (norm_neg_clm_le (norm_nonneg L) (norm_bilinearShift10_le L))
    (norm_bilinearShift01_le L) (norm_bilinearShift11_le L)

private theorem norm_partAL_le (L : E →L[ℝ] E' →L[ℝ] F) : ‖partAL L‖ ≤ ‖L‖ := by
  rw [partAL, sub_eq_add_neg]
  exact norm_four_inv_combo_le (norm_nonneg L) le_rfl (norm_bilinearShift10_le L)
    (norm_neg_clm_le (norm_nonneg L) (norm_bilinearShift01_le L)) (norm_bilinearShift11_le L)

private theorem norm_partAA_le (L : E →L[ℝ] E' →L[ℝ] F) : ‖partAA L‖ ≤ ‖L‖ := by
  rw [partAA, sub_eq_add_neg]
  exact norm_four_inv_combo_le (norm_nonneg L) le_rfl (norm_bilinearShift10_le L)
    (norm_bilinearShift01_le L) (norm_neg_clm_le (norm_nonneg L) (norm_bilinearShift11_le L))

private theorem i_smul_i_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (v : V) :
    I • I • v = -v := by
  rw [smul_smul, I_mul_I, neg_one_smul]

private theorem sesquilinear_of_map_I (B : E →L[ℝ] E' →L[ℝ] F) {s₁ s₂ : ℂ}
    (h₁ : ∀ x y, B (I • x) y = s₁ • B x y) (h₂ : ∀ x y, B x (I • y) = s₂ • B x y)
    {φ ψ : ℂ → ℂ} (hφ : ∀ z : ℂ, (z.re : ℂ) + z.im * s₁ = φ z)
    (hψ : ∀ w : ℂ, (w.re : ℂ) + w.im * s₂ = ψ w) (z w : ℂ) (u : E) (v : E') :
    B (z • u) (w • v) = (φ z * ψ w) • B u v := by
  rw [← Complex.re_smul_add_im_smul z u, ← Complex.re_smul_add_im_smul w v]
  simp only [map_add, add_apply, map_smul, smul_apply, h₁, h₂]
  simp only [← Complex.coe_smul, ← hφ z, ← hψ w]
  module

private theorem conj_eq_re_sub_im (z : ℂ) : (z.re : ℂ) + z.im * (-I) = starRingEnd ℂ z := by
  apply Complex.ext <;> simp

private theorem partLL_smul (L : E →L[ℝ] E' →L[ℝ] F) (z w : ℂ) (u : E) (v : E') :
    partLL L (z • u) (w • v) = (z * w) • partLL L u v :=
  sesquilinear_of_map_I (partLL L)
    (fun x y ↦ by
      simp only [partLL, smul_apply, sub_apply, bilinearShift10_apply, bilinearShift01_apply,
        bilinearShift11_apply, smul_comm I (4⁻¹ : ℝ), smul_sub, i_smul_i_smul, map_neg, neg_apply,
        smul_neg]
      abel)
    (fun x y ↦ by
      simp only [partLL, smul_apply, sub_apply, bilinearShift10_apply, bilinearShift01_apply,
        bilinearShift11_apply, smul_comm I (4⁻¹ : ℝ), smul_sub, i_smul_i_smul, map_neg, smul_neg]
      abel)
    Complex.re_add_im Complex.re_add_im z w u v

private theorem partLA_smul (L : E →L[ℝ] E' →L[ℝ] F) (z w : ℂ) (u : E) (v : E') :
    partLA L (z • u) (w • v) = (z * starRingEnd ℂ w) • partLA L u v :=
  sesquilinear_of_map_I (partLA L)
    (fun x y ↦ by
      simp only [partLA, smul_apply, add_apply, sub_apply, bilinearShift10_apply,
        bilinearShift01_apply, bilinearShift11_apply, smul_comm I (4⁻¹ : ℝ), smul_add, smul_sub,
        i_smul_i_smul, map_neg, neg_apply, smul_neg]
      abel)
    (fun x y ↦ by
      simp only [partLA, smul_apply, add_apply, sub_apply, bilinearShift10_apply,
        bilinearShift01_apply, bilinearShift11_apply, neg_smul, smul_comm I (4⁻¹ : ℝ), smul_add,
        smul_sub, i_smul_i_smul, map_neg, smul_neg]
      abel)
    Complex.re_add_im conj_eq_re_sub_im z w u v

private theorem partAL_smul (L : E →L[ℝ] E' →L[ℝ] F) (z w : ℂ) (u : E) (v : E') :
    partAL L (z • u) (w • v) = (starRingEnd ℂ z * w) • partAL L u v :=
  sesquilinear_of_map_I (partAL L)
    (fun x y ↦ by
      simp only [partAL, smul_apply, add_apply, sub_apply, bilinearShift10_apply,
        bilinearShift01_apply, bilinearShift11_apply, neg_smul, smul_comm I (4⁻¹ : ℝ), smul_add,
        smul_sub, i_smul_i_smul, map_neg, neg_apply, smul_neg]
      abel)
    (fun x y ↦ by
      simp only [partAL, smul_apply, add_apply, sub_apply, bilinearShift10_apply,
        bilinearShift01_apply, bilinearShift11_apply, smul_comm I (4⁻¹ : ℝ), smul_add, smul_sub,
        i_smul_i_smul, map_neg, smul_neg]
      abel)
    conj_eq_re_sub_im Complex.re_add_im z w u v

private theorem partAA_smul (L : E →L[ℝ] E' →L[ℝ] F) (z w : ℂ) (u : E) (v : E') :
    partAA L (z • u) (w • v) = (starRingEnd ℂ z * starRingEnd ℂ w) • partAA L u v :=
  sesquilinear_of_map_I (partAA L)
    (fun x y ↦ by
      simp only [partAA, smul_apply, add_apply, sub_apply, bilinearShift10_apply,
        bilinearShift01_apply, bilinearShift11_apply, neg_smul, smul_comm I (4⁻¹ : ℝ), smul_add,
        smul_sub, i_smul_i_smul, map_neg, neg_apply, smul_neg]
      abel)
    (fun x y ↦ by
      simp only [partAA, smul_apply, add_apply, sub_apply, bilinearShift10_apply,
        bilinearShift01_apply, bilinearShift11_apply, neg_smul, smul_comm I (4⁻¹ : ℝ), smul_add,
        smul_sub, i_smul_i_smul, map_neg, smul_neg]
      abel)
    conj_eq_re_sub_im conj_eq_re_sub_im z w u v

private def reflectRealCLM : CircleSobolev s G →L[ℝ] CircleSobolev s G :=
  (reflect : CircleSobolev s G ≃ₗᵢ[ℂ] CircleSobolev s G).toLinearIsometry.toContinuousLinearMap
    |>.restrictScalars ℝ

@[simp]
private theorem coeff_reflectRealCLM (b : CircleSobolev s G) (n : ℤ) :
    (reflectRealCLM b).coeff n = b.coeff (-n) := by
  simp [reflectRealCLM]

private theorem reflectRealCLM_inclusion (h : t ≤ s) (b : CircleSobolev s G) :
    reflectRealCLM (inclusion h b) = inclusion h (reflectRealCLM b) :=
  CircleSobolev.ext <| funext fun _ ↦ by simp

section PublicConvolutions

variable [CompleteSpace F]

/-- **Symmetric real-bilinear product on `H^s`, `s > 1/2`.** A continuous real-bilinear map
`L : E →L[ℝ] E' →L[ℝ] F` induces a continuous real-bilinear map
`H^s(E) →L[ℝ] H^s(E') →L[ℝ] H^s(F)`. On continuous representatives it is the pointwise map
`x ↦ L (a x) (b x)` (`toContinuousMap_realConvolution_apply`). -/
def realConvolution (hs : 1 / 2 < s) (L : E →L[ℝ] E' →L[ℝ] F) :
    CircleSobolev s E →L[ℝ] CircleSobolev s E' →L[ℝ] CircleSobolev s F :=
  coeffConvolution hs (partLL L) +
    ((coeffConvolution hs (partLA L)).flip.comp reflectRealCLM).flip +
    (coeffConvolution hs (partAL L)).comp reflectRealCLM +
    (((coeffConvolution hs (partAA L)).comp reflectRealCLM).flip.comp reflectRealCLM).flip

private theorem realConvolution_apply (hs : 1 / 2 < s) (L : E →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev s E) (b : CircleSobolev s E') :
    realConvolution hs L a b =
      coeffConvolution hs (partLL L) a b +
        coeffConvolution hs (partLA L) a (reflectRealCLM b) +
        coeffConvolution hs (partAL L) (reflectRealCLM a) b +
        coeffConvolution hs (partAA L) (reflectRealCLM a) (reflectRealCLM b) := by
  simp [realConvolution]

/-- **Product estimate for `realConvolution` on `H^s`, `s > 1/2`.** -/
theorem norm_realConvolution_le (hs : 1 / 2 < s) (L : E →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev s E) (b : CircleSobolev s E') :
    ‖realConvolution hs L a b‖ ≤
      2 ^ (s + 3) * √(∑' n, weight (-(2 * s)) n) * ‖L‖ * ‖a‖ * ‖b‖ := by
  set K := 2 ^ (s + 1) * √(∑' n, weight (-(2 * s)) n)
  have hra : ‖reflectRealCLM a‖ = ‖a‖ := reflect.norm_map a
  have hrb : ‖reflectRealCLM b‖ = ‖b‖ := reflect.norm_map b
  have hpiece {B : E →L[ℝ] E' →L[ℝ] F} (hB : ‖B‖ ≤ ‖L‖) (a' : CircleSobolev s E)
      (b' : CircleSobolev s E') (ha' : ‖a'‖ = ‖a‖) (hb' : ‖b'‖ = ‖b‖) :
      ‖coeffConvolution hs B a' b'‖ ≤ K * ‖L‖ * ‖a‖ * ‖b‖ := by
    calc ‖coeffConvolution hs B a' b'‖
        ≤ K * ‖B‖ * ‖a'‖ * ‖b'‖ := norm_coeffConvolutionAux_le hs B a' b'
      _ ≤ K * ‖L‖ * ‖a‖ * ‖b‖ := by rw [ha', hb']; gcongr
  have h1 := hpiece (norm_partLL_le L) a b rfl rfl
  have h2 := hpiece (norm_partLA_le L) a (reflectRealCLM b) rfl hrb
  have h3 := hpiece (norm_partAL_le L) (reflectRealCLM a) b hra rfl
  have h4 := hpiece (norm_partAA_le L) (reflectRealCLM a) (reflectRealCLM b) hra hrb
  rw [realConvolution_apply]
  have hsum : ‖coeffConvolution hs (partLL L) a b +
      coeffConvolution hs (partLA L) a (reflectRealCLM b) +
      coeffConvolution hs (partAL L) (reflectRealCLM a) b +
      coeffConvolution hs (partAA L) (reflectRealCLM a) (reflectRealCLM b)‖ ≤
      4 * (K * ‖L‖ * ‖a‖ * ‖b‖) := by
    have := norm_add_le
      (coeffConvolution hs (partLL L) a b + coeffConvolution hs (partLA L) a (reflectRealCLM b) +
        coeffConvolution hs (partAL L) (reflectRealCLM a) b)
      (coeffConvolution hs (partAA L) (reflectRealCLM a) (reflectRealCLM b))
    have := norm_add_le
      (coeffConvolution hs (partLL L) a b + coeffConvolution hs (partLA L) a (reflectRealCLM b))
      (coeffConvolution hs (partAL L) (reflectRealCLM a) b)
    have := norm_add_le (coeffConvolution hs (partLL L) a b)
      (coeffConvolution hs (partLA L) a (reflectRealCLM b))
    linarith
  refine hsum.trans_eq ?_
  have h2s : (4 : ℝ) * 2 ^ (s + 1) = 2 ^ (s + 3) := by
    have h4 : (4 : ℝ) = 2 ^ (2 : ℝ) := by norm_num
    rw [h4, ← Real.rpow_add two_pos]
    exact congrArg ((2 : ℝ) ^ ·) (by ring)
  calc 4 * (K * ‖L‖ * ‖a‖ * ‖b‖)
      = (4 * 2 ^ (s + 1)) * √(∑' n, weight (-(2 * s)) n) * ‖L‖ * ‖a‖ * ‖b‖ := by
        simp only [K]; ring
    _ = 2 ^ (s + 3) * √(∑' n, weight (-(2 * s)) n) * ‖L‖ * ‖a‖ * ‖b‖ := by rw [h2s]

/-- **Asymmetric real-bilinear product `H^r(E) × H^t(E') → H^t(F)` for `0 ≤ t` and
`t + 1/2 < r`.** Extends `realConvolution` (`realConvolutionAsym_inclusion_right`) so that an `H^r`
multiplier acts boundedly on `H^t` even when `t ≤ 1/2`. -/
def realConvolutionAsym (ht : 0 ≤ t) (htr : t + 1 / 2 < r) (L : E →L[ℝ] E' →L[ℝ] F) :
    CircleSobolev r E →L[ℝ] CircleSobolev t E' →L[ℝ] CircleSobolev t F :=
  coeffConvolutionAsym ht htr (partLL L) +
    ((coeffConvolutionAsym ht htr (partLA L)).flip.comp reflectRealCLM).flip +
    (coeffConvolutionAsym ht htr (partAL L)).comp reflectRealCLM +
    (((coeffConvolutionAsym ht htr (partAA L)).comp reflectRealCLM).flip.comp reflectRealCLM).flip

private theorem realConvolutionAsym_apply (ht : 0 ≤ t) (htr : t + 1 / 2 < r)
    (L : E →L[ℝ] E' →L[ℝ] F) (a : CircleSobolev r E) (b : CircleSobolev t E') :
    realConvolutionAsym ht htr L a b =
      coeffConvolutionAsym ht htr (partLL L) a b +
        coeffConvolutionAsym ht htr (partLA L) a (reflectRealCLM b) +
        coeffConvolutionAsym ht htr (partAL L) (reflectRealCLM a) b +
        coeffConvolutionAsym ht htr (partAA L) (reflectRealCLM a) (reflectRealCLM b) := by
  simp [realConvolutionAsym]

/-- **On continuous representatives `realConvolution` is pointwise:** for `s > 1/2`, the continuous
function attached to `realConvolution hs L a b` is `x ↦ L (a x) (b x)`. -/
@[simp]
theorem toContinuousMap_realConvolution_apply (T : ℝ) [Fact (0 < T)] [CompleteSpace E]
    [CompleteSpace E'] (hs : 1 / 2 < s) (L : E →L[ℝ] E' →L[ℝ] F) (a : CircleSobolev s E)
    (b : CircleSobolev s E') (x : AddCircle T) :
    toContinuousMap T hs (realConvolution hs L a b) x =
      L (toContinuousMap T hs a x) (toContinuousMap T hs b x) := by
  have hA := (hasSum_toContinuousMap T hs a).mapL (ContinuousMap.evalCLM ℂ x)
  have hB := (hasSum_toContinuousMap T hs b).mapL (ContinuousMap.evalCLM ℂ x)
  simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply', ContinuousMap.const_apply]
    at hA hB
  have hAn := (Equiv.neg ℤ).hasSum_iff.2 hA
  have hBn := (Equiv.neg ℤ).hasSum_iff.2 hB
  have hLL := toContinuousMap_coeffConvolution_eq T hs (partLL L) a b x hA hB fun m k ↦ by
    rw [partLL_smul, fourier_add]
  have hLA := toContinuousMap_coeffConvolution_eq T hs (partLA L) a (reflectRealCLM b) x hA hBn
    fun m k ↦ by
      simp only [coeff_reflectRealCLM, Function.comp_apply, Equiv.neg_apply, partLA_smul,
        fourier_neg, RingHomCompTriple.comp_apply, RingHom.id_apply, fourier_add]
  have hAL := toContinuousMap_coeffConvolution_eq T hs (partAL L) (reflectRealCLM a) b x hAn hB
    fun m k ↦ by
      simp only [coeff_reflectRealCLM, Function.comp_apply, Equiv.neg_apply, partAL_smul,
        fourier_neg, RingHomCompTriple.comp_apply, RingHom.id_apply, fourier_add]
  have hAA := toContinuousMap_coeffConvolution_eq T hs (partAA L) (reflectRealCLM a)
    (reflectRealCLM b) x hAn hBn fun m k ↦ by
      simp only [coeff_reflectRealCLM, Function.comp_apply, Equiv.neg_apply, partAA_smul,
        fourier_neg, RingHomCompTriple.comp_apply, RingHom.id_apply, fourier_add]
  rw [realConvolution_apply, map_add, map_add, map_add]
  simp only [ContinuousMap.add_apply, hLL, hLA, hAL, hAA, part_sum_apply]

/-- `realConvolution` commutes with the Sobolev inclusions `H^s → H^t`, `1/2 < t ≤ s`. -/
@[simp]
theorem realConvolution_inclusion (ht : 1 / 2 < t) (h : t ≤ s) (L : E →L[ℝ] E' →L[ℝ] F)
    (a : CircleSobolev s E) (b : CircleSobolev s E') :
    realConvolution ht L (inclusion h a) (inclusion h b) =
      inclusion h (realConvolution (ht.trans_le h) L a b) :=
  CircleSobolev.ext <| funext fun n ↦ by
    simp [realConvolution_apply, reflectRealCLM_inclusion]

/-- When the second factor also lies in `H^r`, `realConvolutionAsym` agrees with `realConvolution`
at order `r`. -/
@[simp]
theorem realConvolutionAsym_inclusion_right (ht : 0 ≤ t) (htr : t + 1 / 2 < r)
    (L : E →L[ℝ] E' →L[ℝ] F) (a : CircleSobolev r E) (b : CircleSobolev r E') :
    realConvolutionAsym ht htr L a (inclusion (by linarith) b) =
      inclusion (by linarith) (realConvolution (by linarith) L a b) :=
  CircleSobolev.ext <| funext fun n ↦ by
    simp [realConvolutionAsym_apply, realConvolution_apply, reflectRealCLM_inclusion]

/-- When both factors come from `H^s` with `r ≤ s`, `realConvolutionAsym` agrees with
`realConvolution` at order `s`. -/
@[simp]
theorem realConvolutionAsym_inclusion (ht : 0 ≤ t) (htr : t + 1 / 2 < r) (hrs : r ≤ s)
    (L : E →L[ℝ] E' →L[ℝ] F) (a : CircleSobolev s E) (b : CircleSobolev s E') :
    realConvolutionAsym ht htr L (inclusion hrs a) (inclusion (by linarith) b) =
      inclusion (by linarith) (realConvolution (by linarith) L a b) :=
  CircleSobolev.ext <| funext fun n ↦ by
    simp [realConvolutionAsym_apply, realConvolution_apply, reflectRealCLM_inclusion]

end PublicConvolutions

end CircleSobolev

end TauCeti
