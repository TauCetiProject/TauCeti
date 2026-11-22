/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.Derivative
public import TauCeti.Analysis.Sobolev.Circle.Lp
public import TauCeti.Analysis.Sobolev.Circle.Rotation
import TauCeti.Analysis.Fourier.AddCircle
import TauCeti.Analysis.Fourier.FourierCoeffOn
import TauCeti.Analysis.Fourier.Uniqueness
import TauCeti.MeasureTheory.Integral.ContinuousMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Continuous loops in the circle Sobolev space `H⁰`

For a finite-dimensional complex normed space `E`, every continuous loop `f : AddCircle T → E` is
square integrable, so its Fourier coefficients define an element of the Sobolev space `H⁰(E)`
of `TauCeti/Analysis/Sobolev/Circle/Basic.lean`. This file constructs that element as a
continuous linear map `C(AddCircle T, E) → H⁰(E)` and compares it with the continuous
representatives of the spaces `H^s(E)`, `s > 1/2`, and with their derivatives.

The map is assembled from the scalar case `H⁰(ℂ) = L²` (`TauCeti.CircleSobolev.toLpₗᵢ`) in the
coordinates of a basis of `E`. Its coefficients are the Fourier coefficients of the loop
(`TauCeti.CircleSobolev.coeff_ofContinuousMap`), independently of the basis.

The comparison with derivatives is the statement that weak and classical derivatives agree when
both are continuous. Let `a ∈ H¹(E)` have the continuous representative `u`. If the derivative of
`a`, an element of `H⁰(E)`, is the class of a continuous loop `g`, then `u` is differentiable
with derivative `g` (`TauCeti.CircleSobolev.hasDerivAt_toContinuousMap_of_derivative_eq`).
Conversely a loop with a continuous classical derivative comes from `H¹(E)`, with the derivative
in `H⁰(E)` given by the class of the classical derivative
(`TauCeti.CircleSobolev.exists_toContinuousMap_eq_and_derivative_eq`). The first statement is
proved by comparing `u` with a primitive of `g`: both have the same Fourier coefficients away
from frequency zero, because differentiation multiplies Fourier coefficients by `2πin / T`
(`TauCeti.fourierCoeff_of_hasDerivAt`).

## Main definitions

* `TauCeti.CircleSobolev.smulRight x`: the continuous linear map `H^s(ℂ) → H^s(E)` multiplying
  the coefficients of a scalar function by the vector `x`.
* `TauCeti.CircleSobolev.ofContinuousMap T`: the continuous linear map
  `C(AddCircle T, E) → H⁰(E)` sending a loop to its Fourier coefficients.

## Main statements

* `TauCeti.CircleSobolev.coeff_ofContinuousMap`: the coefficients of `ofContinuousMap T f` are
  the Fourier coefficients of `f`.
* `TauCeti.CircleSobolev.rotate_ofContinuousMap`: the rotation by `θ` of the class of a loop
  `f` is the class of the translated loop `x ↦ f (x + θ)`.
* `TauCeti.CircleSobolev.ofContinuousMap_toContinuousMap`: for `s > 1/2`, the continuous
  representative of `a ∈ H^s(E)` is sent back to `a`, regarded as an element of `H⁰(E)`.
* `TauCeti.CircleSobolev.ofContinuousMap_injective`: a continuous loop is determined by its
  class in `H⁰(E)`.
* `TauCeti.CircleSobolev.toContinuousMap_eq_iff`: for `s > 1/2`, the continuous representative of
  `a ∈ H^s(E)` is the continuous loop with the Fourier coefficients of `a`.
* `TauCeti.CircleSobolev.hasDerivAt_toContinuousMap_of_derivative_eq` and
  `TauCeti.CircleSobolev.exists_toContinuousMap_eq_and_derivative_eq`: continuous weak
  derivatives in `H¹(E)` are classical derivatives, and conversely.
* `TauCeti.CircleSobolev.inner_ofContinuousMap`, `TauCeti.CircleSobolev.real_inner_ofContinuousMap`:
  Parseval's identity, the inner product in `H⁰` of two continuous loops is the mean of their
  pointwise inner product.
* `TauCeti.CircleSobolev.norm_ofContinuousMap_sq`,
  `TauCeti.CircleSobolev.norm_ofContinuousMap_le_of_forall_norm_le`: the squared `H⁰` norm of a
  continuous loop is the mean of its squared pointwise norm, so pointwise domination of loops
  gives domination in `H⁰`.
* `TauCeti.CircleSobolev.integral_norm_sq_eq_mul_norm_ofContinuousMap_sq`: Parseval on a period,
  `∫_{[0, T]} ‖f‖² = T ‖ofContinuousMap T f‖²`.
* `TauCeti.CircleSobolev.eq_zero_of_abs_le_of_hilbertBasis`: a real-linear functional on
  continuous loops, bounded by a multiple of the `H⁰` norm and vanishing on loops forming a Hilbert
  basis of `H⁰`, vanishes.

## References

* Y. Katznelson, *An Introduction to Harmonic Analysis*, 3rd ed., Cambridge University Press,
  2004, Chapter I (Fourier coefficients of derivatives and of `L²` functions, and Parseval's
  identity).
-/

public section

noncomputable section

open MeasureTheory Complex
open scoped Real

namespace TauCeti

namespace CircleSobolev

variable {s : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The element of `H^s(E)` with coefficients `a.coeff n • x`. -/
private def smulRightFun (x : E) (a : CircleSobolev s ℂ) : CircleSobolev s E :=
  ⟨fun n ↦ a.coeff n • x, (a.memℓp_weight_smul_coeff.const_smul (‖x‖ : ℂ)).mono' fun n ↦ by
    simp only [Pi.smul_apply, norm_smul, norm_weight, Complex.norm_real, norm_norm]
    exact le_of_eq (by ring)⟩

private theorem norm_smulRightFun (x : E) (a : CircleSobolev s ℂ) :
    ‖smulRightFun x a‖ = ‖x‖ * ‖a‖ := by
  have h := (hasSum_sq_weight_mul_norm_coeff a).mul_left (‖x‖ ^ 2)
  have h' : HasSum (fun n ↦ (weight s n * ‖(smulRightFun x a).coeff n‖) ^ 2)
      ((‖x‖ * ‖a‖) ^ 2) := by
    convert h using 1
    · funext n
      simp only [smulRightFun, norm_smul]
      ring
    · ring
  have := (hasSum_sq_weight_mul_norm_coeff (smulRightFun x a)).unique h'
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 this

/-- The continuous linear map `H^s(ℂ) → H^s(E)` multiplying the Fourier coefficients of a scalar
function by the vector `x`: on continuous representatives it is `u ↦ (θ ↦ u(θ) • x)`. -/
def smulRight (x : E) : CircleSobolev s ℂ →L[ℂ] CircleSobolev s E :=
  LinearMap.mkContinuous
    { toFun := smulRightFun x
      map_add' a b := CircleSobolev.ext (funext fun n ↦ by simp [smulRightFun, add_smul])
      map_smul' c a := CircleSobolev.ext (funext fun n ↦ by simp [smulRightFun, smul_smul]) }
    ‖x‖ fun a ↦ (norm_smulRightFun x a).le

@[simp]
theorem coeff_smulRight (x : E) (a : CircleSobolev s ℂ) (n : ℤ) :
    (smulRight x a).coeff n = a.coeff n • x :=
  (rfl)

@[simp]
theorem norm_smulRight (x : E) (a : CircleSobolev s ℂ) : ‖smulRight x a‖ = ‖x‖ * ‖a‖ :=
  norm_smulRightFun x a

variable (T : ℝ) [hT : Fact (0 < T)]

section OfContinuousMap

variable [FiniteDimensional ℂ E]

/-- The element of `H⁰(E)` given by the Fourier coefficients of a continuous loop in a
finite-dimensional space `E`, as a continuous linear map. It is assembled in the coordinates of a
basis of `E` from the scalar identification of `H⁰(ℂ)` with `L²`; its coefficients do not depend
on that basis (`CircleSobolev.coeff_ofContinuousMap`). -/
def ofContinuousMap : C(AddCircle T, E) →L[ℂ] CircleSobolev 0 E :=
  ∑ i, (smulRight (Module.finBasis ℂ E i)).comp
    (((toLpₗᵢ T).symm : Lp ℂ 2 (AddCircle.haarAddCircle (T := T)) →L[ℂ] CircleSobolev 0 ℂ).comp
      ((ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ).comp
        (ContinuousLinearMap.compLeftContinuous ℂ (AddCircle T)
          (LinearMap.toContinuousLinearMap ((Module.finBasis ℂ E).coord i)))))

/-- The coefficients of `ofContinuousMap T f` are the Fourier coefficients of `f`. -/
@[simp]
theorem coeff_ofContinuousMap (f : C(AddCircle T, E)) (n : ℤ) :
    (ofContinuousMap T f).coeff n = fourierCoeff f n := by
  have := FiniteDimensional.completeSpace ℂ E
  set b := Module.finBasis ℂ E
  have hcoord (i) : fourierCoeff (fun x ↦ b.coord i (f x)) n = b.coord i (fourierCoeff f n) :=
    (LinearMap.toContinuousLinearMap (b.coord i)).fourierCoeff_comp
      (f.integrable AddCircle.haarAddCircle) n
  simp only [ofContinuousMap, FunLike.coe_sum, Finset.sum_apply, coeff_sum,
    ContinuousLinearMap.coe_comp, Function.comp_apply, coeff_smulRight]
  conv_rhs => rw [← b.sum_repr (fourierCoeff f n)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← b.coord_apply, ← hcoord]
  congr 1
  exact (coeff_toLpₗᵢ_symm T _ n).trans (fourierCoeff_toLp _ n)

/-- The rotation by `θ` of the class in `H⁰(E)` of a continuous loop `f` is the class of the
translated loop `x ↦ f (x + θ)`. -/
@[simp]
theorem rotate_ofContinuousMap (θ : AddCircle T) (f : C(AddCircle T, E)) :
    rotate θ (ofContinuousMap T f) = ofContinuousMap T (f.comp (ContinuousMap.addRight θ)) :=
  CircleSobolev.ext (funext fun n ↦ by
    rw [coeff_rotate, coeff_ofContinuousMap, coeff_ofContinuousMap, ContinuousMap.coe_comp,
      ContinuousMap.coe_addRight]
    exact (fourierCoeff_comp_add_right f θ n).symm)

end OfContinuousMap

section ContinuousRepresentative

variable [CompleteSpace E]

/-- **The continuous representative is determined by Fourier coefficients.** For `s > 1/2`, the
continuous representative of `a ∈ H^s(E)` is the continuous loop `F` exactly when the Fourier
coefficients of `F` are the coefficients of `a`. -/
theorem toContinuousMap_eq_iff (hs : 1 / 2 < s) (a : CircleSobolev s E) (F : C(AddCircle T, E)) :
    toContinuousMap T hs a = F ↔ ∀ n, fourierCoeff F n = a.coeff n := by
  refine ⟨fun h n ↦ h ▸ fourierCoeff_toContinuousMap T hs a n, fun h ↦ ?_⟩
  have hae := ((toContinuousMap T hs a).integrable AddCircle.haarAddCircle)
    |>.ae_eq_of_forall_fourierCoeff_eq (F.integrable AddCircle.haarAddCircle) fun n ↦ by
    rw [fourierCoeff_toContinuousMap, h]
  exact ContinuousMap.ext (congrFun ((map_continuous _).ae_eq_iff_eq _ F.continuous |>.1 hae))

end ContinuousRepresentative

section FiniteDimensional

variable [FiniteDimensional ℂ E]

/-- A finite-dimensional complex space is complete, as needed for continuous representatives. -/
local instance instCompleteSpaceOfContinuousMap : CompleteSpace E :=
  FiniteDimensional.completeSpace ℂ E

/-- For `s > 1/2`, the loop given by the continuous representative of `a ∈ H^s(E)` is `a` itself,
regarded as an element of `H⁰(E)`. -/
@[simp]
theorem ofContinuousMap_toContinuousMap (hs : 1 / 2 < s) (a : CircleSobolev s E) :
    ofContinuousMap T (toContinuousMap T hs a) = inclusion (by linarith) a :=
  CircleSobolev.ext (funext fun n ↦ by
    rw [coeff_ofContinuousMap, fourierCoeff_toContinuousMap, coeff_inclusion])

/-- A continuous loop is determined by its class in `H⁰(E)`. -/
theorem ofContinuousMap_injective : Function.Injective (ofContinuousMap (E := E) T) := by
  intro F G h
  have hae := (F.integrable AddCircle.haarAddCircle).ae_eq_of_forall_fourierCoeff_eq
    (G.integrable AddCircle.haarAddCircle) fun n ↦ by
      rw [← coeff_ofContinuousMap, h, coeff_ofContinuousMap]
  exact ContinuousMap.ext (congrFun ((map_continuous _).ae_eq_iff_eq _ G.continuous |>.1 hae))

/-- **Continuous weak derivatives are classical derivatives.** If the derivative in `H⁰(E)` of
`a ∈ H¹(E)` is the class of a continuous loop `g`, then the continuous representative of `a` is
differentiable, with derivative `g`. -/
theorem hasDerivAt_toContinuousMap_of_derivative_eq (a : CircleSobolev 1 E)
    (g : C(AddCircle T, E))
    (h : derivative T (show (0 : ℝ) + 1 ≤ 1 by norm_num) a = ofContinuousMap T g) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ toContinuousMap T (by norm_num) a y) (g x) x := by
  have hT0 : T ≠ 0 := hT.out.ne'
  have hcoeff (n : ℤ) : fourierCoeff g n = (2 * π * I * n / T : ℂ) • a.coeff n := by
    rw [← coeff_ofContinuousMap, ← h, coeff_derivative]
  have hgc : Continuous fun y : ℝ ↦ g y := g.continuous.comp (AddCircle.continuous_mk' T)
  -- The primitive `G` of `g` is periodic, because `g` has mean zero.
  set G : ℝ → E := fun y ↦ ∫ t in (0 : ℝ)..y, g t
  have hG (y : ℝ) : HasDerivAt G (g y) y := (hgc.integral_hasStrictDerivAt 0 y).hasDerivAt
  have hmean : ∫ t in (0 : ℝ)..0 + T, g t = 0 := by
    have h0 := hcoeff 0
    rw [fourierCoeff_eq_intervalIntegral g 0 0] at h0
    simpa [hT0] using h0
  have hper : Function.Periodic G T := fun y ↦ by
    have hgp : Function.Periodic (fun y : ℝ ↦ g y) T := fun y ↦ by simp
    simp only [G]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hgc.intervalIntegrable 0 y)
      (hgc.intervalIntegrable y (y + T)), hgp.intervalIntegral_add_eq y 0, hmean, add_zero]
  set Gc : C(AddCircle T, E) := ⟨hper.lift,
    continuous_coinduced_dom.2 <| continuous_iff_continuousAt.2 fun y ↦ (hG y).continuousAt⟩
  have hGc (y : ℝ) : Gc y = G y := hper.lift_coe y
  -- Away from frequency zero, `G` has the Fourier coefficients of `a`.
  have hGcoeff (n : ℤ) (hn : n ≠ 0) : fourierCoeff Gc n = a.coeff n := by
    have hl : (2 * π * I * n / T : ℂ) ≠ 0 := by
      simp [hn, Real.pi_ne_zero, I_ne_zero, hT0]
    refine smul_right_injective E hl ?_
    simp only [← hcoeff]
    exact (fourierCoeff_of_hasDerivAt (f := Gc) hG g.continuous n).symm
  set c := a.coeff 0 - fourierCoeff Gc 0
  have heq : toContinuousMap T (by norm_num) a = Gc + ContinuousMap.const _ c := by
    refine (toContinuousMap_eq_iff T _ a _).2 fun n ↦ ?_
    rw [ContinuousMap.coe_add, fourierCoeff.add (Gc.integrable AddCircle.haarAddCircle)
      ((ContinuousMap.const _ c).integrable AddCircle.haarAddCircle), Pi.add_apply,
      ContinuousMap.coe_const, ← Function.const_def, fourierCoeff_const]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [c]
    · simp [hn, hGcoeff n hn]
  simp only [heq, ContinuousMap.add_apply, hGc, ContinuousMap.const_apply]
  exact (hG x).add_const c

/-- **Classical derivatives are weak derivatives.** A continuous loop `F` whose lift to `ℝ` has the
continuous derivative `g` is the continuous representative of an element of `H¹(E)`, whose
derivative in `H⁰(E)` is the class of `g`. -/
theorem exists_toContinuousMap_eq_and_derivative_eq (F g : C(AddCircle T, E))
    (hF : ∀ x : ℝ, HasDerivAt (fun y : ℝ ↦ F y) (g x) x) :
    ∃ a : CircleSobolev 1 E, toContinuousMap T (by norm_num) a = F ∧
      derivative T (show (0 : ℝ) + 1 ≤ 1 by norm_num) a = ofContinuousMap T g := by
  obtain ⟨c, hc, hdc⟩ := exists_inclusion_eq_and_derivative_eq T (ofContinuousMap T F)
    (ofContinuousMap T g) fun n ↦ by
      rw [coeff_ofContinuousMap, coeff_ofContinuousMap, fourierCoeff_of_hasDerivAt hF g.continuous]
  have hmem : Memℓp (fun n ↦ weight 1 n • c.coeff n) 2 := by
    simpa only [zero_add] using c.memℓp_weight_smul_coeff
  refine ⟨⟨c.coeff, hmem⟩, (toContinuousMap_eq_iff T _ _ F).2 fun n ↦ ?_,
    CircleSobolev.ext (funext fun n ↦ ?_)⟩
  · rw [← coeff_ofContinuousMap, ← hc, coeff_inclusion]
  · rw [← hdc, coeff_derivative, coeff_derivative]

end FiniteDimensional

section Inner

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- **Parseval's identity for continuous loops.** For continuous loops `f`, `g` in a
finite-dimensional complex inner product space, the inner product in `H⁰` of their Fourier
coefficient sequences is the mean `∫ ⟪f x, g x⟫` over the circle, for the normalized Haar
measure. -/
theorem inner_ofContinuousMap (f g : C(AddCircle T, F)) :
    inner ℂ (ofContinuousMap T f) (ofContinuousMap T g) =
      ∫ x, inner ℂ (f x) (g x) ∂AddCircle.haarAddCircle := by
  have := FiniteDimensional.completeSpace ℂ F
  set e := stdOrthonormalBasis ℂ F
  -- The coordinates of a loop in the orthonormal basis `e`, and their Fourier coefficients.
  let φ (h : C(AddCircle T, F)) (j) : C(AddCircle T, ℂ) :=
    ⟨fun x ↦ inner ℂ (e j) (h x), continuous_const.inner h.continuous⟩
  have hcoeff (h : C(AddCircle T, F)) (j) (n : ℤ) :
      fourierCoeff (φ h j) n = inner ℂ (e j) (fourierCoeff h n) :=
    (innerSL ℂ (e j)).fourierCoeff_comp (h.integrable AddCircle.haarAddCircle) n
  -- The scalar Parseval identity for each pair of coordinates.
  have hj (j) : HasSum (fun n : ℤ ↦ inner ℂ (fourierCoeff f n) (e j) *
      inner ℂ (e j) (fourierCoeff g n)) (∫ x, inner ℂ (f x) (e j) * inner ℂ (e j) (g x)
        ∂AddCircle.haarAddCircle) := by
    convert fourierBasis.hasSum_inner_mul_inner
      (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (φ f j))
      (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (φ g j)) using 1
    · funext n
      simp only [← inner_conj_symm _ (fourierBasis n), inner_fourierBasis_left,
        fourierCoeff_toLp, hcoeff, inner_conj_symm]
    · rw [ContinuousMap.inner_toLp]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
      simp [φ, mul_comm]
  have hsum := hasSum_sum (s := Finset.univ) fun j _ ↦ hj j
  simp only [e.sum_inner_mul_inner] at hsum
  rw [inner_eq_tsum]
  simp only [mul_zero, weight_zero_left, Complex.ofReal_one, one_mul, coeff_ofContinuousMap]
  rw [hsum.tsum_eq, ← integral_finsetSum _ fun j _ ↦ ?_]
  · simp [e.sum_inner_mul_inner]
  · exact ((continuous_inner.comp (f.continuous.prodMk continuous_const)).mul
      (continuous_const.inner g.continuous)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

/-- **Parseval's identity for the real inner product.** The real inner product in `H⁰` of the
Fourier coefficient sequences of continuous loops `f`, `g` is the mean of `Re ⟪f x, g x⟫`. -/
theorem real_inner_ofContinuousMap (f g : C(AddCircle T, F)) :
    inner ℝ (ofContinuousMap T f) (ofContinuousMap T g) =
      ∫ x, (inner ℂ (f x) (g x)).re ∂AddCircle.haarAddCircle := by
  have hi : Integrable (fun x ↦ inner ℂ (f x) (g x)) AddCircle.haarAddCircle :=
    (continuous_inner.comp (f.continuous.prodMk g.continuous)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [real_inner_eq_re_inner, inner_ofContinuousMap, ← RCLike.re_eq_complex_re, ← integral_re hi]

/-- **Parseval's identity for the norm.** The squared norm in `H⁰` of the Fourier coefficient
sequence of a continuous loop `f` is the mean of `‖f x‖²`. -/
theorem norm_ofContinuousMap_sq (f : C(AddCircle T, F)) :
    ‖ofContinuousMap T f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂AddCircle.haarAddCircle := by
  rw [← real_inner_self_eq_norm_sq, real_inner_ofContinuousMap]
  simp only [← RCLike.re_eq_complex_re, inner_self_eq_norm_sq]

/-- Pointwise domination `‖f x‖ ≤ C ‖g x‖` of continuous loops gives the same domination of their
Fourier coefficient sequences in `H⁰`. -/
theorem norm_ofContinuousMap_le_of_forall_norm_le {f g : C(AddCircle T, F)} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, ‖f x‖ ≤ C * ‖g x‖) :
    ‖ofContinuousMap T f‖ ≤ C * ‖ofContinuousMap T g‖ := by
  have hint (u : C(AddCircle T, F)) :
      Integrable (fun x ↦ ‖u x‖ ^ 2) AddCircle.haarAddCircle :=
    (u.continuous.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, norm_ofContinuousMap_sq, norm_ofContinuousMap_sq, ← integral_const_mul]
  refine integral_mono (hint f) ((hint g).const_mul _) fun x ↦ ?_
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (h x) 2

/-- **Parseval's identity on a period.** For a continuous loop `f` of period `T`,
`∫_{[0, T]} ‖f‖² = T ‖ofContinuousMap T f‖²`. -/
theorem integral_norm_sq_eq_mul_norm_ofContinuousMap_sq (f : C(AddCircle T, F)) :
    ∫ t in Set.Icc 0 T, ‖f t‖ ^ 2 = T * ‖ofContinuousMap T f‖ ^ 2 := by
  have h := AddCircle.integral_preimage (T := T) 0 fun x ↦ ‖f x‖ ^ 2
  rw [zero_add] at h
  rw [norm_ofContinuousMap_sq, integral_Icc_eq_integral_Ioc, h,
    AddCircle.volume_eq_smul_haarAddCircle, integral_smul_measure,
    ENNReal.toReal_ofReal hT.out.le, smul_eq_mul]

/-- **Density in `H⁰`.** A real-linear functional on continuous loops bounded by a multiple of the
`H⁰` norm and vanishing on loops forming a Hilbert basis of `H⁰` vanishes. -/
theorem eq_zero_of_abs_le_of_hilbertBasis (Λ : C(AddCircle T, F) →ₗ[ℝ] ℝ) {K : ℝ}
    (hΛ : ∀ χ, |Λ χ| ≤ K * ‖ofContinuousMap T χ‖) {ι : Type*}
    (b : HilbertBasis ι ℝ (CircleSobolev 0 F)) (e : ι → C(AddCircle T, F))
    (hb : ∀ i, b i = ofContinuousMap T (e i)) (he : ∀ i, Λ (e i) = 0)
    (ψ : C(AddCircle T, F)) : Λ ψ = 0 := by
  -- The bound also holds with the nonnegative constant `|K|`.
  replace hΛ (χ : C(AddCircle T, F)) : |Λ χ| ≤ |K| * ‖ofContinuousMap T χ‖ :=
    (hΛ χ).trans (mul_le_mul_of_nonneg_right (le_abs_self K) (norm_nonneg _))
  have hK : 0 ≤ |K| := abs_nonneg K
  -- The loops on which `Λ` vanishes have a dense image in `H⁰`, since it contains the basis.
  set P : Submodule ℝ (CircleSobolev 0 F) := (LinearMap.ker Λ).map
    ((ofContinuousMap T : C(AddCircle T, F) →L[ℂ] CircleSobolev 0 F)
      |>.toLinearMap.restrictScalars ℝ)
  have hspan : Submodule.span ℝ (Set.range b) ≤ P :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact ⟨e i, he i, (hb i).symm⟩)
  have hmem : ofContinuousMap T ψ ∈ closure (P : Set (CircleSobolev 0 F)) := by
    have h := Submodule.topologicalClosure_mono hspan
    rw [b.dense_span, top_le_iff] at h
    rw [← Submodule.topologicalClosure_coe, h]
    trivial
  by_contra hne
  have hpos : 0 < |Λ ψ| := abs_pos.2 hne
  obtain ⟨y, ⟨χ, hχ, rfl⟩, hy⟩ := Metric.mem_closure_iff.1 hmem (|Λ ψ| / (|K| + 1))
    (by positivity)
  have h1 : |Λ ψ| ≤ |K| * dist (ofContinuousMap T ψ) (ofContinuousMap T χ) := by
    have := hΛ (ψ - χ)
    rwa [map_sub, LinearMap.mem_ker.1 hχ, sub_zero, map_sub, ← dist_eq_norm] at this
  have h2 := mul_le_mul_of_nonneg_left hy.le hK
  have h3 : |K| * (|Λ ψ| / (|K| + 1)) < |Λ ψ| := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  exact (h1.trans h2).not_gt h3

end Inner

end CircleSobolev

end TauCeti
