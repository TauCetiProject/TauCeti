/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.Derivative
public import Mathlib.Analysis.Calculus.ContDiff.Defs

import Mathlib.Analysis.Calculus.FDeriv.Partial
import TauCeti.Analysis.Fourier.Monomial

/-!
# Rotations of the circle acting on the Sobolev spaces `H^s`

Rotating the circle `AddCircle T` by `θ` reparametrizes a function `u` as `x ↦ u (x + θ)`. On
Fourier coefficients this multiplies the `n`-th coefficient by `e^{2πinθ/T}`, so it acts on every
Fourier-coefficient Sobolev space `H^s` of `TauCeti/Analysis/Sobolev/Circle/Basic.lean` as a linear
isometry, for every real order `s`. Rotations are the reparametrizations of a boundary circle by
the isometries of the circle, so this is the coordinate invariance of `H^s` under them.

The action is strongly continuous: `θ ↦ rotate θ a` is continuous for every `a ∈ H^s`. The
differentiability of an orbit map depends on the regularity of the vector: the orbit map
`θ ↦ rotate θ a` of `a ∈ H^s` is differentiable in `H^s` exactly when `a` lies in `H^(s + 1)`,
and its derivative is then the rotated derivative of `a`. In the jointly varying form, a
sufficient condition is one extra order of regularity: `(θ, a) ↦ rotate θ a` is continuously
differentiable as a map `ℝ × H^t → H^s` whenever `s + 1 ≤ t`. This is the derivative offset of
variable reparametrizations of boundary maps by rotations: differentiating the rotated map in the
rotation parameter is controlled by one more order of regularity of the map than that of the
target space.

## Main definitions

* `TauCeti.CircleSobolev.rotate θ`: for `θ : AddCircle T`, the linear isometric automorphism of
  `H^s` multiplying the `n`-th Fourier coefficient by `e^{2πinθ/T}`.

## Main statements

* `TauCeti.CircleSobolev.toContinuousMap_rotate`: for `s > 1/2`, `rotate θ a` is the continuous
  function `x ↦ a (x + θ)`.
* `TauCeti.CircleSobolev.rotate_add`, `TauCeti.CircleSobolev.rotate_symm`: the rotations form an
  action of the group `AddCircle T`.
* `TauCeti.CircleSobolev.continuous_rotate`: the action `AddCircle T × H^s → H^s` is jointly
  continuous.
* `TauCeti.CircleSobolev.hasDerivAt_rotate`: for `a ∈ H^t` and `s + 1 ≤ t`, the orbit map
  `θ ↦ rotate θ a` is differentiable as a map into `H^s`, with derivative
  `rotate θ (derivative T h a)`.
* `TauCeti.CircleSobolev.norm_rotate_sub_rotate_le`: the orbit map of `a ∈ H^t` is Lipschitz into
  `H^s`, `‖rotate φ a - rotate ψ a‖ ≤ |φ - ψ| ‖derivative T h a‖`.
* `TauCeti.CircleSobolev.differentiableAt_rotate_iff`: the orbit map of `a ∈ H^s` is
  differentiable in `H^s` at some (equivalently every) point exactly when `a ∈ H^(s + 1)`.
* `TauCeti.CircleSobolev.contDiff_rotate`: for `s + 1 ≤ t`, `(θ, a) ↦ rotate θ a` is a `C¹` map
  `ℝ × H^t → H^s`.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Graduate
  Texts in Mathematics 194, Springer, 2000, Chapter II, for the generator of a strongly continuous
  group and the differentiability of its orbit maps.
* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. **8** (2006), 611–699, for the loss of derivatives under reparametrizations
  of boundary maps in the Hardy decompositions of cut Riemann surfaces.
-/

public section

noncomputable section

open Complex Filter Topology Real

namespace TauCeti

namespace CircleSobolev

variable {s t : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {T : ℝ}

/-- The rotated coefficient sequence, as an element of `H^s`. -/
private def rotateFun (θ : AddCircle T) (a : CircleSobolev s E) : CircleSobolev s E :=
  ⟨fun n ↦ fourier n θ • a.coeff n, memℓp_of_forall_le (C := 1) fun n ↦ by
    rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul, one_mul]⟩

private theorem coeff_rotateFun (θ : AddCircle T) (a : CircleSobolev s E) (n : ℤ) :
    (rotateFun θ a).coeff n = fourier n θ • a.coeff n :=
  (rfl)

private theorem rotateFun_rotateFun (θ φ : AddCircle T) (a : CircleSobolev s E) :
    rotateFun θ (rotateFun φ a) = rotateFun (θ + φ) a :=
  CircleSobolev.ext (funext fun n ↦ by
    simp only [coeff_rotateFun, smul_smul, fourier_apply_add])

private theorem rotateFun_zero (a : CircleSobolev s E) : rotateFun (0 : AddCircle T) a = a :=
  CircleSobolev.ext (funext fun n ↦ by simp [coeff_rotateFun])

/-- The rotation by `θ : AddCircle T`, the linear isometry of `H^s` multiplying the `n`-th Fourier
coefficient by `e^{2πinθ/T}`. For `s > 1/2` it sends the continuous function `x ↦ a x` to
`x ↦ a (x + θ)` (`CircleSobolev.toContinuousMap_rotate`). -/
def rotate (θ : AddCircle T) : CircleSobolev s E ≃ₗᵢ[ℂ] CircleSobolev s E where
  toFun := rotateFun θ
  map_add' a b := CircleSobolev.ext (funext fun n ↦ smul_add _ _ _)
  map_smul' c a := CircleSobolev.ext (funext fun n ↦ smul_comm _ c _)
  invFun := rotateFun (-θ)
  left_inv a := by rw [rotateFun_rotateFun, neg_add_cancel, rotateFun_zero]
  right_inv a := by rw [rotateFun_rotateFun, add_neg_cancel, rotateFun_zero]
  norm_map' a := by
    have h₁ : ‖rotateFun θ a‖ ≤ 1 * ‖a‖ := norm_le_of_forall_le zero_le_one fun n ↦ by
      simp [coeff_rotateFun, norm_smul]
    have h₂ : ‖a‖ ≤ 1 * ‖rotateFun θ a‖ := norm_le_of_forall_le zero_le_one fun n ↦ by
      simp [coeff_rotateFun, norm_smul]
    exact le_antisymm (by simpa using h₁) (by simpa using h₂)

@[simp]
theorem coeff_rotate (θ : AddCircle T) (a : CircleSobolev s E) (n : ℤ) :
    (rotate θ a).coeff n = fourier n θ • a.coeff n :=
  (rfl)

@[simp]
theorem rotate_zero (a : CircleSobolev s E) : rotate (0 : AddCircle T) a = a :=
  rotateFun_zero a

theorem rotate_add (θ φ : AddCircle T) (a : CircleSobolev s E) :
    rotate (θ + φ) a = rotate θ (rotate φ a) :=
  (rotateFun_rotateFun θ φ a).symm

@[simp]
theorem rotate_symm (θ : AddCircle T) :
    (rotate θ : CircleSobolev s E ≃ₗᵢ[ℂ] CircleSobolev s E).symm = rotate (-θ) :=
  LinearIsometryEquiv.ext fun a ↦ (rotate θ).symm_apply_eq.2 <| by
    rw [← rotate_add, add_neg_cancel, rotate_zero]

@[simp]
theorem rotate_single (θ : AddCircle T) (n : ℤ) (x : E) :
    rotate θ (single (s := s) n x) = single n (fourier n θ • x) :=
  CircleSobolev.ext (funext fun m ↦ by
    rcases eq_or_ne m n with rfl | hm
    · simp
    · simp [hm])

@[simp]
theorem inclusion_rotate (h : t ≤ s) (θ : AddCircle T) (a : CircleSobolev s E) :
    inclusion h (rotate θ a) = rotate θ (inclusion h a) :=
  CircleSobolev.ext (funext fun n ↦ by simp)

@[simp]
theorem derivative_rotate [Fact (0 < T)] (h : s + 1 ≤ t) (θ : AddCircle T)
    (a : CircleSobolev t E) :
    derivative T h (rotate θ a) = rotate θ (derivative T h a) :=
  CircleSobolev.ext (funext fun n ↦ by
    simp only [coeff_derivative, coeff_rotate]
    exact smul_comm _ _ _)

/-- For `s > 1/2`, the rotation by `θ` reparametrizes the continuous representative:
`(rotate θ a) x = a (x + θ)`. -/
@[simp]
theorem toContinuousMap_rotate [Fact (0 < T)] [CompleteSpace E] (hs : 1 / 2 < s)
    (θ : AddCircle T) (a : CircleSobolev s E) (x : AddCircle T) :
    toContinuousMap T hs (rotate θ a) x = toContinuousMap T hs a (x + θ) := by
  simp only [toContinuousMap_apply, coeff_rotate, smul_smul, fourier_apply_add]

/-! ### Continuity of the action -/

/-- The orbit maps of the rotation action are continuous: the action is strongly continuous. -/
theorem continuous_rotate_apply (a : CircleSobolev s E) :
    Continuous fun θ : AddCircle T ↦ rotate θ a := by
  refine continuous_iff_continuousAt.2 fun θ₀ ↦ tendsto_of_tendsto_coeff
    (bound := fun n ↦ 4 * (weight s n * ‖a.coeff n‖) ^ 2)
    ((hasSum_sq_weight_mul_norm_coeff a).summable.mul_left 4)
    (fun n ↦ by simpa using ((fourier n).continuous.tendsto θ₀).smul_const (a.coeff n))
    (Eventually.of_forall fun θ n ↦ ?_)
  have hle : ‖fourier n θ • a.coeff n - fourier n θ₀ • a.coeff n‖ ≤ 2 * ‖a.coeff n‖ := by
    refine (norm_sub_le _ _).trans_eq ?_
    rw [norm_smul, norm_smul, fourier_apply, fourier_apply, Circle.norm_coe, Circle.norm_coe]
    ring
  rw [coeff_rotate, coeff_rotate]
  calc (weight s n * ‖fourier n θ • a.coeff n - fourier n θ₀ • a.coeff n‖) ^ 2
      ≤ (weight s n * (2 * ‖a.coeff n‖)) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (weight_nonneg s n) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hle (weight_nonneg s n)) 2
    _ = 4 * (weight s n * ‖a.coeff n‖) ^ 2 := by ring

/-- The rotation action `AddCircle T × H^s → H^s` is jointly continuous. -/
theorem continuous_rotate :
    Continuous fun p : AddCircle T × CircleSobolev s E ↦ rotate p.1 p.2 := by
  refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h₁ : Tendsto (fun p : AddCircle T × CircleSobolev s E ↦ ‖p.2 - p₀.2‖) (𝓝 p₀) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 (continuous_snd.tendsto p₀)
  have h₂ : Tendsto (fun p : AddCircle T × CircleSobolev s E ↦ ‖rotate p.1 p₀.2 - rotate p₀.1 p₀.2‖)
      (𝓝 p₀) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1
      (((continuous_rotate_apply p₀.2).comp continuous_fst).tendsto p₀)
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun p ↦ ?_) (by simpa using h₁.add h₂)
  calc ‖rotate p.1 p.2 - rotate p₀.1 p₀.2‖
      = ‖rotate p.1 (p.2 - p₀.2) + (rotate p.1 p₀.2 - rotate p₀.1 p₀.2)‖ := by
        rw [map_sub]
        abel_nf
    _ ≤ ‖p.2 - p₀.2‖ + ‖rotate p.1 p₀.2 - rotate p₀.1 p₀.2‖ := by
        refine (norm_add_le _ _).trans_eq ?_
        rw [LinearIsometryEquiv.norm_map]

/-! ### Differentiability of the orbit maps -/

variable [hT : Fact (0 < T)]

/-- The coefficients of the difference of two rotations are controlled by those of the
derivative. -/
private theorem norm_coeff_rotate_sub_le (h : s + 1 ≤ t) (a : CircleSobolev t E) (φ ψ : ℝ)
    (n : ℤ) :
    ‖fourier n (φ : AddCircle T) • a.coeff n - fourier n (ψ : AddCircle T) • a.coeff n‖ ≤
      |φ - ψ| * ‖(derivative T h a).coeff n‖ := by
  rw [← sub_smul, norm_smul, coeff_derivative, norm_smul]
  calc _ ≤ ‖(2 * π * I * n / T : ℂ)‖ * |φ - ψ| * ‖a.coeff n‖ :=
        mul_le_mul_of_nonneg_right (norm_fourier_coe_sub_le n φ ψ) (norm_nonneg _)
    _ = _ := by ring

/-- The orbit map of `a ∈ H^t` is Lipschitz as a map into `H^s` for `s + 1 ≤ t`:
`‖rotate φ a - rotate ψ a‖ ≤ |φ - ψ| ‖derivative T h a‖`. -/
theorem norm_rotate_sub_rotate_le (h : s + 1 ≤ t) (a : CircleSobolev t E) (φ ψ : ℝ) :
    ‖(rotate (φ : AddCircle T) (inclusion (by linarith) a) -
        rotate (ψ : AddCircle T) (inclusion (by linarith) a) : CircleSobolev s E)‖ ≤
      |φ - ψ| * ‖derivative T h a‖ :=
  norm_le_of_forall_le (abs_nonneg _) fun n ↦ by
    rw [coeff_sub, Pi.sub_apply, coeff_rotate, coeff_rotate, coeff_inclusion, mul_left_comm]
    exact mul_le_mul_of_nonneg_left (norm_coeff_rotate_sub_le h a φ ψ n) (weight_nonneg s n)

/-- For `s + 1 ≤ t`, the orbit map `θ ↦ rotate θ a` of `a ∈ H^t` is differentiable as a map into
`H^s`, with derivative `rotate θ (derivative T h a)`. -/
theorem hasDerivAt_rotate (h : s + 1 ≤ t) (a : CircleSobolev t E) (θ : ℝ) :
    HasDerivAt (fun φ : ℝ ↦ rotate (φ : AddCircle T) (inclusion (by linarith) a))
      (rotate (θ : AddCircle T) (derivative T h a) : CircleSobolev s E) θ := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  set D := derivative T h a
  -- The coefficients of the difference quotients converge to those of the rotated derivative,
  -- and they are dominated by twice the coefficients of the derivative.
  refine tendsto_of_tendsto_coeff (bound := fun n ↦ 4 * (weight s n * ‖D.coeff n‖) ^ 2)
    ((hasSum_sq_weight_mul_norm_coeff D).summable.mul_left 4) (fun n ↦ ?_) ?_
  · have hn := (hasDerivAt_iff_tendsto_slope_zero.1 (hasDerivAt_fourier T n θ)).smul_const
      (a.coeff n)
    convert hn using 1
    · funext τ
      simp only [coeff_real_smul, coeff_sub, Pi.smul_apply, Pi.sub_apply, coeff_rotate,
        coeff_inclusion, sub_smul, smul_sub, smul_assoc]
    · rw [coeff_rotate, coeff_derivative, smul_smul, mul_comm]
  · refine Eventually.of_forall fun τ n ↦ ?_
    have hτ : ‖τ⁻¹ • (fourier n ((θ + τ : ℝ) : AddCircle T) • a.coeff n -
        fourier n (θ : AddCircle T) • a.coeff n)‖ ≤ ‖D.coeff n‖ := by
      rw [norm_smul]
      calc ‖τ⁻¹‖ * ‖fourier n ((θ + τ : ℝ) : AddCircle T) • a.coeff n -
            fourier n (θ : AddCircle T) • a.coeff n‖
          ≤ ‖τ⁻¹‖ * (|θ + τ - θ| * ‖D.coeff n‖) :=
            mul_le_mul_of_nonneg_left (norm_coeff_rotate_sub_le h a _ _ n) (norm_nonneg _)
        _ = (|τ|⁻¹ * |τ|) * ‖D.coeff n‖ := by
            rw [add_sub_cancel_left, Real.norm_eq_abs, abs_inv]
            ring
        _ ≤ 1 * ‖D.coeff n‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            rcases eq_or_ne τ 0 with rfl | hτ
            · simp
            · rw [inv_mul_cancel₀ (abs_ne_zero.2 hτ)]
        _ = ‖D.coeff n‖ := one_mul _
    have hle : ‖τ⁻¹ • (fourier n ((θ + τ : ℝ) : AddCircle T) • a.coeff n -
        fourier n (θ : AddCircle T) • a.coeff n) - fourier n (θ : AddCircle T) • D.coeff n‖ ≤
        2 * ‖D.coeff n‖ := by
      have hD : ‖fourier n (θ : AddCircle T) • D.coeff n‖ = ‖D.coeff n‖ := by
        rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
      exact (norm_sub_le _ _).trans (by linarith)
    simp only [coeff_sub, coeff_real_smul, Pi.sub_apply, Pi.smul_apply, coeff_rotate,
      coeff_inclusion]
    calc _ ≤ (weight s n * (2 * ‖D.coeff n‖)) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg (weight_nonneg s n) (norm_nonneg _))
            (mul_le_mul_of_nonneg_left hle (weight_nonneg s n)) 2
      _ = 4 * (weight s n * ‖D.coeff n‖) ^ 2 := by ring

/-- The orbit map `θ ↦ rotate θ a` of `a ∈ H^s` is differentiable in `H^s` at a point exactly
when `a` lies in `H^(s + 1)`: the orbit of `a` is differentiable in `H^s` precisely when `a` has
one more order of regularity. -/
theorem differentiableAt_rotate_iff (a : CircleSobolev s E) (θ : ℝ) :
    DifferentiableAt ℝ (fun φ : ℝ ↦ rotate (φ : AddCircle T) a) θ ↔
      ∃ b : CircleSobolev (s + 1) E, inclusion (by linarith) b = a := by
  refine ⟨fun hd ↦ ?_, fun ⟨b, hb⟩ ↦ hb ▸ (hasDerivAt_rotate le_rfl b θ).differentiableAt⟩
  set D := deriv (fun φ : ℝ ↦ rotate (φ : AddCircle T) a) θ
  -- Each Fourier coefficient of the derivative `D` is the derivative of the coefficient
  -- `φ ↦ e^{2πinφ/T} a_n`, so rotating `D` back gives the formal derivative of `a`.
  have hcoeff (n : ℤ) :
      D.coeff n = (2 * π * I * n / T * fourier n (θ : AddCircle T)) • a.coeff n := by
    have h := ((coeffCLM n).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt θ hd.hasDerivAt
    have hfun : ⇑((coeffCLM n).restrictScalars ℝ) ∘ (fun φ : ℝ ↦ rotate (φ : AddCircle T) a) =
        fun φ : ℝ ↦ fourier n (φ : AddCircle T) • a.coeff n :=
      funext fun φ ↦ by simp
    rw [hfun] at h
    simpa using h.unique ((hasDerivAt_fourier T n θ).smul_const (a.coeff n))
  obtain ⟨c, hc, -⟩ := exists_inclusion_eq_and_derivative_eq T a (rotate (-(θ : AddCircle T)) D)
    fun n ↦ by
      rw [coeff_rotate, hcoeff, smul_smul, mul_comm, mul_assoc, ← fourier_apply_add,
        add_neg_cancel, fourier_eval_zero, mul_one]
  exact ⟨c, hc⟩

/-- For `s + 1 ≤ t`, the rotation action `(θ, a) ↦ rotate θ a` is a `C¹` map `ℝ × H^t → H^s`. Its
partial derivative in `θ` is `rotate θ (derivative T h a)`, and in `a` it is the rotation itself. -/
theorem contDiff_rotate (h : s + 1 ≤ t) :
    ContDiff ℝ 1 fun p : ℝ × CircleSobolev t E ↦
      (rotate (p.1 : AddCircle T) (inclusion (by linarith) p.2) : CircleSobolev s E) := by
  have hst : s ≤ t := by linarith
  let f : ℝ → CircleSobolev t E → CircleSobolev s E :=
    fun φ b ↦ rotate (φ : AddCircle T) (inclusion hst b)
  let f₁ : ℝ → CircleSobolev t E → ℝ →L[ℝ] CircleSobolev s E :=
    fun φ b ↦ (1 : ℝ →L[ℝ] ℝ).smulRight (rotate (φ : AddCircle T) (derivative T h b))
  let f₂ : ℝ → CircleSobolev t E → CircleSobolev t E →L[ℝ] CircleSobolev s E :=
    fun φ _ ↦ (((rotate (φ : AddCircle T) : CircleSobolev s E ≃ₗᵢ[ℂ] CircleSobolev s E) :
      CircleSobolev s E →L[ℂ] CircleSobolev s E).comp (inclusion hst)).restrictScalars ℝ
  have df₁ (φ : ℝ) (b : CircleSobolev t E) : HasFDerivAt (f · b) (f₁ φ b) φ :=
    (hasDerivAt_rotate h b φ).hasFDerivAt
  have df₂ (φ : ℝ) (b : CircleSobolev t E) : HasFDerivAt (f φ ·) (f₂ φ b) b :=
    (f₂ φ b).hasFDerivAt
  have cf₁ : Continuous ↿f₁ :=
    (ContinuousLinearMap.smulRightL ℝ ℝ (CircleSobolev s E) 1).continuous.comp <|
      continuous_rotate.comp <| (continuous_quotient_mk'.comp continuous_fst).prodMk
        ((derivative T h).continuous.comp continuous_snd)
  -- The partial derivative in `a` is Lipschitz in `θ` for the operator norm, by the Lipschitz
  -- bound on the orbit maps.
  have cf₂ : Continuous ↿f₂ := by
    refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun p : ℝ × CircleSobolev t E ↦ |p.1 - p₀.1| * (2 * π / T)) (𝓝 p₀)
        (𝓝 0) := by
      have := ((continuous_fst.sub continuous_const).abs.mul continuous_const).tendsto p₀
        (f := fun p : ℝ × CircleSobolev t E ↦ |p.1 - p₀.1| * (2 * π / T))
      simpa using this
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun p ↦ ?_) hlim
    refine ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (abs_nonneg _) (div_nonneg (by positivity) hT.out.le)) fun b ↦ ?_
    calc ‖rotate (p.1 : AddCircle T) (inclusion hst b) -
          rotate (p₀.1 : AddCircle T) (inclusion hst b)‖
        ≤ |p.1 - p₀.1| * ‖derivative T h b‖ := norm_rotate_sub_rotate_le h b p.1 p₀.1
      _ ≤ |p.1 - p₀.1| * (2 * π / T * ‖b‖) :=
          mul_le_mul_of_nonneg_left (norm_derivative_le T h b) (abs_nonneg _)
      _ = |p.1 - p₀.1| * (2 * π / T) * ‖b‖ := by ring
  refine contDiff_one_iff_hasFDerivAt.2 ⟨fun p ↦ (↿f₁ p).coprod (↿f₂ p),
    (ContinuousLinearMap.coprodEquivL ℝ).continuous.comp (cf₁.prodMk cf₂), fun p ↦ ?_⟩
  exact (hasStrictFDerivAt_uncurry_coprod (Eventually.of_forall fun q ↦ df₁ q.1 q.2)
    (Eventually.of_forall fun q ↦ df₂ q.1 q.2) cf₁.continuousAt cf₂.continuousAt).hasFDerivAt

end CircleSobolev

end TauCeti
