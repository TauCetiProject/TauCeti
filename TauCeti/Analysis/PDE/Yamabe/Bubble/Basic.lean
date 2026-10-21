/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# The Euclidean Yamabe bubbles

On a real inner product space `E` of dimension `n`, the *conformal coefficient* and the
*critical Sobolev exponent* are

`aₙ = 4 (n - 1) / (n - 2)`,  `pₙ = 2 n / (n - 2)`,

so that, for `n > 2`, the conformal Laplacian of a metric `g` is `aₙ Δ⁺_g + Scal_g`, with
`Δ⁺ = -Δ` the nonnegative Laplacian. The *bubble* of scale `t > 0` centred at `b` is

`U_{t,b}(x) = (2 t / (t² + ‖x - b‖²)) ^ ((n - 2) / 2)`.

The definitions are total: they make sense in every dimension, and at `n = 2` the divisions by
`n - 2` evaluate to `0` by Lean's convention. Their geometric and analytic meaning is classical
only for `n > 2`, which is the setting of the Yamabe problem.

Classically, for `n > 2`, `U_{t,b} ^ (4 / (n - 2))` times the Euclidean metric is the pullback of
the unit round metric of `Sⁿ` under `x ↦ σ⁻¹ ((2 / t) • (x - b))`, where `σ = stereographic' n v`
is Mathlib's stereographic chart from a unit vector `v`; this identification is
`TauCeti.Yamabe.inner_mfderiv_stereographic'_symm_smul_sub`. Accordingly, the bubble solves the
conformal Laplacian equation whose right-hand side carries the scalar curvature `n (n - 1)` of the
unit sphere:

`aₙ (-Δ U_{t,b}) = n (n - 1) U_{t,b} ^ (pₙ - 1)`.

As stated, this equation is proved here for every `n ≠ 2`; in dimensions `0` and `1` both sides
vanish, and it carries no geometric content.

For `n > 2`, these functions are the extremals of the sharp Euclidean Sobolev inequality and the
local models for the test functions of the Yamabe problem.

## Main declarations

* `TauCeti.Yamabe.conformalCoefficient`, `TauCeti.Yamabe.criticalExponent`: the constants `aₙ`
  and `pₙ`.
* `TauCeti.Yamabe.bubble`: the bubble `U_{t,b}`.
* `TauCeti.Yamabe.bubble_pos`, `TauCeti.Yamabe.contDiff_bubble`: positivity and smoothness.
* `TauCeti.Yamabe.bubble_zero_sub`, `TauCeti.Yamabe.bubble_zero_smul`: every bubble is a
  translate of a rescaled standard bubble `U_{1,0}`.
* `TauCeti.Yamabe.bubble_rpow_criticalExponent`,
  `TauCeti.Yamabe.bubble_rpow_criticalExponent_eq_mul_rpow_neg_one_add_norm_sq`: the critical
  power of a bubble, and its form as a rescaled translate of a Japanese bracket power.
* `TauCeti.Yamabe.bubble_sq`: the square of a bubble as a power of its profile.
* `TauCeti.Yamabe.bubble_rpow_four_div_finrank_sub_two`: the conformal factor
  `U_{t,b} ^ (4 / (n - 2))` of a bubble.
* `TauCeti.Yamabe.hasGradientAt_bubble`, `TauCeti.Yamabe.norm_fderiv_bubble_sq`: the gradient of
  a bubble and the square of the norm of its differential.
* `TauCeti.Yamabe.laplacian_div_add_norm_sub_sq_rpow`: the Laplacian of an arbitrary real power
  of the bubble profile `y ↦ 2 t / (t² + ‖y - b‖²)`.
* `TauCeti.Yamabe.laplacian_bubble`: `Δ U_{t,b} = -(n (n - 2) / 4) U_{t,b} ^ (pₙ - 1)`.
* `TauCeti.Yamabe.conformalCoefficient_mul_neg_laplacian_bubble`: the bubble equation
  `aₙ (-Δ U_{t,b}) = n (n - 1) U_{t,b} ^ (pₙ - 1)`.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §2–§3.
* T. Aubin, *Problèmes isopérimétriques et espaces de Sobolev*, J. Differential Geom. 11 (1976).
-/

public section

noncomputable section

namespace TauCeti.Yamabe

open InnerProductSpace Laplacian Module
open scoped Gradient

/-- The exponent `pₙ = 2 n / (n - 2)`; for `n > 2` it is the critical Sobolev exponent of `H¹` in
dimension `n`. At `n = 2` it is `0` by the convention for division by zero. -/
def criticalExponent (n : ℕ) : ℝ := 2 * n / (n - 2)

/-- Unfolding lemma for `TauCeti.Yamabe.criticalExponent`. -/
theorem criticalExponent_def (n : ℕ) : criticalExponent n = 2 * n / (n - 2) := (rfl)

/-- The coefficient `aₙ = 4 (n - 1) / (n - 2)`; for `n > 2` it is the coefficient of the
nonnegative Laplacian in the conformal Laplacian `aₙ Δ⁺ + Scal` in dimension `n`. At `n = 2` it is
`0` by the convention for division by zero. -/
def conformalCoefficient (n : ℕ) : ℝ := 4 * (n - 1) / (n - 2)

/-- Unfolding lemma for `TauCeti.Yamabe.conformalCoefficient`. -/
theorem conformalCoefficient_def (n : ℕ) :
    conformalCoefficient n = 4 * (n - 1) / (n - 2) := (rfl)

/-- The conformal coefficient is positive in every dimension `n > 2`. -/
theorem conformalCoefficient_pos {n : ℕ} (hn : 2 < n) : 0 < conformalCoefficient n := by
  have h : (2 : ℝ) < n := by exact_mod_cast hn
  rw [conformalCoefficient_def]
  exact div_pos (by linarith) (by linarith)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **bubble** `U_{t,b}(x) = (2 t / (t² + ‖x - b‖²)) ^ ((n - 2) / 2)` of scale `t` centred at
`b`, where `n` is the dimension of `E`. -/
def bubble (t : ℝ) (b x : E) : ℝ :=
  (2 * t / (t ^ 2 + ‖x - b‖ ^ 2)) ^ (((Module.finrank ℝ E : ℝ) - 2) / 2)

/-- Unfolding lemma for `TauCeti.Yamabe.bubble`. -/
theorem bubble_apply (t : ℝ) (b x : E) :
    bubble t b x = (2 * t / (t ^ 2 + ‖x - b‖ ^ 2)) ^ (((Module.finrank ℝ E : ℝ) - 2) / 2) :=
  (rfl)

/-- A bubble of positive scale is positive. -/
theorem bubble_pos {t : ℝ} (ht : 0 < t) (b x : E) : 0 < bubble t b x := by
  rw [bubble_apply]
  positivity

/-- A bubble of nonzero scale is smooth. -/
theorem contDiff_bubble {t : ℝ} (ht : t ≠ 0) (b : E) {m : WithTop ℕ∞} :
    ContDiff ℝ m (bubble t b) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hq : ∀ y : E, t ^ 2 + ‖y - b‖ ^ 2 ≠ 0 := fun y ↦ by positivity
  have hcd : ContDiffAt ℝ m (fun y : E ↦ 2 * t / (t ^ 2 + ‖y - b‖ ^ 2)) x :=
    contDiffAt_const.div
      (contDiffAt_const.add ((contDiff_id.sub contDiff_const).norm_sq ℝ).contDiffAt) (hq x)
  exact hcd.rpow_const_of_ne (div_ne_zero (mul_ne_zero two_ne_zero ht) (hq x))

/-- The bubble centred at `b` is the translate by `b` of the bubble centred at the origin. -/
theorem bubble_zero_sub (t : ℝ) (b x : E) : bubble t 0 (x - b) = bubble t b x := by
  rw [bubble_apply, bubble_apply, sub_zero]

/-- The bubble of scale `t` centred at the origin is the rescaled standard bubble:
`U_{t,0}(t x) = t ^ (-(n - 2) / 2) U_{1,0}(x)`. -/
theorem bubble_zero_smul {t : ℝ} (ht : 0 < t) (x : E) :
    bubble t 0 (t • x) = t ^ (-(((Module.finrank ℝ E : ℝ) - 2) / 2)) * bubble 1 0 x := by
  have hbase : 2 * t / (t ^ 2 + ‖t • x - 0‖ ^ 2) = t⁻¹ * (2 * 1 / (1 ^ 2 + ‖x - 0‖ ^ 2)) := by
    rw [sub_zero, sub_zero, norm_smul, Real.norm_of_nonneg ht.le]
    field_simp
  rw [bubble_apply, bubble_apply, hbase, Real.mul_rpow (inv_nonneg.mpr ht.le) (by positivity),
    Real.inv_rpow ht.le, Real.rpow_neg ht.le]

/-- In dimension `n ≠ 2`, the critical power of a bubble is
`U_{t,b} ^ pₙ = (2 t / (t² + ‖x - b‖²)) ^ n`. -/
theorem bubble_rpow_criticalExponent (hn : finrank ℝ E ≠ 2) {t : ℝ} (ht : 0 < t) (b x : E) :
    bubble t b x ^ criticalExponent (finrank ℝ E) =
      (2 * t / (t ^ 2 + ‖x - b‖ ^ 2)) ^ finrank ℝ E := by
  have hn' : (finrank ℝ E : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hn)
  rw [bubble_apply, criticalExponent_def, ← Real.rpow_mul (by positivity),
    ← Real.rpow_natCast _ (finrank ℝ E)]
  congr 1
  field_simp

/-- In dimension `n ≥ 2`, the square of a bubble is a power of its profile:
`U_{t,b} ^ 2 = (2 t / (t² + ‖x - b‖²)) ^ (n - 2)`. -/
theorem bubble_sq (hn : 2 ≤ finrank ℝ E) {t : ℝ} (ht : 0 ≤ t) (b x : E) :
    bubble t b x ^ 2 = (2 * t / (t ^ 2 + ‖x - b‖ ^ 2)) ^ (finrank ℝ E - 2) := by
  rw [bubble_apply, ← Real.rpow_mul_natCast (by positivity), ← Real.rpow_natCast _ (_ - 2)]
  congr 1
  push_cast [Nat.cast_sub hn]
  ring

/-- In dimension `n ≠ 2`, the critical power of a bubble is a rescaled translate of a power of the
Japanese bracket: `U_{t,b}(x) ^ pₙ = (2 / t) ^ n (1 + ‖t⁻¹ (x - b)‖²) ^ (-n)`. -/
theorem bubble_rpow_criticalExponent_eq_mul_rpow_neg_one_add_norm_sq (hn : finrank ℝ E ≠ 2)
    {t : ℝ} (ht : 0 < t) (b x : E) :
    bubble t b x ^ criticalExponent (finrank ℝ E) =
      (2 / t) ^ finrank ℝ E * (1 + ‖t⁻¹ • (x - b)‖ ^ 2) ^ (-(finrank ℝ E : ℝ)) := by
  rw [bubble_rpow_criticalExponent hn ht, Real.rpow_neg (by positivity), Real.rpow_natCast,
    ← inv_pow, ← mul_pow, norm_smul, norm_inv, Real.norm_of_nonneg ht.le]
  congr 1
  field_simp

/-- In dimension `n ≠ 2`, the Yamabe conformal factor of a bubble is
`U_{t,b} ^ (4 / (n - 2)) = (2 t / (t² + ‖x - b‖²)) ^ 2`. -/
theorem bubble_rpow_four_div_finrank_sub_two (hn : finrank ℝ E ≠ 2) {t : ℝ} (ht : 0 < t)
    (b x : E) :
    bubble t b x ^ (4 / ((finrank ℝ E : ℝ) - 2)) = (2 * t / (t ^ 2 + ‖x - b‖ ^ 2)) ^ 2 := by
  have hn' : (finrank ℝ E : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hn)
  have hexp : ((finrank ℝ E : ℝ) - 2) / 2 * (4 / ((finrank ℝ E : ℝ) - 2)) = (2 : ℕ) := by
    field_simp
    norm_num
  rw [bubble_apply, ← Real.rpow_mul (by positivity), hexp, Real.rpow_natCast]

section Gradient

variable [CompleteSpace E]

/-- **The gradient of a bubble**:
`∇U_{t,b}(x) = -((n - 2) / (t² + ‖x - b‖²)) U_{t,b}(x) (x - b)`, where `n` is the dimension of
`E`. -/
theorem hasGradientAt_bubble {t : ℝ} (ht : 0 < t) (b x : E) :
    HasGradientAt (bubble t b)
      (-(((finrank ℝ E : ℝ) - 2) / (t ^ 2 + ‖x - b‖ ^ 2) * bubble t b x) • (x - b)) x := by
  set k : ℝ := ((finrank ℝ E : ℝ) - 2) / 2
  have hQ : 0 < t ^ 2 + ‖x - b‖ ^ 2 := by positivity
  -- Write the bubble as `F ∘ q` with `q y = t² + ‖y - b‖²` and `F s = (2 t s⁻¹) ^ k`.
  have hq : HasFDerivAt (fun y : E ↦ t ^ 2 + ‖y - b‖ ^ 2) (toDual ℝ E ((2 : ℝ) • (x - b))) x := by
    refine (((hasStrictFDerivAt_norm_sq (x - b)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).sub_const b)).const_add (t ^ 2)).congr_fderiv ?_
    ext v
    simp
  have hF : HasDerivAt (fun s : ℝ ↦ (2 * t * s⁻¹) ^ k)
      (2 * t * -((t ^ 2 + ‖x - b‖ ^ 2) ^ 2)⁻¹ * k * (2 * t * (t ^ 2 + ‖x - b‖ ^ 2)⁻¹) ^ (k - 1))
      (t ^ 2 + ‖x - b‖ ^ 2) :=
    ((hasDerivAt_inv hQ.ne').const_mul (2 * t)).rpow_const (Or.inl (by positivity))
  have hU : bubble t b = (fun s : ℝ ↦ (2 * t * s⁻¹) ^ k) ∘ fun y : E ↦ t ^ 2 + ‖y - b‖ ^ 2 := by
    funext y
    simp [bubble_apply, div_eq_mul_inv, k]
  have h := hF.comp_hasFDerivAt x hq
  rw [← hU, ← map_smul, smul_smul] at h
  rw [hasGradientAt_iff_hasFDerivAt]
  refine h.congr_fderiv ?_
  congr 2
  rw [bubble_apply, div_eq_mul_inv,
    Real.rpow_sub_one (by positivity : 2 * t * (t ^ 2 + ‖x - b‖ ^ 2)⁻¹ ≠ 0)]
  simp only [k]
  field_simp

/-- The gradient of a bubble, as a value of `gradient`. -/
theorem gradient_bubble {t : ℝ} (ht : 0 < t) (b x : E) :
    ∇ (bubble t b) x =
      -(((finrank ℝ E : ℝ) - 2) / (t ^ 2 + ‖x - b‖ ^ 2) * bubble t b x) • (x - b) :=
  (hasGradientAt_bubble ht b x).gradient

/-- The squared norm of the differential of a bubble is the radial function
`((n - 2) / (2 t)) ² ‖x - b‖² (2 t / (t² + ‖x - b‖²)) ^ n`. -/
theorem norm_fderiv_bubble_sq {t : ℝ} (ht : 0 < t) (b x : E) :
    ‖fderiv ℝ (bubble t b) x‖ ^ 2 = (((finrank ℝ E : ℝ) - 2) / (2 * t)) ^ 2 * ‖x - b‖ ^ 2 *
      (2 * t / (t ^ 2 + ‖x - b‖ ^ 2)) ^ finrank ℝ E := by
  have hQ : 0 < t ^ 2 + ‖x - b‖ ^ 2 := by positivity
  have hU2 : bubble t b x ^ 2 =
      (2 * t / (t ^ 2 + ‖x - b‖ ^ 2)) ^ finrank ℝ E / (2 * t / (t ^ 2 + ‖x - b‖ ^ 2)) ^ 2 := by
    have ha : 0 < 2 * t / (t ^ 2 + ‖x - b‖ ^ 2) := by positivity
    rw [bubble_apply, ← Real.rpow_mul_natCast ha.le, show ((finrank ℝ E : ℝ) - 2) / 2 * (2 : ℕ) =
      (finrank ℝ E : ℝ) - 2 by push_cast; ring, Real.rpow_sub ha, Real.rpow_natCast, Real.rpow_two]
  rw [(hasGradientAt_bubble ht b x).hasFDerivAt.fderiv, LinearIsometryEquiv.norm_map, norm_smul,
    mul_pow, norm_neg, Real.norm_eq_abs, sq_abs, mul_pow, hU2]
  field_simp

end Gradient

variable [FiniteDimensional ℝ E]

/-- The Laplacian of a real power of the bubble profile `y ↦ 2 t / (t² + ‖y - b‖²)`, by the chain
rule through the squared distance to `b`. -/
theorem laplacian_div_add_norm_sub_sq_rpow {t : ℝ} (ht : 0 < t) (k : ℝ) (b x : E) :
    Δ (fun y : E ↦ ((2 * t / (t ^ 2 + ‖y - b‖ ^ 2)) ^ k : ℝ)) x =
      (2 * t) ^ k * (t ^ 2 + ‖x - b‖ ^ 2) ^ (-k - 2) *
        (4 * k * (k + 1) * ‖x - b‖ ^ 2 -
          2 * (Module.finrank ℝ E : ℝ) * k * (t ^ 2 + ‖x - b‖ ^ 2)) := by
  have hqpos : ∀ y : E, 0 < t ^ 2 + ‖y - b‖ ^ 2 := fun y ↦ by positivity
  -- Write the power as `F ∘ q` with `q y = t² + ‖y - b‖²` and `F s = (2 t) ^ k s ^ (-k)`.
  have hUF : (fun y : E ↦ ((2 * t / (t ^ 2 + ‖y - b‖ ^ 2)) ^ k : ℝ)) =
      (fun s ↦ (2 * t) ^ k * s ^ (-k)) ∘ fun y ↦ t ^ 2 + ‖y - b‖ ^ 2 := by
    funext y
    rw [Function.comp_apply, Real.div_rpow (by positivity) (hqpos y).le,
      Real.rpow_neg (hqpos y).le, div_eq_mul_inv]
  have hFd : deriv (fun s : ℝ ↦ (2 * t) ^ k * s ^ (-k)) =
      fun s ↦ (2 * t) ^ k * (-k * s ^ (-k - 1)) := by
    funext s
    simp [Real.deriv_rpow_const]
  have hFdd : deriv (fun s : ℝ ↦ (2 * t) ^ k * (-k * s ^ (-k - 1))) =
      fun s ↦ (2 * t) ^ k * (-k * ((-k - 1) * s ^ (-k - 1 - 1))) := by
    funext s
    simp [Real.deriv_rpow_const]
  have hFc : ContDiffAt ℝ 2 (fun s : ℝ ↦ (2 * t) ^ k * s ^ (-k)) (t ^ 2 + ‖x - b‖ ^ 2) :=
    contDiffAt_const.mul (Real.contDiffAt_rpow_const_of_ne (hqpos x).ne')
  have hqc : ContDiffAt ℝ 2 (fun y : E ↦ t ^ 2 + ‖y - b‖ ^ 2) x :=
    contDiffAt_const.add ((contDiff_id.sub contDiff_const).norm_sq ℝ).contDiffAt
  -- The gradient of `q` is `2 (x - b)`, and its Laplacian is `2 n`.
  have hgrad : ‖∇ (fun y : E ↦ t ^ 2 + ‖y - b‖ ^ 2) x‖ ^ 2 = 4 * ‖x - b‖ ^ 2 := by
    have h : HasGradientAt (fun y : E ↦ t ^ 2 + ‖y - b‖ ^ 2) ((2 : ℝ) • (x - b)) x := by
      rw [hasGradientAt_iff_hasFDerivAt]
      refine (((hasStrictFDerivAt_norm_sq (x - b)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).sub_const b)).const_add (t ^ 2)).congr_fderiv ?_
      ext v
      simp [toDual_apply_apply]
    rw [h.gradient, norm_smul, mul_pow, Real.norm_two]
    norm_num
  have hlap : Δ (fun y : E ↦ t ^ 2 + ‖y - b‖ ^ 2) x = 2 * (Module.finrank ℝ E : ℝ) := by
    have h := congrFun (laplacian_comp_add_right (fun z : E ↦ t ^ 2 + ‖z‖ ^ 2) (-b)) x
    simp only [← sub_eq_add_neg] at h
    rw [h, (contDiff_const.add contDiff_id :
      ContDiff ℝ 2 fun s : ℝ ↦ t ^ 2 + s).laplacian_comp_norm_sq]
    simp
  rw [hUF, ContDiffAt.laplacian_comp (q := fun y : E ↦ t ^ 2 + ‖y - b‖ ^ 2) hFc hqc, hFd, hFdd,
    hgrad, hlap]
  have h1 : (t ^ 2 + ‖x - b‖ ^ 2) ^ (-k - 1) =
      (t ^ 2 + ‖x - b‖ ^ 2) * (t ^ 2 + ‖x - b‖ ^ 2) ^ (-k - 2) := by
    rw [show (-k - 1 : ℝ) = 1 + (-k - 2) by ring, Real.rpow_add (hqpos x), Real.rpow_one]
  beta_reduce
  rw [show (-k - 1 - 1 : ℝ) = -k - 2 by ring, h1]
  ring

/-- **The Laplacian of a bubble**: `Δ U_{t,b} = -(n (n - 2) / 4) U_{t,b} ^ (pₙ - 1)`, where
`n` is the dimension of `E` and `pₙ = 2 n / (n - 2)` is the exponent `criticalExponent n`. The
identity holds in every dimension; at `n = 2` both sides vanish. -/
theorem laplacian_bubble {t : ℝ} (ht : 0 < t) (b x : E) :
    Δ (bubble t b) x = -((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E - 2) / 4) *
      bubble t b x ^ (criticalExponent (Module.finrank ℝ E) - 1) := by
  have hU : bubble t b = fun y : E ↦
      ((2 * t / (t ^ 2 + ‖y - b‖ ^ 2)) ^ (((Module.finrank ℝ E : ℝ) - 2) / 2) : ℝ) :=
    funext (bubble_apply t b)
  rw [hU, laplacian_div_add_norm_sub_sq_rpow ht, criticalExponent_def]
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  have hQ : 0 < t ^ 2 + ‖x - b‖ ^ 2 := by positivity
  rcases eq_or_ne n 2 with hn | hn
  · simp [hn]
  -- Away from dimension two, `U ^ (pₙ - 1) = (2 t / (t² + ‖x - b‖²)) ^ ((n - 2) / 2 + 2)`.
  have hexp : (n - 2) / 2 * (2 * n / (n - 2) - 1) = (n - 2) / 2 + 2 := by
    field_simp [sub_ne_zero.mpr hn]
    ring
  rw [← Real.rpow_mul (by positivity), hexp, Real.div_rpow (by positivity) hQ.le,
    Real.rpow_add (by positivity), Real.rpow_two,
    show -((n - 2) / 2) - 2 = -((n - 2) / 2 + 2) by ring, Real.rpow_neg hQ.le]
  ring

/-- **The bubble equation**: in dimension `n ≠ 2`, every bubble of positive scale solves the
Yamabe equation of the unit round sphere, `aₙ (-Δ U_{t,b}) = n (n - 1) U_{t,b} ^ (pₙ - 1)`. -/
theorem conformalCoefficient_mul_neg_laplacian_bubble (hn : Module.finrank ℝ E ≠ 2) {t : ℝ}
    (ht : 0 < t) (b x : E) :
    conformalCoefficient (Module.finrank ℝ E) * -Δ (bubble t b) x =
      (Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E - 1) *
        bubble t b x ^ (criticalExponent (Module.finrank ℝ E) - 1) := by
  have hn' : (Module.finrank ℝ E : ℝ) - 2 ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast hn)
  rw [laplacian_bubble ht, conformalCoefficient_def]
  field_simp

end TauCeti.Yamabe
