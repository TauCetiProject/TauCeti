/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import Mathlib.Analysis.Complex.UnitDisc.Basic
public import TauCeti.Algebra.Field.LinearFractional
public import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
# The disc coordinate centred at a point of the upper half-plane

For `z ∈ ℍ`, the Cayley transform `τ ↦ (τ - z) / (τ - conj z)` is a bijection from the upper
half-plane onto the open unit disc sending `z` to `0`, with inverse
`w ↦ (z - conj z * w) / (1 - w)`; its modulus is `tanh (d / 2)` for the
hyperbolic distance `d` to `z`. In this coordinate every matrix of positive determinant fixing
`z` is a rotation of the disc about `0`: if `g • z = z`, then
`discCoordinate z (g • τ) = conj (denom g z) / denom g z * discCoordinate z τ`.

This is the local linearizing coordinate at a point with nontrivial stabilizer: the multiplier
`conj (denom g z) / denom g z` is a complex number of modulus one, and it records the
derivative of `τ ↦ g • τ` at its fixed point `z`.

## Main declarations

* `UpperHalfPlane.discCoordinate`: the Cayley transform centred at `z`.
* `UpperHalfPlane.discCoordinate_eq_zero_iff` and `UpperHalfPlane.discCoordinate_injective`.
* `UpperHalfPlane.norm_discCoordinate`: the modulus of the disc coordinate is
  `tanh (dist τ z / 2)`, so the coordinate takes values in the unit disc.
* `UpperHalfPlane.discCoordinateEquiv`: the disc coordinate as an equivalence `ℍ ≃ 𝔻`, with
  explicit inverse, and `UpperHalfPlane.range_discCoordinate`: its range is the open unit disc.
* `UpperHalfPlane.discCoordinateBallHomeomorph`: the disc coordinate maps the hyperbolic disc of
  radius `r` about `z` homeomorphically onto the Euclidean disc of radius `tanh (r / 2)`.
* `UpperHalfPlane.discCoordinate_smul_of_smul_eq_self`: a matrix of positive determinant
  fixing `z` acts in the disc coordinate by multiplication by `conj (denom g z) / denom g z`,
  with the `SL(2, ℝ)` specialization
  `UpperHalfPlane.discCoordinate_specialLinearGroup_smul_of_smul_eq_self`.

## References

* S. Katok, *Fuchsian Groups*, University of Chicago Press, 1992, §§1.1 and 2.1.
* H. Farkas and I. Kra, *Riemann Surfaces*, 2nd ed., Springer, 1992, Chapter I §4.
-/

public section

noncomputable section

open scoped MatrixGroups ComplexConjugate Complex.UnitDisc

namespace UpperHalfPlane

/-- The disc coordinate centred at `z`: the Cayley transform `τ ↦ (τ - z) / (τ - conj z)`, which
maps the upper half-plane injectively into the unit disc and sends `z` to `0`. -/
def discCoordinate (z τ : ℍ) : ℂ :=
  ((τ : ℂ) - z) / ((τ : ℂ) - conj (z : ℂ))

theorem discCoordinate_def (z τ : ℍ) :
    discCoordinate z τ = ((τ : ℂ) - z) / ((τ : ℂ) - conj (z : ℂ)) := (rfl)

/-- The denominator of the disc coordinate does not vanish: `conj z` lies in the lower
half-plane. -/
theorem coe_sub_conj_ne_zero (z τ : ℍ) : (τ : ℂ) - conj (z : ℂ) ≠ 0 := by
  intro h
  have h' := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.conj_im, sub_neg_eq_add, Complex.zero_im, coe_im] at h'
  linarith [τ.im_pos, z.im_pos]

/-- The disc coordinate centred at `z` vanishes exactly at its centre `z`. -/
@[simp]
theorem discCoordinate_eq_zero_iff {z τ : ℍ} : discCoordinate z τ = 0 ↔ τ = z := by
  rw [discCoordinate_def, div_eq_zero_iff, or_iff_left (coe_sub_conj_ne_zero z τ), sub_eq_zero,
    UpperHalfPlane.ext_iff]

@[simp]
theorem discCoordinate_self (z : ℍ) : discCoordinate z z = 0 :=
  discCoordinate_eq_zero_iff.mpr rfl

/-- The disc coordinate centred at any point is injective on the upper half-plane. -/
theorem discCoordinate_injective (z : ℍ) : Function.Injective (discCoordinate z) := by
  intro τ σ h
  rw [discCoordinate_def, discCoordinate_def,
    div_eq_div_iff (coe_sub_conj_ne_zero z τ) (coe_sub_conj_ne_zero z σ)] at h
  have hz : (z : ℂ) - conj (z : ℂ) ≠ 0 := by
    simpa using coe_sub_conj_ne_zero z z
  have h' : ((τ : ℂ) - σ) * ((z : ℂ) - conj (z : ℂ)) = 0 := by
    linear_combination h
  exact UpperHalfPlane.ext (sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right hz))

/-- The modulus of the disc coordinate centred at `z` is `tanh (d / 2)`, where `d` is the
hyperbolic distance to `z`. -/
theorem norm_discCoordinate (z τ : ℍ) : ‖discCoordinate z τ‖ = Real.tanh (dist τ z / 2) := by
  rw [tanh_half_dist, discCoordinate_def, norm_div, Complex.dist_eq, Complex.dist_eq]

/-- The disc coordinate takes values in the open unit disc. -/
theorem norm_discCoordinate_lt_one (z τ : ℍ) : ‖discCoordinate z τ‖ < 1 := by
  rw [norm_discCoordinate]
  exact Real.tanh_lt_one _

/-- The imaginary part of the inverse disc coordinate `(z - conj z * w) / (1 - w)` is
`im z * (1 - |w| ^ 2) / |1 - w| ^ 2`. -/
private theorem im_discCoordinateInv (z : ℍ) (w : 𝔻) :
    (((z : ℂ) - conj (z : ℂ) * w) / (1 - w)).im =
      z.im * (1 - Complex.normSq (w : ℂ)) / Complex.normSq (1 - w) := by
  rw [Complex.div_im]
  simp only [Complex.sub_im, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_im,
    Complex.sub_re, Complex.mul_re, Complex.one_re, coe_im, coe_re, Complex.normSq_apply]
  ring

private theorem im_discCoordinateInv_pos (z : ℍ) (w : 𝔻) :
    0 < (((z : ℂ) - conj (z : ℂ) * w) / (1 - w)).im := by
  rw [im_discCoordinateInv]
  exact div_pos (mul_pos z.im_pos (sub_pos.mpr w.normSq_lt_one))
    (Complex.normSq_pos.mpr (sub_ne_zero.mpr w.coe_ne_one.symm))

/-- The disc coordinate centred at `z` as an equivalence between the upper half-plane and the
open unit disc `𝔻`, with inverse `w ↦ (z - conj z * w) / (1 - w)`. -/
def discCoordinateEquiv (z : ℍ) : ℍ ≃ 𝔻 where
  toFun τ := .mk (discCoordinate z τ) (norm_discCoordinate_lt_one z τ)
  invFun w := ⟨((z : ℂ) - conj (z : ℂ) * w) / (1 - w), im_discCoordinateInv_pos z w⟩
  left_inv τ := by
    have hτ := coe_sub_conj_ne_zero z τ
    have hz := coe_sub_conj_ne_zero z z
    ext
    simp only [Complex.UnitDisc.coe_mk, discCoordinate_def]
    rw [div_eq_iff]
    · field_simp
      ring
    · rw [one_sub_div hτ]
      exact div_ne_zero (by simpa using hz) hτ
  right_inv w := by
    have h1 : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr w.coe_ne_one.symm
    have hz := coe_sub_conj_ne_zero z z
    ext
    simp only [Complex.UnitDisc.coe_mk, discCoordinate_def]
    rw [div_sub' h1, div_sub' h1, div_div_div_cancel_right₀ h1, div_eq_iff]
    · ring
    · convert hz using 1
      ring

@[simp]
theorem coe_discCoordinateEquiv_apply (z τ : ℍ) :
    (discCoordinateEquiv z τ : ℂ) = discCoordinate z τ :=
  (rfl)

@[simp]
theorem coe_discCoordinateEquiv_symm_apply (z : ℍ) (w : 𝔻) :
    ((discCoordinateEquiv z).symm w : ℂ) = ((z : ℂ) - conj (z : ℂ) * w) / (1 - w) :=
  (rfl)

/-- The range of the disc coordinate centred at any point is the open unit disc. -/
theorem range_discCoordinate (z : ℍ) : Set.range (discCoordinate z) = Metric.ball 0 1 := by
  ext w
  refine ⟨?_, fun hw ↦ ?_⟩
  · rintro ⟨τ, rfl⟩
    exact mem_ball_zero_iff.mpr (norm_discCoordinate_lt_one z τ)
  · lift w to 𝔻 using mem_ball_zero_iff.mp hw
    exact ⟨(discCoordinateEquiv z).symm w,
      congrArg ((↑) : 𝔻 → ℂ) ((discCoordinateEquiv z).apply_symm_apply w)⟩

/-- The disc coordinate centred at `z` is continuous. -/
@[fun_prop]
theorem continuous_discCoordinate (z : ℍ) : Continuous (discCoordinate z) := by
  simp only [funext (discCoordinate_def z)]
  exact (by fun_prop : Continuous fun τ : ℍ ↦ (τ : ℂ) - z).div₀ (by fun_prop)
    (coe_sub_conj_ne_zero z)

/-- The inverse `w ↦ (z - conj z * w) / (1 - w)` of the disc coordinate centred at `z` is
continuous on the open unit disc. -/
theorem continuous_discCoordinateEquiv_symm (z : ℍ) :
    Continuous (discCoordinateEquiv z).symm := by
  rw [isEmbedding_coe.continuous_iff]
  simp only [Function.comp_def, coe_discCoordinateEquiv_symm_apply]
  exact (by fun_prop : Continuous fun w : 𝔻 ↦ (z : ℂ) - conj (z : ℂ) * w).div₀
    (by fun_prop) fun w ↦ sub_ne_zero.mpr w.coe_ne_one.symm

/-- A point lies in the hyperbolic disc of radius `r` about `z` exactly when its disc coordinate
centred at `z` has modulus less than `tanh (r / 2)`. -/
theorem norm_discCoordinate_lt_tanh_iff {z τ : ℍ} {r : ℝ} :
    ‖discCoordinate z τ‖ < Real.tanh (r / 2) ↔ dist τ z < r := by
  have hmem (x : ℝ) : Real.tanh x ∈ Set.Ioo (-1) 1 := ⟨Real.neg_one_lt_tanh x, Real.tanh_lt_one x⟩
  rw [norm_discCoordinate, ← Real.artanh_lt_artanh_iff (hmem _) (hmem _), Real.artanh_tanh,
    Real.artanh_tanh, div_lt_div_iff_of_pos_right two_pos]

/-- The disc coordinate centred at `z` maps the hyperbolic disc of radius `r` about `z`
homeomorphically onto the Euclidean disc of radius `tanh (r / 2)` about `0`. -/
def discCoordinateBallHomeomorph (z : ℍ) (r : ℝ) :
    Metric.ball z r ≃ₜ Metric.ball (0 : ℂ) (Real.tanh (r / 2)) where
  toFun τ := ⟨discCoordinate z τ,
    mem_ball_zero_iff.mpr (norm_discCoordinate_lt_tanh_iff.mpr τ.2)⟩
  invFun w := ⟨(discCoordinateEquiv z).symm (.mk w
      ((mem_ball_zero_iff.mp w.2).trans (Real.tanh_lt_one _))), by
    rw [Metric.mem_ball, ← norm_discCoordinate_lt_tanh_iff, ← coe_discCoordinateEquiv_apply,
      Equiv.apply_symm_apply, Complex.UnitDisc.coe_mk]
    exact mem_ball_zero_iff.mp w.2⟩
  left_inv τ := Subtype.ext ((discCoordinateEquiv z).symm_apply_apply τ)
  right_inv w := Subtype.ext <| by
    simp only [← coe_discCoordinateEquiv_apply, Equiv.apply_symm_apply,
      Complex.UnitDisc.coe_mk]
  continuous_toFun := by fun_prop
  continuous_invFun := by
    refine ((continuous_discCoordinateEquiv_symm z).comp ?_).subtype_mk _
    simp only [Complex.UnitDisc.isEmbedding_coe.continuous_iff, Function.comp_def,
      Complex.UnitDisc.coe_mk]
    fun_prop

@[simp]
theorem coe_discCoordinateBallHomeomorph_apply (z : ℍ) (r : ℝ) (τ : Metric.ball z r) :
    (discCoordinateBallHomeomorph z r τ : ℂ) = discCoordinate z τ :=
  (rfl)

/-- The inverse of `discCoordinateBallHomeomorph` is the inverse disc-coordinate formula. -/
@[simp]
theorem coe_discCoordinateBallHomeomorph_symm_apply (z : ℍ) (r : ℝ)
    (w : Metric.ball (0 : ℂ) (Real.tanh (r / 2))) :
    ((discCoordinateBallHomeomorph z r).symm w : ℂ) =
      ((z : ℂ) - conj (z : ℂ) * w) / (1 - w) :=
  (rfl)

/-- **A matrix of positive determinant fixing `z` is a rotation in the disc coordinate centred
at `z`**, by the unimodular multiplier `conj (denom g z) / denom g z`.

Positive determinant is what makes the Möbius transformation holomorphic; the determinant
itself cancels, since it scales the displacements from `z` and from `conj z` alike. -/
theorem discCoordinate_smul_of_smul_eq_self {g : GL (Fin 2) ℝ} (hdet : 0 < g.det.val) {z : ℍ}
    (hg : g • z = z) (τ : ℍ) :
    discCoordinate z (g • τ) = conj (denom g z) / denom g z * discCoordinate z τ := by
  have hz := congrArg ((↑) : ℍ → ℂ) hg
  have hj := denom_ne_zero g z
  have hjτ := denom_ne_zero g τ
  have hτ := coe_sub_conj_ne_zero z τ
  have hD : (g 0 0 : ℂ) * g 1 1 - g 0 1 * g 1 0 ≠ 0 := by
    have h : (g : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]
      exact hdet.ne'
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  rw [coe_smul_of_det_pos hdet] at hz
  simp only [num, denom] at hz hj hjτ
  rw [div_eq_iff hj] at hz
  have hjc : (g 1 0 : ℂ) * conj (z : ℂ) + g 1 1 ≠ 0 := by
    simpa using (map_ne_zero (starRingEnd ℂ)).mpr hj
  have hzc : (g 0 0 : ℂ) * conj (z : ℂ) + g 0 1 =
      conj (z : ℂ) * ((g 1 0 : ℂ) * conj (z : ℂ) + g 1 1) := by
    simpa using congrArg conj hz
  simp only [discCoordinate_def, coe_smul_of_det_pos hdet, num, denom]
  rw [TauCeti.moebius_sub_of_fixed hz hj hjτ, TauCeti.moebius_sub_of_fixed hzc hjc hjτ]
  simp only [map_add, map_mul, Complex.conj_ofReal]
  rw [div_div_div_eq, div_mul_div_comm,
    div_eq_div_iff (mul_ne_zero (mul_ne_zero hjτ hj) (mul_ne_zero hD hτ)) (mul_ne_zero hj hτ)]
  ring

/-- **An element of `SL(2, ℝ)` fixing `z` is a rotation in the disc coordinate centred at `z`**,
by the unimodular multiplier `conj (denom g z) / denom g z`: the determinant-one case of
`UpperHalfPlane.discCoordinate_smul_of_smul_eq_self`. -/
theorem discCoordinate_specialLinearGroup_smul_of_smul_eq_self {g : SL(2, ℝ)} {z : ℍ}
    (hg : g • z = z) (τ : ℍ) :
    discCoordinate z (g • τ) = conj (denom g z) / denom g z * discCoordinate z τ := by
  rw [← Matrix.SpecialLinearGroup.toGL_smul]
  exact discCoordinate_smul_of_smul_eq_self (by simp)
    (by rwa [Matrix.SpecialLinearGroup.toGL_smul]) τ

end UpperHalfPlane
