/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-!
# The disc coordinate centred at a point of the upper half-plane

For `z ∈ ℍ`, the Cayley transform `τ ↦ (τ - z) / (τ - conj z)` is an injective map from the upper
half-plane into the open unit disc sending `z` to `0`; its modulus is `tanh (d / 2)` for the
hyperbolic distance `d` to `z`. In this coordinate every element of
`SL(2, ℝ)` fixing `z` is a rotation of the disc about `0`: if `g • z = z`, then
`discCoordinate z (g • τ) = conj (denom g z) / denom g z * discCoordinate z τ`.

This is the local linearizing coordinate at a point with nontrivial stabilizer: the multiplier
`conj (denom g z) / denom g z` is a complex number of modulus one, and it records the
derivative of `τ ↦ g • τ` at its fixed point `z`.

## Main declarations

* `UpperHalfPlane.discCoordinate`: the Cayley transform centred at `z`.
* `UpperHalfPlane.discCoordinate_eq_zero_iff` and `UpperHalfPlane.discCoordinate_injective`.
* `UpperHalfPlane.norm_discCoordinate`: the modulus of the disc coordinate is
  `tanh (dist τ z / 2)`, so the coordinate takes values in the unit disc.
* `UpperHalfPlane.discCoordinate_smul_of_smul_eq_self`: an element of `SL(2, ℝ)` fixing `z`
  acts in the disc coordinate by multiplication by `conj (denom g z) / denom g z`.

## References

* S. Katok, *Fuchsian Groups*, University of Chicago Press, 1992, §§1.1 and 2.1.
* H. Farkas and I. Kra, *Riemann Surfaces*, 2nd ed., Springer, 1992, Chapter I §4.
-/

public section

noncomputable section

open scoped MatrixGroups ComplexConjugate

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

/-- The Möbius difference formula at a fixed point: if `(a w + b) / (c w + d) = w` and
`a d - b c = 1`, then `(a t + b) / (c t + d) - w = (t - w) / ((c t + d) (c w + d))`. -/
private theorem moebius_sub_of_fixed {a b c d w t : ℂ} (hdet : a * d - b * c = 1)
    (hw : a * w + b = w * (c * w + d)) (hj : c * w + d ≠ 0) (hjt : c * t + d ≠ 0) :
    (a * t + b) / (c * t + d) - w = (t - w) / ((c * t + d) * (c * w + d)) := by
  rw [div_sub' hjt, div_eq_div_iff hjt (mul_ne_zero hjt hj)]
  linear_combination (c * t + d) * ((t - w) * hdet + (c * t + d) * hw)

/-- **An element of `SL(2, ℝ)` fixing `z` is a rotation in the disc coordinate centred at `z`**,
by the unimodular multiplier `conj (denom g z) / denom g z`. -/
theorem discCoordinate_smul_of_smul_eq_self {g : SL(2, ℝ)} {z : ℍ} (hg : g • z = z) (τ : ℍ) :
    discCoordinate z (g • τ) = conj (denom g z) / denom g z * discCoordinate z τ := by
  have hz := congrArg ((↑) : ℍ → ℂ) hg
  have hj := denom_ne_zero g z
  have hjτ := denom_ne_zero g τ
  have hτ := coe_sub_conj_ne_zero z τ
  have hdet : (g 0 0 : ℂ) * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h := g.det_coe
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  simp only [coe_specialLinearGroup_apply, Algebra.algebraMap_self, RingHom.id_apply] at hz
  simp only [denom, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at hj hjτ ⊢
  rw [div_eq_iff hj] at hz
  have hjc : (g 1 0 : ℂ) * conj (z : ℂ) + g 1 1 ≠ 0 := by
    simpa using (map_ne_zero (starRingEnd ℂ)).mpr hj
  have hzc : (g 0 0 : ℂ) * conj (z : ℂ) + g 0 1 =
      conj (z : ℂ) * ((g 1 0 : ℂ) * conj (z : ℂ) + g 1 1) := by
    simpa using congrArg conj hz
  simp only [discCoordinate_def, coe_specialLinearGroup_apply, Algebra.algebraMap_self,
    RingHom.id_apply]
  rw [moebius_sub_of_fixed hdet hz hj hjτ, moebius_sub_of_fixed hdet hzc hjc hjτ]
  simp only [map_add, map_mul, Complex.conj_ofReal]
  rw [div_div_div_eq, div_mul_div_comm, div_eq_div_iff (mul_ne_zero (mul_ne_zero hjτ hj) hτ)
    (mul_ne_zero hj hτ)]
  ring

end UpperHalfPlane
