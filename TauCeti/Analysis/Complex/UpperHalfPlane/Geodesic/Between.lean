/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic
public import TauCeti.Analysis.Complex.UpperHalfPlane.Rotation
public import TauCeti.Analysis.Complex.UpperHalfPlane.SmulDeriv
import TauCeti.Analysis.Complex.UpperHalfPlane.Stabilizer

/-!
# The geodesic line through two points of the upper half-plane

`geodesicBetween z w` is the parametrised geodesic line with `z` at parameter `0` and `w` at
parameter `dist z w`; it is unique (`eq_geodesicBetween_of_geodesicLine_eq`), since an element
of `PSL(2, ℝ)` fixing two points is the identity, and so it transforms naturally under the
action (`geodesicBetween_smul`). Reparametrisation is right multiplication by the dilations
`dilation s : z ↦ exp s * z` (`geodesicLine_mul_dilation`) and by `pslS`
(`geodesicLine_mul_pslS`); together they give the reversed line `geodesicBetween w z`.

Source: Katok, *Fuchsian groups, geodesic flows on surfaces of constant negative curvature and
symbolic coding of geodesics*, Clay Math. Proc. 8 (2008), §3 p. 10 (Theorem 3.1 and the
remark after it: any two points of `ℍ` are joined by a unique geodesic).
-/

public section

noncomputable section

open Matrix.ProjectiveSpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups

namespace TauCeti.UpperHalfPlane

open Matrix.SpecialLinearGroup (rotation)

/-! ### Dilations -/

/-- The dilation `!![exp (s / 2), 0; 0, exp (-(s / 2))]`, an element of `SL(2, ℝ)` acting on `ℍ`
as `z ↦ exp s * z`. -/
def _root_.Matrix.SpecialLinearGroup.dilation (s : ℝ) : SL(2, ℝ) :=
  ⟨!![Real.exp (s / 2), 0; 0, Real.exp (-(s / 2))], by
    rw [Matrix.det_fin_two_of]
    simp [← Real.exp_add]⟩

open Matrix.SpecialLinearGroup (dilation)

/-- The entries of `dilation s`. -/
@[simp]
theorem coe_dilation (s : ℝ) :
    (dilation s : Matrix (Fin 2) (Fin 2) ℝ) = !![Real.exp (s / 2), 0; 0, Real.exp (-(s / 2))] :=
  (rfl)

/-- `dilation s` acts on `ℍ` as `z ↦ exp s * z`. -/
theorem coe_dilation_smul (s : ℝ) (z : ℍ) : ((dilation s • z : ℍ) : ℂ) = Real.exp s * z := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [coe_dilation, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Algebra.algebraMap_self_apply,
    Complex.ofReal_zero, zero_mul, add_zero, zero_add]
  have h2 : (Real.exp s : ℂ) = Real.exp (s / 2) * Real.exp (s / 2) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, add_halves]
  have hne : (Real.exp (-(s / 2)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'
  rw [div_eq_iff hne, h2, Real.exp_neg]
  push_cast
  field_simp

/-- The dilation by `0` is the identity. -/
@[simp]
theorem dilation_zero : dilation 0 = 1 :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j ↦ by
    fin_cases i <;> fin_cases j <;> simp

/-- The dilations form a one-parameter subgroup: `dilation (s + t) = dilation s * dilation t`. -/
theorem dilation_add (s t : ℝ) : dilation (s + t) = dilation s * dilation t :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j ↦ by
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← Real.exp_add, add_div, add_comm]

/-- The inverse of `dilation s` is `dilation (-s)`. -/
@[simp]
theorem dilation_inv (s : ℝ) : (dilation s)⁻¹ = dilation (-s) :=
  inv_eq_of_mul_eq_one_right (by rw [← dilation_add, add_neg_cancel, dilation_zero])

/-- The imaginary axis is the orbit of `I` under the dilations. -/
theorem geodesicLine_one_eq_dilation_smul_I (t : ℝ) :
    geodesicLine 1 t = dilation t • UpperHalfPlane.I := by
  apply UpperHalfPlane.coe_injective
  rw [geodesicLine_one_apply, coe_dilation_smul, UpperHalfPlane.coe_mk, UpperHalfPlane.coe_I]
  simp [Complex.ext_iff, Complex.exp_ofReal_re]

/-- Right multiplication by a dilation shifts the parameter of a geodesic line. -/
@[simp]
theorem geodesicLine_mul_dilation (g : PSL(2, ℝ)) (s t : ℝ) :
    geodesicLine (g * ↑(dilation s)) t = geodesicLine g (s + t) := by
  rw [← smul_geodesicLine]
  conv_rhs => rw [← mul_one g, ← smul_geodesicLine]
  congr 1
  rw [geodesicLine_def, UpperHalfPlane.pslMk_smul, ← geodesicLine_one_apply,
    geodesicLine_one_eq_dilation_smul_I, geodesicLine_one_eq_dilation_smul_I, ← mul_smul,
    ← dilation_add]

/-- Shifting the parameter does not change a geodesic line as a set. -/
@[simp]
theorem range_geodesicLine_mul_dilation (g : PSL(2, ℝ)) (s : ℝ) :
    Set.range (geodesicLine (g * ↑(dilation s))) = Set.range (geodesicLine g) := by
  have h : geodesicLine (g * ↑(dilation s)) = geodesicLine g ∘ (s + ·) :=
    funext (geodesicLine_mul_dilation g s)
  rw [h, (add_left_surjective s).range_comp]

-- Not `@[simp]`: `smulDeriv_coe` rewrites the left-hand side first. Use it via `rw`.
/-- The derivative of the dilation `z ↦ exp s * z` is `exp s`. -/
theorem smulDeriv_dilation (s : ℝ) (z : ℍ) : smulDeriv (↑(dilation s)) z = Real.exp s := by
  rw [Matrix.SpecialLinearGroup.smulDeriv_coe]
  simp only [denom, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    Algebra.algebraMap_self_apply, coe_dilation, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Complex.ofReal_zero,
    zero_mul, zero_add]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_inv, Complex.ofReal_inj, ← Real.exp_nat_mul,
    ← Real.exp_neg]
  congr 1
  push_cast
  ring

/-! ### The stabiliser of `I` -/

/-- Every element of `PSL(2, ℝ)` fixing `I` is the class of a rotation.
Source: Katok, *Fuchsian groups, geodesic flows…* (Clay Math. Proc. 8), §1 p. 6:
`K = SO(2)` is the stabiliser of `i` in `SL(2, ℝ)`. -/
theorem exists_rotation_eq_of_smul_I_eq_I {q : PSL(2, ℝ)}
    (hq : q • UpperHalfPlane.I = UpperHalfPlane.I) : ∃ θ : ℝ, q = ↑(rotation θ) := by
  induction q using QuotientGroup.induction_on with | _ g =>
  rw [UpperHalfPlane.pslMk_smul, MulAction.compHom_smul_def,
    gl_smul_I_eq_I_iff_of_pos (by simp)] at hq
  simp only [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.algebraMap_self_apply] at hq
  obtain ⟨h₀, h₁⟩ := hq
  -- the representative is `!![a, -c; c, a]` with `a ^ 2 + c ^ 2 = 1`
  have hdet : g 0 0 ^ 2 + g 1 0 ^ 2 = 1 := by
    have := g.det_coe
    rw [Matrix.det_fin_two, h₁, ← h₀] at this
    linear_combination this
  set w : ℂ := g 0 0 - g 1 0 * Complex.I with hw
  have hnorm : ‖w‖ = 1 := by
    rw [hw, Complex.norm_eq_sqrt_sq_add_sq]
    simp [hdet]
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact zero_ne_one hnorm
  refine ⟨w.arg, ?_⟩
  congr 1
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j ↦ ?_
  have hcos : Real.cos w.arg = g 0 0 := by
    rw [Complex.cos_arg hw0, hnorm, div_one, hw]
    simp
  have hsin : Real.sin w.arg = -g 1 0 := by
    rw [Complex.sin_arg, hnorm, div_one, hw]
    simp
  fin_cases i <;> fin_cases j <;> simp [hcos, hsin, h₀, h₁]

/-! ### The geodesic line through two points -/

/-- The geodesic line from `z` to `w`: `z` sits at parameter `0` and `w` at parameter
`dist z w`. -/
def geodesicBetween (z w : ℍ) : PSL(2, ℝ) :=
  Classical.choose (exists_geodesicLine_zero_eq_and_dist_eq z w)

/-- The geodesic line from `z` to `w` starts at `z`. -/
@[simp]
theorem geodesicLine_geodesicBetween_zero (z w : ℍ) :
    geodesicLine (geodesicBetween z w) 0 = z :=
  (Classical.choose_spec (exists_geodesicLine_zero_eq_and_dist_eq z w)).1

/-- The geodesic line from `z` to `w` reaches `w` at parameter `dist z w`. -/
@[simp]
theorem geodesicLine_geodesicBetween_dist (z w : ℍ) :
    geodesicLine (geodesicBetween z w) (dist z w) = w :=
  (Classical.choose_spec (exists_geodesicLine_zero_eq_and_dist_eq z w)).2

/-- `z` lies on the geodesic line from `z` to `w`. -/
theorem mem_range_geodesicLine_geodesicBetween_left (z w : ℍ) :
    z ∈ Set.range (geodesicLine (geodesicBetween z w)) :=
  ⟨0, geodesicLine_geodesicBetween_zero z w⟩

/-- `w` lies on the geodesic line from `z` to `w`. -/
theorem mem_range_geodesicLine_geodesicBetween_right (z w : ℍ) :
    w ∈ Set.range (geodesicLine (geodesicBetween z w)) :=
  ⟨dist z w, geodesicLine_geodesicBetween_dist z w⟩

/-- **Uniqueness of the geodesic through two points**: a parametrised geodesic line with `z` at
parameter `0` and `w` at parameter `dist z w` is `geodesicBetween z w`. -/
theorem eq_geodesicBetween_of_geodesicLine_eq {g : PSL(2, ℝ)} {z w : ℍ} (hzw : z ≠ w)
    (h0 : geodesicLine g 0 = z) (hd : geodesicLine g (dist z w) = w) :
    g = geodesicBetween z w := by
  -- `(geodesicBetween z w)⁻¹ * g` fixes the two distinct points `I` and `i exp (dist z w)`
  have key : ∀ t : ℝ, geodesicLine g t = geodesicLine (geodesicBetween z w) t →
      ((geodesicBetween z w)⁻¹ * g) • geodesicLine 1 t = geodesicLine 1 t := by
    intro t ht
    have h1 := smul_geodesicLine (geodesicBetween z w) 1 t
    rw [mul_one] at h1
    rw [smul_geodesicLine, mul_one, ← smul_geodesicLine, ht, ← h1, inv_smul_smul]
  have h := eq_one_of_smul_eq_self_of_smul_eq_self
    (key 0 (by rw [h0, geodesicLine_geodesicBetween_zero]))
    (key (dist z w) (by rw [hd, geodesicLine_geodesicBetween_dist]))
    (fun h ↦ (dist_pos.2 hzw).ne' (geodesicLine_injective 1 h))
  rwa [inv_mul_eq_one, eq_comm] at h

/-- The geodesic line through two points transforms naturally under the action. -/
theorem geodesicBetween_smul (h : PSL(2, ℝ)) {z w : ℍ} (hzw : z ≠ w) :
    geodesicBetween (h • z) (h • w) = h * geodesicBetween z w := by
  symm
  refine eq_geodesicBetween_of_geodesicLine_eq ((MulAction.injective h).ne hzw) ?_ ?_
  · rw [← smul_geodesicLine, geodesicLine_geodesicBetween_zero]
  · rw [(isometry_smul ℍ h).dist_eq, ← smul_geodesicLine, geodesicLine_geodesicBetween_dist]

/-- The geodesic line from `w` back to `z` is the line from `z` to `w`, shifted to start at `w`
and reversed. -/
theorem geodesicBetween_swap {z w : ℍ} (hzw : z ≠ w) :
    geodesicBetween w z = geodesicBetween z w * ↑(dilation (dist z w)) * pslS := by
  symm
  refine eq_geodesicBetween_of_geodesicLine_eq hzw.symm ?_ ?_
  · rw [geodesicLine_mul_pslS, neg_zero, geodesicLine_mul_dilation, add_zero,
      geodesicLine_geodesicBetween_dist]
  · rw [geodesicLine_mul_pslS, geodesicLine_mul_dilation, dist_comm, add_neg_cancel,
      geodesicLine_geodesicBetween_zero]

/-- The geodesic lines from `z` to `w` and from `w` to `z` have the same image. -/
theorem range_geodesicLine_geodesicBetween_swap {z w : ℍ} (hzw : z ≠ w) :
    Set.range (geodesicLine (geodesicBetween w z)) =
      Set.range (geodesicLine (geodesicBetween z w)) := by
  rw [geodesicBetween_swap hzw, range_geodesicLine_mul_pslS, range_geodesicLine_mul_dilation]

/-- Two distinct points of a geodesic line determine it: the geodesic line through them has the
same image. -/
theorem range_geodesicLine_geodesicBetween_of_mem {g : PSL(2, ℝ)} {z w : ℍ}
    (hz : z ∈ Set.range (geodesicLine g)) (hw : w ∈ Set.range (geodesicLine g)) (hzw : z ≠ w) :
    Set.range (geodesicLine (geodesicBetween z w)) = Set.range (geodesicLine g) := by
  obtain ⟨s, rfl⟩ := hz
  obtain ⟨t, rfl⟩ := hw
  have hst : s ≠ t := fun h ↦ hzw (h ▸ rfl)
  rcases lt_or_gt_of_ne hst with h | h
  · have : geodesicBetween (geodesicLine g s) (geodesicLine g t) = g * ↑(dilation s) := by
      symm
      refine eq_geodesicBetween_of_geodesicLine_eq hzw ?_ ?_
      · rw [geodesicLine_mul_dilation, add_zero]
      · rw [geodesicLine_mul_dilation, dist_geodesicLine, abs_of_neg (by linarith)]
        congr 1
        ring
    rw [this, range_geodesicLine_mul_dilation]
  · have : geodesicBetween (geodesicLine g s) (geodesicLine g t) = g * ↑(dilation s) * pslS := by
      symm
      refine eq_geodesicBetween_of_geodesicLine_eq hzw ?_ ?_
      · rw [geodesicLine_mul_pslS, neg_zero, geodesicLine_mul_dilation, add_zero]
      · rw [geodesicLine_mul_pslS, geodesicLine_mul_dilation, dist_geodesicLine,
          abs_of_pos (by linarith)]
        congr 1
        ring
    rw [this, range_geodesicLine_mul_pslS, range_geodesicLine_mul_dilation]

/-- The geodesic line from `I` up the imaginary axis is the identity's. -/
theorem geodesicBetween_I_geodesicLine_one {d : ℝ} (hd : 0 < d) :
    geodesicBetween UpperHalfPlane.I (geodesicLine 1 d) = 1 := by
  have h0 : geodesicLine 1 0 = UpperHalfPlane.I := by rw [geodesicLine_zero, one_smul]
  symm
  refine eq_geodesicBetween_of_geodesicLine_eq (fun h ↦ hd.ne ?_) h0 ?_
  · exact geodesicLine_injective 1 (h0.trans h)
  · rw [← h0, dist_geodesicLine, zero_sub, abs_neg, abs_of_pos hd]

/-- The geodesic line from `I` to any point is a rotation of the imaginary axis. -/
theorem exists_geodesicBetween_I_eq_rotation (z : ℍ) :
    ∃ θ : ℝ, geodesicBetween UpperHalfPlane.I z = ↑(rotation θ) :=
  exists_rotation_eq_of_smul_I_eq_I
    (by rw [← geodesicLine_zero, geodesicLine_geodesicBetween_zero])

end TauCeti.UpperHalfPlane
