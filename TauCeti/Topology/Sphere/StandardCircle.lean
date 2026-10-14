/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import TauCeti.Topology.Homotopy.Cube.Sphere

/-!
# The standard parametrization of the circle

The loop `t ↦ (cos 2πt, sin 2πt)` parametrizes the unit circle `S¹ ⊆ ℝ²` once, counterclockwise,
starting at `(1, 0)`. As a map from the interval `I¹`, it collapses the boundary of the interval to
the point `(1, 0)` and is injective elsewhere, so it is a quotient map of `I¹` onto `S¹`.

## Main declarations

* `TauCeti.Sphere1.east`: the point `(1, 0)` of the unit circle.
* `TauCeti.circleLoop`: the standard loop `I¹ → S¹`.
* `TauCeti.circleLoop_eq_east_iff`, `TauCeti.circleLoop_surjective` and
  `TauCeti.eq_or_of_circleLoop_eq`: it collapses exactly the boundary to `(1, 0)`, is surjective,
  and is injective elsewhere.
-/

public section

noncomputable section

open Metric Real
open scoped unitInterval

namespace TauCeti

/-- The point `(1, 0)` of the unit circle. -/
def Sphere1.east : Sphere1 := ⟨EuclideanSpace.single 0 1, by simp⟩

/-- The standard loop `I¹ → S¹`, `t ↦ (cos 2πt, sin 2πt)`. -/
def circleLoop : C(Fin 1 → I, Sphere1) where
  toFun t :=
    ⟨!₂[cos (2 * π * t 0), sin (2 * π * t 0)], by
      rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Real.sqrt_eq_one]
      simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      exact cos_sq_add_sin_sq _⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    fin_cases i
    · simp only [Fin.zero_eta]
      fun_prop
    · simp only [Fin.mk_one]
      fun_prop

theorem circleLoop_apply_zero (t : Fin 1 → I) :
    (circleLoop t : EuclideanSpace ℝ (Fin 2)) 0 = cos (2 * π * t 0) := by
  rw [circleLoop]
  rfl

theorem circleLoop_apply_one (t : Fin 1 → I) :
    (circleLoop t : EuclideanSpace ℝ (Fin 2)) 1 = sin (2 * π * t 0) := by
  rw [circleLoop]
  rfl

private theorem exists_int_of_circleLoop_eq {a b : ℝ} (hc : cos (2 * π * a) = cos (2 * π * b))
    (hs : sin (2 * π * a) = sin (2 * π * b)) : ∃ n : ℤ, a = b + n := by
  have h : Complex.exp ((2 * π * a : ℝ) * Complex.I) =
      Complex.exp ((2 * π * b : ℝ) * Complex.I) := by
    refine Complex.ext ?_ ?_
    · rw [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_re, hc]
    · rw [Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_im, hs]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  refine ⟨n, ?_⟩
  have him := congrArg Complex.im hn
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.mul_im, Complex.mul_re,
    Complex.re_ofNat, Complex.ofReal_re, Complex.im_ofNat, Complex.ofReal_im, mul_zero, sub_zero,
    zero_mul, add_zero, Complex.I_im, mul_one, Complex.I_re, Complex.add_im, Complex.intCast_re,
    Complex.intCast_im, sub_self] at him
  have hpi : (2 * π) ≠ 0 := by positivity
  exact mul_left_cancel₀ hpi (by linarith)

private theorem mem_boundary_fin_one_iff (t : Fin 1 → I) :
    t ∈ Cube.boundary (Fin 1) ↔ (t 0 : ℝ) = 0 ∨ (t 0 : ℝ) = 1 := by
  simp only [Cube.boundary, Set.mem_ofPred_eq, Fin.exists_fin_one, Subtype.ext_iff,
    Set.Icc.coe_zero, Set.Icc.coe_one]

/-- The standard loop sends a point of the interval to `(1, 0)` exactly when it is an end point. -/
theorem circleLoop_eq_east_iff (t : Fin 1 → I) :
    circleLoop t = Sphere1.east ↔ t ∈ Cube.boundary (Fin 1) := by
  rw [mem_boundary_fin_one_iff]
  constructor
  · intro h
    have h0 := congrArg (fun q : Sphere1 => (q : EuclideanSpace ℝ (Fin 2)) 0) h
    simp only [circleLoop_apply_zero, Sphere1.east, PiLp.single_apply,
      ite_true] at h0
    obtain ⟨n, hn⟩ := Real.cos_eq_one_iff _ |>.1 h0
    have hpi : (2 * π) ≠ 0 := by positivity
    have hnt : (n : ℝ) = t 0 := mul_right_cancel₀ hpi (by linarith)
    have h1 : (0 : ℝ) ≤ n := hnt ▸ (t 0).2.1
    have h2 : (n : ℝ) ≤ 1 := hnt ▸ (t 0).2.2
    have : n = 0 ∨ n = 1 := by
      have h1' : 0 ≤ n := by exact_mod_cast h1
      have h2' : n ≤ 1 := by exact_mod_cast h2
      omega
    rcases this with rfl | rfl
    · exact Or.inl (by simpa using hnt.symm)
    · exact Or.inr (by simpa using hnt.symm)
  · rintro (h | h)
    · refine Subtype.ext ?_
      ext i
      fin_cases i <;> simp [circleLoop_apply_zero, circleLoop_apply_one, Sphere1.east, h]
    · refine Subtype.ext ?_
      ext i
      fin_cases i <;> simp [circleLoop_apply_zero, circleLoop_apply_one, Sphere1.east, h]

/-- Two points of the interval with the same image under the standard loop are equal, or both
end points. -/
theorem eq_or_of_circleLoop_eq {t t' : Fin 1 → I} (h : circleLoop t = circleLoop t') :
    t = t' ∨ (t ∈ Cube.boundary (Fin 1) ∧ t' ∈ Cube.boundary (Fin 1)) := by
  have hc := congrArg (fun q : Sphere1 => (q : EuclideanSpace ℝ (Fin 2)) 0) h
  have hs := congrArg (fun q : Sphere1 => (q : EuclideanSpace ℝ (Fin 2)) 1) h
  simp only [circleLoop_apply_zero, circleLoop_apply_one] at hc hs
  obtain ⟨n, hn⟩ := exists_int_of_circleLoop_eq hc hs
  have ha := (t 0).2
  have hb := (t' 0).2
  have h1 : (-1 : ℝ) ≤ n := by linarith [ha.1, ha.2, hb.1, hb.2]
  have h2 : (n : ℝ) ≤ 1 := by linarith [ha.1, ha.2, hb.1, hb.2]
  have h1' : -1 ≤ n := by exact_mod_cast h1
  have h2' : n ≤ 1 := by exact_mod_cast h2
  rw [mem_boundary_fin_one_iff, mem_boundary_fin_one_iff]
  have hcases : n = -1 ∨ n = 0 ∨ n = 1 := by omega
  rcases hcases with rfl | rfl | rfl
  · right
    push_cast at hn
    refine ⟨Or.inl ?_, Or.inr ?_⟩ <;> linarith [ha.1, ha.2, hb.1, hb.2]
  · left
    push_cast at hn
    funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact Subtype.ext (by linarith)
  · right
    push_cast at hn
    refine ⟨Or.inr ?_, Or.inl ?_⟩ <;> linarith [ha.1, ha.2, hb.1, hb.2]

/-- The standard loop is surjective. -/
theorem circleLoop_surjective : Function.Surjective circleLoop := by
  rintro ⟨v, hv⟩
  have hn : v 0 ^ 2 + v 1 ^ 2 = 1 := by
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Real.sqrt_eq_one] at hv
    simpa [Fin.sum_univ_two] using hv
  let z : ℂ := ⟨v 0, v 1⟩
  have hzn : ‖z‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_mk, Real.sqrt_eq_one]
    nlinarith
  have hz0 : z ≠ 0 := fun h => by simp [h] at hzn
  have hcos : cos (Complex.arg z) = v 0 := by
    rw [Complex.cos_arg hz0, hzn, div_one]
  have hsin : sin (Complex.arg z) = v 1 := by
    rw [Complex.sin_arg, hzn, div_one]
  set θ := Complex.arg z with hθ
  have hp : (0 : ℝ) < 2 * π := by positivity
  set r := toIcoMod hp 0 θ with hr
  have hrmem : r ∈ Set.Ico 0 (2 * π) := toIcoMod_mem_Ico' hp θ
  have hrθ : r = θ - (toIcoDiv hp 0 θ : ℝ) * (2 * π) := by
    rw [hr, toIcoMod, zsmul_eq_mul]
  have hrc : cos r = v 0 := by rw [hrθ, cos_sub_int_mul_two_pi, hcos]
  have hrs : sin r = v 1 := by rw [hrθ, sin_sub_int_mul_two_pi, hsin]
  have hs0 : 0 ≤ r / (2 * π) := div_nonneg hrmem.1 hp.le
  have hs1 : r / (2 * π) ≤ 1 := (div_le_one hp).2 hrmem.2.le
  refine ⟨fun _ => ⟨r / (2 * π), hs0, hs1⟩, Subtype.ext ?_⟩
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, circleLoop_apply_zero]
    rw [mul_div_cancel₀ _ hp.ne', hrc]
  · simp only [Fin.mk_one, circleLoop_apply_one]
    rw [mul_div_cancel₀ _ hp.ne', hrs]

end TauCeti
