/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Topology.UnitInterval
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.UnitInterval

/-!
# The two-sphere as the suspension of the circle

The map `I × S¹ → S²`, `(t, z) ↦ (cos πt, sin πt · z)`, from the product of the unit interval and
the circle to the unit sphere in `ℝ³ = ℝ × ℂ`, is a continuous surjection that collapses the
circle `{0} × S¹` to the north pole `(1, 0, 0)` and the circle `{1} × S¹` to the south pole
`(-1, 0, 0)`, and is injective elsewhere. So `S²` is the unreduced suspension of `S¹`.

## Main declarations

* `TauCeti.suspensionToSphere`: the continuous map `I × S¹ → S²`.
* `TauCeti.suspensionToSphere_surjective`: it is surjective.
* `TauCeti.suspensionToSphere_eq_north_iff` and `TauCeti.suspensionToSphere_eq_south_iff`: it
  collapses exactly the two ends to the poles.
* `TauCeti.eq_or_of_suspensionToSphere_eq`: its other fibres are single points.
-/

public section

noncomputable section

open Metric Real
open scoped unitInterval

namespace TauCeti

/-- The unit circle `S¹` in `ℝ²`. -/
abbrev Sphere1 : Type := sphere (0 : EuclideanSpace ℝ (Fin 2)) 1

/-- The unit sphere `S²` in `ℝ³`. -/
abbrev Sphere2 : Type := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- The north pole `(1, 0, 0)` of `S²`. -/
def Sphere2.north : Sphere2 :=
  ⟨!₂[1, 0, 0], by simp [EuclideanSpace.norm_eq, Fin.sum_univ_three]⟩

/-- The south pole `(-1, 0, 0)` of `S²`. -/
def Sphere2.south : Sphere2 :=
  ⟨!₂[-1, 0, 0], by simp [EuclideanSpace.norm_eq, Fin.sum_univ_three]⟩

/-- The map `I × S¹ → S²`, `(t, z) ↦ (cos πt, sin πt · z)`. -/
def suspensionToSphere : C(I × Circle, Sphere2) where
  toFun p :=
    ⟨!₂[cos (π * p.1), sin (π * p.1) * (p.2 : ℂ).re, sin (π * p.1) * (p.2 : ℂ).im], by
      have h := Circle.normSq_coe p.2
      simp only [Complex.normSq_apply, ← sq] at h
      rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Real.sqrt_eq_one]
      simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons]
      nlinarith [sin_sq_add_cos_sq (π * (p.1 : ℝ))]⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    fin_cases i
    · simp only [Fin.zero_eta]
      fun_prop
    · simp only [Fin.mk_one]
      fun_prop
    · simp only [Fin.reduceFinMk]
      fun_prop

@[simp]
theorem suspensionToSphere_apply_zero (p : I × Circle) :
    (suspensionToSphere p : EuclideanSpace ℝ (Fin 3)) 0 = cos (π * p.1) := by
  rw [suspensionToSphere]
  rfl

@[simp]
theorem suspensionToSphere_apply_one (p : I × Circle) :
    (suspensionToSphere p : EuclideanSpace ℝ (Fin 3)) 1 = sin (π * p.1) * (p.2 : ℂ).re := by
  rw [suspensionToSphere]
  rfl

@[simp]
theorem suspensionToSphere_apply_two (p : I × Circle) :
    (suspensionToSphere p : EuclideanSpace ℝ (Fin 3)) 2 = sin (π * p.1) * (p.2 : ℂ).im := by
  rw [suspensionToSphere]
  rfl

/-- The collapse sends exactly the end `{0} × S¹` to the north pole. -/
theorem suspensionToSphere_eq_north_iff (p : I × Circle) :
    suspensionToSphere p = Sphere2.north ↔ p.1 = 0 := by
  constructor
  · intro h
    have h0 := congrArg (fun x : Sphere2 => (x : EuclideanSpace ℝ (Fin 3)) 0) h
    simp only [suspensionToSphere_apply_zero] at h0
    refine cos_pi_mul_injOn (Set.mem_univ _) (Set.mem_univ _) ?_
    simpa [Sphere2.north] using h0
  · intro h
    refine Subtype.ext ?_
    ext i
    fin_cases i <;> simp [Sphere2.north, h, suspensionToSphere]

/-- The collapse sends exactly the end `{1} × S¹` to the south pole. -/
theorem suspensionToSphere_eq_south_iff (p : I × Circle) :
    suspensionToSphere p = Sphere2.south ↔ p.1 = 1 := by
  constructor
  · intro h
    have h0 := congrArg (fun x : Sphere2 => (x : EuclideanSpace ℝ (Fin 3)) 0) h
    simp only [suspensionToSphere_apply_zero] at h0
    refine cos_pi_mul_injOn (Set.mem_univ _) (Set.mem_univ _) ?_
    simpa [Sphere2.south] using h0
  · intro h
    refine Subtype.ext ?_
    ext i
    fin_cases i <;> simp [Sphere2.south, h, suspensionToSphere]

/-- Two points with the same image under the suspension map are equal, or both lie in the end
`{0} × S¹`, or both lie in the end `{1} × S¹`. -/
theorem eq_or_of_suspensionToSphere_eq {p p' : I × Circle}
    (h : suspensionToSphere p = suspensionToSphere p') :
    p = p' ∨ (p.1 = 0 ∧ p'.1 = 0) ∨ (p.1 = 1 ∧ p'.1 = 1) := by
  have hc := congrArg (fun x : Sphere2 => (x : EuclideanSpace ℝ (Fin 3)) 0) h
  have h1 := congrArg (fun x : Sphere2 => (x : EuclideanSpace ℝ (Fin 3)) 1) h
  have h2 := congrArg (fun x : Sphere2 => (x : EuclideanSpace ℝ (Fin 3)) 2) h
  simp only [suspensionToSphere_apply_zero, suspensionToSphere_apply_one,
    suspensionToSphere_apply_two] at hc h1 h2
  have ht : p.1 = p'.1 := cos_pi_mul_injOn (Set.mem_univ _) (Set.mem_univ _) hc
  by_cases h0 : p.1 = 0
  · exact Or.inr (Or.inl ⟨h0, ht ▸ h0⟩)
  by_cases h1' : p.1 = 1
  · exact Or.inr (Or.inr ⟨h1', ht ▸ h1'⟩)
  refine Or.inl (Prod.ext ht (Circle.ext (Complex.ext ?_ ?_)))
  · rw [← ht] at h1
    exact mul_left_cancel₀ (sin_pi_mul_pos h0 h1').ne' h1
  · rw [← ht] at h2
    exact mul_left_cancel₀ (sin_pi_mul_pos h0 h1').ne' h2

/-- The suspension map is surjective. -/
theorem suspensionToSphere_surjective : Function.Surjective suspensionToSphere := by
  rintro ⟨v, hv⟩
  have hn : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 := by
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Real.sqrt_eq_one] at hv
    simpa [Fin.sum_univ_three] using hv
  have ha : v 0 ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> nlinarith [sq_nonneg (v 1), sq_nonneg (v 2)]
  set θ := arccos (v 0) with hθ
  have hθ0 : 0 ≤ θ := arccos_nonneg _
  have hθ1 : θ ≤ π := arccos_le_pi _
  let t : I := ⟨θ / π, div_nonneg hθ0 pi_pos.le, (div_le_one pi_pos).2 hθ1⟩
  have htθ : π * (t : ℝ) = θ := by
    have ht : (t : ℝ) = θ / π := rfl
    rw [ht]
    field_simp
  have hs : sin θ = Real.sqrt (1 - v 0 ^ 2) := sin_arccos _
  have hc : cos θ = v 0 := cos_arccos ha.1 ha.2
  have hsq : v 1 ^ 2 + v 2 ^ 2 = sin θ ^ 2 := by
    have : sin θ ^ 2 = 1 - v 0 ^ 2 := by
      rw [← hc]
      linarith [sin_sq_add_cos_sq θ]
    linarith
  by_cases hz : sin θ = 0
  · refine ⟨(t, 1), Subtype.ext ?_⟩
    have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2)]
    have h2 : v 2 = 0 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2)]
    ext i
    fin_cases i <;> simp [suspensionToSphere, htθ, hz, hc, h1, h2]
  · have hsp : 0 < sin θ := lt_of_le_of_ne (sin_nonneg_of_nonneg_of_le_pi hθ0 hθ1) (Ne.symm hz)
    have hw : ‖(⟨v 1 / sin θ, v 2 / sin θ⟩ : ℂ)‖ = 1 := by
      rw [Complex.norm_def, Complex.normSq_mk, Real.sqrt_eq_one]
      field_simp
      linarith
    refine ⟨(t, ⟨⟨v 1 / sin θ, v 2 / sin θ⟩, mem_sphere_zero_iff_norm.2 hw⟩), Subtype.ext ?_⟩
    ext i
    fin_cases i <;> simp [suspensionToSphere, htθ, hc] <;> field_simp

end TauCeti
