/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ContinuousMap.GlueHalves
public import TauCeti.Topology.Homotopy.HurewiczFibration.Basic

/-!
# Relative homotopy lifting for the open box

A Hurewicz fibration `p : E → B` lifts homotopies relative to the open box: given a homotopy
`H : A × I × I → B` and a lift `g` of `H` on the open box `J = I × {0} ∪ ∂I × I` (the bottom and
the two sides of the square, in coordinates `(u, t)`), there is a lift of `H` on the whole square
that agrees with `g` on `J` (`TauCeti.IsHurewiczFibration.exists_lift_openBox`).  The data on `J`
is passed as a map on the whole square, of which only the values on `J` are used.

This is the form in which families of paths with prescribed end points are lifted: a homotopy of
paths whose end points stay fixed in `B` lifts to a homotopy of paths whose end points follow
prescribed lifts, for instance the constant lifts at a base point for loops
(`TauCeti.IsHurewiczFibration.loopMap`).  No cofibration theory is needed.

## Main results

* `TauCeti.IsHurewiczFibration.exists_lift_openBox`: relative homotopy lifting for the pair
  `(A × I × I, A × J)`.
* `TauCeti.IsHurewiczFibration.exists_homotopy_lifts`: two lifts of the same family of paths from
  the same starting points are homotopic through lifts, relative to the starting points.
* `TauCeti.IsHurewiczFibration.exists_homotopy_endpoints`: two lifts of the same family of paths
  from the same starting points have homotopic end points, fiberwise over the end points of the
  paths.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter I.7.
* A. Strøm, *Note on cofibrations II*, Math. Scand. 22 (1968), 130–142.
-/

public section

open unitInterval Set

universe w u v

namespace TauCeti

namespace OpenBox

/-- The denominator `max (2 - t) (4 |u - 1/2|)` of the deformation of the square onto the open
box. -/
noncomputable def den (u t : ℝ) : ℝ :=
  max (2 - t) (4 * |u - 1 / 2|)

/-- The time `φ(u, t) = 2 / max (2 - t) (4 |u - 1/2|) - 1` at which the deformation of the square
onto the open box reaches the point `(u, t)`; it vanishes exactly on the open box. -/
noncomputable def time (u t : ℝ) : ℝ :=
  2 / den u t - 1

theorem one_le_den (u : ℝ) (t : I) : 1 ≤ den u t :=
  le_max_of_le_left (by linarith [t.2.2])

theorem den_le_two (u t : I) : den u t ≤ 2 := by
  have h : |(u : ℝ) - 1 / 2| ≤ 1 / 2 := abs_le.2 ⟨by linarith [u.2.1], by linarith [u.2.2]⟩
  exact max_le (by linarith [t.2.1]) (by linarith)

theorem time_nonneg (u t : I) : 0 ≤ time u t := by
  have h1 := one_le_den u t
  rw [time, sub_nonneg, le_div_iff₀ (by linarith)]
  linarith [den_le_two u t]

theorem time_le_one (u t : I) : time u t ≤ 1 := by
  have h1 := one_le_den u t
  rw [time, sub_le_iff_le_add, div_le_iff₀ (by linarith)]
  linarith

theorem continuous_time : Continuous fun x : I × I ↦ time x.1 x.2 := by
  refine (Continuous.div continuous_const ?_ fun x ↦ ?_).sub continuous_const
  · unfold den
    fun_prop
  · exact (lt_of_lt_of_le one_pos (one_le_den x.1 x.2)).ne'

/-- The point of the open box `J = I × {0} ∪ ∂I × I`. -/
def IsBox (x : I × I) : Prop :=
  x.2 = 0 ∨ x.1 = 0 ∨ x.1 = 1

theorem time_eq_zero_of_isBox {x : I × I} (hx : IsBox x) : time x.1 x.2 = 0 := by
  have hden : den x.1 x.2 = 2 := by
    refine le_antisymm (den_le_two _ _) ?_
    rcases hx with h | h | h
    · exact le_max_of_le_left (by simp [h])
    · exact le_max_of_le_right (by simp [h]; norm_num)
    · exact le_max_of_le_right (by simp [h]; norm_num)
  simp [time, hden]

/-- The `u`-coordinate of the radial projection of `(u, t)` from `(1/2, 2)` onto the open box. -/
noncomputable def projU (u t : ℝ) : ℝ :=
  u + time u t * (u - 1 / 2)

/-- The `t`-coordinate of the radial projection of `(u, t)` from `(1/2, 2)` onto the open box. -/
noncomputable def projT (u t : ℝ) : ℝ :=
  t + time u t * (t - 2)

/-- The radial projection lands on the open box: its `t`-coordinate is `0` or its `u`-coordinate
is `0` or `1`. -/
theorem projT_eq_zero_or (u t : I) :
    projT u t = 0 ∨ projU u t = 0 ∨ projU u t = 1 := by
  have h1 := one_le_den u t
  rcases max_choice (2 - (t : ℝ)) (4 * |(u : ℝ) - 1 / 2|) with h | h
  · left
    have hden : den u t = 2 - t := h
    have h2 : (2 : ℝ) - t ≠ 0 := by linarith
    have key : 2 / (2 - (t : ℝ)) * (t - 2) = -2 := by field_simp; ring
    rw [projT, time, hden, sub_mul, key]
    ring
  · right
    have hden : den u t = 4 * |(u : ℝ) - 1 / 2| := h
    have hu : (u : ℝ) - 1 / 2 ≠ 0 := by
      intro hu
      rw [hden, hu, abs_zero, mul_zero] at h1
      linarith
    rcases lt_or_gt_of_ne hu with hneg | hpos
    · left
      have key : 2 / (4 * -((u : ℝ) - 1 / 2)) * (u - 1 / 2) = -1 / 2 := by
        rw [div_mul_eq_mul_div, div_eq_iff (mul_ne_zero four_ne_zero (neg_ne_zero.2 hu))]
        ring
      rw [projU, time, hden, abs_of_neg hneg, sub_mul, key]
      ring
    · right
      have key : 2 / (4 * ((u : ℝ) - 1 / 2)) * (u - 1 / 2) = 1 / 2 := by
        rw [div_mul_eq_mul_div, div_eq_iff (by simpa using hu)]
        ring
      rw [projU, time, hden, abs_of_pos hpos, sub_mul, key]
      ring

/-- The deformation `k(s, x) = r(x) + min (φ x, s) (P - x)` of the square, clamped to the square,
where `P = (1/2, 2)` lies above the square and `r(x) = x + φ(x) (x - P)` is the radial projection of
`x` from `P` onto the open box: at time `0` it is `r(x)`, at time `φ x` it is `x`, and it is
constant at the points of the open box. -/
noncomputable def deform (s : I) (x : I × I) : I × I :=
  (projIcc 0 1 zero_le_one (projU x.1 x.2 + min (time x.1 x.2) s * (1 / 2 - x.1)),
    projIcc 0 1 zero_le_one (projT x.1 x.2 + min (time x.1 x.2) s * (2 - x.2)))

theorem continuous_deform : Continuous fun y : I × (I × I) ↦ deform y.1 y.2 := by
  have hφ : Continuous fun y : I × (I × I) ↦ time y.2.1 y.2.2 :=
    continuous_time.comp continuous_snd
  refine (continuous_projIcc.comp ?_).prodMk (continuous_projIcc.comp ?_) <;>
  · simp only [projU, projT]
    fun_prop

theorem deform_zero_isBox (x : I × I) : IsBox (deform 0 x) := by
  have h0 : min (time x.1 x.2) ((0 : I) : ℝ) = 0 := min_eq_right (time_nonneg _ _)
  simp only [IsBox, deform, h0, zero_mul, add_zero]
  rcases projT_eq_zero_or x.1 x.2 with h | h | h
  · left; rw [h]; exact projIcc_left zero_le_one
  · right; left; rw [h]; exact projIcc_left zero_le_one
  · right; right; rw [h]; exact projIcc_right zero_le_one

theorem deform_time (x : I × I) :
    deform (projIcc 0 1 zero_le_one (time x.1 x.2)) x = x := by
  have hφ : ((projIcc 0 1 zero_le_one (time x.1 x.2) : I) : ℝ) = time x.1 x.2 :=
    congrArg Subtype.val (projIcc_of_mem zero_le_one ⟨time_nonneg _ _, time_le_one _ _⟩)
  simp only [deform, hφ, min_self, projU, projT]
  refine Prod.ext ?_ ?_
  · have hu : (x.1 : ℝ) + time x.1 x.2 * (x.1 - 1 / 2) + time x.1 x.2 * (1 / 2 - x.1) = x.1 := by
      ring
    rw [hu]
    exact projIcc_val zero_le_one _
  · have ht : (x.2 : ℝ) + time x.1 x.2 * (x.2 - 2) + time x.1 x.2 * (2 - x.2) = x.2 := by ring
    rw [ht]
    exact projIcc_val zero_le_one _

theorem deform_zero_of_isBox {x : I × I} (hx : IsBox x) : deform 0 x = x := by
  have h := time_eq_zero_of_isBox hx
  have h0 : projIcc 0 1 zero_le_one (time x.1 x.2) = 0 := by
    rw [h]; exact projIcc_left zero_le_one
  simpa [h0] using deform_time x

end OpenBox

open OpenBox

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}
  {A : Type w} [TopologicalSpace A]

/-- **Relative homotopy lifting for the open box.** For a Hurewicz fibration `p`, a homotopy
`H : A × I × I → B` with a lift `g` on the open box `I × {0} ∪ ∂I × I` (coordinates `(u, t)`)
lifts to the whole square, agreeing with `g` on the open box.  Only the values of `g` on the
open box matter. -/
theorem IsHurewiczFibration.exists_lift_openBox (hp : IsHurewiczFibration.{w} p)
    (g : C(A × (I × I), E)) (H : C(A × (I × I), B))
    (hg : ∀ a (x : I × I), x.2 = 0 ∨ x.1 = 0 ∨ x.1 = 1 → p (g (a, x)) = H (a, x)) :
    ∃ G : C(A × (I × I), E), p ∘ G = H ∧
      ∀ a (x : I × I), x.2 = 0 ∨ x.1 = 0 ∨ x.1 = 1 → G (a, x) = g (a, x) := by
  -- Lift `H ∘ deform` from `g ∘ deform 0` and evaluate the lift at time `time x`.
  let K : C(I × (A × (I × I)), B) :=
    ⟨fun y ↦ H (y.2.1, deform y.1 y.2.2),
      H.continuous.comp ((continuous_fst.comp continuous_snd).prodMk
      (continuous_deform.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))))⟩
  let f₀ : C(A × (I × I), E) :=
    ⟨fun y ↦ g (y.1, deform 0 y.2), g.continuous.comp (continuous_fst.prodMk
      (continuous_deform.comp ((continuous_const (y := (0 : I))).prodMk continuous_snd)))⟩
  obtain ⟨L, hL, hL₀⟩ := hp.hasHomotopyLiftingProperty (A × (I × I)) f₀ K fun y ↦
    (hg y.1 _ (deform_zero_isBox y.2)).symm
  let τ : C(I × I, I) := ⟨fun x ↦ projIcc 0 1 zero_le_one (time x.1 x.2),
    continuous_projIcc.comp continuous_time⟩
  refine ⟨⟨fun y ↦ L (τ y.2, y), by fun_prop⟩, funext fun y ↦ ?_, fun a x hx ↦ ?_⟩
  · have := congrFun hL (τ y.2, y)
    simp only [Function.comp_apply, ContinuousMap.coe_mk] at this ⊢
    rw [this]
    simp only [K, ContinuousMap.coe_mk, τ, deform_time]
  · have hτ : τ x = 0 := by
      simp only [τ, ContinuousMap.coe_mk, time_eq_zero_of_isBox hx]
      exact projIcc_left zero_le_one
    simp only [ContinuousMap.coe_mk, hτ, hL₀, f₀, deform_zero_of_isBox hx]

section Endpoints

/-- The reparametrization `(u, t) ↦ t (1 - 2 u)`, clipped to `I`: on the left half of the square
it runs from the full path at `u = 0` to the constant path at `u = 1/2`. -/
private noncomputable def leftTime : C(I × I, I) :=
  ⟨fun x ↦ projIcc 0 1 zero_le_one ((x.2 : ℝ) * (1 - 2 * x.1)),
    continuous_projIcc.comp (by fun_prop)⟩

/-- The reparametrization `(u, t) ↦ t (2 u - 1)`, clipped to `I`: on the right half of the square
it runs from the constant path at `u = 1/2` to the full path at `u = 1`. -/
private noncomputable def rightTime : C(I × I, I) :=
  ⟨fun x ↦ projIcc 0 1 zero_le_one ((x.2 : ℝ) * (2 * x.1 - 1)),
    continuous_projIcc.comp (by fun_prop)⟩

private theorem leftTime_apply (x : I × I) :
    leftTime x = projIcc 0 1 zero_le_one ((x.2 : ℝ) * (1 - 2 * x.1)) :=
  (rfl) -- the definition of `leftTime`

private theorem rightTime_apply (x : I × I) :
    rightTime x = projIcc 0 1 zero_le_one ((x.2 : ℝ) * (2 * x.1 - 1)) :=
  (rfl) -- the definition of `rightTime`

private theorem leftTime_zero_left (t : I) : leftTime (0, t) = t := by simp [leftTime_apply]

private theorem leftTime_zero_right (u : I) : leftTime (u, 0) = 0 := by simp [leftTime_apply]

private theorem leftTime_half (x : I × I) (hx : (x.1 : ℝ) = 2⁻¹) : leftTime x = 0 := by
  simp [leftTime_apply, hx]

private theorem rightTime_one_left (t : I) : rightTime (1, t) = t := by
  simp [rightTime_apply]; norm_num

private theorem rightTime_zero_right (u : I) : rightTime (u, 0) = 0 := by simp [rightTime_apply]

private theorem rightTime_half (x : I × I) (hx : (x.1 : ℝ) = 2⁻¹) : rightTime x = 0 := by
  simp [rightTime_apply, hx]

variable {Y : Type*} [TopologicalSpace Y]

/-- The lift on the open box of two families of paths with the same starting points: `α` on the
side `u = 0`, `α'` on the side `u = 1`, and the common starting point on the bottom. -/
private noncomputable def openBoxDatum (α α' : C(Y × I, E)) (h₀ : ∀ y, α (y, 0) = α' (y, 0)) :
    C(Y × (I × I), E) :=
  ContinuousMap.glueHalves (ContinuousMap.fst.comp ContinuousMap.snd)
    (α.comp ⟨fun x ↦ (x.1, leftTime x.2), by fun_prop⟩)
    (α'.comp ⟨fun x ↦ (x.1, rightTime x.2), by fun_prop⟩)
    (fun x hx ↦ by
      simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk]
      rw [leftTime_half x.2 hx, rightTime_half x.2 hx]
      exact h₀ x.1)

variable (α α' : C(Y × I, E)) (h₀ : ∀ y, α (y, 0) = α' (y, 0))

private theorem openBoxDatum_of_le {y : Y} {x : I × I} (hx : (x.1 : ℝ) ≤ 2⁻¹) :
    openBoxDatum α α' h₀ (y, x) = α (y, leftTime x) :=
  ContinuousMap.glueHalves_of_le _ _ _ _ hx

private theorem openBoxDatum_of_not_le {y : Y} {x : I × I} (hx : ¬ (x.1 : ℝ) ≤ 2⁻¹) :
    openBoxDatum α α' h₀ (y, x) = α' (y, rightTime x) :=
  ContinuousMap.glueHalves_of_not_le _ _ _ _ hx

private theorem openBoxDatum_left (y : Y) (t : I) :
    openBoxDatum α α' h₀ (y, (0, t)) = α (y, t) := by
  rw [openBoxDatum_of_le α α' h₀ (by simp), leftTime_zero_left]

private theorem openBoxDatum_right (y : Y) (t : I) :
    openBoxDatum α α' h₀ (y, (1, t)) = α' (y, t) := by
  rw [openBoxDatum_of_not_le α α' h₀ (by norm_num), rightTime_one_left]

private theorem openBoxDatum_bottom (y : Y) (u : I) :
    openBoxDatum α α' h₀ (y, (u, 0)) = α (y, 0) := by
  by_cases hu : (u : ℝ) ≤ 2⁻¹
  · rw [openBoxDatum_of_le α α' h₀ hu, leftTime_zero_right]
  · rw [openBoxDatum_of_not_le α α' h₀ hu, rightTime_zero_right, h₀]

end Endpoints

/-- **Lifts of the same family of paths are vertically homotopic.**  Let `α` and `α'` be two
families of paths in `E`, parametrized by a space `Y`, with the same starting points and lying over
the same family `γ` of paths in `B`.  Then they are homotopic through lifts of `γ`, relative to
their starting points: there is a family of squares `G`, in coordinates `(u, t)`, equal to `α` on
the side `u = 0`, to `α'` on the side `u = 1` and to the common starting point on the bottom
`t = 0`, with `p (G (y, (u, t))) = γ (y, t)` throughout. -/
theorem IsHurewiczFibration.exists_homotopy_lifts {Y : Type w} [TopologicalSpace Y]
    (hp : IsHurewiczFibration.{w} p) (γ : C(Y × I, B)) (α α' : C(Y × I, E))
    (hα : ∀ y t, p (α (y, t)) = γ (y, t))
    (hα' : ∀ y t, p (α' (y, t)) = γ (y, t)) (h₀ : ∀ y, α (y, 0) = α' (y, 0)) :
    ∃ G : C(Y × (I × I), E), (∀ y t, G (y, (0, t)) = α (y, t)) ∧
      (∀ y t, G (y, (1, t)) = α' (y, t)) ∧ (∀ y u, G (y, (u, 0)) = α (y, 0)) ∧
      ∀ y u t, p (G (y, (u, t))) = γ (y, t) := by
  let H : C(Y × (I × I), B) := ⟨fun x ↦ γ (x.1, x.2.2), by fun_prop⟩
  have H_apply : ∀ x, H x = γ (x.1, x.2.2) := fun _ ↦ (rfl) -- the definition of `H`
  -- Lift the square over `γ (y, t)` from the data on the open box.
  obtain ⟨G, hG, hGJ⟩ := hp.exists_lift_openBox (openBoxDatum α α' h₀) H (by
    rintro y ⟨u, t⟩ (h | h | h)
    · obtain rfl : t = 0 := h
      rw [openBoxDatum_bottom, hα, H_apply]
    · obtain rfl : u = 0 := h
      rw [openBoxDatum_left, hα, H_apply]
    · obtain rfl : u = 1 := h
      rw [openBoxDatum_right, hα', H_apply])
  refine ⟨G, fun y t ↦ ?_, fun y t ↦ ?_, fun y u ↦ ?_, fun y u t ↦ ?_⟩
  · rw [hGJ y (0, t) (Or.inr (Or.inl rfl)), openBoxDatum_left]
  · rw [hGJ y (1, t) (Or.inr (Or.inr rfl)), openBoxDatum_right]
  · rw [hGJ y (u, 0) (Or.inl rfl), openBoxDatum_bottom]
  · rw [← H_apply (y, (u, t))]
    exact congr_fun hG (y, (u, t))

/-- **Uniqueness of lifts up to homotopy.**  Let `α` and `α'` be two families of paths in `E`,
parametrized by a space `Y`, with the same starting points and lying over the same family `γ` of
paths in `B`.  Then their end points are homotopic: there is a homotopy `K` from `α (·, 1)` to
`α' (·, 1)` such that, for each `y`, it stays in the fiber over `γ (y, 1)`, the end point of the
path `γ (y, ·)`. -/
theorem IsHurewiczFibration.exists_homotopy_endpoints {Y : Type w} [TopologicalSpace Y]
    (hp : IsHurewiczFibration.{w} p) (γ : C(Y × I, B)) (α α' : C(Y × I, E))
    (hα : ∀ y t, p (α (y, t)) = γ (y, t))
    (hα' : ∀ y t, p (α' (y, t)) = γ (y, t)) (h₀ : ∀ y, α (y, 0) = α' (y, 0)) :
    ∃ K : C(Y × I, E), (∀ y, K (y, 0) = α (y, 1)) ∧ (∀ y, K (y, 1) = α' (y, 1)) ∧
      ∀ y s, p (K (y, s)) = γ (y, 1) := by
  obtain ⟨G, hG₀, hG₁, -, hG⟩ := hp.exists_homotopy_lifts γ α α' hα hα' h₀
  -- The homotopy is the lift on the top edge `t = 1`.
  exact ⟨⟨fun z ↦ G (z.1, (z.2, 1)), by fun_prop⟩, fun y ↦ hG₀ y 1, fun y ↦ hG₁ y 1,
    fun y s ↦ hG y s 1⟩

end TauCeti
