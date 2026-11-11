/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Analysis.Real.Sqrt
public import TauCeti.Analysis.InnerProductSpace.TwoDim
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Algebra.Order.ToIntervalMod
import TauCeti.Analysis.Calculus.PeriodicDeriv

/-!
# The next-collision map of a strictly convex billiard table

Let `χ : ℝ → E` be an `L`-periodic arclength parametrization of the boundary of a bounded strictly
convex table in an oriented Euclidean plane `E`, positively oriented, with `L > 0` and `χ` injective
on `[0, L)`. A ball leaving the boundary point `χ(s)` with unit velocity `u` whose component along
the unit tangent `χ'(s)` is `v ∈ (-1, 1)` travels along a straight chord, hits the boundary again at
`χ(t)` and reflects specularly there. The *next-collision map* (the billiard ball map, lifted to the
strip `ℝ × (-1, 1)`) sends the collision state `(s, v)` to the next one `(t, w)`, where `w` is the
component of the reflected velocity along `χ'(t)`.

This file constructs that map, `TauCeti.StrictConvexBilliardTable.nextCollision`, and proves that it
is well defined:

* the outgoing velocity `u = v χ'(s) + √(1 - v ^ 2) J χ'(s)` is a unit vector pointing into the
  table, `J` being the rotation by a right angle (`outgoingDir`);
* the chord from `χ(s)` in the direction `u` meets the boundary again at exactly one parameter
  `t ∈ (s, s + L)` (`exists_collision`, `eq_nextParam_of_areaForm_eq_zero`), and
  `χ(t) - χ(s) = ‖χ(t) - χ(s)‖ u` (`sub_eq_norm_smul_outgoingDir`);
* the new tangential component `w = ⟪u, χ'(t)⟫` lies in `(-1, 1)`, that is, the chord is never
  tangent to the boundary (`nextTangential_mem_Ioo`);
* the outgoing velocity of the new state is the mirror image of `u` in the tangent line at `χ(t)`
  (`outgoingDir_nextCollision`), which is the law of specular reflection;
* the map commutes with the deck translation `τ(s, v) = (s + L, v)`
  (`nextCollision_add_period`).

The *strict convexity* and *positive orientation* of the table enter through a single hypothesis:
the table lies strictly to the left of each oriented tangent line, meeting it only at its point of
tangency, `0 < ω(χ'(s), χ(t) - χ(s))` whenever `χ(t) ≠ χ(s)`, where `ω` is the area form of the
orientation (`StrictConvexBilliardTable.areaForm_pos`). No smoothness beyond a unit-speed derivative
is assumed here; the smoothness of the map, its inverse and its generating function are separate.

## Main definitions

* `TauCeti.StrictConvexBilliardTable`: an arclength parametrization of the boundary of a strictly
  convex table.
* `TauCeti.StrictConvexBilliardTable.outgoingDir`: the unit velocity of the state `(s, v)`.
* `TauCeti.StrictConvexBilliardTable.nextParam`, `TauCeti.StrictConvexBilliardTable.nextTangential`
  and `TauCeti.StrictConvexBilliardTable.nextCollision`: the next-collision map on the strip.

## References

* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 5.2 (the billiard map of a convex table).
* Serge Tabachnikov, *Geometry and Billiards*, Student Mathematical Library 30, American
  Mathematical Society, 2005, Chapter 3.
-/

public section

noncomputable section

open Function Set Filter Topology Module
open scoped RealInnerProductSpace

namespace TauCeti

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2)]

/-- An arclength parametrization `χ : ℝ → E` of the boundary of a bounded strictly convex table in
the plane `E` oriented by `o`. It is `L`-periodic with `L > 0`, has unit speed, is injective on
`[0, L)`, and the table lies strictly to the left of each oriented tangent line, which it meets only
at the point of tangency: `0 < ω(χ'(s), χ(t) - χ(s))` whenever `χ(t) ≠ χ(s)`. The last condition
combines the strict convexity of the table with the positive orientation of its boundary. -/
structure StrictConvexBilliardTable (o : Orientation ℝ E (Fin 2)) where
  /-- The parametrization of the boundary. -/
  toFun : ℝ → E
  /-- The length `L` of the boundary. -/
  period : ℝ
  period_pos : 0 < period
  periodic : Periodic toFun period
  norm_deriv : ∀ s, ‖deriv toFun s‖ = 1
  injOn : InjOn toFun (Ico 0 period)
  areaForm_pos : ∀ s t, toFun t ≠ toFun s → 0 < o.areaForm (deriv toFun s) (toFun t - toFun s)

namespace StrictConvexBilliardTable

variable {o : Orientation ℝ E (Fin 2)} (χ : StrictConvexBilliardTable o)

instance : CoeFun (StrictConvexBilliardTable o) fun _ ↦ ℝ → E :=
  ⟨toFun⟩

theorem differentiableAt (s : ℝ) : DifferentiableAt ℝ χ s :=
  differentiableAt_of_deriv_ne_zero fun h ↦ by simpa [h] using χ.norm_deriv s

theorem continuous : Continuous χ :=
  continuous_iff_continuousAt.2 fun s ↦ (χ.differentiableAt s).continuousAt

@[simp]
theorem deriv_add_period (s : ℝ) : deriv χ (s + χ.period) = deriv χ s :=
  χ.periodic.deriv s

/-- The parametrization is injective on every half-open interval of length `L`. -/
theorem injOn_Ico (s : ℝ) : InjOn χ (Ico s (s + χ.period)) :=
  χ.periodic.injOn_Ico χ.period_pos χ.injOn s

theorem apply_ne_of_mem_Ioo {s t : ℝ} (ht : t ∈ Ioo s (s + χ.period)) : χ t ≠ χ s := fun h ↦
  ht.1.ne' (χ.injOn_Ico s ⟨ht.1.le, ht.2⟩ ⟨le_rfl, by linarith [χ.period_pos]⟩ h)

/-! ### The outgoing velocity -/

/-- The unit velocity `v χ'(s) + √(1 - v ^ 2) J χ'(s)` of a ball leaving `χ(s)` into the table
with tangential component `v`, where `J` is the rotation by a right angle. -/
def outgoingDir (s v : ℝ) : E :=
  v • deriv χ s + √(1 - v ^ 2) • o.rightAngleRotation (deriv χ s)

theorem outgoingDir_def (s v : ℝ) :
    χ.outgoingDir s v = v • deriv χ s + √(1 - v ^ 2) • o.rightAngleRotation (deriv χ s) :=
  (rfl)

@[simp]
theorem inner_deriv_outgoingDir (s v : ℝ) : ⟪deriv χ s, χ.outgoingDir s v⟫ = v := by
  simp [outgoingDir, inner_add_right, inner_smul_right, χ.norm_deriv _]

@[simp]
theorem areaForm_deriv_outgoingDir (s v : ℝ) :
    o.areaForm (deriv χ s) (χ.outgoingDir s v) = √(1 - v ^ 2) := by
  simp [outgoingDir, χ.norm_deriv _]

theorem norm_outgoingDir {s v : ℝ} (hv : v ∈ Icc (-1) 1) : ‖χ.outgoingDir s v‖ = 1 := by
  have h := o.inner_sq_add_areaForm_sq (deriv χ s) (χ.outgoingDir s v)
  rw [inner_deriv_outgoingDir, areaForm_deriv_outgoingDir, χ.norm_deriv _,
    Real.sq_sqrt (by nlinarith [hv.1, hv.2])] at h
  have : ‖χ.outgoingDir s v‖ ^ 2 = 1 ^ 2 := by linarith
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 this

/-- A collision parameter: a point `χ(t)` on the line through `χ(s)` in the direction `u` is
`χ(s) + ‖χ(t) - χ(s)‖ u`. -/
theorem sub_eq_norm_smul_outgoingDir_of_areaForm_eq_zero {s v t : ℝ} (hv : v ∈ Ioo (-1) 1)
    (h : o.areaForm (χ.outgoingDir s v) (χ t - χ s) = 0) :
    χ t - χ s = ‖χ t - χ s‖ • χ.outgoingDir s v := by
  set u := χ.outgoingDir s v
  have hu : ‖u‖ = 1 := χ.norm_outgoingDir ⟨hv.1.le, hv.2.le⟩
  have hx := o.sq_norm_smul_eq_of_areaForm_eq_zero h
  rw [hu, one_pow, one_smul] at hx
  by_cases h0 : χ t = χ s
  · simp [h0]
  have hpos := χ.areaForm_pos _ _ h0
  rw [hx, map_smul, areaForm_deriv_outgoingDir, smul_eq_mul] at hpos
  have hsqrt : 0 < √(1 - v ^ 2) := Real.sqrt_pos.2 (by nlinarith [hv.1, hv.2])
  have hc : 0 < ⟪u, χ t - χ s⟫ := pos_of_mul_pos_left hpos hsqrt.le
  rw [hx, norm_smul, hu, mul_one, Real.norm_of_nonneg hc.le]

/-! ### Existence and uniqueness of the next collision -/

/-- The chord leaving `χ(s)` with tangential component `v ∈ (-1, 1)` meets the boundary again at a
parameter `t ∈ (s, s + L)`. -/
theorem exists_collision {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    ∃ t ∈ Ioo s (s + χ.period), o.areaForm (χ.outgoingDir s v) (χ t - χ s) = 0 := by
  set u := χ.outgoingDir s v
  set L := χ.period
  have hL : 0 < L := χ.period_pos
  let f : ℝ → ℝ := fun t ↦ o.areaForm u (χ t - χ s)
  have hf : Continuous f :=
    (LinearMap.continuous_of_finiteDimensional (o.areaForm u)).comp
      (χ.continuous.sub continuous_const)
  -- `f` vanishes at `s` and `s + L`, with the negative derivative `ω(u, χ'(s))` at both.
  have hderiv : ∀ a, HasDerivAt f (o.areaForm u (deriv χ a)) a := fun a ↦
    (o.areaForm u).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt a
      ((χ.differentiableAt a).hasDerivAt.sub_const (χ s))
  have hneg : o.areaForm u (deriv χ s) < 0 := by
    rw [o.areaForm_swap, areaForm_deriv_outgoingDir, neg_lt_zero]
    exact Real.sqrt_pos.2 (by nlinarith [hv.1, hv.2])
  have hf_s : f s = 0 := by simp [f]
  have hf_sL : f (s + L) = 0 := by simp [f, L, χ.periodic s]
  have hslope_s := (hasDerivAt_iff_tendsto_slope.1 (hderiv s)).eventually
    (gt_mem_nhds hneg)
  have hslope_sL := (hasDerivAt_iff_tendsto_slope.1
    (hderiv (s + L))).eventually
    (gt_mem_nhds (by rwa [χ.deriv_add_period]))
  obtain ⟨t₁, ht₁, ht₁'⟩ := ((hslope_s.filter_mono (nhdsGT_le_nhdsNE s)).and
    (Ioo_mem_nhdsGT (by linarith : s < s + L / 2))).exists
  obtain ⟨t₂, ht₂, ht₂'⟩ := ((hslope_sL.filter_mono (nhdsLT_le_nhdsNE (s + L))).and
    (Ioo_mem_nhdsLT (by linarith : s + L / 2 < s + L))).exists
  rw [slope_def_field, hf_s, sub_zero] at ht₁
  rw [slope_def_field, hf_sL, sub_zero] at ht₂
  have hft₁ : f t₁ < 0 := by
    by_contra hc
    exact ht₁.not_ge (div_nonneg (not_lt.1 hc) (by linarith [ht₁'.1]))
  have hft₂ : 0 < f t₂ := by
    by_contra hc
    exact ht₂.not_ge (div_nonneg_of_nonpos (not_lt.1 hc) (by linarith [ht₂'.2]))
  obtain ⟨t, ht, hft⟩ := intermediate_value_Ioo (by linarith [ht₁'.2, ht₂'.1])
    hf.continuousOn ⟨hft₁, hft₂⟩
  exact ⟨t, ⟨by linarith [ht.1, ht₁'.1], by linarith [ht.2, ht₂'.2]⟩, hft⟩

/-- The parameter `t ∈ (s, s + L)` of the next collision of the state `(s, v)`, for
`v ∈ (-1, 1)`; it is `s` for other values of `v`. -/
def nextParam (s v : ℝ) : ℝ :=
  open Classical in
  if h : ∃ t ∈ Ioo s (s + χ.period), o.areaForm (χ.outgoingDir s v) (χ t - χ s) = 0 then
    h.choose else s

theorem nextParam_mem_Ioo {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    χ.nextParam s v ∈ Ioo s (s + χ.period) := by
  unfold nextParam
  split_ifs with h
  · exact h.choose_spec.1
  · exact absurd (χ.exists_collision hv) h

theorem areaForm_outgoingDir_sub_nextParam {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    o.areaForm (χ.outgoingDir s v) (χ (χ.nextParam s v) - χ s) = 0 := by
  unfold nextParam
  split_ifs with h
  · exact h.choose_spec.2
  · exact absurd (χ.exists_collision hv) h

/-- The next collision point lies on the ray from `χ(s)` in the outgoing direction. -/
theorem sub_eq_norm_smul_outgoingDir {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    χ (χ.nextParam s v) - χ s = ‖χ (χ.nextParam s v) - χ s‖ • χ.outgoingDir s v :=
  χ.sub_eq_norm_smul_outgoingDir_of_areaForm_eq_zero hv (χ.areaForm_outgoingDir_sub_nextParam hv)

theorem apply_nextParam_ne {s v : ℝ} (hv : v ∈ Ioo (-1) 1) : χ (χ.nextParam s v) ≠ χ s :=
  χ.apply_ne_of_mem_Ioo (χ.nextParam_mem_Ioo hv)

/-- The next collision is unique: a parameter `t ∈ (s, s + L)` whose boundary point lies on the
line through `χ(s)` in the outgoing direction is `nextParam s v`. -/
theorem eq_nextParam_of_areaForm_eq_zero {s v t : ℝ} (hv : v ∈ Ioo (-1) 1)
    (ht : t ∈ Ioo s (s + χ.period)) (h : o.areaForm (χ.outgoingDir s v) (χ t - χ s) = 0) :
    t = χ.nextParam s v := by
  set t' := χ.nextParam s v
  set u := χ.outgoingDir s v
  have ht' : t' ∈ Ioo s (s + χ.period) := χ.nextParam_mem_Ioo hv
  have ea := χ.sub_eq_norm_smul_outgoingDir_of_areaForm_eq_zero hv h
  have eb := χ.sub_eq_norm_smul_outgoingDir (s := s) hv
  set a := ‖χ t - χ s‖
  set b := ‖χ t' - χ s‖
  have ha : 0 < a := norm_pos_iff.2 (sub_ne_zero.2 (χ.apply_ne_of_mem_Ioo ht))
  have hb : 0 < b := norm_pos_iff.2 (sub_ne_zero.2 (χ.apply_ne_of_mem_Ioo ht'))
  -- If the two collision points differ, the nearer one lies strictly between `χ(s)` and the
  -- farther one, which contradicts the strict convexity at the nearer one.
  have key : ∀ {p q : ℝ} {c d : ℝ}, 0 < c → c < d → χ p - χ s = c • u → χ q - χ s = d • u →
      χ p ≠ χ s → χ q ≠ χ p → False := by
    intro p q c d hc hcd hp hq hps hqp
    have h₁ := χ.areaForm_pos _ _ hps.symm
    have h₂ := χ.areaForm_pos _ _ hqp
    have e₁ : χ s - χ p = (-c) • u := by rw [neg_smul, ← hp, neg_sub]
    have e₂ : χ q - χ p = (d - c) • u := by
      rw [sub_smul, ← hp, ← hq]; abel
    rw [e₁, map_smul, smul_eq_mul] at h₁
    rw [e₂, map_smul, smul_eq_mul] at h₂
    nlinarith
  have hmem : ∀ {r : ℝ}, r ∈ Ioo s (s + χ.period) → r ∈ Ico s (s + χ.period) :=
    fun hr ↦ ⟨hr.1.le, hr.2⟩
  by_contra hne
  have hne' : χ t ≠ χ t' := fun e ↦ hne (χ.injOn_Ico s (hmem ht) (hmem ht') e)
  rcases lt_trichotomy a b with hab | hab | hab
  · exact key ha hab ea eb (χ.apply_ne_of_mem_Ioo ht) hne'.symm
  · exact hne' (by rw [← sub_left_inj, ea, eb, hab])
  · exact key hb hab eb ea (χ.apply_ne_of_mem_Ioo ht') hne'

/-! ### The new tangential component and specular reflection -/

/-- The tangential component `⟪u, χ'(t)⟫` at the next collision point `χ(t)` of the velocity `u`
of the state `(s, v)`. Specular reflection preserves it, so it is the tangential component of the
next state. -/
def nextTangential (s v : ℝ) : ℝ :=
  ⟪χ.outgoingDir s v, deriv χ (χ.nextParam s v)⟫

/-- The next tangential component is the inner product of the incoming velocity with the tangent
at the next collision point. -/
theorem nextTangential_def (s v : ℝ) :
    χ.nextTangential s v = ⟪χ.outgoingDir s v, deriv χ (χ.nextParam s v)⟫ :=
  (rfl)

/-- The next-collision map `(s, v) ↦ (t, w)` on the strip `ℝ × (-1, 1)`, defined by the straight
chord and specular reflection. Its values outside the strip carry no meaning. -/
def nextCollision (x : ℝ × ℝ) : ℝ × ℝ :=
  (χ.nextParam x.1 x.2, χ.nextTangential x.1 x.2)

@[simp]
theorem nextCollision_apply (x : ℝ × ℝ) :
    χ.nextCollision x = (χ.nextParam x.1 x.2, χ.nextTangential x.1 x.2) :=
  (rfl)

/-- At the next collision point the velocity points out of the table:
`ω(χ'(t), u) < 0`. -/
theorem areaForm_deriv_nextParam_outgoingDir_neg {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    o.areaForm (deriv χ (χ.nextParam s v)) (χ.outgoingDir s v) < 0 := by
  have h := χ.areaForm_pos _ _ (χ.apply_nextParam_ne (s := s) hv).symm
  have hb : 0 < ‖χ (χ.nextParam s v) - χ s‖ :=
    norm_pos_iff.2 (sub_ne_zero.2 (χ.apply_nextParam_ne hv))
  rw [← neg_sub, χ.sub_eq_norm_smul_outgoingDir hv, ← neg_smul, map_smul, smul_eq_mul] at h
  nlinarith

theorem areaForm_deriv_nextParam_outgoingDir {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    o.areaForm (deriv χ (χ.nextParam s v)) (χ.outgoingDir s v) =
      -√(1 - χ.nextTangential s v ^ 2) := by
  set T := deriv χ (χ.nextParam s v)
  have hneg := χ.areaForm_deriv_nextParam_outgoingDir_neg (s := s) hv
  have h := o.inner_sq_add_areaForm_sq T (χ.outgoingDir s v)
  rw [χ.norm_deriv _, χ.norm_outgoingDir ⟨hv.1.le, hv.2.le⟩, real_inner_comm] at h
  have key : √(1 - χ.nextTangential s v ^ 2) = -o.areaForm T (χ.outgoingDir s v) :=
    (Real.sqrt_eq_iff_mul_self_eq_of_pos (neg_pos.2 hneg)).2 (by rw [nextTangential_def]; nlinarith)
  rw [key, neg_neg]

/-- The chord is never tangent to the boundary at its far end: the next tangential component lies
in `(-1, 1)`. -/
theorem nextTangential_mem_Ioo {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    χ.nextTangential s v ∈ Ioo (-1) 1 := by
  set T := deriv χ (χ.nextParam s v)
  have hneg := χ.areaForm_deriv_nextParam_outgoingDir_neg (s := s) hv
  have h := o.inner_sq_add_areaForm_sq T (χ.outgoingDir s v)
  rw [χ.norm_deriv _, χ.norm_outgoingDir ⟨hv.1.le, hv.2.le⟩, real_inner_comm] at h
  have hw : χ.nextTangential s v ^ 2 < 1 := by
    rw [nextTangential_def]; nlinarith
  constructor <;> nlinarith

/-- The law of specular reflection: the outgoing velocity of the next state is the mirror image of
the incoming velocity `u` in the tangent line at the next collision point. -/
theorem outgoingDir_nextCollision {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    χ.outgoingDir (χ.nextParam s v) (χ.nextTangential s v) =
      (ℝ ∙ deriv χ (χ.nextParam s v)).reflection (χ.outgoingDir s v) := by
  set T := deriv χ (χ.nextParam s v)
  set u := χ.outgoingDir s v
  set w := χ.nextTangential s v
  have hT : ‖T‖ = 1 := χ.norm_deriv _
  -- Decompose `u` in the orthonormal basis `T, J T`.
  have hu : u = w • T + (-√(1 - w ^ 2)) • o.rightAngleRotation T := by
    refine ext_inner_right ℝ fun y ↦ ?_
    have := o.inner_mul_inner_add_areaForm_mul_areaForm T u y
    have hw : ⟪T, u⟫ = w := real_inner_comm _ _
    rw [hT, one_pow, one_mul, hw, areaForm_deriv_nextParam_outgoingDir χ hv] at this
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
      o.inner_rightAngleRotation_left, ← this]
  have hw : ⟪T, u⟫ = w := real_inner_comm _ _
  rw [Submodule.reflection_singleton_apply, outgoingDir, hw]
  conv_rhs => rw [hu]
  simp only [hT, RCLike.ofReal_real_eq_id, id, one_pow, div_one]
  module

/-! ### Equivariance under the deck translation -/

@[simp]
theorem outgoingDir_add_period (s v : ℝ) :
    χ.outgoingDir (s + χ.period) v = χ.outgoingDir s v := by
  rw [outgoingDir, outgoingDir, χ.deriv_add_period]

theorem nextParam_add_period {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    χ.nextParam (s + χ.period) v = χ.nextParam s v + χ.period := by
  have ht := χ.nextParam_mem_Ioo (s := s) hv
  refine (χ.eq_nextParam_of_areaForm_eq_zero hv ⟨by linarith [ht.1], by linarith [ht.2]⟩ ?_).symm
  rw [χ.outgoingDir_add_period, χ.periodic, χ.periodic]
  exact χ.areaForm_outgoingDir_sub_nextParam hv

theorem nextTangential_add_period {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    χ.nextTangential (s + χ.period) v = χ.nextTangential s v := by
  rw [nextTangential_def, nextTangential_def, χ.nextParam_add_period hv, χ.deriv_add_period,
    χ.outgoingDir_add_period]

/-- The next-collision map commutes with the deck translation `τ(s, v) = (s + L, v)`. -/
theorem nextCollision_add_period {x : ℝ × ℝ} (hx : x.2 ∈ Ioo (-1) 1) :
    χ.nextCollision (x.1 + χ.period, x.2) =
      ((χ.nextCollision x).1 + χ.period, (χ.nextCollision x).2) := by
  simp [χ.nextParam_add_period hx, χ.nextTangential_add_period hx]

/-- The next-collision map sends the strip `ℝ × (-1, 1)` to itself. -/
theorem nextCollision_snd_mem_Ioo {x : ℝ × ℝ} (hx : x.2 ∈ Ioo (-1) 1) :
    (χ.nextCollision x).2 ∈ Ioo (-1) 1 :=
  χ.nextTangential_mem_Ioo hx

end StrictConvexBilliardTable

end TauCeti
