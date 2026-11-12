/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import TauCeti.Dynamics.Billiard.NextCollision
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Smoothness of the billiard next-collision map

Let `χ` be an arclength parametrization of the boundary of a strictly convex billiard table
(`TauCeti.StrictConvexBilliardTable`) and let `(s, v) ↦ (t, w)` be its next-collision map on the
strip `ℝ × (-1, 1)` (`TauCeti.StrictConvexBilliardTable.nextCollision`). This file proves that the
next-collision map is as smooth as the unit tangent `χ'`: if `χ` is `C^(n + 1)` with `n ≠ 0`, the
map is `C^n` on the strip (`TauCeti.StrictConvexBilliardTable.contDiffOn_nextCollision`).

The parameter `t` of the next collision is the solution in `(s, s + L)` of the chord equation

`F((s, v), t) = ω(u(s, v), χ(t) - χ(s)) = 0`,

where `u(s, v) = v χ'(s) + √(1 - v ^ 2) J χ'(s)` is the outgoing velocity and `ω` the area form.
The equation `F` is `C^n` on the strip, and its derivative in `t` at the next collision is
`ω(u, χ'(t)) = √(1 - w ^ 2) > 0`, positive because the chord is not tangent to the boundary at its
far end. The implicit function theorem therefore solves `F = 0` for `t` by a `C^n` function near
each state, and the uniqueness of the next collision identifies that solution with `t`. The new
tangential component `w = ⟪u, χ'(t)⟫` is then `C^n` as well.

Differentiating the chord equation in `v` computes the rate at which the next collision moves as the
ball is aimed further forward:

`∂t/∂v = -ℓ / (√(1 - v ^ 2) √(1 - w ^ 2))`, where `ℓ = ‖χ(t) - χ(s)‖` is the chord length

(`TauCeti.StrictConvexBilliardTable.hasDerivAt_nextParam`). In particular `∂t/∂v < 0`, so for a
fixed starting point the next collision parameter is strictly decreasing in `v`
(`TauCeti.StrictConvexBilliardTable.strictAntiOn_nextParam`). These two statements only need a
`C²` table.

## Main results

* `TauCeti.StrictConvexBilliardTable.contDiffAt_uncurry_nextParam`,
  `TauCeti.StrictConvexBilliardTable.contDiffAt_uncurry_nextTangential`: the two components of the
  next-collision map are `C^n` at every state of the strip for a `C^(n + 1)` table.
* `TauCeti.StrictConvexBilliardTable.contDiffAt_nextCollision`,
  `TauCeti.StrictConvexBilliardTable.contDiffOn_nextCollision`: the next-collision map is `C^n`
  on the strip.
* `TauCeti.StrictConvexBilliardTable.hasDerivAt_nextParam`: the derivative `∂t/∂v`.
* `TauCeti.StrictConvexBilliardTable.strictAntiOn_nextParam`: `t` is strictly decreasing in `v`.

## References

* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 5.2 (the billiard map of a convex table).
* Serge Tabachnikov, *Geometry and Billiards*, Student Mathematical Library 30, American
  Mathematical Society, 2005, Chapter 3.
-/

public section

noncomputable section

open Function Set Filter Topology Module
open scoped RealInnerProductSpace ContDiff

namespace TauCeti

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2)]

namespace StrictConvexBilliardTable

variable {o : Orientation ℝ E (Fin 2)} (χ : StrictConvexBilliardTable o) {n : WithTop ℕ∞}

/-- The outgoing velocity `u(s, v)` is `C^n` at a state `(s, v)` of the strip when the unit tangent
`χ'` is `C^n` at `s`. -/
theorem contDiffAt_uncurry_outgoingDir {x : ℝ × ℝ} (hχ : ContDiffAt ℝ n (deriv χ) x.1)
    (hx : x.2 ∈ Ioo (-1) 1) : ContDiffAt ℝ n (uncurry χ.outgoingDir) x := by
  have he : uncurry χ.outgoingDir = fun y : ℝ × ℝ ↦
      y.2 • deriv χ y.1 + √(1 - y.2 ^ 2) • o.rightAngleRotation (deriv χ y.1) :=
    funext fun y ↦ χ.outgoingDir_def y.1 y.2
  have hd : ContDiffAt ℝ n (fun y : ℝ × ℝ ↦ deriv χ y.1) x := hχ.comp x contDiffAt_fst
  have hsq : ContDiffAt ℝ n (fun y : ℝ × ℝ ↦ √(1 - y.2 ^ 2)) x :=
    (contDiffAt_const.sub (contDiffAt_snd.pow 2)).sqrt (by nlinarith [hx.1, hx.2])
  rw [he]
  exact (contDiffAt_snd.smul hd).add
    (hsq.smul (o.rightAngleRotation.contDiff.contDiffAt.comp x hd))

/-! ### The chord equation -/

/-- The chord equation `F((s, v), t) = ω(u(s, v), χ(t) - χ(s))`, which vanishes exactly when
`χ(t)` lies on the line through `χ(s)` in the outgoing direction of the state `(s, v)`. -/
private def chordEquation (p : (ℝ × ℝ) × ℝ) : ℝ :=
  o.areaForm (χ.outgoingDir p.1.1 p.1.2) (χ p.2 - χ p.1.1)

private theorem contDiffAt_chordEquation (hχ : ContDiff ℝ (n + 1) χ) {p : (ℝ × ℝ) × ℝ}
    (hp : p.1.2 ∈ Ioo (-1) 1) : ContDiffAt ℝ n χ.chordEquation p := by
  have hχn : ContDiff ℝ n χ := hχ.of_succ
  have he : χ.chordEquation = fun p : (ℝ × ℝ) × ℝ ↦
      ⟪o.rightAngleRotation (uncurry χ.outgoingDir p.1), χ p.2 - χ p.1.1⟫ :=
    funext fun p ↦ (o.inner_rightAngleRotation_left _ _).symm
  rw [he]
  refine ContDiffAt.inner ℝ (o.rightAngleRotation.contDiff.contDiffAt.comp p
    ((χ.contDiffAt_uncurry_outgoingDir (contDiff_succ_iff_deriv.1 hχ).2.2.contDiffAt hp).comp p
      contDiffAt_fst)) ?_
  exact (hχn.contDiffAt.comp p contDiffAt_snd).sub
    (hχn.contDiffAt.comp p (contDiffAt_fst.comp p contDiffAt_fst))

/-- The derivative of the chord equation in the collision parameter `t`. -/
private theorem hasDerivAt_chordEquation_snd (x : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (fun t' ↦ χ.chordEquation (x, t'))
      (o.areaForm (χ.outgoingDir x.1 x.2) (deriv χ t)) t :=
  (o.areaForm (χ.outgoingDir x.1 x.2)).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    ((χ.differentiableAt t).hasDerivAt.sub_const (χ x.1))

/-- The derivative of the chord equation in the tangential component `v`. -/
private theorem hasDerivAt_chordEquation_fst_snd {s v : ℝ} (hv : v ∈ Ioo (-1) 1) (t : ℝ) :
    HasDerivAt (fun v' ↦ χ.chordEquation ((s, v'), t))
      (o.areaForm (deriv χ s) (χ t - χ s) -
        v / √(1 - v ^ 2) * o.areaForm (o.rightAngleRotation (deriv χ s)) (χ t - χ s)) v := by
  set A := o.areaForm (deriv χ s) (χ t - χ s)
  set B := o.areaForm (o.rightAngleRotation (deriv χ s)) (χ t - χ s)
  have he : (fun v' ↦ χ.chordEquation ((s, v'), t)) = fun v' ↦ v' * A + √(1 - v' ^ 2) * B := by
    funext v'
    simp [chordEquation, outgoingDir_def, A, B]
  have hne : 1 - v ^ 2 ≠ 0 := by nlinarith [hv.1, hv.2]
  have hpoly : HasDerivAt (fun y : ℝ ↦ 1 - y ^ 2) (-(2 * v)) v := by
    simpa using (hasDerivAt_pow 2 v).const_sub 1
  rw [he]
  refine (((hasDerivAt_id v).mul_const A).add ((hpoly.sqrt hne).mul_const B)).congr_deriv ?_
  field_simp
  ring

private theorem areaForm_outgoingDir_deriv_nextParam {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    o.areaForm (χ.outgoingDir s v) (deriv χ (χ.nextParam s v)) =
      √(1 - χ.nextTangential s v ^ 2) := by
  rw [o.areaForm_swap, χ.areaForm_deriv_nextParam_outgoingDir hv, neg_neg]

private theorem areaForm_outgoingDir_deriv_nextParam_ne_zero {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    o.areaForm (χ.outgoingDir s v) (deriv χ (χ.nextParam s v)) ≠ 0 := by
  rw [o.areaForm_swap, neg_ne_zero]
  exact (χ.areaForm_deriv_nextParam_outgoingDir_neg hv).ne

private theorem fderiv_chordEquation_comp_inr (hχ : ContDiff ℝ (n + 1) χ) (hn : n ≠ 0)
    {x : ℝ × ℝ} (hx : x.2 ∈ Ioo (-1) 1) (t : ℝ) :
    fderiv ℝ χ.chordEquation (x, t) ∘L .inr ℝ (ℝ × ℝ) ℝ =
      (1 : ℝ →L[ℝ] ℝ).smulRight (o.areaForm (χ.outgoingDir x.1 x.2) (deriv χ t)) := by
  have hdiff : DifferentiableAt ℝ χ.chordEquation (x, t) :=
    (χ.contDiffAt_chordEquation hχ (p := (x, t)) hx).differentiableAt hn
  have h₁ := hdiff.hasFDerivAt.comp t (hasFDerivAt_prodMk_right x t)
  exact h₁.unique (hasDerivAt_iff_hasFDerivAt.mp (χ.hasDerivAt_chordEquation_snd x t))

/-- At the next collision, the chord equation has invertible derivative in `t`. -/
private theorem isInvertible_fderiv_chordEquation (hχ : ContDiff ℝ (n + 1) χ) (hn : n ≠ 0)
    {x : ℝ × ℝ} (hx : x.2 ∈ Ioo (-1) 1) :
    (fderiv ℝ χ.chordEquation (x, uncurry χ.nextParam x) ∘L
      .inr ℝ (ℝ × ℝ) ℝ).IsInvertible := by
  rw [χ.fderiv_chordEquation_comp_inr hχ hn hx]
  refine ⟨ContinuousLinearEquiv.unitsEquivAut ℝ
    (Units.mk0 _ (χ.areaForm_outgoingDir_deriv_nextParam_ne_zero (s := x.1) hx)), ?_⟩
  ext
  simp [uncurry]

/-- Near every state of the strip, the next collision parameter agrees with a `C^n` solution of the
chord equation, the implicit function of `F` at the next collision. -/
private theorem exists_contDiffAt_eventuallyEq_uncurry_nextParam (hχ : ContDiff ℝ (n + 1) χ)
    (hn : n ≠ 0) {x : ℝ × ℝ} (hx : x.2 ∈ Ioo (-1) 1) :
    ∃ ψ : ℝ × ℝ → ℝ, ContDiffAt ℝ n ψ x ∧ uncurry χ.nextParam =ᶠ[𝓝 x] ψ := by
  have hF : ContDiffAt ℝ n χ.chordEquation (x, uncurry χ.nextParam x) :=
    χ.contDiffAt_chordEquation hχ hx
  have hinv := χ.isInvertible_fderiv_chordEquation hχ hn hx
  set ψ := hF.implicitFunction hn hinv
  have hψ : ContDiffAt ℝ n ψ x := hF.contDiffAt_implicitFunction hn hinv
  have hψx : ψ x = χ.nextParam x.1 x.2 := hF.implicitFunction_apply_self hn hinv
  have hmem := χ.nextParam_mem_Ioo (s := x.1) hx
  have h₁ : ∀ᶠ y in 𝓝 x, ψ y - y.1 ∈ Ioo 0 χ.period :=
    (hψ.continuousAt.sub continuousAt_fst).eventually_mem (isOpen_Ioo.mem_nhds
      (by rw [Pi.sub_apply, hψx]; exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩))
  have h₂ : ∀ᶠ y in 𝓝 x, y.2 ∈ Ioo (-1) 1 :=
    continuousAt_snd.eventually_mem (isOpen_Ioo.mem_nhds hx)
  have hzero : χ.chordEquation (x, uncurry χ.nextParam x) = 0 :=
    χ.areaForm_outgoingDir_sub_nextParam hx
  refine ⟨ψ, hψ, ?_⟩
  filter_upwards [h₁, h₂, hF.eventually_apply_implicitFunction hn hinv] with y hy₁ hy₂ hy₃
  rw [hzero] at hy₃
  exact (χ.eq_nextParam_of_areaForm_eq_zero hy₂
    ⟨by linarith [hy₁.1], by linarith [hy₁.2]⟩ hy₃).symm

/-! ### Smoothness of the next-collision map -/

/-- The parameter `t` of the next collision is `C^n` in the state `(s, v)` on the strip
`ℝ × (-1, 1)`, for a `C^(n + 1)` table and `n ≠ 0`. -/
theorem contDiffAt_uncurry_nextParam (hχ : ContDiff ℝ (n + 1) χ) (hn : n ≠ 0) {x : ℝ × ℝ}
    (hx : x.2 ∈ Ioo (-1) 1) : ContDiffAt ℝ n (uncurry χ.nextParam) x := by
  obtain ⟨ψ, hψ, he⟩ := χ.exists_contDiffAt_eventuallyEq_uncurry_nextParam hχ hn hx
  exact hψ.congr_of_eventuallyEq he

/-- The new tangential component `w` of the next collision is `C^n` in the state `(s, v)` on the
strip `ℝ × (-1, 1)`, for a `C^(n + 1)` table and `n ≠ 0`. -/
theorem contDiffAt_uncurry_nextTangential (hχ : ContDiff ℝ (n + 1) χ) (hn : n ≠ 0)
    {x : ℝ × ℝ} (hx : x.2 ∈ Ioo (-1) 1) : ContDiffAt ℝ n (uncurry χ.nextTangential) x := by
  have he : uncurry χ.nextTangential = fun y : ℝ × ℝ ↦
      ⟪uncurry χ.outgoingDir y, deriv χ (uncurry χ.nextParam y)⟫ :=
    funext fun y ↦ χ.nextTangential_def y.1 y.2
  have hd := (contDiff_succ_iff_deriv.1 hχ).2.2
  rw [he]
  exact (χ.contDiffAt_uncurry_outgoingDir hd.contDiffAt hx).inner ℝ
    (hd.contDiffAt.comp x (χ.contDiffAt_uncurry_nextParam hχ hn hx))

/-- The next-collision map is `C^n` at every state of the strip `ℝ × (-1, 1)`, for a `C^(n + 1)`
table and `n ≠ 0`. -/
theorem contDiffAt_nextCollision (hχ : ContDiff ℝ (n + 1) χ) (hn : n ≠ 0) {x : ℝ × ℝ}
    (hx : x.2 ∈ Ioo (-1) 1) : ContDiffAt ℝ n χ.nextCollision x := by
  have he : χ.nextCollision = fun y ↦ (uncurry χ.nextParam y, uncurry χ.nextTangential y) :=
    funext χ.nextCollision_apply
  rw [he]
  exact (χ.contDiffAt_uncurry_nextParam hχ hn hx).prodMk
    (χ.contDiffAt_uncurry_nextTangential hχ hn hx)

/-- **Smoothness of the billiard map.** The next-collision map of a `C^(n + 1)` strictly convex
table is `C^n` on the strip `ℝ × (-1, 1)`, for `n ≠ 0`. -/
theorem contDiffOn_nextCollision (hχ : ContDiff ℝ (n + 1) χ) (hn : n ≠ 0) :
    ContDiffOn ℝ n χ.nextCollision (univ ×ˢ Ioo (-1) 1) :=
  fun _ hx ↦ (χ.contDiffAt_nextCollision hχ hn hx.2).contDiffWithinAt

/-! ### The twist of the billiard map -/

/-- The partial derivative `∂_v F = ℓ / √(1 - v ^ 2)` of the chord equation at the next collision,
where `ℓ` is the length of the chord. -/
private theorem fderiv_chordEquation_apply_inl_inr (hχ : ContDiff ℝ (1 + 1) χ) {s v : ℝ}
    (hv : v ∈ Ioo (-1) 1) :
    fderiv ℝ χ.chordEquation ((s, v), χ.nextParam s v) (((0 : ℝ), (1 : ℝ)), (0 : ℝ)) =
      ‖χ (χ.nextParam s v) - χ s‖ / √(1 - v ^ 2) := by
  set t := χ.nextParam s v
  set ℓ := ‖χ t - χ s‖
  have hD := ((χ.contDiffAt_chordEquation hχ (p := ((s, v), t)) hv).differentiableAt
    one_ne_zero).hasFDerivAt
  have hc := hD.comp_hasDerivAt v
    (((hasDerivAt_const v s).prodMk (hasDerivAt_id v)).prodMk (hasDerivAt_const v t))
  have h := hc.unique (χ.hasDerivAt_chordEquation_fst_snd (s := s) hv t)
  have hsq : √(1 - v ^ 2) ^ 2 = 1 - v ^ 2 := Real.sq_sqrt (by nlinarith [hv.1, hv.2])
  have hsq₀ : √(1 - v ^ 2) ≠ 0 := (Real.sqrt_pos.2 (by nlinarith [hv.1, hv.2])).ne'
  rw [h, χ.sub_eq_norm_smul_outgoingDir hv, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
    areaForm_deriv_outgoingDir, o.areaForm_rightAngleRotation_left, inner_deriv_outgoingDir]
  field_simp
  linear_combination ℓ * hsq

/-- The partial derivative `∂_t F = √(1 - w ^ 2)` of the chord equation at the next collision,
where `w` is the new tangential component. -/
private theorem fderiv_chordEquation_apply_inr (hχ : ContDiff ℝ (1 + 1) χ) {s v : ℝ}
    (hv : v ∈ Ioo (-1) 1) :
    fderiv ℝ χ.chordEquation ((s, v), χ.nextParam s v) ((0 : ℝ × ℝ), (1 : ℝ)) =
      √(1 - χ.nextTangential s v ^ 2) := by
  set t := χ.nextParam s v
  have hD := ((χ.contDiffAt_chordEquation hχ (p := ((s, v), t)) hv).differentiableAt
    one_ne_zero).hasFDerivAt
  have h := (hD.comp_hasDerivAt t ((hasDerivAt_const t (s, v)).prodMk (hasDerivAt_id t))).unique
    (χ.hasDerivAt_chordEquation_snd (s, v) t)
  rw [h]
  exact χ.areaForm_outgoingDir_deriv_nextParam hv

/-- **The twist of the billiard map.** For a `C²` table, the parameter `t` of the next collision of
`(s, v)` has derivative `∂t/∂v = -ℓ / (√(1 - v ^ 2) √(1 - w ^ 2))` in `v`, where
`ℓ = ‖χ(t) - χ(s)‖` is the length of the chord and `w` the new tangential component. -/
theorem hasDerivAt_nextParam (hχ : ContDiff ℝ 2 χ) {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    HasDerivAt (χ.nextParam s)
      (-(‖χ (χ.nextParam s v) - χ s‖ /
        (√(1 - v ^ 2) * √(1 - χ.nextTangential s v ^ 2)))) v := by
  have hχ' : ContDiff ℝ (1 + 1) χ := by simpa [one_add_one_eq_two] using hχ
  set ℓ := ‖χ (χ.nextParam s v) - χ s‖
  set w := χ.nextTangential s v
  have hline : HasDerivAt (fun v' : ℝ ↦ (s, v')) ((0 : ℝ), (1 : ℝ)) v :=
    (hasDerivAt_const v s).prodMk (hasDerivAt_id v)
  have hdt : DifferentiableAt ℝ (χ.nextParam s) v :=
    ((χ.contDiffAt_uncurry_nextParam hχ' one_ne_zero (x := (s, v)) hv).differentiableAt
      one_ne_zero).comp v hline.differentiableAt
  set t' := deriv (χ.nextParam s) v
  -- Differentiating `F((s, v'), t(v')) = 0` in `v'` gives `∂_v F + t' ∂_t F = 0`.
  have hD := ((χ.contDiffAt_chordEquation hχ' (p := ((s, v), χ.nextParam s v)) hv).differentiableAt
    one_ne_zero).hasFDerivAt
  have hchain := hD.comp_hasDerivAt v (hline.prodMk hdt.hasDerivAt)
  have hzero : HasDerivAt (fun v' ↦ χ.chordEquation ((s, v'), χ.nextParam s v')) 0 v :=
    (hasDerivAt_const v (0 : ℝ)).congr_of_eventuallyEq <| by
      filter_upwards [isOpen_Ioo.mem_nhds hv] with v' hv'
      exact χ.areaForm_outgoingDir_sub_nextParam hv'
  have hsplit : (((0 : ℝ), (1 : ℝ)), t') = (((0 : ℝ), (1 : ℝ)), (0 : ℝ)) +
      t' • ((0 : ℝ × ℝ), (1 : ℝ)) := by
    ext <;> simp
  have hsum : ℓ / √(1 - v ^ 2) + t' * √(1 - w ^ 2) = 0 := by
    have h := hchain.unique hzero
    rw [hsplit, map_add, map_smul, χ.fderiv_chordEquation_apply_inl_inr hχ' hv,
      χ.fderiv_chordEquation_apply_inr hχ' hv, smul_eq_mul] at h
    exact h
  have hw₀ : √(1 - w ^ 2) ≠ 0 := by
    have hw := χ.nextTangential_mem_Ioo (s := s) hv
    exact (Real.sqrt_pos.2 (by nlinarith [hw.1, hw.2])).ne'
  have ht' : t' = -(ℓ / √(1 - v ^ 2)) / √(1 - w ^ 2) := by
    rw [eq_div_iff hw₀]
    linarith
  convert hdt.hasDerivAt using 1
  rw [show -(ℓ / (√(1 - v ^ 2) * √(1 - w ^ 2))) = -(ℓ / √(1 - v ^ 2)) / √(1 - w ^ 2) by ring]
  exact ht'.symm

/-- For a `C²` table and a fixed starting point `χ(s)`, the parameter of the next collision is
strictly decreasing in the tangential component `v ∈ (-1, 1)`: aiming further forward moves the
next collision point backward along the boundary, towards `χ(s)`. -/
theorem strictAntiOn_nextParam (hχ : ContDiff ℝ 2 χ) (s : ℝ) :
    StrictAntiOn (χ.nextParam s) (Ioo (-1) 1) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioo _ _)
    (fun v hv ↦ (χ.hasDerivAt_nextParam hχ hv).continuousAt.continuousWithinAt) fun v hv ↦ ?_
  rw [interior_Ioo] at hv
  rw [(χ.hasDerivAt_nextParam hχ hv).deriv, neg_neg_iff_pos]
  have hw := χ.nextTangential_mem_Ioo (s := s) hv
  have hℓ : 0 < ‖χ (χ.nextParam s v) - χ s‖ :=
    norm_pos_iff.2 (sub_ne_zero.2 (χ.apply_nextParam_ne hv))
  exact div_pos hℓ (mul_pos (Real.sqrt_pos.2 (by nlinarith [hv.1, hv.2]))
    (Real.sqrt_pos.2 (by nlinarith [hw.1, hw.2])))

end StrictConvexBilliardTable

end TauCeti
