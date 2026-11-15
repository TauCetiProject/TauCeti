/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import TauCeti.Dynamics.Billiard.NextCollision
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
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
tangential component `w = ⟪u, χ'(t)⟫` is then `C^n` as well. These statements are pointwise: at a
state `(s, v)` they only need `χ` to be `C^(n + 1)` at `s` and at `t`.

For a fixed starting point `χ(s)`, the cotangent `⟪χ'(s), χ(t) - χ(s)⟫ / ω(χ'(s), χ(t) - χ(s))` of
the chord angle is strictly decreasing in `t ∈ (s, s + L)` and equals `v / √(1 - v ^ 2)` at the
next collision. Inverting it computes the rate at which the next collision moves as the ball is
aimed further forward:

`∂t/∂v = -ℓ / (√(1 - v ^ 2) √(1 - w ^ 2))`, where `ℓ = ‖χ(t) - χ(s)‖` is the chord length

(`TauCeti.StrictConvexBilliardTable.hasDerivAt_nextParam`). In particular `∂t/∂v < 0`
(`TauCeti.StrictConvexBilliardTable.deriv_nextParam_neg`), so for a fixed starting point the next
collision parameter is strictly decreasing in `v`
(`TauCeti.StrictConvexBilliardTable.strictAntiOn_nextParam`). These statements need no smoothness
of the table beyond the differentiability of its arclength parametrization.

## Main results

* `TauCeti.StrictConvexBilliardTable.contDiffAt_uncurry_nextParam`,
  `TauCeti.StrictConvexBilliardTable.contDiffAt_uncurry_nextTangential`: the two components of the
  next-collision map are `C^n` at a state of the strip where the table is `C^(n + 1)`.
* `TauCeti.StrictConvexBilliardTable.contDiffAt_nextCollision`,
  `TauCeti.StrictConvexBilliardTable.contDiffOn_nextCollision`: the next-collision map is `C^n`
  on the strip.
* `TauCeti.StrictConvexBilliardTable.hasDerivAt_nextParam`,
  `TauCeti.StrictConvexBilliardTable.deriv_nextParam_neg`: the derivative `∂t/∂v`, which is
  negative.
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

private theorem one_sub_sq_pos {v : ℝ} (hv : v ∈ Ioo (-1) 1) : 0 < 1 - v ^ 2 := by
  nlinarith [hv.1, hv.2]

private theorem sqrt_one_sub_sq_pos {v : ℝ} (hv : v ∈ Ioo (-1) 1) : 0 < √(1 - v ^ 2) :=
  Real.sqrt_pos.2 (one_sub_sq_pos hv)

/-- One half of `continuousAt_of_strictMonoOn_comp`: if `g` is strictly increasing on a
neighbourhood `S` of `f x`, `f` maps a neighbourhood of `x` into `S` and `g ∘ f` is continuous at
`x`, then `f` stays above every `b < f x` near `x`. -/
private theorem eventually_lt_of_strictMonoOn_comp {X α β : Type*} [TopologicalSpace X]
    [LinearOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]
    [LinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {f : X → α} {g : α → β} {S : Set α} {x : X} (hg : StrictMonoOn g S) (hS : S ∈ 𝓝 (f x))
    (hf : ∀ᶠ y in 𝓝 x, f y ∈ S) (hgf : ContinuousAt (g ∘ f) x) {b : α} (hb : b < f x) :
    ∀ᶠ y in 𝓝 x, b < f y := by
  obtain ⟨l, hl, hlS⟩ := exists_Ioc_subset_of_mem_nhds hS ⟨b, hb⟩
  obtain ⟨τ, hτ₁, hτ₂⟩ := exists_between (max_lt hl hb)
  have hτS : τ ∈ S := hlS ⟨(le_max_left _ _).trans_lt hτ₁, hτ₂.le⟩
  filter_upwards [hf, hgf.eventually (lt_mem_nhds (hg hτS (mem_of_mem_nhds hS) hτ₂))]
    with y hy hgy
  exact ((le_max_right _ _).trans_lt hτ₁).trans ((hg.lt_iff_lt hτS hy).1 hgy)

/-- If `g` is strictly increasing on a neighbourhood `S` of `f x`, `f` maps a neighbourhood of `x`
into `S` and `g ∘ f` is continuous at `x`, then `f` is continuous at `x`. -/
private theorem continuousAt_of_strictMonoOn_comp {X α β : Type*} [TopologicalSpace X]
    [LinearOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]
    [LinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {f : X → α} {g : α → β} {S : Set α} {x : X} (hg : StrictMonoOn g S) (hS : S ∈ 𝓝 (f x))
    (hf : ∀ᶠ y in 𝓝 x, f y ∈ S) (hgf : ContinuousAt (g ∘ f) x) : ContinuousAt f x :=
  tendsto_order.2 ⟨fun _ hb ↦ eventually_lt_of_strictMonoOn_comp hg hS hf hgf hb,
    fun _ hb ↦ eventually_lt_of_strictMonoOn_comp (α := αᵒᵈ) (β := βᵒᵈ) hg.dual hS hf hgf hb⟩

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
    (contDiffAt_const.sub (contDiffAt_snd.pow 2)).sqrt (one_sub_sq_pos hx).ne'
  rw [he]
  exact (contDiffAt_snd.smul hd).add
    (hsq.smul (o.rightAngleRotation.contDiff.contDiffAt.comp x hd))

/-! ### The chord equation -/

/-- The chord equation `F((s, v), t) = ω(u(s, v), χ(t) - χ(s))`, which vanishes exactly when
`χ(t)` lies on the line through `χ(s)` in the outgoing direction of the state `(s, v)`. -/
private def chordEquation (p : (ℝ × ℝ) × ℝ) : ℝ :=
  o.areaForm (χ.outgoingDir p.1.1 p.1.2) (χ p.2 - χ p.1.1)

private theorem contDiffAt_chordEquation {p : (ℝ × ℝ) × ℝ} (hχ₁ : ContDiffAt ℝ (n + 1) χ p.1.1)
    (hχ₂ : ContDiffAt ℝ n χ p.2) (hp : p.1.2 ∈ Ioo (-1) 1) :
    ContDiffAt ℝ n χ.chordEquation p := by
  have he : χ.chordEquation = fun p : (ℝ × ℝ) × ℝ ↦
      ⟪o.rightAngleRotation (uncurry χ.outgoingDir p.1), χ p.2 - χ p.1.1⟫ :=
    funext fun p ↦ (o.inner_rightAngleRotation_left _ _).symm
  rw [he]
  refine ContDiffAt.inner ℝ (o.rightAngleRotation.contDiff.contDiffAt.comp p
    ((χ.contDiffAt_uncurry_outgoingDir (hχ₁.derivWithin le_rfl) hp).comp p
      contDiffAt_fst)) ?_
  exact (hχ₂.comp p contDiffAt_snd).sub
    ((hχ₁.of_le le_self_add).comp p (contDiffAt_fst.comp p contDiffAt_fst))

/-- The derivative of the chord equation in the collision parameter `t`. -/
private theorem hasDerivAt_chordEquation_snd (x : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (fun t' ↦ χ.chordEquation (x, t'))
      (o.areaForm (χ.outgoingDir x.1 x.2) (deriv χ t)) t :=
  (o.areaForm (χ.outgoingDir x.1 x.2)).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
    ((χ.differentiableAt t).hasDerivAt.sub_const (χ x.1))

private theorem areaForm_outgoingDir_deriv_nextParam_ne_zero {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    o.areaForm (χ.outgoingDir s v) (deriv χ (χ.nextParam s v)) ≠ 0 := by
  rw [o.areaForm_swap, neg_ne_zero]
  exact (χ.areaForm_deriv_nextParam_outgoingDir_neg hv).ne

private theorem fderiv_chordEquation_comp_inr {x : ℝ × ℝ} {t : ℝ}
    (hχ₁ : ContDiffAt ℝ (n + 1) χ x.1) (hχ₂ : ContDiffAt ℝ n χ t) (hn : n ≠ 0)
    (hx : x.2 ∈ Ioo (-1) 1) :
    fderiv ℝ χ.chordEquation (x, t) ∘L .inr ℝ (ℝ × ℝ) ℝ =
      (1 : ℝ →L[ℝ] ℝ).smulRight (o.areaForm (χ.outgoingDir x.1 x.2) (deriv χ t)) := by
  have hdiff : DifferentiableAt ℝ χ.chordEquation (x, t) :=
    (χ.contDiffAt_chordEquation (p := (x, t)) hχ₁ hχ₂ hx).differentiableAt hn
  have h₁ := hdiff.hasFDerivAt.comp t (hasFDerivAt_prodMk_right x t)
  exact h₁.unique (hasDerivAt_iff_hasFDerivAt.mp (χ.hasDerivAt_chordEquation_snd x t))

/-- At the next collision, the chord equation has invertible derivative in `t`. -/
private theorem isInvertible_fderiv_chordEquation {x : ℝ × ℝ}
    (hχ₁ : ContDiffAt ℝ (n + 1) χ x.1) (hχ₂ : ContDiffAt ℝ n χ (χ.nextParam x.1 x.2))
    (hn : n ≠ 0) (hx : x.2 ∈ Ioo (-1) 1) :
    (fderiv ℝ χ.chordEquation (x, uncurry χ.nextParam x) ∘L
      .inr ℝ (ℝ × ℝ) ℝ).IsInvertible := by
  rw [χ.fderiv_chordEquation_comp_inr (t := uncurry χ.nextParam x) hχ₁ hχ₂ hn hx]
  refine ⟨ContinuousLinearEquiv.unitsEquivAut ℝ
    (Units.mk0 _ (χ.areaForm_outgoingDir_deriv_nextParam_ne_zero (s := x.1) hx)), ?_⟩
  ext
  simp [uncurry]

/-- Near every state of the strip, the next collision parameter agrees with a `C^n` solution of the
chord equation, the implicit function of `F` at the next collision. -/
private theorem exists_contDiffAt_eventuallyEq_uncurry_nextParam {x : ℝ × ℝ}
    (hχ₁ : ContDiffAt ℝ (n + 1) χ x.1) (hχ₂ : ContDiffAt ℝ n χ (χ.nextParam x.1 x.2))
    (hn : n ≠ 0) (hx : x.2 ∈ Ioo (-1) 1) :
    ∃ ψ : ℝ × ℝ → ℝ, ContDiffAt ℝ n ψ x ∧ uncurry χ.nextParam =ᶠ[𝓝 x] ψ := by
  have hF : ContDiffAt ℝ n χ.chordEquation (x, uncurry χ.nextParam x) :=
    χ.contDiffAt_chordEquation hχ₁ hχ₂ hx
  have hinv := χ.isInvertible_fderiv_chordEquation hχ₁ hχ₂ hn hx
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

/-- The parameter `t` of the next collision is `C^n` at a state `(s, v)` of the strip
`ℝ × (-1, 1)`, for `n ≠ 0`, when the table is `C^(n + 1)` at `s` and `C^n` at `t`. -/
theorem contDiffAt_uncurry_nextParam {x : ℝ × ℝ} (hχ₁ : ContDiffAt ℝ (n + 1) χ x.1)
    (hχ₂ : ContDiffAt ℝ n χ (χ.nextParam x.1 x.2)) (hn : n ≠ 0) (hx : x.2 ∈ Ioo (-1) 1) :
    ContDiffAt ℝ n (uncurry χ.nextParam) x := by
  obtain ⟨ψ, hψ, he⟩ := χ.exists_contDiffAt_eventuallyEq_uncurry_nextParam hχ₁ hχ₂ hn hx
  exact hψ.congr_of_eventuallyEq he

/-- The new tangential component `w` of the next collision is `C^n` at a state `(s, v)` of the
strip `ℝ × (-1, 1)`, for `n ≠ 0`, when the table is `C^(n + 1)` at both `s` and `t`. -/
theorem contDiffAt_uncurry_nextTangential {x : ℝ × ℝ} (hχ₁ : ContDiffAt ℝ (n + 1) χ x.1)
    (hχ₂ : ContDiffAt ℝ (n + 1) χ (χ.nextParam x.1 x.2)) (hn : n ≠ 0)
    (hx : x.2 ∈ Ioo (-1) 1) : ContDiffAt ℝ n (uncurry χ.nextTangential) x := by
  have he : uncurry χ.nextTangential = fun y : ℝ × ℝ ↦
      ⟪uncurry χ.outgoingDir y, deriv χ (uncurry χ.nextParam y)⟫ :=
    funext fun y ↦ χ.nextTangential_def y.1 y.2
  rw [he]
  exact (χ.contDiffAt_uncurry_outgoingDir (hχ₁.derivWithin le_rfl) hx).inner ℝ
    (ContDiffAt.comp (g := deriv χ) x (hχ₂.derivWithin le_rfl)
      (χ.contDiffAt_uncurry_nextParam hχ₁ (hχ₂.of_le le_self_add) hn hx))

/-- The next-collision map is `C^n` at a state `(s, v)` of the strip `ℝ × (-1, 1)`, for `n ≠ 0`,
when the table is `C^(n + 1)` at both `s` and the next collision parameter `t`. -/
theorem contDiffAt_nextCollision {x : ℝ × ℝ} (hχ₁ : ContDiffAt ℝ (n + 1) χ x.1)
    (hχ₂ : ContDiffAt ℝ (n + 1) χ (χ.nextParam x.1 x.2)) (hn : n ≠ 0)
    (hx : x.2 ∈ Ioo (-1) 1) : ContDiffAt ℝ n χ.nextCollision x := by
  have he : χ.nextCollision = fun y ↦ (uncurry χ.nextParam y, uncurry χ.nextTangential y) :=
    funext χ.nextCollision_apply
  rw [he]
  exact (χ.contDiffAt_uncurry_nextParam hχ₁ (hχ₂.of_le le_self_add) hn hx).prodMk
    (χ.contDiffAt_uncurry_nextTangential hχ₁ hχ₂ hn hx)

/-- **Smoothness of the billiard map.** The next-collision map of a `C^(n + 1)` strictly convex
table is `C^n` on the strip `ℝ × (-1, 1)`, for `n ≠ 0`. -/
theorem contDiffOn_nextCollision (hχ : ContDiff ℝ (n + 1) χ) (hn : n ≠ 0) :
    ContDiffOn ℝ n χ.nextCollision (univ ×ˢ Ioo (-1) 1) :=
  fun _ hx ↦ (χ.contDiffAt_nextCollision hχ.contDiffAt hχ.contDiffAt hn hx.2).contDiffWithinAt

/-! ### The twist of the billiard map -/

/-- The cotangent `⟪χ'(s), χ(t) - χ(s)⟫ / ω(χ'(s), χ(t) - χ(s))` of the angle between the tangent
at `χ(s)` and the chord from `χ(s)` to `χ(t)`. -/
private def chordCot (s t : ℝ) : ℝ :=
  ⟪deriv χ s, χ t - χ s⟫ / o.areaForm (deriv χ s) (χ t - χ s)

private theorem hasDerivAt_chordCot {s t : ℝ} (ht : t ∈ Ioo s (s + χ.period)) :
    HasDerivAt (χ.chordCot s)
      (o.areaForm (deriv χ t) (χ t - χ s) / o.areaForm (deriv χ s) (χ t - χ s) ^ 2) t := by
  have hd : HasDerivAt (fun t' ↦ χ t' - χ s) (deriv χ t) t :=
    (χ.differentiableAt t).hasDerivAt.sub_const (χ s)
  have hN : HasDerivAt (fun t' ↦ ⟪deriv χ s, χ t' - χ s⟫) ⟪deriv χ s, deriv χ t⟫ t :=
    (innerSL ℝ (deriv χ s)).hasFDerivAt.comp_hasDerivAt t hd
  have hD : HasDerivAt (fun t' ↦ o.areaForm (deriv χ s) (χ t' - χ s))
      (o.areaForm (deriv χ s) (deriv χ t)) t :=
    (o.areaForm (deriv χ s)).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hd
  have hD₀ : o.areaForm (deriv χ s) (χ t - χ s) ≠ 0 :=
    (χ.areaForm_pos _ _ (χ.apply_ne_of_mem_Ioo ht)).ne'
  refine (hN.div hD hD₀).congr_deriv ?_
  have h := o.inner_mul_areaForm_sub (deriv χ s) (deriv χ t) (χ t - χ s)
  rw [χ.norm_deriv, one_pow, one_mul] at h
  congr 1
  linear_combination h

/-- For a fixed starting point `χ(s)`, the cotangent of the chord angle is strictly decreasing in
the far endpoint `t ∈ (s, s + L)`. -/
private theorem strictAntiOn_chordCot (s : ℝ) :
    StrictAntiOn (χ.chordCot s) (Ioo s (s + χ.period)) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioo _ _)
    (fun t ht ↦ (χ.hasDerivAt_chordCot ht).continuousAt.continuousWithinAt) fun t ht ↦ ?_
  rw [interior_Ioo] at ht
  have hne := χ.apply_ne_of_mem_Ioo ht
  have hneg : o.areaForm (deriv χ t) (χ t - χ s) < 0 := by
    rw [← neg_sub, map_neg, neg_lt_zero]
    exact χ.areaForm_pos _ _ hne.symm
  rw [(χ.hasDerivAt_chordCot ht).deriv]
  exact div_neg_of_neg_of_pos hneg (pow_pos (χ.areaForm_pos _ _ hne) 2)

private theorem chordCot_nextParam {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    χ.chordCot s (χ.nextParam s v) = v / √(1 - v ^ 2) := by
  have hℓ : ‖χ (χ.nextParam s v) - χ s‖ ≠ 0 :=
    norm_ne_zero_iff.2 (sub_ne_zero.2 (χ.apply_nextParam_ne hv))
  rw [chordCot, χ.sub_eq_norm_smul_outgoingDir hv, inner_smul_right, map_smul, smul_eq_mul,
    inner_deriv_outgoingDir, areaForm_deriv_outgoingDir, mul_div_mul_left _ _ hℓ]

/-- For a fixed starting point `χ(s)`, the parameter of the next collision is continuous in the
tangential component `v ∈ (-1, 1)`. -/
private theorem continuousAt_nextParam {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    ContinuousAt (χ.nextParam s) v := by
  have hk : ContinuousAt (fun v' : ℝ ↦ v' / √(1 - v' ^ 2)) v :=
    continuousAt_id.div (continuousAt_const.sub (continuousAt_id.pow 2)).sqrt
      (sqrt_one_sub_sq_pos hv).ne'
  have hv' : ∀ᶠ v' in 𝓝 v, v' ∈ Ioo (-1) 1 := isOpen_Ioo.mem_nhds hv
  refine continuousAt_of_strictMonoOn_comp (χ.strictAntiOn_chordCot s).dual_right
    (isOpen_Ioo.mem_nhds (χ.nextParam_mem_Ioo hv))
    (hv'.mono fun _ ↦ χ.nextParam_mem_Ioo) (continuous_toDual.continuousAt.comp ?_)
  exact hk.congr (hv'.mono fun _ hv'' ↦ (χ.chordCot_nextParam hv'').symm)

/-- **The twist of the billiard map.** The parameter `t` of the next collision of `(s, v)` has
derivative `∂t/∂v = -ℓ / (√(1 - v ^ 2) √(1 - w ^ 2))` in `v`, where `ℓ = ‖χ(t) - χ(s)‖` is the
length of the chord and `w` the new tangential component. -/
theorem hasDerivAt_nextParam {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    HasDerivAt (χ.nextParam s)
      (-(‖χ (χ.nextParam s v) - χ s‖ /
        (√(1 - v ^ 2) * √(1 - χ.nextTangential s v ^ 2)))) v := by
  have hv₂ := one_sub_sq_pos hv
  -- The chord cotangent `ψ(t(v')) = v' / √(1 - v' ^ 2)` is inverted by `t` near `v`.
  have hψ := χ.hasDerivAt_chordCot (χ.nextParam_mem_Ioo (s := s) hv)
  rw [χ.sub_eq_norm_smul_outgoingDir hv, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
    areaForm_deriv_outgoingDir, χ.areaForm_deriv_nextParam_outgoingDir hv] at hψ
  have hpoly : HasDerivAt (fun y : ℝ ↦ 1 - y ^ 2) (-(2 * v)) v := by
    simpa using (hasDerivAt_pow 2 v).const_sub 1
  have hk := (hasDerivAt_id' v).div (hpoly.sqrt hv₂.ne') (Real.sqrt_pos.2 hv₂).ne'
  have hcomp : χ.chordCot s ∘ χ.nextParam s =ᶠ[𝓝 v] fun v' ↦ v' / √(1 - v' ^ 2) := by
    filter_upwards [isOpen_Ioo.mem_nhds hv] with v' hv'
    exact χ.chordCot_nextParam hv'
  set t := χ.nextParam s v
  set ℓ := ‖χ t - χ s‖
  set w := χ.nextTangential s v
  set r := √(1 - v ^ 2)
  have hr₂ : r ^ 2 = 1 - v ^ 2 := Real.sq_sqrt hv₂.le
  have hr : r ≠ 0 := (Real.sqrt_pos.2 hv₂).ne'
  have hℓ : ℓ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 (χ.apply_nextParam_ne hv))
  have hw : √(1 - w ^ 2) ≠ 0 := (sqrt_one_sub_sq_pos (χ.nextTangential_mem_Ioo hv)).ne'
  have hψ₀ : ℓ * -√(1 - w ^ 2) / (ℓ * r) ^ 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero hℓ (neg_ne_zero.2 hw)) (pow_ne_zero 2 (mul_ne_zero hℓ hr))
  convert hψ.of_comp_left (χ.continuousAt_nextParam hv) hk hψ₀ hcomp using 1
  field_simp
  linear_combination hr₂

/-- **The twist condition** `∂t/∂v < 0`: the derivative of the next collision parameter in the
tangential component `v ∈ (-1, 1)` is negative. -/
theorem deriv_nextParam_neg {s v : ℝ} (hv : v ∈ Ioo (-1) 1) : deriv (χ.nextParam s) v < 0 := by
  rw [(χ.hasDerivAt_nextParam hv).deriv, neg_neg_iff_pos]
  have hℓ : 0 < ‖χ (χ.nextParam s v) - χ s‖ :=
    norm_pos_iff.2 (sub_ne_zero.2 (χ.apply_nextParam_ne hv))
  exact div_pos hℓ (mul_pos (sqrt_one_sub_sq_pos hv)
    (sqrt_one_sub_sq_pos (χ.nextTangential_mem_Ioo hv)))

/-- For a fixed starting point `χ(s)`, the parameter of the next collision is strictly decreasing
in the tangential component `v ∈ (-1, 1)`: aiming further forward moves the next collision point
backward along the boundary, towards `χ(s)`. -/
theorem strictAntiOn_nextParam (s : ℝ) : StrictAntiOn (χ.nextParam s) (Ioo (-1) 1) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioo _ _)
    (fun v hv ↦ (χ.hasDerivAt_nextParam hv).continuousAt.continuousWithinAt) fun v hv ↦ ?_
  rw [interior_Ioo] at hv
  exact χ.deriv_nextParam_neg hv

end StrictConvexBilliardTable

end TauCeti
