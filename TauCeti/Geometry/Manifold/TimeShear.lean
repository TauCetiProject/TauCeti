/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Topology.Maps.Proper.Basic
public import TauCeti.Geometry.Manifold.Immersion.Differential
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import TauCeti.Geometry.Manifold.Instances.Sphere

/-!
# Time shears of a cylinder

The *time shear* of a cylinder `M × ℝ` by functions `β : ℝ → ℝ` and `h : M → ℝ` is the map
`(x, t) ↦ (x, t + β t * h x)` (`TauCeti.timeShear`). It preserves the base point and moves each
time by `β t * h x`. When the time derivative `1 + β' t * h x` is positive, it is injective, and
when the displacement is bounded it is proper; for smooth `β` and `h` it is then an injective
proper immersion, so composing a smooth embedding of the cylinder with it gives a smooth embedding
again.

Over the circle, a smooth `β` of compact support and any `ε > 0` admit an `h` vanishing at a
chosen point `exp (θ₀ i)`, with velocity `1` there along `Circle.exp`, for which the time shear
moves times by less than `ε` and has positive time derivative (`TauCeti.exists_shear_circle`).
Along the slice through `exp (θ₀ i)` at time `t`, such a shear has time velocity `β t`, so it can
cancel a prescribed time component of the derivative along a line `{exp (θ₀ i)} × ℝ`.

## Main definitions

* `TauCeti.timeShear β h`: the time shear `(x, t) ↦ (x, t + β t * h x)` of a cylinder `M × ℝ`.

## Main results

* `TauCeti.injective_timeShear`, `TauCeti.isProperMap_timeShear`, `TauCeti.isImmersion_timeShear`:
  a time shear with positive time derivative and bounded displacement is an injective proper
  immersion.
* `TauCeti.contMDiff_timeShear`: a time shear by smooth functions is smooth.
* `TauCeti.exists_shear_circle`: small time shears of the cylinder over the circle with prescribed
  velocity at a point.
-/

public section

noncomputable section

open Set Function Filter Manifold Topology
open scoped Manifold ContDiff

namespace TauCeti

section TimeShear

/-- The **time shear** `(x, t) ↦ (x, t + β t * h x)` of the cylinder `M × ℝ`. -/
def timeShear {M : Type*} (β : ℝ → ℝ) (h : M → ℝ) (p : M × ℝ) : M × ℝ :=
  (p.1, p.2 + β p.2 * h p.1)

/-- A time shear moves `(x, t)` to `(x, t + β t * h x)`. -/
@[simp]
theorem timeShear_apply {M : Type*} (β : ℝ → ℝ) (h : M → ℝ) (x : M) (t : ℝ) :
    timeShear β h (x, t) = (x, t + β t * h x) :=
  (rfl)

/-- For a fixed point `x`, the time coordinate of a time shear is strictly increasing in time when
its derivative `1 + β' t * h x` is positive. -/
theorem strictMono_timeShear_snd {M : Type*} {β : ℝ → ℝ} {h : M → ℝ} (hβ : Differentiable ℝ β)
    (hpos : ∀ x t, 0 < 1 + deriv β t * h x) (x : M) :
    StrictMono fun t => (timeShear β h (x, t)).2 := by
  refine strictMono_of_deriv_pos fun t => ?_
  have hd : HasDerivAt (fun t => t + β t * h x) (1 + deriv β t * h x) t :=
    (hasDerivAt_id t).add ((hβ t).hasDerivAt.mul_const (h x))
  simpa only [timeShear_apply] using hd.deriv ▸ hpos x t

/-- A time shear whose time derivative is positive is injective. -/
theorem injective_timeShear {M : Type*} {β : ℝ → ℝ} {h : M → ℝ} (hβ : Differentiable ℝ β)
    (hpos : ∀ x t, 0 < 1 + deriv β t * h x) : Injective (timeShear β h) := by
  rintro ⟨x, t⟩ ⟨x', t'⟩ he
  simp only [timeShear_apply, Prod.mk.injEq] at he
  obtain ⟨rfl, he⟩ := he
  exact Prod.ext rfl ((strictMono_timeShear_snd hβ hpos x).injective he)

variable {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IM : ModelWithCorners ℝ EM HM} [TopologicalSpace M] [ChartedSpace HM M]

/-- A time shear with bounded displacement is proper: a sequence, or ultrafilter, whose image
converges has converging base points and bounded times. -/
theorem isProperMap_timeShear [T2Space M] {β : ℝ → ℝ} {h : M → ℝ}
    (hβ : Continuous β) (hh : Continuous h) {C : ℝ} (hC : ∀ x t, |β t * h x| ≤ C) :
    IsProperMap (timeShear β h) := by
  have hc : Continuous (timeShear β h) :=
    continuous_fst.prodMk (continuous_snd.add ((hβ.comp continuous_snd).mul (hh.comp
      continuous_fst)))
  refine isProperMap_iff_ultrafilter.2 ⟨hc, fun 𝒰 y hy => ?_⟩
  -- The base points converge to `y.1`, since the shear does not move them.
  have h₁ : Tendsto Prod.fst (𝒰 : Filter (M × ℝ)) (𝓝 y.1) := by
    simpa only [comp_def, timeShear] using (continuous_fst.tendsto y).comp hy
  -- The times stay within `C + 1` of `y.2`, so they converge along `𝒰` to some `s`.
  have hb : ∀ᶠ p in (𝒰 : Filter (M × ℝ)), p.2 ∈ Icc (y.2 - 1 - C) (y.2 + 1 + C) := by
    filter_upwards [((continuous_snd.tendsto y).comp hy).eventually
      (Ioo_mem_nhds (sub_one_lt y.2) (lt_add_one y.2))] with p hp
    obtain ⟨hlo, hhi⟩ := hp
    simp only [Function.comp_apply, timeShear] at hlo hhi
    have := abs_le.1 (hC p.1 p.2)
    exact ⟨by linarith, by linarith⟩
  obtain ⟨s, -, hs⟩ := isCompact_iff_ultrafilter_le_nhds.1 isCompact_Icc (𝒰.map Prod.snd)
    (le_principal_iff.2 (mem_map.2 hb))
  have hx : Tendsto id (𝒰 : Filter (M × ℝ)) (𝓝 (y.1, s)) := h₁.prodMk_nhds hs
  exact ⟨(y.1, s), tendsto_nhds_unique ((hc.tendsto _).comp hx) hy, hx⟩

/-- The time coordinate `(x, t) ↦ t + β t * h x` of a time shear by smooth `β` and `h` is
smooth. -/
private theorem contMDiff_timeShear_snd {β : ℝ → ℝ} {h : M → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hh : ContMDiff IM 𝓘(ℝ) ∞ h) :
    ContMDiff (IM.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ fun q : M × ℝ => q.2 + β q.2 * h q.1 := by
  have hm : ContMDiff (IM.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ fun q : M × ℝ => β q.2 • h q.1 :=
    (hβ.contMDiff.comp contMDiff_snd).smul (hh.comp contMDiff_fst)
  simp only [smul_eq_mul] at hm
  exact contMDiff_snd.add hm

/-- A time shear by smooth `β` and `h` is smooth. -/
theorem contMDiff_timeShear {β : ℝ → ℝ} {h : M → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hh : ContMDiff IM 𝓘(ℝ) ∞ h) :
    ContMDiff (IM.prod 𝓘(ℝ)) (IM.prod 𝓘(ℝ)) ∞ (timeShear β h) :=
  contMDiff_fst.prodMk (contMDiff_timeShear_snd hβ hh)

variable [IM.Boundaryless] [IsManifold IM ∞ M] in
/-- A smooth time shear whose time derivative `1 + β' t * h x` never vanishes is an immersion. -/
theorem isImmersion_timeShear [FiniteDimensional ℝ EM] {β : ℝ → ℝ} {h : M → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hh : ContMDiff IM 𝓘(ℝ) ∞ h) (hpos : ∀ x t, 1 + deriv β t * h x ≠ 0) :
    IsImmersion (IM.prod 𝓘(ℝ)) (IM.prod 𝓘(ℝ)) ∞ (timeShear β h) := by
  refine isImmersion_iff_forall_isImmersionAt.2 fun q => ?_
  refine (contMDiff_timeShear_snd hβ hh).isImmersionAt_fst_prod (by simp) ?_
  refine IsDiffImmersionAt.of_injective_of_finiteDimensional ?_
  have hd : HasDerivAt (fun t => t + β t * h q.1) (1 + deriv β q.2 * h q.1) q.2 :=
    (hasDerivAt_id q.2).add ((hβ.differentiable (by simp) q.2).hasDerivAt.mul_const (h q.1))
  rw [mfderiv_eq_fderiv, hd.hasFDerivAt.fderiv]
  intro r r' hr
  simpa [hpos q.1 q.2] using hr

end TimeShear

/-! ### Time shears of the cylinder over the circle -/

section Circle

attribute [local instance] finrank_real_complex_fact'

/-- **Choosing the shear.** For a smooth `β : ℝ → ℝ` with compact support and `ε > 0`, some
smooth `h` on the circle vanishes at `exp (θ₀ i)`, has velocity `1` there along `Circle.exp`, and
is so small that the time shear `(x, t) ↦ (x, t + β t * h x)` moves times by less than `ε` and has
positive time derivative `1 + β' t * h x`. -/
theorem exists_shear_circle (θ₀ : ℝ) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hcs : HasCompactSupport β) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : Circle → ℝ, ContMDiff (𝓡 1) 𝓘(ℝ) ∞ h ∧ h (Circle.exp θ₀) = 0 ∧
      HasDerivAt (fun θ => h (Circle.exp θ)) 1 θ₀ ∧
        ∀ x t, |β t * h x| < ε ∧ 0 < 1 + deriv β t * h x := by
  obtain ⟨C₁, hC₁⟩ := hβ.continuous.bounded_above_of_compact_support hcs
  obtain ⟨C₂, hC₂⟩ := (hβ.continuous_deriv (by simp)).bounded_above_of_compact_support hcs.deriv
  set C := max (max C₁ C₂) 0
  have hC0 : 0 ≤ C := le_max_right _ _
  have hβC (t : ℝ) : |β t| ≤ C :=
    (hC₁ t).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hβ'C (t : ℝ) : |deriv β t| ≤ C :=
    (hC₂ t).trans ((le_max_right _ _).trans (le_max_left _ _))
  -- With `|h| ≤ δ`, both displacements are at most `C δ < min ε 1 / 2`.
  have hm : 0 < min ε 1 := lt_min hε one_pos
  set δ := min ε 1 / (2 * (C + 1))
  have hδ : 0 < δ := div_pos hm (by positivity)
  have hCδ : C * δ < min ε 1 / 2 := by
    calc C * δ = min ε 1 / 2 * (C / (C + 1)) := by simp only [δ]; field_simp
      _ < min ε 1 / 2 * 1 :=
        mul_lt_mul_of_pos_left ((div_lt_one (by positivity)).2 (by linarith)) (by positivity)
      _ = min ε 1 / 2 := mul_one _
  obtain ⟨h, hh, hh0, hhd, hhδ⟩ := exists_contMDiff_circle_hasDerivAt θ₀ hδ
  refine ⟨h, hh, hh0, hhd, fun x t => ?_⟩
  have hε1 := min_le_left ε 1
  have h11 := min_le_right ε 1
  have h₁ : |deriv β t * h x| < 1 := by
    rw [abs_mul]
    exact (mul_le_mul (hβ'C t) (hhδ x) (abs_nonneg _) hC0).trans_lt (by linarith)
  refine ⟨?_, by linarith [neg_abs_le (deriv β t * h x)]⟩
  rw [abs_mul]
  exact (mul_le_mul (hβC t) (hhδ x) (abs_nonneg _) hC0).trans_lt (by linarith)

end Circle

end TauCeti
