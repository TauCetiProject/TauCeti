/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

import TauCeti.Analysis.Complex.Conformal.Inverse.Function
import TauCeti.Analysis.Complex.Conformal.Jordan.Unbounded.BoundaryPrevertex
import TauCeti.Analysis.Complex.Conformal.LocalFrontier
import TauCeti.Analysis.Complex.UpperHalfPlane.Topology

/-!
# Ends of opening `2 * π` of an inverted coordinate

Let `f` be a conformal map of the upper half-plane onto an unbounded domain with several accesses
to infinity, and let `g = (f - q)⁻¹` be its inverted coordinate, continuous on the closed upper
half-plane and injective away from its zeros.  The real zeros of `g` are the boundary parameters
at which `f` tends to infinity.

This file treats a zero `x` of `g` at which the domain has an end of opening `2 * π`: `f` maps the
points of the upper half-plane near `x` into the far part
`{ρ < ‖w - c‖, re ((w - c) / b) < 0 or im ((w - c) / b) ∉ [0, π]}` of the exterior of a closed
half-strip, and that far part lies in the image of `f`.  If `x` is an isolated zero of `g`, then
the recovered map `z ↦ q + (g z)⁻¹` is continuous and injective on a punctured closed upper
half-disc about `x`, tends to infinity at `x`, and far out the image of the open upper half-disc is
exactly the exterior of the half-strip.  These are the local conditions at a vertex at infinity of
opening `2 * π`, with turning exponent `-3`, in the Schwarz--Christoffel formula
`TauCeti.eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_boundary`, so they apply to
polygonal domains with several ends, one of which has opening `2 * π`.

That `x` is an isolated zero of `g` is an explicit hypothesis, in the form produced by
`TauCeti.eventually_ne_zero_of_real_on_axis`; it holds, for instance, when `g` has only finitely
many real zeros.

## Main results

* `TauCeti.exists_ball_halfStripExterior_end_of_inverted_coordinate`: at an isolated zero of the
  inverted coordinate whose end is the exterior of a half-strip, the recovered map satisfies the
  local conditions at a vertex at infinity of opening `2 * π`.

## References

* C. Carathéodory, Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung,
  Math. Ann. 73 (1913).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Springer, 1992, Ch. 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

open Bornology Complex Filter Function Metric Set Topology UpperHalfPlane

namespace TauCeti

variable {f g : ℂ → ℂ} {q : ℂ}

/-- **The recovered map at an end of opening `2 * π`.**  Let `g = (f - q)⁻¹` be the inverted
coordinate of a holomorphic map `f` of the upper half-plane: `g` is continuous on the closed upper
half-plane, nonzero in its interior, and injective away from its zeros.  Let `x` be an isolated
real zero of `g`, and suppose that `f` maps the points of the upper half-plane near `x` into the
far part `E = {ρ < ‖w - c‖, re ((w - c) / b) < 0 or im ((w - c) / b) ∉ [0, π]}` of the exterior of
a closed half-strip, and that `E` lies in the image of `f`.  Then on a closed upper half-disc about
`x` with `x` removed, the recovered map `z ↦ q + (g z)⁻¹`, which is `f` in the upper half-plane, is
continuous and injective, it tends to infinity at `x`, and far from `c` the image of the open
upper half-disc is exactly the exterior of the half-strip.

These are the local conditions of
`TauCeti.eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_boundary` at a vertex at
infinity with turning exponent `-3`. -/
theorem exists_ball_halfStripExterior_end_of_inverted_coordinate
    (hgc : ContinuousOn g {z : ℂ | 0 ≤ z.im}) (hfd : DifferentiableOn ℂ f upperHalfPlaneSet)
    (hgf : EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet)
    (hgne : ∀ z ∈ upperHalfPlaneSet, g z ≠ 0)
    (hgi : InjOn g {z : ℂ | 0 ≤ z.im ∧ g z ≠ 0}) {x : ℝ} (hx : g x = 0)
    (hiso : ∀ᶠ z in 𝓝[{z : ℂ | 0 ≤ z.im} \ {(x : ℂ)}] (x : ℂ), g z ≠ 0) {ρ : ℝ} {c b : ℂ}
    (hS : {w : ℂ | ρ < ‖w - c‖ ∧
      (((w - c) / b).re < 0 ∨ ((w - c) / b).im ∉ Icc 0 Real.pi)} ⊆ f '' upperHalfPlaneSet)
    (hfS : ∀ᶠ z in 𝓝[upperHalfPlaneSet] (x : ℂ), f z ∈ {w : ℂ | ρ < ‖w - c‖ ∧
      (((w - c) / b).re < 0 ∨ ((w - c) / b).im ∉ Icc 0 Real.pi)}) :
    ∃ r > 0, ∃ ρ' : ℝ,
      ContinuousOn (fun z => q + (g z)⁻¹)
        ((closedBall (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) \ {(x : ℂ)}) ∧
      InjOn (fun z => q + (g z)⁻¹) ((closedBall (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) \ {(x : ℂ)}) ∧
      Tendsto (fun z => q + (g z)⁻¹) (𝓝[{z : ℂ | 0 ≤ z.im} \ {(x : ℂ)}] (x : ℂ))
        (cobounded ℂ) ∧
      ∀ w : ℂ, ρ' < ‖w - c‖ →
        (w ∈ (fun z => q + (g z)⁻¹) '' (ball (x : ℂ) r ∩ upperHalfPlaneSet) ↔
          ((w - c) / b).re < 0 ∨ ((w - c) / b).im ∉ Icc 0 Real.pi) := by
  set F : ℂ → ℂ := fun z => q + (g z)⁻¹
  have hFf {z : ℂ} (hz : z ∈ upperHalfPlaneSet) : F z = f z := by
    simp only [F]
    rw [hgf hz, inv_inv, add_sub_cancel]
  have hfi : InjOn f upperHalfPlaneSet := fun z hz w hw h =>
    hgi ⟨le_of_lt hz, hgne z hz⟩ ⟨le_of_lt hw, hgne w hw⟩ (by simp only [hgf hz, hgf hw, h])
  -- a closed upper half-disc about `x` on which `f` lands in the end and `g` vanishes only at `x`
  obtain ⟨r₁, hr₁, hE₁⟩ := Metric.mem_nhdsWithin_iff.mp hfS
  obtain ⟨r₂, hr₂, hne₂⟩ := Metric.mem_nhdsWithin_iff.mp hiso
  obtain ⟨r, hr, hrr₁, hrr₂⟩ : ∃ r, 0 < r ∧ r < r₁ ∧ r < r₂ :=
    ⟨min r₁ r₂ / 2, by positivity, by linarith [min_le_left r₁ r₂, lt_min hr₁ hr₂],
      by linarith [min_le_right r₁ r₂, lt_min hr₁ hr₂]⟩
  set A := (closedBall (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) \ {(x : ℂ)}
  have hgA (z : ℂ) (hz : z ∈ A) : g z ≠ 0 :=
    hne₂ ⟨closedBall_subset_ball hrr₂ hz.1.1, hz.1.2, hz.2⟩
  have hFc : ContinuousOn F A :=
    continuousOn_const.add ((hgc.mono fun z (hz : z ∈ A) => hz.1.2).inv₀ hgA)
  have hFi : InjOn F A := fun z hz w hw h =>
    hgi ⟨hz.1.2, hgA z hz⟩ ⟨hw.1.2, hgA w hw⟩ (inv_injective (add_left_cancel h))
  have hFt : Tendsto F (𝓝[{z : ℂ | 0 ≤ z.im} \ {(x : ℂ)}] (x : ℂ)) (cobounded ℂ) := by
    have hg : Tendsto g (𝓝[{z : ℂ | 0 ≤ z.im} \ {(x : ℂ)}] (x : ℂ)) (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨hx ▸ ((hgc _ (by simp)).mono sdiff_subset).tendsto, hiso⟩
    exact (tendsto_const_add_cobounded q).comp (tendsto_inv₀_nhdsNE_zero.comp hg)
  -- `F` is bounded on the semicircle of radius `r`, a crosscut of the upper half-plane
  set K := sphere (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}
  have hKA : K ⊆ A := fun z hz => ⟨⟨sphere_subset_closedBall hz.1, hz.2⟩, fun h => by
    rw [mem_singleton_iff.mp h] at hz
    exact hr.ne ((dist_self _).symm.trans (mem_sphere.mp hz.1))⟩
  obtain ⟨M, hM⟩ := ((isCompact_sphere (x : ℂ) r).inter_right
    (isClosed_le continuous_const continuous_im)).exists_bound_of_continuousOn (hFc.mono hKA)
  refine ⟨r, hr, max ρ (M + ‖c‖), hFc, hFi, hFt, fun w hw => ⟨?_, fun hext => ?_⟩⟩
  · rintro ⟨z, ⟨hzb, hzH⟩, rfl⟩
    rw [hFf hzH]
    exact (hE₁ ⟨ball_subset_ball hrr₁.le hzb, hzH⟩).2
  -- far out, the exterior of the half-strip is preconnected, in the image of `f`, and beyond `M`
  set D := {w : ℂ | max ρ (M + ‖c‖) < ‖w - c‖ ∧
    (((w - c) / b).re < 0 ∨ ((w - c) / b).im ∉ Icc 0 Real.pi)}
  have hDf : D ⊆ f '' upperHalfPlaneSet := fun v hv =>
    hS ⟨(le_max_left _ _).trans_lt hv.1, hv.2⟩
  have hDM {v : ℂ} (hv : v ∈ D) : M < ‖v‖ := by
    have := (le_max_right ρ (M + ‖c‖)).trans_lt hv.1
    linarith [norm_sub_le v c]
  -- so its preimage under `f` avoids the semicircle
  have hinv := hfi.leftInvOn_invFunOn
  have hsep : invFunOn f upperHalfPlaneSet '' D ⊆ ball (x : ℂ) r ∪ (closedBall (x : ℂ) r)ᶜ := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨y, hyH, rfl⟩ := hDf hv
    rw [hinv hyH]
    by_cases hyb : y ∈ ball (x : ℂ) r
    · exact Or.inl hyb
    refine Or.inr fun hyc => (hDM hv).not_ge ?_
    rw [← hFf hyH]
    refine hM y ⟨?_, le_of_lt hyH⟩
    rw [← closedBall_sdiff_ball]
    exact ⟨hyc, hyb⟩
  -- and it contains points inside the semicircle, near `x`, so it lies inside
  have := Real.nhdsWithin_upperHalfPlaneSet_neBot x
  obtain ⟨z₀, hz₀D, hz₀E, hz₀b, hz₀H⟩ :=
    ((tendsto_norm_cobounded_atTop.comp ((tendsto_sub_const_cobounded c).comp
      (tendsto_cobounded_of_inverted_boundary_eq_zero (hgc _ (by simp)) hgf hgne hx))).eventually
        (eventually_gt_atTop (max ρ (M + ‖c‖))) |>.and (hfS.and
          ((eventually_nhdsWithin_of_eventually_nhds (ball_mem_nhds _ hr)).and
            self_mem_nhdsWithin))).exists
  have hsub := ((isPreconnected_far_halfStripExterior _ c b).image _
    ((hfd.invFunOn isOpen_upperHalfPlaneSet hfi).continuousOn.mono hDf)).subset_left_of_subset_union
      isOpen_ball isClosed_closedBall.isOpen_compl
      (disjoint_compl_right.mono_left ball_subset_closedBall) hsep
      ⟨z₀, ⟨f z₀, ⟨hz₀D, hz₀E.2⟩, hinv hz₀H⟩, hz₀b⟩
  obtain ⟨y, hyH, rfl⟩ := hDf ⟨hw, hext⟩
  exact ⟨y, ⟨hinv hyH ▸ hsub ⟨f y, ⟨hw, hext⟩, rfl⟩, hyH⟩, hFf hyH⟩

end TauCeti
