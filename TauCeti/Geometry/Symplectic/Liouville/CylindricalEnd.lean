/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Liouville.LinearAtInfinity
import Mathlib.Analysis.Calculus.ImplicitContDiff
import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# Smoothness of the radial coordinate on the cylindrical end

Let `M` be a completion of the Liouville domain `W ⊆ M` (`TauCeti.IsLiouvilleCompletion`), with
Liouville field `Z` and Liouville flow `ψ`, and let `r = TauCeti.liouvilleRadialCoordinate Z W` be
the radial coordinate of its cylindrical end. It is `1` on `W` and `e^t` at the point `ψ_t(y)`
reached from a boundary point `y` in time `t ≥ 0`. This file proves that `r` is a smooth function
on the cylindrical end `M \ W` and that the Liouville field is `r ∂_r` there, `dr(Z) = r`.
So a Hamiltonian linear at infinity is smooth on the part of the cylindrical end where it equals
`a r + b`, and there its Hamiltonian vector field can be computed from `dr`.

At the boundary of `W` the radial coordinate is only continuous: it is constant on `W` and grows
like `e^t` along the outgoing trajectories.

The identity `dr(Z) = r` is the infinitesimal form of `r(ψ_s x) = e^s r(x)`.

## Main results

* `TauCeti.IsLiouvilleCompletion.contMDiffAt_log_liouvilleRadialCoordinate`: the logarithm of the
  radial coordinate, the exit time from the boundary of `W`, is smooth outside the Liouville domain.
* `TauCeti.IsLiouvilleCompletion.contMDiffAt_liouvilleRadialCoordinate`,
  `TauCeti.IsLiouvilleCompletion.contMDiffOn_liouvilleRadialCoordinate`: the radial coordinate is
  smooth outside the Liouville domain.
* `TauCeti.IsLiouvilleCompletion.mvfderiv_liouvilleRadialCoordinate_apply`: the Liouville field
  differentiates the radial coordinate to itself outside the Liouville domain, `dr(Z) = r`.

## References

* P. Seidel, *A biased view of symplectic cohomology*, Current Developments in Mathematics 2006,
  Section 3 (completions and Hamiltonians linear at infinity).
* K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*, AMS Colloquium Publications 59,
  2012, Section 11.1.
-/

public section

open Filter Set
open scoped Manifold Topology

namespace TauCeti

namespace IsLiouvilleCompletion

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
  {ω : SmoothTwoForm I M} {α : SmoothForm I M ℝ 1} {W : Set M} {Z : (x : M) → TangentSpace I x}
  {x : M}

/-- On a completion of the Liouville domain `W`, the logarithm of the radial coordinate, the time
`log r(x)` at which the trajectory through `x` leaves the boundary of `W`, is smooth at every point
outside `W`. -/
theorem contMDiffAt_log_liouvilleRadialCoordinate (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (hx : x ∉ W) :
    ContMDiffAt I 𝓘(ℝ) (⊤ : ℕ∞) (fun x' ↦ Real.log (liouvilleRadialCoordinate Z W x')) x := by
  -- Smoothness comes from the implicit function theorem. Write `W = {f ≤ c}` with `df(Z) > 0`
  -- along the boundary `f⁻¹(c)`. Near `x ∉ W`, the time `τ = log r(x')` is the solution of
  -- `f(ψ_{-τ}(x')) = c`, and the derivative of the left side in `τ` is `-df(Z) ≠ 0` at the
  -- boundary point `ψ_{-τ}(x)`. Since the flow is jointly smooth, the implicit function theorem
  -- (`ContDiffAt.implicitFunction`), applied in a chart at `x`, gives a smooth solution `τ(x')`
  -- near `x`, and `log r = τ` there.
  have hZs := h.contMDiff_of_interior_eq hZ
  have hc := h.isCompleteVectorField hZ
  have hflow := hc.contMDiff_flowOf le_top hZs
  obtain ⟨f, c, hf, hW, hfc⟩ := h.exists_sublevel_of_interior_eq hZ
  have hfront : frontier W = {y | f y = c} :=
    hW ▸ frontier_setOf_le_eq_of_mvfderiv_pos hf fun y hy ↦ (hfc y hy).2
  -- The boundary point `y₀ = ψ_{-τ₀}(x)` on the trajectory through `x`, at time `τ₀ = log r(x)`.
  set τ₀ := Real.log (liouvilleRadialCoordinate Z W x)
  have hτ₀ : 0 < τ₀ := Real.log_pos ((h.one_lt_liouvilleRadialCoordinate_iff hZ).2 hx)
  have hy₀ : f (flowOf Z (-τ₀) x) = c := by
    have := h.flowOf_neg_log_liouvilleRadialCoordinate_mem_frontier hZ
      fun hi ↦ hx (interior_subset hi)
    rwa [hfront] at this
  -- The implicit equation `G(u, τ) = f(ψ_{-τ}(φ⁻¹ u)) = c`, read in the chart `φ` at `x`.
  set φ := extChartAt I x
  set G : E × ℝ → ℝ := fun p ↦ f (flowOf Z (-p.2) (φ.symm p.1))
  have hφx : φ.symm (φ x) = x := extChartAt_to_inv x
  have hG0 : G (φ x, τ₀) = c := by simp only [G, hφx, hy₀]
  have hG : ContDiffAt ℝ (⊤ : ℕ∞) G (φ x, τ₀) := by
    rw [← contMDiffAt_iff_contDiffAt]
    have hsymm : ContMDiffAt 𝓘(ℝ, E) I (⊤ : ℕ∞) φ.symm (φ x) :=
      (contMDiffOn_extChartAt_symm x).contMDiffAt (extChartAt_target_mem_nhds x)
    have hfst : ContMDiffAt 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E) (⊤ : ℕ∞) Prod.fst (φ x, τ₀) :=
      contDiff_fst.contMDiff.contMDiffAt
    have hneg : ContMDiffAt 𝓘(ℝ, E × ℝ) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) (fun p : E × ℝ ↦ -p.2) (φ x, τ₀) :=
      contDiff_snd.neg.contMDiff.contMDiffAt
    have hchart := hneg.prodMk (hsymm.comp (φ x, τ₀) hfst)
    have hf₀ : ContMDiffAt I 𝓘(ℝ) (⊤ : ℕ∞) f (flowOf Z (-τ₀) (φ.symm (φ x))) := by
      rw [hφx]
      exact (hfc _ hy₀).1
    exact hf₀.comp (φ x, τ₀) ((hflow _).comp (φ x, τ₀) hchart)
  -- The derivative of `G` in the time variable is `-df(Z) ≠ 0` at the boundary point.
  have hderiv : HasDerivAt (fun t ↦ G (φ x, t))
      (-mvfderiv I f (flowOf Z (-τ₀) x) (Z (flowOf Z (-τ₀) x))) τ₀ := by
    have hcomp := (Manifold.hasDerivAt_comp_curve ((hfc _ hy₀).1.mdifferentiableAt (by simp))
      (hc.isMIntegralCurve_flowOf (hZs.of_le (by simp)) x (-τ₀))).comp τ₀ (hasDerivAt_neg τ₀)
    rw [mul_neg_one] at hcomp
    exact hcomp.congr_of_eventuallyEq
      (Eventually.of_forall fun t ↦ congrArg (fun y ↦ f (flowOf Z (-t) y)) hφx)
  have hinv : (fderiv ℝ G (φ x, τ₀) ∘L .inr ℝ E ℝ).IsInvertible := by
    have hpartial : HasFDerivAt (fun t ↦ G (φ x, t)) (fderiv ℝ G (φ x, τ₀) ∘L .inr ℝ E ℝ) τ₀ :=
      (hG.differentiableAt (by simp)).hasFDerivAt.comp τ₀ (hasFDerivAt_prodMk_right _ τ₀)
    rw [hpartial.unique hderiv.hasFDerivAt]
    exact ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ (neg_ne_zero.2 (hfc _ hy₀).2.ne')),
      by ext; simp⟩
  -- The implicit function `T` solves `G(u, T u) = c` near `φ x`, and `log r = T ∘ φ` there.
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  set T := hG.implicitFunction hn hinv
  have hT : ContDiffAt ℝ (⊤ : ℕ∞) T (φ x) := hG.contDiffAt_implicitFunction hn hinv
  have hTeq : ∀ᶠ u in 𝓝 (φ x), G (u, T u) = c := by
    simpa [hG0] using hG.eventually_apply_implicitFunction hn hinv
  have hT₀ : T (φ x) = τ₀ := hG.implicitFunction_apply_self hn hinv
  have hTpos : ∀ᶠ u in 𝓝 (φ x), 0 < T u := hT.continuousAt.eventually (lt_mem_nhds (hT₀ ▸ hτ₀))
  have heq : (fun x' ↦ Real.log (liouvilleRadialCoordinate Z W x')) =ᶠ[𝓝 x] T ∘ φ := by
    have hφ : Tendsto φ (𝓝 x) (𝓝 (φ x)) := continuousAt_extChartAt (I := I) x
    filter_upwards [hφ.eventually hTeq, hφ.eventually hTpos,
      extChartAt_source_mem_nhds (I := I) x] with x' h₁ h₂ h₃
    have hfr : flowOf Z (-T (φ x')) x' ∈ frontier W := by
      simp only [G, φ.left_inv h₃] at h₁
      rwa [hfront]
    have := h.liouvilleRadialCoordinate_flowOf hZ hfr h₂.le
    rw [h.flowOf_flowOf hZ, add_neg_cancel, h.flowOf_zero hZ] at this
    rw [Function.comp_apply, this, Real.log_exp]
  exact (hT.contMDiffAt.comp x contMDiffAt_extChartAt).congr_of_eventuallyEq heq

/-- **The radial coordinate is smooth on the cylindrical end.** On a completion of the Liouville
domain `W`, the radial coordinate is smooth at every point outside `W`. -/
theorem contMDiffAt_liouvilleRadialCoordinate (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (hx : x ∉ W) :
    ContMDiffAt I 𝓘(ℝ) (⊤ : ℕ∞) (liouvilleRadialCoordinate Z W) x :=
  (Real.contDiff_exp.contMDiff.contMDiffAt.comp x
    (h.contMDiffAt_log_liouvilleRadialCoordinate hZ hx)).congr_of_eventuallyEq
    (Eventually.of_forall fun x' ↦ (Real.exp_log
      (zero_lt_one.trans_le (one_le_liouvilleRadialCoordinate Z W x'))).symm)

/-- The radial coordinate of a completion is smooth outside the Liouville domain. -/
theorem contMDiffOn_liouvilleRadialCoordinate (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) :
    ContMDiffOn I 𝓘(ℝ) (⊤ : ℕ∞) (liouvilleRadialCoordinate Z W) Wᶜ :=
  fun _ hx ↦ (h.contMDiffAt_liouvilleRadialCoordinate hZ hx).contMDiffWithinAt

/-- **The Liouville field is `r ∂_r` on the cylindrical end.** Outside the Liouville domain, the
Liouville field differentiates the radial coordinate to itself, `dr(Z) = r`. -/
theorem mvfderiv_liouvilleRadialCoordinate_apply (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (hx : x ∉ W) :
    mvfderiv I (liouvilleRadialCoordinate Z W) x (Z x) = liouvilleRadialCoordinate Z W x := by
  -- Along the trajectory `x = ψ_t(y)` from the boundary, `r(ψ_s x) = e^{s + t} = e^s r(x)` for
  -- `s > -t`, a neighbourhood of `0`.
  obtain ⟨⟨y, t⟩, ⟨hy, ht, hyx⟩, -⟩ := h.existsUnique_flowOf_eq hZ hx
  have hr : MDifferentiableAt I 𝓘(ℝ) (liouvilleRadialCoordinate Z W) (flowOf Z 0 x) := by
    rw [h.flowOf_zero hZ]
    exact (h.contMDiffAt_liouvilleRadialCoordinate hZ hx).mdifferentiableAt (by simp)
  have hcurve := Manifold.hasDerivAt_comp_curve hr
    ((h.isCompleteVectorField hZ).isMIntegralCurve_flowOf
      ((h.contMDiff_of_interior_eq hZ).of_le (by simp)) x 0)
  simp only at hcurve
  rw [h.flowOf_zero hZ] at hcurve
  have heq : (liouvilleRadialCoordinate Z W ∘ fun s ↦ flowOf Z s x) =ᶠ[𝓝 0]
      fun s ↦ Real.exp s * liouvilleRadialCoordinate Z W x := by
    filter_upwards [Ioi_mem_nhds (neg_lt_zero.2 ht)] with s hs
    rw [Function.comp_apply, ← hyx, h.flowOf_flowOf hZ,
      h.liouvilleRadialCoordinate_flowOf hZ hy (by linarith [mem_Ioi.1 hs]),
      h.liouvilleRadialCoordinate_flowOf hZ hy ht.le, Real.exp_add]
  refine hcurve.unique (HasDerivAt.congr_of_eventuallyEq ?_ heq)
  simpa using (Real.hasDerivAt_exp 0).mul_const (liouvilleRadialCoordinate Z W x)

end IsLiouvilleCompletion

end TauCeti
