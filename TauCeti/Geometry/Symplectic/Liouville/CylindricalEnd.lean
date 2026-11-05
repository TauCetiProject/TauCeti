/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Liouville.LinearAtInfinity
import TauCeti.Geometry.Manifold.Flow.HittingTime

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
  -- Write `W = {f ≤ c}` with `df(Z) > 0` along the boundary `f⁻¹(c)`. The trajectory through `x`
  -- meets the boundary at time `-log r(x)`, transversally, so the hitting time `T` of the boundary
  -- is smooth near `x` (`contMDiffAt_flowHittingTime`), and `log r = -T`.
  have hZs := h.contMDiff_of_interior_eq hZ
  obtain ⟨f, c, hf, hW, hfc⟩ := h.exists_sublevel_of_interior_eq hZ
  have hfront : frontier W = {y | f y = c} :=
    hW ▸ frontier_setOf_le_eq_of_mvfderiv_pos hf fun y hy ↦ (hfc y hy).2
  -- The boundary point `ψ_{-τ₀}(x)` on the trajectory through `x`, at time `τ₀ = log r(x)`.
  set τ₀ := Real.log (liouvilleRadialCoordinate Z W x)
  have hτ₀ : 0 < τ₀ := Real.log_pos ((h.one_lt_liouvilleRadialCoordinate_iff hZ).2 hx)
  have hy₀ : f (flowOf Z (-τ₀) x) = c := by
    have := h.flowOf_neg_log_liouvilleRadialCoordinate_mem_frontier hZ
      fun hi ↦ hx (interior_subset hi)
    rwa [hfront] at this
  have hdom : (-τ₀, x) ∈ flowDomain Z := (h.isCompleteVectorField hZ).mem_flowDomain _ _
  set T := flowHittingTime Z f (-τ₀) x
  have hT : ContMDiffAt I 𝓘(ℝ) (⊤ : ℕ∞) T x :=
    contMDiffAt_flowHittingTime le_top hZs hdom (hfc _ hy₀).1 (hfc _ hy₀).2.ne'
  have hTneg : ∀ᶠ x' in 𝓝 x, T x' < 0 :=
    hT.continuousAt.eventually
      (gt_mem_nhds (by simpa only [T, flowHittingTime_self] using neg_neg_of_pos hτ₀))
  have heq : (fun x' ↦ Real.log (liouvilleRadialCoordinate Z W x')) =ᶠ[𝓝 x] fun x' ↦ -T x' := by
    filter_upwards [eventually_flowHittingTime (hZs.of_le (by simp)) hdom
      ((hfc _ hy₀).1.of_le (by simp)) (hfc _ hy₀).2.ne', hTneg] with x' h₁ h₂
    have hfr : flowOf Z (T x') x' ∈ frontier W := by
      rw [hfront]
      exact h₁.2.trans hy₀
    have := h.liouvilleRadialCoordinate_flowOf hZ hfr (neg_nonneg.2 h₂.le)
    rw [h.flowOf_flowOf hZ, neg_add_cancel, h.flowOf_zero hZ] at this
    rw [this, Real.log_exp]
  exact (contDiff_neg.contMDiff.contMDiffAt.comp x hT).congr_of_eventuallyEq heq

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
  have hcurve := hasDerivAt_comp_flowOf ((h.contMDiff_of_interior_eq hZ).of_le (by simp))
    ((h.isCompleteVectorField hZ).mem_flowDomain 0 x) hr
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
