/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Basic
public import TauCeti.Geometry.Symplectic.Liouville.CylindricalEnd
import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow

/-!
# The Liouville retraction of a completion onto its Liouville domain

Let `M` be a completion of the Liouville domain `W` (`TauCeti.IsLiouvilleCompletion`), with
Liouville field `Z`, Liouville flow `ψ` and radial coordinate `r`
(`TauCeti.liouvilleRadialCoordinate`). Every point `x` outside the interior of `W` lies on the
trajectory of exactly one boundary point, reached at time `log r(x)`. Flowing back for that time is
the **Liouville retraction** (`TauCeti.liouvilleRetraction`)

`π(x) = ψ_{-log r(x)}(x)`,

which is the identity on `W` (`TauCeti.IsLiouvilleCompletion.liouvilleRetraction_of_mem`) and sends
the cylindrical end `M \ int W` to the boundary `∂W`
(`TauCeti.IsLiouvilleCompletion.liouvilleRetraction_mem_frontier`), constantly along each Liouville
trajectory (`TauCeti.IsLiouvilleCompletion.liouvilleRetraction_flowOf_of_notMem_interior`). In the
coordinates `(t, y) ↦ ψ_t(y)` of the cylindrical end it is the projection to `y`. It is continuous
on `M` (`TauCeti.IsLiouvilleCompletion.continuous_liouvilleRetraction`) and smooth outside `W`
(`TauCeti.IsLiouvilleCompletion.contMDiffAt_liouvilleRetraction`).

Flowing back for the times `s log r(x)`, `s ∈ [0, 1]`, deforms the identity of `M` into the
Liouville retraction, relative to `W` (`TauCeti.IsLiouvilleCompletion.liouvilleRetractionHomotopy`):
so `W` is a strong deformation retract of its completion. Along this homotopy the time coordinate
`log r` decreases linearly to `0`
(`TauCeti.IsLiouvilleCompletion.log_liouvilleRadialCoordinate_liouvilleRetractionHomotopy`) and the
retraction does not change
(`TauCeti.IsLiouvilleCompletion.liouvilleRetraction_liouvilleRetractionHomotopy`), so the homotopy
preserves every region of the completion described by an upper bound on `r` that depends only on
the retraction, such as the domain bounded by a Liouville graph over `∂W`.

## Main definitions

* `TauCeti.liouvilleRetraction Z W`: the map `x ↦ ψ_{-log r(x)}(x)`.
* `TauCeti.IsLiouvilleCompletion.liouvilleRetractionHomotopy`: the homotopy
  `(s, x) ↦ ψ_{-s log r(x)}(x)` from the identity to the Liouville retraction, relative to `W`.

## References

* P. Seidel, *A biased view of symplectic cohomology*, Current Developments in Mathematics 2006,
  Section 3 (completions of Liouville domains).
* K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*, AMS Colloquium Publications 59,
  2012, Section 11.1.
-/

public section

open Filter Set
open scoped Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {Z : (x : M) → TangentSpace I x} {W : Set M}

variable (Z W) in
/-- The **Liouville retraction** of a completion of the Liouville domain `W` with Liouville field
`Z`: the point `x` flowed back for the time `log r(x)`, where `r` is the radial coordinate. It is
the identity on `W` (`TauCeti.IsLiouvilleCompletion.liouvilleRetraction_of_mem`), and it sends a
point of the cylindrical end to the boundary point of its Liouville trajectory
(`TauCeti.IsLiouvilleCompletion.liouvilleRetraction_mem_frontier`). -/
noncomputable def liouvilleRetraction (x : M) : M :=
  flowOf Z (-Real.log (liouvilleRadialCoordinate Z W x)) x

theorem liouvilleRetraction_apply (x : M) :
    liouvilleRetraction Z W x = flowOf Z (-Real.log (liouvilleRadialCoordinate Z W x)) x :=
  (rfl)

namespace IsLiouvilleCompletion

variable [IsManifold I (⊤ : ℕ∞) M] [FiniteDimensional ℝ E] [T2Space M] [I.Boundaryless]
  {ω : SmoothTwoForm I M} {α : SmoothForm I M ℝ 1} {x y : M} {t : ℝ}

/-! ### The Liouville retraction -/

section Retraction

variable (h : IsLiouvilleCompletion ω α W) (hZ : RoughForm.interior Z ω.val = α.val)
include h hZ

/-- The Liouville retraction is the identity on the Liouville domain. -/
theorem liouvilleRetraction_of_mem (hx : x ∈ W) : liouvilleRetraction Z W x = x := by
  rw [liouvilleRetraction_apply, (h.liouvilleRadialCoordinate_eq_one_iff hZ).2 hx, Real.log_one,
    neg_zero, flowOf_zero Z]

/-- The Liouville retraction sends a point outside the interior of the Liouville domain to the
boundary. -/
theorem liouvilleRetraction_mem_frontier (hx : x ∉ interior W) :
    liouvilleRetraction Z W x ∈ frontier W :=
  h.flowOf_neg_log_liouvilleRadialCoordinate_mem_frontier hZ hx

/-- The Liouville retraction takes its values in the Liouville domain. -/
theorem liouvilleRetraction_mem (x : M) : liouvilleRetraction Z W x ∈ W := by
  by_cases hx : x ∈ interior W
  · rw [h.liouvilleRetraction_of_mem hZ (interior_subset hx)]
    exact interior_subset hx
  · exact h.isClosed.frontier_subset (h.liouvilleRetraction_mem_frontier hZ hx)

omit [FiniteDimensional ℝ E] in
/-- **A point is the Liouville flow of its retraction**: flowing the Liouville retraction of `x`
forward for the time `log r(x)` gives back `x`. -/
theorem flowOf_log_liouvilleRadialCoordinate_liouvilleRetraction (x : M) :
    flowOf Z (Real.log (liouvilleRadialCoordinate Z W x)) (liouvilleRetraction Z W x) = x := by
  rw [liouvilleRetraction_apply, h.flowOf_flowOf hZ, add_neg_cancel, flowOf_zero Z]

/-- The Liouville retraction of the point reached from a boundary point `y` at a time `t ≥ 0` is
`y`. -/
theorem liouvilleRetraction_flowOf (hy : y ∈ frontier W) (ht : 0 ≤ t) :
    liouvilleRetraction Z W (flowOf Z t y) = y := by
  rw [liouvilleRetraction_apply, h.liouvilleRadialCoordinate_flowOf hZ hy ht, Real.log_exp,
    h.flowOf_flowOf hZ, neg_add_cancel, flowOf_zero Z]

/-- **The Liouville retraction is constant along the Liouville trajectories** of the cylindrical
end: if `x` lies outside the interior of the Liouville domain and `0 ≤ log r(x) + t`, then `ψ_t(x)`
has the same retraction as `x`. -/
theorem liouvilleRetraction_flowOf_of_notMem_interior (hx : x ∉ interior W)
    (ht : 0 ≤ Real.log (liouvilleRadialCoordinate Z W x) + t) :
    liouvilleRetraction Z W (flowOf Z t x) = liouvilleRetraction Z W x := by
  obtain ⟨y, hy, s, hs, rfl⟩ := h.exists_mem_frontier_flowOf_eq hZ hx
  rw [h.liouvilleRadialCoordinate_flowOf hZ hy hs, Real.log_exp] at ht
  rw [h.flowOf_flowOf hZ, h.liouvilleRetraction_flowOf hZ hy (by linarith),
    h.liouvilleRetraction_flowOf hZ hy hs]

/-- The Liouville retraction of a completion is continuous. -/
theorem continuous_liouvilleRetraction : Continuous (liouvilleRetraction Z W) := by
  obtain ⟨ψ, hψ⟩ := h.exists_flow_eq hZ
  simp only [funext liouvilleRetraction_apply, hψ]
  exact ψ.continuous ((h.continuous_liouvilleRadialCoordinate hZ).log
    fun x ↦ (liouvilleRadialCoordinate_pos Z W x).ne').neg continuous_id

/-- The Liouville retraction is smooth outside the Liouville domain. -/
theorem contMDiffAt_liouvilleRetraction (hx : x ∉ W) :
    ContMDiffAt I I (⊤ : ℕ∞) (liouvilleRetraction Z W) x := by
  have hZs := h.contMDiff_of_interior_eq hZ
  have hc := h.isCompleteVectorField hZ
  have hψ := flowOf_eq_globalFlow (hZs.of_le (by simp)) hc
  -- The retraction is the smooth global flow evaluated at the smooth time `-log r`.
  have hτ : ContMDiffAt I 𝓘(ℝ) (⊤ : ℕ∞)
      (fun x' ↦ -Real.log (liouvilleRadialCoordinate Z W x')) x :=
    contDiff_neg.contMDiff.contMDiffAt.comp x (h.contMDiffAt_log_liouvilleRadialCoordinate hZ hx)
  have hflow := (contMDiff_globalFlow_uncurry hc le_top hZs).contMDiffAt.comp x
    (hτ.prodMk contMDiffAt_id)
  refine hflow.congr_of_eventuallyEq (Eventually.of_forall fun x' ↦ ?_)
  rw [liouvilleRetraction_apply, hψ]
  rfl

end Retraction

/-! ### The deformation retraction onto the Liouville domain -/

section Homotopy

variable (h : IsLiouvilleCompletion ω α W) (hZ : RoughForm.interior Z ω.val = α.val)

/-- **The Liouville deformation retraction.** On a completion of the Liouville domain `W`, flowing
each point `x` back for the time `s log r(x)`, `s ∈ [0, 1]`, is a homotopy from the identity to the
Liouville retraction, relative to `W`: the points of `W` have `log r = 0` and do not move. So `W` is
a strong deformation retract of its completion. -/
noncomputable def liouvilleRetractionHomotopy :
    ContinuousMap.HomotopyRel (ContinuousMap.id M)
      ⟨liouvilleRetraction Z W, h.continuous_liouvilleRetraction hZ⟩ W where
  toFun p := flowOf Z (-((p.1 : ℝ) * Real.log (liouvilleRadialCoordinate Z W p.2))) p.2
  continuous_toFun := by
    obtain ⟨ψ, hψ⟩ := h.exists_flow_eq hZ
    simp only [hψ]
    exact ψ.continuous ((continuous_subtypeVal.comp continuous_fst).mul
      (((h.continuous_liouvilleRadialCoordinate hZ).comp continuous_snd).log
        fun p ↦ (liouvilleRadialCoordinate_pos Z W p.2).ne')).neg continuous_snd
  map_zero_left x := by simp
  map_one_left x := by simp [liouvilleRetraction_apply]
  prop' s x hx := by
    simp [(h.liouvilleRadialCoordinate_eq_one_iff hZ).2 hx]

@[simp]
theorem liouvilleRetractionHomotopy_apply (p : unitInterval × M) :
    h.liouvilleRetractionHomotopy hZ p =
      flowOf Z (-((p.1 : ℝ) * Real.log (liouvilleRadialCoordinate Z W p.2))) p.2 :=
  (rfl)

include h hZ

/-- Along the Liouville deformation retraction, the time coordinate `log r` decreases linearly to
`0`: at the time `s` of the homotopy it is `(1 - s) log r(x)`. -/
theorem log_liouvilleRadialCoordinate_liouvilleRetractionHomotopy (p : unitInterval × M) :
    Real.log (liouvilleRadialCoordinate Z W (h.liouvilleRetractionHomotopy hZ p)) =
      (1 - p.1) * Real.log (liouvilleRadialCoordinate Z W p.2) := by
  have h0 := Real.log_nonneg (one_le_liouvilleRadialCoordinate Z W p.2)
  have hs := sub_nonneg.2 (unitInterval.le_one p.1)
  by_cases hx : p.2 ∈ interior W
  · simp [(h.liouvilleRadialCoordinate_eq_one_iff hZ).2 (interior_subset hx)]
  · rw [liouvilleRetractionHomotopy_apply,
      h.log_liouvilleRadialCoordinate_flowOf hZ hx (by nlinarith)]
    ring

/-- The Liouville deformation retraction does not move the Liouville retraction: each point stays
on its Liouville trajectory. -/
theorem liouvilleRetraction_liouvilleRetractionHomotopy (p : unitInterval × M) :
    liouvilleRetraction Z W (h.liouvilleRetractionHomotopy hZ p) = liouvilleRetraction Z W p.2 := by
  have h0 := Real.log_nonneg (one_le_liouvilleRadialCoordinate Z W p.2)
  have hs := sub_nonneg.2 (unitInterval.le_one p.1)
  by_cases hx : p.2 ∈ interior W
  · simp [(h.liouvilleRadialCoordinate_eq_one_iff hZ).2 (interior_subset hx)]
  · rw [liouvilleRetractionHomotopy_apply,
      h.liouvilleRetraction_flowOf_of_notMem_interior hZ hx (by nlinarith)]

end Homotopy

end IsLiouvilleCompletion

end TauCeti
