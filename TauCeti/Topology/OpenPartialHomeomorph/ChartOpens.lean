/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.OpenPartialHomeomorph.Continuity
public import Mathlib.Topology.Sets.Opens

/-!
# Opens read in a chart and coordinate discs

For an open partial homeomorphism `e : X → Y`, this file introduces two families of opens:

* `OpenPartialHomeomorph.chartRead`: the open `e (V ∩ e.source)` of `Y` read from an open `V` of
  `X`, written as `e.target ∩ e.symm ⁻¹' V`. When `Y` is Hausdorff and `closure V'` is compact and
  lies in `V ⊆ e.source`, the read open of `V'` has compact closure inside that of `V`
  (`OpenPartialHomeomorph.isCompact_closure_chartRead_and_subset`).
* `OpenPartialHomeomorph.chartDisc`: for a metric codomain, the coordinate disc
  `e.source ∩ e ⁻¹' ball c r`. When `Y` is proper and `closedBall c r ⊆ e.target`, its closure is
  compact and lies in every coordinate disc of larger radius
  (`OpenPartialHomeomorph.isCompact_closure_chartDisc_and_subset`).
-/

public noncomputable section

open Set TopologicalSpace

namespace OpenPartialHomeomorph

variable {X : Type*} [TopologicalSpace X]

/-! ### Opens read in a chart -/

section Read

variable {Y : Type*} [TopologicalSpace Y]

/-- The open `e (V ∩ e.source)` of the codomain, written as `e.target ∩ e.symm ⁻¹' V`. -/
def chartRead (e : OpenPartialHomeomorph X Y) (V : Opens X) : Opens Y :=
  ⟨e.target ∩ e.symm ⁻¹' V, e.isOpen_inter_preimage_symm V.isOpen⟩

variable {e : OpenPartialHomeomorph X Y} {V V' : Opens X}

@[simp]
theorem coe_chartRead : (e.chartRead V : Set Y) = e.target ∩ e.symm ⁻¹' V := (rfl)

@[simp]
theorem mem_chartRead {z : Y} : z ∈ e.chartRead V ↔ z ∈ e.target ∧ e.symm z ∈ V := Iff.rfl

theorem chartRead_mono (h : V ≤ V') : e.chartRead V ≤ e.chartRead V' :=
  fun _ hz ↦ ⟨hz.1, h hz.2⟩

/-- A point of `V ⊆ e.source` is read in the chart as a point of `e.chartRead V`. -/
theorem map_mem_chartRead (hV : (V : Set X) ⊆ e.source) {x : X} (hx : x ∈ V) :
    e x ∈ e.chartRead V :=
  mem_chartRead.2 ⟨e.map_source (hV hx), by rwa [e.left_inv (hV hx)]⟩

/-- If `closure V'` is compact and lies in `V ⊆ e.source`, the open read from `V'` has compact
closure inside the open read from `V`. -/
theorem isCompact_closure_chartRead_and_subset [T2Space Y] (hV : (V : Set X) ⊆ e.source)
    (hK : IsCompact (closure (V' : Set X))) (hKV : closure (V' : Set X) ⊆ V) :
    IsCompact (closure (e.chartRead V' : Set Y)) ∧
      closure (e.chartRead V' : Set Y) ⊆ e.chartRead V := by
  have hKc : IsCompact (e '' closure (V' : Set X)) :=
    hK.image_of_continuousOn (e.continuousOn.mono (hKV.trans hV))
  have hcl : closure (e.chartRead V' : Set Y) ⊆ e '' closure (V' : Set X) :=
    closure_minimal (fun z hz ↦ ⟨e.symm z, subset_closure hz.2, e.right_inv hz.1⟩) hKc.isClosed
  refine ⟨hKc.of_isClosed_subset isClosed_closure hcl, hcl.trans ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact map_mem_chartRead hV (hKV hx)

end Read

/-! ### Coordinate discs -/

section Disc

variable {Y : Type*} [PseudoMetricSpace Y] {e : OpenPartialHomeomorph X Y}

/-- The coordinate disc `e.source ∩ e ⁻¹' ball c r`. -/
def chartDisc (e : OpenPartialHomeomorph X Y) (c : Y) (r : ℝ) : Opens X :=
  ⟨e.source ∩ e ⁻¹' Metric.ball c r, e.isOpen_inter_preimage Metric.isOpen_ball⟩

@[simp]
theorem coe_chartDisc {c : Y} {r : ℝ} :
    (e.chartDisc c r : Set X) = e.source ∩ e ⁻¹' Metric.ball c r := (rfl)

@[simp]
theorem mem_chartDisc {c : Y} {r : ℝ} {x : X} :
    x ∈ e.chartDisc c r ↔ x ∈ e.source ∧ e x ∈ Metric.ball c r := Iff.rfl

theorem chartDisc_subset_source {c : Y} {r : ℝ} : (e.chartDisc c r : Set X) ⊆ e.source :=
  inter_subset_left

/-- If `closedBall c r` lies in the chart target, the coordinate disc of radius `r` has compact
closure, contained in the coordinate disc of any larger radius. -/
theorem isCompact_closure_chartDisc_and_subset [T2Space X] [ProperSpace Y] {c : Y}
    {r s : ℝ}
    (hr : Metric.closedBall c r ⊆ e.target) (hrs : r < s) :
    IsCompact (closure (e.chartDisc c r : Set X)) ∧
      closure (e.chartDisc c r : Set X) ⊆ e.chartDisc c s := by
  have hK : IsCompact (e.symm '' Metric.closedBall c r) :=
    (isCompact_closedBall c r).image_of_continuousOn (e.continuousOn_symm.mono hr)
  have hcl : closure (e.chartDisc c r : Set X) ⊆ e.symm '' Metric.closedBall c r :=
    closure_minimal (fun x hx ↦ ⟨e x, Metric.ball_subset_closedBall hx.2, e.left_inv hx.1⟩)
      hK.isClosed
  refine ⟨hK.of_isClosed_subset isClosed_closure hcl, hcl.trans ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact mem_chartDisc.2 ⟨e.map_target (hr hz), by
    rw [e.right_inv (hr hz)]; exact Metric.closedBall_subset_ball hrs hz⟩

end Disc

end OpenPartialHomeomorph
