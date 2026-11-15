/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.OpenPartialHomeomorph.Continuity
public import Mathlib.Topology.Sets.Opens
import TauCeti.Topology.OpenPartialHomeomorph.Basic

/-!
# Images of opens and preimages of balls under an open partial homeomorphism

When `e : X → Y` is a chart of a manifold, open sets of `X` inside the chart source are read as
open sets of the model space `Y`, where function spaces such as Bergman spaces live; balls of a
metric model space pull back to coordinate balls of `X`. This file records both operations as
`Opens` and shows that they carry relatively compact inclusions, so that model-space function
spaces can be indexed by them and nested covers by coordinate balls can be built.

* `OpenPartialHomeomorph.imageOpens`: the open `e '' (e.source ∩ V)` of `Y` for an open `V` of
  `X`, written as `e.target ∩ e.symm ⁻¹' V`. When `Y` is R₁ and `closure V'` is compact and
  lies in `e.source`, `e.imageOpens V'` has compact closure
  (`OpenPartialHomeomorph.isCompact_closure_imageOpens`), contained in `e.imageOpens V` whenever
  `closure V' ⊆ V` (`OpenPartialHomeomorph.closure_imageOpens_subset`).
* `OpenPartialHomeomorph.preimageBall`: for a pseudometric codomain, the coordinate ball
  `e.source ∩ e ⁻¹' ball c r`, which is `e.symm.imageOpens (ball c r)`. When `X` is R₁,
  `Y` is proper and `closedBall c r ⊆ e.target`, its closure is compact
  (`OpenPartialHomeomorph.isCompact_closure_preimageBall`) and lies in the coordinate ball of any
  larger radius (`OpenPartialHomeomorph.closure_preimageBall_subset`).
-/

public noncomputable section

open Set TopologicalSpace

namespace OpenPartialHomeomorph

variable {X : Type*} [TopologicalSpace X]

/-! ### Images of opens -/

section Image

variable {Y : Type*} [TopologicalSpace Y]

/-- The open `e '' (e.source ∩ V)` of the codomain, written as `e.target ∩ e.symm ⁻¹' V`. -/
def imageOpens (e : OpenPartialHomeomorph X Y) (V : Opens X) : Opens Y :=
  ⟨e.target ∩ e.symm ⁻¹' V, e.isOpen_inter_preimage_symm V.isOpen⟩

variable {e : OpenPartialHomeomorph X Y} {V V' : Opens X}

@[simp]
theorem coe_imageOpens : (e.imageOpens V : Set Y) = e.target ∩ e.symm ⁻¹' V := (rfl)

@[simp]
theorem mem_imageOpens {z : Y} : z ∈ e.imageOpens V ↔ z ∈ e.target ∧ e.symm z ∈ V := Iff.rfl

theorem imageOpens_mono (h : V ≤ V') : e.imageOpens V ≤ e.imageOpens V' :=
  fun _ hz ↦ ⟨hz.1, h hz.2⟩

theorem imageOpens_subset_target : (e.imageOpens V : Set Y) ⊆ e.target :=
  inter_subset_left

/-- A point of `V` in the source of `e` maps to a point of `e.imageOpens V`. -/
theorem map_mem_imageOpens {x : X} (hxe : x ∈ e.source) (hx : x ∈ V) :
    e x ∈ e.imageOpens V :=
  mem_imageOpens.2 ⟨e.map_source hxe, by rwa [e.left_inv hxe]⟩

/-- If `closure V'` is compact and lies in `e.source`, the closure of `e.imageOpens V'` lies in the
image of `closure V'`. -/
theorem closure_imageOpens_subset_image [R1Space Y] (hK : IsCompact (closure (V' : Set X)))
    (hKe : closure (V' : Set X) ⊆ e.source) :
    closure (e.imageOpens V' : Set Y) ⊆ e '' closure (V' : Set X) :=
  closure_minimal (fun z hz ↦ ⟨e.symm z, subset_closure hz.2, e.right_inv hz.1⟩)
    (e.isClosed_image_of_closure_subset_target isClosed_closure hKe
      ((hK.image_of_continuousOn (e.continuousOn.mono hKe)).closure_subset_of_isOpen
        e.open_target (e.mapsTo.mono_left hKe).image_subset))

/-- If `closure V'` is compact and lies in `e.source`, `e.imageOpens V'` has compact closure. -/
theorem isCompact_closure_imageOpens [R1Space Y] (hK : IsCompact (closure (V' : Set X)))
    (hKe : closure (V' : Set X) ⊆ e.source) :
    IsCompact (closure (e.imageOpens V' : Set Y)) :=
  (hK.image_of_continuousOn (e.continuousOn.mono hKe)).closure_of_subset
    fun _ hz ↦ ⟨_, subset_closure hz.2, e.right_inv hz.1⟩

/-- If `closure V'` is compact and lies in `V` and in `e.source`, the closure of `e.imageOpens V'`
lies in `e.imageOpens V`. -/
theorem closure_imageOpens_subset [R1Space Y] (hK : IsCompact (closure (V' : Set X)))
    (hKe : closure (V' : Set X) ⊆ e.source) (hKV : closure (V' : Set X) ⊆ V) :
    closure (e.imageOpens V' : Set Y) ⊆ e.imageOpens V := by
  refine (closure_imageOpens_subset_image hK hKe).trans ?_
  rintro _ ⟨x, hx, rfl⟩
  exact map_mem_imageOpens (hKe hx) (hKV hx)

end Image

/-! ### Preimages of balls -/

section Ball

variable {Y : Type*} [PseudoMetricSpace Y] {e : OpenPartialHomeomorph X Y}

/-- The coordinate ball `e.source ∩ e ⁻¹' ball c r`, the image of `e.target ∩ ball c r` under
`e.symm`. -/
def preimageBall (e : OpenPartialHomeomorph X Y) (c : Y) (r : ℝ) : Opens X :=
  e.symm.imageOpens ⟨Metric.ball c r, Metric.isOpen_ball⟩

@[simp]
theorem coe_preimageBall {c : Y} {r : ℝ} :
    (e.preimageBall c r : Set X) = e.source ∩ e ⁻¹' Metric.ball c r := (rfl)

@[simp]
theorem mem_preimageBall {c : Y} {r : ℝ} {x : X} :
    x ∈ e.preimageBall c r ↔ x ∈ e.source ∧ e x ∈ Metric.ball c r := Iff.rfl

theorem preimageBall_subset_source {c : Y} {r : ℝ} : (e.preimageBall c r : Set X) ⊆ e.source :=
  e.symm.imageOpens_subset_target

/-- If `closedBall c r` lies in the chart target, the coordinate ball of radius `r` has compact
closure. -/
theorem isCompact_closure_preimageBall [R1Space X] [ProperSpace Y] {c : Y} {r : ℝ}
    (hr : Metric.closedBall c r ⊆ e.target) :
    IsCompact (closure (e.preimageBall c r : Set X)) :=
  e.symm.isCompact_closure_imageOpens
    ((isCompact_closedBall c r).of_isClosed_subset isClosed_closure
      Metric.closure_ball_subset_closedBall)
    (Metric.closure_ball_subset_closedBall.trans hr)

/-- If `closedBall c r` lies in the chart target, the closure of the coordinate ball of radius `r`
lies in the coordinate ball of any larger radius. -/
theorem closure_preimageBall_subset [R1Space X] [ProperSpace Y] {c : Y} {r s : ℝ}
    (hr : Metric.closedBall c r ⊆ e.target) (hrs : r < s) :
    closure (e.preimageBall c r : Set X) ⊆ e.preimageBall c s :=
  e.symm.closure_imageOpens_subset (V := ⟨Metric.ball c s, Metric.isOpen_ball⟩)
    ((isCompact_closedBall c r).of_isClosed_subset isClosed_closure
      Metric.closure_ball_subset_closedBall)
    (Metric.closure_ball_subset_closedBall.trans hr)
    (Metric.closure_ball_subset_closedBall.trans (Metric.closedBall_subset_ball hrs))

end Ball

end OpenPartialHomeomorph
