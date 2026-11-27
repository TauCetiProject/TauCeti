/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Manifold.SMulGroupoid
public import TauCeti.Geometry.Toric.Algebraic.IntegralAffine

/-!
# The structure groupoid of integral affine chart changes

The structure groupoid of integral affine chart changes is the `TauCeti.smulGroupoid` of the
group of integral affine self-equivalences acting on the ambient space. A chart change whose
source is connected extends uniquely to one global integral affine equivalence; this follows from
the unique-extension theorems `IntegralAffineEquiv.existsUnique_extension` and
`IntegralAffineEquiv.existsUnique_extension_connectedComponentIn`. At a point in the
overlap of two maximal-atlas charts, the change has a unique affine representative.
These representatives are locally constant on the overlap and compose on triple overlaps.

Adapted from `yuma-mizuno-lean/Mei`, commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca`,
`Mei/Geometry/Manifold/IntegralAffine/Basic.lean` (Apache 2.0).
The pointwise chart changes are adapted from `yuma-mizuno-lean/Mei`, commit
`bf3986029ff4d3eb4025d4067489511b0724374e`,
`Mei/Geometry/Manifold/IntegralAffine/TangentLattice.lean` (Apache 2.0).
-/

public section

open Set Filter Topology Manifold

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : IsIntegralLattice i}

variable (h) in
/-- The structure groupoid of integral affine chart changes: open partial homeomorphisms of the
ambient space that are locally given by an integral affine self-equivalence. -/
abbrev integralAffineGroupoid : StructureGroupoid V :=
  smulGroupoid (IntegralAffineEquiv h h) V

/-- A partial homeomorphism lies in the integral affine groupoid iff it agrees near each point of
its source with an integral affine self-equivalence. -/
theorem mem_integralAffineGroupoid_iff {e : OpenPartialHomeomorph V V} :
    e ∈ integralAffineGroupoid h ↔
      ∀ x ∈ e.source, ∃ a : IntegralAffineEquiv h h, e =ᶠ[𝓝 x] a := by
  simp only [integralAffineGroupoid, mem_smulGroupoid_iff, IntegralAffineEquiv.smul_def]

/-- A connected nonempty chart-change domain has a unique global integral affine extension. -/
theorem existsUnique_extension_of_mem_integralAffineGroupoid
    {e : OpenPartialHomeomorph V V} (he : e ∈ integralAffineGroupoid h)
    (hc : IsConnected e.source) :
    ∃! a : IntegralAffineEquiv h h, EqOn e a e.source :=
  IntegralAffineEquiv.existsUnique_extension (mem_integralAffineGroupoid_iff.mp he)
    e.open_source hc

/-- Each connected component of the source of a chart change has a unique global integral
affine extension. -/
theorem existsUnique_extension_connectedComponentIn_of_mem_integralAffineGroupoid
    {e : OpenPartialHomeomorph V V} (he : e ∈ integralAffineGroupoid h) {x : V}
    (hx : x ∈ e.source) :
    ∃! a : IntegralAffineEquiv h h, EqOn e a (connectedComponentIn e.source x) :=
  IntegralAffineEquiv.existsUnique_extension_connectedComponentIn
    (mem_integralAffineGroupoid_iff.mp he) e.open_source hx

variable {B : Type*} [TopologicalSpace B] [ChartedSpace V B]

private theorem chartChangeAt_exists {e e' : (integralAffineGroupoid h).maximalAtlas B}
    {x : B} (hx : x ∈ e.val.source ∩ e'.val.source) :
    ∃ a : IntegralAffineEquiv h h, (e.val.symm ≫ₕ e'.val : V → V) =ᶠ[𝓝 (e.val x)] a :=
  mem_integralAffineGroupoid_iff.mp
    ((integralAffineGroupoid h).compatible_of_mem_maximalAtlas e.property e'.property)
    (e.val x) (PartialEquiv.mem_symm_trans_source e.val.toPartialEquiv hx.1 hx.2)

/-- The integral affine equivalence representing the change of charts near the
coordinate of a point on their overlap. -/
noncomputable def chartChangeAt {e e' : (integralAffineGroupoid h).maximalAtlas B} {x : B}
    (hx : x ∈ e.val.source ∩ e'.val.source) : IntegralAffineEquiv h h :=
  (chartChangeAt_exists hx).choose

/-- The chosen integral affine equivalence agrees locally with the chart transition. -/
theorem eventuallyEq_chartChangeAt {e e' : (integralAffineGroupoid h).maximalAtlas B} {x : B}
    (hx : x ∈ e.val.source ∩ e'.val.source) :
    (e.val.symm ≫ₕ e'.val : V → V) =ᶠ[𝓝 (e.val x)] (chartChangeAt (h := h) hx : V → V) :=
  (chartChangeAt_exists hx).choose_spec

/-- Any integral affine equivalence with the same germ is the chosen chart change. -/
theorem chartChangeAt_eq {e e' : (integralAffineGroupoid h).maximalAtlas B} {x : B}
    (hx : x ∈ e.val.source ∩ e'.val.source) {a : IntegralAffineEquiv h h}
    (ha : (e.val.symm ≫ₕ e'.val : V → V) =ᶠ[𝓝 (e.val x)] (a : V → V)) :
    chartChangeAt hx = a :=
  IntegralAffineEquiv.eq_of_eventuallyEq ((eventuallyEq_chartChangeAt hx).symm.trans ha)

/-- The affine chart change maps the given point's coordinates to its new coordinates. -/
@[simp]
theorem chartChangeAt_apply {e e' : (integralAffineGroupoid h).maximalAtlas B} {x : B}
    (hx : x ∈ e.val.source ∩ e'.val.source) :
    chartChangeAt (h := h) hx (e.val x) = e'.val x := by
  rw [← (eventuallyEq_chartChangeAt (h := h) hx).eq_of_nhds,
    OpenPartialHomeomorph.trans_apply, e.val.left_inv hx.1]

/-- The affine chart change is locally constant on the overlap. -/
theorem eventually_chartChangeAt_eq {e e' : (integralAffineGroupoid h).maximalAtlas B} {x : B}
    (hx : x ∈ e.val.source ∩ e'.val.source) :
    ∀ᶠ y in 𝓝 x, ∀ hy : y ∈ e.val.source ∩ e'.val.source,
      chartChangeAt (h := h) hy = chartChangeAt hx :=
  ((e.val.continuousAt hx.1).eventually
    (eventuallyEq_chartChangeAt (h := h) hx).eventuallyEq_nhds).mono
      fun _ hg hy => chartChangeAt_eq hy hg

/-- The affine chart change is locally constant as a function on the overlap subtype. -/
theorem isLocallyConstant_chartChangeAt {e e' : (integralAffineGroupoid h).maximalAtlas B} :
    IsLocallyConstant
      (fun x : ↥(e.val.source ∩ e'.val.source) => chartChangeAt (h := h) x.property) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  have hc : ContinuousAt (Subtype.val : ↥(e.val.source ∩ e'.val.source) → B) x :=
    continuous_subtypeVal.continuousAt
  exact (hc.eventually (eventually_chartChangeAt_eq (h := h) x.property)).mono
    fun y hy => hy y.property

/-- The identity chart change has identity affine germ. -/
@[simp]
theorem chartChangeAt_self {e : (integralAffineGroupoid h).maximalAtlas B} {x : B}
    (hx : x ∈ e.val.source) :
    chartChangeAt (h := h) (e := e) (e' := e) ⟨hx, hx⟩ = 1 := by
  apply chartChangeAt_eq
  filter_upwards [e.val.eventually_right_inverse' hx] with y hy
  rw [OpenPartialHomeomorph.trans_apply, IntegralAffineEquiv.one_apply]
  exact hy

/-- On a triple overlap, the composition of two successive affine frame changes
is the direct frame change. -/
@[simp]
theorem chartChangeAt_mul {e e' e'' : (integralAffineGroupoid h).maximalAtlas B} {x : B}
    (hx : x ∈ e.val.source) (hx' : x ∈ e'.val.source) (hx'' : x ∈ e''.val.source) :
    chartChangeAt (h := h) ⟨hx', hx''⟩ * chartChangeAt (h := h) ⟨hx, hx'⟩ =
      chartChangeAt (h := h) ⟨hx, hx''⟩ := by
  let a := chartChangeAt (h := h) ⟨hx, hx'⟩
  have ha := eventuallyEq_chartChangeAt (h := h) (e := e) (e' := e') ⟨hx, hx'⟩
  have hb := eventuallyEq_chartChangeAt (h := h) (e := e') (e' := e'') ⟨hx', hx''⟩
  have ha_cont : Tendsto (a : V → V) (𝓝 (e.val x)) (𝓝 (e'.val x)) := by
    rw [← chartChangeAt_apply (h := h) (e := e) (e' := e') ⟨hx, hx'⟩]
    exact a.continuous.continuousAt
  have hcancel := (e.val.tendsto_symm hx).eventually (e'.val.eventually_left_inverse hx')
  symm
  apply chartChangeAt_eq
  filter_upwards [ha, hb.comp_tendsto ha_cont, hcancel] with y hay hby hy
  rw [OpenPartialHomeomorph.trans_apply] at hay
  simp only [Function.comp_apply, OpenPartialHomeomorph.trans_apply] at hby
  rw [← hay, hy, hay] at hby
  rw [OpenPartialHomeomorph.trans_apply, IntegralAffineEquiv.mul_apply]
  exact hby

/-- Reversing the order of the charts inverts the affine chart change. -/
@[simp]
theorem chartChangeAt_inv {e e' : (integralAffineGroupoid h).maximalAtlas B} {x : B}
    (hx : x ∈ e.val.source ∩ e'.val.source) :
    (chartChangeAt (h := h) hx)⁻¹ =
      chartChangeAt (h := h) (e := e') (e' := e) ⟨hx.2, hx.1⟩ := by
  apply inv_eq_of_mul_eq_one_left
  exact (chartChangeAt_mul (h := h) (e := e) (e' := e') (e'' := e) hx.1 hx.2 hx.1).trans
    (chartChangeAt_self (h := h) (e := e) hx.1)

end TauCeti.Toric
