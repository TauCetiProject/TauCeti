/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code, Codex
-/
module

public import TauCeti.Geometry.Manifold.IntegralAffine.Basic
public import Mathlib.Geometry.Manifold.HasGroupoid

/-!
# Integral tangent frame changes

An overlap of an integral affine atlas determines a unique affine germ at each point.
The lattice parts of these germs are locally constant and obey the cocycle identity,
so they supply the transition functions of the integral tangent lattice.

Adapted from `yuma-mizuno-lean/Mei`, commit
`bf3986029ff4d3eb4025d4067489511b0724374e`,
`Mei/Geometry/Manifold/IntegralAffine/TangentLattice.lean` (Apache 2.0).
-/

public section

open Set Filter Topology Manifold

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : IsIntegralLattice i}
  {B : Type*} [TopologicalSpace B] [ChartedSpace V B]
  [HasGroupoid B (integralAffineGroupoid h)]

private theorem eq_of_eventuallyEq_integralAffineEquiv {a b : IntegralAffineEquiv h h} {x : V}
    (hab : (a : V → V) =ᶠ[𝓝 x] b) : a = b := by
  obtain ⟨u, hu, huo, hxu⟩ := mem_nhds_iff.mp hab
  exact IntegralAffineEquiv.eq_of_eqOn_open huo ⟨x, hxu⟩ hu

/-- The integral affine equivalence representing the change of charts near the
coordinate of a point on their overlap. -/
noncomputable def chartChangeAt {e e' : atlas V B} {x : B}
    (hx : x ∈ e.val.source ∩ e'.val.source) : IntegralAffineEquiv h h :=
  (mem_integralAffineGroupoid_iff.mp ((integralAffineGroupoid h).compatible e.property e'.property)
    (e.val x) (PartialEquiv.mem_symm_trans_source e.val.toPartialEquiv hx.1 hx.2)).choose

/-- The chosen integral affine equivalence agrees locally with the chart transition. -/
theorem eventuallyEq_chartChangeAt {e e' : atlas V B} {x : B}
    (hx : x ∈ e.val.source ∩ e'.val.source) :
    (e.val.symm ≫ₕ e'.val : V → V) =ᶠ[𝓝 (e.val x)] (chartChangeAt (h := h) hx : V → V) :=
  (mem_integralAffineGroupoid_iff.mp ((integralAffineGroupoid h).compatible e.property e'.property)
    (e.val x) (PartialEquiv.mem_symm_trans_source e.val.toPartialEquiv hx.1 hx.2)).choose_spec

/-- Any integral affine equivalence with the same germ is the chosen chart change. -/
theorem chartChangeAt_eq {e e' : atlas V B} {x : B}
    (hx : x ∈ e.val.source ∩ e'.val.source) {a : IntegralAffineEquiv h h}
    (ha : (e.val.symm ≫ₕ e'.val : V → V) =ᶠ[𝓝 (e.val x)] (a : V → V)) :
    chartChangeAt hx = a :=
  eq_of_eventuallyEq_integralAffineEquiv ((eventuallyEq_chartChangeAt hx).symm.trans ha)

/-- The affine chart change maps the given point's coordinates to its new coordinates. -/
@[simp]
theorem chartChangeAt_apply {e e' : atlas V B} {x : B}
    (hx : x ∈ e.val.source ∩ e'.val.source) :
    chartChangeAt (h := h) hx (e.val x) = e'.val x := by
  rw [← (eventuallyEq_chartChangeAt (h := h) hx).eq_of_nhds,
    OpenPartialHomeomorph.trans_apply, e.val.left_inv hx.1]

/-- The affine chart change is locally constant on the overlap. -/
theorem eventually_chartChangeAt_eq {e e' : atlas V B} {x : B}
    (hx : x ∈ e.val.source ∩ e'.val.source) :
    ∀ᶠ y in 𝓝 x, ∀ hy : y ∈ e.val.source ∩ e'.val.source,
      chartChangeAt (h := h) hy = chartChangeAt hx := by
  obtain ⟨u, hu, huo, hxu⟩ := mem_nhds_iff.mp (eventuallyEq_chartChangeAt (h := h) hx)
  filter_upwards [(e.val.continuousAt hx.1).eventually (huo.mem_nhds hxu)] with y hyu hy
  apply chartChangeAt_eq hy
  filter_upwards [huo.mem_nhds hyu] with z hz
  exact hu hz

/-- The identity chart change has identity affine germ. -/
@[simp]
theorem chartChangeAt_self {e : atlas V B} {x : B} (hx : x ∈ e.val.source) :
    chartChangeAt (h := h) (e := e) (e' := e) ⟨hx, hx⟩ = 1 := by
  apply chartChangeAt_eq
  filter_upwards [e.val.open_target.mem_nhds (e.val.map_source hx)] with y hy
  rw [OpenPartialHomeomorph.trans_apply, e.val.right_inv hy, IntegralAffineEquiv.one_apply]

/-- On a triple overlap, the composition of two successive affine frame changes
is the direct frame change. -/
theorem chartChangeAt_mul {e e' e'' : atlas V B} {x : B}
    (hx : x ∈ e.val.source) (hx' : x ∈ e'.val.source) (hx'' : x ∈ e''.val.source) :
    chartChangeAt (h := h) ⟨hx', hx''⟩ * chartChangeAt (h := h) ⟨hx, hx'⟩ =
      chartChangeAt (h := h) ⟨hx, hx''⟩ := by
  let a := chartChangeAt (h := h) ⟨hx, hx'⟩
  let b := chartChangeAt (h := h) ⟨hx', hx''⟩
  have ha := eventuallyEq_chartChangeAt (h := h) (e := e) (e' := e') ⟨hx, hx'⟩
  have hb := eventuallyEq_chartChangeAt (h := h) (e := e') (e' := e'') ⟨hx', hx''⟩
  have ha_cont : Tendsto (a : V → V) (𝓝 (e.val x)) (𝓝 (e'.val x)) := by
    rw [← chartChangeAt_apply (h := h) (e := e) (e' := e') ⟨hx, hx'⟩]
    exact a.continuous.continuousAt
  have hoverlap := (e.val.isOpen_inter_preimage_symm e'.val.open_source).mem_nhds
    ⟨e.val.map_source hx, by simpa only [mem_preimage, e.val.left_inv hx] using hx'⟩
  symm
  apply chartChangeAt_eq
  filter_upwards [ha, hb.comp_tendsto ha_cont, hoverlap] with y hay hby hy
  rw [OpenPartialHomeomorph.trans_apply] at hay
  change e''.val (e'.val.symm (a y)) = b (a y) at hby
  rw [← hay, e'.val.left_inv hy.2, hay] at hby
  rw [OpenPartialHomeomorph.trans_apply, IntegralAffineEquiv.mul_apply]
  exact hby

/-- The integral linear part of the affine chart change gives the transition
between the two tangent lattice frames. -/
noncomputable def tangentLatticeChange {e e' : atlas V B} {x : B}
    (hx : x ∈ e.val.source ∩ e'.val.source) : N ≃+ N :=
  (chartChangeAt (h := h) hx).latticeEquiv

/-- Tangent frame changes are locally constant along the overlap. -/
theorem eventually_tangentLatticeChange_eq {e e' : atlas V B} {x : B}
    (hx : x ∈ e.val.source ∩ e'.val.source) :
    ∀ᶠ y in 𝓝 x, ∀ hy : y ∈ e.val.source ∩ e'.val.source,
      tangentLatticeChange (h := h) (e := e) (e' := e') hy = tangentLatticeChange (h := h) hx :=
  (eventually_chartChangeAt_eq (h := h) hx).mono fun _ hy hz =>
    congrArg IntegralAffineEquiv.latticeEquiv (hy hz)

/-- A chart is related to itself by the identity tangent frame change. -/
@[simp]
theorem tangentLatticeChange_self {e : atlas V B} {x : B} (hx : x ∈ e.val.source) :
    tangentLatticeChange (h := h) (e := e) (e' := e) ⟨hx, hx⟩ = AddEquiv.refl N := by
  simpa only [tangentLatticeChange, IntegralAffineEquiv.one_latticeEquiv] using
    congrArg IntegralAffineEquiv.latticeEquiv (chartChangeAt_self (h := h) (e := e) hx)

/-- On a triple overlap, changing the integral lattice frame twice agrees with the
direct change. -/
theorem tangentLatticeChange_trans {e e' e'' : atlas V B} {x : B}
    (hx : x ∈ e.val.source) (hx' : x ∈ e'.val.source) (hx'' : x ∈ e''.val.source) :
    (tangentLatticeChange (h := h) ⟨hx, hx'⟩).trans
        (tangentLatticeChange (h := h) ⟨hx', hx''⟩) =
      tangentLatticeChange (h := h) ⟨hx, hx''⟩ := by
  simpa only [tangentLatticeChange, IntegralAffineEquiv.mul_latticeEquiv] using
    congrArg IntegralAffineEquiv.latticeEquiv
      (chartChangeAt_mul (h := h) (e := e) (e' := e') (e'' := e'') hx hx' hx'')

end TauCeti.Toric
