/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code, Codex
-/
module

public import TauCeti.Geometry.Manifold.IntegralAffine.Basic

/-!
# Integral tangent frame changes

An overlap of maximal integral affine charts determines a unique affine germ at each point.
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

/-- The integral linear part of the affine chart change gives the transition
between the two tangent lattice frames. -/
noncomputable def tangentLatticeChange {e e' : (integralAffineGroupoid h).maximalAtlas B} {x : B}
    (hx : x ∈ e.val.source ∩ e'.val.source) : N ≃+ N :=
  (chartChangeAt (h := h) hx).latticeEquiv

/-- The tangent frame change is the lattice equivalence of the affine chart change. -/
@[simp ←]
theorem tangentLatticeChange_def {e e' : (integralAffineGroupoid h).maximalAtlas B} {x : B}
    (hx : x ∈ e.val.source ∩ e'.val.source) :
    tangentLatticeChange (h := h) hx = (chartChangeAt (h := h) hx).latticeEquiv := (rfl)

/-- On integral lattice vectors, the affine chart change acts linearly by the tangent
frame change. -/
theorem chartChangeAt_linear_apply_lattice
    {e e' : (integralAffineGroupoid h).maximalAtlas B} {x : B}
    (hx : x ∈ e.val.source ∩ e'.val.source) (n : N) :
    (chartChangeAt (h := h) hx).toAffineEquiv.linear (i n) =
      i (tangentLatticeChange (h := h) hx n) := by
  simpa only [← tangentLatticeChange_def] using (chartChangeAt (h := h) hx).map_lattice n

/-- Tangent frame changes are locally constant along the overlap. -/
theorem eventually_tangentLatticeChange_eq {e e' : (integralAffineGroupoid h).maximalAtlas B}
    {x : B} (hx : x ∈ e.val.source ∩ e'.val.source) :
    ∀ᶠ y in 𝓝 x, ∀ hy : y ∈ e.val.source ∩ e'.val.source,
      tangentLatticeChange (h := h) (e := e) (e' := e') hy = tangentLatticeChange (h := h) hx :=
  (eventually_chartChangeAt_eq (h := h) hx).mono fun _ hy hz =>
    congrArg IntegralAffineEquiv.latticeEquiv (hy hz)

/-- The tangent frame change is locally constant as a function on the overlap subtype. -/
theorem isLocallyConstant_tangentLatticeChange
    {e e' : (integralAffineGroupoid h).maximalAtlas B} :
    IsLocallyConstant
      (fun x : ↥(e.val.source ∩ e'.val.source) => tangentLatticeChange (h := h) x.property) :=
  (isLocallyConstant_chartChangeAt (h := h) (e := e) (e' := e')).comp
    IntegralAffineEquiv.latticeEquiv

/-- The inverse tangent frame change is the change with the charts exchanged. -/
@[simp]
theorem tangentLatticeChange_symm {e e' : (integralAffineGroupoid h).maximalAtlas B} {x : B}
    (hx : x ∈ e.val.source ∩ e'.val.source) :
    (tangentLatticeChange (h := h) hx).symm =
      tangentLatticeChange (h := h) (e := e') (e' := e) ⟨hx.2, hx.1⟩ := by
  rw [tangentLatticeChange_def (h := h) hx,
    tangentLatticeChange_def (h := h) (e := e') (e' := e) ⟨hx.2, hx.1⟩,
    ← IntegralAffineEquiv.inv_latticeEquiv, chartChangeAt_inv (h := h) hx]

/-- A chart is related to itself by the identity tangent frame change. -/
@[simp]
theorem tangentLatticeChange_self {e : (integralAffineGroupoid h).maximalAtlas B} {x : B}
    (hx : x ∈ e.val.source) :
    tangentLatticeChange (h := h) (e := e) (e' := e) ⟨hx, hx⟩ = AddEquiv.refl N := by
  simpa only [tangentLatticeChange, IntegralAffineEquiv.one_latticeEquiv] using
    congrArg IntegralAffineEquiv.latticeEquiv (chartChangeAt_self (h := h) (e := e) hx)

/-- On a triple overlap, changing the integral lattice frame twice agrees with the
direct change. -/
theorem tangentLatticeChange_trans {e e' e'' : (integralAffineGroupoid h).maximalAtlas B} {x : B}
    (hx : x ∈ e.val.source) (hx' : x ∈ e'.val.source) (hx'' : x ∈ e''.val.source) :
    (tangentLatticeChange (h := h) ⟨hx, hx'⟩).trans
        (tangentLatticeChange (h := h) ⟨hx', hx''⟩) =
      tangentLatticeChange (h := h) ⟨hx, hx''⟩ := by
  simpa only [tangentLatticeChange, IntegralAffineEquiv.mul_latticeEquiv] using
    congrArg IntegralAffineEquiv.latticeEquiv
      (chartChangeAt_mul (h := h) (e := e) (e' := e') (e'' := e'') hx hx' hx'')

end TauCeti.Toric
