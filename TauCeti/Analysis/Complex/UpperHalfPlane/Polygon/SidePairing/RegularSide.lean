/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Geometry
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.RegularSide

/-!
# Local coverage across regular paired sides

The polygon and its adjacent paired translate contain a neighbourhood of every point on the
paired side other than its finite endpoints. Convexity supplies the strict inequalities against
all the other supporting geodesics in both tiles, so no extra side-inequality hypotheses are
required. Ideal endpoints lie outside the upper half-plane and are automatically excluded.

This is the local edge-coverage step in constructing a tessellation from side pairings; coverage
at vertices still requires the cycle conditions.

## References

Beardon, *The Geometry of Discrete Groups*, Chapter 9; Walkden, *Hyperbolic geometry*
(MATH32052 lecture notes, Manchester 2019), §§19–20 (Poincaré's polygon theorem).
-/

public section

open Set Topology UpperHalfPlane
open scoped MatrixGroups Pointwise

namespace TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing

variable {n : ℕ} [NeZero n] {P : ConvexPolygon n} (σ : P.SidePairing)

/-- At every point of the paired side other than its finite endpoints, the polygon and its
adjacent paired translate together contain a neighbourhood. -/
theorem mem_interior_union_smul_carrier_of_mem_side (i : Fin n) {z : ℍ}
    (hz : z ∈ P.side (σ.pair i)) (hzi : Sum.inl z ≠ P.vertex (σ.pair i))
    (hzi' : Sum.inl z ≠ P.vertex (σ.pair i + 1)) :
    z ∈ interior (P.carrier ∪ (σ.map i • P.carrier)) := by
  have hzinv : (σ.map i)⁻¹ • z ∈ P.side i := by
    rw [← σ.map_smul_side, Set.mem_smul_set_iff_inv_smul_mem] at hz
    exact hz
  have hvinv : Sum.inl ((σ.map i)⁻¹ • z) ≠ P.vertex i := by
    intro h
    apply hzi'
    have h' := congrArg (fun v : ℍ ⊕ OnePoint ℝ ↦ σ.map i • v) h
    simpa only [Sum.smul_inl, smul_inv_smul, σ.map_smul_vertex] using h'
  have hvinv' : Sum.inl ((σ.map i)⁻¹ • z) ≠ P.vertex (i + 1) := by
    intro h
    apply hzi
    have h' := congrArg (fun v : ℍ ⊕ OnePoint ℝ ↦ σ.map i • v) h
    simpa only [Sum.smul_inl, smul_inv_smul, σ.map_smul_vertex_add_one] using h'
  exact σ.mem_interior_union_smul_carrier i
    (fun j hj ↦ P.mem_leftHalfPlane_of_mem_side hz hzi hzi' hj.symm)
    (fun j hj ↦ P.mem_leftHalfPlane_of_mem_side hzinv hvinv hvinv' hj.symm)

end TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing
