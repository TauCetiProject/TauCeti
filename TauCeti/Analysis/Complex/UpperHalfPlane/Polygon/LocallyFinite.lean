/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Basic
public import TauCeti.Topology.Algebra.ConstMulAction
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.GaussBonnet
import TauCeti.Topology.LocallyFinite

/-!
# Local finiteness of the translates of a compact convex polygon

Let `Γ ≤ PSL(2, ℝ)` act properly discontinuously on the upper half-plane, as every discrete subgroup
does. The carrier of a compact convex hyperbolic polygon `P` is compact, so the family of translates
`{γ • P.carrier | γ ∈ Γ}` is locally finite in the sense of Katok. The same holds for the translated
sides and vertices, indexed by pairs `(γ, i)`, since each lies in the corresponding translated
carrier; and the union of the translates of the carrier is closed.

## Main results

* `CompactConvexPolygon.locallyFinite_smul_carrier`: the translates of the carrier are locally
  finite.
* `CompactConvexPolygon.locallyFinite_smul_side`,
  `CompactConvexPolygon.locallyFinite_singleton_smul_vertex`: the translates of the sides,
  respectively of the vertices, are locally finite.
* `CompactConvexPolygon.isClosed_iUnion_smul_carrier`: the union of the translates of the carrier is
  closed.

These are the polygon cases of `TauCeti.locallyFinite_smul_of_isCompact`,
`LocallyFinite.comp_fst` and `TauCeti.isClosed_iUnion_smul_of_isCompact`.

## Source

Katok, *Fuchsian groups, geodesic flows on surfaces of constant negative curvature and symbolic
coding of geodesics*, Clay Math. Proc. 10 (2010), Definition 8.2, p. 27 (locally finite family of
subsets) and Definition 11.1, p. 37 (locally finite fundamental region: its tessellation
`{T(F) | T ∈ Γ}` is locally finite).
-/
public section

open Matrix.ProjectiveSpecialLinearGroup Set UpperHalfPlane
open scoped MatrixGroups Pointwise

namespace TauCeti.UpperHalfPlane

namespace CompactConvexPolygon

variable {n : ℕ} [NeZero n] (Γ : Subgroup PSL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ]
  (P : CompactConvexPolygon n)

-- The action of `γ : Γ` on `ℍ` and on its subsets is that of `(γ : PSL(2, ℝ))`
-- (`Subgroup.smul_def`), definitionally; the statements use the ambient action.

/-- **The translates of a compact convex polygon under a properly discontinuous `Γ ≤ PSL(2, ℝ)` are
locally finite**, in the sense of Katok, Definition 8.2, p. 27: every point has a neighbourhood
meeting only finitely many of them. -/
theorem locallyFinite_smul_carrier : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier :=
  locallyFinite_smul_of_isCompact P.isCompact_carrier

/-- The translates of the sides of a compact convex polygon under a properly discontinuous
`Γ ≤ PSL(2, ℝ)`, indexed by `(γ, i) ∈ Γ × Fin n`, are locally finite. -/
theorem locallyFinite_smul_side :
    LocallyFinite fun p : Γ × Fin n ↦ (p.1 : PSL(2, ℝ)) • P.side p.2 :=
  (P.locallyFinite_smul_carrier Γ).comp_fst.subset fun p ↦ smul_set_mono (P.side_subset_carrier p.2)

/-- The translates of the vertices of a compact convex polygon under a properly discontinuous
`Γ ≤ PSL(2, ℝ)`, as singletons indexed by `(γ, i) ∈ Γ × Fin n`, are locally finite. -/
theorem locallyFinite_singleton_smul_vertex :
    LocallyFinite fun p : Γ × Fin n ↦ ({(p.1 : PSL(2, ℝ)) • P.vertex p.2} : Set ℍ) :=
  (P.locallyFinite_smul_carrier Γ).comp_fst.subset fun p ↦
    singleton_subset_iff.2 (smul_mem_smul_set (P.vertex_mem_carrier p.2))

/-- The union of the translates of a compact convex polygon under a properly discontinuous
`Γ ≤ PSL(2, ℝ)` is closed. -/
theorem isClosed_iUnion_smul_carrier : IsClosed (⋃ γ : Γ, (γ : PSL(2, ℝ)) • P.carrier) :=
  isClosed_iUnion_smul_of_isCompact P.isCompact_carrier P.isClosed_carrier

end CompactConvexPolygon

end TauCeti.UpperHalfPlane
