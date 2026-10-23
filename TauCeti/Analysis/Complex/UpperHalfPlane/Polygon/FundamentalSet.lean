/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Basic
public import TauCeti.Analysis.Complex.UpperHalfPlane.ProperAction
public import TauCeti.Topology.Algebra.ConstMulAction

/-!
# The interior of a polygon as a fundamental set

Let `P` be a compact convex hyperbolic polygon and let `Γ ≤ PSL(2, ℝ)`. One of the local
hypotheses in the Poincaré polygon theorem is that distinct `Γ`-translates of the interior of
`P.carrier` are disjoint. This file records the two immediate global consequences of that
hypothesis. The orbit projection is an open embedding on the polygon interior, and, provided the
interior is nonempty, `Γ` is a discrete subgroup.

These are the injectivity and discreteness parts of the fundamental-set argument. Showing that the
translates cover the upper half-plane, and deriving the presentation from side pairings and vertex
cycles, require the cycle and angle hypotheses of the Poincaré polygon theorem.

## Main results

* `CompactConvexPolygon.isOpenEmbedding_quotientMk_domRestrict_interior`: the orbit projection
  restricts to an open embedding on the polygon interior.
* `CompactConvexPolygon.discreteTopology_of_disjoint_smul_interior`: a subgroup with disjoint
  translates of a nonempty polygon interior is discrete.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, Chapter 9.
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, Chapter 3.
-/

public section

noncomputable section

open Matrix.ProjectiveSpecialLinearGroup Set Topology UpperHalfPlane
open scoped MatrixGroups Pointwise

namespace TauCeti.UpperHalfPlane.CompactConvexPolygon

variable {n : ℕ} [NeZero n] (P : CompactConvexPolygon n) (Γ : Subgroup PSL(2, ℝ))

/-- If distinct `Γ`-translates of the interior of a polygon are disjoint, the orbit projection
restricts to an open embedding on that interior. In particular, no two distinct points in the
interior are identified in the quotient. -/
theorem isOpenEmbedding_quotientMk_domRestrict_interior
    (hdisj : ∀ γ : Γ, γ ≠ 1 → Disjoint (γ • interior P.carrier) (interior P.carrier)) :
    IsOpenEmbedding ((interior P.carrier).domRestrict
      (Quotient.mk'' : ℍ → MulAction.orbitRel.Quotient Γ ℍ)) :=
  TauCeti.isOpenEmbedding_quotientMk_domRestrict_of_disjoint_smul isOpen_interior hdisj

/-- **Discreteness from polygon-interior no-overlap.** A subgroup of `PSL(2, ℝ)` is discrete if
the interior of a polygon is nonempty and disjoint from all of its translates by nonidentity
elements of the subgroup. This is the discreteness step in the Poincaré polygon theorem. -/
theorem discreteTopology_of_disjoint_smul_interior (hP : (interior P.carrier).Nonempty)
    (hdisj : ∀ γ : Γ, γ ≠ 1 → Disjoint (γ • interior P.carrier) (interior P.carrier)) :
    DiscreteTopology Γ :=
  TauCeti.discreteTopology_of_disjoint_smul (fun _ ↦ by fun_prop) isOpen_interior hP hdisj

end TauCeti.UpperHalfPlane.CompactConvexPolygon

end
