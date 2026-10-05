/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Covolume
public import TauCeti.Analysis.Complex.UpperHalfPlane.Bisector
public import TauCeti.MeasureTheory.Group.DirichletDomain.Faces
public import TauCeti.Topology.MetricSpace.IsometricSMul

/-!
# Dirichlet domains of Fuchsian groups

Let `Γ ≤ PSL(2, ℝ)` be discrete and let `p ∈ ℍ` have trivial stabilizer in `Γ`. The Dirichlet
domain `TauCeti.dirichletDomain Γ p` consists of the points of `ℍ` hyperbolically at least as
close to `p` as to every other point of the orbit `Γ • p`. It is a closed measurable fundamental
domain for `Γ`: its translates cover `ℍ`, and two distinct translates meet only along a
hyperbolic perpendicular bisector, which has zero area. In particular the covolume of `Γ` is the
hyperbolic area of any Dirichlet domain centred at a point with trivial stabilizer, and every
discrete subgroup has such a Dirichlet domain, since points with trivial stabilizer exist.

The Dirichlet domain is the starting point of the Dirichlet polygon: for a cofinite group it is a
finite-sided convex hyperbolic polygon whose sides are paired by elements of `Γ`. The imported
`TauCeti.dirichletFace` API describes its equality faces: these cover the boundary, form a
locally finite family, and the face indexed by `g` is paired with that indexed by `g⁻¹` by the
transformation `g⁻¹`. Identifying which equality faces are sides requires further polygon geometry.

## Main results

* `Subgroup.isFundamentalDomain_dirichletDomain`: a Dirichlet domain centred at a point with
  trivial stabilizer is a fundamental domain.
* `Subgroup.exists_isFundamentalDomain_dirichletDomain`: every discrete subgroup has a Dirichlet
  fundamental domain.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, §9.4.
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, Theorem 3.2.2.
-/

public section

open MeasureTheory MulAction TauCeti UpperHalfPlane

open scoped MatrixGroups UpperHalfPlane

namespace Subgroup

variable (Γ : Subgroup PSL(2, ℝ)) [DiscreteTopology Γ]

/-- **Dirichlet domains are fundamental domains.** For a discrete subgroup `Γ ≤ PSL(2, ℝ)`, the
Dirichlet domain centred at a point of `ℍ` with trivial stabilizer is a measurable fundamental
domain for the action of `Γ` on `ℍ`. -/
theorem isFundamentalDomain_dirichletDomain {p : ℍ} (hp : p ∈ freeLocus Γ ℍ) :
    IsFundamentalDomain Γ (dirichletDomain Γ p) :=
  TauCeti.isFundamentalDomain_dirichletDomain volume ((mem_freeLocus Γ ℍ).mp hp)
    fun _ _ ↦ UpperHalfPlane.volume_setOf_dist_eq_dist

/-- Every discrete subgroup of `PSL(2, ℝ)` has a Dirichlet domain which is a fundamental
domain. -/
theorem exists_isFundamentalDomain_dirichletDomain :
    ∃ p : ℍ, IsFundamentalDomain Γ (dirichletDomain Γ p) :=
  let ⟨p, hp⟩ := freeLocus_nonempty Γ
  ⟨p, isFundamentalDomain_dirichletDomain Γ hp⟩

end Subgroup
