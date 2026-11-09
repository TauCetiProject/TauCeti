/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import TauCeti.Geometry.Diffeomorphism.Action
import Mathlib.GroupTheory.GroupAction.Transitive
import TauCeti.Geometry.Manifold.Diffeomorph.PointMotion

/-!
# Orbits of the diffeomorphism group

Let `M` be a Hausdorff boundaryless `C^n` manifold, `1 ≤ n`, modelled on a finite-dimensional
real normed space. Every point of `M` can be moved to every nearby point by a diffeomorphism
(`Diffeomorph.exists_contMDiff_family_apply_eq`), so the orbits of the group `Diff(M)` of `C^n`
self-diffeomorphisms are open, and hence closed as complements of the other orbits. In particular
`Diff(M)` acts transitively when `M` is connected.

## Main results

* `Diffeomorph.isOpen_orbit`, `Diffeomorph.isClosed_orbit`: the orbits of `Diff(M)` are open and
  closed.
* `Diffeomorph.isPretransitive`: `Diff(M)` acts transitively on a connected manifold.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint* (1965), §4, Homogeneity Lemma.
-/

public section

open scoped Manifold ContDiff

namespace Diffeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [BoundarylessManifold I M] {n : ℕ∞} [IsManifold I n M]

/-- **The orbits of the diffeomorphism group are open.** -/
theorem isOpen_orbit (hn : 1 ≤ n) (x : M) : IsOpen (MulAction.orbit (M ≃ₘ^n⟮I, I⟯ M) x) := by
  refine isOpen_iff_forall_mem_open.2 ?_
  rintro _ ⟨g, rfl⟩
  obtain ⟨U, hU, hgU, S, f, -, -, hS, -⟩ := exists_contMDiff_family_apply_eq (I := I) hn (g • x)
  refine ⟨U, fun z hz ↦ ?_, hU, hgU⟩
  have hz' : (S (f z) * g) • x = z := by rw [mul_smul, smul_def (S (f z)), hS z hz]
  exact ⟨_, hz'⟩

/-- **The orbits of the diffeomorphism group are closed**, being complements of unions of
orbits. -/
theorem isClosed_orbit (hn : 1 ≤ n) (x : M) : IsClosed (MulAction.orbit (M ≃ₘ^n⟮I, I⟯ M) x) := by
  refine isOpen_compl_iff.1 (isOpen_iff_forall_mem_open.2 fun y hy ↦ ⟨_, fun z hz hzx ↦ hy ?_,
    isOpen_orbit (I := I) hn y, MulAction.mem_orbit_self y⟩)
  rw [← MulAction.orbit_eq_iff.2 hzx, MulAction.orbit_eq_iff.2 hz]
  exact MulAction.mem_orbit_self y

/-- **The diffeomorphism group of a connected manifold acts transitively**: for `1 ≤ n`, every
point of a connected Hausdorff boundaryless `C^n` manifold is carried to every other point
by a `C^n` diffeomorphism. -/
theorem isPretransitive [ConnectedSpace M] (hn : 1 ≤ n) :
    MulAction.IsPretransitive (M ≃ₘ^n⟮I, I⟯ M) M := by
  obtain ⟨x⟩ := ConnectedSpace.toNonempty (α := M)
  rw [MulAction.isPretransitive_iff_orbit_eq_univ x]
  exact IsClopen.eq_univ ⟨isClosed_orbit hn x, isOpen_orbit hn x⟩ ⟨x, MulAction.mem_orbit_self x⟩

end Diffeomorph
