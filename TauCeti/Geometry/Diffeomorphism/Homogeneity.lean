/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import TauCeti.Geometry.Diffeomorphism.Action
import TauCeti.Geometry.Manifold.Diffeomorph.PointMotion

/-!
# Orbits of the diffeomorphism group

The orbits of the group of `C^m` self-diffeomorphisms of a finite-dimensional boundaryless `C^m`
manifold `M` are open and closed for any `1 ≤ m`. Near each point, cut-off translations in a chart
move it to every nearby point (`TauCeti.exists_contMDiff_family_apply_eq`), and unlike flows of
vector fields they lose no derivative, so no further smoothness of `M` is needed. In particular the
diffeomorphism group of a connected manifold acts transitively.

## Main results

* `TauCeti.isOpen_orbit_diffeomorph`: the orbits of the diffeomorphism group are open.
* `TauCeti.isClopen_orbit_diffeomorph`: the orbits of the diffeomorphism group are open and
  closed.
* `TauCeti.orbit_diffeomorph_eq_univ`: on a connected manifold, the diffeomorphism group acts
  transitively.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia
  (1965), §4, Homogeneity Lemma.
-/

public section

noncomputable section

open Set MulAction
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] {m : ℕ∞} [IsManifold I m M]

/-- The orbits of the diffeomorphism group of a finite-dimensional boundaryless manifold are
open. -/
theorem isOpen_orbit_diffeomorph (hm : 1 ≤ m) (x₀ : M) : IsOpen (orbit (M ≃ₘ^m⟮I, I⟯ M) x₀) := by
  refine isOpen_iff_forall_mem_open.2 ?_
  rintro _ ⟨g, rfl⟩
  obtain ⟨U, hU, hgU, -, S, f, -, -, -, -, hS, -, -⟩ :=
    exists_contMDiff_family_apply_eq (I := I) hm isOpen_univ (mem_univ (g • x₀))
  refine ⟨U, fun z hz ↦ ⟨S (f z) * g, ?_⟩, hU, hgU⟩
  dsimp only
  rw [mul_smul, Diffeomorph.smul_def (S (f z)), hS z hz]

/-- The orbits of the diffeomorphism group of a finite-dimensional boundaryless manifold are open
and closed. -/
theorem isClopen_orbit_diffeomorph (hm : 1 ≤ m) (x₀ : M) :
    IsClopen (orbit (M ≃ₘ^m⟮I, I⟯ M) x₀) :=
  ⟨isClosed_orbit_of_forall_isOpen_orbit (isOpen_orbit_diffeomorph hm) x₀,
    isOpen_orbit_diffeomorph hm x₀⟩

/-- **Transitivity.** The diffeomorphism group of a connected finite-dimensional boundaryless
manifold acts transitively. -/
theorem orbit_diffeomorph_eq_univ [PreconnectedSpace M] (hm : 1 ≤ m) (x₀ : M) :
    orbit (M ≃ₘ^m⟮I, I⟯ M) x₀ = univ :=
  (isClopen_orbit_diffeomorph (I := I) hm x₀).eq_univ ⟨x₀, mem_orbit_self x₀⟩

end TauCeti
