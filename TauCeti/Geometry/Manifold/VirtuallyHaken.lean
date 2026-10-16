/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Haken
public import TauCeti.Topology.Covering.IsFiniteCover

/-!
# Virtually Haken spaces

A space `M` is *virtually Haken* when it has a finite-sheeted covering space that is a closed Haken
3-manifold. This is the conclusion of Waldhausen's virtual Haken conjecture, proved by Agol for
closed hyperbolic 3-manifolds (`TauCeti.VirtualHakenConjecture`). It is the companion of being
virtually fibered (`TauCeti.IsVirtuallyFibered`), which Agol's work also establishes for them.

The covering space is a closed Haken 3-manifold in the sense of
`TauCeti.IsPossiblyNonorientableClosedHakenThreeManifold`: an irreducible closed connected
topological 3-manifold containing a closed, bicollared, incompressible surface with infinite
fundamental group. As there, orientability of the cover is not required. Only the cover carries an
atlas, so being virtually Haken is a property of the topological space `M`.

The covering map is a finite cover in the sense of `TauCeti.IsFiniteCover`. Since a composite of
finite covers is a finite cover (`TauCeti.IsFiniteCover.comp`), a space finitely covered by a
virtually Haken space is itself virtually Haken.

## Main definitions

* `TauCeti.IsVirtuallyHaken M`: some finite cover of `M` is a closed Haken 3-manifold;
  `TauCeti.isVirtuallyHaken_iff` unfolds it.

## Main results

* `TauCeti.IsPossiblyNonorientableClosedHakenThreeManifold.isVirtuallyHaken`: a closed Haken
  3-manifold is virtually Haken, through the identity cover.
* `TauCeti.IsVirtuallyHaken.of_isFiniteCover`: the base of a finite cover by a virtually Haken
  space is virtually Haken.
* `Homeomorph.isVirtuallyHaken_iff`: being virtually Haken is invariant under homeomorphisms.
* `TauCeti.IsVirtuallyHaken.compactSpace`, `TauCeti.IsVirtuallyHaken.connectedSpace`: a virtually
  Haken space is compact and connected.

## References

* F. Waldhausen, *On irreducible 3-manifolds which are sufficiently large*, Ann. of Math. 87
  (1968), 56–88.
* A. Hatcher, *Notes on Basic 3-Manifold Topology*, Sections 1.1–1.2.
* I. Agol, *The virtual Haken conjecture* (with an appendix by I. Agol, D. Groves and J. Manning),
  Doc. Math. 18 (2013), 1045–1087.
-/

public section

universe u

namespace TauCeti

/-- A topological space `M` is **virtually Haken** if it has a finite-sheeted covering space that
is a closed Haken 3-manifold: some space `N` in the same universe, with an atlas modelled on
`ℝ³`, maps onto `M` by a finite cover (`TauCeti.IsFiniteCover`) and is a possibly nonorientable
closed Haken 3-manifold (`TauCeti.IsPossiblyNonorientableClosedHakenThreeManifold`). -/
def IsVirtuallyHaken (M : Type u) [TopologicalSpace M] : Prop :=
  ∃ (N : Type u) (_ : TopologicalSpace N) (_ : ChartedSpace (EuclideanSpace ℝ (Fin 3)) N)
    (p : N → M), IsFiniteCover p ∧ IsPossiblyNonorientableClosedHakenThreeManifold N

variable {M : Type u} [TopologicalSpace M]

/-- Unfolding `TauCeti.IsVirtuallyHaken`: `M` is virtually Haken exactly when some finite cover of
it is a closed Haken 3-manifold. -/
theorem isVirtuallyHaken_iff :
    IsVirtuallyHaken M ↔
      ∃ (N : Type u) (_ : TopologicalSpace N) (_ : ChartedSpace (EuclideanSpace ℝ (Fin 3)) N)
        (p : N → M), IsFiniteCover p ∧ IsPossiblyNonorientableClosedHakenThreeManifold N :=
  Iff.rfl

/-- A closed Haken 3-manifold is virtually Haken: it covers itself by the identity. -/
theorem IsPossiblyNonorientableClosedHakenThreeManifold.isVirtuallyHaken
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (h : IsPossiblyNonorientableClosedHakenThreeManifold M) : IsVirtuallyHaken M :=
  ⟨M, inferInstance, inferInstance, id, .id, h⟩

namespace IsVirtuallyHaken

/-- The base of a finite cover by a virtually Haken space is virtually Haken: a finite cover of
the cover is a finite cover of the base. -/
theorem of_isFiniteCover {N : Type u} [TopologicalSpace N] (h : IsVirtuallyHaken N)
    {p : N → M} (hp : IsFiniteCover p) : IsVirtuallyHaken M := by
  obtain ⟨L, _, _, r, hr, hL⟩ := h
  exact ⟨L, inferInstance, inferInstance, p ∘ r, hp.comp hr, hL⟩

/-- A virtually Haken space is compact, as the image of a closed 3-manifold. -/
theorem compactSpace (h : IsVirtuallyHaken M) : CompactSpace M := by
  obtain ⟨N, _, _, p, hp, hN⟩ := h
  obtain ⟨-, -, -, hN, -⟩ := isClosedConnectedThreeManifold_iff.mp hN.isClosedConnectedThreeManifold
  have : CompactSpace N := isCompact_univ_iff.mp hN
  exact hp.surjective.compactSpace hp.isCoveringMap.continuous

/-- A virtually Haken space is connected, as the image of a connected 3-manifold. -/
theorem connectedSpace (h : IsVirtuallyHaken M) : ConnectedSpace M := by
  obtain ⟨N, _, _, p, hp, hN⟩ := h
  obtain ⟨-, -, -, -, hN⟩ := isClosedConnectedThreeManifold_iff.mp hN.isClosedConnectedThreeManifold
  have : ConnectedSpace N := connectedSpace_iff_univ.mpr hN
  exact hp.connectedSpace

end IsVirtuallyHaken

/-- Being virtually Haken is invariant under homeomorphisms. -/
theorem _root_.Homeomorph.isVirtuallyHaken_iff {M' : Type u} [TopologicalSpace M']
    (e : M ≃ₜ M') : IsVirtuallyHaken M ↔ IsVirtuallyHaken M' :=
  ⟨fun h ↦ h.of_isFiniteCover e.isFiniteCover, fun h ↦ h.of_isFiniteCover e.symm.isFiniteCover⟩

end TauCeti
