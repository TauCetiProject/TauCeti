/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Covering.Homeomorph
public import TauCeti.Topology.MappingTorus

/-!
# Virtually fibered spaces

A space `M` is *virtually fibered* when it has a connected finite-sheeted covering space that
fibers over the circle, in the sense of `TauCeti.FibersOverCircle`. This is the conclusion of
Thurston's virtual fibering question for hyperbolic 3-manifolds (Kirby's problem 3.51), answered
by Agol: every closed hyperbolic 3-manifold has a finite cover that is a surface bundle over the
circle.

The covering space is required to be connected, as is customary, and the covering map to be
surjective with finite fibres. Surjectivity is imposed because Mathlib's `IsCoveringMap` allows
empty fibres: without it a space would be virtually fibered as soon as one of its components is.
With both conditions a virtually fibered space is connected
(`TauCeti.IsVirtuallyFibered.connectedSpace`). Finite-sheeted covering spaces in the bundled sense
are the objects of `TauCeti.FiniteCoveringSpace`; the unbundled form, a covering map with finite
fibres, is used here so that the predicate is stated on a type with its topology.

## Main definitions

* `TauCeti.IsVirtuallyFibered M`: some connected space covers `M` surjectively with finite fibres
  and fibers over the circle; `TauCeti.isVirtuallyFibered_iff` unfolds it.

## Main results

* `TauCeti.FibersOverCircle.isVirtuallyFibered`: a connected space that fibers over the circle is
  virtually fibered, through the identity cover.
* `Homeomorph.isVirtuallyFibered_iff`: being virtually fibered is invariant under homeomorphisms.
* `TauCeti.IsVirtuallyFibered.connectedSpace`, `TauCeti.IsVirtuallyFibered.infinite`: a virtually
  fibered space is connected and infinite; in particular a finite space is not virtually fibered.

## References

* R. Kirby (ed.), *Problems in Low-Dimensional Topology*, Problem 3.51, in *Geometric Topology*,
  AMS/IP Stud. Adv. Math. 2.2 (1997).
* I. Agol, *The virtual Haken conjecture* (with an appendix by I. Agol, D. Groves and J. Manning),
  Doc. Math. 18 (2013), 1045–1087.
-/

public section

universe u

namespace TauCeti

/-- A topological space `M` is **virtually fibered** if it has a connected finite-sheeted covering
space that fibers over the circle: some connected space `N` in the same universe maps onto `M` by a
covering map with finite fibres, and `N` is homeomorphic to a mapping torus. -/
def IsVirtuallyFibered (M : Type u) [TopologicalSpace M] : Prop :=
  ∃ (N : Type u) (_ : TopologicalSpace N) (_ : ConnectedSpace N) (p : N → M),
    IsCoveringMap p ∧ Function.Surjective p ∧ (∀ x, Finite (p ⁻¹' {x})) ∧ FibersOverCircle N

variable {M : Type u} [TopologicalSpace M]

/-- Unfolding `TauCeti.IsVirtuallyFibered`: `M` is virtually fibered exactly when some connected
space covers it surjectively with finite fibres and fibers over the circle. -/
theorem isVirtuallyFibered_iff :
    IsVirtuallyFibered M ↔
      ∃ (N : Type u) (_ : TopologicalSpace N) (_ : ConnectedSpace N) (p : N → M),
        IsCoveringMap p ∧ Function.Surjective p ∧ (∀ x, Finite (p ⁻¹' {x})) ∧
          FibersOverCircle N :=
  Iff.rfl

/-- A connected space that fibers over the circle is virtually fibered: it covers itself by the
identity. -/
theorem FibersOverCircle.isVirtuallyFibered [ConnectedSpace M] (h : FibersOverCircle M) :
    IsVirtuallyFibered M :=
  ⟨M, inferInstance, inferInstance, id, (Homeomorph.refl M).isCoveringMap,
    Function.surjective_id, fun x ↦ Set.finite_singleton x, h⟩

namespace IsVirtuallyFibered

/-- A virtually fibered space is connected, as the image of a connected covering space. -/
theorem connectedSpace (h : IsVirtuallyFibered M) : ConnectedSpace M := by
  obtain ⟨N, _, _, p, hp, hsurj, -, -⟩ := h
  exact hsurj.connectedSpace hp.continuous

/-- A virtually fibered space is infinite: a finite-sheeted cover of a finite space is finite,
while a space fibering over the circle is infinite. -/
theorem infinite (h : IsVirtuallyFibered M) : Infinite M := by
  obtain ⟨N, _, _, p, -, -, hfin, hN⟩ := h
  have := hN.infinite
  by_contra hM
  have : Finite M := not_infinite_iff_finite.mp hM
  exact Set.infinite_univ (α := N) <| by
    simpa using Set.finite_univ.preimage' fun x _ ↦ Set.toFinite (p ⁻¹' {x})

end IsVirtuallyFibered

/-- Being virtually fibered is invariant under homeomorphisms. -/
theorem _root_.Homeomorph.isVirtuallyFibered_iff {M' : Type u} [TopologicalSpace M']
    (e : M ≃ₜ M') : IsVirtuallyFibered M ↔ IsVirtuallyFibered M' := by
  suffices ∀ {M M' : Type u} [TopologicalSpace M] [TopologicalSpace M'] (e : M ≃ₜ M'),
      IsVirtuallyFibered M → IsVirtuallyFibered M' from ⟨this e, this e.symm⟩
  intro M M' _ _ e ⟨N, _, _, p, hp, hsurj, hfin, hN⟩
  refine ⟨N, inferInstance, inferInstance, e ∘ p, hp.homeomorph_comp e,
    e.surjective.comp hsurj, fun x ↦ ?_, hN⟩
  rw [Set.preimage_comp, ← e.image_symm, Set.image_singleton]
  exact hfin _

end TauCeti
