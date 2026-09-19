/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Basic
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Potential

/-!
# Skew-zigzag algebras of trees and forests

A skew-zigzag parameter whose transition factor along a path depends only on the endpoints of the
path is gauge trivial (`TauCeti.SkewZigzagParameter.isGaugeEquivalent_one_of_walkTransition_eq`).
On a forest a path is determined by its endpoints, so every skew-zigzag parameter on a forest is
gauge equivalent to the constant parameter, and its relation quotient is isomorphic to the ordinary
zigzag relation quotient.

## Main results

* `TauCeti.SkewZigzagParameter.isGaugeEquivalent_one_of_isAcyclic`: every skew parameter on a
  forest is gauge equivalent to the constant parameter.
* `TauCeti.nonempty_algEquiv_nonisolatedZigzagQuotient_of_isAcyclic`: every skew-zigzag relation
  quotient of a finite forest is isomorphic to the ordinary relation quotient.
* `TauCeti.nonempty_algEquiv_zigzagAlgebra_of_isTree`: on a nontrivial finite tree, that ordinary
  quotient is the public componentwise zigzag algebra.

## References

C. Couture, *Skew-Zigzag Algebras*, Section 4, Theorem 4.8 and Corollary 4.13,
https://arxiv.org/abs/1509.08405.
-/

public section

namespace TauCeti

open DoubledQuiver

universe u w

namespace SkewZigzagParameter

variable {k : Type w} [CommMonoid k] {V : Type u} {G : SimpleGraph V}

/-- **Every skew-zigzag parameter on a forest is gauge equivalent to the constant parameter.** This
includes graphs with isolated vertices, at which there are no incident-edge ratios to trivialize. -/
theorem isGaugeEquivalent_one_of_isAcyclic (c : SkewZigzagParameter k G) (hG : G.IsAcyclic) :
    IsGaugeEquivalent (1 : SkewZigzagParameter k G) c :=
  isGaugeEquivalent_one_of_walkTransition_eq c fun _ _ p q hp hq ↦
    congrArg (walkTransition c ·.val) ((hG.subsingleton_path _ _).allEq ⟨p, hp⟩ ⟨q, hq⟩)

end SkewZigzagParameter

/-- **Every skew-zigzag relation quotient of a finite forest is isomorphic to the ordinary zigzag
relation quotient.** The isomorphism is induced by rescaling the doubled arrows. -/
theorem nonempty_algEquiv_nonisolatedZigzagQuotient_of_isAcyclic
    (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]
    (c : SkewZigzagParameter k G) (hG : G.IsAcyclic) :
    Nonempty (skewZigzagQuotient k G c ≃ₐ[k] nonisolatedZigzagQuotient k G) :=
  nonempty_algEquiv_nonisolatedZigzagQuotient_of_isGaugeEquivalent_one k G
    (c.isGaugeEquivalent_one_of_isAcyclic hG)

/-- **Every skew-zigzag relation quotient of a finite nontrivial tree is isomorphic to the public
ordinary zigzag algebra.** The nontriviality assumption excludes the exceptional one-vertex
convention, where the public ordinary zigzag algebra is the dual numbers rather than the doubled
path-algebra quotient. -/
theorem nonempty_algEquiv_zigzagAlgebra_of_isTree
    (k : Type w) [CommRing k] {V : Type u} [Finite V] [Nontrivial V]
    (G : SimpleGraph V) (c : SkewZigzagParameter k G) (hG : G.IsTree) :
    Nonempty (skewZigzagQuotient k G c ≃ₐ[k] zigzagAlgebra k G) := by
  obtain ⟨e⟩ := nonempty_algEquiv_nonisolatedZigzagQuotient_of_isAcyclic k G c hG.isAcyclic
  exact ⟨e.trans (zigzagAlgebraEquivNonisolated k G hG.connected).symm⟩

end TauCeti
