/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Topology.Algebra.Group.ZPow
public import Mathlib.Topology.Constructions.SumProd

/-!
# Continuity of group homomorphisms and biadditive pairings

Mathlib's `AddMonoidHom.flip` swaps the arguments of a biadditive pairing. Joint continuity
is preserved by composition with the continuous coordinate swap `continuous_swap`.
The power and multiple homomorphisms of commutative topological groups are continuous.

## Main results

* `AddMonoidHom.continuous_flip`: flipping a jointly continuous biadditive pairing preserves
  joint continuity.
* `TauCeti.continuous_zpowGroupHom`: the power homomorphisms of a commutative topological group
  are continuous.
-/

public section

namespace AddMonoidHom

/-- Flipping a jointly continuous biadditive pairing preserves joint continuity. -/
theorem continuous_flip {M N P : Type*} [AddZeroClass M] [AddZeroClass N] [AddCommMonoid P]
    [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P] (μ : M →+ N →+ P)
    (hμ : Continuous fun p : M × N => μ p.1 p.2) :
    Continuous fun p : N × M => μ.flip p.1 p.2 :=
  hμ.comp continuous_swap

end AddMonoidHom

namespace TauCeti

/-- The power homomorphism `g ↦ g ^ n` of a commutative topological group is continuous. -/
@[to_additive /-- The multiple homomorphism `g ↦ n • g` of a commutative topological additive
group is continuous. -/]
theorem continuous_zpowGroupHom {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] (n : ℤ) : Continuous (zpowGroupHom n : G →* G) :=
  continuous_zpow n

end TauCeti
