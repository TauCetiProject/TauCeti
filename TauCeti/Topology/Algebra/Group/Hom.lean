/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Topology.Constructions.SumProd

/-!
# Continuity of flipped bimultiplicative pairings

Mathlib's `MonoidHom.flip` (additively, `AddMonoidHom.flip`) swaps the arguments of a
bimultiplicative (biadditive) pairing. Joint continuity is preserved by composition with the
continuous coordinate swap `continuous_swap`.

## Main results

* `MonoidHom.continuous_flip`: flipping a jointly continuous bimultiplicative pairing
  preserves joint continuity.
* `AddMonoidHom.continuous_flip`: the additive version, for biadditive pairings.
-/

public section

namespace MonoidHom

/-- Flipping a jointly continuous bimultiplicative pairing preserves joint continuity. -/
@[to_additive /-- Flipping a jointly continuous biadditive pairing preserves joint
continuity. -/]
theorem continuous_flip {M N P : Type*} [MulOneClass M] [MulOneClass N] [CommMonoid P]
    [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P] (μ : M →* N →* P)
    (hμ : Continuous fun p : M × N ↦ μ p.1 p.2) :
    Continuous fun p : N × M ↦ μ.flip p.1 p.2 :=
  hμ.comp continuous_swap

end MonoidHom
