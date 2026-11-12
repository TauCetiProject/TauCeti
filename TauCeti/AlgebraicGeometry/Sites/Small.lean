/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Small

/-!
# Small sites of a scheme

Complements to Mathlib's `Mathlib.AlgebraicGeometry.Sites.Small`, about the small site
`S.smallGrothendieckTopology P` of a scheme `S` defined by a morphism property `P`.

## Main results

* `AlgebraicGeometry.Scheme.bot_mem_smallGrothendieckTopology`: on a small site of `S`, such as
  the small étale site, an object with empty underlying space is covered by the empty sieve.
-/

public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

/-- On the small site of `S` defined by a morphism property `P`, for example the small étale
site, an object with empty underlying space is covered by the empty sieve. -/
theorem bot_mem_smallGrothendieckTopology {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] [P.IsMultiplicative] (U : P.Over ⊤ S) [IsEmpty U.left] :
    ⊥ ∈ S.smallGrothendieckTopology P U := by
  rw [Functor.mem_restrictedTopology_iff, GrothendieckTopology.mem_over_iff,
    Sieve.functorPushforward_bot, map_bot]
  exact bot_mem_grothendieckTopology (P := P) U.left

end AlgebraicGeometry.Scheme
