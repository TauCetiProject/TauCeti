/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.GroupTheory.Divisible

/-!
# Divisibility of the circle group

The power covering maps exhibit the circle as a divisible abelian group, allowing the
extension of circle-valued characters.
-/

public section

/-- Every element of the complex unit circle has a root of each positive integral degree. -/
noncomputable instance Circle.instRootableByNat : RootableBy Circle ℕ :=
  rootableByOfPowLeftSurj Circle ℕ fun {n} hn ↦ by
    let : NeZero n := ⟨hn⟩
    exact (Circle.isQuotientCoveringMap_npow n).toIsQuotientMap.surjective
