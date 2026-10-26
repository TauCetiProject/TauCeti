/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Basic
public import TauCeti.RingTheory.RootsOfUnity.Basic

/-!
# Roots of unity in an intermediate field

An intermediate field `L` of a field extension `E/K` contains `K`, so it contains every `n`-th
root of unity of `K`. In particular `L` has enough `n`-th roots of unity whenever `K` does.

## Main results

* `IntermediateField.hasEnoughRootsOfUnity`: an intermediate field of `E/K` has enough `n`-th
  roots of unity when `K` does.
-/

public section

namespace IntermediateField

variable {K : Type*} [Field K] {E : Type*} [Field E] [Algebra K E] (L : IntermediateField K E)
  {n : ℕ} [NeZero n]

/-- An intermediate field of `E/K` contains the `n`-th roots of unity of `K`. -/
instance hasEnoughRootsOfUnity [HasEnoughRootsOfUnity K n] : HasEnoughRootsOfUnity L n :=
  .of_injective (f := (algebraMap K L : K →* L)) (algebraMap K L).injective

end IntermediateField
