/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import TauCeti.LinearAlgebra.Alternating.Basic

/-!
# Alternating maps on linearly dependent families over semirings

An alternating map vanishes on a linearly dependent family whenever unequal scalars act
differently on every nonzero value. Mathlib's `AlternatingMap.map_linearDependent` proves this
over a ring with `IsDomain` when the source and target are additive groups and the values are
torsion-free.

Over a semiring a dependence need not be a nontrivial linear combination equal to zero. Instead,
two distinct coefficient families `c ≠ d` give the same sum
`∑ j ∈ s, c j • v j = ∑ j ∈ s, d j • v j`, and they differ at some `i ∈ s`. Putting such a sum in
place of `v i` multiplies the value by the `i`-th coefficient, since every other term repeats an
argument (`AlternatingMap.map_update_sum_smul`). Hence `c i • f v = d i • f v`, and the
hypothesis on the scalars cancels them unless `f v = 0`. That covers, for example, `ℕ`-modules
with values in `ℤ`.

## Main results

* `AlternatingMap.map_linearDependent_of_smul_left_injective`: an alternating map vanishes on a
  linearly dependent family when unequal scalars act differently on every nonzero value.
-/

public section

namespace AlternatingMap

variable {R M N ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N]

/-- An alternating map vanishes on a linearly dependent family, provided unequal scalars act
differently on every nonzero value. Over a ring with `IsDomain` acting on torsion-free values in an
additive group, the latter hypothesis is `fun _ ↦ smul_left_injective R`. This is
`AlternatingMap.map_linearDependent` over any semiring. -/
theorem map_linearDependent_of_smul_left_injective (f : M [⋀^ι]→ₗ[R] N)
    (hN : ∀ n : N, n ≠ 0 → Function.Injective fun r : R ↦ r • n) {v : ι → M}
    (hv : ¬LinearIndependent R v) : f v = 0 := by
  classical
  obtain ⟨s, c, d, hcd, i, hi, hne⟩ := not_linearIndependent_iffₛ.mp hv
  by_contra h0
  exact hne <| hN _ h0 <| by
    simpa only [f.map_update_sum_smul v hi] using congr(f (Function.update v i $hcd))

end AlternatingMap
