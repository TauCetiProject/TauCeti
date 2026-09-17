/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Discriminant.RamifiedSupport.Basic

/-!
# Ramified support in towers of number fields

Ramification cannot disappear after extending the top field of a tower: if a prime of `𝓞 K`
ramifies in `L`, then it also ramifies in every finite extension `M` of `L`. Equivalently, the
ramified support of `L / K` is contained in that of `M / K`.

The result follows from the tower formula for relative discriminants. The relative discriminant
of `L / K` occurs to the positive power `[M : L]` as a factor of the relative discriminant of
`M / K`, so each of its prime divisors remains a prime divisor upstairs.

## Main result

* `TauCeti.NumberField.ramifiedSupport_mono`: the ramified support is monotone in the top field
  of a tower.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter III, §2.
-/

public section

open scoped NumberField nonZeroDivisors

namespace TauCeti.NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- **Ramified support is monotone in a tower.** If `K ⊆ L ⊆ M` is a tower of number
fields, every prime of `𝓞 K` ramified in `L` is also ramified in `M`. -/
theorem ramifiedSupport_mono {L M : Type*} [Field L] [NumberField L]
    [Field M] [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] :
    ramifiedSupport K L ⊆ ramifiedSupport K M := by
  intro v hv
  rw [mem_ramifiedSupport] at hv ⊢
  rw [relDiscr_tower (K := K) (L := L) (M := M)]
  exact (dvd_pow hv Module.finrank_pos.ne').mul_right _

end TauCeti.NumberField

end
