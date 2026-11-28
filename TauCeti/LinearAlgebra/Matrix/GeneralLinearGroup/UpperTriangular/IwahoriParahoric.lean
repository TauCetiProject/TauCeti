/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Block.Triangular
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Iwahori

/-!
# Iwahori subgroups as parahoric subgroups over a local ring

Let `R` be a commutative local ring with maximal ideal `𝔪 = IsLocalRing.maximalIdeal R` and let
`m` be a finite linearly ordered index type. In `TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup`,
`TauCeti.parahoricSubgroup τ I` consists of the matrices in `GL m R` whose entries `(i, j)` with
`τ i < τ j` lie in `I`, while `TauCeti.iwahori m R` consists of matrices whose entries below the
diagonal (`j < i`) lie in `𝔪`, and `TauCeti.iwahoriOne m R` further requires diagonal entries to
be congruent to `1` modulo `𝔪`.

This file bridges the two APIs:

* `TauCeti.iwahori_le_parahoricSubgroup`: if `τ i < τ j` implies `j < i` (e.g. `τ` antitone), then
  `iwahori m R ≤ parahoricSubgroup τ 𝔪`.
* `TauCeti.iwahoriOne_le_parahoricSubgroup`: under the same condition,
  `iwahoriOne m R ≤ parahoricSubgroup τ 𝔪`.
* `TauCeti.parahoricSubgroup_toDual_eq_iwahori`: for `τ = OrderDual.toDual`,
  `parahoricSubgroup OrderDual.toDual 𝔪 = iwahori m R`.

## References

* Adapted from `src/Lib/LocalGL/Iwahori/QuadraticRelation.lean` in grh-lean
  (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC):
  `New.proIwahori_le_blockParahoric`.
-/

public section

open Matrix

namespace TauCeti

variable {m : Type*} [Fintype m] [LinearOrder m] {R : Type*} [CommRing R] [IsLocalRing R]

/-- If `τ : m → α` reverses strict order (`τ i < τ j → j < i`, as for any antitone labelling),
then the Iwahori subgroup `iwahori m R` is contained in `parahoricSubgroup τ (maximalIdeal R)`. -/
theorem iwahori_le_parahoricSubgroup {α : Type*} [LinearOrder α] {τ : m → α}
    (hτ : ∀ i j : m, τ i < τ j → j < i) :
    iwahori m R ≤ parahoricSubgroup τ (IsLocalRing.maximalIdeal R) := by
  intro g hg
  rw [mem_parahoricSubgroup]
  intro i j hij
  exact (mem_upperTriangularCongruenceSubgroup_iff.mp hg) (hτ i j hij)

/-- If `τ : m → α` reverses strict order (`τ i < τ j → j < i`), then the pro-`p` Iwahori subgroup
`iwahoriOne m R` is contained in `parahoricSubgroup τ (maximalIdeal R)`. -/
theorem iwahoriOne_le_parahoricSubgroup {α : Type*} [LinearOrder α] {τ : m → α}
    (hτ : ∀ i j : m, τ i < τ j → j < i) :
    iwahoriOne m R ≤ parahoricSubgroup τ (IsLocalRing.maximalIdeal R) :=
  iwahoriOne_le_iwahori.trans (iwahori_le_parahoricSubgroup hτ)

/-- The parahoric subgroup for the dual order labelling `OrderDual.toDual : m → mᵒᵈ` and the
maximal ideal of a local ring `R` is the Iwahori subgroup `iwahori m R`. -/
theorem parahoricSubgroup_toDual_eq_iwahori :
    parahoricSubgroup (OrderDual.toDual : m → mᵒᵈ) (IsLocalRing.maximalIdeal R) = iwahori m R := by
  ext g
  simp [mem_parahoricSubgroup, mem_upperTriangularCongruenceSubgroup_iff,
    OrderDual.toDual_lt_toDual]

end TauCeti
