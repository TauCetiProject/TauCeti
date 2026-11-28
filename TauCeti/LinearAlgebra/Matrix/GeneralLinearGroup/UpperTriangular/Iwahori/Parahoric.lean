/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Block.Triangular
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Iwahori.Basic

/-!
# Containment of Iwahori subgroups in block parahoric subgroups

Let `R` be a commutative ring, `I` an ideal of `R`, and `m` a finite linearly ordered index type.
In `TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup`, `TauCeti.parahoricSubgroup τ I` consists of
the matrices in `GL m R` whose entries `(i, j)` with `τ i < τ j` lie in `I`, while
`TauCeti.upperTriangularCongruenceSubgroup m I` consists of matrices whose entries below the
diagonal (`j < i`) lie in `I`. When `R` is local with maximal ideal `𝔪`, this specializes to
`TauCeti.iwahori m R` and its pro-`p` subgroup `TauCeti.iwahoriOne m R`.

This file proves containment under any antitone labelling `τ : m → α`:

* `TauCeti.upperTriangularCongruenceSubgroup_le_parahoricSubgroup`:
  `upperTriangularCongruenceSubgroup m I ≤ parahoricSubgroup τ I` for any `I : Ideal R` and
  `Antitone τ`.
* `TauCeti.iwahori_le_parahoricSubgroup`: specialization to `I = IsLocalRing.maximalIdeal R`.
* `TauCeti.iwahoriOne_le_parahoricSubgroup`: containment `iwahoriOne m R ≤ parahoricSubgroup τ 𝔪`.

## References

* Adapted from `src/Lib/LocalGL/Iwahori/QuadraticRelation.lean` in grh-lean
  (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC):
  `New.proIwahori_le_blockParahoric`.
-/

public section

open Matrix

namespace TauCeti

variable {m : Type*} [Fintype m] [LinearOrder m] {R : Type*} [CommRing R]

/-- For any antitone labelling `τ : m → α` and ideal `I` of a commutative ring `R`, the
upper-triangular congruence subgroup `upperTriangularCongruenceSubgroup m I` is contained in
`parahoricSubgroup τ I`. -/
theorem upperTriangularCongruenceSubgroup_le_parahoricSubgroup {α : Type*} [LinearOrder α]
    {τ : m → α} (hτ : Antitone τ) (I : Ideal R) :
    upperTriangularCongruenceSubgroup m I ≤ parahoricSubgroup τ I := by
  intro g hg
  rw [mem_parahoricSubgroup]
  intro i j hij
  exact (mem_upperTriangularCongruenceSubgroup_iff.mp hg)
    (lt_of_not_ge fun h ↦ not_lt_of_ge (hτ h) hij)

section LocalRing

variable [IsLocalRing R]

/-- For any antitone labelling `τ : m → α`, the Iwahori subgroup `iwahori m R` is contained in
`parahoricSubgroup τ (maximalIdeal R)`. -/
theorem iwahori_le_parahoricSubgroup {α : Type*} [LinearOrder α] {τ : m → α} (hτ : Antitone τ) :
    iwahori m R ≤ parahoricSubgroup τ (IsLocalRing.maximalIdeal R) :=
  upperTriangularCongruenceSubgroup_le_parahoricSubgroup hτ (IsLocalRing.maximalIdeal R)

/-- For any antitone labelling `τ : m → α`, the pro-`p` Iwahori subgroup `iwahoriOne m R` is
contained in `parahoricSubgroup τ (maximalIdeal R)`. -/
theorem iwahoriOne_le_parahoricSubgroup {α : Type*} [LinearOrder α] {τ : m → α}
    (hτ : Antitone τ) :
    iwahoriOne m R ≤ parahoricSubgroup τ (IsLocalRing.maximalIdeal R) :=
  iwahoriOne_le_iwahori.trans (iwahori_le_parahoricSubgroup hτ)

end LocalRing

end TauCeti
