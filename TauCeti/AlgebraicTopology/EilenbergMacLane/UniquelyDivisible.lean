/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.Homology
public import TauCeti.AlgebraicTopology.EilenbergMacLane.PathFibration

/-!
# Eilenberg--Mac Lane spaces of uniquely divisible groups

Let `m` be an integer, `A` an abelian group on which multiplication by `m` is bijective, and `k` a
commutative semisimple ring in which `m = 0`, for instance `k = 𝔽₂` and `m = 2`. Then every
Eilenberg--Mac Lane space of type `K(A, n)`, for every `n ≥ 1`, has the `k`-homology of a point
(`TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_bijective_zsmul`). For
`m = 2`: every `K(A, n)` space of a uniquely two-divisible group has the mod-two homology of a
point (`TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isUniquelyTwoDivisible`).
No hypothesis of CW type is made on the space.

The case `n = 1` is the computation of the group homology of `A`
(`TauCeti.IsEilenbergMacLaneSpaceOne.subsingleton_singularHomology_of_bijective_zsmul`). The
induction goes through the based path fibration `p : P → X` of a `K(A, n + 1)` space `X`, whose
total space `P`, the paths ending at the base point, is contractible and whose fibres are
`K(A, n)` spaces
(`TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isEilenbergMacLaneSpaceOne`).

This is the input on Eilenberg--Mac Lane spaces of Serre's theorem that the homotopy groups of a
simply connected space with the mod-two homology of a point are uniquely two-divisible.

## Main results

* `TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_bijective_zsmul`: a `K(A, n)`
  space of a uniquely `m`-divisible abelian group is acyclic modulo `m`.
* `TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isUniquelyTwoDivisible`: a
  `K(A, n)` space of a uniquely two-divisible abelian group has the mod-two homology of a point.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258–294.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 4.2.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

namespace TauCeti

namespace IsEilenbergMacLaneSpace

variable (k : Type) [CommRing k] [IsSemisimpleRing k] {m : ℤ}

/-- **`K(A, n)` spaces of uniquely `m`-divisible groups are acyclic modulo `m`.** If
multiplication by the integer `m` is a bijection of the abelian group `A`, then every `K(A, n)`
space, for every `n ≥ 1`, has no homology in positive degrees with coefficients in a commutative
semisimple ring `k` in which `m = 0`. -/
theorem subsingleton_singularHomology_of_bijective_zsmul (hmk : (m : k) = 0) {A : Type}
    [AddCommGroup A] (hA : Function.Bijective fun a : A ↦ m • a) {n : ℕ} [NeZero n] {X : Type}
    [TopologicalSpace X] {x : X} (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x)
    (i : ℕ) : Subsingleton (((singularChains k).obj (TopCat.of X)).homology (i + 1)) :=
  subsingleton_singularHomology_of_isEilenbergMacLaneSpaceOne k
    (IsEilenbergMacLaneSpaceOne.subsingleton_singularHomology_of_bijective_zsmul k hmk hA) hX i

/-- **Mod-two acyclicity of `K(A, n)` spaces.** For a uniquely two-divisible abelian group `A`
and every `n ≥ 1`, every `K(A, n)` space has the mod-two homology of a point: `Hᵢ(X; 𝔽₂) = 0` for
all `i > 0`. -/
theorem subsingleton_singularHomology_of_isUniquelyTwoDivisible {A : Type} [AddCommGroup A]
    (hA : IsUniquelyTwoDivisible A) {n : ℕ} [NeZero n] {X : Type} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x) (i : ℕ) :
    Subsingleton (((singularChains (ZMod 2)).obj (TopCat.of X)).homology (i + 1)) :=
  subsingleton_singularHomology_of_bijective_zsmul (ZMod 2) (m := 2) (by decide)
    ((isUniquelyTwoDivisible_iff A).1 hA) hX i

end IsEilenbergMacLaneSpace

end TauCeti
