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
(`TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_bijective_zsmul`). The group,
the space and the ring lie in an arbitrary universe. For `m = 2`: every `K(A, n)` space of a
uniquely two-divisible group has the mod-two homology of a point
(`TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_isUniquelyTwoDivisible`).
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
* `TauCeti.IsEilenbergMacLaneSpace.subsingleton_singularHomology_of_odd_natCard`: so does a
  `K(A, n)` space of a finite abelian group of odd order, such as `K(ℤ/3, 1)`.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258–294.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 4.2.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

universe u

namespace TauCeti

namespace IsEilenbergMacLaneSpace

variable (k : Type u) [CommRing k] [IsSemisimpleRing k] {m : ℤ}

/-- **`K(A, n)` spaces of uniquely `m`-divisible groups are acyclic modulo `m`.** If
multiplication by the integer `m` is a bijection of the abelian group `A`, then every `K(A, n)`
space, for every `n ≥ 1`, has no homology in positive degrees with coefficients in a commutative
semisimple ring `k` in which `m = 0`. -/
theorem subsingleton_singularHomology_of_bijective_zsmul (hmk : (m : k) = 0) {A : Type u}
    [AddCommGroup A] (hA : Function.Bijective fun a : A ↦ m • a) {n : ℕ} [NeZero n] {X : Type u}
    [TopologicalSpace X] {x : X} (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x)
    (i : ℕ) : Subsingleton (((singularChains k).obj (TopCat.of X)).homology (i + 1)) :=
  subsingleton_singularHomology_of_isEilenbergMacLaneSpaceOne k
    (IsEilenbergMacLaneSpaceOne.subsingleton_singularHomology_of_bijective_zsmul k hmk hA) hX i

/-- **Mod-two acyclicity of `K(A, n)` spaces.** For a uniquely two-divisible abelian group `A`
and every `n ≥ 1`, every `K(A, n)` space has the mod-two homology of a point: `Hᵢ(X; k) = 0` for
all `i > 0`, with coefficients in a commutative semisimple ring `k` in which `2 = 0`, such as
`𝔽₂`. -/
theorem subsingleton_singularHomology_of_isUniquelyTwoDivisible (hk : (2 : k) = 0) {A : Type u}
    [AddCommGroup A] (hA : IsUniquelyTwoDivisible A) {n : ℕ} [NeZero n] {X : Type u}
    [TopologicalSpace X] {x : X} (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x) (i : ℕ) :
    Subsingleton (((singularChains k).obj (TopCat.of X)).homology (i + 1)) :=
  subsingleton_singularHomology_of_bijective_zsmul k (m := 2) (mod_cast hk)
    ((isUniquelyTwoDivisible_iff A).1 hA) hX i

/-- **Mod-two acyclicity of `K(A, n)` spaces of finite groups of odd order.** For a finite abelian
group `A` of odd order, such as `ℤ/3`, and every `n ≥ 1`, every `K(A, n)` space has the mod-two
homology of a point, with coefficients in a commutative semisimple ring `k` in which `2 = 0`: `A` is
uniquely two-divisible (`TauCeti.isUniquelyTwoDivisible_iff_odd_natCard`). -/
theorem subsingleton_singularHomology_of_odd_natCard (hk : (2 : k) = 0) {A : Type u}
    [AddCommGroup A] [Finite A] (hA : Odd (Nat.card A)) {n : ℕ} [NeZero n] {X : Type u}
    [TopologicalSpace X] {x : X} (hX : IsEilenbergMacLaneSpace (Multiplicative A) n X x) (i : ℕ) :
    Subsingleton (((singularChains k).obj (TopCat.of X)).homology (i + 1)) :=
  subsingleton_singularHomology_of_isUniquelyTwoDivisible k hk
    ((isUniquelyTwoDivisible_iff_odd_natCard A).2 hA) hX i

end IsEilenbergMacLaneSpace

end TauCeti
