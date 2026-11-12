/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ClassifyingSpace.Homology
public import TauCeti.AlgebraicTopology.ClassifyingSpace.UniquelyDivisible
import TauCeti.AlgebraicTopology.ClassifyingSpace.Uniqueness
import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence

/-!
# The singular homology of `K(G, 1)` spaces

Every `K(G, 1)` space `X`, of any kind, receives a weak homotopy equivalence from Milnor's
classifying space `classifyingSpace G`
(`TauCeti.IsEilenbergMacLaneSpaceOne.exists_isWeakHomotopyEquivalence_classifyingSpace`), and weak
homotopy equivalences induce isomorphisms on singular homology. So the singular homology of `X`
with coefficients in a commutative ring `k` is the group homology of `G` with trivial coefficients
`k` (`TauCeti.IsEilenbergMacLaneSpaceOne.nonempty_singularHomologyIsoGroupHomology`):

`Hₙ(X; k) ≅ Hₙ(G, k)`.

The spaces of interest need not have CW type. The loop space of a `K(A, 2)` space is a `K(A, 1)`
space, and so are the fibres of the path-loop fibration over it; it is to such spaces that the
vanishing theorems for the classifying space have to be applied. In particular, if `A` is an
abelian group on which multiplication by an integer `m` is bijective and `k` is a commutative
semisimple ring in which `m = 0`, then every `K(A, 1)` space has the `k`-homology of a point
(`TauCeti.IsEilenbergMacLaneSpaceOne.subsingleton_singularHomology_of_bijective_zsmul`). For
`m = 2` and `k = 𝔽₂`: every `K(A, 1)` space of a uniquely two-divisible group has the mod-two
homology of a point
(`TauCeti.IsEilenbergMacLaneSpaceOne.subsingleton_singularHomology_of_isUniquelyTwoDivisible`).
This is the case `n = 1` of the mod-two acyclicity of the Eilenberg--Mac Lane spaces `K(A, n)`,
stated for every space of the homotopy type, which is the form in which the induction through
the path-loop fibrations uses it.

## Main results

* `TauCeti.IsEilenbergMacLaneSpaceOne.nonempty_singularHomologyIsoGroupHomology`: the singular
  homology of a `K(G, 1)` space is the group homology of `G`.
* `TauCeti.IsEilenbergMacLaneSpaceOne.subsingleton_singularHomology_of_bijective_zsmul`: a
  `K(A, 1)` space of a uniquely `m`-divisible abelian group is acyclic modulo `m`.
* `TauCeti.IsEilenbergMacLaneSpaceOne.subsingleton_singularHomology_of_isUniquelyTwoDivisible`:
  a `K(A, 1)` space of a uniquely two-divisible abelian group has the mod-two homology of a point.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 4.1,
  Proposition 4.21, and Section 4.2, Proposition 4.30.
* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  Chapter I.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory

universe u

namespace TauCeti

namespace IsEilenbergMacLaneSpaceOne

/-- **The singular homology of a `K(G, 1)` space is the group homology of `G`.** For every
`K(G, 1)` space `X`, with no hypothesis of CW type, and every commutative ring `k`,
`Hₙ(X; k) ≅ Hₙ(G, k)`, the group homology of `G` with trivial coefficients `k`. -/
theorem nonempty_singularHomologyIsoGroupHomology {G : Type u} [Group G] {X : Type u}
    [TopologicalSpace X] {x : X} (hX : IsEilenbergMacLaneSpaceOne G X x) (k : Type u)
    [CommRing k] (n : ℕ) :
    Nonempty (((singularChains k).obj (TopCat.of X)).homology n ≅
      groupHomology (Rep.trivial k G k) n) := by
  obtain ⟨f, hf⟩ := hX.exists_isWeakHomotopyEquivalence_classifyingSpace
  have := hf.isIso_singularHomologyMap (ModuleCat.of k k) n
  exact ⟨(asIso (((singularHomologyFunctor (ModuleCat.{u} k) n).obj (ModuleCat.of k k)).map
    (TopCat.ofHom f))).symm ≪≫ classifyingSpaceSingularHomologyIsoGroupHomology k G n⟩

variable (k : Type) [CommRing k] [IsSemisimpleRing k] {m : ℤ}

/-- **`K(A, 1)` spaces of uniquely `m`-divisible groups are acyclic modulo `m`.** If
multiplication by the integer `m` is a bijection of the abelian group `A`, then every `K(A, 1)`
space has no homology in positive degrees with coefficients in a commutative semisimple ring `k`
in which `m = 0`. -/
theorem subsingleton_singularHomology_of_bijective_zsmul (hmk : (m : k) = 0) {A : Type}
    [AddCommGroup A] (hA : Function.Bijective fun a : A ↦ m • a) {X : Type} [TopologicalSpace X]
    {x : X} (hX : IsEilenbergMacLaneSpaceOne (Multiplicative A) X x) (n : ℕ) :
    Subsingleton (((singularChains k).obj (TopCat.of X)).homology (n + 1)) :=
  have := subsingleton_groupHomology_of_bijective_zsmul k hmk hA n
  (hX.nonempty_singularHomologyIsoGroupHomology k (n + 1)).some.toLinearEquiv.toEquiv.subsingleton

/-- **Mod-two acyclicity of `K(A, 1)` spaces.** For a uniquely two-divisible abelian group `A`,
every `K(A, 1)` space has the mod-two homology of a point: `Hᵢ(X; 𝔽₂) = 0` for all `i > 0`. -/
theorem subsingleton_singularHomology_of_isUniquelyTwoDivisible {A : Type} [AddCommGroup A]
    (hA : IsUniquelyTwoDivisible A) {X : Type} [TopologicalSpace X] {x : X}
    (hX : IsEilenbergMacLaneSpaceOne (Multiplicative A) X x) (n : ℕ) :
    Subsingleton (((singularChains (ZMod 2)).obj (TopCat.of X)).homology (n + 1)) :=
  subsingleton_singularHomology_of_bijective_zsmul (ZMod 2) (m := 2) (by decide)
    ((isUniquelyTwoDivisible_iff A).1 hA) hX n

end IsEilenbergMacLaneSpaceOne

end TauCeti
