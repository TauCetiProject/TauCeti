/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.ModTwoVanishing
public import TauCeti.Topology.PathSpace.Moore.Comparison.HomotopyGroup

/-!
# Mod-two vanishing for the contractible loops of a space

Serre's mod-two vanishing theorem says that the homotopy groups of a simply connected space with
the mod-two homology of a point are uniquely two-divisible
(`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology`). This file
applies it to the component `Ω₀X` of the constant loop in the loop space of a pointed space
`(X, x)`, the space of contractible loops at `x`.

The path-component form of the theorem applies to the component of the constant loop
(`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_pathComponent`),
and the loop-space shift `πₖ₊₁(ΩX) ≅ πₖ₊₂(X)` turns its conclusion into a statement about `X`.
Suppose `π₂(X, x) = 0`, so that `Ω₀X` is simply connected. If
`Hᵢ(Ω₀X; 𝔽₂) = 0` for `i > 0`, then every homotopy group `πₙ₊₃(X, x)` is uniquely two-divisible,
hence `πₙ₊₃(X, x) ⊗ ℤ/2 = 0`. Contrapositively, a space with `π₂(X) = 0` and
`π_ℓ(X) ⊗ ℤ/2 ≠ 0` for some `ℓ ≥ 3` has contractible loops with nonzero reduced mod-two homology.
This is the topological step in Barraud–Damian–Humilière–Oancea's proof of their Theorem 5.15,
where it replaces an appeal to Hurewicz modulo the class of groups `G` with `G ⊗ ℤ/2 = 0`, which
is not a Serre class.

Both loop models are treated: the fixed-interval loops `Ω X x = Path x x`
(`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_loopSpace`), and
the Moore loops `MooreLoopSpace X x`
(`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_mooreLoopSpace`),
whose constant loop is the loop `1` of length zero.

## Main results

* `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_loopSpace`,
  `TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_mooreLoopSpace`:
  if `π₂(X, x) = 0` and the contractible loops at `x` have the mod-two homology of a point, the
  homotopy groups `πₙ₊₃(X, x)` are uniquely two-divisible.

## References

* J.-P. Serre, *Groupes d'homotopie et classes de groupes abéliens*, Ann. of Math. 58 (1953),
  258–294.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, proof of Theorem 5.15.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology

open scoped Topology Topology.Homotopy

namespace TauCeti

variable {X : Type} [TopologicalSpace X] (x : X)

/-- **Mod-two vanishing for the contractible loops.** If `π₂(X, x)` is trivial and the path
component of the constant loop in the loop space `Ω X x` has the mod-two homology of a point,
then every homotopy group `πₙ₊₃(X, x)` is uniquely two-divisible. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_loopSpace
    [Subsingleton (π_ 2 X x)]
    (hX : ∀ i, Subsingleton
      (((singularChains (ZMod 2)).obj (TopCat.of (pathComponent (Path.refl x)))).homology (i + 1)))
    (n : ℕ) : IsUniquelyTwoDivisible (Additive (π_ (n + 3) X x)) :=
  -- The fundamental group of the loop space is `π₂(X, x)`.
  have : Subsingleton (FundamentalGroup (Ω X x) (Path.refl x)) :=
    HomotopyGroup.fundamentalGroupLoopSpaceMulEquiv.toEquiv.subsingleton_congr.2 ‹_›
  (isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_pathComponent
    (Path.refl x) hX n).of_addEquiv (HomotopyGroup.pathLoopSpaceMulEquiv (n + 1)).toAdditive

/-- **Mod-two vanishing for the contractible Moore loops.** If `π₂(X, x)` is trivial and the path
component of the constant loop `1` in the Moore loop space has the mod-two homology of a point,
then every homotopy group `πₙ₊₃(X, x)` is uniquely two-divisible. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_mooreLoopSpace
    [Subsingleton (π_ 2 X x)]
    (hX : ∀ i, Subsingleton (((singularChains (ZMod 2)).obj
      (TopCat.of (pathComponent (1 : MooreLoopSpace X x)))).homology (i + 1)))
    (n : ℕ) : IsUniquelyTwoDivisible (Additive (π_ (n + 3) X x)) :=
  -- The fundamental group of the Moore loop space is `π₂(X, x)`.
  have : Subsingleton (FundamentalGroup (MooreLoopSpace X x) 1) :=
    (HomotopyGroup.pi1MulEquivFundamentalGroup.symm.trans
      (MooreLoopSpace.homotopyGroupMulEquiv x 0)).toEquiv.subsingleton_congr.2 ‹_›
  (isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_pathComponent
    (1 : MooreLoopSpace X x) hX n).of_addEquiv
      (MooreLoopSpace.homotopyGroupMulEquiv x (n + 1)).toAdditive

end TauCeti
