/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.ZModVanishing
public import TauCeti.Topology.PathSpace.Moore.Comparison.HomotopyGroup
import TauCeti.Topology.Homotopy.HomotopyGroup.PathComponent

/-!
# Mod-two vanishing for the contractible loops of a space

Serre's mod-two vanishing theorem says that the higher homotopy groups at a base point with
trivial fundamental group and mod-two acyclic ambient space are uniquely two-divisible
(`TauCeti.isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_modTwo`). This file
applies it to the component `Ω₀X` of the constant loop in the loop space of a pointed space
`(X, x)`, the space of contractible loops at `x`.

Since a path component has the homotopy groups of the ambient space in positive degrees
(`HomotopyGroup.subtypeValMulEquivOfPathComponentSubset`), applying the mod-two vanishing theorem
to the component of the constant loop and composing with the loop-space shift `πₖ₊₁(ΩX) ≅ πₖ₊₂(X)`
turns its conclusion into a statement about `X`. Suppose `π₂(X, x) = 0`, so that `Ω₀X` has
trivial fundamental group. If `Hᵢ(Ω₀X; 𝔽₂) = 0` for `i > 0`, then every homotopy group
`πₙ₊₃(X, x)` is uniquely two-divisible, hence `πₙ₊₃(X, x) ⊗ ℤ/2 = 0`. Contrapositively, a space
with `π₂(X) = 0` and `π_ℓ(X) ⊗ ℤ/2 ≠ 0` for some `ℓ ≥ 3` has contractible loops with nonzero
reduced mod-two homology. This is the topological step in Barraud–Damian–Humilière–Oancea's
proof of their Theorem 5.15, where it replaces an appeal to Hurewicz modulo the class of groups
`G` with `G ⊗ ℤ/2 = 0`, which is not a Serre class.

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
  -- The fundamental group of the path component of `Path.refl x` is `π₂(X, x)`.
  let c₀ : pathComponent (Path.refl x) := ⟨Path.refl x, mem_pathComponent_self _⟩
  have : Subsingleton (π_ 1 (pathComponent (Path.refl x)) c₀) :=
    ((HomotopyGroup.subtypeValMulEquivOfPathComponentSubset subset_rfl rfl).trans
      (HomotopyGroup.pathLoopSpaceMulEquiv 0)).toEquiv.subsingleton_congr.2 ‹_›
  (isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_modTwo (y := c₀) (n := n)
    fun q hq _ ↦ by
      obtain ⟨q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
      exact ModuleCat.isZero_iff_subsingleton.2 (hX q')).of_addEquiv
    ((HomotopyGroup.subtypeValMulEquivOfPathComponentSubset subset_rfl rfl).trans
      (HomotopyGroup.pathLoopSpaceMulEquiv (n + 1))).toAdditive

/-- **Mod-two vanishing for the contractible Moore loops.** If `π₂(X, x)` is trivial and the path
component of the constant loop `1` in the Moore loop space has the mod-two homology of a point,
then every homotopy group `πₙ₊₃(X, x)` is uniquely two-divisible. -/
theorem isUniquelyTwoDivisible_homotopyGroup_of_subsingleton_singularHomology_mooreLoopSpace
    [Subsingleton (π_ 2 X x)]
    (hX : ∀ i, Subsingleton (((singularChains (ZMod 2)).obj
      (TopCat.of (pathComponent (1 : MooreLoopSpace X x)))).homology (i + 1)))
    (n : ℕ) : IsUniquelyTwoDivisible (Additive (π_ (n + 3) X x)) :=
  -- The fundamental group of the path component of `1` is `π₂(X, x)`.
  let c₀ : pathComponent (1 : MooreLoopSpace X x) := ⟨1, mem_pathComponent_self _⟩
  have : Subsingleton (π_ 1 (pathComponent (1 : MooreLoopSpace X x)) c₀) :=
    ((HomotopyGroup.subtypeValMulEquivOfPathComponentSubset subset_rfl rfl).trans
      (MooreLoopSpace.homotopyGroupMulEquiv x 0)).toEquiv.subsingleton_congr.2 ‹_›
  (isUniquelyTwoDivisible_homotopyGroup_of_isZero_singularHomology_modTwo (y := c₀) (n := n)
    fun q hq _ ↦ by
      obtain ⟨q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
      exact ModuleCat.isZero_iff_subsingleton.2 (hX q')).of_addEquiv
    ((HomotopyGroup.subtypeValMulEquivOfPathComponentSubset subset_rfl rfl).trans
      (MooreLoopSpace.homotopyGroupMulEquiv x (n + 1))).toAdditive

end TauCeti
