/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import TauCeti.GroupTheory.GroupAction.Transitive

/-!
# Criteria for multiple transitivity

This file collects two criteria for an action to be multiply transitive.

The full permutation group of a type is `n`-pretransitive for every `n`
(`Equiv.Perm.isMultiplyPretransitive`). Hence so is every action whose permutation representation
`MulAction.toPermHom G α : G →* Equiv.Perm α` is surjective, that is, every action inducing all
permutations of `α`. For a Galois group acting on the embeddings of a field, this is the condition
that the Galois group is the full symmetric group on the embeddings.

A transitive action is doubly transitive as soon as the stabilizer of one point is transitive on
the other points. On `p + 1` points, `p` prime, a single element of that stabilizer suffices: if it
moves a point that its `p`-th power fixes, then the orbit of that point under its powers has `p`
points, which are all the points but one.

## Main results

* `MulAction.isMultiplyPretransitive_of_surjective_toPermHom`: an action inducing every
  permutation is `n`-pretransitive for every `n`.
* `TauCeti.is_two_pretransitive_of_card_eq_succ_of_smul_ne`: a transitive action on `p + 1`
  points, `p` prime, is doubly transitive if some element `a` fixes a point and moves a point that
  `a ^ p` fixes.

## References

* H. Wielandt, *Finite Permutation Groups*, Academic Press, 1964, Theorem 9.1, for double
  transitivity through a point stabilizer.
-/

public section

namespace MulAction

variable {G α : Type*} [Group G] [MulAction G α]

/-- An action inducing every permutation of `α` is `n`-pretransitive for every `n`. -/
theorem isMultiplyPretransitive_of_surjective_toPermHom
    (h : Function.Surjective (toPermHom G α)) (n : ℕ) : IsMultiplyPretransitive G α n := by
  rw [isMultiplyPretransitive_iff]
  intro x y
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_smul_eq_embedding x y
  obtain ⟨g, rfl⟩ := h π
  exact ⟨g, Function.Embedding.ext fun i ↦ by
    simpa [smul_apply] using DFunLike.congr_fun hπ i⟩

end MulAction

namespace TauCeti

open _root_.MulAction

/-- **Double transitivity in degree `p + 1`.** Let a group `G` act transitively on `p + 1` points,
`p` prime. If some element `a` of `G` fixes a point and moves a point `y` that `a ^ p` fixes, then
the action of `G` is doubly transitive.

For a group of permutations containing a cycle with a unique fixed point, of any length, see
`TauCeti.is_two_pretransitive_of_isCycle_mem_of_existsUnique_fixedPoint`. The present statement
is about an arbitrary action, which need not be faithful, and asks only for the period of one
moved point. -/
theorem is_two_pretransitive_of_card_eq_succ_of_smul_ne
    {G X : Type*} [Group G] [MulAction G X] [IsPretransitive G X]
    {p : ℕ} (hp : p.Prime) (hcard : Nat.card X = p + 1)
    {a : G} {x y : X} (hx : a • x = x) (hy : a ^ p • y = y) (hay : a • y ≠ y) :
    IsMultiplyPretransitive G X 2 := by
  have : Finite X := Nat.finite_of_card_ne_zero (by omega)
  have hax : a ∈ stabilizer G x := mem_stabilizer_iff.mpr hx
  have hyx : y ∈ SubMulAction.ofStabilizer G x :=
    (SubMulAction.mem_ofStabilizer_iff G x).mpr fun h ↦ hay (h ▸ hx)
  -- The element `a` of the stabilizer of `x` moves the point `y` of the complement of `x`, which
  -- has `p` points, and `a ^ p` fixes it: the stabilizer of `x` is transitive on this complement.
  have hY : Nat.card (SubMulAction.ofStabilizer G x) = p := by
    rw [SubMulAction.nat_card_ofStabilizer_eq, hcard, Nat.add_sub_cancel]
  have : IsPretransitive (stabilizer G x) (SubMulAction.ofStabilizer G x) :=
    isPretransitive_of_prime_natCard_of_smul_ne (hY ▸ hp) (g := ⟨a, hax⟩) (x := ⟨y, hyx⟩)
      (Subtype.ext (by
        rw [hY, SubMulAction.val_smul, subgroup_smul_def, Subgroup.coe_pow, hy]))
      fun h ↦ hay (by
        simpa only [SubMulAction.val_smul, subgroup_smul_def] using congrArg Subtype.val h)
  exact SubMulAction.ofStabilizer.isMultiplyPretransitive.mpr (is_one_pretransitive_iff.mpr this)

end TauCeti
