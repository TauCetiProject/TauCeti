/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The kernel of an action on a cyclic group

Let a group `G` act by additive automorphisms on a cyclic group `A`. The action factors through
the automorphism group of `A`, which Mathlib identifies with the units of `ZMod (Nat.card A)`
(`IsCyclic.mulAutMulEquiv`, read additively through `MulAutMultiplicative`). Consequently the
kernel of the action has index dividing `φ (Nat.card A)` (`index_ker_toPermHom_dvd_totient`) and
the quotient of `G` by it is commutative (`isMulCommutative_quotient_ker_toPermHom`).

For the roots of unity `μₙ` of a field this says that adjoining `μₙ` to a field is an abelian
extension of degree dividing `φ n`, the input used to make a finite Galois layer contain `μₙ`
without changing the primes dividing its degree, beyond those dividing `φ n`.
-/

public section

namespace TauCeti

variable (G : Type*) [Group G] (A : Type*) [AddGroup A] [DistribMulAction G A] [IsAddCyclic A]

/-- The action of `G` on the cyclic group `A`, read in the units of `ZMod (Nat.card A)` through
Mathlib's identification of the automorphisms of a cyclic group. -/
private noncomputable def actionUnits : G →* (ZMod (Nat.card (Multiplicative A)))ˣ :=
  ((MulAutMultiplicative A).symm.trans
      (IsCyclic.mulAutMulEquiv (Multiplicative A))).toMonoidHom.comp
    (DistribMulAction.toAddAut G A)

/-- The units-valued form of the action has the kernel of the action itself. -/
private theorem ker_actionUnits : (actionUnits G A).ker = (MulAction.toPermHom G A).ker := by
  ext g
  simp only [actionUnits, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, Equiv.ext_iff]
  -- `Multiplicative.toAdd` is the identity on the underlying automorphism `x ↦ g • x`, which
  -- `simp` does not see through, so both directions are closed up to that unfolding.
  constructor
  · intro h x
    exact DFunLike.congr_fun (congrArg Multiplicative.toAdd h) x
  · intro h
    exact Multiplicative.toAdd.injective (AddEquiv.ext h)

/-- **The kernel of an action on a cyclic group has index dividing `φ (Nat.card A)`**: the action
factors through the automorphism group of `A`, which has `φ (Nat.card A)` elements. For an
infinite cyclic `A` the statement is empty, `φ 0 = 0`. -/
theorem index_ker_toPermHom_dvd_totient :
    (MulAction.toPermHom G A).ker.index ∣ (Nat.card A).totient := by
  rcases finite_or_infinite A with hA | hA
  · have : Finite (Multiplicative A) := hA
    rw [← ker_actionUnits, Subgroup.index_ker]
    refine (Subgroup.card_subgroup_dvd_card (actionUnits G A).range).trans (dvd_of_eq ?_)
    rw [← Nat.card_congr (IsCyclic.mulAutMulEquiv (Multiplicative A)).toEquiv,
      IsCyclic.card_mulAut]
    rfl
  · rw [Nat.card_eq_zero_of_infinite, Nat.totient_zero]
    exact dvd_zero _

/-- **The quotient by the kernel of an action on a cyclic group is commutative**: it embeds into
the automorphism group of `A`, the units of `ZMod (Nat.card A)`. -/
theorem isMulCommutative_quotient_ker_toPermHom :
    IsMulCommutative (G ⧸ (MulAction.toPermHom G A).ker) := by
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
    (ker_actionUnits G A ▸ Abelianization.commutator_subset_ker (actionUnits G A))

end TauCeti
