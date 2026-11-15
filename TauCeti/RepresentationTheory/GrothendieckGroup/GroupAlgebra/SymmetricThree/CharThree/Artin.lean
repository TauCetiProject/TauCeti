/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.SymmetricThree.CharThree
import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.SymmetricThree.CharThree.Simple
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.SymmetricThree.Artin
import TauCeti.RepresentationTheory.Induction.Artin.Modular

/-!
# The characteristic-three Artin identity for S₃

In characteristic three, the order-three alternating subgroup contributes
`3 [Ind_{A₃} Res_{A₃} x] = [Ind₁ Res₁ x]`. Removing this term from the integral
Artin identity gives

`6 x = -2 [Ind₁ Res₁ x] + 2 ∑ₐ [Ind_{Stab(a)} Res_{Stab(a)} x]`.

At the trivial class, the known point-stabilizer induction classes then determine the
regular class: `[k[S₃]] = 3[k] + 3[sgn]`. Cancellation takes place in the integral
simple-class coordinates, not in characteristic-three character values. These are
composition-factor identities; no splitting or isomorphism of representations is asserted.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part III, §14.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, §VII.3, (7.3.4).
-/

public section

open scoped MonoidAlgebra

namespace TauCeti

variable (k : Type) [Field k] [CharP k 3]

/-- Removing the three-part of A₃ replaces three times its induced restriction by
induction from the trivial subgroup, for every virtual S₃ module. -/
theorem indK0_resK0_bot_eq_three_nsmul_alternatingGroup_fin_three
    (x : ExactK0 (finiteModulesExactStructure k[Equiv.Perm (Fin 3)])) :
    indK0 k (⊥ : Subgroup (Equiv.Perm (Fin 3)))
        (resK0 k (⊥ : Subgroup (Equiv.Perm (Fin 3))).subtype x) =
      3 • indK0 k (alternatingGroup (Fin 3))
        (resK0 k (alternatingGroup (Fin 3)).subtype x) := by
  have hpow : ∀ c ∈ alternatingGroup (Fin 3),
      ∃ n : ℕ, c ^ 3 ^ n ∈ (⊥ : Subgroup (Equiv.Perm (Fin 3))) := by
    intro c hc
    refine ⟨1, ?_⟩
    have h := pow_card_eq_one' (x := (⟨c, hc⟩ : alternatingGroup (Fin 3)))
    rw [card_alternatingGroup_fin_three] at h
    simpa using congrArg Subtype.val h
  simpa only [Subgroup.relIndex_bot_left, card_alternatingGroup_fin_three] using
    indK0_resK0_eq_relIndex_nsmul (k := k) 3 bot_le hpow x

/-- Artin's identity for S₃ in characteristic three, after removing the three-part.
Only the trivial subgroup and the three subgroups of order two remain. -/
theorem six_nsmul_eq_indK0_resK0_perm_fin_three_char_three
    (x : ExactK0 (finiteModulesExactStructure k[Equiv.Perm (Fin 3)])) :
    6 • x = (-2 : ℤ) • indK0 k (⊥ : Subgroup (Equiv.Perm (Fin 3)))
        (resK0 k (⊥ : Subgroup (Equiv.Perm (Fin 3))).subtype x) +
      2 • (∑ a : Fin 3, indK0 k (MulAction.stabilizer (Equiv.Perm (Fin 3)) a)
        (resK0 k (MulAction.stabilizer (Equiv.Perm (Fin 3)) a).subtype x)) := by
  have h := six_nsmul_eq_indK0_resK0_perm_fin_three k x
  rw [← indK0_resK0_bot_eq_three_nsmul_alternatingGroup_fin_three k x] at h
  convert h using 1
  abel

/-- The regular S₃ module has three trivial and three sign composition factors
in characteristic three, over every coefficient field. -/
@[simp]
theorem permK0_regular_perm_fin_three_char_three :
    permK0 k (Equiv.Perm (Fin 3)) (Equiv.Perm (Fin 3)) =
      3 • (1 : ExactK0 (finiteModulesExactStructure k[Equiv.Perm (Fin 3)])) +
        3 • fdRepK0RingEquiv k (Equiv.Perm (Fin 3))
          (ExactK0.of (FDRep.ofLinearCharacter (signLinearCharacter k (Fin 3)))) := by
  have h := six_nsmul_eq_indK0_resK0_perm_fin_three_char_three k 1
  simp only [resK0_one, indK0_one_stabilizer_perm_fin_three_char_three,
    Fin.sum_univ_three] at h
  rw [indK0_one, permK0_congr k QuotientGroup.quotientBot.toEquiv
    quotientBot_equivariant] at h
  apply (symmetricThreeCharThreeSimpleClassBasis k).repr.injective
  ext b
  have hb := congrArg (fun y ↦ (symmetricThreeCharThreeSimpleClassBasis k).repr y b) h
  simp only [map_add, map_nsmul, map_zsmul, Finsupp.add_apply, Finsupp.smul_apply] at hb ⊢
  simp only [nsmul_eq_mul, zsmul_eq_mul] at hb ⊢
  norm_num at hb ⊢
  omega

end TauCeti
