/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.FinThree.ArtinCoefficient
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Artin

/-!
# The explicit Artin identity for `S₃` in every characteristic

The Artin coefficients of `S₃` give

`6 [k] = -3 [k[S₃]] + 2 ∑ₐ [k[S₃ / Stab(a)]] + 3 [k[S₃ / A₃]]`.

This is an identity in the exact Grothendieck group, over every field: neither
characteristic two nor characteristic three is excluded. Multiplying by an arbitrary
virtual class gives the corresponding identity among its induced restrictions.
In particular, the displayed relation does not assert that the representations are
isomorphic or that any short exact sequences split.

The proof evaluates `TauCeti.natCard_nsmul_eq_sum_artinCoeff_indK0_resK0` using the
six-subgroup enumeration and the integral coefficients.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, §9.2.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, §VII.3, (7.3.4).
-/

public section

open scoped MonoidAlgebra

namespace TauCeti

/-- Artin's induction identity for every virtual `S₃`-module, with explicit integer
coefficients, over an arbitrary field. -/
theorem six_nsmul_eq_indK0_resK0_perm_fin_three (k : Type) [Field k]
    (x : ExactK0 (finiteModulesExactStructure k[Equiv.Perm (Fin 3)])) :
    6 • x = (-3 : ℤ) • indK0 k (⊥ : Subgroup (Equiv.Perm (Fin 3)))
        (resK0 k (⊥ : Subgroup (Equiv.Perm (Fin 3))).subtype x) +
      2 • (∑ a : Fin 3, indK0 k (MulAction.stabilizer (Equiv.Perm (Fin 3)) a)
        (resK0 k (MulAction.stabilizer (Equiv.Perm (Fin 3)) a).subtype x)) +
      3 • indK0 k (alternatingGroup (Fin 3)) (resK0 k (alternatingGroup (Fin 3)).subtype x) := by
  have h := natCard_nsmul_eq_sum_artinCoeff_indK0_resK0 k (Equiv.Perm (Fin 3)) x
  simp only [Subgroup.finsum_fin_three, artinCoeff_bot_perm_fin_three,
    artinCoeff_stabilizer_perm_fin_three, artinCoeff_alternatingGroup_fin_three,
    artinCoeff_top_perm_fin_three, card_stabilizer_perm_fin_three,
    card_alternatingGroup_fin_three, Subgroup.card_bot, Nat.cast_one, mul_one,
    one_mul, zero_mul, zero_smul, add_zero] at h
  have hg : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  rw [hg] at h
  simpa only [Fin.sum_univ_three, smul_add, natCast_zsmul, add_assoc] using h

end TauCeti
