/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Mackey.Basic
public import TauCeti.RepresentationTheory.Symmetric.SignCharacter
public import TauCeti.RepresentationTheory.LinearCharacter.Basic
import TauCeti.GroupTheory.DoubleCoset.PointStabilizer
import TauCeti.GroupTheory.Perm.FinThree.Basic
import TauCeti.RepresentationTheory.CharacterTable.Determined

/-!
# The two Mackey terms for the sign character of a point stabilizer in `S₃`

Let `H` be the stabilizer of a point in `S₃`. The two double cosets are represented by
`1` and a transposition moving that point. The identity term of the Mackey restriction
formula is the sign representation of `H`. The other term is induced from the trivial
intersection of the two stabilizers and has the regular character of `H`.

Compute each term over every field, and sum them using the Mackey character formula.
In characteristic zero this identifies the restricted induced representation as the
trivial representation plus two copies of sign. Thus the extra intertwining term that
prevents the induced sign representation from being irreducible is visible explicitly.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, §7.3–7.4.
* I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 5.
-/

public section

open CategoryTheory

namespace TauCeti

-- The Mackey summand and character decomposition APIs use one universe for the field and group.
variable (k : Type) [Field k] (a : Fin 3)

local notation "H" => MulAction.stabilizer (Equiv.Perm (Fin 3)) a
local notation "χ" => MonoidHom.comp (signLinearCharacter k (Fin 3)) (Subgroup.subtype H)
local notation "A" => FDRep.ofLinearCharacter χ

private theorem mackeyClassFun_sign_stabilizer_perm_fin_three (s : Equiv.Perm (Fin 3)) :
    mackeyClassFun s H H (A).character =
      fun y : (mackeySubgroup s H H).subgroupOf H => (χ (y : H) : k) := by
  funext y
  simp [mackeyClassFun_apply, coe_mackeyToH_apply, map_mul, map_inv, mul_comm]

/-- The Mackey character term is sign on the identity double coset and the regular
character on the other double coset. This formula is valid in every characteristic. -/
theorem character_mackeySummand_sign_stabilizer_perm_fin_three
    (s : Equiv.Perm (Fin 3)) (x : H) :
    (mackeySummand (K := H) s A).character x =
      if s ∈ H then (χ x : k) else if x = 1 then 2 else 0 := by
  classical
  rw [character_mackeySummand, mackeyClassFun_sign_stabilizer_perm_fin_three]
  -- Keep the finite-index instance inside this function when transporting its subgroup.
  -- Rewriting the subgroup directly would leave an instance with the old type.
  let F (J : Subgroup H) := Subgroup.indClassFun J (fun y => (χ (y : H) : k)) x
  have hF : Subgroup.indClassFun ((mackeySubgroup s H H).subgroupOf H)
      (fun y => (χ (y : H) : k)) x = F ((mackeySubgroup s H H).subgroupOf H) := rfl
  rw [hF]
  by_cases hs : s ∈ H
  · rw [ite_eq_left hs, mackeySubgroup_subgroupOf_self_of_mem hs]
    exact Subgroup.indClassFun_top
      (f := fun y => (χ (y : H) : k)) (fun y t => by simp [map_mul, map_inv, mul_comm]) x
  · have hbot : (mackeySubgroup s H H).subgroupOf H = ⊥ := by
      rw [mackeySubgroup_def,
        (isTISubgroup_iff_inf_conj_smul_eq_bot.mp
          (isTISubgroup_stabilizer_perm_fin_three a)) s hs,
        Subgroup.bot_subgroupOf]
    rw [ite_eq_right hs, hbot]
    simp only [F, Subgroup.indClassFun_bot, card_stabilizer_perm_fin_three]
    simp

/-- Restricting the sign representation induced from a point stabilizer of `S₃` gives
sign plus the regular character of the stabilizer. The two terms are exactly the two
Mackey terms. -/
theorem character_resFDRep_indFDRep_sign_stabilizer_perm_fin_three (x : H) :
    ((H).resFDRep (indFDRep A)).character x = (χ x : k) + if x = 1 then 2 else 0 := by
  classical
  let D₀ := DoubleCoset.mk H H (1 : Equiv.Perm (Fin 3))
  let D₁ := DoubleCoset.mk H H (Equiv.swap a (a + 1))
  have hswap : Equiv.swap a (a + 1) a ≠ a := by
    rw [Equiv.swap_apply_left]
    revert a
    decide
  have hne : D₀ ≠ D₁ := fun h => hswap
    ((doubleCosetMk_stabilizer_eq_one_iff a).mp h.symm)
  let := Fintype.ofFinite
    (DoubleCoset.Quotient (H : Set (Equiv.Perm (Fin 3))) (H : Set (Equiv.Perm (Fin 3))))
  have huniv : (Finset.univ : Finset
      (DoubleCoset.Quotient (H : Set (Equiv.Perm (Fin 3)))
        (H : Set (Equiv.Perm (Fin 3))))) = {D₀, D₁} := by
    ext D
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    by_cases hD : D = D₀
    · exact Or.inl hD
    · refine Or.inr ?_
      have hmem : D.out a ≠ a := fun h => hD
        ((DoubleCoset.out_eq' D).symm.trans
          ((doubleCosetMk_stabilizer_eq_one_iff a).mpr h))
      exact (DoubleCoset.out_eq' D).symm.trans
        (Quotient.sound' (doubleCoset_rel_stabilizer_of_ne_of_ne a hmem hswap))
  have h₀ : D₀.out ∈ H :=
    (doubleCosetMk_eq_mk_one_iff_mem H _).mp (DoubleCoset.out_eq' D₀)
  have h₁ : D₁.out ∉ H := fun h => hne
    ((DoubleCoset.out_eq' D₁).symm.trans
      ((doubleCosetMk_eq_mk_one_iff_mem H _).mpr h)).symm
  rw [character_resFDRep_indFDRep_mackey]
  rw [huniv, Finset.sum_pair hne]
  simp only [character_mackeySummand_sign_stabilizer_perm_fin_three,
    ite_eq_left h₀, ite_eq_right h₁]

/-- The restricted induced sign character is the trivial character plus twice sign,
including in positive characteristic. -/
theorem character_resFDRep_indFDRep_sign_stabilizer_perm_fin_three_eq_one_add (x : H) :
    ((H).resFDRep (indFDRep A)).character x = 1 + 2 * (χ x : k) := by
  classical
  rw [character_resFDRep_indFDRep_sign_stabilizer_perm_fin_three]
  by_cases hx : x = 1
  · subst x
    simp
  · have hval : (x : Equiv.Perm (Fin 3)) = Equiv.swap (a + 1) (a + 2) :=
      ((mem_stabilizer_perm_fin_three_iff a _).mp x.2).resolve_left
        (fun h => hx (Subtype.ext h))
    have hidx : (a + 1 : Fin 3) ≠ a + 2 := by revert a; decide
    simp [hx, hval, signLinearCharacter_swap hidx]
    ring

/-- In characteristic zero, the sign representation induced from a point stabilizer of
`S₃` restricts to the trivial representation plus two copies of sign. -/
theorem nonempty_iso_resFDRep_indFDRep_sign_stabilizer_perm_fin_three [CharZero k] :
    Nonempty ((H).resFDRep (indFDRep A) ≅
      FDRep.of (Representation.trivial k H k) ⊞ (A ⊞ A)) := by
  apply FDRep.nonempty_iso_of_character_eq
  funext x
  simp only [FDRep.char_biprod, Pi.add_apply, FDRep.character_of,
    Representation.char_trivial, FDRep.char_ofLinearCharacter, Module.finrank_self, Nat.cast_one]
  rw [character_resFDRep_indFDRep_sign_stabilizer_perm_fin_three_eq_one_add]
  ring

end TauCeti
