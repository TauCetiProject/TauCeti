/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.Alternating.Standard
public import TauCeti.RepresentationTheory.Symmetric.SignCharacter
public import TauCeti.RepresentationTheory.CharacterTwist
public import TauCeti.RepresentationTheory.Induction.LiesOver
import TauCeti.RepresentationTheory.Induction.Permutation
import TauCeti.RepresentationTheory.Induction.Character
import TauCeti.RepresentationTheory.Induction.FrobeniusReciprocity
import TauCeti.RepresentationTheory.CharacterTable.Determined

/-!
# Recovering the fixed constituents for `A₄ ◁ S₄`

Inducing the restriction of a symmetric-group representation gives its direct sum with its
sign twist, in characteristic zero. If the original representation is simple, then a simple
representation lying over that restriction is one of these two summands. This identifies the
representations of `S₄` lying over the fixed trivial and three-dimensional constituents of `A₄`.

The character identity holds over every field. The decomposition and recovery use
characteristic zero, where characters determine representations; algebraic closure is unnecessary.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 6.
* J.-P. Serre, *Linear Representations of Finite Groups*, §7.2.
* The coset character formula `TauCeti.character_indFDRep_sum_quotient` and Mathlib's
  induction–restriction adjunction, through `TauCeti.finrank_hom_indFDRep`.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace FDRep

open TauCeti

variable {k : Type u} [Field k] {α : Type v} [Fintype α] [DecidableEq α] [Nontrivial α]

/-- Inducing a restricted symmetric-group representation adds its sign twist to its character.
This identity is valid in every characteristic. -/
@[simp]
theorem character_ind_res_alternatingGroup (B : FDRep k (Equiv.Perm α)) (g : Equiv.Perm α) :
    (indFDRep ((alternatingGroup α).resFDRep B)).character g =
      B.character g + (signLinearCharacter k α g : k) * B.character g := by
  classical
  by_cases hg : g ∈ alternatingGroup α
  · have hconj (x : Equiv.Perm α) : x⁻¹ * g * x ∈ alternatingGroup α := by
      simpa using (inferInstance : (alternatingGroup α).Normal).conj_mem g hg x⁻¹
    rw [character_indFDRep_sum_quotient]
    simp only [dite_eq_left (hconj _), Subgroup.resFDRep, character_actionRes,
      Subgroup.subtype_apply]
    have hc (x : Equiv.Perm α) : B.character (x⁻¹ * g * x) = B.character g := by
      simpa using B.char_conj g x⁻¹
    simp only [hc]
    simp [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, alternatingGroup.index_eq_two,
      coe_signLinearCharacter_apply, Equiv.Perm.mem_alternatingGroup.mp hg, two_mul]
  · rw [character_indFDRep_eq_zero_of_notMem _ hg]
    have hsign : Equiv.Perm.sign g = -1 :=
      (Int.units_eq_one_or (Equiv.Perm.sign g)).resolve_left
        (fun h => hg (Equiv.Perm.mem_alternatingGroup.mpr h))
    simp [coe_signLinearCharacter_apply, hsign]

variable [CharZero k]

/-- Inducing a restricted symmetric-group representation recovers the representation and its
sign twist as a direct sum. -/
theorem nonempty_iso_ind_res_alternatingGroup (B : FDRep k (Equiv.Perm α)) :
    Nonempty (indFDRep ((alternatingGroup α).resFDRep B) ≅
      B ⊞ FDRep.of (Representation.charTwist (signLinearCharacter k α) B.ρ)) := by
  apply nonempty_iso_of_character_eq
  ext g
  simp only [char_biprod, Pi.add_apply, character_of, Representation.char_charTwist]
  exact character_ind_res_alternatingGroup B g

omit [Nontrivial α] [CharZero k] in
/-- Restricting a sign twist to the alternating group gives the original restriction,
by the identity on carriers. -/
noncomputable def resSignTwistAlternatingGroupIso (B : FDRep k (Equiv.Perm α)) :
    (alternatingGroup α).resFDRep
        (FDRep.of (Representation.charTwist (signLinearCharacter k α) B.ρ)) ≅
      (alternatingGroup α).resFDRep B := by
  refine Action.mkIso (Iso.refl _) fun g => ?_
  ext x
  -- Restriction preserves the carrier and precomposes the action; `FDRep` has no action
  -- evaluation lemma for restriction, so expose only that defining computation here.
  change Representation.charTwist (signLinearCharacter k α) B.ρ g.val x = B.ρ g.val x
  simp [Equiv.Perm.mem_alternatingGroup.mp g.property]

omit [Nontrivial α] [CharZero k] in
/-- The restriction isomorphism for a sign twist is the identity on elements. -/
@[simp]
theorem resSignTwistAlternatingGroupIso_hom_apply (B : FDRep k (Equiv.Perm α)) (x : B) :
    ((resSignTwistAlternatingGroupIso B).hom x : B) = x :=
  (rfl)

omit [Nontrivial α] [CharZero k] in
/-- The inverse restriction isomorphism for a sign twist is the identity on elements. -/
@[simp]
theorem resSignTwistAlternatingGroupIso_inv_apply (B : FDRep k (Equiv.Perm α)) (x : B) :
    ((resSignTwistAlternatingGroupIso B).inv x : B) = x :=
  (rfl)

end FDRep

namespace FDRep

open TauCeti

variable {k α : Type u} [Field k] [CharZero k] [Fintype α] [DecidableEq α] [Nontrivial α]

/-- A simple symmetric-group representation lies over the restriction of a simple representation
exactly when it is that representation or its sign twist. -/
theorem liesOver_res_alternatingGroup_iff (W B : FDRep k (Equiv.Perm α)) [Simple W] [Simple B] :
    W.LiesOver (alternatingGroup α).subtype ((alternatingGroup α).resFDRep B) ↔
      Nonempty (B ≅ W) ∨
        Nonempty (FDRep.of (Representation.charTwist (signLinearCharacter k α) B.ρ) ≅ W) := by
  classical
  let T := FDRep.of (Representation.charTwist (signLinearCharacter k α) B.ρ)
  have hT : Simple T := by
    apply (FDRep.simple_iff_isIrreducible T).mpr
    simpa only [T, of_ρ'] using
      (Representation.isIrreducible_charTwist_iff (signLinearCharacter k α) B.ρ).mpr
        (FDRep.isIrreducible_of_simple B)
  have hB : Nontrivial B := (FDRep.isIrreducible_of_simple B).nontrivial
  have hself := liesOver_res_self B (alternatingGroup α).subtype
  constructor
  · intro h
    have hpos := (Module.finrank_pos_iff_exists_ne_zero (R := k)).mpr (liesOver_iff.mp h)
    rw [← finrank_hom_indFDRep] at hpos
    obtain ⟨f, hf⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := k)).mp hpos
    let e := (nonempty_iso_ind_res_alternatingGroup B).some
    let t : B ⊞ T ⟶ W := e.inv ≫ f
    have ht : t ≠ 0 := fun h => hf ((cancel_epi e.inv).mp (h.trans comp_zero.symm))
    by_cases hl : biprod.inl ≫ t = 0
    · have hr : biprod.inr ≫ t ≠ 0 := fun hr => ht (biprod.hom_ext' _ _ (by simpa) (by simpa))
      have := isIso_of_hom_simple hr
      exact Or.inr ⟨asIso (biprod.inr ≫ t)⟩
    · have := isIso_of_hom_simple hl
      exact Or.inl ⟨asIso (biprod.inl ≫ t)⟩
  · intro h
    rcases h with h | h
    · obtain ⟨e⟩ := h
      exact hself.of_iso_left e
    · obtain ⟨e⟩ := h
      have ht := hself.of_res_iso (resSignTwistAlternatingGroupIso B).symm
      exact ht.of_iso_left e

end FDRep

namespace FDRep

open TauCeti

variable {k : Type} [Field k] [CharZero k]

/-- The simple representations of `S₄` lying over the three-dimensional constituent of `A₄`
are precisely the standard representation and its sign twist. -/
theorem liesOver_alternatingGroupFourStandard_iff (W : FDRep k (Equiv.Perm (Fin 4))) [Simple W] :
    W.LiesOver (alternatingGroup (Fin 4)).subtype (alternatingGroupFourStandard k) ↔
      Nonempty (FDRep.of (standardRepresentation k (Fin 4)) ≅ W) ∨
        Nonempty (FDRep.of (Representation.charTwist (signLinearCharacter k (Fin 4))
          (standardRepresentation k (Fin 4))) ≅ W) := by
  have hB : Simple (FDRep.of (standardRepresentation k (Fin 4))) := by
    apply (FDRep.simple_iff_isIrreducible _).mpr
    rw [of_ρ']
    exact isIrreducible_standardRepresentation (by norm_num) (Or.inr (by norm_num))
  simpa only [alternatingGroupFourStandard_def, of_ρ'] using
    liesOver_res_alternatingGroup_iff W (FDRep.of (standardRepresentation k (Fin 4)))

end FDRep

namespace FDRep

open TauCeti

variable {k α : Type u} [Field k] [CharZero k] [Fintype α] [DecidableEq α] [Nontrivial α]

/-- The simple representations lying over the trivial alternating-group representation are
precisely the trivial and sign representations. -/
theorem liesOver_trivial_alternatingGroup_iff (W : FDRep k (Equiv.Perm α)) [Simple W] :
    W.LiesOver (alternatingGroup α).subtype
        (FDRep.ofLinearCharacter (1 : alternatingGroup α →* kˣ)) ↔
      Nonempty (FDRep.ofLinearCharacter (1 : Equiv.Perm α →* kˣ) ≅ W) ∨
        Nonempty (FDRep.ofLinearCharacter (signLinearCharacter k α) ≅ W) := by
  have hB : Simple (FDRep.of (Representation.trivial k (Equiv.Perm α) k)) := by
    apply (FDRep.simple_iff_isIrreducible _).mpr
    rw [of_ρ']
    infer_instance
  have h := liesOver_res_alternatingGroup_iff W
    (FDRep.of (Representation.trivial k (Equiv.Perm α) k))
  -- Restricting the trivial action preserves its carrier and trivial action by definition.
  have hres : (alternatingGroup α).resFDRep
      (FDRep.of (Representation.trivial k (Equiv.Perm α) k)) =
      FDRep.of (Representation.trivial k (alternatingGroup α) k) := (rfl)
  rw [hres] at h
  simpa only [ofLinearCharacter_def, of_ρ', Representation.ofLinearCharacter_one,
    Representation.charTwist_trivial] using h

end FDRep

namespace TauCeti

/-- The trivial and sign representations of a nontrivial symmetric group are nonisomorphic
when `2 ≠ 0`. These give distinct extensions of the trivial alternating-group representation. -/
theorem not_nonempty_iso_trivial_sign (k : Type*) [CommRing k] [NeZero (2 : k)]
    (α : Type*) [Fintype α] [DecidableEq α] [Nontrivial α] :
    ¬ Nonempty (FDRep.ofLinearCharacter (1 : Equiv.Perm α →* kˣ) ≅
      FDRep.ofLinearCharacter (signLinearCharacter k α)) := by
  rw [FDRep.nonempty_iso_ofLinearCharacter_iff]
  intro h
  obtain ⟨i, j, hij⟩ := exists_pair_ne α
  have hswap := congrArg (fun χ : Equiv.Perm α →* kˣ => (χ (Equiv.swap i j) : k)) h
  simp only [MonoidHom.one_apply, Units.val_one, signLinearCharacter_swap hij,
    Units.val_neg] at hswap
  have htwo : (2 : k) = 0 := by linear_combination hswap
  exact NeZero.ne (2 : k) htwo

variable (k : Type*) [Field k] [NeZero (2 : k)]

/-- The standard representation of `S₄` and its sign twist are nonisomorphic when `2 ≠ 0`.
In characteristic zero these are distinct extensions of the three-dimensional constituent
of `A₄`. -/
theorem not_nonempty_iso_standard_signTwist_fin_four :
    ¬ Nonempty (FDRep.of (standardRepresentation k (Fin 4)) ≅
      FDRep.of (Representation.charTwist (signLinearCharacter k (Fin 4))
        (standardRepresentation k (Fin 4)))) := by
  rintro ⟨e⟩
  have h := congrFun (FDRep.char_iso e) (Equiv.swap 0 1)
  have hcount : Nat.card {x : Fin 4 // Equiv.swap (0 : Fin 4) 1 x = x} = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide
  simp only [FDRep.character_of, Representation.char_charTwist,
    char_standardRepresentation, char_ofMulAction, Equiv.Perm.smul_def,
    signLinearCharacter_swap (k := k) (by decide : (0 : Fin 4) ≠ 1),
    Units.val_neg, Units.val_one, hcount] at h
  have htwo : (2 : k) = 0 := by linear_combination h
  exact NeZero.ne (2 : k) htwo

end TauCeti
