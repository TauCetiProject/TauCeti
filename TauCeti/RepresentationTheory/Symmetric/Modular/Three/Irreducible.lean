/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.PGroupInvariants
public import TauCeti.RepresentationTheory.LinearCharacter.Basic
public import TauCeti.RepresentationTheory.Symmetric.SignCharacter
import TauCeti.GroupTheory.Perm.FinThree.Basic

/-!
# Simple representations of S₃ in characteristic three

Over every field of characteristic three, the trivial and sign lines are the only irreducible
representations of the symmetric group on three points. In particular this classification does
not require an algebraically closed coefficient field or an a priori dimension hypothesis.

The normal subgroup A₃ acts trivially on every irreducible representation. The remaining
involution acts as either the identity or minus the identity, so irreducibility forces a line.
This supplies the simple-module representatives used to compute the exact Grothendieck group
and the image of induction in characteristic three.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part III, §14.
-/

public section

namespace TauCeti

open Representation

universe u v

variable {k : Type u} [Field k] [CharP k 3]
  {V : Type v} [AddCommGroup V] [Module k V]

private theorem action_eq_one_or_sign (ρ : Representation k (Equiv.Perm (Fin 3)) V)
    (hρ : ρ.IsIrreducible) :
    (∀ g, ρ g = 1) ∨
      ∀ g, ρ g = (signLinearCharacter k (Fin 3) g : k) • (1 : Module.End k V) := by
  let := hρ
  -- The normal three-subgroup acts trivially, so the action depends only on parity.
  have hA : IsPGroup 3 (alternatingGroup (Fin 3)) :=
    IsPGroup.iff_card.mpr ⟨1, card_alternatingGroup_fin_three⟩
  have htriv := hρ.comp_eq_trivial_of_isPGroup 3 (alternatingGroup (Fin 3)) hA
  have heven (g : Equiv.Perm (Fin 3)) (hg : Equiv.Perm.sign g = 1) : ρ g = 1 := by
    exact DFunLike.congr_fun htriv ⟨g, Equiv.Perm.mem_alternatingGroup.mpr hg⟩
  let t : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  have ht : t * t = 1 := Equiv.swap_mul_self _ _
  have hsign : Equiv.Perm.sign t = -1 := Equiv.Perm.sign_swap (by decide)
  have hodd (g : Equiv.Perm (Fin 3)) (hg : Equiv.Perm.sign g = -1) : ρ g = ρ t := by
    have hgt : ρ (g * t) = 1 := heven (g * t) (by simp [hg, hsign])
    calc
      ρ g = ρ (g * t) * ρ t := by simp [mul_assoc, ← map_mul, ht]
      _ = ρ t := by rw [hgt, one_mul]
  have hcomm (g : Equiv.Perm (Fin 3)) : ρ t * ρ g = ρ g * ρ t := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign g) with hg | hg
    · simp [heven g hg]
    · rw [hodd g hg]
  let T : IntertwiningMap ρ ρ :=
    (ρ t).intertwiningMap_of_isIntertwiningMap ρ ρ fun g x ↦
      DFunLike.congr_fun (hcomm g) x
  have hT : T.toLinearMap = ρ t := rfl
  have hTapply (x : V) : T x = ρ t x := rfl
  have hsq (x : V) : T (T x) = x := by
    simp only [hTapply, ← Module.End.mul_apply, ← map_mul, ht, map_one,
      Module.End.one_apply]
  -- Schur makes `T - 1` either zero or injective; `(T - 1)(T + 1) = 0` then fixes the sign.
  rcases IsIrreducible.injective_or_eq_zero (T - 1) with hinj | hzero
  · have hneg (x : V) : T x = -x := by
      have hz : (T - 1) (T x + x) = (T - 1) 0 := by
        simp [map_add, hsq]
      have hx : T x + x = 0 := hinj hz
      exact eq_neg_of_add_eq_zero_left hx
    right
    intro g
    rcases Int.units_eq_one_or (Equiv.Perm.sign g) with hg | hg
    · simp [heven g hg, coe_signLinearCharacter_apply, hg]
    · ext x
      simpa [hodd g hg, coe_signLinearCharacter_apply, hg, ← hT] using hneg x
  · left
    have hpos : ρ t = 1 := by
      have h := sub_eq_zero.mp hzero
      exact congrArg IntertwiningMap.toLinearMap h
    intro g
    rcases Int.units_eq_one_or (Equiv.Perm.sign g) with hg | hg
    · exact heven g hg
    · rw [hodd g hg, hpos]

/-- Every irreducible S₃ representation in characteristic three is equivalent to the trivial
line or the sign line. This holds over arbitrary fields of that characteristic and without
assuming finite dimension. -/
theorem _root_.Representation.IsIrreducible.nonempty_equiv_trivial_or_sign_perm_fin_three
    {ρ : Representation k (Equiv.Perm (Fin 3)) V} (hρ : ρ.IsIrreducible) :
    Nonempty (ρ.Equiv (Representation.trivial k (Equiv.Perm (Fin 3)) k)) ∨
      Nonempty (ρ.Equiv (Representation.ofLinearCharacter (signLinearCharacter k (Fin 3)))) := by
  let := hρ
  have := hρ.nontrivial
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨χ, hχ, haction⟩ : ∃ χ : Equiv.Perm (Fin 3) →* kˣ,
      (χ = 1 ∨ χ = signLinearCharacter k (Fin 3)) ∧
        ∀ g, ρ g = (χ g : k) • (1 : Module.End k V) := by
    rcases action_eq_one_or_sign ρ hρ with h | h
    · exact ⟨1, Or.inl rfl, fun g ↦ by simp [h]⟩
    · exact ⟨signLinearCharacter k (Fin 3), Or.inr rfl, h⟩
  let f : IntertwiningMap (Representation.ofLinearCharacter χ) ρ :=
    (LinearMap.toSpanSingleton k V v).intertwiningMap_of_isIntertwiningMap _ _ fun g c ↦ by
      simp [Representation.ofLinearCharacter_apply, haction, mul_smul, mul_comm]
  have hf : f ≠ 0 := by
    intro h
    apply hv
    have heq := DFunLike.congr_fun h 1
    simpa [f] using heq
  have he := (IsIrreducible.bijective_or_eq_zero f).resolve_right hf
  rcases hχ with rfl | rfl
  · left
    simpa only [Representation.ofLinearCharacter_one] using
      Nonempty.intro (f.ofBijective he).symm
  · exact Or.inr ⟨(f.ofBijective he).symm⟩

end TauCeti
