/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Character
public import TauCeti.RepresentationTheory.Induction.Restriction
public import TauCeti.RepresentationTheory.CharacterTable.VirtualCharacter

/-!
# Induction, restriction, and virtual characters

This file records the compatibility of induction and of restriction along a subgroup with the
virtual-character lattice: both send virtual characters to virtual characters, because both send
characters to characters and both are additive.

Together they are the two maps `R(S) → R(G)` and `R(G) → R(S)` on virtual-character lattices whose
interplay -- the projection formula `Subgroup.indClassFun_comp_subtype_mul` -- makes induction a map
of `R(G)`-modules.

## Main definitions

* `TauCeti.ClassFunction.indVirtualCharacterAddHom`: induction bundled as an additive
  homomorphism between the virtual-character lattices of a subgroup and the ambient group.

## Main statements

* `Subgroup.indClassFun_mem_virtualCharacters`: induction preserves virtual characters, since
  it takes characters to characters and commutes with additive generation.
* `TauCeti.ClassFunction.indVirtualCharacterAddHom_apply_coe`: forgetting the target
  subtype in the bundled map recovers induction of class functions.
* `TauCeti.comp_subtype_mem_virtualCharacters`: restricting a virtual character of `G` to a
  subgroup gives a virtual character of the subgroup.

The induced virtual-character lattice is the input to Artin and Brauer induction, while the
projection formula makes its span an ideal over the ambient virtual-character ring.
-/

public section

namespace TauCeti

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G]

/-- **Restriction preserves virtual characters.**  It is the pullback along the inclusion of the
subgroup, `TauCeti.comp_mem_virtualCharacters`; the restriction of a plain function is written
`fun s : S => f s`, and `TauCeti.ClassFunction.comap` is the class-function form.

This is the additive half of the statement that restriction `R(G) → R(S)` is a ring homomorphism;
its multiplicativity is the pointwise `TauCeti.mul_mem_virtualCharacters` on each side. -/
theorem comp_subtype_mem_virtualCharacters (S : Subgroup G) {f : G → k}
    (hf : f ∈ virtualCharacters k G) : (fun s : S => f s) ∈ virtualCharacters k S :=
  comp_mem_virtualCharacters S.subtype hf

/-- **Induction preserves virtual characters.**  A character of the subgroup induces to a character
(`Subgroup.indClassFun_ofFDRep_character`), and induction is additive, so the
property propagates through the additive generation of the lattice. -/
theorem _root_.Subgroup.indClassFun_mem_virtualCharacters (S : Subgroup G)
    [S.FiniteIndex] {ψ : S → k}
    (hψ : ψ ∈ virtualCharacters k S) : Subgroup.indClassFun S ψ ∈ virtualCharacters k G := by
  have hle : virtualCharacters k S ≤ (virtualCharacters k G).comap S.indClassFunAddHom := by
    refine virtualCharacters_le fun V => ?_
    rw [AddSubgroup.mem_comap, Subgroup.indClassFunAddHom_apply]
    rw [Subgroup.indClassFun_ofFDRep_character]
    exact character_mem_virtualCharacters _
  have hmem := hle hψ
  rwa [AddSubgroup.mem_comap, Subgroup.indClassFunAddHom_apply] at hmem

namespace ClassFunction

variable (k G) in
/-- Induction from a subgroup, restricted and corestricted to the virtual-character lattices. -/
noncomputable def indVirtualCharacterAddHom (S : Subgroup G) [S.FiniteIndex] :
    virtualCharacters k S →+ virtualCharacters k G :=
  ((Subgroup.indClassFunAddHom S).comp (virtualCharacters k S).subtype).codRestrict
    (virtualCharacters k G) fun ψ ↦ by
      rw [AddMonoidHom.comp_apply, Subgroup.indClassFunAddHom_apply]
      exact Subgroup.indClassFun_mem_virtualCharacters S ψ.2

/-- Forgetting the target subtype after induction on virtual characters gives
`Subgroup.indClassFun`. -/
@[simp]
theorem indVirtualCharacterAddHom_apply_coe (S : Subgroup G) [S.FiniteIndex]
    (ψ : virtualCharacters k S) :
    (indVirtualCharacterAddHom k G S ψ : G → k) = Subgroup.indClassFun S ψ := by
  simpa only [indVirtualCharacterAddHom, AddMonoidHom.codRestrict_apply,
    AddMonoidHom.comp_apply, AddSubgroup.subtype_apply] using
      Subgroup.indClassFunAddHom_apply S (ψ : S → k)

end ClassFunction

end TauCeti
