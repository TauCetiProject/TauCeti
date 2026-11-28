/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.CM
import TauCeti.LinearAlgebra.LinearIndependent.MonoidHom

/-!
# Finiteness of CM norm-one characters with prescribed restriction

Fixing the restriction of an automorphic character to an integral congruence subgroup
leaves only finitely many choices. The ratio of two extensions factors through the
norm-one ray class group. In particular, a fixed archimedean weight and tame part, which
prescribe the values on the integral ideles, determine the character up to finitely many
choices.

This is the fixed-restriction argument of `New.AutChar.finite_setOf_hasWeight` in
`Lib/ClassField/HeckeCharacter/Basic.lean` of lsernau/grh-lean (revision `72fead1`).
-/

public section

open NumberField

namespace TauCeti.GlobalNumberFields

/-- There are only finitely many automorphic characters of the CM norm-one torus with
prescribed values on the norm-one congruence subgroup of a modulus. The prescription
need not itself be given as a character: if it admits no extension, the set is empty. -/
theorem finite_cmNormOneCharacters_of_restriction {E : Type} [Field E] [NumberField E]
    [IsCMField E] (𝔪 : Modulus E)
    (ρ : (ideleCongruenceSubgroup 𝔪).subgroupOf (cmNormOneIdeles E) → Circle) :
    {χ : cmNormOneIdeles E →ₜ* Circle |
      (∀ x : (IdeleGroup.principalSubgroup (𝓞 E) E).subgroupOf (cmNormOneIdeles E), χ x = 1) ∧
      ∀ x : (ideleCongruenceSubgroup 𝔪).subgroupOf (cmNormOneIdeles E), χ x = ρ x}.Finite := by
  classical
  let S := {χ : cmNormOneIdeles E →ₜ* Circle |
    (∀ x : (IdeleGroup.principalSubgroup (𝓞 E) E).subgroupOf (cmNormOneIdeles E), χ x = 1) ∧
    ∀ x : (ideleCongruenceSubgroup 𝔪).subgroupOf (cmNormOneIdeles E), χ x = ρ x}
  suffices S.Finite from this
  rcases S.eq_empty_or_nonempty with h | ⟨χ₀, h₀⟩
  · rw [h]
    exact Set.finite_empty
  let ratio (χ : S) := χ.val.toMonoidHom / χ₀.toMonoidHom
  have hratio (χ : S) : cmNormOneRaySubgroup 𝔪 ≤ (ratio χ).ker := by
    rw [cmNormOneRaySubgroup_le_iff]
    refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
    · exact div_eq_one.mpr ((χ.property.2 ⟨x, hx⟩).trans (h₀.2 ⟨x, hx⟩).symm)
    · exact div_eq_one.mpr ((χ.property.1 ⟨x, hx⟩).trans (h₀.1 ⟨x, hx⟩).symm)
  let descend (χ : S) : (cmNormOneIdeles E ⧸ cmNormOneRaySubgroup 𝔪) →* ℂ :=
    Circle.coeHom.comp (QuotientGroup.lift _ (ratio χ) (hratio χ))
  refine Set.finite_coe_iff.mp (Finite.of_injective descend ?_)
  intro χ ψ h
  apply Subtype.ext
  apply ContinuousMonoidHom.ext
  intro x
  have he := DFunLike.congr_fun h (x : cmNormOneIdeles E ⧸ cmNormOneRaySubgroup 𝔪)
  simp only [descend, MonoidHom.comp_apply, QuotientGroup.lift_mk] at he
  have hr : ratio χ x = ratio ψ x := Subtype.val_injective he
  exact div_left_injective (b := χ₀ x) hr

end TauCeti.GlobalNumberFields
