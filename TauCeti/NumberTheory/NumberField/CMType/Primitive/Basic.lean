/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMType.Basic
public import Mathlib.FieldTheory.IntermediateField.Algebraic

/-!
# Primitive CM types

A CM type `Φ` on a field `E` is induced from a subfield `F` when it is the type
`TauCeti.CMType.induced` of a CM type `Φ₀` on `F`; the pair `(E, Φ)` is **primitive** when `Φ` is
induced from no proper subfield. By the fibre criterion
`TauCeti.CMType.exists_induced_algebraMap_eq_iff`, `Φ` is induced from `F` exactly when membership
in `Φ` depends only on the restriction to `F`. Choosing a subfield of least degree from which
`Φ` is induced gives a primitive pair inducing `Φ`
(`TauCeti.CMType.exists_isPrimitive_induced_eq`).

A subfield from which a CM type is induced carries a CM type, so it is totally complex; inside a
CM field it is therefore a CM subfield, and the definition here agrees with "induced from no
proper CM subfield".

## Main definitions

* `TauCeti.CMType.IsPrimitive Φ`: `Φ` is induced from no proper subfield.

## Main results

* `TauCeti.CMType.exists_isPrimitive_induced_eq`: every CM type on a number field is induced from
  a primitive CM type on a subfield.

## References

* J. S. Milne, *Complex Multiplication*, §1, p.11, and Proposition 1.9, p.12.
-/

public section

namespace TauCeti

namespace CMType

section Primitive

variable {E : Type*} [Field E] [CharZero E]

/-- A CM type `Φ` on a field `E` of characteristic zero is **primitive** when it is induced from
no proper subfield: whenever `Φ` is induced from a CM type on a subfield `F`, then `F = E`. -/
def IsPrimitive (Φ : CMType E) : Prop :=
  ∀ F : IntermediateField ℚ E, (∃ Φ₀ : CMType F, Φ₀.induced (algebraMap F E) = Φ) → F = ⊤

theorem isPrimitive_iff (Φ : CMType E) :
    Φ.IsPrimitive ↔
      ∀ F : IntermediateField ℚ E, (∃ Φ₀ : CMType F, Φ₀.induced (algebraMap F E) = Φ) → F = ⊤ :=
  Iff.rfl

/-- Every CM type is induced from itself, through the top subfield. -/
theorem exists_induced_top_eq (Φ : CMType E) :
    ∃ Φ₀ : CMType (⊤ : IntermediateField ℚ E), Φ₀.induced (algebraMap _ E) = Φ := by
  refine (exists_induced_algebraMap_eq_iff Φ).2 fun φ ψ h ↦ ?_
  have : φ = ψ := RingHom.ext fun y ↦ h ⟨y, IntermediateField.mem_top⟩
  rw [this]

variable [NumberField E]

/-- **Every CM type is induced from a primitive one.** A CM type `Φ` on a number field `E` is
induced from a primitive CM type `Φ₀` on a subfield `F`. -/
theorem exists_isPrimitive_induced_eq (Φ : CMType E) :
    ∃ (F : IntermediateField ℚ E) (Φ₀ : CMType F),
      Φ₀.induced (algebraMap F E) = Φ ∧ Φ₀.IsPrimitive := by
  classical
  have hP : ∃ n, ∃ F : IntermediateField ℚ E, Module.finrank ℚ F = n ∧
      ∃ Φ₀ : CMType F, Φ₀.induced (algebraMap F E) = Φ :=
    ⟨_, ⊤, rfl, exists_induced_top_eq Φ⟩
  obtain ⟨F, hFn, Φ₀, hΦ₀⟩ := Nat.find_spec hP
  refine ⟨F, Φ₀, hΦ₀, fun F₁ ⟨Φ₁, hΦ₁⟩ ↦ ?_⟩
  -- `Φ` is induced from the image `F₁'` of `F₁` in `E`.
  let F₁' : IntermediateField ℚ E := IntermediateField.lift F₁
  have hind : ∃ Φ₂ : CMType F₁', Φ₂.induced (algebraMap F₁' E) = Φ := by
    refine (exists_induced_algebraMap_eq_iff Φ).2 fun φ ψ h ↦ ?_
    rw [← hΦ₀, mem_induced, mem_induced]
    refine ((exists_induced_algebraMap_eq_iff Φ₀).1 ⟨Φ₁, hΦ₁⟩ _ _ fun x ↦ ?_)
    exact h ⟨((x : F) : E), (IntermediateField.mem_lift (x : F)).2 x.property⟩
  have hle : F₁' ≤ F := IntermediateField.lift_le F₁
  have hmin := Nat.find_min' hP ⟨F₁', rfl, hind⟩
  have heq : F₁' = F := IntermediateField.eq_of_le_of_finrank_le hle (hFn.trans_le hmin)
  exact F.lift_injective (heq.trans F.lift_top.symm)

end Primitive

end CMType

end TauCeti
