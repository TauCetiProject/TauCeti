/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMType.Primitive.Basic
public import Mathlib.NumberTheory.NumberField.Basic
import TauCeti.FieldTheory.Galois.FixedField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings

/-!
# Uniqueness of the primitive pair

A CM type `Φ` on a number field `E` that is induced from two subfields `F₁` and `F₂` is induced
from their intersection `F₁ ⊓ F₂`. Hence the primitive pair inducing `Φ` is unique: if `Φ` is
induced from primitive types on `F` and on `F'`, it is induced from `F ⊓ F'`, and then the type
on `F` is induced from `F ⊓ F'`, which forces `F ⊓ F' = F` by primitivity, and symmetrically.

The intersection is handled in a Galois closure `N` of `E / ℚ`. Extend the embeddings of `E` to
`N`, and fix one extension `φ'` of an embedding `φ`; the others are `φ' ∘ τ` for `τ ∈ Gal(N/ℚ)`.
That `Φ` is induced from `F` says that whether `(φ' ∘ τ)|_E` lies in `Φ` does not change when `τ`
is multiplied on the right by the fixing subgroup `H_F` of `F`. The set of right multipliers
preserving membership is a subgroup, so it contains `H_{F₁} ⊔ H_{F₂}`, which is the fixing
subgroup of `F₁ ⊓ F₂` by the Galois correspondence (`IntermediateField.fixingSubgroup_inf`). Two
embeddings of `E` agreeing on `F₁ ⊓ F₂` have extensions differing by an element of
`H_{F₁ ⊓ F₂}`, so they are both in `Φ` or both out.

## Main results

* `TauCeti.CMType.comp_mem_iff_of_mem_fixingSubgroup_inf`: the Galois step, in a finite Galois
  extension of `ℚ` containing `E`.
* `TauCeti.CMType.exists_induced_inf_eq`: a CM type induced from `F₁` and from `F₂` is induced
  from `F₁ ⊓ F₂`.
* `TauCeti.CMType.le_of_isPrimitive_of_exists_induced_eq`: a subfield carrying a primitive type
  that induces `Φ` lies in every subfield from which `Φ` is induced.
* `TauCeti.CMType.existsUnique_isPrimitive_induced_eq`: the subfield of the primitive pair
  inducing a CM type is unique; the primitive type on it is then unique by
  `TauCeti.CMType.induced_algebraMap_injective`.

## References

* J. S. Milne, *Complex Multiplication*, §1, p.11, and Proposition 1.9, p.12.
-/

public section

open NumberField

namespace TauCeti.CMType

variable {E : Type*} [Field E] [NumberField E]

/-- **The Galois step.** Let `N / ℚ` be a finite Galois extension containing `E`, and `φ'` a
complex embedding of `N`. If a CM type `Φ` on `E` is induced from `F₁` and from `F₂`, then an
automorphism `σ` of `N` fixing the image of `F₁ ⊓ F₂` does not change whether the restriction of
`φ' ∘ σ` to `E` lies in `Φ`. -/
theorem comp_mem_iff_of_mem_fixingSubgroup_inf {N : Type*} [Field N] [Algebra ℚ N] [Algebra E N]
    [IsScalarTower ℚ E N] [FiniteDimensional ℚ N] [IsGalois ℚ N] (Φ : CMType E)
    {F₁ F₂ : IntermediateField ℚ E} (h₁ : ∃ Φ₁ : CMType F₁, Φ₁.induced (algebraMap F₁ E) = Φ)
    (h₂ : ∃ Φ₂ : CMType F₂, Φ₂.induced (algebraMap F₂ E) = Φ) (φ' : N →+* ℂ) {σ : Gal(N/ℚ)}
    (hσ : σ ∈ ((F₁ ⊓ F₂).map (IsScalarTower.toAlgHom ℚ E N)).fixingSubgroup) :
    (φ'.comp (σ : N →+* N)).comp (algebraMap E N) ∈ Φ ↔ φ'.comp (algebraMap E N) ∈ Φ := by
  rw [exists_induced_algebraMap_eq_iff] at h₁ h₂
  let f : E →ₐ[ℚ] N := IsScalarTower.toAlgHom ℚ E N
  -- Right multipliers preserving membership of `(φ' ∘ τ)|_E` in `Φ` form a subgroup.
  let S (τ : Gal(N/ℚ)) : Prop := (φ'.comp (τ : N →+* N)).comp (algebraMap E N) ∈ Φ
  let T : Subgroup Gal(N/ℚ) :=
    { carrier := {h | ∀ τ, S (τ * h) ↔ S τ}
      one_mem' := fun τ ↦ by rw [mul_one]
      mul_mem' := fun ha hb τ ↦ by rw [← mul_assoc, hb, ha]
      inv_mem' := fun {h} hh τ ↦ by rw [← hh, inv_mul_cancel_right] }
  -- If `Φ` is induced from `F`, the fixing subgroup of `F` preserves membership.
  have hT (F : IntermediateField ℚ E)
      (hF : ∀ φ ψ : E →+* ℂ, (∀ x : F, φ (algebraMap F E x) = ψ (algebraMap F E x)) →
        (φ ∈ Φ ↔ ψ ∈ Φ)) : (F.map f).fixingSubgroup ≤ T := fun h hh τ ↦ by
    refine hF _ _ fun x ↦ ?_
    have : h (f x) = f x :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).mp hh _ ⟨x, x.property, rfl⟩
    simp only [RingHom.comp_apply]
    exact congrArg (fun y ↦ φ' (τ y)) this
  -- By the Galois correspondence, `H_{F₁ ⊓ F₂} = H_{F₁} ⊔ H_{F₂}`.
  rw [IntermediateField.map_inf, IntermediateField.fixingSubgroup_inf] at hσ
  have key := (sup_le (hT F₁ h₁) (hT F₂ h₂)) hσ 1
  rw [one_mul] at key
  exact key

/-- **A CM type induced from two subfields is induced from their intersection.** -/
theorem exists_induced_inf_eq (Φ : CMType E) {F₁ F₂ : IntermediateField ℚ E}
    (h₁ : ∃ Φ₁ : CMType F₁, Φ₁.induced (algebraMap F₁ E) = Φ)
    (h₂ : ∃ Φ₂ : CMType F₂, Φ₂.induced (algebraMap F₂ E) = Φ) :
    ∃ Φ₀ : CMType ↥(F₁ ⊓ F₂), Φ₀.induced (algebraMap _ E) = Φ := by
  rw [exists_induced_algebraMap_eq_iff]
  -- A Galois closure `N` of `E / ℚ`, inside an algebraic closure of `E`.
  let Ω := AlgebraicClosure E
  have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  let N := IntermediateField.normalClosure ℚ E Ω
  have : IsGalois ℚ N := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  have : Algebra.IsAlgebraic E N := Algebra.IsAlgebraic.tower_top (K := ℚ) E
  let f : E →ₐ[ℚ] N := IsScalarTower.toAlgHom ℚ E N
  -- Extensions of two embeddings agreeing on `F₁ ⊓ F₂` differ by `σ` fixing `F₁ ⊓ F₂`.
  intro φ ψ hφψ
  let φ' := ComplexEmbedding.lift N φ
  let ψ' := ComplexEmbedding.lift N ψ
  have hφ' : φ'.comp (algebraMap E N) = φ := ComplexEmbedding.lift_comp_algebraMap N φ
  have hψ' : ψ'.comp (algebraMap E N) = ψ := ComplexEmbedding.lift_comp_algebraMap N ψ
  obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := ℚ) φ' ψ'
    (RingHom.ext fun _ ↦ by simp)
  have hσH : σ.symm ∈ ((F₁ ⊓ F₂).map f).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    rintro _ ⟨x, hx, rfl⟩
    refine φ'.injective ?_
    have h1 : φ' (σ.symm (f x)) = ψ' (f x) := RingHom.congr_fun hσ (f x)
    have h2 : ψ' (f x) = ψ x := RingHom.congr_fun hψ' x
    have h3 : φ' (f x) = φ x := RingHom.congr_fun hφ' x
    exact h1.trans (h2.trans ((hφψ ⟨x, hx⟩).symm.trans h3.symm))
  have key := comp_mem_iff_of_mem_fixingSubgroup_inf Φ h₁ h₂ φ' hσH
  rw [hσ, hψ', hφ'] at key
  exact key.symm

/-- If `Φ` is induced from a subfield `F'` of `E`, a type on a subfield `F` inducing `Φ` is
induced from `F ⊓ F'`, viewed as a subfield of `F`. -/
theorem exists_induced_restrict_inf_eq {Φ : CMType E} {F F' : IntermediateField ℚ E}
    {Φ₀ : CMType F} (hΦ₀ : Φ₀.induced (algebraMap F E) = Φ)
    (h' : ∃ Φ₁ : CMType F', Φ₁.induced (algebraMap F' E) = Φ) :
    ∃ Φ₂ : CMType ↥(IntermediateField.restrict (inf_le_left : F ⊓ F' ≤ F)),
      Φ₂.induced (algebraMap _ F) = Φ₀ := by
  have hΨ := (exists_induced_algebraMap_eq_iff Φ).1 (Φ.exists_induced_inf_eq ⟨Φ₀, hΦ₀⟩ h')
  rw [exists_induced_algebraMap_eq_iff]
  intro φ ψ h
  -- Extend `φ` and `ψ` to `E`; the extensions agree on `F ⊓ F'`.
  have hφ := ComplexEmbedding.lift_comp_algebraMap E φ
  have hψ := ComplexEmbedding.lift_comp_algebraMap E ψ
  have key := hΨ (ComplexEmbedding.lift E φ) (ComplexEmbedding.lift E ψ) fun x ↦ by
    have hx : (x : E) ∈ F := (IntermediateField.mem_inf.mp x.property).1
    have := h ⟨⟨x, hx⟩, (IntermediateField.mem_restrict _ _).mpr x.property⟩
    rw [← hφ, ← hψ] at this
    exact this
  rw [← hΦ₀, mem_induced, mem_induced, hφ, hψ] at key
  exact key

/-- A subfield carrying a primitive CM type that induces `Φ` lies in every subfield from which
`Φ` is induced. -/
theorem le_of_isPrimitive_of_exists_induced_eq {Φ : CMType E} {F F' : IntermediateField ℚ E}
    {Φ₀ : CMType F} (hΦ₀ : Φ₀.induced (algebraMap F E) = Φ) (hprim : Φ₀.IsPrimitive)
    (h' : ∃ Φ₁ : CMType F', Φ₁.induced (algebraMap F' E) = Φ) : F ≤ F' := by
  -- `F ⊓ F'` is all of `F`, by primitivity of `Φ₀`.
  have htop := (isPrimitive_iff _).mp hprim _ (exists_induced_restrict_inf_eq hΦ₀ h')
  intro x hx
  have : (⟨x, hx⟩ : F) ∈ IntermediateField.restrict (inf_le_left : F ⊓ F' ≤ F) :=
    htop ▸ IntermediateField.mem_top
  exact (IntermediateField.mem_inf.mp ((IntermediateField.mem_restrict _ _).mp this)).2

/-- **Uniqueness of the primitive pair.** A CM type on a number field is induced from a primitive
CM type on exactly one subfield. The primitive type on that subfield is unique as well, by
`TauCeti.CMType.induced_algebraMap_injective`. -/
theorem existsUnique_isPrimitive_induced_eq (Φ : CMType E) :
    ∃! F : IntermediateField ℚ E, ∃ Φ₀ : CMType F,
      Φ₀.induced (algebraMap F E) = Φ ∧ Φ₀.IsPrimitive := by
  obtain ⟨F, Φ₀, hΦ₀, hprim⟩ := Φ.exists_isPrimitive_induced_eq
  refine ⟨F, ⟨Φ₀, hΦ₀, hprim⟩, fun F' ⟨Φ₁, hΦ₁, hprim'⟩ ↦ ?_⟩
  exact le_antisymm (le_of_isPrimitive_of_exists_induced_eq hΦ₁ hprim' ⟨Φ₀, hΦ₀⟩)
    (le_of_isPrimitive_of_exists_induced_eq hΦ₀ hprim ⟨Φ₁, hΦ₁⟩)

end TauCeti.CMType
