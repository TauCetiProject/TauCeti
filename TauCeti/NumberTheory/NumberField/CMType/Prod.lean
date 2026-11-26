/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Prod
public import TauCeti.NumberTheory.NumberField.CMType.Reflex.Basic

/-!
# CM types on a product

A CM algebra is a finite product of CM fields. This file treats one product `E₁ × E₂` of
commutative rings. Every ring homomorphism `E₁ × E₂ → ℂ` factors through exactly one of the two
projections (`RingHom.exists_eq_comp_fst_or_snd`), so the complex embeddings of `E₁ × E₂` are those
of `E₁` and those of `E₂`. Accordingly CM types on `E₁ × E₂` are pairs of CM types
(`TauCeti.CMType.prodEquiv`): the product type `prod Φ₁ Φ₂` (`TauCeti.CMType.prod`) consists of
the embeddings `φ₁ ∘ fst`, `φ₁ ∈ Φ₁`, and `φ₂ ∘ snd`, `φ₂ ∈ Φ₂` (`TauCeti.CMType.mem_prod_iff`).
It has `|Φ₁| + |Φ₂|` elements, type trace `typeTrace_{Φ₁}(a) + typeTrace_{Φ₂}(b)` at `(a, b)`, and
reflex field the compositum `E₁* E₂*` of the two reflex fields.

## Main definitions

* `TauCeti.CMType.prod Φ₁ Φ₂`: the CM type on `E₁ × E₂` of a pair of CM types.
* `TauCeti.CMType.prodEquiv`: CM types on `E₁ × E₂` are pairs of CM types.

## Main results

* `TauCeti.CMType.mem_prod_iff`: the embeddings in `prod Φ₁ Φ₂`.
* `TauCeti.CMType.natCard_prod`: `prod Φ₁ Φ₂` has `|Φ₁| + |Φ₂|` elements.
* `TauCeti.CMType.two_mul_natCard_eq_finrank_add_finrank`: on a product of two number fields, a
  CM type has half of the total degree many elements.
* `TauCeti.CMType.typeTrace_prod`: the type trace of `prod Φ₁ Φ₂` at `(a, b)` is
  `typeTrace_{Φ₁}(a) + typeTrace_{Φ₂}(b)`.
* `TauCeti.CMType.reflexField_prod`: the reflex field of `prod Φ₁ Φ₂` is the compositum of the
  reflex fields of `Φ₁` and `Φ₂`.

## References

* J. S. Milne, *Complex Multiplication*, §1, Definition 1.8, p.11, and Proposition 1.18, p.14.
-/

public section

namespace TauCeti.CMType

variable {E₁ E₂ : Type*} [CommRing E₁] [CommRing E₂]

/-! ### The product type -/

/-- **The product CM type on `E₁ × E₂`** of `Φ₁` and `Φ₂`: the embeddings `φ₁ ∘ fst` with
`φ₁ ∈ Φ₁` and `φ₂ ∘ snd` with `φ₂ ∈ Φ₂`. Every CM type on `E₁ × E₂` is of this form
(`TauCeti.CMType.prodEquiv`). -/
def prod (Φ₁ : CMType E₁) (Φ₂ : CMType E₂) : CMType (E₁ × E₂) where
  carrier := (fun ψ : E₁ →+* ℂ ↦ ψ.comp (RingHom.fst E₁ E₂)) '' Φ₁ ∪
    (fun ψ : E₂ →+* ℂ ↦ ψ.comp (RingHom.snd E₁ E₂)) '' Φ₂
  star_mem_iff' φ := by
    rcases φ.exists_eq_comp_fst_or_snd with ⟨ψ, rfl⟩ | ⟨ψ, rfl⟩ <;>
      simp only [RingHom.star_comp_right, RingHom.comp_fst_mem_union_iff,
        RingHom.comp_snd_mem_union_iff, SetLike.mem_coe, star_mem_iff]

theorem coe_prod (Φ₁ : CMType E₁) (Φ₂ : CMType E₂) :
    (prod Φ₁ Φ₂ : Set (E₁ × E₂ →+* ℂ)) =
      (fun ψ : E₁ →+* ℂ ↦ ψ.comp (RingHom.fst E₁ E₂)) '' Φ₁ ∪
        (fun ψ : E₂ →+* ℂ ↦ ψ.comp (RingHom.snd E₁ E₂)) '' Φ₂ :=
  (rfl)

/-- An embedding of `E₁ × E₂` lies in `prod Φ₁ Φ₂` exactly when it is `φ₁ ∘ fst` with `φ₁ ∈ Φ₁` or
`φ₂ ∘ snd` with `φ₂ ∈ Φ₂`. -/
theorem mem_prod_iff {Φ₁ : CMType E₁} {Φ₂ : CMType E₂} {φ : E₁ × E₂ →+* ℂ} :
    φ ∈ prod Φ₁ Φ₂ ↔ (∃ φ₁ ∈ Φ₁, φ₁.comp (RingHom.fst E₁ E₂) = φ) ∨
      ∃ φ₂ ∈ Φ₂, φ₂.comp (RingHom.snd E₁ E₂) = φ := by
  rw [← SetLike.mem_coe, coe_prod]
  simp only [Set.mem_union, Set.mem_image, SetLike.mem_coe]

@[simp]
theorem comp_fst_mem_prod {Φ₁ : CMType E₁} {Φ₂ : CMType E₂} {ψ : E₁ →+* ℂ} :
    ψ.comp (RingHom.fst E₁ E₂) ∈ prod Φ₁ Φ₂ ↔ ψ ∈ Φ₁ := by
  rw [← SetLike.mem_coe, coe_prod, RingHom.comp_fst_mem_union_iff, SetLike.mem_coe]

@[simp]
theorem comp_snd_mem_prod {Φ₁ : CMType E₁} {Φ₂ : CMType E₂} {ψ : E₂ →+* ℂ} :
    ψ.comp (RingHom.snd E₁ E₂) ∈ prod Φ₁ Φ₂ ↔ ψ ∈ Φ₂ := by
  rw [← SetLike.mem_coe, coe_prod, RingHom.comp_snd_mem_union_iff, SetLike.mem_coe]

/-- The conjugate of a product type is the product of the conjugates. -/
@[simp]
theorem star_prod (Φ₁ : CMType E₁) (Φ₂ : CMType E₂) :
    star (prod Φ₁ Φ₂) = prod (star Φ₁) (star Φ₂) := by
  ext φ
  rcases φ.exists_eq_comp_fst_or_snd with ⟨ψ, rfl⟩ | ⟨ψ, rfl⟩ <;> simp

/-- Restricting `prod Φ₁ Φ₂` to the first factor gives `Φ₁`. -/
@[simp]
theorem induced_fst_prod (Φ₁ : CMType E₁) (Φ₂ : CMType E₂) :
    (prod Φ₁ Φ₂).induced (RingHom.fst E₁ E₂) = Φ₁ := by
  ext; simp

/-- Restricting `prod Φ₁ Φ₂` to the second factor gives `Φ₂`. -/
@[simp]
theorem induced_snd_prod (Φ₁ : CMType E₁) (Φ₂ : CMType E₂) :
    (prod Φ₁ Φ₂).induced (RingHom.snd E₁ E₂) = Φ₂ := by
  ext; simp

/-- Every CM type on `E₁ × E₂` is the product of its restrictions to the two factors. -/
@[simp]
theorem prod_induced_fst_induced_snd (Φ : CMType (E₁ × E₂)) :
    prod (Φ.induced (RingHom.fst E₁ E₂)) (Φ.induced (RingHom.snd E₁ E₂)) = Φ := by
  ext φ
  rcases φ.exists_eq_comp_fst_or_snd with ⟨ψ, rfl⟩ | ⟨ψ, rfl⟩ <;> simp

/-- **CM types on `E₁ × E₂` are pairs of CM types**, by restriction to the two factors. -/
def prodEquiv : CMType (E₁ × E₂) ≃ CMType E₁ × CMType E₂ where
  toFun Φ := (Φ.induced (RingHom.fst E₁ E₂), Φ.induced (RingHom.snd E₁ E₂))
  invFun Φ := prod Φ.1 Φ.2
  left_inv := prod_induced_fst_induced_snd
  right_inv Φ := by simp

@[simp]
theorem prodEquiv_apply (Φ : CMType (E₁ × E₂)) :
    prodEquiv Φ = (Φ.induced (RingHom.fst E₁ E₂), Φ.induced (RingHom.snd E₁ E₂)) :=
  (rfl)

@[simp]
theorem prodEquiv_symm_apply (Φ : CMType E₁ × CMType E₂) :
    (prodEquiv (E₁ := E₁) (E₂ := E₂)).symm Φ = prod Φ.1 Φ.2 :=
  (rfl)

/-! ### The action of `Aut(ℂ)` -/

/-- If every ring endomorphism of `ℂ` commutes with complex conjugation on the embeddings of `E₁`
and of `E₂`, it does so on the embeddings of `E₁ × E₂`, since each of these factors through a
projection. In particular this holds for a product of two CM fields. -/
instance instStarCompCommuteProd [StarCompCommute E₁] [StarCompCommute E₂] :
    StarCompCommute (E₁ × E₂) where
  star_comp σ φ := by
    rcases φ.exists_eq_comp_fst_or_snd with ⟨ψ, rfl⟩ | ⟨ψ, rfl⟩ <;>
      rw [← RingHom.comp_assoc, RingHom.star_comp_right (σ.comp ψ), StarCompCommute.star_comp,
        RingHom.star_comp_right, RingHom.comp_assoc]

/-- Translating a product type translates both factors: `σ(Φ₁ × Φ₂) = σΦ₁ × σΦ₂`. -/
@[simp]
theorem smul_prod [StarCompCommute E₁] [StarCompCommute E₂] (σ : RingAut ℂ) (Φ₁ : CMType E₁)
    (Φ₂ : CMType E₂) : σ • prod Φ₁ Φ₂ = prod (σ • Φ₁) (σ • Φ₂) := by
  ext φ
  rcases φ.exists_eq_comp_fst_or_snd with ⟨ψ, rfl⟩ | ⟨ψ, rfl⟩ <;>
    simp only [mem_smul, ← RingHom.comp_assoc, comp_fst_mem_prod, comp_snd_mem_prod]

/-- **The product type has `|Φ₁| + |Φ₂|` elements.** -/
theorem natCard_prod [Finite (E₁ →+* ℂ)] [Finite (E₂ →+* ℂ)] (Φ₁ : CMType E₁)
    (Φ₂ : CMType E₂) : Nat.card (prod Φ₁ Φ₂) = Nat.card Φ₁ + Nat.card Φ₂ := by
  simp only [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, coe_prod]
  rw [Set.ncard_union_eq (RingHom.disjoint_image_comp_fst_image_comp_snd _ _) (Set.toFinite _)
    (Set.toFinite _)]
  simp [Set.ncard_image_of_injective _ RingHom.comp_fst_injective,
    Set.ncard_image_of_injective _ RingHom.comp_snd_injective]

/-- **A CM type on a product of two number fields has half of the total degree many elements.** -/
theorem two_mul_natCard_eq_finrank_add_finrank {K₁ K₂ : Type*} [Field K₁] [NumberField K₁]
    [Field K₂] [NumberField K₂] (Φ : CMType (K₁ × K₂)) :
    2 * Nat.card Φ = Module.finrank ℚ K₁ + Module.finrank ℚ K₂ := by
  rw [← prod_induced_fst_induced_snd Φ, natCard_prod, mul_add, two_mul_card_eq_finrank,
    two_mul_card_eq_finrank]

/-! ### Type trace and reflex field -/

variable [Finite (E₁ →+* ℂ)] [Finite (E₂ →+* ℂ)]

/-- The type trace of `prod Φ₁ Φ₂` at `(a, b)` is `typeTrace_{Φ₁}(a) + typeTrace_{Φ₂}(b)`. -/
@[simp]
theorem typeTrace_prod (Φ₁ : CMType E₁) (Φ₂ : CMType E₂) (a : E₁) (b : E₂) :
    (prod Φ₁ Φ₂).typeTrace (a, b) = Φ₁.typeTrace a + Φ₂.typeTrace b := by
  have hdisj :=
    RingHom.disjoint_image_comp_fst_image_comp_snd (E₁ := E₁) (E₂ := E₂) (K := ℂ) Φ₁ Φ₂
  rw [typeTrace_apply, coe_prod, finsum_mem_union hdisj (Set.toFinite _) (Set.toFinite _),
    finsum_mem_image RingHom.comp_fst_injective.injOn,
    finsum_mem_image RingHom.comp_snd_injective.injOn]
  simp [typeTrace_apply]

/-- **The reflex field of a product is the compositum of the reflex fields.** -/
@[simp]
theorem reflexField_prod (Φ₁ : CMType E₁) (Φ₂ : CMType E₂) :
    (prod Φ₁ Φ₂).reflexField = Φ₁.reflexField ⊔ Φ₂.reflexField := by
  refine le_antisymm (reflexField_le_iff.mpr fun ⟨a, b⟩ ↦ ?_) (sup_le ?_ ?_)
  · rw [typeTrace_prod]
    exact add_mem (le_sup_left (a := Φ₁.reflexField) (typeTrace_mem_reflexField Φ₁ a))
      (le_sup_right (a := Φ₁.reflexField) (typeTrace_mem_reflexField Φ₂ b))
  · refine reflexField_le_iff.mpr fun a ↦ ?_
    simpa using typeTrace_mem_reflexField (prod Φ₁ Φ₂) (a, 0)
  · refine reflexField_le_iff.mpr fun b ↦ ?_
    simpa using typeTrace_mem_reflexField (prod Φ₁ Φ₂) (0, b)

end TauCeti.CMType
