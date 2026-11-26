/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic
import TauCeti.NumberTheory.NumberField.ComplexEmbedding.Extension

/-!
# Infinite places over a complex place

Fix a nonreal embedding `σ : K →+* ℂ`. Each infinite place of an extension `L/K` above the
place of `σ` has exactly one representative extending `σ`: of the two conjugate embeddings
representing the place, the other one extends `conjugate σ` instead. In a finite extension the
relative norm evaluated at `σ` is the product of these representatives, with one factor per
infinite place over the place of `σ`.
For an imaginary quadratic base this product runs over all infinite places of `L`.

For the cyclotomic case over an imaginary quadratic field, see `New.Parameters.prod_phi_eq` in
lsernau/grh-lean, `New/Reduction/Data/FieldsAndPlaces.lean` at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public noncomputable section

namespace NumberField.ComplexEmbedding.Extension

open NumberField.ComplexEmbedding
open NumberField.InfinitePlace hiding LiesOver

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {σ : K →+* ℂ}

/-- When `σ` is nonreal, passing to the infinite place identifies the extensions of `σ` with
all infinite places over the place of `σ`. -/
def equivPlacesOver (hσ : ¬ IsReal σ) :
    ComplexEmbedding.Extension L σ ≃ placesOver L (InfinitePlace.mk σ) :=
  Equiv.ofBijective (fun τ ↦ ⟨InfinitePlace.mk τ.val, by
    rw [placesOver, Set.mem_ofPred_eq, liesOver_iff_comap_eq, comap_mk, τ.comp_eq]⟩) (by
    constructor
    · intro τ υ h
      rcases mk_eq_iff.mp (congrArg Subtype.val h) with he | he
      · exact Subtype.ext he
      · exact (τ.conjugate_comp_ne hσ (he ▸ υ.comp_eq)).elim
    · intro w
      have : w.val.LiesOver (InfinitePlace.mk σ) := w.property
      have hw := InfinitePlace.LiesOver.mk_embedding_comp w.val (InfinitePlace.mk σ)
      rcases mk_eq_iff.mp hw with he | he
      · exact ⟨⟨w.val.embedding, liesOver_iff.mpr he⟩, Subtype.ext (mk_embedding _)⟩
      · exact ⟨⟨conjugate w.val.embedding, liesOver_iff.mpr (by
          simpa only [conjugate_comp] using he)⟩,
          Subtype.ext ((mk_conjugate_eq _).trans (mk_embedding _))⟩)

/-- The forward map sends an embedding to its associated infinite place. -/
@[simp]
theorem coe_equivPlacesOver_apply (hσ : ¬ IsReal σ) (τ : ComplexEmbedding.Extension L σ) :
    (equivPlacesOver hσ τ).val = InfinitePlace.mk τ.val := (rfl)

/-- The representative chosen above the base embedding induces the original place. -/
@[simp]
theorem mk_equivPlacesOver_symm_apply (hσ : ¬ IsReal σ)
    (w : placesOver L (InfinitePlace.mk σ)) :
    InfinitePlace.mk ((equivPlacesOver hσ).symm w).val = w.val := by
  rw [← coe_equivPlacesOver_apply hσ, Equiv.apply_symm_apply]

/-- If the base has a unique infinite place and `σ` is nonreal, every infinite place of the
extension has a unique representative extending `σ`. -/
def equivInfinitePlace [Subsingleton (InfinitePlace K)] (hσ : ¬ IsReal σ) :
    ComplexEmbedding.Extension L σ ≃ InfinitePlace L :=
  (equivPlacesOver hσ).trans <|
    Equiv.subtypeUnivEquiv fun _ ↦ liesOver_iff_comap_eq.mpr (Subsingleton.elim _ _)

/-- The forward map sends an embedding to its associated infinite place. -/
@[simp]
theorem equivInfinitePlace_apply [Subsingleton (InfinitePlace K)] (hσ : ¬ IsReal σ)
    (τ : ComplexEmbedding.Extension L σ) : equivInfinitePlace hσ τ = InfinitePlace.mk τ.val := (rfl)

/-- The chosen representative extending `σ` induces the original infinite place. -/
@[simp]
theorem mk_equivInfinitePlace_symm_apply [Subsingleton (InfinitePlace K)] (hσ : ¬ IsReal σ)
    (w : InfinitePlace L) : InfinitePlace.mk ((equivInfinitePlace hσ).symm w).val = w := by
  rw [← equivInfinitePlace_apply hσ, Equiv.apply_symm_apply]

/-- In a finite extension, the relative norm at `σ` is the product of the values of the unique
representatives extending `σ`, one for each infinite place over the place of `σ`. -/
theorem prod_equivPlacesOver_symm_apply [FiniteDimensional K L] (hσ : ¬ IsReal σ) (x : L) :
    ∏ᶠ w : placesOver L (InfinitePlace.mk σ), ((equivPlacesOver hσ).symm w).val x =
      σ (Algebra.norm K x) := by
  have : CharZero K := σ.charZero
  have : IsAlgClosed (Codomain σ) := Complex.isAlgClosed
  let e := (equivAlgHom L σ).symm.trans (equivPlacesOver hσ)
  let := Fintype.ofEquiv (L →ₐ[K] Codomain σ) e
  rw [finprod_eq_prod_of_fintype]
  calc
    _ = ∏ f : L →ₐ[K] Codomain σ, Codomain.equiv σ (f x) :=
      (Fintype.prod_equiv e _ _ fun f ↦ by
        simp only [e, Equiv.trans_apply, Equiv.symm_apply_apply, equivAlgHom_symm_apply]).symm
    _ = σ (Algebra.norm K x) := by
      rw [← map_prod, ← Algebra.norm_eq_prod_embeddings K (Codomain σ), Codomain.equiv_algebraMap]

/-- In a finite extension whose base has only one infinite place, the relative norm at a nonreal
embedding `σ` is a product over all infinite places of the extension. -/
theorem prod_equivInfinitePlace_symm_apply [FiniteDimensional K L] [Subsingleton (InfinitePlace K)]
    (hσ : ¬ IsReal σ) (x : L) :
    ∏ᶠ w : InfinitePlace L, ((equivInfinitePlace hσ).symm w).val x = σ (Algebra.norm K x) := by
  let e : placesOver L (InfinitePlace.mk σ) ≃ InfinitePlace L :=
    (equivPlacesOver hσ).symm.trans (equivInfinitePlace hσ)
  rw [← finprod_comp_equiv e]
  simpa only [e, Equiv.trans_apply, Equiv.symm_apply_apply] using
    prod_equivPlacesOver_symm_apply hσ x

end NumberField.ComplexEmbedding.Extension
