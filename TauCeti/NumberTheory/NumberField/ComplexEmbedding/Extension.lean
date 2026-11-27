/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PrimitiveElement
public import TauCeti.NumberTheory.NumberField.ComplexEmbedding.Codomain

/-!
# The complex embeddings lying over a complex embedding

For a field extension `E/F` and a complex embedding `σ : F →+* ℂ`, the complex embeddings of `E`
lying over `σ` (Mathlib's `NumberField.ComplexEmbedding.Extension E σ`) are exactly the
`F`-algebra homomorphisms from `E` to `ℂ`, where `ℂ` is an `F`-algebra through `σ`
(`NumberField.ComplexEmbedding.Codomain σ`). Since `ℂ` is algebraically closed and `F` has
characteristic zero, a finite extension `E/F` therefore has exactly `[E : F]` complex embeddings
over each complex embedding of `F`. This is the fibre count behind sums over the embeddings of
`E` that extend a given embedding of `F`.

## Main definitions

* `NumberField.ComplexEmbedding.Extension.equivAlgHom`: the embeddings of `E` over `σ` are the
  `F`-algebra homomorphisms `E →ₐ[F] Codomain σ`.

## Main results

* `NumberField.ComplexEmbedding.natCard_extension`: there are `finrank F E` of them.
* `NumberField.ComplexEmbedding.card_filter_comp_algebraMap_eq`: the same count for an extension
  `E` that is a number field, phrased with the finite set of all complex embeddings of `E`.
* `NumberField.ComplexEmbedding.sum_comp_algebraMap`: summing a function of the restriction to `F`
  over the complex embeddings of `E` gives `[E : F]` times the sum over those of `F`.
* `NumberField.ComplexEmbedding.sum_filter_comp_algebraMap_eq_conjugate`: complex conjugation
  reindexes a sum over the embeddings above `σ` as a sum over those above `conj σ`.
* `NumberField.ComplexEmbedding.sum_filter_comp_algebraMap_eq_tower`: in a tower `L/E/F`, a sum
  over the embeddings of `L` above `σ` splits as a sum over the embeddings `τ` of `E` above `σ` of
  the sums over the embeddings of `L` above `τ`.
-/

public noncomputable section

open Module Finset

namespace NumberField.ComplexEmbedding

variable {F : Type*} (E : Type*) [Field F] [Field E] [Algebra F E] (σ : F →+* ℂ)

/-- The complex embeddings of `E` lying over `σ : F →+* ℂ` are the `F`-algebra homomorphisms from
`E` to `ℂ`, regarded as an `F`-algebra through `σ`. -/
def Extension.equivAlgHom : ComplexEmbedding.Extension E σ ≃ (E →ₐ[F] Codomain σ) where
  toFun τ :=
    { (Codomain.equiv σ).symm.toRingHom.comp τ.val with
      commutes' x := (Codomain.equiv σ).injective (by
        simpa using congr($(Extension.comp_eq τ) x)) }
  invFun φ := ⟨(Codomain.equiv σ).toRingHom.comp φ.toRingHom,
    liesOver_iff.mpr (RingHom.ext fun x ↦ by simp)⟩
  left_inv τ := Subtype.ext (RingHom.ext fun x ↦ by simp)
  right_inv φ := AlgHom.ext fun x ↦ by simp

variable {E σ}

@[simp]
theorem Extension.equivAlgHom_apply (τ : ComplexEmbedding.Extension E σ) (x : E) :
    Codomain.equiv σ (Extension.equivAlgHom E σ τ x) = τ.val x := by
  simp [Extension.equivAlgHom]

@[simp]
theorem Extension.equivAlgHom_symm_apply (φ : E →ₐ[F] Codomain σ) (x : E) :
    ((Extension.equivAlgHom E σ).symm φ).val x = Codomain.equiv σ (φ x) := by
  simp [Extension.equivAlgHom]

variable (E σ)

/-- A finite extension `E/F` has exactly `[E : F]` complex embeddings lying over each complex
embedding `σ` of `F`. -/
theorem natCard_extension [FiniteDimensional F E] :
    Nat.card (ComplexEmbedding.Extension E σ) = finrank F E := by
  have : CharZero F := σ.charZero
  have : IsAlgClosed (Codomain σ) := Complex.isAlgClosed
  rw [Nat.card_congr (Extension.equivAlgHom E σ),
    AlgHom.natCard_of_splits F E _ fun _ ↦ IsAlgClosed.splits _]

variable {E} [NumberField E]

open scoped Classical in
/-- An extension `E/F` of a number field has exactly `[E : F]` complex embeddings whose
restriction to `F` is a given complex embedding `σ`. -/
theorem card_filter_comp_algebraMap_eq :
    #{τ : E →+* ℂ | τ.comp (algebraMap F E) = σ} = finrank F E := by
  have : CharZero F := σ.charZero
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  rw [← natCard_extension E σ, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp [liesOver_iff]

/-- Summing a function of the restriction `τ|F` over the complex embeddings `τ` of an extension
`E/F` of a number field gives `[E : F]` times the sum over the complex embeddings of `F`. -/
theorem sum_comp_algebraMap [Fintype (F →+* ℂ)] {M : Type*} [AddCommMonoid M]
    (g : (F →+* ℂ) → M) :
    ∑ τ : E →+* ℂ, g (τ.comp (algebraMap F E)) = finrank F E • ∑ σ : F →+* ℂ, g σ := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun τ : E →+* ℂ ↦ τ.comp (algebraMap F E)),
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [Finset.sum_congr rfl fun τ hτ ↦ by rw [(Finset.mem_filter.1 hτ).2], Finset.sum_const,
    card_filter_comp_algebraMap_eq]

open scoped Classical in
/-- Complex conjugation maps the complex embeddings of `E` over `σ` bijectively onto those over
the conjugate of `σ`, so a sum over the latter is a sum over the former. -/
theorem sum_filter_comp_algebraMap_eq_conjugate {M : Type*} [AddCommMonoid M]
    (w : (E →+* ℂ) → M) :
    ∑ τ with τ.comp (algebraMap F E) = conjugate σ, w τ =
      ∑ τ with τ.comp (algebraMap F E) = σ, w (conjugate τ) := by
  refine Finset.sum_nbij' conjugate conjugate ?_ ?_ ?_ ?_ ?_
  all_goals intro τ hτ
  all_goals simp_all

open scoped Classical in
/-- In a tower `L/E/F`, the complex embeddings of `L` above `σ` are partitioned by their
restrictions to `E`, which are the embeddings of `E` above `σ`, so a sum over the former is an
iterated sum. -/
theorem sum_filter_comp_algebraMap_eq_tower {L : Type*} [Field L] [Algebra E L] [Algebra F L]
    [IsScalarTower F E L] [NumberField L] {M : Type*} [AddCommMonoid M] (w : (L →+* ℂ) → M) :
    ∑ τ with τ.comp (algebraMap F E) = σ, ∑ ρ with ρ.comp (algebraMap E L) = τ, w ρ =
      ∑ ρ with ρ.comp (algebraMap F L) = σ, w ρ := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun ρ : L →+* ℂ ↦ ρ.comp (algebraMap E L))
    (t := {τ : E →+* ℂ | τ.comp (algebraMap F E) = σ}) fun ρ hρ ↦ ?_]
  · refine Finset.sum_congr rfl fun τ hτ ↦ Finset.sum_congr ?_ fun _ _ ↦ rfl
    ext ρ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
    rw [IsScalarTower.algebraMap_eq F E L, ← RingHom.comp_assoc]
    constructor
    · exact fun h ↦ ⟨by rw [h, hτ], h⟩
    · exact fun h ↦ h.2
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, hρ]

end NumberField.ComplexEmbedding
