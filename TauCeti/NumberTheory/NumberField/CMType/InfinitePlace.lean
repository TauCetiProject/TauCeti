/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMType.Basic
public import TauCeti.NumberTheory.NumberField.InfinitePlace.ComplexExtension

/-!
# Representatives of infinite places in a CM type

A CM type picks exactly one embedding representing each infinite place. For a CM type
induced from a base with one infinite place, this representative is the unique extension
of the selected base embedding. This comparison allows the relative norm formula indexed
by infinite places to use representatives in the CM type.
-/

public noncomputable section

open NumberField

namespace TauCeti.CMType

variable {K L : Type*} [Field K] [Field L]

/-- Passing to the associated infinite place identifies a CM type with all infinite places. -/
def equivInfinitePlace (Φ : CMType L) : Φ ≃ InfinitePlace L :=
  Equiv.ofBijective (fun φ ↦ InfinitePlace.mk φ.val) (by
    constructor
    · intro φ ψ h
      rcases InfinitePlace.mk_eq_iff.mp h with he | he
      · exact Subtype.ext he
      · have hconj : ComplexEmbedding.conjugate φ.val ∈ Φ := he.symm ▸ ψ.property
        exact False.elim ((Φ.star_mem_iff φ.val).mp hconj φ.property)
    · intro w
      by_cases h : w.embedding ∈ Φ
      · exact ⟨⟨w.embedding, h⟩, w.mk_embedding⟩
      · exact ⟨⟨ComplexEmbedding.conjugate w.embedding, (Φ.star_mem_iff _).mpr h⟩,
          (InfinitePlace.mk_conjugate_eq _).trans w.mk_embedding⟩)

/-- The forward map forgets the choice of representative. -/
@[simp]
theorem equivInfinitePlace_apply (Φ : CMType L) (φ : Φ) :
    Φ.equivInfinitePlace φ = InfinitePlace.mk φ.val := (rfl)

/-- The embedding selected by the CM type induces the original place. -/
@[simp]
theorem mk_equivInfinitePlace_symm_apply (Φ : CMType L) (w : InfinitePlace L) :
    InfinitePlace.mk (Φ.equivInfinitePlace.symm w).val = w := by
  rw [← equivInfinitePlace_apply, Equiv.apply_symm_apply]

/-- To identify the representative selected by a CM type, it suffices to exhibit a member
of the type inducing the given place. -/
theorem coe_equivInfinitePlace_symm_apply_eq_iff (Φ : CMType L) (w : InfinitePlace L)
    (φ : L →+* ℂ) :
    (Φ.equivInfinitePlace.symm w).val = φ ↔ φ ∈ Φ ∧ InfinitePlace.mk φ = w := by
  constructor
  · rintro rfl
    exact ⟨Subtype.property _, Φ.mk_equivInfinitePlace_symm_apply w⟩
  · rintro ⟨hφ, hw⟩
    have h : Φ.equivInfinitePlace.symm w = ⟨φ, hφ⟩ :=
      Φ.equivInfinitePlace.symm_apply_eq.mpr (by rw [equivInfinitePlace_apply, hw])
    exact congrArg Subtype.val h

/-- For an induced CM type, the representative at `w` is the unique embedding at `w`
extending the chosen member of the base CM type, when the base has only one place. -/
theorem coe_equivInfinitePlace_symm_apply_induced [Algebra K L] [Subsingleton (InfinitePlace K)]
    (Φ : CMType K) {σ : K →+* ℂ} (hσ : σ ∈ Φ) (w : InfinitePlace L) :
    let hn : ¬ ComplexEmbedding.IsReal σ := fun h ↦
      Φ.ringHom_star_ne_self σ (ComplexEmbedding.isReal_iff.mp h)
    ((Φ.induced (algebraMap K L)).equivInfinitePlace.symm w).val =
      ((ComplexEmbedding.Extension.equivInfinitePlace hn).symm w).val := by
  intro hn
  let τ := (ComplexEmbedding.Extension.equivInfinitePlace hn).symm w
  apply (coe_equivInfinitePlace_symm_apply_eq_iff _ _ _).mpr
  refine ⟨mem_induced.mpr ?_, ComplexEmbedding.Extension.mk_equivInfinitePlace_symm_apply hn w⟩
  rw [τ.comp_eq]
  exact hσ

end TauCeti.CMType
