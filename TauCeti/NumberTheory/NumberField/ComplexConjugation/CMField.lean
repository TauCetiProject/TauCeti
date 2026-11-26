/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.NumberTheory.NumberField.CMField
public import TauCeti.NumberTheory.NumberField.ComplexConjugation.Basic

/-!
# Complex conjugation on a CM field is place-independent

`TauCeti/NumberTheory/NumberField/ComplexConjugation/Basic.lean` attaches a conjugation
`complexConjugationAt K w hw` to a complex place `w` of `L` lying above a real place of `K`. The
place is genuinely part of the input: in a general Galois extension the elements attached to
different ramified places are conjugate (`complexConjugationAt_smul`), and conjugate elements
can differ.

An algebraic CM field is a case where that dependence disappears. If `K` is CM and algebraic over
`ℚ`, with maximal real subfield `K⁺`, then `K / K⁺` is a totally complex quadratic extension, so

* every infinite place of `K` is ramified over `K⁺` — the hypothesis `hw` is automatic
  (`NumberField.InfinitePlace.isRamified_maximalRealSubfield_iff`), and
* the conjugation attached to any place is Mathlib's `IsCMField.complexConj`
  (`complexConjugationAt_eq_complexConj`),

hence any two places give the same element
(`complexConjugationAt_eq_complexConjugationAt`). This is what lets a CM field carry a
place-free complex conjugation, and Mathlib's `IsCMField.complexConj` is the element it names:
on a CM field the place index may simply be dropped, and any statement about
`complexConjugationAt` there transfers to `complexConj`. The extension over `ℚ` need not be finite.

The file also records a criterion for being CM in these terms: an algebraic field with one
automorphism, not the identity, conjugating every complex embedding is CM.

## Main results

* `TauCeti.NumberField.complexConjugationAt_eq_complexConj`: the conjugation at any place is
  `IsCMField.complexConj`.
* `TauCeti.NumberField.complexConjugationAt_eq_complexConjugationAt`: consequently it does not
  depend on the place.
* `TauCeti.NumberField.isCMField_of_forall_isConj`: a field algebraic over `ℚ` with one
  automorphism conjugating every complex embedding, not the identity, is CM. Mathlib's
  `NumberField.IsCMField.of_forall_isConj` assumes that the field is Galois over `ℚ` and totally
  complex; this criterion assumes only that the field is algebraic over `ℚ` and has one
  automorphism, not the identity, conjugating every complex embedding.
* `RingHom.star_comp`: on a CM field, every ring endomorphism of `ℂ` commutes with complex
  conjugation on embeddings.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §12.
-/

public section

open NumberField NumberField.InfinitePlace

namespace TauCeti.NumberField

section General

open NumberField.ComplexEmbedding

variable {K : Type*} [Field K] [CharZero K] [Algebra.IsIntegral ℚ K]

open IntermediateField in
/-- **A field with a single nontrivial conjugation of all its complex embeddings is CM.** If `K`
is algebraic over `ℚ` and one automorphism `σ ≠ 1` of `K` satisfies `IsConj φ σ` for every
embedding `φ : K →+* ℂ`, then `K` is a CM field. Mathlib's `NumberField.IsCMField.of_forall_isConj`
proves this for `K` Galois over `ℚ` and totally complex; neither assumption is needed. -/
theorem isCMField_of_forall_isConj {σ : Gal(K/ℚ)} (hσ1 : σ ≠ 1)
    (hσ : ∀ φ : K →+* ℂ, IsConj φ σ) : IsCMField K := by
  have : IsTotallyComplex K := ⟨fun w ↦ isComplex_iff.mpr ((isConj_ne_one_iff (hσ _)).mp hσ1)⟩
  let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  have hσ' : Nat.card (Subgroup.zpowers σ) = 2 := by
    rw [Nat.card_zpowers, orderOf_isConj_two_of_ne_one (hσ φ) hσ1]
  have : Finite (Subgroup.zpowers σ) := Nat.finite_of_card_ne_zero (by positivity)
  let L := FixedPoints.subfield (Subgroup.zpowers σ) K
  have : IsTotallyReal L := ⟨fun w ↦ by
    obtain ⟨W, rfl⟩ := w.comap_surjective (K := K)
    dsimp only
    rw [← mk_embedding W, comap_mk, isReal_mk_iff]
    exact ComplexEmbedding.IsConj.isReal_comp
      (σ := IsGaloisGroup.mulEquivAlgEquiv (Subgroup.zpowers σ) L K ⟨σ, Subgroup.mem_zpowers σ⟩)
      (hσ W.embedding)⟩
  have : Algebra.IsQuadraticExtension L K := ⟨by
    rw [← IsGaloisGroup.card_eq_finrank (Subgroup.zpowers σ), hσ']⟩
  exact IsCMField.ofCMExtension L K

end General

variable (K : Type*) [Field K] [CharZero K] [Algebra.IsIntegral ℚ K] [NumberField.IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- **On a CM field the conjugation at any place is `IsCMField.complexConj`.** The simp normal
form is the canonical `complexConj`, so the place-dependent `complexConjugationAt` rewrites to
it. -/
@[simp]
theorem complexConjugationAt_eq_complexConj (w : InfinitePlace K) (hw : w.IsRamified K⁺) :
    complexConjugationAt K⁺ w hw = NumberField.IsCMField.complexConj K :=
  (eq_complexConjugationAt _ _ (NumberField.IsCMField.isConj_complexConj K w.embedding)).symm

/-- **On a CM field the conjugation does not depend on the place.** In general two ramified
places give conjugate elements, which need not be equal. -/
theorem complexConjugationAt_eq_complexConjugationAt (w w' : InfinitePlace K)
    (hw : w.IsRamified K⁺) (hw' : w'.IsRamified K⁺) :
    complexConjugationAt K⁺ w hw = complexConjugationAt K⁺ w' hw' := by
  simp

end TauCeti.NumberField

namespace AlgEquiv

/-- Complex conjugation of an algebraic CM field commutes with every rational automorphism. -/
theorem commute_complexConj {K : Type*} [Field K] [CharZero K] [Algebra.IsIntegral ℚ K]
    [IsCMField K] (g : Gal(K/ℚ)) :
    Commute g ((IsCMField.complexConj K).restrictScalars ℚ) := by
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  apply AlgEquiv.ext
  intro x
  apply φ.injective
  exact (IsCMField.complexEmbedding_complexConj K (φ.comp g.toRingHom) x).trans
    (IsCMField.complexEmbedding_complexConj K φ (g x)).symm

end AlgEquiv

namespace RingHom

variable {K : Type*} [Field K] [CharZero K] [Algebra.IsIntegral ℚ K] [NumberField.IsCMField K]

/-- On a CM field, every ring endomorphism `σ` of `ℂ` commutes with complex conjugation on the
image of an embedding: `conj ∘ σ ∘ φ = σ ∘ conj ∘ φ` (Milne, *Complex Multiplication*, p.13,
footnote 3). -/
theorem star_comp (σ : ℂ →+* ℂ) (φ : K →+* ℂ) : star (σ.comp φ) = σ.comp (star φ) := by
  ext x
  have h := NumberField.IsCMField.complexEmbedding_complexConj K (σ.comp φ) x
  simpa only [star_apply, comp_apply, Complex.star_def,
    NumberField.IsCMField.complexEmbedding_complexConj K φ x] using h.symm

end RingHom

end
