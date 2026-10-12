/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.Alternating.Basic
public import TauCeti.RepresentationTheory.Induction.Clifford.Alternating.Standard
import TauCeti.RepresentationTheory.CharacterTable.Completeness
import TauCeti.RepresentationTheory.AsModule

/-!
# The four irreducible representations of `A₄`

Over an algebraically closed field of characteristic zero, the simple representations of `A₄`
are the three linear characters and the restricted standard representation of dimension three.
Once a nontrivial linear character `χ` is chosen, the linear characters are `1`, `χ`, and `χ⁻¹`.
The theorem `FDRep.simple_alternatingGroupFour_iff` identifies all four possibilities up to
isomorphism. This makes the constituent list exhaustive when applying Clifford theory to
`A₄ ◁ S₄`.

Completeness follows from `TauCeti.ClassFunction.exists_nonempty_equiv`: the three distinct
linear characters and the standard representation give four inequivalent irreducibles, matching
the four conjugacy classes. The linear-character count and the standard representation's
irreducibility are supplied by the imported alternating-group theory.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, Chapters 2 and 6.
* J.-P. Serre, *Linear Representations of Finite Groups*, §§2.5 and 5.2.
-/

public section

open CategoryTheory

namespace FDRep

open TauCeti

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k]

private noncomputable def alternatingFourFamily
    (i : Option (alternatingGroup (Fin 4) →* kˣ)) : FDRep k (alternatingGroup (Fin 4)) :=
  match i with
  | none => alternatingGroupFourStandard k
  | some χ => ofLinearCharacter χ

private theorem alternatingFourFamily_simple
    (i : Option (alternatingGroup (Fin 4) →* kˣ)) : Simple (alternatingFourFamily i) := by
  cases i with
  | none => exact simple_alternatingGroupFourStandard k
  | some χ => exact simple_ofLinearCharacter χ

omit [IsAlgClosed k] [CharZero k] in
private theorem alternatingFourFamily_pairwise :
    Pairwise fun i j => IsEmpty (Representation.Equiv (alternatingFourFamily (k := k) i).ρ
      (alternatingFourFamily j).ρ) := by
  intro i j hij
  refine ⟨fun e => ?_⟩
  have hiso := nonempty_fdRepIso_iff.mpr ⟨e⟩
  cases i with
  | none =>
    cases j with
    | none => exact hij rfl
    | some χ =>
      have hdim : Module.finrank k (alternatingGroupFourStandard k) =
          Module.finrank k (ofLinearCharacter χ) := (isoToLinearEquiv hiso.some).finrank_eq
      simp at hdim
  | some χ =>
    cases j with
    | none =>
      have hdim : Module.finrank k (ofLinearCharacter χ) =
          Module.finrank k (alternatingGroupFourStandard k) :=
        (isoToLinearEquiv hiso.some).finrank_eq
      simp at hdim
    | some ψ => exact hij (congrArg some ((nonempty_iso_ofLinearCharacter_iff χ ψ).mp hiso))

private theorem exists_iso_alternatingFourFamily (W : FDRep k (alternatingGroup (Fin 4)))
    [Simple W] : ∃ i, Nonempty (W ≅ alternatingFourFamily i) := by
  have : NeZero ((Monoid.exponent (Abelianization (alternatingGroup (Fin 4))) : ℕ) : k) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  have hlinear := card_monoidHom_alternatingGroup k (α := Fin 4) (by simp)
  have : Finite (alternatingGroup (Fin 4) →* kˣ) :=
    Nat.finite_of_card_ne_zero (by omega)
  let _ := Fintype.ofFinite (alternatingGroup (Fin 4) →* kˣ)
  let _ : Invertible (Nat.card (alternatingGroup (Fin 4)) : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hcard : Nat.card (Option (alternatingGroup (Fin 4) →* kˣ)) =
      Nat.card (ConjClasses (alternatingGroup (Fin 4))) := by
    rw [← alternatingGroupFourClassData.numClasses_eq_card_conjClasses,
      numClasses_alternatingGroupFourClassData, Nat.card_eq_fintype_card, Fintype.card_option]
    rw [Nat.card_eq_fintype_card] at hlinear
    omega
  have : ∀ i, Representation.IsIrreducible (alternatingFourFamily (k := k) i).ρ := fun i =>
    have := alternatingFourFamily_simple (k := k) i
    isIrreducible_of_simple _
  have := isIrreducible_of_simple W
  obtain ⟨i, hi⟩ := ClassFunction.exists_nonempty_equiv
    (fun i => (alternatingFourFamily (k := k) i).ρ) alternatingFourFamily_pairwise hcard W.ρ
  exact ⟨i, nonempty_fdRepIso_iff.mpr hi⟩

/-- A representation of `A₄` over an algebraically closed characteristic-zero field is simple
exactly when it is isomorphic to one of the three linear characters or the restricted standard
representation. Any nontrivial linear character `χ` supplies the list `1`, `χ`, `χ⁻¹`. -/
theorem simple_alternatingGroupFour_iff (W : FDRep k (alternatingGroup (Fin 4)))
    {χ : alternatingGroup (Fin 4) →* kˣ} (hχ : χ ≠ 1) :
    Simple W ↔ Nonempty (W ≅ ofLinearCharacter (1 : alternatingGroup (Fin 4) →* kˣ)) ∨
      Nonempty (W ≅ ofLinearCharacter χ) ∨ Nonempty (W ≅ ofLinearCharacter χ⁻¹) ∨
      Nonempty (W ≅ alternatingGroupFourStandard k) := by
  constructor
  · intro hW
    obtain ⟨i, hi⟩ := exists_iso_alternatingFourFamily W
    cases i with
    | none => exact Or.inr (Or.inr (Or.inr hi))
    | some ψ =>
      rcases monoidHom_alternatingGroup_eq_one_or_eq_or_eq_inv (by simp) hχ ψ with
        rfl | rfl | rfl
      · exact Or.inl hi
      · exact Or.inr (Or.inl hi)
      · exact Or.inr (Or.inr (Or.inl hi))
  · rintro (h | h | h | h)
    · exact Simple.of_iso h.some
    · exact Simple.of_iso h.some
    · exact Simple.of_iso h.some
    · have := simple_alternatingGroupFourStandard k
      exact Simple.of_iso h.some

end FDRep
