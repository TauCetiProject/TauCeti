/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Frobenius

/-!
# Complete resolutions in Frobenius exact categories

In a Frobenius exact category, every object admits a bi-infinite sequence of conflations
`Zⁿ ↪ Pⁿ ↠ Zⁿ⁺¹`, with projective-injective middle terms and the given object as `Z⁰`.
Splicing their maps produces a complete resolution. The sequence is constructed by iterating
injective presentations in nonnegative degrees and projective presentations in negative degrees.
The interface retains the conflations, so an exact functor can transport the sequence before
its maps are spliced.

## References

* Ragnar-Olaf Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Section 4.
* Theo Bühler, *Exact categories*, Sections 11–13.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace TauCeti.ExactStructure.IsFrobenius

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] {E : ExactStructure C} (hE : E.IsFrobenius)

private noncomputable def cosyzygy (X : C) : ℕ → C
  | 0 => X
  | n + 1 => (hE.enoughInjectives.injectivePresentation (cosyzygy X n)).K

private noncomputable def syzygy (X : C) : ℕ → C
  | 0 => X
  | n + 1 => (hE.enoughProjectives.projectivePresentation (syzygy X n)).K

private noncomputable def positiveConflation (X : C) (n : ℕ) : ShortComplex C :=
  let P := hE.enoughInjectives.injectivePresentation (cosyzygy hE X n)
  ShortComplex.mk P.i P.p P.zero

private noncomputable def negativeConflation (X : C) (n : ℕ) : ShortComplex C :=
  let P := hE.enoughProjectives.projectivePresentation (syzygy hE X n)
  ShortComplex.mk P.i P.p P.zero

private noncomputable def conflationSequence (X : C) : ℤ → ShortComplex C
  | .ofNat n => positiveConflation hE X n
  | .negSucc n => negativeConflation hE X n

include hE in
/-- Every object of a Frobenius exact category admits a bi-infinite sequence of conflations
with projective-injective middle terms, starting at that object in degree zero. The connecting
isomorphisms identify the cokernel of each conflation with the kernel of the next one. -/
theorem exists_projective_conflation_sequence (X : C) :
    ∃ S : ℤ → ShortComplex C, (∀ n, E.Conflation (S n)) ∧
      (∀ n, E.isProjective (S n).X₂) ∧
      (∀ n, Nonempty ((S n).X₃ ≅ (S (n + 1)).X₁)) ∧ Nonempty ((S 0).X₁ ≅ X) := by
  refine ⟨conflationSequence hE X, ?_, ?_, ?_, ⟨Iso.refl X⟩⟩
  · intro n
    cases n with
    | ofNat n => exact (hE.enoughInjectives.injectivePresentation _).conflation
    | negSucc n => exact (hE.enoughProjectives.projectivePresentation _).conflation
  · intro n
    cases n with
    | ofNat n => exact hE.isProjective_I (hE.enoughInjectives.injectivePresentation _)
    | negSucc n => exact (hE.enoughProjectives.projectivePresentation _).isProjective
  · intro n
    cases n with
    | ofNat n => exact ⟨Iso.refl _⟩
    | negSucc n =>
        cases n with
        | zero => exact ⟨Iso.refl _⟩
        | succ n => exact ⟨Iso.refl _⟩

end TauCeti.ExactStructure.IsFrobenius
