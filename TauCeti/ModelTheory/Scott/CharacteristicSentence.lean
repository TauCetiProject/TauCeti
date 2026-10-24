/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.Finite
public import TauCeti.ModelTheory.Scott.AtomicDiagram
public import TauCeti.ModelTheory.Scott.PotentialIso
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Scott sentences of finite structures

The canonical Scott sentence of a finite structure `M` in a countable relational language holds
in a structure of any cardinality exactly when that structure is isomorphic to `M`, since
potential isomorphism with a finite structure is isomorphism.

When the language is also finite, the same class of structures is cut out by a first-order
sentence, the characteristic sentence of `M`: there are elements with the atomic type of an
enumeration of `M`, and every element is one of them. The Scott sentence of a finite structure in
a finite relational language is therefore equivalent to a first-order sentence.

Finiteness of the language cannot be dropped from this: `TauCeti.ModelTheory.Scott.NatPredicate`
shows that in the language of countably many unary predicates, no one-point structure has a
first-order sentence characterizing it up to isomorphism.

## Main results

* `TauCeti.realize_scottSentence_iff_of_finite`: the Scott sentence of a finite structure holds
  exactly in its isomorphic copies, of any cardinality.
* `TauCeti.characteristicSentence` and `TauCeti.realize_characteristicSentence_iff`: the
  first-order characteristic sentence of a finite structure in a finite relational language.
* `TauCeti.realize_scottSentence_iff_realize_characteristicSentence`: in a finite relational
  language, the Scott sentence of a finite structure is equivalent to its characteristic
  sentence.

## References

* Dana Scott, *Logic with denumerably long formulas and finite strings of quantifiers*, 1965.
* Heinz-Dieter Ebbinghaus and Jörg Flum, *Finite Model Theory*, Springer, 1995, for
  characteristic sentences of finite structures.
-/

public section

universe u v w w'

namespace TauCeti

open FirstOrder FirstOrder.Language

section Scott

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ k, L.Relations k)]
variable (M : Type w) [L.Structure M] [Finite M] {N : Type w'} [L.Structure N]

/-- The Scott sentence of a finite structure holds in a structure of any cardinality exactly
when that structure is isomorphic to it. -/
theorem realize_scottSentence_iff_of_finite :
    SentenceInf.Realize (scottSentence (L := L) M) N ↔ Nonempty (M ≃[L] N) :=
  ⟨fun h => finite_potentialIso_iff_iso.mp (potentialIso_of_realize_scottSentence M h),
    fun ⟨e⟩ => e.realize_scottSentence⟩

end Scott

section Characteristic

variable {L : Language.{u, v}} [Finite (Σ k, L.Relations k)]
variable (M : Type w) [L.Structure M] [Finite M] {N : Type w'} [L.Structure N]

/-- The characteristic sentence of a finite structure `M` in a finite relation language: there
are elements `x₀, …, xₘ₋₁`, where `m = Nat.card M`, with the atomic type of an enumeration
of `M`, such that every element is one of them. -/
noncomputable def characteristicSentence : L.Sentence :=
  (firstOrderAtomicDiagram (L := L) (Finite.equivFin M).symm ⊓
    (BoundedFormula.iSup fun i : Fin (Nat.card M) =>
      (&(Fin.last (Nat.card M))).bdEqual &i.castSucc).all).exs

/-- The characteristic sentence existentially quantifies the atomic diagram of an enumeration
of `M`, together with the statement that every element is one of the enumerated ones. -/
theorem characteristicSentence_def :
    characteristicSentence (L := L) M =
      (firstOrderAtomicDiagram (L := L) (Finite.equivFin M).symm ⊓
        (BoundedFormula.iSup fun i : Fin (Nat.card M) =>
          (&(Fin.last (Nat.card M))).bdEqual &i.castSucc).all).exs := by
  rfl

variable [L.IsRelational]

/-- In a finite relational language, the characteristic sentence of a finite structure holds
in a structure of any cardinality exactly when that structure is isomorphic to it. -/
theorem realize_characteristicSentence_iff :
    N ⊨ characteristicSentence (L := L) M ↔ Nonempty (M ≃[L] N) := by
  let a : Fin (Nat.card M) → M := (Finite.equivFin M).symm
  have ha : Function.Surjective a := (Finite.equivFin M).symm.surjective
  simp only [characteristicSentence_def, Sentence.Realize,
    BoundedFormula.realize_exs, BoundedFormula.realize_inf, BoundedFormula.realize_all,
    BoundedFormula.realize_iSup, BoundedFormula.realize_bdEqual, Term.realize_var,
    Function.comp_apply, Sum.elim_inr, Fin.snoc_last, Fin.snoc_castSucc,
    realize_firstOrderAtomicDiagram_iff_sameAtomicType]
  constructor
  · rintro ⟨b, hab, hb⟩
    obtain ⟨f, hf⟩ := hab.exists_embedding_comp_eq ha
    have hsurj : Function.Surjective f := fun y => by
      obtain ⟨i, hi⟩ := hb y
      exact ⟨a i, (congrFun hf i).trans hi.symm⟩
    exact ⟨⟨Equiv.ofBijective f ⟨f.injective, hsurj⟩, f.map_fun', f.map_rel'⟩⟩
  · rintro ⟨e⟩
    refine ⟨e ∘ a, (sameAtomicType_iff _ _).mpr
      ⟨fun i j => e.injective.eq_iff.symm, fun r f => (e.map_rel r (a ∘ f)).symm⟩, fun y => ?_⟩
    obtain ⟨i, hi⟩ := ha (e.symm y)
    exact ⟨i, by simp [hi]⟩

/-- A finite structure satisfies its characteristic sentence. -/
@[simp]
theorem realize_characteristicSentence_self : M ⊨ characteristicSentence (L := L) M :=
  (realize_characteristicSentence_iff M).mpr ⟨.refl L M⟩

/-- In a finite relational language, the Scott sentence of a finite structure is equivalent to
its first-order characteristic sentence, in structures of every cardinality. -/
theorem realize_scottSentence_iff_realize_characteristicSentence :
    SentenceInf.Realize (scottSentence (L := L) M) N ↔ N ⊨ characteristicSentence (L := L) M := by
  rw [realize_scottSentence_iff_of_finite, realize_characteristicSentence_iff]

end Characteristic

end TauCeti
