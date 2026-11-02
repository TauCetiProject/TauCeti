/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.CodedConnectives
public import TauCeti.ModelTheory.Infinitary.Equiv
public import TauCeti.ModelTheory.Infinitary.LanguageMap
public import Mathlib.Data.Set.Countable

/-!
# Theories of `L_{ω₁ω}` sentences

An `L_{ω₁ω}` theory is a set of `L_{ω₁ω}` sentences, and a structure is a model of it when it
satisfies every member. A *countable* theory can be replaced by a single sentence: its members,
enumerated into the carrier `ℕ` along `IndexCoding.ofEncodableWith`, form one countable
conjunction, which a structure satisfies exactly when it is a model of the theory. Indices that
code no member carry `⊤`, so the conjunction of the empty theory holds in every structure.

Theories move along language homomorphisms, sentence by sentence; along an expansion a structure
is a model of the image of a theory exactly when it is a model of the theory.

## Main definitions

* `FirstOrder.Language.Theoryω`: the `L_{ω₁ω}` theories of a language.
* `FirstOrder.Language.Theoryω.Model`: a structure satisfies every sentence of a theory.
* `FirstOrder.Language.Theoryω.conjunction`: the countable conjunction of a countable theory.
* `FirstOrder.Language.LHom.onTheoryω`: the image of a theory under a language homomorphism.
* `FirstOrder.Language.OmitsType`: a structure omits a partial type when no tuple realizes all of
  it.

## Main results

* `FirstOrder.Language.Theoryω.realize_conjunction_iff`: a structure satisfies the conjunction of
  a countable theory exactly when it is a model of the theory.
* `FirstOrder.Language.Theoryω.Model.mono`, `FirstOrder.Language.Theoryω.model_empty`,
  `FirstOrder.Language.Theoryω.model_union_iff`, `FirstOrder.Language.Theoryω.model_insert_iff`:
  the basic laws of modelhood.
* `FirstOrder.Language.Theoryω.model_image_toOmega_iff`: a structure is a model of the image of
  a first-order theory exactly when it is a model of the first-order theory.
* `FirstOrder.Language.StrongHomClass.theoryω_model_iff`: isomorphic structures are models of the
  same theories.
* `FirstOrder.Language.LHom.onTheoryω_model`: along an expansion, a structure is a model of the
  image of a theory exactly when it is a model of the theory.
* `Set.Countable.onTheoryω`: the image of a countable theory is countable.

## References

* The definitions follow `cameronfreer/infinitary-logic` at commit
  `518a366cba97b1ae8c4dc64a297a396939bc3e0b`, `InfinitaryLogic/Lomega1omega/Theory.lean`, and
  the shape of Mathlib's first-order `Theory` and `Theory.Model`.
* Divergences from that source: only theories, modelhood and the countable conjunction are taken
  from it; the conjunction is the coded conjunction `iInfAlong` along
  `IndexCoding.ofEncodableWith`, so the empty theory needs no separate case.
* `FirstOrder.Language.LHom.onTheoryω`, `FirstOrder.Language.LHom.mem_onTheoryω` and
  `FirstOrder.Language.LHom.onTheoryω_model` follow Mathlib's first-order `LHom.onTheory`,
  `LHom.mem_onTheory` and `LHom.onTheory_model`.
-/

public section

universe u v u' v' w w'

namespace FirstOrder

namespace Language

variable (L : Language.{u, v})

/-- An `L_{ω₁ω}` theory: a set of `L_{ω₁ω}` sentences. -/
abbrev Theoryω := Set L.Sentenceω

variable {L}

namespace Theoryω

variable {T T' : L.Theoryω} {M : Type w} [L.Structure M]

/-- A structure is a **model** of an `L_{ω₁ω}` theory when it satisfies every sentence of the
theory. -/
def Model (T : L.Theoryω) (M : Type w) [L.Structure M] : Prop :=
  ∀ φ ∈ T, SentenceInf.Realize φ M

/-- Unfolding lemma for `Theoryω.Model`. -/
theorem model_iff : T.Model M ↔ ∀ φ ∈ T, SentenceInf.Realize φ M :=
  Iff.rfl

/-- A model of a theory satisfies each of its sentences. -/
theorem Model.realize_of_mem (h : T.Model M) {φ : L.Sentenceω} (hφ : φ ∈ T) :
    SentenceInf.Realize φ M :=
  h φ hφ

/-- A model of a theory is a model of every subtheory. -/
theorem Model.mono (h : T'.Model M) (hT : T ⊆ T') : T.Model M :=
  fun φ hφ => h φ (hT hφ)

/-- Every structure is a model of the empty theory. -/
@[simp]
theorem model_empty : (∅ : L.Theoryω).Model M :=
  fun _ h => h.elim

/-- A structure is a model of a union exactly when it is a model of both theories. -/
@[simp]
theorem model_union_iff : (T ∪ T').Model M ↔ T.Model M ∧ T'.Model M := by
  simp only [model_iff, Set.mem_union, or_imp, forall_and]

/-- A structure is a model of `insert φ T` exactly when it satisfies `φ` and is a model of `T`. -/
@[simp]
theorem model_insert_iff {φ : L.Sentenceω} :
    (insert φ T).Model M ↔ SentenceInf.Realize φ M ∧ T.Model M := by
  simp only [model_iff, Set.mem_insert_iff, forall_eq_or_imp]

/-- A structure is a model of `{φ}` exactly when it satisfies `φ`. -/
@[simp]
theorem model_singleton_iff {φ : L.Sentenceω} :
    ({φ} : L.Theoryω).Model M ↔ SentenceInf.Realize φ M := by
  simp only [model_iff, Set.mem_singleton_iff, forall_eq]

/-- A structure is a model of the image of a first-order theory in `L_{ω₁ω}` exactly when it is a
model of the first-order theory. -/
@[simp]
theorem model_image_toOmega_iff {T : L.Theory} :
    Model (BoundedFormula.toOmega '' T) M ↔ M ⊨ T := by
  simp only [model_iff, Set.forall_mem_image, Sentence.realize_toInf, Theory.model_iff]

/-! ### The conjunction of a countable theory -/

/-- The **conjunction of a countable theory**: its sentences, enumerated into the carrier `ℕ`
along `IndexCoding.ofEncodableWith`, joined by one countable conjunction. Indices that code no
sentence carry `⊤`. -/
noncomputable def conjunction (T : L.Theoryω) (hT : T.Countable) : L.Sentenceω :=
  BoundedFormulaInf.iInfAlong (TauCeti.IndexCoding.ofEncodableWith hT.toEncodable)
    fun φ : T => φ.1

/-- The conjunction of a countable theory is the coded conjunction of its sentences. -/
theorem conjunction_def (T : L.Theoryω) (hT : T.Countable) :
    T.conjunction hT = BoundedFormulaInf.iInfAlong
      (TauCeti.IndexCoding.ofEncodableWith hT.toEncodable) fun φ : T => φ.1 :=
  (rfl)

/-- **A countable theory is one sentence.** A structure satisfies the conjunction of a countable
theory exactly when it is a model of the theory. -/
@[simp]
theorem realize_conjunction_iff (hT : T.Countable) :
    SentenceInf.Realize (T.conjunction hT) M ↔ T.Model M := by
  rw [SentenceInf.realize_def, FormulaInf.realize_def, conjunction_def,
    BoundedFormulaInf.realize_iInfAlong, model_iff]
  simp only [Subtype.forall, SentenceInf.realize_def, FormulaInf.realize_def]

end Theoryω

/-! ### Omitting types -/

/-- A structure **omits** a set `p` of `L_{ω₁ω}` formulas in `n` bound variables, a partial type,
when no `n`-tuple of the structure realizes every member of `p`. -/
def OmitsType (M : Type w) [L.Structure M] {n : ℕ} (p : Set (L.BoundedFormulaω Empty n)) : Prop :=
  ∀ a : Fin n → M, ∃ φ ∈ p, ¬ φ.Realize Empty.elim a

/-- Unfolding lemma for `OmitsType`. -/
theorem omitsType_iff {M : Type w} [L.Structure M] {n : ℕ} {p : Set (L.BoundedFormulaω Empty n)} :
    OmitsType M p ↔ ∀ a : Fin n → M, ∃ φ ∈ p, ¬ φ.Realize Empty.elim a :=
  Iff.rfl

namespace LHom

variable {L' : Language.{u', v'}}

/-- The image of an `L_{ω₁ω}` theory under a language homomorphism: the images of its sentences. -/
def onTheoryω (g : L →ᴸ L') (T : L.Theoryω) : L'.Theoryω :=
  g.onBoundedFormulaInf '' T

/-- The image of a theory is the image of its sentences. -/
theorem onTheoryω_def (g : L →ᴸ L') (T : L.Theoryω) : g.onTheoryω T = g.onBoundedFormulaInf '' T :=
  (rfl)

/-- Membership in the image of a theory. -/
@[simp]
theorem mem_onTheoryω {g : L →ᴸ L'} {T : L.Theoryω} {φ : L'.Sentenceω} :
    φ ∈ g.onTheoryω T ↔ ∃ φ₀ ∈ T, g.onBoundedFormulaInf φ₀ = φ :=
  Iff.rfl

/-- **Modelhood along an expansion.** If the `L'`-structure on `M` expands its `L`-structure along
`g`, then `M` is a model of the image of `T` exactly when it is a model of `T`. No injectivity of
`g` and no countability of `T` is needed. This is the infinitary form of Mathlib's
`LHom.onTheory_model`. -/
@[simp]
theorem onTheoryω_model (g : L →ᴸ L') {M : Type w} [L.Structure M] [L'.Structure M]
    [g.IsExpansionOn M] (T : L.Theoryω) : (g.onTheoryω T).Model M ↔ T.Model M := by
  simp only [Theoryω.model_iff, mem_onTheoryω, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, SentenceInf.realize_def, FormulaInf.realize_def,
    realize_onBoundedFormulaInf]

end LHom

/-- The image of a countable theory under a language homomorphism is countable. -/
theorem _root_.Set.Countable.onTheoryω {L' : Language.{u', v'}} {T : L.Theoryω} (hT : T.Countable)
    (g : L →ᴸ L') : (g.onTheoryω T).Countable :=
  hT.image _

namespace StrongHomClass

variable {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]
  {F : Type*} [EquivLike F M N] [StrongHomClass L F M N]

/-- Isomorphic structures are models of the same `L_{ω₁ω}` theories. -/
theorem theoryω_model_iff (g : F) (T : L.Theoryω) : T.Model M ↔ T.Model N := by
  simp only [Theoryω.model_iff, StrongHomClass.realize_sentenceInf g]

end StrongHomClass

end Language

end FirstOrder
