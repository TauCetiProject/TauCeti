/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.Embedding
public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.TwoCycle
public import TauCeti.RepresentationTheory.Quiver.Kronecker.FiniteRepType
public import TauCeti.RepresentationTheory.Quiver.OneLoop.FiniteRepType
public import TauCeti.RepresentationTheory.Quiver.Subspace.FiniteRepType

/-!
# Extended Dynkin subquivers obstruct finite representation type

The loop quiver has infinitely many nilpotent Jordan block representations
(`TauCeti.not_isFiniteRepType_oneLoop`), and the Kronecker quiver `• ⇉ •` has infinitely many
indecomposable representations (`TauCeti.not_isFiniteRepType_kronecker`). Finite representation
type passes to subquivers (`TauCeti.IsFiniteRepType.of_quiverEmbedding`), so these families,
together with the oriented two-cycle obstruction, show that a quiver of finite representation type
has no loops and at most one arrow between any two vertices, counting both directions. These are
the two smallest extended Dynkin obstructions, `Ã₀` and `Ã₁`, in the non-Dynkin half of Gabriel's
theorem.

The four subspace quiver, whose underlying graph is the extended Dynkin diagram `D4~`, has
infinite representation type as well (`TauCeti.not_isFiniteRepType_subspace_fin_four`), so a
quiver of finite representation type has no vertex receiving arrows from four distinct other
vertices.

## Main results

* `TauCeti.IsFiniteRepType.isEmpty_hom_self`: a quiver of finite representation type has no loops.
* `TauCeti.IsFiniteRepType.subsingleton_hom`: a quiver of finite representation type has no two
  parallel arrows.
* `TauCeti.IsFiniteRepType.isEmpty_hom_reverse`: an arrow has no reverse arrow.
* `TauCeti.IsFiniteRepType.card_hom_add_card_hom_le_one`: there is at most one arrow between two
  vertices, counting both directions, and no loop.
* `TauCeti.not_isFiniteRepType_of_forall_nonempty_hom`: a vertex receiving arrows from four distinct
  other vertices refutes finite representation type.
* `TauCeti.not_isFiniteRepType_subspace`: a subspace quiver with at least four outer vertices has
  infinite representation type.

## Implementation notes

The consequences are stated for representations with vertex spaces in the universe of the base
field, the universe in which the loop-quiver, Kronecker and four subspace families are built.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Volume I, Chapter VII.
* H. Derksen, J. Weyman, *An Introduction to Quiver Representations*, Chapter 4.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v w

variable {k : Type u} [Field k] {Q : Type v} [Quiver.{w} Q]

/-- The embedding of the loop quiver onto a loop `α` of `Q`. -/
private def oneLoopEmbedding {i : Q} (α : i ⟶ i) : QuiverEmbedding Quiver.OneLoop Q where
  obj _ := i
  map _ := α
  obj_injective a b _ := Subsingleton.elim a b
  map_injective _ := Subsingleton.elim _ _

/-- The embedding of the Kronecker quiver `• ⇉ •` onto two distinct parallel arrows `α`, `β` of `Q`
between distinct vertices. -/
private def kroneckerEmbedding {i j : Q} (hij : i ≠ j) {α β : i ⟶ j} (hαβ : α ≠ β) :
    QuiverEmbedding (Quiver.Kronecker Bool) Q where
  obj
    | .src => i
    | .tgt => j
  map {a b} e := match a, b, e with
    | .src, .tgt, e => bif e then α else β
    | .src, .src, e => isEmptyElim e
    | .tgt, .src, e => isEmptyElim e
    | .tgt, .tgt, e => isEmptyElim e
  obj_injective a b hab := by
    cases a <;> cases b
    · rfl
    · exact absurd hab hij
    · exact absurd hab.symm hij
    · rfl
  map_injective {a b} e₁ e₂ he := by
    match a, b, e₁, e₂ with
    | .src, .tgt, e₁, e₂ =>
      cases e₁ <;> cases e₂ <;> first | rfl | exact absurd he hαβ | exact absurd he.symm hαβ
    | .src, .src, e₁, _ => exact isEmptyElim e₁
    | .tgt, .src, e₁, _ => exact isEmptyElim e₁
    | .tgt, .tgt, e₁, _ => exact isEmptyElim e₁

/-- **A quiver of finite representation type has no loops**: a loop embeds the loop quiver, whose
nilpotent Jordan blocks are infinitely many pairwise non-isomorphic indecomposables. -/
theorem IsFiniteRepType.isEmpty_hom_self (h : IsFiniteRepType.{u, v, w, u} k Q) (i : Q) :
    IsEmpty (i ⟶ i) :=
  ⟨fun α ↦ not_isFiniteRepType_oneLoop k (h.of_quiverEmbedding (oneLoopEmbedding.{v, w, 0} α))⟩

/-- **A quiver of finite representation type has at most one arrow from any vertex to any other**:
two parallel arrows between distinct vertices embed the Kronecker quiver `• ⇉ •`, and two loops
at one vertex are excluded already by `TauCeti.IsFiniteRepType.isEmpty_hom_self`. -/
theorem IsFiniteRepType.subsingleton_hom (h : IsFiniteRepType.{u, v, w, u} k Q) (i j : Q) :
    Subsingleton (i ⟶ j) := by
  refine ⟨fun α β ↦ by_contra fun hαβ ↦ ?_⟩
  by_cases hij : i = j
  · subst hij
    exact (h.isEmpty_hom_self i).false α
  · exact not_isFiniteRepType_kronecker k Bool (h.of_quiverEmbedding (kroneckerEmbedding hij hαβ))

/-- An arrow in a quiver of finite representation type has no reverse arrow. -/
theorem IsFiniteRepType.isEmpty_hom_reverse (h : IsFiniteRepType.{u, v, w, u} k Q)
    {a b : Q} (α : a ⟶ b) : IsEmpty (b ⟶ a) := by
  by_cases hab : a = b
  · subst b
    exact h.isEmpty_hom_self a
  · exact ⟨fun β ↦ not_isFiniteRepType_of_opposite_hom hab α β h⟩

/-- Over a quiver of finite representation type, two vertices are
joined by at most one arrow, counting both directions, and there is no loop. -/
theorem IsFiniteRepType.card_hom_add_card_hom_le_one [∀ a b : Q, Fintype (a ⟶ b)]
    (h : IsFiniteRepType.{u, v, w, u} k Q) (a b : Q) :
    Fintype.card (a ⟶ b) + Fintype.card (b ⟶ a) ≤ 1 := by
  have hle (x y : Q) : Fintype.card (x ⟶ y) ≤ 1 :=
    Fintype.card_le_one_iff_subsingleton.mpr (h.subsingleton_hom x y)
  rcases isEmpty_or_nonempty (a ⟶ b) with hl | hl
  · simpa [Fintype.card_eq_zero] using hle b a
  · have := h.isEmpty_hom_reverse hl.some
    simpa [Fintype.card_eq_zero] using hle a b

/-- The embedding of the four subspace quiver onto four arrows `α i : x i ⟶ c` into a vertex `c`
from four pairwise distinct vertices other than `c`. -/
private def subspaceEmbedding {c : Q} (x : Fin 4 ↪ Q) (hc : c ∉ Set.range x)
    (α : ∀ i, x i ⟶ c) : QuiverEmbedding (Quiver.Subspace (Fin 4)) Q where
  obj
    | .center => c
    | .outer i => x i
  map {a b} e := match a, b, e with
    | .outer i, .center, _ => α i
    | .center, .center, e => isEmptyElim e
    | .center, .outer _, e => isEmptyElim e
    | .outer _, .outer _, e => isEmptyElim e
  obj_injective a b hab := by
    cases a <;> cases b
    · rfl
    · exact absurd ⟨_, hab.symm⟩ hc
    · exact absurd ⟨_, hab⟩ hc
    · exact congrArg _ (x.injective hab)
  map_injective {_ _} _ _ _ := Subsingleton.elim _ _

/-- **Four arrows into one vertex from four other distinct vertices obstruct finite representation
type**: they embed the four subspace quiver, whose underlying graph is the extended Dynkin diagram
`D4~` and whose Jordan block configurations are infinitely many pairwise non-isomorphic
indecomposables. -/
theorem not_isFiniteRepType_of_forall_nonempty_hom {c : Q} (x : Fin 4 ↪ Q) (hc : c ∉ Set.range x)
    (hα : ∀ i, Nonempty (x i ⟶ c)) : ¬ IsFiniteRepType.{u, v, w, u} k Q := fun h ↦
  not_isFiniteRepType_subspace_fin_four k
    (h.of_quiverEmbedding (subspaceEmbedding x hc fun i ↦ (hα i).some))

/-- **A subspace quiver with at least four outer vertices has infinite representation type over
every field**: four of its arrows already embed the four subspace quiver. -/
theorem not_isFiniteRepType_subspace {ι : Type v} (f : Fin 4 ↪ ι) :
    ¬ IsFiniteRepType.{u, v, 1, u} k (Quiver.Subspace ι) :=
  not_isFiniteRepType_of_forall_nonempty_hom (c := .center)
    (f.trans ⟨Quiver.Subspace.outer, fun _ _ h ↦ Quiver.Subspace.outer.inj h⟩)
    (by rintro ⟨i, hi⟩; cases hi) fun i ↦ ⟨Quiver.Subspace.arrow (f i)⟩

end TauCeti
