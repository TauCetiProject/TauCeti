/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.Embedding
public import TauCeti.RepresentationTheory.Quiver.Kronecker.FiniteRepType
public import TauCeti.RepresentationTheory.Quiver.OneLoop.FiniteRepType

/-!
# Loops and parallel arrows obstruct finite representation type

The loop quiver has infinitely many nilpotent Jordan block representations
(`TauCeti.not_isFiniteRepType_oneLoop`), and the Kronecker quiver `• ⇉ •` has infinitely many
indecomposable representations (`TauCeti.not_isFiniteRepType_kronecker`). Finite representation
type passes to subquivers (`TauCeti.IsFiniteRepType.of_quiverEmbedding`), so these two families
show that a quiver of finite representation type has no loops and at most one arrow from any
vertex to any other. These are the two smallest extended Dynkin obstructions, `Ã₀` and `Ã₁`,
in the non-Dynkin half of Gabriel's theorem.

## Main results

* `TauCeti.IsFiniteRepType.isEmpty_hom_self`: a quiver of finite representation type has no loops.
* `TauCeti.IsFiniteRepType.subsingleton_hom`: a quiver of finite representation type has no two
  parallel arrows.

## Implementation notes

The consequences are stated for representations with vertex spaces in the universe of the base
field, the universe in which the loop-quiver and Kronecker families are built.

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

end TauCeti
