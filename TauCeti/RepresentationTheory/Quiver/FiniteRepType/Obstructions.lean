/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Cycle.FiniteRepType
public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.Embedding
public import TauCeti.RepresentationTheory.Quiver.Kronecker.FiniteRepType
public import TauCeti.RepresentationTheory.Quiver.OneLoop.FiniteRepType
import Mathlib.Tactic.FinCases

/-!
# Oriented cycles and parallel arrows obstruct finite representation type

The loop quiver has infinitely many nilpotent Jordan block representations
(`TauCeti.not_isFiniteRepType_oneLoop`), the Kronecker quiver `• ⇉ •` has infinitely many
indecomposable representations (`TauCeti.not_isFiniteRepType_kronecker`), and so does the cycle
quiver on `n + 2` vertices (`TauCeti.not_isFiniteRepType_cycle`). Finite representation type passes
to subquivers (`TauCeti.IsFiniteRepType.of_quiverEmbedding`), so these three families show that a
quiver of finite representation type has no loops, at most one arrow from any vertex to any other,
and no oriented cycle at all. These are the extended Dynkin obstructions `Ã₀`, `Ã₁` and `Ã_{n+1}`
in the non-Dynkin half of Gabriel's theorem.

An oriented cycle is presented as an injective family `x : Fin (n + 2) → Q` of vertices together
with an arrow `x i ⟶ x (i + 1)` for every `i`, the addition being cyclic in `Fin (n + 2)`; the
injectivity is what makes the family a subquiver rather than a closed walk, and the loop quiver
covers the degenerate case of a single vertex. Its smallest instance is a pair of vertices joined
in both directions, which is the `Ã₁` graph in the orientation the Kronecker quiver does not
provide, and which `TauCeti.IsFiniteRepType.isEmpty_hom_of_hom` rules out; together with the two
statements above, no arrow of a quiver of finite representation type admits a reverse arrow, so the
underlying graph of such a quiver is *simple*.

## Main results

* `TauCeti.IsFiniteRepType.isEmpty_hom_self`: a quiver of finite representation type has no loops.
* `TauCeti.IsFiniteRepType.subsingleton_hom`: a quiver of finite representation type has no two
  parallel arrows.
* `TauCeti.not_isFiniteRepType_of_injective_of_nonempty_hom_succ`: a quiver carrying an oriented
  cycle through distinct vertices has infinite representation type.
* `TauCeti.IsFiniteRepType.isEmpty_hom_of_hom`: in a quiver of finite representation type an arrow
  admits no reverse arrow.

## Implementation notes

The consequences are stated for representations with vertex spaces in the universe of the base
field, the universe in which the loop-quiver, Kronecker and cycle families are built.

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

/-- The embedding of the cycle quiver onto an oriented cycle of `Q` through distinct vertices. -/
private def cycleEmbedding {n : ℕ} {x : Fin (n + 2) → Q} (hx : Function.Injective x)
    (α : ∀ i : Fin (n + 2), x i ⟶ x (i + 1)) : QuiverEmbedding (Quiver.Cycle n) Q where
  obj c := x c.index
  map {a b} e := cast (by rw [e.down, Quiver.Cycle.index_succ]) (α a.index)
  obj_injective _ _ hab := Quiver.Cycle.ext (hx hab)
  map_injective _ := Subsingleton.elim _ _

/-- **A quiver carrying an oriented cycle through distinct vertices has infinite representation
type**: the cycle embeds the cycle quiver, whose nilpotent representations are infinitely many
pairwise non-isomorphic indecomposables. The cycle is given by an injective family of `n + 2`
vertices and an arrow from each of them to the next, cyclically. -/
theorem not_isFiniteRepType_of_injective_of_nonempty_hom_succ {n : ℕ} (x : Fin (n + 2) → Q)
    (hx : Function.Injective x) (hα : ∀ i : Fin (n + 2), Nonempty (x i ⟶ x (i + 1))) :
    ¬ IsFiniteRepType.{u, v, w, u} k Q :=
  fun h ↦ not_isFiniteRepType_cycle k n
    (h.of_quiverEmbedding (cycleEmbedding hx fun i ↦ (hα i).some))

/-- **In a quiver of finite representation type an arrow admits no reverse arrow**: between
distinct vertices a pair of opposite arrows is an oriented cycle through two vertices, and at a
single vertex it is a loop. This is the `Ã₁` obstruction in the orientation the Kronecker quiver
does not provide, so with `TauCeti.IsFiniteRepType.isEmpty_hom_self` and
`TauCeti.IsFiniteRepType.subsingleton_hom` it says that the underlying graph of such a quiver is
simple. -/
theorem IsFiniteRepType.isEmpty_hom_of_hom (h : IsFiniteRepType.{u, v, w, u} k Q) {i j : Q}
    (α : i ⟶ j) : IsEmpty (j ⟶ i) := by
  by_cases hij : i = j
  · subst hij
    exact h.isEmpty_hom_self i
  refine ⟨fun β ↦ not_isFiniteRepType_of_injective_of_nonempty_hom_succ (n := 0) ![i, j] ?_ ?_ h⟩
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  · intro c
    fin_cases c
    · simpa using ⟨α⟩
    · simpa using ⟨β⟩

end TauCeti
