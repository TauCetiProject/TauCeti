/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Foam.WebExpr.Basic

/-!
# Word duals and closure of web expressions

The dual of a signed boundary word reverses its order and every strand direction.
`WebExpr.cupWord` and `WebExpr.capWord` join a word to its dual by nested, crossing-free
cups and caps. They are explicit raw expressions, with no categorical or skein relations
imposed. `WebExpr.closure f g` closes two parallel expressions by reflecting the second,
stacking, and joining the matching boundary ends. Thus open boundaries never serve as
closed webs merely by taking their disjoint union.

The vertex and extremum counts record precisely the generators introduced by closure.
For one identity strand on each side there are no vertices and exactly two extrema;
for empty boundaries no cups or caps are inserted. Incidence interpretation and passage
from these expressions to abstract closed webs are separate constructions.

The nested cups and caps follow H. Goertz, L. Marino and P. Wedrich,
*Monoidal 2-categories from foam evaluation*, arXiv:2602.11120v1, Construction 4.9.
-/

public section

namespace TauCeti

universe u

namespace WebBoundary

variable {Λ : Type u}

/-- Reverse the order of a boundary word and the direction of each strand. -/
def dual (s : WebBoundary Λ) : WebBoundary Λ :=
  List.map (fun x ↦ (x.1, !x.2)) s.reverse

@[simp] theorem dual_nil : dual ([] : WebBoundary Λ) = [] := (rfl)

@[simp] theorem dual_cons (a : Λ) (b : Bool) (s : WebBoundary Λ) :
    dual ((a, b) :: s) = dual s ++ [(a, !b)] := by simp [dual]

/-- Duality reverses the order of tensor factors in a word. -/
@[simp] theorem dual_append (s t : WebBoundary Λ) :
    dual (s ++ t) = dual t ++ dual s := by simp [dual]

/-- The dual word has the same number of ports. -/
@[simp] theorem length_dual (s : WebBoundary Λ) : (dual s).length = s.length := by
  simp [dual]

/-- Word duality is involutive, including the empty word. -/
@[simp] theorem dual_dual (s : WebBoundary Λ) : dual (dual s) = s := by
  simp [dual, List.map_reverse, List.map_map, Function.comp_def]

/-- Duality negates the signed label weight. -/
@[simp] theorem weight_dual [AddCommGroup Λ] (s : WebBoundary Λ) :
    weight (dual s) = -weight s := by
  induction s with
  | nil => simp
  | cons x s ih =>
    rcases x with ⟨a, b⟩
    cases b <;> simp [ih, add_comm]

end WebBoundary

namespace WebExpr

variable {Λ : Type u} [Add Λ] {s t : WebBoundary Λ}

/-- Nested cups join an arbitrary word to its reversed, oppositely directed dual. -/
def cupWord : (s : WebBoundary Λ) → WebExpr Λ [] (s ++ s.dual)
  | [] => (id []).cast rfl (by simp)
  | (a, b) :: s =>
    comp (cup a b) (((cupWord s).inContext [(a, b)] [(a, !b)]).cast
      (by simp) (by simp [List.append_assoc]))

/-- The empty word requires no cup. -/
theorem cupWord_nil : cupWord ([] : WebBoundary Λ) = (id []).cast rfl (by simp) := (rfl)

/-- The first strand gives the outer cup; the remaining cups lie between its two ends. -/
theorem cupWord_cons (a : Λ) (b : Bool) (s : WebBoundary Λ) :
    cupWord ((a, b) :: s) =
      comp (cup a b) (((cupWord s).inContext [(a, b)] [(a, !b)]).cast
        (by simp) (by simp [List.append_assoc])) := (rfl)

/-- Nested caps close a word followed by its dual. -/
def capWord (s : WebBoundary Λ) : WebExpr Λ (s ++ s.dual) [] := (cupWord s).flip

/-- Word caps are the reflection of the chosen word cups. -/
theorem capWord_def (s : WebBoundary Λ) : capWord s = (cupWord s).flip := (rfl)

/-- Word cups have no trivalent vertices. -/
@[simp] theorem vertexCount_cupWord (s : WebBoundary Λ) : (cupWord s).vertexCount = 0 := by
  induction s with
  | nil => simp [cupWord]
  | cons x s ih =>
    rcases x with ⟨a, b⟩
    simp [cupWord, ih]

/-- There is one cup for each strand of the word. -/
@[simp] theorem extremumCount_cupWord (s : WebBoundary Λ) :
    (cupWord s).extremumCount = s.length := by
  induction s with
  | nil => simp [cupWord]
  | cons x s ih =>
    rcases x with ⟨a, b⟩
    simp [cupWord, ih, Nat.add_comm]

@[simp] theorem vertexCount_capWord (s : WebBoundary Λ) : (capWord s).vertexCount = 0 := by
  simp [capWord]

@[simp] theorem extremumCount_capWord (s : WebBoundary Λ) :
    (capWord s).extremumCount = s.length := by simp [capWord]

/-- Close an endomorphism by nested cups, its tensor with straight dual strands, and nested caps.
This is a closed expression, rather than a scalar-valued evaluation. -/
def trace (f : WebExpr Λ s s) : WebExpr Λ [] [] :=
  comp (cupWord s) (comp (tensor f (id s.dual)) (capWord s))

/-- The raw expression underlying the closure of an endomorphism. -/
theorem trace_def (f : WebExpr Λ s s) :
    trace f = comp (cupWord s) (comp (tensor f (id s.dual)) (capWord s)) := (rfl)

/-- Closing an endomorphism adds no trivalent vertices. -/
@[simp] theorem vertexCount_trace (f : WebExpr Λ s s) : (trace f).vertexCount = f.vertexCount := by
  simp [trace]

/-- Closing an endomorphism adds one cup and one cap for each boundary strand. -/
@[simp] theorem extremumCount_trace (f : WebExpr Λ s s) :
    (trace f).extremumCount = f.extremumCount + 2 * s.length := by
  simp [trace]
  omega

/-- Close a pair of parallel expressions, keeping both diagrams and joining matching ends.
The second expression is reflected, giving a composable endomorphism of the source word. -/
def closure (f g : WebExpr Λ s t) : WebExpr Λ [] [] := trace (comp f g.flip)

/-- The raw closure uses reflection and the trace connectors, retaining both expressions. -/
theorem closure_def (f g : WebExpr Λ s t) : closure f g = trace (comp f g.flip) := (rfl)

/-- The closure retains all the vertices of both expressions. -/
@[simp] theorem vertexCount_closure (f g : WebExpr Λ s t) :
    (closure f g).vertexCount = f.vertexCount + g.vertexCount := by
  simp [closure]

/-- Only the source closure connectors add extrema; reflection retains the extrema of `g`. -/
@[simp] theorem extremumCount_closure (f g : WebExpr Λ s t) :
    (closure f g).extremumCount = f.extremumCount + g.extremumCount + 2 * s.length := by
  simp [closure]

end WebExpr

end TauCeti
