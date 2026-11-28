/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.CongrExclamation

/-!
# Typed expressions for labelled webs

`WebExpr s t` is a crossing-free expression with ordered signed boundaries `s` and `t`.
It retains identity strands, cups, caps, trivalent vertices, stacking and side-by-side
placement as syntax. No isotopy, monoidal interchange or skein relation is imposed.
In particular a circle, expressed as a cup followed by a cap, differs from the empty identity.

A boundary entry `(a, true)` points upwards, in the direction of composition, and
`(a, false)` points downwards. Labels have only an addition operation: the two smaller
labels at a vertex are ordered, and their sum is the third label. Zero and arbitrarily
large natural labels are permitted. Bending the uniformly oriented trivalent generators
with cups and caps gives the other boundary orientations.

The reflection `WebExpr.flip` exchanges source and target, cups and caps, and merges and
splits. Geometrically this is height reflection together with reversal of every arrow,
so the signs relative to the upward direction are unchanged. It reverses stacking and
preserves the order of tensor factors. Label transport preserves the entire expression tree.

The counting and conservation results constrain subsequent incidence interpretations:
trivalent vertices and extrema have prescribed effects on boundary length, and signed
label weight is conserved. The progressive fragment has only upward strands and vertices;
its intermediate boundaries are proved upward as well.

The generator conventions follow H. Goertz, L. Marino and P. Wedrich,
*Monoidal 2-categories from foam evaluation*, arXiv:2602.11120v1,
Definition 4.2 and Construction 4.6. This file constructs raw syntax only.
-/

public section

namespace TauCeti

universe u v w

/-- An ordered word of strand labels and directions; `true` means upward. -/
abbrev WebBoundary (Λ : Type u) := List (Λ × Bool)

namespace WebBoundary

variable {Λ : Type u} {Λ' : Type v}

/-- Every strand in the boundary points upwards. -/
def IsUpward (s : WebBoundary Λ) : Prop := ∀ x ∈ s, x.2 = true

@[simp] theorem isUpward_nil : IsUpward ([] : WebBoundary Λ) := by simp [IsUpward]

@[simp] theorem isUpward_cons (a : Λ) (b : Bool) (s : WebBoundary Λ) :
    IsUpward ((a, b) :: s) ↔ b = true ∧ IsUpward s := by simp [IsUpward]

@[simp] theorem isUpward_append (s t : WebBoundary Λ) :
    IsUpward (s ++ t) ↔ IsUpward s ∧ IsUpward t := by simp [IsUpward, or_imp, forall_and]

/-- The signed sum of labels. Downward strands contribute the negative of their label. -/
def weight [AddCommGroup Λ] (s : WebBoundary Λ) : Λ :=
  (List.map (fun x ↦ if x.2 then x.1 else -x.1) s).sum

@[simp] theorem weight_nil [AddCommGroup Λ] : weight ([] : WebBoundary Λ) = 0 := (rfl)

@[simp] theorem weight_cons [AddCommGroup Λ] (a : Λ) (b : Bool) (s : WebBoundary Λ) :
    weight ((a, b) :: s) = (if b then a else -a) + weight s := (rfl)

@[simp] theorem weight_append [AddCommGroup Λ] (s t : WebBoundary Λ) :
    weight (s ++ t) = weight s + weight t := by simp [weight]

end WebBoundary

/-- Raw, typed planar web expressions. `comp f g` means first `f`, then `g`.
The equation at a vertex uses the ordered pair of small labels; no commutativity or rank
bound is imposed. Only upward merges and splits are primitive; rotated versions are
expressed by bending with cups and caps. -/
inductive WebExpr (Λ : Type u) [Add Λ] : WebBoundary Λ → WebBoundary Λ → Type u
  /-- Straight strands. -/
  | id (s) : WebExpr Λ s s
  /-- A cup with either choice of orientation. -/
  | cup (a : Λ) (b : Bool) : WebExpr Λ [] [(a, b), (a, !b)]
  /-- A cap with either choice of orientation. -/
  | cap (a : Λ) (b : Bool) : WebExpr Λ [(a, b), (a, !b)] []
  /-- A trivalent vertex with two lower ends, whose labels sum in their stored order. -/
  | merge {a b c : Λ} (h : a + b = c) :
      WebExpr Λ [(a, true), (b, true)] [(c, true)]
  /-- A trivalent vertex with two upper ends, whose labels sum in their stored order. -/
  | split {a b c : Λ} (h : a + b = c) :
      WebExpr Λ [(c, true)] [(a, true), (b, true)]
  /-- Stack two expressions with exactly matching ordered signed boundaries. -/
  | comp {s t r} (f : WebExpr Λ s t) (g : WebExpr Λ t r) : WebExpr Λ s r
  /-- Place expressions side by side, with the left factor first in each boundary. -/
  | tensor {s t s' t'} (f : WebExpr Λ s t) (g : WebExpr Λ s' t') :
      WebExpr Λ (s ++ s') (t ++ t')

namespace WebExpr

variable {Λ : Type u} [Add Λ] {s t r : WebBoundary Λ}

/-- Reflect height and reverse strand orientations, exchanging source and target boundaries. -/
def flip : {s t : WebBoundary Λ} → WebExpr Λ s t → WebExpr Λ t s
  | _, _, .id s => .id s
  | _, _, .cup a b => .cap a b
  | _, _, .cap a b => .cup a b
  | _, _, .merge h => .split h
  | _, _, .split h => .merge h
  | _, _, .comp f g => .comp g.flip f.flip
  | _, _, .tensor f g => .tensor f.flip g.flip

@[simp] theorem flip_id (s : WebBoundary Λ) : (id s : WebExpr Λ s s).flip = id s := (rfl)
@[simp] theorem flip_cup (a : Λ) (b : Bool) : (cup a b).flip = cap a b := (rfl)
@[simp] theorem flip_cap (a : Λ) (b : Bool) : (cap a b).flip = cup a b := (rfl)
@[simp] theorem flip_merge {a b c : Λ} (h : a + b = c) :
    (merge h).flip = split h := (rfl)
@[simp] theorem flip_split {a b c : Λ} (h : a + b = c) :
    (split h).flip = merge h := (rfl)
@[simp] theorem flip_comp (f : WebExpr Λ s t) (g : WebExpr Λ t r) :
    (comp f g).flip = comp g.flip f.flip := (rfl)
@[simp] theorem flip_tensor {s' t'} (f : WebExpr Λ s t) (g : WebExpr Λ s' t') :
    (tensor f g).flip = tensor f.flip g.flip := (rfl)

/-- Reflection is involutive on raw expressions, before imposing any relations. -/
@[simp] theorem flip_flip (f : WebExpr Λ s t) : f.flip.flip = f := by
  induction f <;> simp_all

/-- Reflection is a bijection between the two raw expression types. -/
def flipEquiv (s t : WebBoundary Λ) : WebExpr Λ s t ≃ WebExpr Λ t s where
  toFun := flip
  invFun := flip
  left_inv := flip_flip
  right_inv := flip_flip

/-- Transport an expression along equalities of its two boundary words. -/
def cast {s' t' : WebBoundary Λ} (hs : s = s') (ht : t = t') (f : WebExpr Λ s t) :
    WebExpr Λ s' t' := hs ▸ ht ▸ f

@[simp] theorem cast_rfl (f : WebExpr Λ s t) : f.cast rfl rfl = f := (rfl)

@[simp] theorem cast_heq_iff {s' t' s'' t'' : WebBoundary Λ}
    (hs : s = s') (ht : t = t') (f : WebExpr Λ s t) (g : WebExpr Λ s'' t'') :
    HEq (f.cast hs ht) g ↔ HEq f g := by
  subst hs ht
  rfl

@[simp] theorem heq_cast_iff {s' t' s'' t'' : WebBoundary Λ}
    (hs : s = s') (ht : t = t') (f : WebExpr Λ s t) (g : WebExpr Λ s'' t'') :
    HEq g (f.cast hs ht) ↔ HEq g f := by
  subst hs ht
  rfl

@[simp] theorem flip_cast {s' t' : WebBoundary Λ} (hs : s = s') (ht : t = t')
    (f : WebExpr Λ s t) : (f.cast hs ht).flip = f.flip.cast ht hs := by
  subst hs ht
  rfl

/-- Change labels along an addition-preserving map. The ordered vertex equations are retained. -/
def map {Λ' : Type v} [Add Λ'] (f : Λ →ₙ+ Λ') :
    {s t : WebBoundary Λ} → WebExpr Λ s t →
      WebExpr Λ' (List.map (Prod.map f _root_.id) s) (List.map (Prod.map f _root_.id) t)
  | _, _, .id s => .id _
  | _, _, .cup a b => .cup (f a) b
  | _, _, .cap a b => .cap (f a) b
  | _, _, .merge h => .merge (by rw [← f.map_add, h])
  | _, _, .split h => .split (by rw [← f.map_add, h])
  | _, _, .comp g h => .comp (g.map f) (h.map f)
  | _, _, .tensor g h =>
    (tensor (g.map f) (h.map f)).cast List.map_append.symm List.map_append.symm

@[simp] theorem map_id {Λ' : Type v} [Add Λ'] (f : Λ →ₙ+ Λ') (s : WebBoundary Λ) :
    (id s : WebExpr Λ s s).map f = id (List.map (Prod.map f _root_.id) s) := (rfl)
@[simp] theorem map_cup {Λ' : Type v} [Add Λ'] (f : Λ →ₙ+ Λ') (a : Λ) (b : Bool) :
    (cup a b).map f = cup (f a) b := (rfl)
@[simp] theorem map_cap {Λ' : Type v} [Add Λ'] (f : Λ →ₙ+ Λ') (a : Λ) (b : Bool) :
    (cap a b).map f = cap (f a) b := (rfl)
@[simp] theorem map_comp {Λ' : Type v} [Add Λ'] (f : Λ →ₙ+ Λ')
    (g : WebExpr Λ s t) (h : WebExpr Λ t r) :
    (comp g h).map f = comp (g.map f) (h.map f) := (rfl)

@[simp] theorem map_merge {Λ' : Type v} [Add Λ'] (f : Λ →ₙ+ Λ')
    {a b c : Λ} (h : a + b = c) :
    (merge h).map f = merge ((f.map_add a b).symm.trans (congrArg f h)) := (rfl)

@[simp] theorem map_split {Λ' : Type v} [Add Λ'] (f : Λ →ₙ+ Λ')
    {a b c : Λ} (h : a + b = c) :
    (split h).map f = split ((f.map_add a b).symm.trans (congrArg f h)) := (rfl)

@[simp] theorem map_tensor {Λ' : Type v} [Add Λ'] (f : Λ →ₙ+ Λ')
    {s' t'} (g : WebExpr Λ s t) (h : WebExpr Λ s' t') :
    (tensor g h).map f =
      (tensor (g.map f) (h.map f)).cast List.map_append.symm List.map_append.symm := (rfl)

/-- Label transport commutes with reflection of expressions. -/
@[simp] theorem map_flip {Λ' : Type v} [Add Λ'] (f : Λ →ₙ+ Λ')
    (g : WebExpr Λ s t) : g.flip.map f = (g.map f).flip := by
  induction g <;> simp_all

/-- Relabelling by the identity preserves the expression, up to its boundary equalities. -/
theorem map_id_heq (g : WebExpr Λ s t) : HEq (g.map (AddHom.id Λ)) g := by
  induction g <;>
    simp_all only [AddHom.coe_id, Prod.map_id, map_id, map_cup, map_cap, map_merge,
      map_split, map_comp, map_tensor, cast, eqRec_heq_iff] <;>
    congr! 1 <;> exact List.map_id _

@[simp] theorem map_cast {Λ' : Type v} [Add Λ'] (f : Λ →ₙ+ Λ')
    {s' t' : WebBoundary Λ} (hs : s = s') (ht : t = t') (g : WebExpr Λ s t) :
    (g.cast hs ht).map f = (g.map f).cast
      (congrArg (List.map (Prod.map f _root_.id)) hs)
      (congrArg (List.map (Prod.map f _root_.id)) ht) := by
  subst hs ht
  rfl

/-- Consecutive changes of labels agree with their composite, up to boundary equalities. -/
theorem map_map_heq {Λ' : Type v} [Add Λ'] {Λ'' : Type w} [Add Λ'']
    (f : Λ →ₙ+ Λ') (g : Λ' →ₙ+ Λ'') (h : WebExpr Λ s t) :
    HEq ((h.map f).map g) (h.map (g.comp f)) := by
  induction h <;>
    simp_all only [map_id, map_cup, map_cap, map_merge, map_split, map_comp, map_tensor,
      map_cast, cast_heq_iff, heq_cast_iff, AddHom.comp_apply] <;> congr! 1 <;>
    simp_all only [List.map_map, Function.comp_def, Prod.map_map] <;> rfl

/-- Number of trivalent vertices, counting their occurrences in the expression tree. -/
def vertexCount : {s t : WebBoundary Λ} → WebExpr Λ s t → ℕ
  | _, _, .id _ | _, _, .cup _ _ | _, _, .cap _ _ => 0
  | _, _, .merge _ | _, _, .split _ => 1
  | _, _, .comp f g | _, _, .tensor f g => f.vertexCount + g.vertexCount

/-- Number of local extrema, counting cups and caps. -/
def extremumCount : {s t : WebBoundary Λ} → WebExpr Λ s t → ℕ
  | _, _, .id _ | _, _, .merge _ | _, _, .split _ => 0
  | _, _, .cup _ _ | _, _, .cap _ _ => 1
  | _, _, .comp f g | _, _, .tensor f g => f.extremumCount + g.extremumCount

@[simp] theorem vertexCount_id (s : WebBoundary Λ) :
    (id s : WebExpr Λ _ _).vertexCount = 0 := (rfl)

@[simp] theorem vertexCount_cup (a : Λ) (b : Bool) :
    (cup a b : WebExpr Λ _ _).vertexCount = 0 := (rfl)

@[simp] theorem vertexCount_cap (a : Λ) (b : Bool) :
    (cap a b : WebExpr Λ _ _).vertexCount = 0 := (rfl)

@[simp] theorem vertexCount_merge {a b c : Λ} (h : a + b = c) :
    (merge h : WebExpr Λ _ _).vertexCount = 1 := (rfl)

@[simp] theorem vertexCount_split {a b c : Λ} (h : a + b = c) :
    (split h : WebExpr Λ _ _).vertexCount = 1 := (rfl)

@[simp] theorem vertexCount_comp (f : WebExpr Λ s t) (g : WebExpr Λ t r) :
    (comp f g).vertexCount = f.vertexCount + g.vertexCount := (rfl)

@[simp] theorem vertexCount_tensor {s' t'} (f : WebExpr Λ s t) (g : WebExpr Λ s' t') :
    (tensor f g).vertexCount = f.vertexCount + g.vertexCount := (rfl)

@[simp] theorem extremumCount_id (s : WebBoundary Λ) :
    (id s : WebExpr Λ _ _).extremumCount = 0 := (rfl)

@[simp] theorem extremumCount_cup (a : Λ) (b : Bool) :
    (cup a b : WebExpr Λ _ _).extremumCount = 1 := (rfl)

@[simp] theorem extremumCount_cap (a : Λ) (b : Bool) :
    (cap a b : WebExpr Λ _ _).extremumCount = 1 := (rfl)

@[simp] theorem extremumCount_merge {a b c : Λ} (h : a + b = c) :
    (merge h : WebExpr Λ _ _).extremumCount = 0 := (rfl)

@[simp] theorem extremumCount_split {a b c : Λ} (h : a + b = c) :
    (split h : WebExpr Λ _ _).extremumCount = 0 := (rfl)

@[simp] theorem extremumCount_comp (f : WebExpr Λ s t) (g : WebExpr Λ t r) :
    (comp f g).extremumCount = f.extremumCount + g.extremumCount := (rfl)

@[simp] theorem extremumCount_tensor {s' t'} (f : WebExpr Λ s t) (g : WebExpr Λ s' t') :
    (tensor f g).extremumCount = f.extremumCount + g.extremumCount := (rfl)

/-- The signed change in the number of boundary strands. Merges contribute `-1`, splits `1`,
cups `2`, and caps `-2`. -/
def boundaryChange : {s t : WebBoundary Λ} → WebExpr Λ s t → ℤ
  | _, _, .id _ => 0
  | _, _, .cup _ _ => 2
  | _, _, .cap _ _ => -2
  | _, _, .merge _ => -1
  | _, _, .split _ => 1
  | _, _, .comp f g | _, _, .tensor f g => f.boundaryChange + g.boundaryChange

@[simp] theorem vertexCount_cast {s' t' : WebBoundary Λ} (hs : s = s') (ht : t = t')
    (f : WebExpr Λ s t) : (f.cast hs ht).vertexCount = f.vertexCount := by
  subst hs ht
  rfl

@[simp] theorem extremumCount_cast {s' t' : WebBoundary Λ} (hs : s = s') (ht : t = t')
    (f : WebExpr Λ s t) : (f.cast hs ht).extremumCount = f.extremumCount := by
  subst hs ht
  rfl

/-- Changing labels preserves the number of trivalent vertex occurrences. -/
@[simp] theorem vertexCount_map {Λ' : Type v} [Add Λ'] (f : Λ →ₙ+ Λ')
    (g : WebExpr Λ s t) : (g.map f).vertexCount = g.vertexCount := by
  induction g <;> simp_all

/-- Changing labels preserves cups and caps, even when a label maps to zero. -/
@[simp] theorem extremumCount_map {Λ' : Type v} [Add Λ'] (f : Λ →ₙ+ Λ')
    (g : WebExpr Λ s t) : (g.map f).extremumCount = g.extremumCount := by
  induction g <;> simp_all

/-- Counting the elementary events recovers the difference of boundary lengths. -/
theorem boundaryChange_eq (f : WebExpr Λ s t) :
    f.boundaryChange = (t.length : ℤ) - s.length := by
  induction f <;> simp_all [boundaryChange, List.length_append]; omega

/-- The total number of trivalent vertices has the parity of the number of boundary ports. -/
theorem vertexCount_add_length_mod_two (f : WebExpr Λ s t) :
    (f.vertexCount + s.length + t.length) % 2 = 0 := by
  induction f <;> simp_all [List.length_append] <;> omega

@[simp] theorem vertexCount_flip (f : WebExpr Λ s t) : f.flip.vertexCount = f.vertexCount := by
  induction f <;> simp_all [Nat.add_comm]

@[simp] theorem extremumCount_flip (f : WebExpr Λ s t) :
    f.flip.extremumCount = f.extremumCount := by
  induction f <;> simp_all [Nat.add_comm]

@[simp] theorem boundaryChange_flip (f : WebExpr Λ s t) :
    f.flip.boundaryChange = -f.boundaryChange := by
  rw [boundaryChange_eq, boundaryChange_eq]
  omega

/-- Raw web expressions conserve the signed boundary label weight. -/
theorem weight_eq {Λ : Type u} [AddCommGroup Λ] {s t : WebBoundary Λ}
    (f : WebExpr Λ s t) :
    WebBoundary.weight s = WebBoundary.weight t := by
  induction f with
  | id => rfl
  | cup a b => cases b <;> simp
  | cap a b => cases b <;> simp
  | merge h => simp [← h]
  | split h => simp [← h]
  | comp _ _ hf hg => exact hf.trans hg
  | tensor _ _ hf hg => simp [hf, hg]

/-- A vertex-free circle represented as a cup followed by a cap, retaining its orientation. -/
def circle (a : Λ) (b : Bool) : WebExpr Λ [] [] := comp (cup a b) (cap a b)

/-- A circle is the indicated cup followed by the cap with matching signed ends. -/
theorem circle_def (a : Λ) (b : Bool) : circle a b = comp (cup a b) (cap a b) := (rfl)

@[simp] theorem vertexCount_circle (a : Λ) (b : Bool) : (circle a b).vertexCount = 0 := (rfl)
@[simp] theorem extremumCount_circle (a : Λ) (b : Bool) : (circle a b).extremumCount = 2 := (rfl)

/-- A closed circle is different from the empty identity even before evaluation. -/
theorem circle_ne_id (a : Λ) (b : Bool) : circle a b ≠ id [] := by
  intro h
  have := congrArg extremumCount h
  simp at this

/-- A context of straight strands to the left and right of an expression. -/
def inContext (left right : WebBoundary Λ) (f : WebExpr Λ s t) :
    WebExpr Λ ((left ++ s) ++ right) ((left ++ t) ++ right) :=
  tensor (tensor (id left) f) (id right)

/-- Context insertion retains the explicit left and right identity factors. -/
theorem inContext_def (left right : WebBoundary Λ) (f : WebExpr Λ s t) :
    f.inContext left right = tensor (tensor (id left) f) (id right) := (rfl)

@[simp] theorem vertexCount_inContext (left right : WebBoundary Λ) (f : WebExpr Λ s t) :
    (f.inContext left right).vertexCount = f.vertexCount := by simp [inContext]

@[simp] theorem extremumCount_inContext (left right : WebBoundary Λ) (f : WebExpr Λ s t) :
    (f.inContext left right).extremumCount = f.extremumCount := by simp [inContext]

/-- The progressive fragment retains only upward strands and vertices, with no cups or caps.
Each intermediate expression, rather than only its external boundary, must be progressive. -/
inductive IsProgressive : {s t : WebBoundary Λ} → WebExpr Λ s t → Prop
  | id {s : WebBoundary Λ} (h : WebBoundary.IsUpward s) : IsProgressive (.id s)
  | merge {a b c : Λ} (h : a + b = c) : IsProgressive (.merge h)
  | split {a b c : Λ} (h : a + b = c) : IsProgressive (.split h)
  | comp {s t r : WebBoundary Λ} {f : WebExpr Λ s t} {g : WebExpr Λ t r}
      (hf : IsProgressive f) (hg : IsProgressive g) : IsProgressive (.comp f g)
  | tensor {s t s' t' : WebBoundary Λ} {f : WebExpr Λ s t} {g : WebExpr Λ s' t'}
      (hf : IsProgressive f) (hg : IsProgressive g) : IsProgressive (.tensor f g)

/-- A progressive expression has upward source and target words. -/
theorem IsProgressive.isUpward {f : WebExpr Λ s t} (h : f.IsProgressive) :
    WebBoundary.IsUpward s ∧ WebBoundary.IsUpward t := by
  induction h with
  | id h => exact ⟨h, h⟩
  | merge => simp
  | split => simp
  | comp _ _ ihf ihg => exact ⟨ihf.1, ihg.2⟩
  | tensor _ _ ihf ihg => simp_all

/-- Progressive expressions contain no local extrema. -/
theorem IsProgressive.extremumCount_eq_zero {f : WebExpr Λ s t} (h : f.IsProgressive) :
    f.extremumCount = 0 := by
  induction h <;> simp_all

@[simp] theorem not_isProgressive_cup (a : Λ) (b : Bool) : ¬(cup a b).IsProgressive := by
  intro h
  have := h.extremumCount_eq_zero
  simp at this

@[simp] theorem not_isProgressive_cap (a : Λ) (b : Bool) : ¬(cap a b).IsProgressive := by
  intro h
  have := h.extremumCount_eq_zero
  simp at this

@[simp] theorem not_isProgressive_circle (a : Λ) (b : Bool) : ¬(circle a b).IsProgressive := by
  intro h
  simpa using h.extremumCount_eq_zero

/-- Reflection preserves progressiveness, including its intermediate-boundary restriction. -/
theorem IsProgressive.flip {f : WebExpr Λ s t} (h : f.IsProgressive) : f.flip.IsProgressive := by
  induction h with
  | id h => exact .id h
  | merge h => exact .split h
  | split h => exact .merge h
  | comp _ _ ihf ihg => exact .comp ihg ihf
  | tensor _ _ ihf ihg => exact .tensor ihf ihg

/-- Progressiveness can be checked by the source signs and the absence of cups and caps.
The upward-only vertex generators then force every intermediate boundary to be upward. -/
theorem isProgressive_iff (f : WebExpr Λ s t) :
    f.IsProgressive ↔ WebBoundary.IsUpward s ∧ f.extremumCount = 0 := by
  refine ⟨fun h ↦ ⟨h.isUpward.1, h.extremumCount_eq_zero⟩, ?_⟩
  induction f with
  | id s => exact fun h ↦ .id h.1
  | cup a b => simp
  | cap a b => simp
  | merge h => exact fun _ ↦ .merge h
  | split h => exact fun _ ↦ .split h
  | comp f g ihf ihg =>
    rintro ⟨hs, he⟩
    obtain ⟨hf, hg⟩ := Nat.add_eq_zero_iff.mp he
    have hfp := ihf ⟨hs, hf⟩
    exact .comp hfp (ihg ⟨hfp.isUpward.2, hg⟩)
  | tensor f g ihf ihg =>
    rintro ⟨hs, he⟩
    obtain ⟨hsl, hsr⟩ := (WebBoundary.isUpward_append _ _).mp hs
    obtain ⟨hf, hg⟩ := Nat.add_eq_zero_iff.mp he
    exact .tensor (ihf ⟨hsl, hf⟩) (ihg ⟨hsr, hg⟩)

@[simp] theorem isProgressive_flip_iff (f : WebExpr Λ s t) :
    f.flip.IsProgressive ↔ f.IsProgressive :=
  ⟨fun h ↦ by simpa using h.flip, IsProgressive.flip⟩

/-- Label transport neither creates nor removes progressive expressions. -/
@[simp] theorem isProgressive_map_iff {Λ' : Type v} [Add Λ'] (f : Λ →ₙ+ Λ')
    (g : WebExpr Λ s t) : (g.map f).IsProgressive ↔ g.IsProgressive := by
  simp [isProgressive_iff, WebBoundary.IsUpward]

/-- Progressive expressions conserve the ordinary sum of labels, including natural labels.
No commutativity is needed: tensor factors and the small labels at vertices remain ordered. -/
theorem IsProgressive.sum_eq {Λ : Type u} [AddMonoid Λ] {s t : WebBoundary Λ}
    {f : WebExpr Λ s t} (h : f.IsProgressive) :
    (List.map Prod.fst s).sum = (List.map Prod.fst t).sum := by
  induction h with
  | id => rfl
  | merge h => simp [h]
  | split h => simp [h]
  | comp _ _ ihf ihg => exact ihf.trans ihg
  | tensor _ _ ihf ihg => simp [ihf, ihg]

end WebExpr

end TauCeti
