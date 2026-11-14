/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Basic
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Logic.Relation

/-!
# Lists of involutions

Left folds of involutions describe finite sequences of reversible operations. Reversing a
list undoes its action; repeated adjacent indices cancel. The resulting bijections and
reachability relation describe the orbits of such operations, while predicates preserved
by each step are invariant along these orbits.

## Main results

* `TauCeti.predicate_foldl_iff_of_involutive`: a predicate preserved by involutive steps is
  invariant along a list of steps.
* `TauCeti.foldl_reverse_foldl_of_involutive`: reverse a word of involutions to undo its action.
-/

public section

namespace TauCeti

/-- Applying a list of involutions in reverse order undoes its left-fold action. No relations
between distinct indices, decidable equality, or finiteness of the index type are needed. -/
theorem foldl_reverse_foldl_of_involutive {I J : Type*} (f : I → J → I)
    (hf : ∀ j, Function.Involutive (fun a ↦ f a j)) (l : List J) (a : I) :
    l.reverse.foldl f (l.foldl f a) = a := by
  induction l generalizing a with
  | nil => rfl
  | cons j l ih =>
    simpa only [List.foldl_cons, List.reverse_cons, List.foldl_append, List.foldl_nil,
      ih] using hf j a

/-- Reversing the initial fold also gives the inverse law in the other order. -/
theorem foldl_foldl_reverse_of_involutive {I J : Type*} (f : I → J → I)
    (hf : ∀ j, Function.Involutive (fun a ↦ f a j)) (l : List J) (a : I) :
    l.foldl f (l.reverse.foldl f a) = a := by
  simpa only [List.reverse_reverse] using foldl_reverse_foldl_of_involutive f hf l.reverse a

/-- Two adjacent copies of an involutive step cancel inside any list. Only that step
must be involutive; no condition is imposed on the other list elements. -/
theorem foldl_append_cons_cons_of_involutive {I J : Type*} (f : I → J → I) {j : J}
    (hf : Function.Involutive (fun a ↦ f a j)) (u v : List J) (a : I) :
    (u ++ j :: j :: v).foldl f a = (u ++ v).foldl f a := by
  simp only [List.foldl_append, List.foldl_cons]
  exact congrArg (fun x ↦ v.foldl f x) (hf (u.foldl f a))

/-- A list of involutions acts bijectively, with inverse given by its reversal. -/
def foldlEquiv {I J : Type*} (f : I → J → I)
    (hf : ∀ j, Function.Involutive (fun a ↦ f a j)) (l : List J) : I ≃ I where
  toFun a := l.foldl f a
  invFun a := l.reverse.foldl f a
  left_inv := foldl_reverse_foldl_of_involutive f hf l
  right_inv := foldl_foldl_reverse_of_involutive f hf l

@[simp]
theorem foldlEquiv_apply {I J : Type*} (f : I → J → I)
    (hf : ∀ j, Function.Involutive (fun a ↦ f a j)) (l : List J) (a : I) :
    foldlEquiv f hf l a = l.foldl f a := by rfl

@[simp]
theorem foldlEquiv_symm {I J : Type*} (f : I → J → I)
    (hf : ∀ j, Function.Involutive (fun a ↦ f a j)) (l : List J) :
    (foldlEquiv f hf l).symm = foldlEquiv f hf l.reverse := by
  ext a
  rfl

@[simp]
theorem foldlEquiv_nil {I J : Type*} (f : I → J → I)
    (hf : ∀ j, Function.Involutive (fun a ↦ f a j)) :
    foldlEquiv f hf [] = Equiv.refl I := by
  ext a
  rfl

/-- Concatenation acts by composition of the corresponding fold bijections. -/
theorem foldlEquiv_append {I J : Type*} (f : I → J → I)
    (hf : ∀ j, Function.Involutive (fun a ↦ f a j)) (u v : List J) :
    foldlEquiv f hf (u ++ v) = (foldlEquiv f hf u).trans (foldlEquiv f hf v) := by
  ext a
  exact List.foldl_append

/-- Move an action by a list of involutions across an equality using the reversed list. -/
theorem foldl_eq_iff_of_involutive {I J : Type*} (f : I → J → I)
    (hf : ∀ j, Function.Involutive (fun a ↦ f a j)) (l : List J) (a b : I) :
    l.foldl f a = b ↔ a = l.reverse.foldl f b := by
  simpa only [foldlEquiv_symm, foldlEquiv_apply] using
    ((foldlEquiv f hf l).eq_symm_apply (x := b) (y := a)).symm

/-- A left fold of involutions cancels from both sides of an equality. -/
@[simp]
theorem foldl_eq_foldl_iff_of_involutive {I J : Type*} (f : I → J → I)
    (hf : ∀ j, Function.Involutive (fun a ↦ f a j)) (l : List J) (a b : I) :
    l.foldl f a = l.foldl f b ↔ a = b := by
  simpa only [foldlEquiv_apply] using (foldlEquiv f hf l).apply_eq_iff_eq (x := a) (y := b)

/-- `FoldReachable f a b` means that a finite list of steps of `f` takes `a` to `b`. -/
def FoldReachable {I J : Type*} (f : I → J → I) (a b : I) : Prop :=
  ∃ w : List J, w.foldl f a = b

/-- Eliminate fold reachability into its witnessing list. -/
theorem foldReachable_def {I J : Type*} {f : I → J → I} {a b : I} :
    FoldReachable f a b ↔ ∃ w : List J, w.foldl f a = b := Iff.rfl

/-- Every fold gives a reachable value, with no condition on the steps. -/
theorem foldReachable_foldl {I J : Type*} (f : I → J → I) (a : I) (w : List J) :
    FoldReachable f a (w.foldl f a) := ⟨w, rfl⟩

/-- A single step gives a reachable value, with no condition on the steps. -/
theorem foldReachable_apply {I J : Type*} (f : I → J → I) (a : I) (j : J) :
    FoldReachable f a (f a j) := ⟨[j], rfl⟩

namespace FoldReachable

variable {I J I' J' : Type*} {f : I → J → I} {f' : I' → J' → I'}

/-- Fold reachability is reflexive, without any condition on the steps. -/
@[refl, simp]
theorem refl (a : I) : FoldReachable f a a := ⟨[], rfl⟩

/-- Fold reachability is transitive, without any condition on the steps. -/
@[trans]
theorem trans {a b c : I} (h : FoldReachable f a b) (h' : FoldReachable f b c) :
    FoldReachable f a c := by
  obtain ⟨u, rfl⟩ := h
  obtain ⟨v, rfl⟩ := h'
  exact ⟨u ++ v, List.foldl_append⟩

/-- Involutive steps make fold reachability symmetric. -/
theorem symm (hf : ∀ j, Function.Involutive (fun a ↦ f a j)) {a b : I}
    (h : FoldReachable f a b) : FoldReachable f b a := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨w.reverse, foldl_reverse_foldl_of_involutive f hf w a⟩

/-- Involutive steps allow interchanging both endpoints of reachability. -/
theorem comm (hf : ∀ j, Function.Involutive (fun a ↦ f a j)) (a b : I) :
    FoldReachable f a b ↔ FoldReachable f b a := ⟨symm hf, symm hf⟩

/-- Involutive steps make fold reachability an equivalence relation. -/
theorem equivalence (hf : ∀ j, Function.Involutive (fun a ↦ f a j)) :
    Equivalence (FoldReachable f) := ⟨refl, symm hf, trans⟩

/-- Reachable initial values have the same reachable class. -/
theorem congr_left (hf : ∀ j, Function.Involutive (fun a ↦ f a j)) {a b c : I}
    (h : FoldReachable f a b) : FoldReachable f b c ↔ FoldReachable f a c :=
  ⟨h.trans, (h.symm hf).trans⟩

/-- Reachable target values can replace one another in a reachability statement. -/
theorem congr_right (hf : ∀ j, Function.Involutive (fun a ↦ f a j)) {a b c : I}
    (h : FoldReachable f a b) : FoldReachable f c b ↔ FoldReachable f c a :=
  ⟨fun h' ↦ h'.trans (h.symm hf), fun h' ↦ h'.trans h⟩

/-- Equivariant maps transport fold reachability, without injectivity assumptions. -/
theorem map {a b : I} (h : FoldReachable f a b) (g : I → I') (m : J → J')
    (hgm : ∀ a j, g (f a j) = f' (g a) (m j)) : FoldReachable f' (g a) (g b) := by
  obtain ⟨w, rfl⟩ := h
  refine ⟨w.map m, ?_⟩
  rw [List.foldl_map]
  exact List.foldl_hom g (fun a j ↦ (hgm a j).symm)

/-- An injective state map and a surjective step map preserve and reflect reachability
when they intertwine every step. No reversibility or surjectivity of the state map is needed. -/
theorem map_iff {g : I → I'} {m : J → J'} (hg : Function.Injective g)
    (hm : Function.Surjective m) (hgm : ∀ a j, g (f a j) = f' (g a) (m j)) (a b : I) :
    FoldReachable f' (g a) (g b) ↔ FoldReachable f a b := by
  constructor
  · rintro ⟨w', hw'⟩
    obtain ⟨w, rfl⟩ := hm.list_map w'
    refine ⟨w, hg ?_⟩
    have hfold : (w.map m).foldl f' (g a) = g (w.foldl f a) := by
      rw [List.foldl_map]
      exact List.foldl_hom g (fun a j ↦ (hgm a j).symm)
    rwa [← hfold]
  · intro h
    exact h.map g m hgm

/-- Equivariant bijections preserve and reflect fold reachability. -/
theorem equiv_iff (g : I ≃ I') (m : J ≃ J')
    (hgm : ∀ a j, g (f a j) = f' (g a) (m j)) (a b : I) :
    FoldReachable f' (g a) (g b) ↔ FoldReachable f a b :=
  map_iff g.injective m.surjective hgm a b

end FoldReachable

/-- Fold reachability is the reflexive transitive closure of the relation of taking one step.
This characterization does not require the steps to be involutions. -/
theorem foldReachable_iff_reflTransGen {I J : Type*} {f : I → J → I} {a b : I} :
    FoldReachable f a b ↔ Relation.ReflTransGen (fun x y ↦ ∃ j, f x j = y) a b := by
  constructor
  · rintro ⟨w, rfl⟩
    induction w generalizing a with
    | nil => exact .refl
    | cons j w ih =>
      exact (Relation.ReflTransGen.single ⟨j, rfl⟩).trans (ih (a := f a j))
  · intro h
    induction h with
    | refl => exact FoldReachable.refl a
    | @tail x y _hax hxy ih =>
      obtain ⟨j, rfl⟩ := hxy
      exact ih.trans (foldReachable_apply f x j)

namespace FoldReachable

/-- Prove a property on the set of states reachable from an initial state, using preservation
only at states already in that set. No reversibility of the steps is needed. -/
@[elab_as_elim]
theorem induction {I J : Type*} {f : I → J → I} {a b : I} {motive : I → Prop}
    (h : FoldReachable f a b) (ha : motive a)
    (hstep : ∀ x j, FoldReachable f a x → motive x → motive (f x j)) : motive b := by
  have hind {c : I}
      (hpath : Relation.ReflTransGen (fun x y ↦ ∃ j, f x j = y) a c) : motive c := by
    induction hpath with
    | refl => exact ha
    | @tail x y hax hxy ih =>
      obtain ⟨j, rfl⟩ := hxy
      exact hstep x j (foldReachable_iff_reflTransGen.mpr hax) ih
  exact hind (foldReachable_iff_reflTransGen.mp h)

end FoldReachable

/-- A word of involutive steps on the initial value preserves its reachable class. -/
@[simp]
theorem foldReachable_foldl_left_iff {I J : Type*} (f : I → J → I)
    (hf : ∀ j, Function.Involutive (fun a ↦ f a j)) (a b : I) (w : List J) :
    FoldReachable f (w.foldl f a) b ↔ FoldReachable f a b :=
  (foldReachable_foldl f a w).congr_left hf

/-- A word of involutive steps on the target value preserves reachability. -/
@[simp]
theorem foldReachable_foldl_right_iff {I J : Type*} (f : I → J → I)
    (hf : ∀ j, Function.Involutive (fun a ↦ f a j)) (a b : I) (w : List J) :
    FoldReachable f a (w.foldl f b) ↔ FoldReachable f a b :=
  (foldReachable_foldl f b w).congr_right hf

/-- An involutive step on the initial value preserves its reachable class, even when other
steps are not involutions. -/
@[simp]
theorem foldReachable_apply_left_iff {I J : Type*} (f : I → J → I) {j : J}
    (hf : Function.Involutive (fun a ↦ f a j)) (a b : I) :
    FoldReachable f (f a j) b ↔ FoldReachable f a b := by
  have hback : FoldReachable f (f a j) a := by
    simpa only [hf a] using foldReachable_apply f (f a j) j
  exact ⟨(foldReachable_apply f a j).trans, hback.trans⟩

/-- An involutive step on the target value preserves reachability, even when other steps are
not involutions. -/
@[simp]
theorem foldReachable_apply_right_iff {I J : Type*} (f : I → J → I) {j : J}
    (hf : Function.Involutive (fun a ↦ f a j)) (a b : I) :
    FoldReachable f a (f b j) ↔ FoldReachable f a b := by
  have hback : FoldReachable f (f b j) b := by
    simpa only [hf b] using foldReachable_apply f (f b j) j
  exact ⟨fun h ↦ h.trans hback, fun h ↦ h.trans (foldReachable_apply f b j)⟩

/-- A predicate preserved by a family of involutions is invariant under every list of those
involutions. -/
theorem predicate_foldl_iff_of_involutive {I J : Type*} (p : I → Prop)
    (reflect : J → I → I) (hinvolutive : ∀ j, Function.Involutive (reflect j))
    (hreflect : ∀ a j, p a → p (reflect j a)) (l : List J) (a : I) :
    p (l.foldl (fun b j ↦ reflect j b) a) ↔ p a := by
  induction l generalizing a with
  | nil => rfl
  | cons j l ih =>
    rw [List.foldl_cons, ih]
    exact ⟨fun h ↦ hinvolutive j a ▸ hreflect _ j h, hreflect a j⟩

end TauCeti
