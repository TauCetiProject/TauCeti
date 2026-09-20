/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Reflection.Admissible
public import TauCeti.RepresentationTheory.Quiver.Reflection.Coxeter
public import TauCeti.RepresentationTheory.Quiver.Reflection.Source.Indecomposable

/-!
# Composites of source reflection functors

A list is **source-admissible** when each vertex is a source after reflecting at the preceding
vertices. Source reflection functors therefore compose along such a list. This file constructs
that composite and proves that it preserves finite-dimensional indecomposables whenever the
successive reflected dimension vectors stay nonnegative.

The reverse of a sink-admissible list is source-admissible for the quiver obtained after the sink
reflections. This is the direction needed to reconstruct a quiver representation from a simple
representation in the reflection induction for Gabriel's theorem.

## Main definitions

* `TauCeti.Quiver.IsSourceAdmissible`: each entry of a list is a source after its predecessors
  have been reflected.
* `TauCeti.sourceReflectionFunctorList`: the composite of source reflection functors along a
  source-admissible list.

## Main results

* `TauCeti.Quiver.IsSinkAdmissible.reverse`: reversing a sink-admissible list gives a
  source-admissible list for the fully reflected quiver.
* `TauCeti.indecomposable_and_dimVector_sourceReflectionFunctorList`: if all successive reflected
  dimension vectors are nonnegative, the composite preserves indecomposability and realizes the
  corresponding product of simple reflections on dimension vectors.

## Implementation notes

The functor and its finite-dimensionality theorem are universe-polymorphic. The indecomposability
theorem uses the existing vertex-simple comparison API, whose field, vertex, arrow, and auxiliary
module universes coincide, and therefore carries the same restriction.

## References

See Bernstein--Gelfand--Ponomarev, *Coxeter functors and Gabriel's theorem*, and Derksen--Weyman,
*An Introduction to Quiver Representations*, Ch. 2.
-/

public section

namespace TauCeti

open CategoryTheory
open _root_.TauCeti.Quiver

universe u v w x

namespace Quiver

variable {V : Type v}

/-! ### Source-admissible lists -/

/-- A list of vertices is **source-admissible** when each entry is a source in the quiver obtained
by reflecting at all preceding entries. -/
def IsSourceAdmissible (q : _root_.Quiver.{w} V) (l : List V) : Prop :=
  ∀ t u : List V, ∀ i : V, l = t ++ i :: u → @IsSource V (reflectList q t) i

/-- The defining condition for a source-admissible list. -/
theorem isSourceAdmissible_def (q : _root_.Quiver.{w} V) (l : List V) :
    IsSourceAdmissible q l ↔
      ∀ t u : List V, ∀ i : V, l = t ++ i :: u → @IsSource V (reflectList q t) i :=
  Iff.rfl

@[simp]
theorem isSourceAdmissible_nil (q : _root_.Quiver.{w} V) : IsSourceAdmissible q [] := by
  rw [isSourceAdmissible_def]
  intro t u i h
  simp at h

/-- A list is source-admissible exactly when its head is a source and its tail is
source-admissible after reflecting at the head. -/
@[simp]
theorem isSourceAdmissible_cons {q : _root_.Quiver.{w} V} {i : V} {l : List V} :
    IsSourceAdmissible q (i :: l) ↔
      @IsSource V q i ∧ IsSourceAdmissible (reflectAt q i) l := by
  simp only [isSourceAdmissible_def]
  constructor
  · intro h
    refine ⟨?_, fun t u j ht ↦ ?_⟩
    · have := h [] l i rfl
      rwa [reflectList_nil] at this
    · have := h (i :: t) u j (by rw [List.cons_append, ht])
      rwa [reflectList_cons] at this
  · rintro ⟨hi, h⟩ t u j hj
    rcases t with _ | ⟨a, t⟩
    · rw [List.nil_append, List.cons.injEq] at hj
      rw [reflectList_nil, ← hj.1]
      exact hi
    · rw [List.cons_append, List.cons.injEq] at hj
      rw [← hj.1, reflectList_cons]
      exact h t u j hj.2

/-- Reflecting along a list and then along its reverse returns the original quiver structure. -/
@[simp]
theorem reflectList_reverse (q : _root_.Quiver.{w} V) :
    ∀ l : List V, reflectList (reflectList q l) l.reverse = q
  | [] => by simp
  | i :: l => by
      rw [reflectList_cons, List.reverse_cons, reflectList_append, reflectList_reverse,
        reflectList_cons, reflectList_nil, reflectAt_reflectAt]

/-- Appending a final source to a source-admissible list preserves source-admissibility. -/
theorem IsSourceAdmissible.append_singleton {q : _root_.Quiver.{w} V} {l : List V} {i : V}
    (hl : IsSourceAdmissible q l) (hi : @IsSource V (reflectList q l) i) :
    IsSourceAdmissible q (l ++ [i]) := by
  induction l generalizing q with
  | nil =>
      rw [List.nil_append, isSourceAdmissible_cons]
      rw [reflectList_nil] at hi
      exact ⟨hi, isSourceAdmissible_nil _⟩
  | cons j l ih =>
      rw [List.cons_append, isSourceAdmissible_cons]
      rw [isSourceAdmissible_cons] at hl
      rw [reflectList_cons] at hi
      exact ⟨hl.1, ih hl.2 hi⟩

/-- **A reversed sink-admissible list is source-admissible.** After all sink reflections have
been performed, undoing them in reverse order always reflects at a source. -/
theorem IsSinkAdmissible.reverse {q : _root_.Quiver.{w} V} {l : List V}
    (hl : IsSinkAdmissible q l) : IsSourceAdmissible (reflectList q l) l.reverse := by
  induction l generalizing q with
  | nil => simp
  | cons i l ih =>
      obtain ⟨hi, hl⟩ := isSinkAdmissible_cons.mp hl
      rw [reflectList_cons, List.reverse_cons]
      refine (ih hl).append_singleton ?_
      rw [reflectList_reverse]
      exact hi.isSource_reflect

end Quiver

/-! ### The composite along a source-admissible list -/

/-- **The composite of the source reflection functors along a source-admissible list.** It sends
representations of `q` to representations of the quiver obtained by reflecting successively at
the entries of `l`. -/
noncomputable def sourceReflectionFunctorList (k : Type u) {V : Type v}
    [fld : Field k] [fV : Fintype V] :
    ∀ (l : List V) (q : _root_.Quiver.{w} V)
      (_hq : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b)),
      Quiver.IsSourceAdmissible q l →
      (@QuiverRep.{u, v, w, max v w x} k V fld q ⥤
        @QuiverRep.{u, v, w, max v w x} k V fld (Quiver.reflectList q l))
  | [], _, _, _ => 𝟭 _
  | i :: l, q, hq, hl => by
      letI := q
      letI := hq
      exact sourceReflectionFunctor i (Quiver.isSourceAdmissible_cons.mp hl).1 ⋙
        sourceReflectionFunctorList k l (Quiver.reflectAt q i)
          (@Quiver.instFintypeReflectHom V q hq i)
          (Quiver.isSourceAdmissible_cons.mp hl).2

variable {k : Type u} {V : Type v} [fld : Field k] [fV : Fintype V]

@[simp]
theorem sourceReflectionFunctorList_nil (q : _root_.Quiver.{w} V)
    (hq : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b))
    (hl : Quiver.IsSourceAdmissible q []) :
    sourceReflectionFunctorList.{u, v, w, x} k [] q hq hl = 𝟭 _ := by
  rw [sourceReflectionFunctorList]

@[simp]
theorem sourceReflectionFunctorList_cons (i : V) (l : List V)
    (q : _root_.Quiver.{w} V)
    (hq : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b))
    (hl : Quiver.IsSourceAdmissible q (i :: l)) :
    sourceReflectionFunctorList.{u, v, w, x} k (i :: l) q hq hl =
      sourceReflectionFunctor i (Quiver.isSourceAdmissible_cons.mp hl).1 ⋙
        sourceReflectionFunctorList k l (Quiver.reflectAt q i)
          (@Quiver.instFintypeReflectHom V q hq i)
          (Quiver.isSourceAdmissible_cons.mp hl).2 := by
  rw [sourceReflectionFunctorList]
  congr

/-- The composite along a nonempty source-admissible list first source-reflects at its head. -/
theorem sourceReflectionFunctorList_cons_obj (i : V) (l : List V)
    (q : _root_.Quiver.{w} V)
    (hq : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b))
    (hl : Quiver.IsSourceAdmissible q (i :: l))
    (M : @QuiverRep.{u, v, w, max v w x} k V fld q) :
    (sourceReflectionFunctorList.{u, v, w, x} k (i :: l) q hq hl).obj M =
      (sourceReflectionFunctorList k l (Quiver.reflectAt q i)
          (@Quiver.instFintypeReflectHom V q hq i)
          (Quiver.isSourceAdmissible_cons.mp hl).2).obj
        (sourceReflectRep M (Quiver.isSourceAdmissible_cons.mp hl).1) := by
  let : _root_.Quiver.{w} V := q
  let : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b) := hq
  rw [sourceReflectionFunctorList_cons]
  exact congrArg _ (sourceReflectionFunctor_obj i
    (Quiver.isSourceAdmissible_cons.mp hl).1 M)

/-- Source-reflection composites preserve pointwise finite-dimensionality. -/
theorem isFinDim_sourceReflectionFunctorList_obj :
    ∀ (l : List V) (q : _root_.Quiver.{w} V)
      (hq : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b))
      (hl : Quiver.IsSourceAdmissible q l)
      (M : @QuiverRep.{u, v, w, max v w x} k V fld q),
      @IsFinDim.{u, v, w, max v w x} k V fld q M →
      @IsFinDim.{u, v, w, max v w x} k V fld (Quiver.reflectList q l)
        ((sourceReflectionFunctorList k l q hq hl).obj M)
  | [], q, hq, hl, M, hfd => by
      rw [sourceReflectionFunctorList_nil]
      exact hfd
  | i :: l, q, hq, hl, M, hfd => by
      let : _root_.Quiver.{w} V := q
      let : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b) := hq
      rw [sourceReflectionFunctorList_cons]
      refine isFinDim_sourceReflectionFunctorList_obj l (Quiver.reflectAt q i)
        (@Quiver.instFintypeReflectHom V q hq i)
        (Quiver.isSourceAdmissible_cons.mp hl).2
        ((sourceReflectionFunctor i (Quiver.isSourceAdmissible_cons.mp hl).1).obj M) ?_
      rw [sourceReflectionFunctor_obj]
      exact (@isFinDim_iff.{u, v, w, max v w x} k V fld (Quiver.reflectAt q i) _).mpr
        (finiteDimensional_sourceReflectRep_obj M
          (Quiver.isSourceAdmissible_cons.mp hl).1
          ((@isFinDim_iff.{u, v, w, max v w x} k V fld q M).mp hfd))

/-! ### Indecomposability and dimension vectors -/

section EqualUniverse

variable {K W : Type u} [fldK : Field K] [fW : Fintype W]

/-- **A source-reflection composite reconstructs an indecomposable along a nonnegative reflection
word.** If `M` is indecomposable and the image of its dimension vector after every nonempty prefix
of the source-admissible word is nonnegative, then every source reflection avoids its exceptional
vertex simple.
The final representation is indecomposable, and its dimension vector is the product of the simple
reflections along the word applied to `dimVector M`. -/
theorem indecomposable_and_dimVector_sourceReflectionFunctorList [DecidableEq W] :
    ∀ (l : List W) (q : _root_.Quiver.{u} W)
      (hq : ∀ a b : W, Fintype (@_root_.Quiver.Hom W q a b))
      (hl : Quiver.IsSourceAdmissible q l)
      (M : @QuiverRep.{u, u, u, u} K W fldK q),
      Indecomposable M →
      (∀ a : W, FiniteDimensional K (M.obj a)) →
      (∀ r < l.length, 0 ≤ @vertexPreReflectionList W q fW hq _ (l.take (r + 1))
        (fun j : W ↦ (@dimVector K W fldK q M j : ℤ))) →
      Indecomposable ((sourceReflectionFunctorList K l q hq hl).obj M) ∧
        (fun j : W ↦ (@dimVector K W fldK (Quiver.reflectList q l)
            ((sourceReflectionFunctorList K l q hq hl).obj M) j : ℤ)) =
          @vertexPreReflectionList W q fW hq _ l
            (fun j : W ↦ (@dimVector K W fldK q M j : ℤ))
  | [], q, hq, hl, M, hM, _, _ => by
      rw [sourceReflectionFunctorList_nil, vertexPreReflectionList_nil]
      exact ⟨hM, rfl⟩
  | i :: l, q, hq, hl, M, hM, hfd, hnonneg => by
      let : _root_.Quiver.{u} W := q
      let : ∀ a b : W, Fintype (@_root_.Quiver.Hom W q a b) := hq
      obtain ⟨hi, hl'⟩ := Quiver.isSourceAdmissible_cons.mp hl
      -- Nonnegativity after the first reflection rules out the exceptional vertex simple.
      have hnext : 0 ≤ @vertexPreReflection W q fW hq _ i
          (fun j : W ↦ (@dimVector K W fldK q M j : ℤ)) := by
        simpa [vertexPreReflectionList_apply_cons] using hnonneg 0 (by simp)
      have hloop : IsEmpty (@_root_.Quiver.Hom W q i i) := hi.isEmpty_hom_self
      have hne : ¬ Nonempty (M ≅ simpleRep K W i) :=
        not_nonempty_iso_simpleRep_of_vertexPreReflection_nonneg hloop hnext
      have hM' : Indecomposable (sourceReflectRep M hi) :=
        indecomposable_sourceReflectRep_of_not_nonempty_iso_simpleRep hi hM hne
      have hdim : (fun j : W ↦
            (@dimVector K W fldK (Quiver.reflectAt q i) (sourceReflectRep M hi) j : ℤ)) =
          @vertexPreReflection W q fW hq _ i
            (fun j : W ↦ (@dimVector K W fldK q M j : ℤ)) :=
        dimVector_sourceReflectRep_of_indecomposable hi hM hne (fun e ↦ hfd e.1)
      have hfd' : ∀ a : W, FiniteDimensional K ((sourceReflectRep M hi).obj a) :=
        finiteDimensional_sourceReflectRep_obj M hi hfd
      -- Prefixes of the tail are precisely nonempty prefixes of the original word after its head.
      have hnonneg' : ∀ r < l.length,
          0 ≤ @vertexPreReflectionList W (Quiver.reflectAt q i) fW
            (@Quiver.instFintypeReflectHom W q hq i) _ (l.take (r + 1))
            (fun j : W ↦
              (@dimVector K W fldK (Quiver.reflectAt q i) (sourceReflectRep M hi) j : ℤ)) := by
        intro r hr
        rw [vertexPreReflectionList_reflectAt, hdim]
        simpa [vertexPreReflectionList_apply_cons] using hnonneg (r + 1) (by simp [hr])
      rw [sourceReflectionFunctorList_cons_obj]
      obtain ⟨hfinal, hfinaldim⟩ :=
        indecomposable_and_dimVector_sourceReflectionFunctorList l
          (Quiver.reflectAt q i) (@Quiver.instFintypeReflectHom W q hq i) hl'
          (sourceReflectRep M hi) hM' hfd' hnonneg'
      refine ⟨hfinal, ?_⟩
      -- Simple reflections are unchanged by reversing the quiver at the preceding vertex.
      calc
        (fun j : W ↦ (@dimVector K W fldK (Quiver.reflectList q (i :: l))
            ((sourceReflectionFunctorList K l (Quiver.reflectAt q i)
              (@Quiver.instFintypeReflectHom W q hq i) hl').obj
                (sourceReflectRep M hi)) j : ℤ)) =
            @vertexPreReflectionList W (Quiver.reflectAt q i) fW
              (@Quiver.instFintypeReflectHom W q hq i) _ l
              (fun j : W ↦ (@dimVector K W fldK (Quiver.reflectAt q i)
                (sourceReflectRep M hi) j : ℤ)) := hfinaldim
        _ = @vertexPreReflectionList W q fW hq _ l
              (@vertexPreReflection W q fW hq _ i
                (fun j : W ↦ (@dimVector K W fldK q M j : ℤ))) := by
              rw [vertexPreReflectionList_reflectAt, hdim]
        _ = @vertexPreReflectionList W q fW hq _ (i :: l)
              (fun j : W ↦ (@dimVector K W fldK q M j : ℤ)) :=
              (vertexPreReflectionList_apply_cons W i l _).symm

end EqualUniverse

end TauCeti
