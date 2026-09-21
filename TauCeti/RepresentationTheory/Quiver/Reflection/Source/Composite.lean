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

## Main definition

* `TauCeti.sourceReflectionFunctorList`: the composite of source reflection functors along a
  source-admissible list.

## Main results

* `TauCeti.indecomposable_and_dimVector_sourceReflectionFunctorList`: if all successive reflected
  dimension vectors are nonnegative, the composite preserves indecomposability and realizes the
  corresponding product of simple reflections on dimension vectors.

## References

See Bernstein--Gelfand--Ponomarev, *Coxeter functors and Gabriel's theorem*, and Derksen--Weyman,
*An Introduction to Quiver Representations*, Ch. 2. The source-reflection construction here is
dual to the sink-reflection composite `TauCeti.reflectionFunctorList` in
`TauCeti.RepresentationTheory.Quiver.Reflection.Composite`.
-/

public section

namespace TauCeti

open CategoryTheory
open _root_.TauCeti.Quiver

universe u v w x

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

/-- The composite of source reflection functors is additive. -/
noncomputable instance sourceReflectionFunctorList_additive (l : List V)
    (q : _root_.Quiver.{w} V)
    (hq : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b))
    (hl : Quiver.IsSourceAdmissible q l) :
    (sourceReflectionFunctorList.{u, v, w, x} k l q hq hl).Additive := by
  induction l generalizing q with
  | nil =>
      let : _root_.Quiver.{w} V := q
      rw [sourceReflectionFunctorList_nil]
      change (𝟭 (@QuiverRep.{u, v, w, max v w x} k V fld q)).Additive
      exact Functor.instAdditiveId
  | cons i l ih =>
      let : _root_.Quiver.{w} V := q
      let : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b) := hq
      rw [sourceReflectionFunctorList_cons]
      exact @Functor.instAdditiveComp _ _ _ _ _ _
        (sourceReflectionFunctor i (Quiver.isSourceAdmissible_cons.mp hl).1)
        (sourceReflectionFunctor_additive i (Quiver.isSourceAdmissible_cons.mp hl).1)
        _ _ _
        (sourceReflectionFunctorList k l (Quiver.reflectAt q i)
          (@Quiver.instFintypeReflectHom V q hq i)
          (Quiver.isSourceAdmissible_cons.mp hl).2)
        (ih (Quiver.reflectAt q i) (@Quiver.instFintypeReflectHom V q hq i)
          (Quiver.isSourceAdmissible_cons.mp hl).2)

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

variable {K : Type u} {W : Type v} [fldK : Field K] [fW : Fintype W]

/-- **A source-reflection composite reconstructs an indecomposable along a nonnegative reflection
word.** If `M` is indecomposable and the image of its dimension vector after every nonempty prefix
of the source-admissible word is nonnegative, then every source reflection avoids its exceptional
vertex simple.
The final representation is indecomposable, and its dimension vector is the product of the simple
reflections along the word applied to `dimVector M`. -/
theorem indecomposable_and_dimVector_sourceReflectionFunctorList [DecidableEq W] :
    ∀ (l : List W) (q : _root_.Quiver.{w} W)
      (hq : ∀ a b : W, Fintype (@_root_.Quiver.Hom W q a b))
      (hl : Quiver.IsSourceAdmissible q l)
      (M : @QuiverRep.{u, v, w, max v w x} K W fldK q),
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
      let : _root_.Quiver.{w} W := q
      let : ∀ a b : W, Fintype (@_root_.Quiver.Hom W q a b) := hq
      obtain ⟨hi, hl'⟩ := Quiver.isSourceAdmissible_cons.mp hl
      -- Nonnegativity after the first reflection rules out the exceptional vertex simple.
      have hnext : 0 ≤ @vertexPreReflection W q fW hq _ i
          (fun j : W ↦ (@dimVector K W fldK q M j : ℤ)) := by
        simpa [vertexPreReflectionList_apply_cons] using hnonneg 0 (by simp)
      have hinj : Function.Injective (outgoingMap M i) :=
        outgoingMap_injective_of_vertexPreReflection_nonneg hi hM hnext
      have hM' : Indecomposable (sourceReflectRep M hi) :=
        indecomposable_sourceReflectRep hi hM hinj
      have hdim : (fun j : W ↦
            (@dimVector K W fldK (Quiver.reflectAt q i) (sourceReflectRep M hi) j : ℤ)) =
          @vertexPreReflection W q fW hq _ i
            (fun j : W ↦ (@dimVector K W fldK q M j : ℤ)) :=
        dimVector_sourceReflectRep M hi (fun e ↦ hfd e.1) hinj
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

end TauCeti
