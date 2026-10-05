/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Reflection.Root
public import TauCeti.RepresentationTheory.Quiver.Acyclic.TitsForm

/-!
# Indecomposable representations of positive definite quivers are bricks

A finite-dimensional indecomposable representation of a finite quiver with positive definite
Tits form has a one-dimensional endomorphism space over the base field. Thus every
endomorphism is a scalar, over an arbitrary field. This distinguishes these representations
from general indecomposables, whose endomorphism rings can contain nonzero nilpotents.

## Main results

* `TauCeti.finrank_end_eq_one_of_indecomposable_of_isSinkAdmissible`: the endomorphism
  dimension for a quiver equipped with a sink-admissible ordering.
* `TauCeti.finrank_end_eq_one_of_indecomposable`: the result assuming only positive
  definiteness, with the ordering chosen internally.

## Implementation notes

Coxeter descent eventually annihilates an indecomposable. Before the annihilating stage,
reflection is fully faithful and linear, so it preserves the endomorphism dimension. The
annihilating stage finds a representation concentrated at a single vertex, where it is a line.

## References

I. N. Bernstein, I. M. Gelfand and V. A. Ponomarev, *Coxeter functors and Gabriel's theorem*
(1973); I. Assem, D. Simson and A. Skowroński, *Elements of the Representation Theory of
Associative Algebras*, Vol. I, Chapter VII.
-/

public section

namespace TauCeti

open CategoryTheory
open _root_.TauCeti.Quiver

universe u v w x

variable {k : Type u} {V : Type v} [fld : Field k] [fV : Fintype V]

/-- Along a sink-admissible list, an indecomposable is either a brick already or has the
same endomorphism dimension as its image. -/
private theorem finrank_end_eq_one_or_eq_reflectionFunctorList :
    ∀ (l : List V) (q : _root_.Quiver.{w} V)
      (hq : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b))
      (hl : Quiver.IsSinkAdmissible q l) (M : @QuiverRep.{u, v, w, max v w x} k V fld q),
      Indecomposable M →
      Module.finrank k (End M) = 1 ∨
        Indecomposable ((reflectionFunctorList k l q hq hl).obj M) ∧
          Module.finrank k (End M) =
            Module.finrank k (End ((reflectionFunctorList k l q hq hl).obj M))
  | [], q, hq, hl, M, hM => by
      rw [reflectionFunctorList_nil]
      exact Or.inr ⟨hM, rfl⟩
  | i :: l, q, hq, hl, M, hM => by
      classical
      let : _root_.Quiver.{w} V := q
      let : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b) := hq
      obtain ⟨hi, hl'⟩ := Quiver.isSinkAdmissible_cons.mp hl
      rcases incomingSum_surjective_or_forall_subsingleton hi hM with hs | hsub
      · have ih := finrank_end_eq_one_or_eq_reflectionFunctorList l (Quiver.reflectAt q i)
          (@instFintypeReflectHom V q hq i) hl' (reflectRep M hi)
          (indecomposable_reflectRep hi hM hs)
        have he := finrank_end_reflectRep hi hs
        rw [reflectionFunctorList_cons_obj i l q hq hl M]
        exact ih.imp (fun h ↦ he.symm.trans h) (fun ⟨hind, h⟩ ↦ ⟨hind, he.symm.trans h⟩)
      · exact Or.inl (finrank_end_eq_one_of_forall_subsingleton hi.path_self_eq_nil hM hsub)

/-- A power of the Coxeter functor can kill an indecomposable only if it is a brick. -/
private theorem finrank_end_eq_one_of_isZero_iterate (q : _root_.Quiver.{w} V)
    (hq : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b))
    {l : List V} (hnd : l.Nodup) (hall : ∀ v : V, v ∈ l) (hl : Quiver.IsSinkAdmissible q l) :
    ∀ (n : ℕ) (M : @QuiverRep.{u, v, w, max v w x} k V fld q), Indecomposable M →
      @IsFinDim.{u, v, w, max v w x} k V fld q M →
      Limits.IsZero (((coxeterFunctor.{u, v, w, x} k q hq hnd hall hl).obj)^[n] M) →
      Module.finrank k (End M) = 1 := by
  classical
  intro n
  induction n with
  | zero =>
    intro M hM _ hz
    rw [Function.iterate_zero_apply] at hz
    exact absurd hz hM.1
  | succ n ih =>
    intro M hM hfd hz
    rw [Function.iterate_succ_apply] at hz
    rcases finrank_end_eq_one_or_eq_reflectionFunctorList l q hq hl M hM with hone | ⟨hlist, he⟩
    · exact hone
    rw [← finrank_end_coxeterFunctor_obj q hq hnd hall hl M] at he
    rcases indecomposable_and_dimVector_coxeterFunctor_or_isZero q hq hnd hall hl M hM
        ((@isFinDim_iff.{u, v, w, max v w x} k V fld q M).mp hfd) with ⟨hind, _⟩ | hzero
    · exact he.trans (ih _ hind (isFinDim_coxeterFunctor_obj q hq hnd hall hl M hfd) hz)
    · exact absurd ((isZero_coxeterFunctor_obj_iff_isZero_reflectionFunctorList_obj
        q hq hnd hall hl M).mp hzero) hlist.1

/-- Every finite-dimensional indecomposable representation of a quiver with positive definite
Tits form and a sink-admissible ordering has a one-dimensional endomorphism space. -/
theorem finrank_end_eq_one_of_indecomposable_of_isSinkAdmissible (q : _root_.Quiver.{w} V)
    (hq : ∀ a b : V, Fintype (@_root_.Quiver.Hom V q a b)) {l : List V} (hnd : l.Nodup)
    (hall : ∀ v : V, v ∈ l) (hl : Quiver.IsSinkAdmissible q l)
    (hpd : (@titsForm V q fV hq).PosDef) (M : @QuiverRep.{u, v, w, max v w x} k V fld q)
    (hM : Indecomposable M) (hfd : @IsFinDim.{u, v, w, max v w x} k V fld q M) :
    Module.finrank k (End M) = 1 := by
  obtain ⟨n, hn⟩ := exists_isZero_coxeterFunctor_iterate q hq hnd hall hl hpd M hM hfd
  exact finrank_end_eq_one_of_isZero_iterate q hq hnd hall hl n M hM hfd hn

/-- Every finite-dimensional indecomposable representation of a finite quiver with
positive definite Tits form has a one-dimensional endomorphism space, over any field. -/
theorem finrank_end_eq_one_of_indecomposable [q : _root_.Quiver.{w} V]
    [hq : ∀ a b : V, Fintype (a ⟶ b)] (hpd : (titsForm V).PosDef)
    (M : QuiverRep.{u, v, w, max v w x} k V) (hM : Indecomposable M)
    (hfd : IsFinDim.{u, v, w, max v w x} k V M) :
    Module.finrank k (End M) = 1 := by
  obtain ⟨l, hnd, hall, hl⟩ := (isAcyclic_of_titsForm_posDef hpd).exists_isSinkAdmissible
  exact finrank_end_eq_one_of_indecomposable_of_isSinkAdmissible q hq hnd hall hl hpd M hM hfd

end TauCeti
