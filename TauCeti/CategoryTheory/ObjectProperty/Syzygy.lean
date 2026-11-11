/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms

/-!
# Syzygies relative to a property of objects

Let `P` be a property of objects of a category with zero morphisms, such as being a finitely
generated projective module. An object `X` is a **`k`-th syzygy relative to `P`** when there is an
exact sequence `0 ⟶ X ⟶ Q₁ ⟶ ⋯ ⟶ Q_k` with every `Qᵢ` satisfying `P`. It is defined by recursion
on `k`: every object is a `0`-th syzygy, and `X` is a `(k + 1)`-st syzygy when it is the first term
of a short exact sequence `0 ⟶ X ⟶ Q ⟶ X' ⟶ 0` with `P Q` and `X'` a `k`-th syzygy. Splicing these
short exact sequences gives the long exact sequence, ending in an epimorphism onto the last
cokernel; so for the projective objects of an abelian category, the `k`-th syzygies are the objects
of the form `Ωᵏ N`.

## Main definitions

* `CategoryTheory.ObjectProperty.IsSyzygy P k`: the `k`-th syzygies relative to `P`.

## Main results

* `CategoryTheory.ObjectProperty.isSyzygy_succ_iff`: the recursive description.
* `CategoryTheory.ObjectProperty.IsSyzygy.of_succ`: a `(k + 1)`-st syzygy is a `k`-th syzygy.
* `CategoryTheory.ObjectProperty.IsSyzygy.map`: functors preserving short exact sequences preserve
  syzygies.
* The `k`-th syzygies are closed under isomorphisms.

## References

* M. Auslander, M. Bridger, *Stable module theory*, Mem. Amer. Math. Soc. 94 (1969), §2.
-/

public section

namespace CategoryTheory.ObjectProperty

open Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (P : ObjectProperty C)

/-- **`k`-th syzygies relative to `P`**: every object is a `0`-th syzygy, and `X` is a `(k + 1)`-st
syzygy when there is a short exact sequence `0 ⟶ X ⟶ Q ⟶ X' ⟶ 0` with `P Q` and `X'` a `k`-th
syzygy. -/
def IsSyzygy : ℕ → ObjectProperty C
  | 0 => fun _ ↦ True
  | k + 1 => fun X ↦ ∃ S : ShortComplex C, S.ShortExact ∧ Nonempty (X ≅ S.X₁) ∧ P S.X₂ ∧
      IsSyzygy k S.X₃

/-- Every object is a `0`-th syzygy. -/
@[simp]
theorem isSyzygy_zero (X : C) : P.IsSyzygy 0 X :=
  trivial

/-- `X` is a `(k + 1)`-st syzygy exactly when it is the first term of a short exact sequence whose
middle term satisfies `P` and whose last term is a `k`-th syzygy. -/
theorem isSyzygy_succ_iff (k : ℕ) (X : C) :
    P.IsSyzygy (k + 1) X ↔ ∃ S : ShortComplex C, S.ShortExact ∧ Nonempty (X ≅ S.X₁) ∧ P S.X₂ ∧
      P.IsSyzygy k S.X₃ :=
  Iff.rfl

instance (k : ℕ) : (P.IsSyzygy k).IsClosedUnderIsomorphisms where
  of_iso e hX := by
    cases k with
    | zero => exact isSyzygy_zero P _
    | succ k =>
      obtain ⟨S, hS, ⟨e'⟩, hQ, hX'⟩ := (P.isSyzygy_succ_iff k _).1 hX
      exact (P.isSyzygy_succ_iff k _).2 ⟨S, hS, ⟨e.symm ≪≫ e'⟩, hQ, hX'⟩

variable {P}

/-- A `(k + 1)`-st syzygy is a `k`-th syzygy. -/
theorem IsSyzygy.of_succ {k : ℕ} {X : C} (h : P.IsSyzygy (k + 1) X) : P.IsSyzygy k X := by
  induction k generalizing X with
  | zero => exact isSyzygy_zero P X
  | succ k ih =>
    obtain ⟨S, hS, e, hQ, hX'⟩ := (P.isSyzygy_succ_iff (k + 1) X).1 h
    exact (P.isSyzygy_succ_iff k X).2 ⟨S, hS, e, hQ, ih hX'⟩

/-- A `k`-th syzygy is an `l`-th syzygy for every `l ≤ k`. -/
theorem IsSyzygy.of_le {k l : ℕ} (hlk : l ≤ k) {X : C} (h : P.IsSyzygy k X) :
    P.IsSyzygy l X := by
  induction hlk with
  | refl => exact h
  | step _ ih => exact ih h.of_succ

/-- **Syzygies are preserved by functors** that preserve short exact sequences and send objects of
`P` to objects of `P'`. -/
theorem IsSyzygy.map {D : Type*} [Category* D] [HasZeroMorphisms D] {P' : ObjectProperty D}
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (hF : ∀ S : ShortComplex C, S.ShortExact → (S.map F).ShortExact)
    (hP : ∀ Q, P Q → P' (F.obj Q)) {k : ℕ} {X : C} (h : P.IsSyzygy k X) :
    P'.IsSyzygy k (F.obj X) := by
  induction k generalizing X with
  | zero => exact isSyzygy_zero P' _
  | succ k ih =>
    obtain ⟨S, hS, ⟨e⟩, hQ, hX'⟩ := (P.isSyzygy_succ_iff k X).1 h
    exact (P'.isSyzygy_succ_iff k _).2 ⟨S.map F, hF S hS, ⟨F.mapIso e⟩, hP _ hQ, ih hX'⟩

end CategoryTheory.ObjectProperty
