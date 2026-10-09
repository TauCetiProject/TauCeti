/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Graded.Basic
public import TauCeti.Algebra.Module.GradedModule.DirectSum
public import TauCeti.Algebra.Module.GradedModule.Multilinear.Basic
public import Mathlib.LinearAlgebra.Multilinear.DirectSum

/-!
# The total module of morphisms of a graded linear quiver

The **total module** of a graded linear quiver is the external direct sum
`⨁ (X, Y), Hom(X, Y)` of all of its hom modules, graded degreewise.  Operations on composable
strings of morphisms are conveniently encoded as multilinear operations on the total module
which respect the decomposition into hom modules: a string `aₙ, …, a₁` with
`aᵢ : Xᵢ₋₁ ⟶ Xᵢ` is sent to a morphism `X₀ ⟶ Xₙ`, and a string that is not composable is sent
to zero.  This is the predicate `TauCeti.GradedLinearQuiver.IsPathCompatible`.  It lets the
structure on a many-object quiver be stated as structure on a single graded module, the
many-object analogue of an algebra over the product of copies of the ground ring indexed by the
objects.

The inclusion and projection of a single hom module are `homInclusion` and `homProjection`.
They are `DirectSum.lof` and `DirectSum.component`; `homInclusion` is defined with classical
decidable equality on objects, so that no decidability assumption on the objects enters the
statements that use it.

## Main definitions

* `TauCeti.GradedLinearQuiver.TotalHom`: the direct sum of all hom modules.
* `TauCeti.GradedLinearQuiver.totalGrading`: its degreewise grading.
* `TauCeti.GradedLinearQuiver.homInclusion` and `TauCeti.GradedLinearQuiver.homProjection`: the
  inclusion and projection of the hom module of a pair of objects.
* `TauCeti.GradedLinearQuiver.IsPathCompatible`: a multilinear operation on the total module
  sending composable strings to the hom module of their endpoints and other strings to zero.

## Main results

* `TauCeti.GradedLinearQuiver.mem_totalGrading_piece_iff`: an element of the total module has
  degree `n` exactly when each of its components has.
* `TauCeti.GradedLinearQuiver.homInclusion_homProjection_of_mem_range`: an element of the image
  of a hom module is recovered from its component there.
* `TauCeti.GradedLinearQuiver.IsPathCompatible.ext`: a path-compatible operation is determined
  by its values on composable strings.
* `TauCeti.GradedLinearQuiver.isPathCompatible_of_homogeneous`: path compatibility can be tested
  on homogeneous morphisms.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 7.1.
-/

public section

open scoped DirectSum

namespace TauCeti.GradedLinearQuiver

universe u v w

variable (R : Type w) [CommRing R] (C : Type u) [GradedLinearQuiver.{u, v, w} R C]

/-- The **total module of morphisms** of a graded linear quiver: the external direct sum of the
hom modules of all ordered pairs of objects. -/
abbrev TotalHom : Type (max u v) :=
  ⨁ p : C × C, homModule (R := R) p.1 p.2

/-- The grading of the total module of morphisms: an element has degree `n` when each of its
components has degree `n`. -/
noncomputable def totalGrading : InternalGrading R (TotalHom R C) :=
  InternalGrading.directSum fun p : C × C ↦ grading (R := R) p.1 p.2

variable {R C}

/-- The inclusion of the morphisms `X ⟶ Y` into the total module of morphisms. -/
noncomputable def homInclusion (X Y : C) : homModule (R := R) X Y →ₗ[R] TotalHom R C :=
  letI := Classical.decEq C
  DirectSum.lof R (C × C) (fun p ↦ homModule (R := R) p.1 p.2) (X, Y)

/-- The projection of the total module of morphisms onto the morphisms `X ⟶ Y`. -/
noncomputable def homProjection (X Y : C) : TotalHom R C →ₗ[R] homModule (R := R) X Y :=
  DirectSum.component R (C × C) (fun p ↦ homModule (R := R) p.1 p.2) (X, Y)

/-- The inclusion of a hom module is the direct-sum inclusion of its summand, for any decidable
equality on the objects. -/
theorem homInclusion_eq_lof [DecidableEq C] (X Y : C) :
    homInclusion (R := R) X Y =
      DirectSum.lof R (C × C) (fun p ↦ homModule (R := R) p.1 p.2) (X, Y) := by
  rw [homInclusion]
  congr
  exact Subsingleton.elim _ _

/-- Projecting an included morphism back to its own hom module recovers it. -/
@[simp]
theorem homProjection_homInclusion (X Y : C) (f : homModule (R := R) X Y) :
    homProjection X Y (homInclusion X Y f) = f := by
  classical
  rw [homInclusion_eq_lof, homProjection, DirectSum.component.lof_self]

/-- Projecting an included morphism to the hom module of another pair of objects gives zero. -/
@[simp]
theorem homProjection_homInclusion_of_ne {X Y X' Y' : C} (h : (X, Y) ≠ (X', Y'))
    (f : homModule (R := R) X Y) :
    homProjection X' Y' (homInclusion X Y f) = 0 := by
  classical
  simp [homInclusion_eq_lof, homProjection, DirectSum.component.of, h]

/-- The inclusion of a hom module into the total module is injective. -/
theorem homInclusion_injective (X Y : C) :
    Function.Injective (homInclusion (R := R) X Y) :=
  Function.LeftInverse.injective (homProjection_homInclusion X Y)

/-- Two elements of the total module of morphisms are equal when all of their components are. -/
theorem totalHom_ext {x y : TotalHom R C}
    (h : ∀ X Y : C, homProjection X Y x = homProjection X Y y) : x = y :=
  DirectSum.ext_component R fun p ↦ h p.1 p.2

/-- An element of the image of the morphisms `X ⟶ Y` is the inclusion of its component there. -/
theorem homInclusion_homProjection_of_mem_range {X Y : C} {x : TotalHom R C}
    (hx : x ∈ LinearMap.range (homInclusion (R := R) X Y)) :
    homInclusion X Y (homProjection X Y x) = x := by
  obtain ⟨f, rfl⟩ := hx
  rw [homProjection_homInclusion]

/-- An element of the total module of morphisms has degree `n` exactly when each of its
components has degree `n`. -/
theorem mem_totalGrading_piece_iff (n : ℤ) (x : TotalHom R C) :
    x ∈ (totalGrading R C).piece n ↔
      ∀ X Y : C, homProjection X Y x ∈ (grading (R := R) X Y).piece n := by
  rw [totalGrading, InternalGrading.directSum_piece, InternalGrading.mem_directSumPiece_iff]
  exact ⟨fun h X Y ↦ h (X, Y), fun h p ↦ h p.1 p.2⟩

/-- The component of an element of degree `n` of the total module has degree `n`. -/
theorem homProjection_mem_piece {n : ℤ} {x : TotalHom R C}
    (hx : x ∈ (totalGrading R C).piece n) (X Y : C) :
    homProjection X Y x ∈ (grading (R := R) X Y).piece n :=
  (mem_totalGrading_piece_iff n x).1 hx X Y

/-- An included morphism has degree `n` in the total module exactly when it has degree `n`. -/
@[simp]
theorem homInclusion_mem_totalGrading_piece_iff {X Y : C} (n : ℤ) (f : homModule (R := R) X Y) :
    homInclusion X Y f ∈ (totalGrading R C).piece n ↔ f ∈ (grading (R := R) X Y).piece n := by
  refine ⟨fun h ↦ by simpa using homProjection_mem_piece h X Y, fun h ↦ ?_⟩
  rw [mem_totalGrading_piece_iff]
  intro X' Y'
  by_cases hXY : (X, Y) = (X', Y')
  · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 hXY
    simpa using h
  · rw [homProjection_homInclusion_of_ne hXY]
    exact zero_mem _

/-- A multilinear operation on the total module of morphisms is **path-compatible** when it is an
operation on composable strings of morphisms.  Inputs are ordered `aₙ, …, a₁` with
`aᵢ : Xᵢ₋₁ ⟶ Xᵢ`, as for `TauCeti.GradedLinearQuiver.PathOperation`: the `i`-th input of a string
`X : Fin (n + 1) → C` runs from `X (n - 1 - i)` to `X (n - i)`.  A path-compatible operation sends
such a composable string to a morphism `X₀ ⟶ Xₙ`, and sends every string of morphisms which is
not composable to zero.

Since a multilinear map on a direct sum is determined by its values on the summands, a
path-compatible operation is determined by its values on composable strings. -/
structure IsPathCompatible {n : ℕ}
    (f : MultilinearMap R (fun _ : Fin n ↦ TotalHom R C) (TotalHom R C)) : Prop where
  /-- A composable string is sent to a morphism between the endpoints of the string. -/
  mem_range_homInclusion (X : Fin (n + 1) → C)
      (x : ∀ i : Fin n, homModule (R := R) (X i.rev.castSucc) (X i.rev.succ)) :
    f (fun i ↦ homInclusion _ _ (x i)) ∈
      LinearMap.range (homInclusion (R := R) (X 0) (X (Fin.last n)))
  /-- A string in which the target of the `j`-th morphism is not the source of the `i`-th, for
  `j = i + 1`, is sent to zero. -/
  eq_zero_of_ne (s t : Fin n → C) (x : ∀ i, homModule (R := R) (s i) (t i)) (i j : Fin n)
      (hij : (j : ℕ) = i + 1) (hne : t j ≠ s i) :
    f (fun k ↦ homInclusion (s k) (t k) (x k)) = 0

/-- A string of morphisms in which the target of each morphism is the source of the one before it
comes from a string of objects. -/
private theorem exists_eq_of_chain {n : ℕ} (s t : Fin (n + 1) → C)
    (hst : ∀ j : Fin n, t j.succ = s j.castSucc) :
    ∃ X : Fin (n + 2) → C, s = (fun i ↦ X i.rev.castSucc) ∧ t = fun i ↦ X i.rev.succ := by
  refine ⟨Fin.snoc (fun k ↦ s k.rev) (t 0), funext fun i ↦ by simp, funext fun i ↦ ?_⟩
  cases i using Fin.cases with
  | zero => simp
  | succ j => simp [Fin.rev_succ, Fin.succ_castSucc, -Fin.castSucc_succ, hst]

/-- **Path-compatible operations are determined by their values on composable strings.** -/
theorem IsPathCompatible.ext {n : ℕ}
    {f g : MultilinearMap R (fun _ : Fin n ↦ TotalHom R C) (TotalHom R C)}
    (hf : IsPathCompatible f) (hg : IsPathCompatible g)
    (h : ∀ (X : Fin (n + 1) → C)
      (x : ∀ i : Fin n, homModule (R := R) (X i.rev.castSucc) (X i.rev.succ)),
        f (fun i ↦ homInclusion _ _ (x i)) = g fun i ↦ homInclusion _ _ (x i)) :
    f = g := by
  classical
  rcases n with _ | n
  · refine MultilinearMap.ext fun x ↦ ?_
    rcases isEmpty_or_nonempty C with hC | ⟨⟨c⟩⟩
    · exact totalHom_ext fun X ↦ isEmptyElim X
    · obtain rfl : x = fun i ↦ homInclusion c c i.elim0 := Subsingleton.elim _ _
      exact h (fun _ ↦ c) fun i ↦ i.elim0
  suffices key : ∀ (s t : Fin (n + 1) → C) (x : ∀ i, homModule (R := R) (s i) (t i)),
      f (fun i ↦ homInclusion (s i) (t i) (x i)) = g fun i ↦ homInclusion (s i) (t i) (x i) by
    refine MultilinearMap.directSum_ext fun p ↦ MultilinearMap.ext fun x ↦ ?_
    have e (i : Fin (n + 1)) : DirectSum.lof R (C × C) (fun q ↦ homModule (R := R) q.1 q.2) (p i) =
        homInclusion (p i).1 (p i).2 := (homInclusion_eq_lof _ _).symm
    simp only [MultilinearMap.compLinearMap_apply, e]
    exact key (fun i ↦ (p i).1) (fun i ↦ (p i).2) x
  intro s t x
  by_cases hst : ∀ j : Fin n, t j.succ = s j.castSucc
  · obtain ⟨X, rfl, rfl⟩ := exists_eq_of_chain s t hst
    exact h X x
  · obtain ⟨j, hj⟩ := not_forall.1 hst
    rw [hf.eq_zero_of_ne s t x j.castSucc j.succ (by simp) hj,
      hg.eq_zero_of_ne s t x j.castSucc j.succ (by simp) hj]

/-- A path-compatible operation sends a string of morphisms in which the target of each morphism
is the source of the one before it to a morphism from the source `a` of its last morphism to the
target `b` of its first.  This is `IsPathCompatible.mem_range_homInclusion` for a string presented
by the sources and targets of its morphisms rather than by its objects. -/
theorem IsPathCompatible.mem_range_homInclusion_of_chain {n : ℕ}
    {f : MultilinearMap R (fun _ : Fin (n + 1) ↦ TotalHom R C) (TotalHom R C)}
    (hf : IsPathCompatible f) (s t : Fin (n + 1) → C) (x : ∀ i, homModule (R := R) (s i) (t i))
    (hst : ∀ j : Fin n, t j.succ = s j.castSucc) {a b : C} (ha : s (Fin.last n) = a)
    (hb : t 0 = b) :
    f (fun i ↦ homInclusion (s i) (t i) (x i)) ∈ LinearMap.range (homInclusion (R := R) a b) := by
  subst ha hb
  obtain ⟨X, rfl, rfl⟩ := exists_eq_of_chain s t hst
  beta_reduce
  rw [Fin.rev_last, Fin.castSucc_zero, Fin.rev_zero, Fin.succ_last]
  exact hf.mem_range_homInclusion X x

/-- **Path compatibility can be tested on homogeneous morphisms.** -/
theorem isPathCompatible_of_homogeneous {n : ℕ}
    {f : MultilinearMap R (fun _ : Fin n ↦ TotalHom R C) (TotalHom R C)}
    (mem_range : ∀ (X : Fin (n + 1) → C)
      (x : ∀ i : Fin n, homModule (R := R) (X i.rev.castSucc) (X i.rev.succ)) (d : Fin n → ℤ),
      (∀ i, x i ∈ (grading (R := R) (X i.rev.castSucc) (X i.rev.succ)).piece (d i)) →
        f (fun i ↦ homInclusion _ _ (x i)) ∈
          LinearMap.range (homInclusion (R := R) (X 0) (X (Fin.last n))))
    (eq_zero : ∀ (s t : Fin n → C) (x : ∀ i, homModule (R := R) (s i) (t i)) (d : Fin n → ℤ),
      (∀ i, x i ∈ (grading (R := R) (s i) (t i)).piece (d i)) → ∀ i j : Fin n,
        (j : ℕ) = i + 1 → t j ≠ s i → f (fun k ↦ homInclusion (s k) (t k) (x k)) = 0) :
    IsPathCompatible f where
  mem_range_homInclusion X x :=
    InternalGrading.multilinearMap_apply_mem
      (fun i ↦ grading (R := R) (X i.rev.castSucc) (X i.rev.succ))
      (f := f.compLinearMap fun i ↦ homInclusion (X i.rev.castSucc) (X i.rev.succ))
      (fun d x hx ↦ mem_range X x d hx) x
  eq_zero_of_ne s t x i j hij hne :=
    (Submodule.mem_bot R).1 <| InternalGrading.multilinearMap_apply_mem
      (fun k ↦ grading (R := R) (s k) (t k))
      (f := f.compLinearMap fun k ↦ homInclusion (s k) (t k))
      (fun d x hx ↦ (Submodule.mem_bot R).2 (eq_zero s t x d hx i j hij hne)) x

end TauCeti.GradedLinearQuiver
