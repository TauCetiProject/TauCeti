/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Opposite
public import TauCeti.CategoryTheory.Graded.TotalHom

/-!
# The opposite of a graded linear quiver

The **opposite** of a graded linear quiver `C` has the objects `Cᵒᵖ`, and its morphisms
`op X ⟶ op Y` are the morphisms `Y ⟶ X` of `C`, with the same grading.  It is the quiver of the
opposite of an `A∞` category: a composable string of `Cᵒᵖ` is a composable string of `C` read
backwards.

The total module of morphisms of `Cᵒᵖ` is the total module of morphisms of `C`, with the summand
of the pair `(op Y, op X)` identified with the summand of `(X, Y)`; this is the linear equivalence
`TauCeti.GradedLinearQuiver.opTotalHomEquiv`, and it preserves the degreewise gradings.  Reversing
the inputs of a path-compatible operation on `C` and transporting it along this equivalence gives
a path-compatible operation on `Cᵒᵖ`.

## Main definitions

* `TauCeti.GradedLinearQuiver.opposite`: the opposite graded linear quiver.
* `TauCeti.GradedLinearQuiver.opTotalHomEquiv`: the identification of the total modules of
  morphisms of `C` and of `Cᵒᵖ`.

## Main results

* `TauCeti.GradedLinearQuiver.opTotalHomEquiv_homInclusion`: the identification sends the
  summand `X ⟶ Y` of `C` to the summand `op Y ⟶ op X` of `Cᵒᵖ`.
* `TauCeti.GradedLinearQuiver.totalGrading_map_opTotalHomEquiv`: the identification preserves the
  degreewise gradings.
* `TauCeti.GradedLinearQuiver.IsPathCompatible.reverse`: a path-compatible operation on `C` with
  its inputs reversed is a path-compatible operation on `Cᵒᵖ`.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 7.1.
-/

public section

open Opposite

namespace TauCeti.GradedLinearQuiver

universe u v w

variable {R : Type w} [CommRing R] {C : Type u} [GradedLinearQuiver.{u, v, w} R C]

/-- The **opposite** graded linear quiver: the morphisms `op X ⟶ op Y` are the morphisms `Y ⟶ X`
of `C`, with the same grading. -/
instance opposite : GradedLinearQuiver.{u, v, w} R Cᵒᵖ where
  homModule X Y := homModule (R := R) (unop Y) (unop X)
  grading X Y := grading (R := R) (unop Y) (unop X)

/-- The morphisms `op X ⟶ op Y` of the opposite quiver are the morphisms `Y ⟶ X`. -/
theorem homModule_op (X Y : C) :
    homModule (R := R) (op X) (op Y) = homModule (R := R) Y X :=
  rfl

/-- The grading of the morphisms `op X ⟶ op Y` of the opposite quiver is the grading of the
morphisms `Y ⟶ X`. -/
@[simp]
theorem grading_op (X Y : C) :
    grading (R := R) (op X) (op Y) = grading (R := R) Y X :=
  rfl

/-- The pairs of objects of `C` and of `Cᵒᵖ`, matched as source and target of the same morphisms:
the pair `(X, Y)` goes to `(op Y, op X)`. -/
private def opPairEquiv : C × C ≃ Cᵒᵖ × Cᵒᵖ where
  toFun p := (op p.2, op p.1)
  invFun p := (unop p.2, unop p.1)
  left_inv _ := rfl
  right_inv _ := rfl

variable (R C) in
/-- The **total module of morphisms of the opposite quiver** is the total module of morphisms of
`C`: the summand `X ⟶ Y` of `C` is the summand `op Y ⟶ op X` of `Cᵒᵖ`. -/
noncomputable def opTotalHomEquiv : TotalHom R C ≃ₗ[R] TotalHom R Cᵒᵖ :=
  DirectSum.lequivCongrLeft R (opPairEquiv (C := C))

/-- The identification of the total modules of morphisms sends the morphism `f : X ⟶ Y` of `C` to
the same morphism `op Y ⟶ op X` of `Cᵒᵖ`. -/
@[simp]
theorem opTotalHomEquiv_homInclusion (X Y : C) (f : homModule (R := R) X Y) :
    opTotalHomEquiv R C (homInclusion X Y f) = homInclusion (op Y) (op X) f := by
  classical
  rw [homInclusion_eq_lof, homInclusion_eq_lof]
  exact DirectSum.lequivCongrLeft_lof (R := R) (M := fun p : C × C ↦ homModule (R := R) p.1 p.2)
    (e := opPairEquiv (C := C)) (i := (X, Y)) (k := (op Y, op X)) rfl f f rfl

/-- The inverse identification of the total modules of morphisms sends the morphism
`f : X ⟶ Y` of `Cᵒᵖ` to the same morphism `unop Y ⟶ unop X` of `C`. -/
@[simp]
theorem opTotalHomEquiv_symm_homInclusion (X Y : Cᵒᵖ) (f : homModule (R := R) X Y) :
    (opTotalHomEquiv R C).symm (homInclusion X Y f) = homInclusion (unop Y) (unop X) f := by
  rw [LinearEquiv.symm_apply_eq, opTotalHomEquiv_homInclusion]

/-- The component `X ⟶ Y` in `Cᵒᵖ` of an element of the total module of morphisms of `C` is its
component `unop Y ⟶ unop X`. -/
@[simp]
theorem homProjection_opTotalHomEquiv (X Y : Cᵒᵖ) (x : TotalHom R C) :
    homProjection X Y (opTotalHomEquiv R C x) = homProjection (unop Y) (unop X) x := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | of p f =>
    obtain ⟨A, B⟩ := p
    rw [← DirectSum.lof_eq_of R, ← homInclusion_eq_lof, opTotalHomEquiv_homInclusion]
    by_cases h : (A, B) = (unop Y, unop X)
    · obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 h
      exact (homProjection_homInclusion X Y f).trans
        (homProjection_homInclusion (unop Y) (unop X) f).symm
    · have h' : (op B, op A) ≠ (X, Y) := fun e ↦ h <| by
        obtain ⟨rfl, rfl⟩ := Prod.ext_iff.1 e
        rfl
      rw [homProjection_homInclusion_of_ne h, homProjection_homInclusion_of_ne h']
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/-- The identification of the total modules of morphisms preserves the degreewise gradings. -/
theorem totalGrading_map_opTotalHomEquiv :
    (totalGrading R C).map (opTotalHomEquiv R C) = totalGrading R Cᵒᵖ := by
  refine InternalGrading.ext fun p ↦ Submodule.ext fun x ↦ ?_
  obtain ⟨y, rfl⟩ := (opTotalHomEquiv R C).surjective x
  rw [InternalGrading.mem_map_piece_iff, LinearEquiv.symm_apply_apply, mem_totalGrading_piece_iff,
    mem_totalGrading_piece_iff]
  simp only [homProjection_opTotalHomEquiv]
  exact ⟨fun h X Y ↦ h (unop Y) (unop X), fun h X Y ↦ h (op Y) (op X)⟩

/-- An element of the total module of morphisms has degree `n` in `Cᵒᵖ` exactly when it has
degree `n` in `C`. -/
@[simp]
theorem opTotalHomEquiv_mem_totalGrading_piece_iff (n : ℤ) (x : TotalHom R C) :
    opTotalHomEquiv R C x ∈ (totalGrading R Cᵒᵖ).piece n ↔ x ∈ (totalGrading R C).piece n := by
  rw [← totalGrading_map_opTotalHomEquiv, InternalGrading.apply_mem_map_piece_iff]

/-- The operation on `Cᵒᵖ` given by a multilinear operation `f` on `C` with its inputs reversed:
`(x₀, …, xₙ₋₁) ↦ f (xₙ₋₁, …, x₀)`, along the identification of the total modules of
morphisms. -/
noncomputable def reverseOperation {n : ℕ}
    (f : MultilinearMap R (fun _ : Fin n ↦ TotalHom R C) (TotalHom R C)) :
    MultilinearMap R (fun _ : Fin n ↦ TotalHom R Cᵒᵖ) (TotalHom R Cᵒᵖ) :=
  (opTotalHomEquiv R C).toLinearMap.compMultilinearMap
    ((f.domDomCongr Fin.revPerm).compLinearMap fun _ ↦ (opTotalHomEquiv R C).symm.toLinearMap)

/-- The reversed operation evaluates the original operation on the reversed inputs. -/
@[simp]
theorem reverseOperation_apply {n : ℕ}
    (f : MultilinearMap R (fun _ : Fin n ↦ TotalHom R C) (TotalHom R C))
    (x : Fin n → TotalHom R Cᵒᵖ) :
    reverseOperation f x = opTotalHomEquiv R C (f fun i ↦ (opTotalHomEquiv R C).symm (x i.rev)) :=
  (rfl)

/-- **The reverse of a path-compatible operation is path-compatible.**  A composable string of
`Cᵒᵖ`, read backwards, is a composable string of `C` between the same endpoints. -/
theorem IsPathCompatible.reverse {n : ℕ}
    {f : MultilinearMap R (fun _ : Fin n ↦ TotalHom R C) (TotalHom R C)}
    (hf : IsPathCompatible f) : IsPathCompatible (reverseOperation f) where
  mem_range_homInclusion X x := by
    rcases n with _ | n
    · obtain ⟨y, hy⟩ := hf.mem_range_homInclusion (fun _ ↦ unop (X 0)) fun i ↦ i.elim0
      refine ⟨y, ?_⟩
      rw [reverseOperation_apply, Subsingleton.elim (fun i : Fin 0 ↦ _)
        fun i ↦ homInclusion (unop (X 0)) (unop (X 0)) i.elim0, ← hy, opTotalHomEquiv_homInclusion]
      rfl
    · obtain ⟨y, hy⟩ := hf.mem_range_homInclusion_of_chain (fun i ↦ unop (X i.rev.rev.succ))
        (fun i ↦ unop (X i.rev.rev.castSucc)) (fun i ↦ x i.rev)
        (fun j ↦ by simp only [Fin.rev_rev, Fin.succ_castSucc])
        (a := unop (X (Fin.last (n + 1)))) (b := unop (X 0)) (by simp) (by simp)
      refine ⟨y, ?_⟩
      rw [reverseOperation_apply]
      simp only [opTotalHomEquiv_symm_homInclusion]
      rw [← hy, opTotalHomEquiv_homInclusion]
  eq_zero_of_ne s t x i j hij hne := by
    rw [reverseOperation_apply]
    simp only [opTotalHomEquiv_symm_homInclusion]
    rw [hf.eq_zero_of_ne (fun k ↦ unop (t k.rev)) (fun k ↦ unop (s k.rev)) (fun k ↦ x k.rev)
      j.rev i.rev (by simp [Fin.val_rev]; omega) (by simpa using unop_injective.ne hne.symm),
      map_zero]

end TauCeti.GradedLinearQuiver
