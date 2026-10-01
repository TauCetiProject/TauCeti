/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Graded.Basic
public import TauCeti.Algebra.Module.GradedModule.Multilinear

/-!
# Multilinear operations on composable graded morphisms

For a string of objects `X : Fin (n + 1) → C`, inputs are ordered from left to right as
`Hom(X₁,X₀), …, Hom(Xₙ,Xₙ₋₁)`, and the output lies in `Hom(Xₙ,X₀)`.
Thus binary operations take `(g,f)` in the order used by `m₂(g,f) = g ∘ f`.

`GradedLinearQuiver.PathOperation` records an operation of degree `q` by its multilinear maps on
each tuple of homogeneous pieces. `GradedLinearQuiver.pathOperationEquiv` identifies this with a
homogeneous multilinear map on the total Hom modules: degreewise operations extend uniquely,
and restricting the extension recovers every component. The representation accommodates the
degree `2 - n` operations of an `A∞` category without assuming composition on the quiver.

Coordinate changes use linear equivalences of the input and output pieces, through Mathlib's
`LinearEquiv.multilinearMapCongrLeft` and `LinearEquiv.multilinearMapCongrRight`. No equality cast
of an operation is needed to change its homogeneous modules.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 7.1.
-/

public section

open scoped BigOperators

namespace TauCeti.GradedLinearQuiver

universe u v w

variable (R : Type w) [CommRing R] {C : Type u} [GradedLinearQuiver.{u, v, w} R C]
  {n : ℕ} (X : Fin (n + 1) → C)

/-- A degree-`q` operation on a composable string, on the input degrees `d`.
The `i`-th input runs from `X (i + 1)` to `X i`, so binary inputs are `(g,f)`. -/
abbrev PathMultilinear (d : Fin n → ℤ) (q : ℤ) :=
  MultilinearMap R (fun i : Fin n ↦ grHom R (X i.succ) (X i.castSucc) (d i))
    (grHom R (X (Fin.last n)) (X 0) ((∑ i, d i) + q))

/-- A degree-`q` operation on a composable string, specified on every tuple of input degrees.
All data are used: there is one component for each tuple and no choice of degree casts. -/
abbrev PathOperation (q : ℤ) := ∀ d : Fin n → ℤ, PathMultilinear R X d q

/-- Homogeneous multilinear operations on the total Hom modules of a composable string. -/
abbrev HomogeneousPathOperation (q : ℤ) :=
  TauCeti.MultilinearMap.homogeneousSubmodule (R := R) (S := R)
    (fun i : Fin n ↦ (grading (R := R) (X i.succ) (X i.castSucc)).piece)
    (grading (R := R) (X (Fin.last n)) (X 0)).piece q

/-- Restriction to homogeneous pieces identifies total homogeneous operations with degreewise
path operations. Its inverse is the unique multilinear extension to total Hom modules. -/
noncomputable def pathOperationEquiv (q : ℤ) :
    HomogeneousPathOperation R X q ≃ₗ[R] PathOperation R X q :=
  InternalGrading.homogeneousMultilinearEquiv
    (fun i : Fin n ↦ grading (R := R) (X i.succ) (X i.castSucc))
    (grading (R := R) (X (Fin.last n)) (X 0)).piece q

/-- Restricting a total path operation evaluates it on the underlying homogeneous inputs. -/
@[simp]
theorem coe_pathOperationEquiv_apply (q : ℤ) (f : HomogeneousPathOperation R X q)
    (d : Fin n → ℤ) (x : ∀ i, grHom R (X i.succ) (X i.castSucc) (d i)) :
    (pathOperationEquiv R X q f d x : homModule (R := R) (X (Fin.last n)) (X 0)) =
      f.val (fun i ↦ (x i : homModule (R := R) (X i.succ) (X i.castSucc))) := by
  exact InternalGrading.coe_homogeneousMultilinearEquiv_apply _ _ q f d x

/-- Extending degreewise path operations recovers their values on homogeneous inputs. -/
@[simp]
theorem pathOperationEquiv_symm_apply (q : ℤ) (f : PathOperation R X q)
    (d : Fin n → ℤ) (x : ∀ i, grHom R (X i.succ) (X i.castSucc) (d i)) :
    ((pathOperationEquiv R X q).symm f).val
        (fun i ↦ (x i : homModule (R := R) (X i.succ) (X i.castSucc))) =
      (f d x : homModule (R := R) (X (Fin.last n)) (X 0)) := by
  exact InternalGrading.homogeneousMultilinearEquiv_symm_apply _ _ q f d x

end TauCeti.GradedLinearQuiver
