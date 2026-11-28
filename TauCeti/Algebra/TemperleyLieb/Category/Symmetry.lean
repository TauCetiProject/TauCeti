/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.Category
import Mathlib.LinearAlgebra.Basis.Bilinear

/-!
# Symmetries and corner-dragging on morphisms of `TLCat R δ`

This file lifts the planar-matching symmetries of Temperley–Lieb diagrams linearly to morphism
modules of the linear Temperley–Lieb category `TauCeti.TLCat R δ` over a commutative ring `R` at
loop value `δ : R`:

* `TauCeti.TLCat.dragRight`, `TauCeti.TLCat.dragLeft`: dragging the bottom-right or bottom-left
  boundary point up to the top boundary, yielding linear equivalences
  `((of (n + 1) : TLCat R δ) ⟶ of m) ≃ₗ[R] (of n ⟶ of (m + 1))`.
* `TauCeti.TLCat.rotateHom`: counterclockwise rotation of the `n + m` boundary points as a linear
  automorphism of `(of n : TLCat R δ) ⟶ of m` of order dividing `n + m`
  (`TauCeti.TLCat.rotateHom_iterate_self`).
* `TauCeti.TLCat.verticalReflectHom`: vertical reflection (turning a diagram upside down) as a
  linear equivalence `((of n : TLCat R δ) ⟶ of m) ≃ₗ[R] (of m ⟶ of n)`, swapping `cup` and `cap`
  and fixing `𝟙 (of n)`. The composition law `TauCeti.TLCat.verticalReflectHom_comp` lifts
  `TauCeti.TLDiagram.verticalReflect_comp` using Mathlib’s `LinearMap.ext_basis` on
  `TauCeti.TLCat.diagBasis`.
* `TauCeti.TLCat.reflectHom`: horizontal (left–right) reflection as a linear involution of
  `(of n : TLCat R δ) ⟶ of m`, commuting with `verticalReflectHom` and intertwining `dragRight`
  with `dragLeft`.

All five equivalences are compatible with `TauCeti.TLCat.linearize R δ` and the underlying diagram
operations on `TauCeti.TLDiagram`.

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845, §2.
-/

public section

open CategoryTheory

namespace TauCeti.TLCat

universe u

variable {R : Type u} [CommRing R] {δ : R}

/-! ### Corner-dragging and rotation linear equivalences -/

/-- **Dragging the bottom-right corner up**, lifted linearly to morphism modules of `TLCat R δ`. -/
noncomputable def dragRight (n m : ℕ) :
    ((of (n + 1) : TLCat R δ) ⟶ of m) ≃ₗ[R] ((of n : TLCat R δ) ⟶ of (m + 1)) :=
  (diagBasis (of (n + 1)) (of m)).equiv (diagBasis (of n) (of (m + 1)))
    (PlanarMatching.cast (Nat.add_right_comm n 1 m))

@[simp]
theorem dragRight_diagBasis (n m : ℕ) (x : PlanarMatching (n + 1 + m)) :
    dragRight (R := R) (δ := δ) n m (diagBasis (of (n + 1)) (of m) x) =
      diagBasis (of n) (of (m + 1)) (PlanarMatching.cast (Nat.add_right_comm n 1 m) x) := by
  simp [dragRight]

@[simp]
theorem dragRight_symm_diagBasis (n m : ℕ) (x : PlanarMatching (n + (m + 1))) :
    (dragRight (R := R) (δ := δ) n m).symm (diagBasis (of n) (of (m + 1)) x) =
      diagBasis (of (n + 1)) (of m) (PlanarMatching.cast (Nat.add_right_comm n 1 m).symm x) := by
  simp [dragRight]

@[simp]
theorem dragRight_linearize_map (n m : ℕ) (f : TLDiagCat.of (n + 1) ⟶ .of m) :
    dragRight (R := R) (δ := δ) n m ((linearize R δ).map f) =
      (linearize R δ).map (TLDiagCat.Hom.mk (TLDiagram.dragRight n m f.diagram)) := by
  rw [linearize_map, map_smul, dragRight_diagBasis]
  simp [linearize_map]

/-- **Dragging the bottom-left corner up**, lifted linearly to morphism modules of `TLCat R δ`. -/
noncomputable def dragLeft (n m : ℕ) :
    ((of (n + 1) : TLCat R δ) ⟶ of m) ≃ₗ[R] ((of n : TLCat R δ) ⟶ of (m + 1)) :=
  (diagBasis (of (n + 1)) (of m)).equiv (diagBasis (of n) (of (m + 1)))
    ((PlanarMatching.rotate (n + 1 + m)).symm.trans
      (PlanarMatching.cast (Nat.add_right_comm n 1 m)))

@[simp]
theorem dragLeft_diagBasis (n m : ℕ) (x : PlanarMatching (n + 1 + m)) :
    dragLeft (R := R) (δ := δ) n m (diagBasis (of (n + 1)) (of m) x) =
      diagBasis (of n) (of (m + 1))
        (PlanarMatching.cast (Nat.add_right_comm n 1 m)
          ((PlanarMatching.rotate (n + 1 + m)).symm x)) := by
  simp [dragLeft]

@[simp]
theorem dragLeft_symm_diagBasis (n m : ℕ) (x : PlanarMatching (n + (m + 1))) :
    (dragLeft (R := R) (δ := δ) n m).symm (diagBasis (of n) (of (m + 1)) x) =
      diagBasis (of (n + 1)) (of m)
        (PlanarMatching.rotate (n + 1 + m)
          (PlanarMatching.cast (Nat.add_right_comm n 1 m).symm x)) := by
  simp [dragLeft]

@[simp]
theorem dragLeft_linearize_map (n m : ℕ) (f : TLDiagCat.of (n + 1) ⟶ .of m) :
    dragLeft (R := R) (δ := δ) n m ((linearize R δ).map f) =
      (linearize R δ).map (TLDiagCat.Hom.mk (TLDiagram.dragLeft n m f.diagram)) := by
  rw [linearize_map, map_smul, dragLeft_diagBasis]
  simp [linearize_map]

/-- **Counterclockwise rotation** of boundary points, lifted linearly to a module automorphism of
`(of n : TLCat R δ) ⟶ of m`. -/
noncomputable def rotateHom (n m : ℕ) :
    ((of n : TLCat R δ) ⟶ of m) ≃ₗ[R] ((of n : TLCat R δ) ⟶ of m) :=
  (diagBasis (of n) (of m)).equiv (diagBasis (of n) (of m)) (PlanarMatching.rotate (n + m))

@[simp]
theorem rotateHom_diagBasis (n m : ℕ) (x : PlanarMatching (n + m)) :
    rotateHom (R := R) (δ := δ) n m (diagBasis (of n) (of m) x) =
      diagBasis (of n) (of m) (PlanarMatching.rotate (n + m) x) := by
  simp [rotateHom]

@[simp]
theorem rotateHom_symm_diagBasis (n m : ℕ) (x : PlanarMatching (n + m)) :
    (rotateHom (R := R) (δ := δ) n m).symm (diagBasis (of n) (of m) x) =
      diagBasis (of n) (of m) ((PlanarMatching.rotate (n + m)).symm x) := by
  simp [rotateHom]

@[simp]
theorem rotateHom_linearize_map (n m : ℕ) (f : TLDiagCat.of n ⟶ .of m) :
    rotateHom (R := R) (δ := δ) n m ((linearize R δ).map f) =
      (linearize R δ).map (TLDiagCat.Hom.mk (TLDiagram.rotate n m f.diagram)) := by
  rw [linearize_map, map_smul, rotateHom_diagBasis]
  simp [linearize_map]

/-- Rotating once counterclockwise and then dragging the bottom-left corner up equals dragging the
bottom-right corner up, as linear equivalences on morphism modules. -/
theorem rotateHom_trans_dragLeft (n m : ℕ) :
    (rotateHom (R := R) (δ := δ) (n + 1) m).trans (dragLeft n m) = dragRight n m := by
  rw [rotateHom, dragLeft, dragRight, Module.Basis.equiv_trans]
  congr 1
  ext x
  simp

@[simp]
theorem dragLeft_rotateHom (n m : ℕ) (f : (of (n + 1) : TLCat R δ) ⟶ of m) :
    dragLeft n m (rotateHom (n + 1) m f) = dragRight n m f :=
  LinearEquiv.congr_fun (rotateHom_trans_dragLeft n m) f

private theorem rotateHom_iterate_eq_equiv (n m k : ℕ) (f : (of n : TLCat R δ) ⟶ of m) :
    (rotateHom n m)^[k] f =
      (diagBasis (of n) (of m)).equiv (diagBasis (of n) (of m))
        (PlanarMatching.rotate (n + m) ^ k) f := by
  induction k with
  | zero =>
    rw [Function.iterate_zero_apply, pow_zero, Equiv.Perm.one_def, Module.Basis.equiv_refl,
      LinearEquiv.refl_apply]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    have heq :
        ((diagBasis (of n : TLCat R δ) (of m)).equiv (diagBasis (of n : TLCat R δ) (of m))
          (PlanarMatching.rotate (n + m) ^ k)).trans (rotateHom n m) =
        (diagBasis (of n : TLCat R δ) (of m)).equiv (diagBasis (of n : TLCat R δ) (of m))
          (PlanarMatching.rotate (n + m) ^ (k + 1)) := by
      rw [rotateHom, Module.Basis.equiv_trans]
      congr 1
      refine Equiv.ext fun x => ?_
      simp [pow_succ', Equiv.Perm.mul_apply]
    exact LinearEquiv.congr_fun heq f

/-- Rotating `n + m` times around the boundary of `of n ⟶ of m` is the identity. -/
@[simp]
theorem rotateHom_iterate_self (n m : ℕ) (f : (of n : TLCat R δ) ⟶ of m) :
    (rotateHom n m)^[n + m] f = f := by
  rw [rotateHom_iterate_eq_equiv, PlanarMatching.rotate_pow_self, Equiv.Perm.one_def,
    Module.Basis.equiv_refl, LinearEquiv.refl_apply]

theorem dragRight_id_one :
    dragRight 0 1 (𝟙 (of 1 : TLCat R δ)) = (cup : (of 0 : TLCat R δ) ⟶ of 2) := by
  rw [id_eq_diagBasis, dragRight_diagBasis, cup_eq_diagBasis]
  exact congrArg (diagBasis (of 0 : TLCat R δ) (of 2))
    (by simpa using congrArg TLDiagram.matching TLDiagram.dragRight_id_one)

theorem dragLeft_id_one :
    dragLeft 0 1 (𝟙 (of 1 : TLCat R δ)) = (cup : (of 0 : TLCat R δ) ⟶ of 2) := by
  rw [id_eq_diagBasis, dragLeft_diagBasis, cup_eq_diagBasis]
  exact congrArg (diagBasis (of 0 : TLCat R δ) (of 2))
    (by simpa using congrArg TLDiagram.matching TLDiagram.dragLeft_id_one)

theorem dragRight_symm_id_one :
    (dragRight 1 0).symm (𝟙 (of 1 : TLCat R δ)) = (cap : (of 2 : TLCat R δ) ⟶ of 0) := by
  rw [id_eq_diagBasis, dragRight_symm_diagBasis, cap_eq_diagBasis]
  exact congrArg (diagBasis (of 2 : TLCat R δ) (of 0))
    (by simpa using congrArg TLDiagram.matching TLDiagram.dragRight_symm_id_one)

/-! ### Vertical and horizontal reflection linear equivalences -/

/-- **Vertical reflection** (turning a diagram upside down), lifted linearly to morphism modules
`((of n : TLCat R δ) ⟶ of m) ≃ₗ[R] (of m ⟶ of n)`. -/
noncomputable def verticalReflectHom (n m : ℕ) :
    ((of n : TLCat R δ) ⟶ of m) ≃ₗ[R] ((of m : TLCat R δ) ⟶ of n) :=
  (diagBasis (of n) (of m)).equiv (diagBasis (of m) (of n))
    ((PlanarMatching.reflect (n + m)).trans (PlanarMatching.cast (Nat.add_comm n m)))

@[simp]
theorem verticalReflectHom_diagBasis (n m : ℕ) (x : PlanarMatching (n + m)) :
    verticalReflectHom (R := R) (δ := δ) n m (diagBasis (of n) (of m) x) =
      diagBasis (of m) (of n)
        (PlanarMatching.cast (Nat.add_comm n m) (PlanarMatching.reflect (n + m) x)) := by
  simp [verticalReflectHom]

@[simp]
theorem verticalReflectHom_linearize_map (n m : ℕ) (f : TLDiagCat.of n ⟶ .of m) :
    verticalReflectHom (R := R) (δ := δ) n m ((linearize R δ).map f) =
      (linearize R δ).map (TLDiagCat.Hom.mk (TLDiagram.verticalReflect n m f.diagram)) := by
  rw [linearize_map, map_smul, verticalReflectHom_diagBasis]
  simp [linearize_map]

theorem verticalReflectHom_trans_verticalReflectHom (n m : ℕ) :
    (verticalReflectHom (R := R) (δ := δ) n m).trans (verticalReflectHom m n) =
      LinearEquiv.refl R _ := by
  rw [verticalReflectHom, verticalReflectHom, Module.Basis.equiv_trans,
    ← Module.Basis.equiv_refl (diagBasis (of n) (of m))]
  congr 1
  refine Equiv.ext fun x => ?_
  have h := congrArg TLDiagram.matching
    (TLDiagram.verticalReflect_verticalReflect (⟨x, 0⟩ : TLDiagram n m))
  simpa only [TLDiagram.matching_verticalReflect, Equiv.trans_apply, Equiv.refl_apply] using h

@[simp]
theorem verticalReflectHom_verticalReflectHom (n m : ℕ) (f : (of n : TLCat R δ) ⟶ of m) :
    verticalReflectHom m n (verticalReflectHom n m f) = f :=
  LinearEquiv.congr_fun (verticalReflectHom_trans_verticalReflectHom n m) f

@[simp]
theorem verticalReflectHom_symm (n m : ℕ) :
    (verticalReflectHom (R := R) (δ := δ) n m).symm = verticalReflectHom m n :=
  LinearEquiv.ext fun f =>
    (LinearEquiv.symm_apply_eq _).mpr (verticalReflectHom_verticalReflectHom m n f).symm

@[simp]
theorem verticalReflectHom_id (n : ℕ) :
    verticalReflectHom n n (𝟙 (of n : TLCat R δ)) = 𝟙 (of n : TLCat R δ) := by
  rw [id_eq_diagBasis, verticalReflectHom_diagBasis]
  have h := congrArg TLDiagram.matching (TLDiagram.verticalReflect_id n)
  rw [TLDiagram.matching_verticalReflect, TLDiagram.matching_id] at h
  exact congrArg (diagBasis (of n : TLCat R δ) (of n)) h

/-- Vertical reflection reverses composition of linear Temperley–Lieb morphisms.
The underlying diagram reflection is Chen, Definition 2.1.5. -/
@[simp]
theorem verticalReflectHom_comp {n m p : ℕ}
    (f : (of n : TLCat R δ) ⟶ of m) (g : (of m : TLCat R δ) ⟶ of p) :
    verticalReflectHom n p (f ≫ g) =
      verticalReflectHom m p g ≫ verticalReflectHom n m f := by
  let X : TLCat R δ := of n
  let Y : TLCat R δ := of m
  let Z : TLCat R δ := of p
  -- Compare the two bilinear maps on the images of diagrams without circles.
  let reflectAfter := (Linear.comp (S := R) X Y Z).compr₂
    (verticalReflectHom n p).toLinearMap
  let reflectBefore := (Linear.comp (S := R) Z Y X).flip.compl₁₂
    (verticalReflectHom n m).toLinearMap (verticalReflectHom m p).toLinearMap
  suffices h : reflectAfter = reflectBefore from LinearMap.ext_iff₂.mp h f g
  apply LinearMap.ext_basis (diagBasis X Y) (diagBasis Y Z)
  intro x y
  simp only [reflectAfter, reflectBefore, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply,
    LinearMap.flip_apply, Linear.comp_apply, Linear.leftComp_apply, LinearEquiv.coe_coe]
  rw [diagBasis_eq_linearize_map, diagBasis_eq_linearize_map, ← Functor.map_comp]
  -- Compare the two reflected stacks before linearizing.
  rw [verticalReflectHom_linearize_map, verticalReflectHom_linearize_map,
    verticalReflectHom_linearize_map, ← Functor.map_comp]
  refine congrArg (linearize R δ).map (TLDiagCat.hom_ext ?_)
  simp only [TLDiagCat.diagram_comp, TLDiagram.verticalReflect_comp, Y]

@[simp]
theorem verticalReflectHom_cup :
    verticalReflectHom 0 2 (cup : (of 0 : TLCat R δ) ⟶ of 2) = cap := by
  rw [cup_eq_diagBasis, verticalReflectHom_diagBasis, cap_eq_diagBasis]
  have h := congrArg TLDiagram.matching TLDiagram.verticalReflect_cup
  rw [TLDiagram.matching_verticalReflect] at h
  exact congrArg (diagBasis (of 2 : TLCat R δ) (of 0)) h

@[simp]
theorem verticalReflectHom_cap :
    verticalReflectHom 2 0 (cap : (of 2 : TLCat R δ) ⟶ of 0) = cup := by
  rw [cap_eq_diagBasis, verticalReflectHom_diagBasis, cup_eq_diagBasis]
  have h := congrArg TLDiagram.matching TLDiagram.verticalReflect_cap
  rw [TLDiagram.matching_verticalReflect] at h
  exact congrArg (diagBasis (of 0 : TLCat R δ) (of 2)) h

/-- **Horizontal (left–right) reflection**, lifted linearly to a module involution of
`(of n : TLCat R δ) ⟶ of m`. -/
noncomputable def reflectHom (n m : ℕ) :
    ((of n : TLCat R δ) ⟶ of m) ≃ₗ[R] ((of n : TLCat R δ) ⟶ of m) :=
  (diagBasis (of n) (of m)).equiv (diagBasis (of n) (of m))
    ((PlanarMatching.reflect (n + m)).trans (PlanarMatching.rotate (n + m) ^ n))

@[simp]
theorem reflectHom_diagBasis (n m : ℕ) (x : PlanarMatching (n + m)) :
    reflectHom (R := R) (δ := δ) n m (diagBasis (of n) (of m) x) =
      diagBasis (of n) (of m)
        ((PlanarMatching.rotate (n + m) ^ n) (PlanarMatching.reflect (n + m) x)) := by
  simp [reflectHom]

@[simp]
theorem reflectHom_linearize_map (n m : ℕ) (f : TLDiagCat.of n ⟶ .of m) :
    reflectHom (R := R) (δ := δ) n m ((linearize R δ).map f) =
      (linearize R δ).map (TLDiagCat.Hom.mk (TLDiagram.reflect n m f.diagram)) := by
  rw [linearize_map, map_smul, reflectHom_diagBasis]
  simp [linearize_map]

theorem reflectHom_trans_reflectHom (n m : ℕ) :
    (reflectHom (R := R) (δ := δ) n m).trans (reflectHom n m) = LinearEquiv.refl R _ := by
  rw [reflectHom, Module.Basis.equiv_trans, ← Module.Basis.equiv_refl (diagBasis (of n) (of m))]
  congr 1
  refine Equiv.ext fun x => ?_
  have h := congrArg TLDiagram.matching (TLDiagram.reflect_reflect (⟨x, 0⟩ : TLDiagram n m))
  simpa only [TLDiagram.matching_reflect, Equiv.trans_apply, Equiv.refl_apply] using h

@[simp]
theorem reflectHom_reflectHom (n m : ℕ) (f : (of n : TLCat R δ) ⟶ of m) :
    reflectHom n m (reflectHom n m f) = f :=
  LinearEquiv.congr_fun (reflectHom_trans_reflectHom n m) f

@[simp]
theorem reflectHom_symm (n m : ℕ) :
    (reflectHom (R := R) (δ := δ) n m).symm = reflectHom n m :=
  LinearEquiv.ext fun f =>
    (LinearEquiv.symm_apply_eq _).mpr (reflectHom_reflectHom n m f).symm

theorem verticalReflectHom_trans_reflectHom (n m : ℕ) :
    (verticalReflectHom (R := R) (δ := δ) n m).trans (reflectHom m n) =
      (reflectHom n m).trans (verticalReflectHom n m) := by
  rw [verticalReflectHom, reflectHom, reflectHom, Module.Basis.equiv_trans,
    Module.Basis.equiv_trans]
  congr 1
  refine Equiv.ext fun x => ?_
  have h := congrArg TLDiagram.matching
    (TLDiagram.reflect_verticalReflect (⟨x, 0⟩ : TLDiagram n m))
  simpa only [TLDiagram.matching_reflect, TLDiagram.matching_verticalReflect,
    Equiv.trans_apply] using h

theorem reflectHom_verticalReflectHom (n m : ℕ) (f : (of n : TLCat R δ) ⟶ of m) :
    reflectHom m n (verticalReflectHom n m f) =
      verticalReflectHom n m (reflectHom n m f) :=
  LinearEquiv.congr_fun (verticalReflectHom_trans_reflectHom n m) f

theorem dragRight_trans_reflectHom (n m : ℕ) :
    (dragRight (R := R) (δ := δ) n m).trans (reflectHom n (m + 1)) =
      (reflectHom (n + 1) m).trans (dragLeft n m) := by
  rw [dragRight, reflectHom, reflectHom, dragLeft, Module.Basis.equiv_trans,
    Module.Basis.equiv_trans]
  congr 1
  refine Equiv.ext fun x => ?_
  have h := congrArg TLDiagram.matching
    (TLDiagram.reflect_dragRight (⟨x, 0⟩ : TLDiagram (n + 1) m))
  simpa only [TLDiagram.matching_reflect, TLDiagram.matching_dragRight,
    TLDiagram.matching_dragLeft, Equiv.trans_apply] using h

theorem reflectHom_dragRight (n m : ℕ) (f : (of (n + 1) : TLCat R δ) ⟶ of m) :
    reflectHom n (m + 1) (dragRight n m f) = dragLeft n m (reflectHom (n + 1) m f) :=
  LinearEquiv.congr_fun (dragRight_trans_reflectHom n m) f

end TauCeti.TLCat
