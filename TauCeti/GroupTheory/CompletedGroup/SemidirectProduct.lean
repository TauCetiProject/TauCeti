/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.GroupTheory.CompletedGroup.Map
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Completing semidirect products with a fixed acting group

Suppose a monoid `H` acts by automorphisms on each group of a tower, compatibly with
its transitions. The action extends to the completed group. When `H` is a group,
forming the semidirect product with `H` commutes with completion, provided the
transitions leave the `H` coordinate fixed.
The comparison and its inverse are characterized by their finite projections.
Thus a compatible family of elements of `Gₖ ⋊ H` has a single, constant `H`-coordinate.

The construction uses `CompletedGroup.congr`, `CompletedGroup.lift`, and Mathlib's
`SemidirectProduct.map`.
No surjectivity of the tower transitions or finiteness of either group is required.

## Attribution

Adapted from `Mei/GroupTheory/CompletedGroup/SemidirectProduct.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), at
`9cf969cdee9748087aae45dbf4888a130890655c` (Apache 2.0).
Original author credit is retained; the file uses the requested Tau Ceti copyright header.
-/

public section

open CategoryTheory Opposite

universe u v

namespace TauCeti.CompletedGroup

variable {F : ℕᵒᵖ ⥤ GrpCat.{u}} {H : Type v}

section Action

variable [Monoid H]
  (φ : ∀ j, H →* MulAut (F.obj j))
  (hφ : ∀ {j l} (f : j ⟶ l) (h : H) (x : F.obj j),
    F.map f (φ j h x) = φ l h (F.map f x))

/-- The compatible levelwise automorphisms give an action on the completed group. -/
def action : H →* MulAut (completedGroup F) where
  toFun h := congr (NatIso.ofComponents (fun j => (φ j h).toGrpIso) (by
    intro j l f
    ext x
    exact (hφ f h x).symm))
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply ext
    intro k
    simp [projection_congr]
  map_mul' h h' := by
    apply MulEquiv.ext
    intro x
    apply ext
    intro k
    simp [projection_congr, MulAut.mul_apply]

/-- The completed action is computed by the action at each finite order. -/
@[simp]
theorem projection_action (h : H) (x : completedGroup F) (k : ℕ) :
    projection k (action φ hφ h x) = φ (op k) h (projection k x) := by
  exact projection_congr _ k x

end Action

variable [Group H]
  (φ : ∀ j, H →* MulAut (F.obj j))
  (hφ : ∀ {j l} (f : j ⟶ l) (h : H) (x : F.obj j),
    F.map f (φ j h x) = φ l h (F.map f x))

/-- The tower of semidirect products, with transitions fixing the acting group. -/
abbrev semidirectTower : ℕᵒᵖ ⥤ GrpCat.{max u v} where
  obj j := GrpCat.of (F.obj j ⋊[φ j] H)
  map f := GrpCat.ofHom (SemidirectProduct.map (F.map f).hom (MonoidHom.id H)
    (fun h => by ext x; exact hφ f h x))
  map_id j := by
    ext x <;> simp
  map_comp f g := by
    ext x
    · exact ConcreteCategory.congr_hom (F.map_comp f g) x.left
    · rfl

/-- Projection from the completed semidirect product to one finite semidirect product. -/
def semidirectProjection (k : ℕ) :
    (completedGroup F ⋊[action φ hφ] H) →* F.obj (op k) ⋊[φ (op k)] H :=
  SemidirectProduct.map (projection k) (MonoidHom.id H)
    (fun h => by ext x; exact projection_action φ hφ h x k)

/-- The left coordinate of a projected element is the projection of its left coordinate. -/
@[simp]
theorem semidirectProjection_left (k : ℕ) (x : completedGroup F ⋊[action φ hφ] H) :
    (semidirectProjection φ hφ k x).left = projection k x.left := (rfl)

/-- Projection preserves the `H`-coordinate. -/
@[simp]
theorem semidirectProjection_right (k : ℕ) (x : completedGroup F ⋊[action φ hφ] H) :
    (semidirectProjection φ hφ k x).right = x.right := (rfl)

private def assemble : (completedGroup F ⋊[action φ hφ] H) →*
    completedGroup (semidirectTower φ hφ) :=
  lift (semidirectProjection φ hφ) (by
    intro k l hkl
    ext x <;> simp)

private theorem projection_assemble (x : completedGroup F ⋊[action φ hφ] H) (k : ℕ) :
    projection k (assemble φ hφ x) = semidirectProjection φ hφ k x :=
  projection_lift _ _ k x

/-- All finite projections of an element of the completed semidirect tower have the same
`H`-coordinate. -/
@[simp]
theorem projection_right_eq_projection_zero (x : completedGroup (semidirectTower φ hφ)) (k : ℕ) :
    (projection k x).right = (projection 0 x).right := by
  have hx := congrArg SemidirectProduct.right (map_projection 0 k (Nat.zero_le k) x)
  simpa only [ConcreteCategory.hom_ofHom, SemidirectProduct.map_right,
    MonoidHom.id_apply] using hx

private def leftPart (x : completedGroup (semidirectTower φ hφ)) : completedGroup F :=
  ⟨fun k => (projection k x).left, (mem_completedGroup_iff F _).mpr (by
    intro k l hkl
    have hx := congrArg SemidirectProduct.left (map_projection k l hkl x)
    simpa only [ConcreteCategory.hom_ofHom, SemidirectProduct.map_left] using hx)⟩

private theorem projection_leftPart (x : completedGroup (semidirectTower φ hφ)) (k : ℕ) :
    projection k (leftPart φ hφ x) = (projection k x).left := by
  rw [projection_apply]
  rfl

/-- Completion commutes with semidirect product by a fixed acting group. The left
coordinate is completed, while the acting-group coordinate is constant through the tower. -/
def semidirectProductEquiv : completedGroup (semidirectTower φ hφ) ≃*
    (completedGroup F ⋊[action φ hφ] H) where
  toFun x := ⟨leftPart φ hφ x, (projection 0 x).right⟩
  invFun := assemble φ hφ
  left_inv x := by
    apply ext
    intro k
    apply SemidirectProduct.ext
    · rw [projection_assemble φ hφ, semidirectProjection_left, projection_leftPart]
    · rw [projection_assemble, semidirectProjection_right]
      exact (projection_right_eq_projection_zero φ hφ x k).symm
  right_inv x := by
    apply SemidirectProduct.ext
    · apply ext
      intro k
      rw [projection_leftPart, projection_assemble φ hφ, semidirectProjection_left]
    · dsimp only
      rw [projection_assemble φ hφ, semidirectProjection_right]
  map_mul' x y := by
    apply SemidirectProduct.ext
    · apply ext
      intro k
      simp only [projection_leftPart, map_mul, SemidirectProduct.mul_left, projection_action]
      rw [projection_right_eq_projection_zero]
    · simp

/-- The first coordinate of the comparison is the compatible family of first coordinates. -/
@[simp]
theorem projection_semidirectProductEquiv_left
    (x : completedGroup (semidirectTower φ hφ)) (k : ℕ) :
    projection k (semidirectProductEquiv φ hφ x).left = (projection k x).left :=
  projection_leftPart φ hφ x k

/-- The fixed acting-group coordinate can be read at order zero. -/
@[simp]
theorem semidirectProductEquiv_right (x : completedGroup (semidirectTower φ hφ)) :
    (semidirectProductEquiv φ hφ x).right = (projection 0 x).right := (rfl)

/-- Each finite projection of the forward comparison is the original projection. -/
@[simp]
theorem semidirectProjection_semidirectProductEquiv
    (x : completedGroup (semidirectTower φ hφ)) (k : ℕ) :
    semidirectProjection φ hφ k (semidirectProductEquiv φ hφ x) = projection k x := by
  apply SemidirectProduct.ext
  · simp
  · simpa using (projection_right_eq_projection_zero φ hφ x k).symm

/-- Each finite projection of the inverse comparison is `semidirectProjection`. -/
@[simp]
theorem projection_semidirectProductEquiv_symm
    (x : completedGroup F ⋊[action φ hφ] H) (k : ℕ) :
    projection k ((semidirectProductEquiv φ hφ).symm x) =
      semidirectProjection φ hφ k x :=
  projection_assemble φ hφ x k

end TauCeti.CompletedGroup
