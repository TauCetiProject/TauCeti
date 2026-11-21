/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearMap.Multilinear

/-!
# Alternating bilinear maps and two-forms

The alternating bilinear maps form a submodule of the bilinear maps. The linear equivalence
`TauCeti.alternatingBilinMapEquiv` identifies this submodule with alternating maps on `Fin 2`,
without multiplying by two. It packages the inverse conversions
`LinearMap.IsAlt.toAlternatingMap` and `MultilinearMap.toBilinMap`.

Pullback applies the same linear map in both arguments. The equivalence commutes with pullback,
so identities between bilinear forms can be used as identities between two-forms. In particular,
this is the algebraic comparison needed to read a symplectic bilinear form as a two-form.
-/

public section

variable (R V N : Type*) [CommSemiring R] [AddCommMonoid V] [Module R V]
  [AddCommMonoid N] [Module R N]

namespace TauCeti

/-- The submodule of bilinear maps that vanish on every pair of equal arguments. -/
def alternatingBilinMap : Submodule R (V →ₗ[R] V →ₗ[R] N) where
  carrier := {B | B.IsAlt}
  zero_mem' := fun _ ↦ rfl
  add_mem' hB hC := fun x ↦ by simp [hB.self_eq_zero x, hC.self_eq_zero x]
  smul_mem' a B hB := fun x ↦ by simp [hB.self_eq_zero x]

variable {R V N}

/-- Membership in the alternating submodule is the usual alternating condition. -/
@[simp]
theorem mem_alternatingBilinMap (B : V →ₗ[R] V →ₗ[R] N) :
    B ∈ alternatingBilinMap R V N ↔ B.IsAlt :=
  (Iff.rfl)

variable (R V N)

/-- Alternating bilinear maps and alternating two-forms carry the same data.
Unlike alternatization, this identification introduces no factor of two. -/
def alternatingBilinMapEquiv : alternatingBilinMap R V N ≃ₗ[R] V [⋀^Fin 2]→ₗ[R] N where
  toFun B := ((mem_alternatingBilinMap _).mp B.property).toAlternatingMap
  invFun A := ⟨A.toMultilinearMap.toBilinMap,
    (mem_alternatingBilinMap _).mpr A.isAlt_toBilinMap⟩
  left_inv B := Subtype.ext
    ((mem_alternatingBilinMap _).mp B.property).toBilinMap_toAlternatingMap
  right_inv A := A.toAlternatingMap_isAlt_toBilinMap
  map_add' B C := by ext v; simp [LinearMap.IsAlt.toAlternatingMap_apply]
  map_smul' a B := by ext v; simp [LinearMap.IsAlt.toAlternatingMap_apply]

variable {R V N}

/-- The two-form corresponding to `B` evaluates to `B (v 0) (v 1)`. -/
@[simp]
theorem alternatingBilinMapEquiv_apply (B : alternatingBilinMap R V N) (v : Fin 2 → V) :
    alternatingBilinMapEquiv R V N B v = B.val (v 0) (v 1) :=
  ((mem_alternatingBilinMap _).mp B.property).toAlternatingMap_apply v

/-- The bilinear map corresponding to a two-form evaluates it on the ordered pair. -/
@[simp]
theorem alternatingBilinMapEquiv_symm_apply (A : V [⋀^Fin 2]→ₗ[R] N) (x y : V) :
    ((alternatingBilinMapEquiv R V N).symm A).val x y = A ![x, y] :=
  MultilinearMap.toBilinMap_apply _ x y

end TauCeti

namespace LinearMap

open TauCeti

variable {R V N} {W U : Type*} [AddCommMonoid W] [Module R W] [AddCommMonoid U] [Module R U]

/-- Pullback of an alternating bilinear map, applying `L` in both arguments. -/
def alternatingBilinMapPullback (L : W →ₗ[R] V) :
    alternatingBilinMap R V N →ₗ[R] alternatingBilinMap R W N where
  toFun B := ⟨B.val.compl₁₂ L L, fun x ↦ B.property (L x)⟩
  map_add' B C := by apply Subtype.ext; ext x y; rfl
  map_smul' a B := by apply Subtype.ext; ext x y; rfl

/-- Evaluation of the pullback on an ordered pair. -/
@[simp]
theorem alternatingBilinMapPullback_apply (L : W →ₗ[R] V)
    (B : alternatingBilinMap R V N) (x y : W) :
    (alternatingBilinMapPullback L B).val x y = B.val (L x) (L y) :=
  (rfl)

/-- Pullback by the identity is the identity. -/
@[simp]
theorem _root_.TauCeti.alternatingBilinMapPullback_id :
    alternatingBilinMapPullback (N := N) (LinearMap.id : V →ₗ[R] V) = LinearMap.id := by
  ext B x y
  rfl

/-- Pullbacks compose contravariantly. -/
theorem alternatingBilinMapPullback_comp (L : W →ₗ[R] V) (K : U →ₗ[R] W) :
    alternatingBilinMapPullback (N := N) (L.comp K) =
      (alternatingBilinMapPullback K).comp (alternatingBilinMapPullback L) := by
  ext B x y
  rfl

/-- The identification of alternating bilinear maps with two-forms commutes with pullback. -/
@[simp]
theorem alternatingBilinMapEquiv_pullback (L : W →ₗ[R] V) (B : alternatingBilinMap R V N) :
    alternatingBilinMapEquiv R W N (alternatingBilinMapPullback L B) =
      (alternatingBilinMapEquiv R V N B).compLinearMap L := by
  ext v
  simp

end LinearMap
