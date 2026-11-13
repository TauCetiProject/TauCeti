/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Symmetrized
public import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Tactic.Module

/-!
# Jordan star maps

Jordan star maps are complex linear maps preserving adjoints and self-adjoint squares.
Polarization identifies their product law with multiplication in Mathlib's `SymAlg`.
Unitality is separate, but follows from surjectivity. Open `scoped TauCeti` to obtain
the scalar-induced inverse of two for `SymAlg` multiplication.
-/

public section

namespace TauCeti
variable (A B : Type*) [Ring A] [StarRing A] [Algebra ℂ A]
  [Ring B] [StarRing B] [Algebra ℂ B]

/-- The inverse of two in a complex algebra, transported from the scalar inverse. -/
noncomputable scoped instance invertibleTwo : Invertible (2 : A) :=
  letI : Invertible (2 : ℂ) := invertibleOfNonzero two_ne_zero
  (Invertible.map (algebraMap ℂ A) (2 : ℂ)).copy 2 ((map_ofNat (algebraMap ℂ A) 2).symm)

/-- A complex linear, adjoint-preserving map preserving squares of self-adjoint elements. -/
structure JordanStarMap extends A →ₗ[ℂ] B where
  map_star' (x : A) : toLinearMap (star x) = star (toLinearMap x)
  map_sq' (x : A) : IsSelfAdjoint x → toLinearMap (x * x) = toLinearMap x * toLinearMap x

open scoped TauCeti
variable {A B}

namespace JordanStarMap

instance : FunLike (JordanStarMap A B) A B where
  coe f := f.toLinearMap
  coe_injective f g h := by cases f; cases g; congr; exact DFunLike.coe_injective h

instance : LinearMapClass (JordanStarMap A B) ℂ A B where
  map_add f := f.toLinearMap.map_add
  map_smulₛₗ f := f.toLinearMap.map_smul

instance : StarHomClass (JordanStarMap A B) A B where
  map_star f := f.map_star'

@[ext]
theorem ext {f g : JordanStarMap A B} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

@[simp]
theorem toLinearMap_apply (f : JordanStarMap A B) (x : A) : f.toLinearMap x = f x := rfl

/-- A Jordan star map preserves squares on the self-adjoint part. -/
theorem map_sq (f : JordanStarMap A B) {x : A} (hx : IsSelfAdjoint x) :
    f (x * x) = f x * f x := f.map_sq' x hx

private theorem map_mul_add_mul_selfAdjoint (f : JordanStarMap A B) {x y : A}
    (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) :
    f (x * y + y * x) = f x * f y + f y * f x := by
  have h := f.map_sq (hx.add hy)
  simp only [add_mul, mul_add, map_add, f.map_sq hx, f.map_sq hy] at h
  simp only [map_add]
  grind

/-- Polarization extends square preservation to the symmetrized product of arbitrary elements. -/
theorem map_mul_add_mul [StarModule ℂ A] (f : JordanStarMap A B) (x y : A) :
    f (x * y + y * x) = f x * f y + f y * f x := by
  have hy (a : A) (ha : IsSelfAdjoint a) (b : A) :
      f (a * b + b * a) = f a * f b + f b * f a := by
    rw [← realPart_add_I_smul_imaginaryPart b]
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, map_add, map_smul]
    have hr := f.map_mul_add_mul_selfAdjoint ha (realPart b).property
    have hi := f.map_mul_add_mul_selfAdjoint ha (imaginaryPart b).property
    simp only [map_add] at hr hi
    calc
      _ = (f (a * ↑(realPart b)) + f (↑(realPart b) * a)) +
          Complex.I • (f (a * ↑(imaginaryPart b)) + f (↑(imaginaryPart b) * a)) := by module
      _ = _ := by rw [hr, hi]; module
  rw [← realPart_add_I_smul_imaginaryPart x]
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, map_add, map_smul]
  have hr := hy _ (realPart x).property y
  have hi := hy _ (imaginaryPart x).property y
  simp only [map_add] at hr hi
  calc
    _ = (f (↑(realPart x) * y) + f (y * ↑(realPart x))) +
        Complex.I • (f (↑(imaginaryPart x) * y) + f (y * ↑(imaginaryPart x))) := by module
    _ = _ := by rw [hr, hi]; module

/-- A Jordan star map preserves squares of every element. -/
@[simp]
theorem map_mul_self [StarModule ℂ A] (f : JordanStarMap A B) (x : A) : f (x * x) = f x * f x := by
  have h := f.map_mul_add_mul x x
  simp only [← two_smul ℂ, map_smul] at h
  exact (smul_right_injective B (two_ne_zero : (2 : ℂ) ≠ 0)) h

/-- Jordan star maps preserve multiplication in the symmetrized algebra. -/
theorem map_sym_mul [StarModule ℂ A] (f : JordanStarMap A B) (x y : A) :
    SymAlg.sym (f (SymAlg.unsym (SymAlg.sym x * SymAlg.sym y))) =
      SymAlg.sym (f x) * SymAlg.sym (f y) := by
  have ha : ⅟(2 : A) = algebraMap ℂ A ((2 : ℂ)⁻¹) := (rfl)
  have hb : ⅟(2 : B) = algebraMap ℂ B ((2 : ℂ)⁻¹) := (rfl)
  simp only [SymAlg.sym_mul_sym, SymAlg.unsym_sym, ha, hb, ← Algebra.smul_def,
    map_smul, f.map_mul_add_mul]

/-- The identity Jordan star map. -/
def id : JordanStarMap A A where
  toLinearMap := LinearMap.id
  map_star' _ := rfl
  map_sq' _ _ := rfl

@[simp] theorem id_apply (x : A) : id x = x := (rfl)

/-- Composition of Jordan star maps. -/
def comp {C : Type*} [Ring C] [StarRing C] [Algebra ℂ C]
    (g : JordanStarMap B C) (f : JordanStarMap A B) : JordanStarMap A C where
  toLinearMap := g.toLinearMap.comp f.toLinearMap
  map_star' x := by simp only [LinearMap.comp_apply, toLinearMap_apply, map_star]
  map_sq' x hx := by
    simp only [LinearMap.comp_apply, toLinearMap_apply, f.map_sq hx]
    exact g.map_sq (by simpa only [IsSelfAdjoint, map_star] using congrArg f hx.star_eq)

@[simp] theorem comp_apply {C : Type*} [Ring C] [StarRing C] [Algebra ℂ C]
    (g : JordanStarMap B C) (f : JordanStarMap A B) (x : A) : g.comp f x = g (f x) := (rfl)

/-- The zero Jordan star map. -/
def zero : JordanStarMap A B where
  toLinearMap := 0
  map_star' _ := by simp
  map_sq' _ _ := by simp

@[simp] theorem zero_apply (x : A) : (zero : JordanStarMap A B) x = 0 := (rfl)

/-- A surjective Jordan star map between unital algebras preserves the unit. -/
theorem map_one_of_surjective [StarModule ℂ A] (f : JordanStarMap A B)
    (hf : Function.Surjective f) : f 1 = 1 := by
  obtain ⟨x, hx⟩ := hf 1
  have h := f.map_mul_add_mul x 1
  simp only [mul_one, one_mul, map_add, hx] at h
  have : (2 : ℂ) • (1 : B) = (2 : ℂ) • f 1 := by simpa [two_smul] using h
  exact ((smul_right_injective B (two_ne_zero : (2 : ℂ) ≠ 0)) this).symm

/-- The zero map into a nonzero algebra is not unital. -/
theorem zero_not_unital [Nontrivial B] : (zero : JordanStarMap A B) 1 ≠ 1 := by simp

end JordanStarMap

variable (A B) in
/-- A bijective Jordan star map, carried by a native complex linear equivalence. -/
structure JordanStarEquiv extends A ≃ₗ[ℂ] B where
  map_star' (x : A) : toLinearEquiv (star x) = star (toLinearEquiv x)
  map_sq' (x : A) : IsSelfAdjoint x → toLinearEquiv (x * x) =
    toLinearEquiv x * toLinearEquiv x

namespace JordanStarEquiv

/-- Forget bijectivity of a Jordan star equivalence. -/
def toJordanStarMap (e : JordanStarEquiv A B) : JordanStarMap A B where
  toLinearMap := e.toLinearEquiv.toLinearMap
  map_star' := e.map_star'
  map_sq' := e.map_sq'

instance : FunLike (JordanStarEquiv A B) A B where
  coe e := e.toLinearEquiv
  coe_injective e f h := by cases e; cases f; congr; exact DFunLike.coe_injective h

instance : LinearMapClass (JordanStarEquiv A B) ℂ A B where
  map_add e := e.toLinearEquiv.map_add
  map_smulₛₗ e := e.toLinearEquiv.map_smul

instance : StarHomClass (JordanStarEquiv A B) A B where
  map_star e := e.map_star'

@[ext]
theorem ext {e f : JordanStarEquiv A B} (h : ∀ x, e x = f x) : e = f :=
  DFunLike.ext _ _ h

@[simp]
theorem toJordanStarMap_apply (e : JordanStarEquiv A B) (x : A) :
    e.toJordanStarMap x = e x := (rfl)

/-- The inverse of a Jordan star equivalence. -/
def symm (e : JordanStarEquiv A B) : JordanStarEquiv B A where
  toLinearEquiv := e.toLinearEquiv.symm
  map_star' x := by
    apply e.toLinearEquiv.injective
    simp [e.map_star']
  map_sq' x hx := by
    have hsa : IsSelfAdjoint (e.toLinearEquiv.symm x) := by
      apply e.toLinearEquiv.injective
      simp [e.map_star', hx.star_eq]
    apply e.toLinearEquiv.injective
    simp [e.map_sq' _ hsa]

/-- The identity Jordan star equivalence. -/
def refl : JordanStarEquiv A A where
  toLinearEquiv := LinearEquiv.refl ℂ A
  map_star' _ := rfl
  map_sq' _ _ := rfl

/-- Compose Jordan star equivalences in application order. -/
def trans {C : Type*} [Ring C] [StarRing C] [Algebra ℂ C]
    (e : JordanStarEquiv A B) (f : JordanStarEquiv B C) : JordanStarEquiv A C where
  toLinearEquiv := e.toLinearEquiv.trans f.toLinearEquiv
  map_star' x := by simp [e.map_star', f.map_star']
  map_sq' x hx := (f.toJordanStarMap.comp e.toJordanStarMap).map_sq hx

@[simp] theorem refl_apply (x : A) : refl x = x := (rfl)

@[simp] theorem trans_apply {C : Type*} [Ring C] [StarRing C] [Algebra ℂ C]
    (e : JordanStarEquiv A B) (f : JordanStarEquiv B C) (x : A) :
    e.trans f x = f (e x) := (rfl)

@[simp] theorem symm_apply_apply (e : JordanStarEquiv A B) (x : A) :
    e.symm (e x) = x :=
  (e.toLinearEquiv.symm_apply_apply x)

@[simp] theorem apply_symm_apply (e : JordanStarEquiv A B) (x : B) :
    e (e.symm x) = x :=
  (e.toLinearEquiv.apply_symm_apply x)

@[simp] theorem symm_symm (e : JordanStarEquiv A B) : e.symm.symm = e := by ext; rfl

/-- Every Jordan star equivalence is unital. -/
@[simp]
theorem map_one [StarModule ℂ A] (e : JordanStarEquiv A B) : e 1 = 1 :=
  e.toJordanStarMap.map_one_of_surjective e.toLinearEquiv.surjective

end JordanStarEquiv
end TauCeti

open scoped TauCeti

/-- For an adjoint-preserving complex linear map, preserving self-adjoint squares is
 equivalent to preserving multiplication in the symmetrized algebra. -/
theorem LinearMap.map_selfAdjoint_sq_iff_map_sym_mul
    {A B : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    [Ring B] [StarRing B] [Algebra ℂ B]
    (f : A →ₗ[ℂ] B) (hstar : ∀ x, f (star x) = star (f x)) :
    (∀ x, IsSelfAdjoint x → f (x * x) = f x * f x) ↔
      (∀ x y, SymAlg.sym (f (SymAlg.unsym (SymAlg.sym x * SymAlg.sym y))) =
        SymAlg.sym (f x) * SymAlg.sym (f y)) := by
  constructor
  · intro h
    exact (TauCeti.JordanStarMap.mk f hstar h).map_sym_mul
  · intro h x _
    simpa only [← SymAlg.sym_mul_self, SymAlg.unsym_sym, SymAlg.sym_inj] using h x x
