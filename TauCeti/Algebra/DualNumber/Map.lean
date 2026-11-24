/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Coefficient maps on dual numbers

An algebra homomorphism `f : A →ₐ[R] B` induces a homomorphism `A[ε] →ₐ[R] B[ε]`
by applying `f` to both coefficients and preserving `ε`. This is the morphism of trivial
first-order deformations, constructed with Mathlib's universal property `DualNumber.lift`.

Dually, an `R`-algebra endomorphism `f` of `R[ε]` is determined by `f ε`: the `ε`-coefficient of
`f x` is that of `x` times that of `f ε`. Over a reduced semiring `f ε` has zero `R`-component, so
`f ε = (f ε).snd • ε`; for the endomorphism `TrivSqZeroExt.map g` induced by a linear map
`g : R →ₗ[R] R` this is `g 1 • ε`.
-/

public section

open TrivSqZeroExt DualNumber

namespace AlgHom

variable {R A B C : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Semiring C]
  [Algebra R A] [Algebra R B] [Algebra R C]

/-- Apply an algebra homomorphism to both coefficients of a dual number, fixing `ε`. -/
def dualNumberMap (f : A →ₐ[R] B) : A[ε] →ₐ[R] B[ε] :=
  DualNumber.lift ⟨((inlAlgHom R B B).comp f, ε), eps_mul_eps,
    fun _ ↦ commute_eps_left _⟩

@[simp]
theorem dualNumberMap_fst (f : A →ₐ[R] B) (z : A[ε]) :
    (f.dualNumberMap z).fst = f z.fst := by
  simp [dualNumberMap, DualNumber.lift_apply_apply]

@[simp]
theorem dualNumberMap_snd (f : A →ₐ[R] B) (z : A[ε]) :
    (f.dualNumberMap z).snd = f z.snd := by
  simp [dualNumberMap, DualNumber.lift_apply_apply]

@[simp]
theorem dualNumberMap_inl (f : A →ₐ[R] B) (a : A) :
    f.dualNumberMap (inl a) = inl (f a) := by
  ext <;> simp

@[simp]
theorem dualNumberMap_eps (f : A →ₐ[R] B) : f.dualNumberMap ε = ε := by
  ext <;> simp

@[simp]
theorem dualNumberMap_id : (AlgHom.id R A).dualNumberMap = AlgHom.id R A[ε] := by
  ext z <;> simp

@[simp]
theorem dualNumberMap_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    (g.comp f).dualNumberMap = g.dualNumberMap.comp f.dualNumberMap := by
  ext z <;> simp

end AlgHom

namespace TauCeti.DualNumber

variable {R : Type*} [CommSemiring R]

/-- `TrivSqZeroExt.map f` multiplies `ε` by `f 1`. -/
@[simp]
theorem map_eps (f : R →ₗ[R] R) : map f ε = f 1 • ε :=
  (map_inr f 1).trans (inr_eq_smul_eps _)

variable {F : Type*} [FunLike F R[ε] R[ε]] [AlgHomClass F R R[ε] R[ε]]

/-- The `ε`-coefficient of the image of `x` under an endomorphism `f` of the dual numbers is the
`ε`-coefficient of `x` times that of `f ε`. -/
theorem snd_apply_eq_snd_mul_snd_apply_eps (f : F) (x : R[ε]) : (f x).snd = x.snd * (f ε).snd := by
  conv_lhs => rw [← inl_fst_add_inr_snd_eq x, inr_eq_smul_eps, map_add, map_smul,
    ← algebraMap_eq_inl, AlgHomClass.commutes]
  simp [algebraMap_eq_inl]

/-- Over a reduced semiring, an endomorphism of the dual numbers sends `ε` to an element with zero
`R`-component. -/
@[simp]
theorem fst_apply_eps_eq_zero [IsReduced R] (f : F) : (f ε).fst = 0 :=
  ((IsNilpotent.map ⟨2, by rw [pow_two, eps_mul_eps]⟩ f).map (fstHom R R R)).eq_zero

/-- Over a reduced semiring, an endomorphism of the dual numbers multiplies `ε` by the
`ε`-coefficient of its image. -/
theorem apply_eps_eq_snd_smul_eps [IsReduced R] (f : F) : f ε = (f ε).snd • ε := by
  conv_lhs => rw [← inl_fst_add_inr_snd_eq (f ε)]
  rw [fst_apply_eps_eq_zero, inl_zero, zero_add, inr_eq_smul_eps]

end TauCeti.DualNumber
