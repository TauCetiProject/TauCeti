/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DualNumber

/-!
# Coefficient maps on dual numbers

An algebra homomorphism `f : A →ₐ[R] B` induces a homomorphism `A[ε] →ₐ[R] B[ε]`
by applying `f` to both coefficients and preserving `ε`. This is the morphism of trivial
first-order deformations, constructed with Mathlib's universal property `DualNumber.lift`.
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
