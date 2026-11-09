/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PolynomialLaw.Homogeneous
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Power polynomial laws

The power map on an associative algebra is a homogeneous polynomial law, even when the
algebra is noncommutative. Its naturality under algebra homomorphisms allows one to apply
it in a tensor algebra and then project to a tensor power.

The underlying polynomial laws are Mathlib's construction by Antoine Chambert-Loir and
María Inés de Frutos-Fernández. See Roby, *Lois polynômes et lois formelles en théorie des
modules* (1963), Chapter I, for polynomial laws on algebras.
-/

public noncomputable section

open TensorProduct

universe u

namespace PolynomialLaw

variable {R : Type u} [CommSemiring R] {A B : Type*}
  [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/-- The homogeneous polynomial law `x ↦ x ^ d` on an associative `R`-algebra. -/
def power (R : Type u) [CommSemiring R] (A : Type*) [Semiring A] [Algebra R A]
    (d : ℕ) : A →ₚₗ[R] A where
  toFun' _ _ _ x := x ^ d
  isCompat' φ := funext fun x ↦ map_pow (Algebra.TensorProduct.map φ (AlgHom.id R A)) x d

/-- The component of the power law in the universe used by `PolynomialLaw`. -/
@[simp]
theorem power_toFun' (d : ℕ) (S : Type u) [CommSemiring S] [Algebra R S] (x : S ⊗[R] A) :
    (power R A d).toFun' S x = x ^ d :=
  (rfl)

/-- The power law raises an element to its `d`th power after every scalar extension. -/
@[simp]
theorem power_toFun (d : ℕ) (S : Type*) [CommSemiring S] [Algebra R S] (x : S ⊗[R] A) :
    (power R A d).toFun S x = x ^ d := by
  obtain ⟨n, φ, x, rfl⟩ := PolynomialLaw.exists_lift x
  rw [← PolynomialLaw.isCompat_apply, ← PolynomialLaw.toFun'_eq_toFun]
  exact map_pow (Algebra.TensorProduct.map φ (AlgHom.id R A)) x d

/-- The ground value of the power law is the ordinary power. -/
@[simp]
theorem ground_power (d : ℕ) (x : A) : (power R A d).ground x = x ^ d := by
  simp [PolynomialLaw.ground_apply]

/-- The power law has degree `d`, without a commutativity assumption on the algebra. -/
theorem isHomogeneousOfDegree_power (d : ℕ) : (power R A d).IsHomogeneousOfDegree d :=
  isHomogeneousOfDegree_iff.mpr fun _ _ _ s x ↦ smul_pow s x d

/-- Power laws commute with algebra homomorphisms, on all scalar extensions. -/
theorem power_comp_toPolynomialLaw (d : ℕ) (f : A →ₐ[R] B) :
    (power R B d).comp f.toLinearMap.toPolynomialLaw =
      f.toLinearMap.toPolynomialLaw.comp (power R A d) := by
  ext S _ _ x
  simp only [comp_toFun', Function.comp_apply, LinearMap.toPolynomialLaw_toFun', power_toFun']
  exact (map_pow (Algebra.TensorProduct.map (AlgHom.id R S) f) x d).symm

end PolynomialLaw
