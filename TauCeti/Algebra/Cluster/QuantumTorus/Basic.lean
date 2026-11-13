/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Twisted.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Based quantum tori

The based quantum torus of an integral bilinear form `Λ` and a scalar unit `u` has
basis `Xᵃ` and multiplication `Xᵃ Xᵇ = u ^ Λ(a,b) • Xᵃ⁺ᵇ`. It is constructed from
`TauCeti.twistedMonoidAlgebra`, using the factor set obtained by exponentiating `Λ`.
For an alternating form, the inverse of `Xᵃ` is exactly `X⁻ᵃ`.

The construction works over commutative semirings and on any additive commutative
group of exponents. In particular, it applies to the finite free exponent lattices
of quantum cluster charts, including the zero lattice. No order or infinite-order
hypothesis on the scalar parameter is used.

## References

* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Advances in Mathematics
  195 (2005), §4, especially (4.1).
-/

public section

namespace TauCeti

namespace QuantumTorus

variable {R L : Type*} [CommSemiring R] [AddCommGroup L]

/-- Exponentiating an integral bilinear form gives a normalized factor set. -/
def factorSet (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L)
    (a b : Multiplicative L) : Rˣ :=
  u ^ (Λ a.toAdd b.toAdd)

@[simp]
theorem factorSet_apply (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L) (a b : L) :
    factorSet u Λ (Multiplicative.ofAdd a) (Multiplicative.ofAdd b) = u ^ (Λ a b) :=
  (rfl)

instance (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L) : IsFactorSet (factorSet u Λ) where
  cocycle a b c := by
    simp [factorSet, map_add, zpow_add, mul_comm, mul_assoc]
  one_left a := by simp [factorSet]

end QuantumTorus

/-- The based quantum torus with scalar unit `u` and integral form `Λ`, realized as
its twisted group algebra. Alternation is needed for the normalized inverse and
commutation formulas, but not for the algebra construction. -/
noncomputable abbrev QuantumTorus (R : Type*) [CommSemiring R] (L : Type*) [AddCommGroup L]
    (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L) :=
  twistedMonoidAlgebra R (Multiplicative L) (QuantumTorus.factorSet u Λ)

namespace QuantumTorus

variable {R L : Type*} [CommSemiring R] [AddCommGroup L]
  (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L)

/-- The normalized monomial with exponent `a`. -/
noncomputable def monomial (a : L) : QuantumTorus R L u Λ :=
  TwistedMonoidAlgebra.of (Multiplicative.ofAdd a)

@[simp]
theorem monomial_zero : monomial u Λ 0 = 1 :=
  TwistedMonoidAlgebra.of_one

/-- The normalized monomial multiplication rule. -/
@[simp]
theorem monomial_mul_monomial (a b : L) :
    monomial u Λ a * monomial u Λ b =
      ((u ^ (Λ a b) : Rˣ) : R) • monomial u Λ (a + b) :=
  TwistedMonoidAlgebra.of_mul_of _ _

/-- The normalized monomials form a basis, with additive exponent indices. -/
noncomputable def basis : Module.Basis L R (QuantumTorus R L u Λ) :=
  (TwistedMonoidAlgebra.basis R (Multiplicative L) (factorSet u Λ)).reindex
    Multiplicative.toAdd

@[simp]
theorem basis_apply (a : L) : basis u Λ a = monomial u Λ a := by
  simp [basis, monomial]

/-- A map out of a based quantum torus is determined by its normalized monomials. -/
@[ext]
theorem algHom_ext {B : Type*} [Semiring B] [Algebra R B]
    {f g : QuantumTorus R L u Λ →ₐ[R] B}
    (h : ∀ a, f (monomial u Λ a) = g (monomial u Λ a)) : f = g :=
  TwistedMonoidAlgebra.algHom_ext fun a ↦ h a.toAdd

/-- Extend a family satisfying the normalized multiplication rule to an algebra map.
Uniqueness is `QuantumTorus.algHom_ext`. -/
noncomputable def lift {B : Type*} [Semiring B] [Algebra R B]
    (M : L → B) (hzero : M 0 = 1)
    (hmul : ∀ a b, M a * M b = ((u ^ (Λ a b) : Rˣ) : R) • M (a + b)) :
    QuantumTorus R L u Λ →ₐ[R] B :=
  TwistedMonoidAlgebra.lift (fun a ↦ M a.toAdd) hzero fun a b ↦ hmul a.toAdd b.toAdd

@[simp]
theorem lift_monomial {B : Type*} [Semiring B] [Algebra R B]
    (M : L → B) (hzero : M 0 = 1)
    (hmul : ∀ a b, M a * M b = ((u ^ (Λ a b) : Rˣ) : R) • M (a + b)) (a : L) :
    lift u Λ M hzero hmul (monomial u Λ a) = M a :=
  TwistedMonoidAlgebra.lift_of ..

/-- Normalized monomials as units, with inverse given by negating the exponent. -/
noncomputable def monomialUnit (hΛ : Λ.IsAlt) (a : L) : (QuantumTorus R L u Λ)ˣ where
  val := monomial u Λ a
  inv := monomial u Λ (-a)
  val_inv := by simp [hΛ.self_eq_zero]
  inv_val := by simp [hΛ.self_eq_zero]

@[simp]
theorem val_monomialUnit (hΛ : Λ.IsAlt) (a : L) :
    (monomialUnit u Λ hΛ a : QuantumTorus R L u Λ) = monomial u Λ a :=
  (rfl)

@[simp]
theorem monomialUnit_zero (hΛ : Λ.IsAlt) : monomialUnit u Λ hΛ 0 = 1 :=
  Units.ext (monomial_zero u Λ)

@[simp]
theorem monomialUnit_neg (hΛ : Λ.IsAlt) (a : L) :
    monomialUnit u Λ hΛ (-a) = (monomialUnit u Λ hΛ a)⁻¹ :=
  Units.ext (by rfl)

/-- The normalized monomial multiplication rule, in the group of units. -/
theorem monomialUnit_mul (hΛ : Λ.IsAlt) (a b : L) :
    monomialUnit u Λ hΛ a * monomialUnit u Λ hΛ b =
      Units.map (algebraMap R (QuantumTorus R L u Λ)) (u ^ (Λ a b)) *
        monomialUnit u Λ hΛ (a + b) := by
  apply Units.ext
  simp only [Units.val_mul, val_monomialUnit, Units.coe_map]
  exact monomial_mul_monomial u Λ a b

/-- Alternation gives the usual quasi-commutation factor `u ^ (2 * Λ(a,b))`. -/
theorem monomial_mul_comm (hΛ : Λ.IsAlt) (a b : L) :
    monomial u Λ a * monomial u Λ b =
      ((u ^ (2 * Λ a b) : Rˣ) : R) • (monomial u Λ b * monomial u Λ a) := by
  rw [monomial_mul_monomial, monomial_mul_monomial, smul_smul, ← Units.val_mul,
    ← zpow_add, ← hΛ.neg_eq, add_comm b a]
  congr 1
  rw [show 2 * -(Λ b) a + (Λ b) a = -(Λ b) a by omega]

/-- When all twist factors are one, the based torus is the ordinary group algebra,
with its normalized monomial basis preserved. In particular this applies at `u = 1`
and for the zero form. -/
noncomputable def untwistedEquiv (h : ∀ a b, u ^ (Λ a b) = 1) :
    QuantumTorus R L u Λ ≃ₐ[R] AddMonoidAlgebra R L :=
  ((TwistedMonoidAlgebra.equivOfCoboundary
    (1 : Multiplicative L → Multiplicative L → Rˣ) (factorSet u Λ) (fun _ ↦ 1)
    (fun a b ↦ by simp [factorSet, h])).trans
      (TwistedMonoidAlgebra.monoidAlgebraEquiv R (Multiplicative L))).trans
        (AddMonoidAlgebra.toMultiplicativeAlgEquiv R R L).symm

@[simp]
theorem untwistedEquiv_monomial (h : ∀ a b, u ^ (Λ a b) = 1) (a : L) :
    untwistedEquiv u Λ h (monomial u Λ a) = AddMonoidAlgebra.single a 1 := by
  apply (AddMonoidAlgebra.toMultiplicativeAlgEquiv R R L).injective
  simp [untwistedEquiv, monomial, AddMonoidAlgebra.toMultiplicativeAlgEquiv_single]

@[simp]
theorem untwistedEquiv_symm_single (h : ∀ a b, u ^ (Λ a b) = 1) (a : L) :
    (untwistedEquiv u Λ h).symm (AddMonoidAlgebra.single a 1) = monomial u Λ a :=
  (untwistedEquiv u Λ h).symm_apply_eq.mpr (untwistedEquiv_monomial u Λ h a).symm

end QuantumTorus

end TauCeti
