/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Twisted.Basic

/-!
# Coefficient bars on twisted monoid algebras

A scalar automorphism acts coefficientwise in the distinguished monomial basis. If it
exchanges the two arguments of the factor set on a commutative monoid, the resulting map
reverses multiplication. An involutive scalar automorphism therefore gives a semilinear
anti-involution fixing every normalized monomial. No infinite-order parameter or domain
hypothesis is needed.

This supplies the coefficient bar used for based quantum tori. The scalar compatibility is
an explicit hypothesis: it can fail at finite order even when the twisted algebra exists.

## References

* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, §6, equation (6.2).
-/

public section

namespace TauCeti.TwistedMonoidAlgebra

variable {R G : Type*} [CommSemiring R] [Monoid G]
variable {α : G → G → Rˣ} [IsFactorSet α]

/-- Apply a scalar automorphism to the coefficients in the distinguished monomial basis. -/
noncomputable def bar (σ : R ≃+* R) :
    twistedMonoidAlgebra R G α ≃+ twistedMonoidAlgebra R G α :=
  (basis R G α).repr.toAddEquiv.trans
    ((Finsupp.mapRange.addEquiv σ.toAddEquiv).trans (basis R G α).repr.symm.toAddEquiv)

/-- The monomial coefficients of the bar are obtained by applying the scalar automorphism. -/
@[simp]
theorem repr_bar (σ : R ≃+* R) (x : twistedMonoidAlgebra R G α) (g : G) :
    (basis R G α).repr (bar σ x) g = σ ((basis R G α).repr x g) := by
  simp [bar]

/-- The coefficient bar is semilinear with respect to its scalar automorphism. -/
@[simp]
theorem bar_smul (σ : R ≃+* R) (r : R) (x : twistedMonoidAlgebra R G α) :
    bar σ (r • x) = σ r • bar σ x := by
  apply (basis R G α).repr.injective
  ext g
  simp [map_mul]

/-- Every normalized monomial is fixed by the coefficient bar. -/
@[simp]
theorem bar_of (σ : R ≃+* R) (g : G) :
    bar σ (of g : twistedMonoidAlgebra R G α) = of g := by
  apply (basis R G α).repr.injective
  have hb : (basis R G α).repr (of g) = Finsupp.single g 1 := by
    rw [← basis_apply R G α g]
    exact (basis R G α).repr_self g
  ext h
  simp only [repr_bar, hb]
  classical
  by_cases hgh : g = h <;> simp [hgh]

@[simp]
theorem bar_one (σ : R ≃+* R) : bar σ (1 : twistedMonoidAlgebra R G α) = 1 := by
  simpa only [of_one] using bar_of (α := α) σ 1

/-- An involutive scalar automorphism gives an involutive coefficient bar. -/
theorem bar_involutive (σ : R ≃+* R) (hσ : Function.Involutive σ) :
    Function.Involutive (bar (α := α) σ) := by
  intro x
  apply (basis R G α).repr.injective
  ext g
  simp only [repr_bar]
  exact hσ _

/-- Applying an involutive bar twice recovers the original element. -/
@[simp]
theorem bar_bar (σ : R ≃+* R) (hσ : Function.Involutive σ)
    (x : twistedMonoidAlgebra R G α) : bar σ (bar σ x) = x :=
  bar_involutive σ hσ x

section Commutative

variable {R G : Type*} [CommSemiring R] [CommMonoid G]
variable {α : G → G → Rˣ} [IsFactorSet α]

/-- If the scalar automorphism reverses the factor set, the coefficient bar reverses products. -/
theorem bar_mul (σ : R ≃+* R) (hα : ∀ g h, σ (α g h : R) = (α h g : R))
    (x y : twistedMonoidAlgebra R G α) : bar σ (x * y) = bar σ y * bar σ x := by
  conv_lhs =>
    rw [← (basis R G α).linearCombination_repr x,
      ← (basis R G α).linearCombination_repr y]
  conv_rhs =>
    rw [← (basis R G α).linearCombination_repr x,
      ← (basis R G α).linearCombination_repr y]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, basis_apply, Finset.sum_mul,
    Finset.mul_sum, map_sum, bar_smul,
    bar_of, smul_mul_smul_comm, of_mul_of, smul_smul, map_mul, hα]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _hg
  apply Finset.sum_congr rfl
  intro h _hh
  rw [mul_comm g h]
  congr 1
  ac_rfl

end Commutative

end TauCeti.TwistedMonoidAlgebra
