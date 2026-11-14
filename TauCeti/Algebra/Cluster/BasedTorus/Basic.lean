/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import TauCeti.Algebra.MonoidAlgebra.Twisted.Basic
public import TauCeti.Algebra.MvPolynomial.Laurent.Basic

/-!
# Based quantum tori

Let `R` be a commutative semiring, `u : Rˣ` a unit and `Λ : Matrix I I ℤ` an integer form on the
lattice `I →₀ ℤ` of a finite type `I`. The **based quantum torus** `T(R, u, Λ)` is the `R`-algebra
with basis the monomials `X^a`, `a : I →₀ ℤ`, multiplied by

`X^a * X^b = u ^ Λ(a, b) • X^(a + b)`,

where `Λ(a, b) = ∑ i, ∑ j, a i * Λ i j * b j` is the pairing of `Λ`. Bilinearity of the pairing
makes `(a, b) ↦ u ^ Λ(a, b)` a normalized factor set on the exponent lattice, and `T(R, u, Λ)` is
the twisted monoid algebra `TauCeti.twistedMonoidAlgebra` of that factor set. For an alternating
form the monomials quasi-commute, `X^a * X^b = u ^ (2 Λ(a, b)) • X^b * X^a`, and `X^(-a)` is the
inverse of `X^a`. In quantum cluster algebras `u = v = q^{1/2}` and the coordinates `X^{e_i}`
satisfy `X_i X_j = v^{2 Λ_ij} X_j X_i`. At `u = 1`, or for `Λ = 0`, the factor set is trivial and
`T(R, u, Λ)` is the ordinary Laurent ring `TauCeti.LaurentRing R I`.

These tori are the sources of the charts of classical and quantum cluster seeds
(`TauCeti.BasedChart`).

## Main definitions

* `Matrix.formPairing`: the bilinear pairing `Λ(a, b)` of a square matrix on finitely supported
  vectors.
* `TauCeti.basedTorusFactor`: the factor set `(a, b) ↦ u ^ Λ(a, b)`.
* `TauCeti.BasedTorus R u Λ`: the based quantum torus `T(R, u, Λ)`.
* `TauCeti.BasedTorus.monomial`: the basis monomials `X^a`, forming the basis
  `TauCeti.BasedTorus.basis`.
* `TauCeti.BasedTorus.lift`: the universal property. A family `M` in an `R`-algebra with
  `M 0 = 1` and `M a * M b = u ^ Λ(a, b) • M (a + b)` extends to an algebra map out of
  `T(R, u, Λ)`.
* `TauCeti.BasedTorus.laurentRingEquiv`: for a trivial factor set, the based torus is the Laurent
  ring.

## Main results

* `TauCeti.BasedTorus.monomial_mul_monomial`: the multiplication rule of the monomials.
* `TauCeti.BasedTorus.monomial_mul_monomial_comm`: monomials commute up to the scalar
  `u ^ (Λ(a, b) - Λ(b, a))`.
* `TauCeti.BasedTorus.isUnit_monomial` and `TauCeti.BasedTorus.monomial_mul_monomial_neg`: the
  monomials are units, and for an alternating form `X^(-a)` is the inverse of `X^a`.

## References

* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Advances in Mathematics 195
  (2005), §2.
-/

public section

namespace Matrix

variable {R I : Type*} [CommSemiring R] [Fintype I] [DecidableEq I]

/-- The bilinear pairing `Λ(a, b) = ∑ i, ∑ j, a i * Λ i j * b j` of a square matrix `Λ` on
finitely supported vectors: the bilinear form `Matrix.toBilin` of `Λ` in the standard basis
`Finsupp.basisSingleOne`. -/
noncomputable def formPairing (Λ : Matrix I I R) : LinearMap.BilinForm R (I →₀ R) :=
  Λ.toBilin Finsupp.basisSingleOne

theorem formPairing_apply_eq_sum (Λ : Matrix I I R) (a b : I →₀ R) :
    Λ.formPairing a b = ∑ i, ∑ j, a i * Λ i j * b j :=
  toBilin_apply ..

/-- The pairing of a matrix is the bilinear form `Matrix.toBilin'` on the underlying functions. -/
theorem formPairing_apply_eq_toBilin' (Λ : Matrix I I R) (a b : I →₀ R) :
    Λ.formPairing a b = Λ.toBilin' a b := by
  rw [formPairing_apply_eq_sum, toBilin'_apply]

@[simp]
theorem formPairing_single_single (Λ : Matrix I I R) (i j : I) (r s : R) :
    Λ.formPairing (Finsupp.single i r) (Finsupp.single j s) = r * Λ i j * s := by
  rw [formPairing_apply_eq_sum, Finset.sum_eq_single i (fun i' _ hi' ↦ by simp [hi'])
    (by simp), Finset.sum_eq_single j (fun j' _ hj' ↦ by simp [hj']) (by simp)]
  simp

/-- The pairing of a matrix is alternating exactly when its bilinear form is. -/
@[simp]
theorem isAlt_formPairing_iff {Λ : Matrix I I R} : Λ.formPairing.IsAlt ↔ Λ.toBilin'.IsAlt := by
  refine ⟨fun h v ↦ ?_, fun h a ↦ h a⟩
  simpa [formPairing_apply_eq_toBilin'] using h (Finsupp.equivFunOnFinite.symm v)

/-- The pairing of a reindexed matrix is the pairing of the original matrix on the reindexed
vectors. -/
theorem formPairing_reindex {I' : Type*} [Fintype I'] [DecidableEq I'] (e : I ≃ I')
    (Λ : Matrix I I R) (a b : I' →₀ R) :
    (Λ.reindex e e).formPairing a b =
      Λ.formPairing (a.equivMapDomain e.symm) (b.equivMapDomain e.symm) := by
  simp only [formPairing_apply_eq_sum, reindex_apply, submatrix_apply,
    Finsupp.equivMapDomain_apply, Equiv.symm_symm]
  exact Fintype.sum_equiv e.symm _ _ fun i ↦ Fintype.sum_equiv e.symm _ _ fun j ↦ by simp

end Matrix

namespace TauCeti

variable {R : Type*} [CommSemiring R] {I : Type*} [Fintype I] [DecidableEq I]

/-- The factor set `(a, b) ↦ u ^ Λ(a, b)` on the exponent lattice `I →₀ ℤ`, written
multiplicatively, whose twisted monoid algebra is the based quantum torus. -/
noncomputable def basedTorusFactor (u : Rˣ) (Λ : Matrix I I ℤ) :
    Multiplicative (I →₀ ℤ) → Multiplicative (I →₀ ℤ) → Rˣ :=
  fun a b ↦ u ^ Λ.formPairing a.toAdd b.toAdd

@[simp]
theorem basedTorusFactor_apply (u : Rˣ) (Λ : Matrix I I ℤ) (a b : Multiplicative (I →₀ ℤ)) :
    basedTorusFactor u Λ a b = u ^ Λ.formPairing a.toAdd b.toAdd :=
  (rfl)

/-- Bilinearity of the pairing makes `u ^ Λ(a, b)` a normalized `2`-cocycle. -/
instance (u : Rˣ) (Λ : Matrix I I ℤ) : IsFactorSet (basedTorusFactor u Λ) where
  cocycle a b c := by
    simp only [basedTorusFactor_apply, toAdd_mul, map_add, LinearMap.add_apply, ← zpow_add]
    congr 1
    ring
  one_left a := by simp

/-- At `u = 1` the factor set is trivial, whatever the form. -/
@[simp]
theorem basedTorusFactor_one (Λ : Matrix I I ℤ) : basedTorusFactor (1 : Rˣ) Λ = 1 := by
  ext; simp

/-- For the zero form the factor set is trivial, whatever the unit. -/
@[simp]
theorem basedTorusFactor_zero (u : Rˣ) : basedTorusFactor u (0 : Matrix I I ℤ) = 1 := by
  ext; simp [Matrix.formPairing_apply_eq_sum]

variable (R) in
/-- **The based quantum torus** `T(R, u, Λ)`: the `R`-algebra with basis the monomials `X^a`,
`a : I →₀ ℤ`, and multiplication `X^a * X^b = u ^ Λ(a, b) • X^(a + b)`. It is the twisted monoid
algebra of the factor set `TauCeti.basedTorusFactor u Λ`. -/
abbrev BasedTorus (u : Rˣ) (Λ : Matrix I I ℤ) : Type _ :=
  twistedMonoidAlgebra R (Multiplicative (I →₀ ℤ)) (basedTorusFactor u Λ)

namespace BasedTorus

variable {u : Rˣ} {Λ : Matrix I I ℤ}

/-- The basis monomial `X^a` of the based quantum torus. -/
noncomputable def monomial (a : I →₀ ℤ) : BasedTorus R u Λ :=
  TwistedMonoidAlgebra.of (Multiplicative.ofAdd a)

@[simp]
theorem monomial_zero : (monomial 0 : BasedTorus R u Λ) = 1 := by
  simp [monomial]

/-- **The multiplication rule of the based quantum torus**:
`X^a * X^b = u ^ Λ(a, b) • X^(a + b)`. -/
@[simp]
theorem monomial_mul_monomial (a b : I →₀ ℤ) :
    (monomial a : BasedTorus R u Λ) * monomial b =
      ((u ^ Λ.formPairing a b : Rˣ) : R) • monomial (a + b) := by
  simp [monomial]

/-- The monomials of the based quantum torus commute up to the scalar `u ^ (Λ(a, b) - Λ(b, a))`.
-/
theorem monomial_mul_monomial_comm (a b : I →₀ ℤ) :
    (monomial a : BasedTorus R u Λ) * monomial b =
      ((u ^ (Λ.formPairing a b - Λ.formPairing b a) : Rˣ) : R) • (monomial b * monomial a) := by
  rw [monomial_mul_monomial, monomial_mul_monomial, smul_smul, ← Units.val_mul, ← zpow_add,
    sub_add_cancel, add_comm]

/-- For an alternating form the monomials quasi-commute:
`X^a * X^b = u ^ (2 Λ(a, b)) • X^b * X^a`. -/
theorem monomial_mul_monomial_comm_of_isAlt (hΛ : Λ.toBilin'.IsAlt) (a b : I →₀ ℤ) :
    (monomial a : BasedTorus R u Λ) * monomial b =
      ((u ^ (2 * Λ.formPairing a b) : Rˣ) : R) • (monomial b * monomial a) := by
  rw [monomial_mul_monomial_comm, ← (Matrix.isAlt_formPairing_iff.2 hΛ).neg_eq a b, sub_neg_eq_add,
    two_mul]

/-- The monomials of the based quantum torus are units. -/
theorem isUnit_monomial (a : I →₀ ℤ) : IsUnit (monomial a : BasedTorus R u Λ) :=
  TwistedMonoidAlgebra.isUnit_of _

/-- For an alternating form, `X^(-a)` is the inverse of `X^a`. -/
theorem monomial_mul_monomial_neg (hΛ : Λ.toBilin'.IsAlt) (a : I →₀ ℤ) :
    (monomial a : BasedTorus R u Λ) * monomial (-a) = 1 := by
  simp [(Matrix.isAlt_formPairing_iff.2 hΛ).self_eq_zero a]

variable (R u Λ) in
/-- The monomials `X^a` form a basis of the based quantum torus indexed by the exponent lattice. -/
noncomputable def basis : Module.Basis (I →₀ ℤ) R (BasedTorus R u Λ) :=
  (TwistedMonoidAlgebra.basis R (Multiplicative (I →₀ ℤ)) (basedTorusFactor u Λ)).reindex
    Multiplicative.toAdd

@[simp]
theorem basis_apply (a : I →₀ ℤ) : basis R u Λ a = monomial a := by
  simp [basis, monomial]

/-- An algebra map out of the based quantum torus is determined by its values on the monomials. -/
@[ext]
theorem algHom_ext {A : Type*} [Semiring A] [Algebra R A] {f g : BasedTorus R u Λ →ₐ[R] A}
    (h : ∀ a, f (monomial a) = g (monomial a)) : f = g :=
  TwistedMonoidAlgebra.algHom_ext fun a ↦ h a.toAdd

section Lift

variable {A : Type*} [Semiring A] [Algebra R A]

/-- **The universal property of the based quantum torus.** A family `M` in an `R`-algebra with
`M 0 = 1` and `M a * M b = u ^ Λ(a, b) • M (a + b)` extends to the algebra map
`X^a ↦ M a`. Uniqueness is `TauCeti.BasedTorus.algHom_ext`. -/
noncomputable def lift (M : (I →₀ ℤ) → A) (h₀ : M 0 = 1)
    (hM : ∀ a b, M a * M b = ((u ^ Λ.formPairing a b : Rˣ) : R) • M (a + b)) :
    BasedTorus R u Λ →ₐ[R] A :=
  TwistedMonoidAlgebra.lift (fun a ↦ M a.toAdd) h₀ fun a b ↦ hM a.toAdd b.toAdd

@[simp]
theorem lift_monomial (M : (I →₀ ℤ) → A) (h₀ : M 0 = 1)
    (hM : ∀ a b, M a * M b = ((u ^ Λ.formPairing a b : Rˣ) : R) • M (a + b)) (a : I →₀ ℤ) :
    lift M h₀ hM (monomial a) = M a :=
  TwistedMonoidAlgebra.lift_of ..

end Lift

section Laurent

/-- **A based quantum torus with trivial factor set is the Laurent ring**, by `X^a ↦ X^a`. This
applies at `u = 1` (`TauCeti.basedTorusFactor_one`) and for `Λ = 0`
(`TauCeti.basedTorusFactor_zero`). -/
noncomputable def laurentRingEquiv (h : basedTorusFactor u Λ = 1) :
    BasedTorus R u Λ ≃ₐ[R] LaurentRing R I :=
  (TwistedMonoidAlgebra.equivOfCoboundary 1 (basedTorusFactor u Λ) 1
      (by simp [h, -basedTorusFactor_apply])).trans <|
    (TwistedMonoidAlgebra.monoidAlgebraEquiv R _).trans
      (AddMonoidAlgebra.toMultiplicativeAlgEquiv R R (I →₀ ℤ)).symm

@[simp]
theorem laurentRingEquiv_monomial (h : basedTorusFactor u Λ = 1) (a : I →₀ ℤ) :
    laurentRingEquiv h (monomial a) = AddMonoidAlgebra.single a 1 := by
  simp [laurentRingEquiv, monomial, AlgEquiv.symm_apply_eq]

@[simp]
theorem laurentRingEquiv_symm_single (h : basedTorusFactor u Λ = 1) (a : I →₀ ℤ) :
    (laurentRingEquiv h).symm (AddMonoidAlgebra.single a 1) = monomial a := by
  rw [AlgEquiv.symm_apply_eq, laurentRingEquiv_monomial]

end Laurent

end BasedTorus

end TauCeti
