/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.Bialgebra.Primitive
public import Mathlib.RingTheory.Bialgebra.SymmetricAlgebra
public import Mathlib.RingTheory.PolynomialAlgebra
public import TauCeti.Algebra.Polynomial.AdditivePolynomial

/-!
# Primitive elements of the rank-one symmetric algebra

The symmetric algebra `SymmetricAlgebra R R` is the polynomial algebra `R[x]` on the primitive
generator `x = ι R R 1`; with this comultiplication it is the coordinate bialgebra of the additive
group `𝔾ₐ`. Its primitive elements are the homomorphisms `𝔾ₐ → 𝔾ₐ`, and a bialgebra endomorphism
of `R[x]` is determined by the primitive element it sends `x` to.

Identifying `R[x] ⊗[R] R[x]` with the bivariate polynomial ring `R[X][Y]`, the comultiplication
sends `f(x)` to `f(X + Y)`, so `f(x)` is primitive exactly when `f(X + Y) = f(X) + f(Y)`, the
additivity identity characterised in `TauCeti.Algebra.Polynomial.AdditivePolynomial`. Over a ring
of prime characteristic `p` the primitive elements are therefore the `p`-polynomials, the
`R`-linear combinations of the powers `x ^ p ^ i`, and every bialgebra endomorphism of `R[x]`
sends `x` to one of them. Over a `ℚ`-algebra, the primitive elements are the multiples of `x`
(`SymmetricAlgebra.isPrimitiveElem_iff_mem_range_ι`, for every module).

## Main results

* `SymmetricAlgebra.isPrimitiveElem_aeval_ι_one_iff`: `f(x)` is primitive exactly when
  `f(X + Y) = f(X) + f(Y)` in `R[X][Y]`.
* `SymmetricAlgebra.isPrimitiveElem_iff_mem_span_ι_one_pow`: in prime characteristic `p`, the
  primitive elements of `R[x]` are the `R`-linear combinations of the `x ^ p ^ i`.
* `BialgHom.apply_ι_one_mem_span_ι_one_pow`: in prime characteristic `p`, a bialgebra endomorphism
  of `R[x]` sends `x` to such a `p`-polynomial.

## References

* J. S. Milne, *Algebraic Groups*, Cambridge Studies in Advanced Mathematics 170, Cambridge
  University Press, 2017, Chapter 14 (unipotent groups in nonzero characteristic).
* D. Goss, *Basic Structures of Function Field Arithmetic*, Springer, 1996, Chapter 1.
-/

public section

open Polynomial Polynomial.Bivariate Bialgebra Coalgebra TensorProduct

namespace SymmetricAlgebra

variable {R : Type*} [CommRing R]

/-- The rank-one symmetric algebra is the polynomial algebra on `ι R R 1`. -/
private noncomputable def polynomialEquiv : SymmetricAlgebra R R ≃ₐ[R] R[X] :=
  .ofAlgHom (lift (LinearMap.toSpanSingleton R R[X] X)) (aeval (ι R R 1))
    (by ext; simp) (by ext; simp)

private theorem polynomialEquiv_symm_apply (f : R[X]) :
    polynomialEquiv.symm f = aeval (ι R R 1) f := rfl

private theorem polynomialEquiv_ι_one : polynomialEquiv (ι R R 1) = X := by
  simp [polynomialEquiv]

/-- The tensor square of the rank-one symmetric algebra is the bivariate polynomial algebra, the
left factor giving the variable `X` and the right factor the variable `Y`. -/
private noncomputable def tensorEquiv :
    SymmetricAlgebra R R ⊗[R] SymmetricAlgebra R R ≃ₐ[R] R[X][Y] :=
  (Algebra.TensorProduct.congr polynomialEquiv polynomialEquiv).trans
    (polyEquivTensor R R[X]).symm

private theorem tensorEquiv_tmul (a b : SymmetricAlgebra R R) :
    tensorEquiv (a ⊗ₜ[R] b) = C (polynomialEquiv a) * (polynomialEquiv b).map C := by
  simp [tensorEquiv, smul_eq_C_mul, ← Polynomial.algebraMap_eq]

/-- A polynomial `f(x)` in the primitive generator `x = ι R R 1` of the rank-one symmetric algebra
is primitive exactly when `f(X + Y) = f(X) + f(Y)` in the bivariate polynomial ring. -/
theorem isPrimitiveElem_aeval_ι_one_iff {f : R[X]} :
    IsPrimitiveElem R (aeval (ι R R 1) f) ↔ aeval (C X + Y : R[X][Y]) f = C f + f.map C := by
  have hcomul : comul (R := R) (aeval (ι R R 1) f) =
      aeval (ι R R 1 ⊗ₜ[R] 1 + 1 ⊗ₜ[R] ι R R 1) f := by
    rw [← comulAlgHom_apply, ← aeval_algHom_apply, comulAlgHom_apply, comul_ι]
  rw [isPrimitiveElem_iff_comul_eq_tmul_add_tmul, ← tensorEquiv.injective.eq_iff, hcomul,
    ← aeval_algHom_apply]
  simp only [map_add, tensorEquiv_tmul, ← polynomialEquiv_symm_apply, AlgEquiv.apply_symm_apply,
    polynomialEquiv_ι_one, map_one, Polynomial.map_one, mul_one, one_mul, Polynomial.map_X,
    add_comm (f.map C)]

/-- Over a ring of prime characteristic `p`, the primitive elements of the rank-one symmetric
algebra `R[x]`, `x = ι R R 1`, are the `p`-polynomials: the `R`-linear combinations of the powers
`x ^ p ^ i`. -/
theorem isPrimitiveElem_iff_mem_span_ι_one_pow (p : ℕ) [Fact p.Prime] [CharP R p]
    {a : SymmetricAlgebra R R} :
    IsPrimitiveElem R a ↔ a ∈ Submodule.span R (Set.range fun i => ι R R 1 ^ p ^ i) := by
  obtain ⟨f, rfl⟩ := polynomialEquiv.symm.surjective a
  have hspan : Submodule.span R (Set.range fun i => ι R R 1 ^ p ^ i) =
      (Submodule.span R (Set.range fun i => (X : R[X]) ^ p ^ i)).map
        ((polynomialEquiv (R := R)).symm.toLinearEquiv : R[X] →ₗ[R] SymmetricAlgebra R R) := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 1
    ext i
    simp [polynomialEquiv_symm_apply]
  rw [polynomialEquiv_symm_apply, isPrimitiveElem_aeval_ι_one_iff,
    aeval_C_X_add_Y_eq_iff_mem_span p, hspan, Submodule.mem_map_equiv]
  simp [← polynomialEquiv_symm_apply]

end SymmetricAlgebra

namespace BialgHom

open SymmetricAlgebra

variable {R : Type*} [CommRing R]

/-- Over a ring of prime characteristic `p`, a bialgebra endomorphism of the rank-one symmetric
algebra `R[x]`, `x = ι R R 1`, sends `x` to a `p`-polynomial, an `R`-linear combination of the
powers `x ^ p ^ i`: every endomorphism of the additive group is a `p`-polynomial. -/
theorem apply_ι_one_mem_span_ι_one_pow (p : ℕ) [Fact p.Prime] [CharP R p]
    (φ : SymmetricAlgebra R R →ₐc[R] SymmetricAlgebra R R) :
    φ (ι R R 1) ∈ Submodule.span R (Set.range fun i => ι R R 1 ^ p ^ i) := by
  have hx : IsPrimitiveElem R (ι R R 1) :=
    isPrimitiveElem_iff_comul_eq_tmul_add_tmul.mpr (by simp [add_comm])
  have hφ := hx.map φ
  rw [map_one] at hφ
  exact (isPrimitiveElem_iff_mem_span_ι_one_pow p).mp hφ

end BialgHom
