/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.Bialgebra.Primitive
public import Mathlib.RingTheory.Bialgebra.SymmetricAlgebra
public import TauCeti.Algebra.Polynomial.AdditivePolynomial
public import TauCeti.LinearAlgebra.SymmetricAlgebra.RankOne

/-!
# Primitive elements of the rank-one symmetric algebra

The symmetric algebra `SymmetricAlgebra R R` is the polynomial algebra `R[x]` on the primitive
generator `x = ι R R 1`; with this comultiplication it is the coordinate bialgebra of the additive
group `𝔾ₐ`. Its primitive elements are the homomorphisms `𝔾ₐ → 𝔾ₐ`, and a bialgebra endomorphism
of `R[x]` is determined by the primitive element it sends `x` to.

Identifying `R[x] ⊗[R] R[x]` with the bivariate polynomial ring `R[X][Y]`
(`SymmetricAlgebra.tensorEquivBivariate`), the comultiplication
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

section CommSemiring

variable {R : Type*} [CommSemiring R] [IsCancelAdd R]

/-- A polynomial `f(x)` in the primitive generator `x = ι R R 1` of the rank-one symmetric algebra
is primitive exactly when `f(X + Y) = f(X) + f(Y)` in the bivariate polynomial ring. -/
theorem isPrimitiveElem_aeval_ι_one_iff {f : R[X]} :
    IsPrimitiveElem R (aeval (ι R R 1) f) ↔ aeval (C X + Y : R[X][Y]) f = C f + f.map C := by
  let : IsCancelAdd (SymmetricAlgebra R R) :=
    equivPolynomial.injective.isCancelAdd _ equivPolynomial.map_add
  have hcomul : comul (R := R) (aeval (ι R R 1) f) =
      aeval (ι R R 1 ⊗ₜ[R] 1 + 1 ⊗ₜ[R] ι R R 1) f := by
    rw [← comulAlgHom_apply, ← aeval_algHom_apply, comulAlgHom_apply, comul_ι]
  rw [isPrimitiveElem_iff_comul_eq_tmul_add_tmul, ← tensorEquivBivariate.injective.eq_iff, hcomul,
    ← aeval_algHom_apply]
  simp only [map_add, tensorEquivBivariate_tmul, ← equivPolynomial_symm_apply,
    AlgEquiv.apply_symm_apply, equivPolynomial_ι_one, map_one, Polynomial.map_one, mul_one,
    one_mul, Polynomial.map_X, add_comm (f.map C)]

end CommSemiring

variable {R : Type*} [CommRing R]

/-- Over a ring killed by a prime `p`, the primitive elements of the rank-one symmetric
algebra `R[x]`, `x = ι R R 1`, are the `p`-polynomials: the `R`-linear combinations of the powers
`x ^ p ^ i`. -/
theorem isPrimitiveElem_iff_mem_span_ι_one_pow (p : ℕ) [Fact p.Prime] (hR : (p : R) = 0)
    {a : SymmetricAlgebra R R} :
    IsPrimitiveElem R a ↔ a ∈ Submodule.span R (Set.range fun i => ι R R 1 ^ p ^ i) := by
  obtain ⟨f, rfl⟩ := equivPolynomial.symm.surjective a
  have hspan : Submodule.span R (Set.range fun i => ι R R 1 ^ p ^ i) =
      (Submodule.span R (Set.range fun i => (X : R[X]) ^ p ^ i)).map
        ((equivPolynomial (R := R)).symm.toLinearEquiv : R[X] →ₗ[R] SymmetricAlgebra R R) := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 1
    ext i
    simp [equivPolynomial_symm_apply]
  rw [equivPolynomial_symm_apply, isPrimitiveElem_aeval_ι_one_iff,
    aeval_C_X_add_Y_eq_iff_mem_span p hR, hspan, Submodule.mem_map_equiv]
  simp [← equivPolynomial_symm_apply]

end SymmetricAlgebra

namespace BialgHom

open SymmetricAlgebra

variable {R : Type*} [CommRing R]

/-- Over a ring killed by a prime `p`, a bialgebra endomorphism of the rank-one symmetric
algebra `R[x]`, `x = ι R R 1`, sends `x` to a `p`-polynomial, an `R`-linear combination of the
powers `x ^ p ^ i`: every endomorphism of the additive group is a `p`-polynomial. -/
theorem apply_ι_one_mem_span_ι_one_pow (p : ℕ) [Fact p.Prime] (hR : (p : R) = 0)
    (φ : SymmetricAlgebra R R →ₐc[R] SymmetricAlgebra R R) :
    φ (ι R R 1) ∈ Submodule.span R (Set.range fun i => ι R R 1 ^ p ^ i) := by
  have hx : IsPrimitiveElem R (ι R R 1) :=
    isPrimitiveElem_iff_comul_eq_tmul_add_tmul.mpr (by simp [add_comm])
  have hφ := hx.map φ
  rw [map_one] at hφ
  exact (isPrimitiveElem_iff_mem_span_ι_one_pow p hR).mp hφ

end BialgHom
