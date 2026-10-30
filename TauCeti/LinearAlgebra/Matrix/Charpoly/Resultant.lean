/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.SplittingField.Construction
import TauCeti.RingTheory.Polynomial.Resultant.Basic

/-!
# Determinants of polynomials in a matrix as resultants

For a square matrix `A` of size `n` over a commutative ring and a polynomial `f` of degree at most
`m`, the determinant of `f(A)` is the resultant of the characteristic polynomial `χ_A` and `f`:

`det f(A) = Res(χ_A, f)`, read with the degree bounds `n` and `m`
(`Matrix.det_aeval_eq_resultant`).

If `χ_A = ∏ (X - αᵢ)` this is `∏ f(αᵢ)`, the determinant form of the spectral mapping theorem.
Applied over `R[T]` to `T - f` it identifies the characteristic polynomial of `f(A)`
(`Matrix.charpoly_aeval_eq_resultant`): `χ_{f(A)}(T) = Res_X(χ_A(X), T - f(X))`. In particular
`χ_{f(A)}` depends on `A` only through `χ_A`. These identities hold over every commutative ring,
including rings with zero divisors, where no factorisation of `χ_A` is available.

The proof is by universality. If `f = c ∏ (X - βⱼ)` splits over a field, then
`f(A) = c ∏ (A - βⱼ)`, and `det (A - β) = (-1) ^ n χ_A(β)` gives `c ^ n ∏ ±χ_A(βⱼ)`, which is the
resultant. Both sides commute with ring homomorphisms, so the identity transfers from a splitting
field of `f` to any integral domain, and from the integral domain `MvPolynomial R ℤ` to its
quotient `R`.

## Main results

* `Matrix.det_aeval_eq_resultant`: `det f(A) = Res(χ_A, f)`.
* `Matrix.charpoly_aeval_eq_resultant`: `χ_{f(A)}(T) = Res_X(χ_A(X), T - f(X))`.
* `Matrix.aeval_map`: evaluating polynomials in a matrix commutes with ring homomorphisms.
-/

public section

namespace Matrix

open Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Evaluating a polynomial in a matrix commutes with applying a ring homomorphism to the
coefficients of the polynomial and to the entries of the matrix. -/
@[simp]
theorem aeval_map {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (A : Matrix ι ι R) (f : R[X]) :
    aeval (A.map φ) (f.map φ) = (aeval A f).map φ := by
  refine (map_aeval_eq_aeval_map (S := Matrix ι ι R) (U := Matrix ι ι S) (φ := φ)
    (ψ := φ.mapMatrix) (RingHom.ext fun r ↦ ?_) f A).symm
  ext i j
  by_cases h : i = j <;> simp [algebraMap_matrix_apply, h]

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The identity `det f(A) = Res(χ_A, f)` for a polynomial `f` that splits over a field. -/
private theorem det_aeval_eq_resultant_of_splits {K : Type*} [Field K] (A : Matrix ι ι K)
    {f : K[X]} (hf : f.Splits) {m : ℕ} (hm : f.natDegree ≤ m) :
    (aeval A f).det = A.charpoly.resultant f (Fintype.card ι) m := by
  -- `g ↦ det g(A)` is multiplicative, so it can be applied factor by factor.
  let detAeval : K[X] →* K := detMonoidHom.comp (aeval A).toMonoidHom
  have hroot (β : K) : detAeval (X - C β) = (-1) ^ Fintype.card ι * A.charpoly.eval β := by
    rw [eval_charpoly, ← det_neg, neg_sub]
    simp [detAeval, algebraMap_eq_diagonal, scalar_apply, Pi.algebraMap_def]
  have hdet : (aeval A f).det = f.leadingCoeff ^ Fintype.card ι *
      ((-1) ^ (Fintype.card ι * f.natDegree) * (f.roots.map A.charpoly.eval).prod) := by
    -- `detAeval f` is `det f(A)` by definition; restate the goal in the multiplicative form.
    change detAeval f = _
    conv_lhs => rw [hf.eq_prod_roots]
    rw [map_mul, map_multiset_prod, Multiset.map_map]
    simp only [Function.comp_def, hroot, Multiset.prod_map_mul, Multiset.map_const',
      Multiset.prod_replicate, ← pow_mul, hf.natDegree_eq_card_roots, mul_comm (Fintype.card ι)]
    simp [detAeval, Algebra.algebraMap_eq_smul_one]
  have hχ := charpoly_natDegree_eq_dim A
  rw [hdet, ← hχ, (charpoly_monic A).resultant_of_le hm,
    ← (charpoly_monic A).resultant_of_le le_rfl, hχ, resultant_comm,
    resultant_eq_prod_eval _ _ _ hχ.le hf]
  ring

/-- Both sides of `det f(A) = Res(χ_A, f)` commute with ring homomorphisms. -/
private theorem map_det_aeval_eq_resultant_iff (φ : R →+* S) (A : Matrix ι ι R) (f : R[X])
    (m : ℕ) :
    φ (aeval A f).det = φ (A.charpoly.resultant f (Fintype.card ι) m) ↔
      (aeval (A.map φ) (f.map φ)).det =
        (A.map φ).charpoly.resultant (f.map φ) (Fintype.card ι) m := by
  rw [aeval_map, RingHom.map_det, RingHom.mapMatrix_apply, ← resultant_map_map, charpoly_map]

/-- The identity `det f(A) = Res(χ_A, f)` over an integral domain, obtained from a splitting
field of `f` over the fraction field. -/
private theorem det_aeval_eq_resultant_of_isDomain [IsDomain R] (A : Matrix ι ι R) (f : R[X])
    {m : ℕ} (hm : f.natDegree ≤ m) :
    (aeval A f).det = A.charpoly.resultant f (Fintype.card ι) m := by
  let K := FractionRing R
  let L := SplittingField (f.map (algebraMap R K))
  have hφ : Function.Injective ((algebraMap K L).comp (algebraMap R K)) :=
    (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  have hf : (f.map ((algebraMap K L).comp (algebraMap R K))).Splits := by
    rw [← Polynomial.map_map]
    exact SplittingField.splits _
  exact hφ ((map_det_aeval_eq_resultant_iff _ A f m).2
    (det_aeval_eq_resultant_of_splits _ hf (natDegree_map_le.trans hm)))

/-- **Determinants of polynomials in a matrix are resultants.** For a square matrix `A` of size
`n` and a polynomial `f` of degree at most `m`, `det f(A) = Res(χ_A, f)`, the resultant of the
characteristic polynomial of `A` and `f` with degree bounds `n` and `m`. If `χ_A = ∏ (X - αᵢ)`,
the right-hand side is `∏ f(αᵢ)`. -/
theorem det_aeval_eq_resultant (A : Matrix ι ι R) (f : R[X]) {m : ℕ} (hm : f.natDegree ≤ m) :
    (aeval A f).det = A.charpoly.resultant f (Fintype.card ι) m := by
  -- Lift `A` and `f` to the integral domain `MvPolynomial R ℤ`, which surjects onto `R`.
  let ψ : MvPolynomial R ℤ →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) id
  have hψ : Function.Surjective ψ := fun r ↦ ⟨.X r, by simp [ψ]⟩
  obtain ⟨f', rfl, hf'⟩ := exists_natDegree_eq_of_mem_lifts (map_surjective ψ hψ f)
  have hA : (A.map MvPolynomial.X).map ψ = A := by ext; simp [ψ]
  have := (map_det_aeval_eq_resultant_iff ψ (A.map MvPolynomial.X) f' m).1 <|
    congrArg ψ (det_aeval_eq_resultant_of_isDomain _ f' (hf'.trans_le hm))
  rwa [hA] at this

/-- **The characteristic polynomial of a polynomial in a matrix.** For a square matrix `A` of size
`n` and a polynomial `f` of degree at most `m`, `χ_{f(A)}(T) = Res_X(χ_A(X), T - f(X))`, the
resultant over `R[T]` with degree bounds `n` and `m`. In particular `χ_{f(A)}` depends on `A` only
through `χ_A`. -/
theorem charpoly_aeval_eq_resultant (A : Matrix ι ι R) (f : R[X]) {m : ℕ}
    (hm : f.natDegree ≤ m) :
    (aeval A f).charpoly = (A.charpoly.map C).resultant (C X - f.map C) (Fintype.card ι) m := by
  have hdeg : (C X - f.map C).natDegree ≤ m :=
    (natDegree_sub_le _ _).trans (max_le (by simp) (natDegree_map_le.trans hm))
  rw [← charpoly_map, ← det_aeval_eq_resultant _ _ hdeg, charpoly, charmatrix, map_sub,
    aeval_C, aeval_map, algebraMap_eq_diagonal, Pi.algebraMap_def, scalar_apply,
    RingHom.mapMatrix_apply, Algebra.algebraMap_self, RingHom.id_apply]

end Matrix
