/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import TauCeti.LinearAlgebra.Matrix.Polynomial
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

## Main results

* `Matrix.det_aeval_eq_resultant`: `det f(A) = Res(χ_A, f)`.
* `Matrix.charmatrix_aeval`: the characteristic matrix of `f(A)` is `T - f` evaluated at `A`.
* `Matrix.charpoly_aeval_eq_resultant`: `χ_{f(A)}(T) = Res_X(χ_A(X), T - f(X))`.
-/

public section

namespace Matrix

open Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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
  -- The resultant does not depend on the degree bound for `f`, so read it with `f.natDegree`.
  have hbound : A.charpoly.resultant f (Fintype.card ι) m =
      A.charpoly.resultant f (Fintype.card ι) f.natDegree := by
    rw [← hχ, (charpoly_monic A).resultant_of_le hm, (charpoly_monic A).resultant_of_le le_rfl]
  -- Swapping the arguments, the resultant is the product of `χ_A` over the roots of `f`.
  have hprod : A.charpoly.resultant f (Fintype.card ι) f.natDegree =
      (-1) ^ (Fintype.card ι * f.natDegree) *
        (f.leadingCoeff ^ Fintype.card ι * (f.roots.map A.charpoly.eval).prod) := by
    rw [resultant_comm, resultant_eq_prod_eval _ _ _ hχ.le hf]
  rw [hdet, hbound, hprod]
  ring

/-- Both sides of `det f(A) = Res(χ_A, f)` commute with ring homomorphisms. -/
private theorem map_det_aeval_eq_resultant_iff (φ : R →+* S) (A : Matrix ι ι R) (f : R[X])
    (m : ℕ) :
    φ (aeval A f).det = φ (A.charpoly.resultant f (Fintype.card ι) m) ↔
      (aeval (A.map φ) (f.map φ)).det =
        (A.map φ).charpoly.resultant (f.map φ) (Fintype.card ι) m := by
  rw [aeval_map, RingHom.map_det, RingHom.mapMatrix_apply, ← resultant_map_map, charpoly_map]

/- The proof is by universality. If `f = c ∏ (X - βⱼ)` splits over a field, then
`f(A) = c ∏ (A - βⱼ)`, and `det (A - β) = (-1) ^ n χ_A(β)` gives `c ^ n ∏ ±χ_A(βⱼ)`, which is the
resultant. Both sides commute with ring homomorphisms, so the identity transfers along injective
ring homomorphisms and surjective covers. Mathlib's universality principle for resultants,
`Polynomial.induction_of_Splits_of_injective_of_surjective`, then extends it from split
polynomials over fields to every commutative ring. -/

/-- **Determinants of polynomials in a matrix are resultants.** For a square matrix `A` of size
`n` and a polynomial `f` of degree at most `m`, `det f(A) = Res(χ_A, f)`, the resultant of the
characteristic polynomial of `A` and `f` with degree bounds `n` and `m`. If `χ_A = ∏ (X - αᵢ)`,
the right-hand side is `∏ f(αᵢ)`. -/
theorem det_aeval_eq_resultant (A : Matrix ι ι R) (f : R[X]) {m : ℕ} (hm : f.natDegree ≤ m) :
    (aeval A f).det = A.charpoly.resultant f (Fintype.card ι) m := by
  induction f using induction_of_Splits_of_injective_of_surjective generalizing m with
  | Splits K f hf => exact det_aeval_eq_resultant_of_splits A hf hm
  | injective R S φ hφ f IH =>
    exact hφ ((map_det_aeval_eq_resultant_iff φ A f m).2 (IH _ (natDegree_map_le.trans hm)))
  | surjective R S φ hφ f IH =>
    -- Lift the entries of `A` and the coefficients of `f`, keeping the degree of `f`.
    obtain ⟨f', rfl, hf'⟩ := exists_natDegree_eq_of_mem_lifts (map_surjective φ hφ f)
    have hA : (A.map (Function.surjInv hφ)).map φ = A := by
      ext; simp [Function.surjInv_eq hφ]
    rw [← hA]
    exact (map_det_aeval_eq_resultant_iff φ _ f' m).1
      (congrArg φ (IH f' _ (hf'.trans_le hm)))

/-- The characteristic matrix of `f(A)` is `T - f` evaluated at `A`, read over `R[T]`. -/
theorem charmatrix_aeval (A : Matrix ι ι R) (f : R[X]) :
    (aeval A f).charmatrix = aeval (A.map C) (C X - f.map C) := by
  simp [charmatrix, aeval_map, algebraMap_eq_diagonal, Pi.algebraMap_def, scalar_apply]

/-- **The characteristic polynomial of a polynomial in a matrix.** For a square matrix `A` of size
`n` and a polynomial `f` of degree at most `m`, `χ_{f(A)}(T) = Res_X(χ_A(X), T - f(X))`, the
resultant over `R[T]` with degree bounds `n` and `m`. In particular `χ_{f(A)}` depends on `A` only
through `χ_A`. -/
theorem charpoly_aeval_eq_resultant (A : Matrix ι ι R) (f : R[X]) {m : ℕ}
    (hm : f.natDegree ≤ m) :
    (aeval A f).charpoly = (A.charpoly.map C).resultant (C X - f.map C) (Fintype.card ι) m := by
  have hdeg : (C X - f.map C).natDegree ≤ m :=
    (natDegree_sub_le _ _).trans (max_le (by simp) (natDegree_map_le.trans hm))
  rw [← charpoly_map, ← det_aeval_eq_resultant _ _ hdeg, charpoly, charmatrix_aeval]

end Matrix
