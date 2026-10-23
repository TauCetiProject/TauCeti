/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import TauCeti.RingTheory.Polynomial.Resultant.Basic

/-!
# Determinants of polynomials in a matrix as resultants

For a square matrix `M` of size `n` over a commutative ring and a polynomial `g` of degree at most
`m`, the determinant of `g(M)` is the resultant of the characteristic polynomial of `M` with `g`,
computed with the degree bounds `n` and `m`:

`det g(M) = Res_{n,m}(χ_M, g)`.

Over a field over which `g` splits as `c ∏ⱼ (X - βⱼ)`, both sides equal `c ^ n ∏ⱼ (-1) ^ n χ_M(βⱼ)`.
The general case is reduced to this one by Mathlib's universal induction principle for resultants,
`Polynomial.induction_of_Splits_of_injective_of_surjective`. No hypothesis on the coefficient ring
is needed, so the identity also holds over rings with nilpotents.

This is the finite-dimensional spectral mapping theorem in resultant form: the eigenvalues of
`g(M)` are the values of `g` at the eigenvalues of `M`, with multiplicity.

## Main results

* `Matrix.map_aeval`: evaluating a polynomial at a matrix commutes with ring homomorphisms.
* `Matrix.det_aeval_eq_resultant_charpoly`: `det g(M) = Res_{n,m}(χ_M, g)`.
-/

public section

open Polynomial

namespace Matrix

variable {ι R S : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S]

/-- Evaluating a polynomial at a matrix commutes with applying a ring homomorphism to the
coefficients of both. -/
theorem map_aeval (M : Matrix ι ι R) (φ : R →+* S) (g : R[X]) :
    (aeval M g).map φ = aeval (M.map φ) (g.map φ) :=
  map_aeval_eq_aeval_map (φ := φ) (ψ := φ.mapMatrix)
    (by ext r : 1; simp [algebraMap_eq_diagonal]) g M

/-- The determinant of `g(M)` is the resultant of the characteristic polynomial of `M` with `g`,
computed at the size of `M` and at any bound `m` for the degree of `g`. -/
theorem det_aeval_eq_resultant_charpoly (M : Matrix ι ι R) (g : R[X]) {m : ℕ}
    (hg : g.natDegree ≤ m) :
    (aeval M g).det = M.charpoly.resultant g (Fintype.card ι) m := by
  induction g using induction_of_Splits_of_injective_of_surjective generalizing m with
  | Splits K g hsplit =>
    -- both sides are `c ^ n ∏ⱼ (-1) ^ n χ_M(βⱼ)`, where `g = c ∏ⱼ (X - βⱼ)`
    rw [← M.charpoly_natDegree_eq_dim, M.charpoly_monic.resultant_of_le hg, resultant_comm,
      resultant_eq_prod_eval g _ _ le_rfl hsplit, M.charpoly_natDegree_eq_dim]
    -- `g ↦ det g(M)` is multiplicative, with values in a commutative ring
    let D : K[X] →* K := detMonoidHom.comp (aeval M).toMonoidHom
    have hD (p : K[X]) : D p = (aeval M p).det := rfl
    have hroot (β : K) : D (X - C β) = (-1) ^ Fintype.card ι * M.charpoly.eval β := by
      rw [hD, eval_charpoly, ← det_neg, neg_sub]
      congr 1
      ext i j
      simp [algebraMap_eq_diagonal, scalar_apply, diagonal_apply, Pi.algebraMap_apply]
    rw [← hD]
    conv_lhs => rw [hsplit.eq_prod_roots]
    rw [map_mul, map_multiset_prod, Multiset.map_map, Function.comp_def]
    simp only [hroot, hD, aeval_C, algebraMap_eq_diagonal, Pi.algebraMap_def,
      Algebra.algebraMap_self, RingHom.id_apply, det_diagonal, Finset.prod_const,
      Finset.card_univ, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
      ← hsplit.natDegree_eq_card_roots, ← pow_mul]
    ring
  | injective R S φ hφ g IH =>
    apply hφ
    rw [RingHom.map_det, RingHom.mapMatrix_apply, map_aeval, ← resultant_map_map, ← charpoly_map]
    exact IH (M.map φ) (natDegree_map_le.trans hg)
  | surjective R S φ hφ g IH =>
    obtain ⟨g, rfl, hdeg⟩ := exists_natDegree_eq_of_mem_lifts (Polynomial.map_surjective φ hφ g)
    obtain ⟨M, rfl⟩ : ∃ M' : Matrix ι ι R, M'.map φ = M :=
      ⟨M.map (Function.surjInv hφ), by ext; simp [Function.surjInv_eq hφ]⟩
    rw [← map_aeval, ← RingHom.mapMatrix_apply, ← RingHom.map_det, charpoly_map,
      resultant_map_map, IH g M (hdeg ▸ hg)]

end Matrix
