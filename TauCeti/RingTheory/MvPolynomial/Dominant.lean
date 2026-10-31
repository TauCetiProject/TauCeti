/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import TauCeti.RingTheory.MvPolynomial.DirectionalOrder
public import TauCeti.RingTheory.MvPolynomial.Jacobian

/-!
# Polynomial maps with surjective differential at a point are dominant

Let `p : ι → R[X_j : j ∈ σ]` be a polynomial map, and suppose that its Jacobian matrix
`TauCeti.jacobiMatrixAt p v` is surjective at one point `v`. Then the components of `p` are
algebraically independent: no nonzero polynomial `q` in the variables `ι` satisfies `q(p) = 0`.
This holds over every commutative ring. Over an infinite domain, where polynomials are determined
by their values, it says that a polynomial vanishing on the image of `p` is zero, so the image of
`p` is Zariski dense.

This is the density statement behind the injectivity half of Chevalley's restriction theorem: an
invariant polynomial function on a semisimple Lie algebra that vanishes on a Cartan subalgebra
vanishes on the image of a polynomial parametrization of conjugates of the Cartan subalgebra whose
differential is surjective at a regular point, and is therefore zero.

## Main results

* `TauCeti.algebraicIndependent_of_mulVec_surjective_jacobiMatrixAt`: a polynomial family whose
  Jacobian matrix is surjective at some point is algebraically independent.
* `TauCeti.eq_zero_of_forall_eval_eq_zero_of_mulVec_surjective_jacobiMatrixAt`: over an infinite
  domain, a polynomial vanishing on the image of such a polynomial map is zero.
-/

public section

namespace TauCeti

open MvPolynomial Matrix

variable {R σ ι : Type*} [CommRing R]

/-- **A polynomial family whose Jacobian matrix is surjective at a point is algebraically
independent.** If the Jacobian matrix of `p : ι → R[X_j : j ∈ σ]` is surjective at one point `v`,
then a polynomial `q` in the variables `ι` with `q(p) = 0` is zero. -/
theorem algebraicIndependent_of_mulVec_surjective_jacobiMatrixAt [Fintype σ] [Finite ι]
    {p : ι → MvPolynomial σ R} {v : σ → R} (hJ : (jacobiMatrixAt p v).mulVec.Surjective) :
    AlgebraicIndependent R p := by
  classical
  cases nonempty_fintype ι
  refine algebraicIndependent_iff.2 fun q hq ↦ ?_
  by_contra hq0
  -- Taylor-expand `q` at the image point `b = p(v)`, and let `q_k` be its lowest nonzero
  -- homogeneous component.
  set b : ι → R := fun i ↦ eval v (p i)
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (orderAt_eq_top_iff.not.2 hq0 : q.orderAt b ≠ ⊤)
  have hqk : homogeneousComponent k (taylor b q) ≠ 0 :=
    homogeneousComponent_ne_zero_of_orderAt_eq q b hk.symm
  -- In Taylor coordinates the map fixes the origin and its linear part is the Jacobian matrix
  -- `J`, so the degree-`k` component of `q(p)`, which vanishes, is `q_k(J Y)`.
  set J := jacobiMatrixAt p v
  set L : ι → MvPolynomial σ R := fun i ↦ ∑ j, J i j • X j
  have hzero : aeval L (homogeneousComponent k (taylor b q)) = 0 := by
    have h := homogeneousComponent_aeval_of_le_order (hk.trans (orderAt_def q b)).le
      (h := fun i ↦ taylor v (p i) - C (b i)) fun i ↦ by simp [b]
    rw [← taylor_aeval, hq, map_zero, map_zero] at h
    simpa [L, J, homogeneousComponent_one_taylor, homogeneousComponent_eq_zero] using h.symm
  -- A right inverse `B` of `J` gives a linear substitution undoing `Y ↦ J Y`, so `q_k = 0`.
  obtain ⟨B, hB⟩ := mulVec_surjective_iff_exists_right_inverse.1 hJ
  have hinv : (aeval fun j ↦ ∑ i, B j i • X i).comp (aeval L) = AlgHom.id R _ := by
    rw [comp_aeval, ← aeval_X_left]
    congr 1
    funext i
    simp only [L, map_sum, map_smul, aeval_X, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp [← Finset.sum_smul, ← Matrix.mul_apply, hB, Matrix.one_apply]
  have h := DFunLike.congr_fun hinv (homogeneousComponent k (taylor b q))
  rw [AlgHom.comp_apply, hzero, map_zero, AlgHom.id_apply] at h
  exact hqk h.symm

/-- **A polynomial vanishing on the image of a polynomial map with surjective differential at a
point is zero.** Over an infinite domain, if `q(p(x)) = 0` at every point `x` and the Jacobian
matrix of `p` is surjective at one point `v`, then `q = 0`. -/
theorem eq_zero_of_forall_eval_eq_zero_of_mulVec_surjective_jacobiMatrixAt [IsDomain R]
    [Infinite R] [Fintype σ] [Finite ι] {p : ι → MvPolynomial σ R} {v : σ → R}
    (hJ : (jacobiMatrixAt p v).mulVec.Surjective) {q : MvPolynomial ι R}
    (hq : ∀ x : σ → R, eval (fun i ↦ eval x (p i)) q = 0) : q = 0 := by
  refine (algebraicIndependent_of_mulVec_surjective_jacobiMatrixAt hJ).eq_zero_of_aeval_eq_zero q
    (MvPolynomial.funext fun x ↦ ?_)
  rw [map_zero, aeval_eq_bind₁, ← hq x]
  simpa only [aeval_eq_eval] using aeval_bind₁ x p q

end TauCeti
