/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Vandermonde

/-!
# Families of vectors and operators depending polynomially on a parameter

A family `c ↦ ∑ m < d, c ^ m • u m` of vectors of a module, or of linear maps between modules, is
the general shape of a family depending polynomially on a scalar parameter. This file proves the
two statements such a family is used through.

*Recovering the coefficients.* Let `R` be an infinite integral domain and `M` a torsion-free
`R`-module. Then the coefficients of a power sum in `M` are determined by its values: if
`∑ m < d, c ^ m • u m = 0` for every `c : R`, then `u m = 0` for every `m < d`
(`TauCeti.eq_zero_of_forall_sum_range_pow_smul_eq_zero`), and two power sums of the same length
that agree at every `c : R` have the same coefficients below that length
(`TauCeti.eq_of_forall_sum_range_pow_smul_eq`). Neither hypothesis can be dropped. Over the
finite field `𝔽₂` the functions `c ↦ c` and `c ↦ c ^ 2` agree. In the `ℤ`-module `ℤ/2`, which
has torsion, `c ↦ c • 1` and `c ↦ c ^ 2 • 1` agree.
Over an arbitrary commutative ring the values still determine the coefficients up to the
Vandermonde determinant of the evaluation points, by Cramer's rule
(`TauCeti.det_vandermonde_smul_eq_sum_adjugate_smul`). For instance, if the points and the values
lie in a subring `S`, then the determinant times each coefficient lies in `S`.

*Producing the coefficients.* Conversely, let `K` be a commutative semiring and `f c` a family
of `K`-linear maps between modules with finite bases. If every matrix entry of `f c` against
these bases is a fixed polynomial evaluated at `c`, then `f` is such a power sum: there are a
length `d` and linear maps `A m` with `f c = ∑ m < d, c ^ m • A m` for every `c : K`
(`Module.Basis.exists_forall_eq_sum_pow_smul_of_toMatrix_eq_eval`).

Together they are how a representation of a matrix group whose matrix entries are polynomial
functions is expanded along a one-parameter subgroup and its terms then identified.

## Main results

* `TauCeti.det_vandermonde_smul_eq_sum_adjugate_smul`: over any commutative ring, the
  Vandermonde determinant of `d` points times a coefficient of a power sum of length `d` is a
  linear combination of the values of the power sum at the points.
* `TauCeti.eq_zero_of_forall_sum_range_pow_smul_eq_zero`: the coefficients below `d` of an
  identically vanishing power sum `∑ m < d, c ^ m • u m` are zero.
* `TauCeti.eq_of_forall_sum_range_pow_smul_eq`: two power sums of length `d` agreeing at every
  point have the same coefficients below `d`.
* `Module.Basis.exists_forall_eq_sum_pow_smul_of_toMatrix_eq_eval`: a family of linear maps
  with polynomial matrix entries is a finite power sum of fixed linear maps.
-/

public section

universe u v v' w w'

namespace TauCeti

/-! ## Recovering the coefficients from the values -/

section Coefficients

/-- **Cramer's rule for power sums.** Over any commutative ring, the Vandermonde determinant of
`d` points `x i` times a coefficient `u m` of a power sum `c ↦ ∑ k < d, c ^ k • u k` is a fixed
linear combination of the values of the power sum at the points, with coefficients the entries of
the adjugate of the Vandermonde matrix. -/
theorem det_vandermonde_smul_eq_sum_adjugate_smul {R : Type u} [CommRing R] {M : Type v}
    [AddCommMonoid M] [Module R M] {d : ℕ} (x : Fin d → R) (u : ℕ → M) (m : Fin d) :
    (Matrix.vandermonde x).det • u m = ∑ i, (Matrix.vandermonde x).adjugate m i •
      ∑ k ∈ Finset.range d, x i ^ k • u k := by
  set V := Matrix.vandermonde x
  have hdet : V.det • u m = ∑ k, (V.adjugate * V) m k • u k := by
    simp [Matrix.adjugate_mul, Matrix.one_apply, ite_smul]
  rw [hdet]
  simp_rw [Matrix.mul_apply, Finset.sum_smul, mul_smul, ← Fin.sum_univ_eq_sum_range
    (fun k ↦ x _ ^ k • u k), Finset.smul_sum]
  rw [Finset.sum_comm]
  simp [V, Matrix.vandermonde_apply]

variable {R : Type u} [CommRing R] [IsDomain R] [Infinite R] {M : Type v} [AddCommMonoid M]
  [Module R M] [Module.IsTorsionFree R M]

/-- **A power sum with vector coefficients that vanishes identically has zero coefficients.**
Let `R` be an infinite integral domain and `M` a torsion-free `R`-module. If
`∑ m < d, c ^ m • u m = 0` for every `c : R`, then `u m = 0` for every `m < d`. -/
theorem eq_zero_of_forall_sum_range_pow_smul_eq_zero {d : ℕ} {u : ℕ → M}
    (h : ∀ c : R, ∑ m ∈ Finset.range d, c ^ m • u m = 0) {m : ℕ} (hm : m < d) : u m = 0 := by
  -- Evaluating at `d` distinct points and applying Cramer's rule gives `det V • u m = 0` for
  -- their Vandermonde matrix `V`, and `det V ≠ 0` because the points are distinct.
  set x : Fin d → R := fun i ↦ Infinite.natEmbedding R i
  have hV : (Matrix.vandermonde x).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr
    ((Infinite.natEmbedding R).injective.comp Fin.val_injective)
  rw [← smul_eq_zero_iff_right hV]
  simpa [x, h] using det_vandermonde_smul_eq_sum_adjugate_smul x u ⟨m, hm⟩

/-- **Two power sums with vector coefficients that agree at every point have the same
coefficients.** Let `R` be an infinite integral domain and `M` a torsion-free `R`-module. If
`∑ m < d, c ^ m • u m = ∑ m < d, c ^ m • v m` for every `c : R`, then `u m = v m` for every
`m < d`. -/
theorem eq_of_forall_sum_range_pow_smul_eq {d : ℕ} {u v : ℕ → M}
    (h : ∀ c : R, ∑ m ∈ Finset.range d, c ^ m • u m = ∑ m ∈ Finset.range d, c ^ m • v m)
    {m : ℕ} (hm : m < d) : u m = v m := by
  -- Cramer's rule at `d` distinct points expresses `det V • u m` and `det V • v m` through the
  -- same values, and `det V ≠ 0` because the points are distinct.
  set x : Fin d → R := fun i ↦ Infinite.natEmbedding R i
  have hV : (Matrix.vandermonde x).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr
    ((Infinite.natEmbedding R).injective.comp Fin.val_injective)
  rw [← smul_right_inj hV, det_vandermonde_smul_eq_sum_adjugate_smul x u ⟨m, hm⟩,
    det_vandermonde_smul_eq_sum_adjugate_smul x v ⟨m, hm⟩]
  simp only [h]

end Coefficients

end TauCeti

/-! ## Producing the coefficients from polynomial matrix entries -/

-- The leading explicit argument is a `Module.Basis`, so this lives in its namespace and is used
-- through dot notation.
namespace Module.Basis

/-- **A family of linear maps whose matrix entries are polynomial in the parameter is a finite
power sum of fixed linear maps.** Let `K` be a commutative semiring, `b` and `b'` finite bases of
`V` and `W`, and `f : K → V →ₗ[K] W`. If the matrix of `f c` against `b` and `b'` has entries
`(Q a a').eval c` for every `c : K`, then there are `d : ℕ` and linear maps `A m : V →ₗ[K] W`
with `f c = ∑ m < d, c ^ m • A m` for every `c : K`. -/
theorem exists_forall_eq_sum_pow_smul_of_toMatrix_eq_eval {K : Type u} [CommSemiring K]
    {V : Type v} {W : Type v'} [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W]
    {ι : Type w} {κ : Type w'} [Fintype ι] [Finite κ] [DecidableEq ι]
    (b : Module.Basis ι K V) (b' : Module.Basis κ K W) (f : K → V →ₗ[K] W)
    (Q : κ → ι → Polynomial K)
    (hQ : ∀ (c : K) (a : κ) (a' : ι), LinearMap.toMatrix b b' (f c) a a' = (Q a a').eval c) :
    ∃ (d : ℕ) (A : ℕ → V →ₗ[K] W), ∀ c : K, f c = ∑ m ∈ Finset.range d, c ^ m • A m := by
  have := Fintype.ofFinite κ
  refine ⟨(Finset.univ.sup fun q : κ × ι ↦ (Q q.1 q.2).natDegree) + 1,
    fun m ↦ (LinearMap.toMatrix b b').symm (.of fun a a' ↦ (Q a a').coeff m), fun c ↦ ?_⟩
  refine (LinearMap.toMatrix b b').injective ?_
  ext a a'
  have hdeg : (Q a a').natDegree < (Finset.univ.sup fun q : κ × ι ↦ (Q q.1 q.2).natDegree) + 1 :=
    Nat.lt_succ_of_le <| Finset.le_sup (f := fun q : κ × ι ↦ (Q q.1 q.2).natDegree)
      (Finset.mem_univ (a, a'))
  simp [hQ, Polynomial.eval_eq_sum_range' hdeg, Matrix.sum_apply, mul_comm]

end Module.Basis
