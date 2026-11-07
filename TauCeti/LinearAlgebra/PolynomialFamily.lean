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

*Producing the coefficients.* Conversely, let `K` be a commutative semiring and `f c` a family
of `K`-linear maps between modules with finite bases. If every matrix entry of `f c` against
these bases is a fixed polynomial evaluated at `c`, then `f` is such a power sum: there are a
length `d` and linear maps `A m` with `f c = ∑ m < d, c ^ m • A m` for every `c : K`
(`Module.Basis.exists_forall_eq_sum_pow_smul_of_toMatrix_eq_eval`).

Together they are how a representation of a matrix group whose matrix entries are polynomial
functions is expanded along a one-parameter subgroup and its terms then identified.

## Main results

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

variable {R : Type u} [CommRing R] [IsDomain R] [Infinite R] {M : Type v} [AddCommGroup M]
  [Module R M] [Module.IsTorsionFree R M]

/-- **A power sum with vector coefficients that vanishes identically has zero coefficients.**
Let `R` be an infinite integral domain and `M` a torsion-free `R`-module. If
`∑ m < d, c ^ m • u m = 0` for every `c : R`, then `u m = 0` for every `m < d`. -/
theorem eq_zero_of_forall_sum_range_pow_smul_eq_zero {d : ℕ} {u : ℕ → M}
    (h : ∀ c : R, ∑ m ∈ Finset.range d, c ^ m • u m = 0) {m : ℕ} (hm : m < d) : u m = 0 := by
  -- Evaluating at `d` distinct points shows that their Vandermonde matrix `V` kills the
  -- coefficient vector. Multiplying by the adjugate of `V` gives `det V • u m = 0`, and
  -- `det V ≠ 0` because the points are distinct.
  set V := Matrix.vandermonde fun i : Fin d ↦ Infinite.natEmbedding R i
  have hV : V.det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr
    ((Infinite.natEmbedding R).injective.comp Fin.val_injective)
  have hrow (i : Fin d) : ∑ k, V i k • u k = 0 := by
    simpa [V, Finset.sum_range] using h (Infinite.natEmbedding R i)
  have hdet : V.det • u m = ∑ k, (V.adjugate * V) ⟨m, hm⟩ k • u k := by
    simp [Matrix.adjugate_mul, Matrix.one_apply, ite_smul]
  rw [← smul_eq_zero_iff_right hV, hdet]
  simp_rw [Matrix.mul_apply, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  simp [← Finset.smul_sum, hrow]

/-- **Two power sums with vector coefficients that agree at every point have the same
coefficients.** Let `R` be an infinite integral domain and `M` a torsion-free `R`-module. If
`∑ m < d, c ^ m • u m = ∑ m < d, c ^ m • v m` for every `c : R`, then `u m = v m` for every
`m < d`. -/
theorem eq_of_forall_sum_range_pow_smul_eq {d : ℕ} {u v : ℕ → M}
    (h : ∀ c : R, ∑ m ∈ Finset.range d, c ^ m • u m = ∑ m ∈ Finset.range d, c ^ m • v m)
    {m : ℕ} (hm : m < d) : u m = v m :=
  sub_eq_zero.mp <| eq_zero_of_forall_sum_range_pow_smul_eq_zero (R := R) (u := u - v)
    (fun c ↦ by simp [smul_sub, Finset.sum_sub_distrib, h c]) hm

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
