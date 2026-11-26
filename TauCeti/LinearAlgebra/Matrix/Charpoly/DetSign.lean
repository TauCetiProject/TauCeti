/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Sign.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Polynomial.Order
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Zero
import TauCeti.Algebra.Ring.Parity
import TauCeti.Analysis.Polynomial.RealRoots.Product
import TauCeti.Data.Multiset.Filter
import TauCeti.Data.SignType.Basic
import TauCeti.LinearAlgebra.Matrix.Charpoly.Roots

/-!
# Signs of `det (1 - A ^ k)` from the real eigenvalues of `A`

For a real square matrix `A` and a real polynomial `f`, the determinant of `f(A)` is a nonnegative
multiple of the product of `f(x)` over the real characteristic roots `x` of `A`, counted with
algebraic multiplicity: each conjugate pair `λ, conj λ` of nonreal eigenvalues contributes
`|f(λ)|² ≥ 0`. So whenever `det (f(A)) ≠ 0`, its sign is the product of the signs of `f(x)` over
the real eigenvalues.

For `f = 1 - X ^ k` this computes the Lefschetz sign `ε(A ^ k) = sgn det (1 - A ^ k)` of the
`k`-th iterate of a linearized return map `A`. Write `i₊` and `i₋` for the numbers of real
eigenvalues of `A` in `(1, ∞)` and in `(-∞, -1)`, and `i₀` for the number in `(-1, 1)`, all with
algebraic multiplicity. If `1 - A ^ k` is invertible then

`ε(A ^ k) = (-1) ^ i₊ * (-1) ^ ((k + 1) i₋)`.

In particular `ε(A) = (-1) ^ i₊`. If `1 - A ^ k` is invertible for every positive `k`, then the
signs `ε(A ^ k)` alternate in `k` exactly when `i₋` is odd, and are constant otherwise. If no
eigenvalue is `± 1`, the number of nonreal eigenvalues is even, so
`(-1) ^ (i₊ + i₋) = (-1) ^ (n + i₀)` for an `n × n` matrix. For a closed orbit all of whose
iterates are nondegenerate, these identities make the exponential of the logarithmic series
`∑_k ε(A ^ k) t ^ k / k` equal to the factor `(1 - (-1) ^ i₋ t) ^ (-(-1) ^ (i₊ + i₋))` of a
dynamical zeta function; that series identity is
`TauCeti.NovikovSeries.orbitZeta_sign_det_one_sub_pow_eq_eulerProduct`, in
`TauCeti.RingTheory.NovikovSeries.OrbitZeta.ReturnMap`.

Without counting roots, the location of the real eigenvalues of an endomorphism `f` of a
finite-dimensional real vector space `V` already fixes the sign of `det (1 - f)`. If `f` has no
real eigenvalue `μ ≥ 1`, then `det (1 - f) > 0`, since the monic characteristic polynomial has no
root at or beyond `1`. If `f` has no real eigenvalue in `[0, 1]`, then
`sgn det (1 - f) = (-1) ^ (dim V) * sgn det f`, since `1 - f = (-f) (1 - f⁻¹)` and `f⁻¹` has no
real eigenvalue `μ ≥ 1`. For a map `f × g` of `V × W` that expands along `V` and contracts along
`W` in this sense, `sgn det (1 - f × g) = (-1) ^ (dim V) * sgn det f`. This is the sign
`sgn det (1 - A)` of the fixed-point index of a linear map `A` at its nondegenerate fixed point
`0`, at a fixed point expanding along one factor and contracting across it.

## Main results

* `Matrix.exists_det_aeval_eq_mul_prod_roots`: `det (f(A)) = c ∏ f(x)` over the real
  characteristic roots `x` of `A`, for some real `c ≥ 0`.
* `Matrix.sign_det_aeval`: if `det (f(A)) ≠ 0`, its sign is `∏ sgn f(x)` over the real roots.
* `Matrix.sign_det_one_sub_pow`, `LinearMap.sign_det_one_sub_pow`: the iterate sign formula
  `sgn det (1 - A ^ k) = (-1) ^ i₊ * (-1) ^ ((k + 1) i₋)`.
* `Matrix.sign_det_one_sub`, `LinearMap.sign_det_one_sub`: the case `k = 1`,
  `sgn det (1 - A) = (-1) ^ i₊`.
* `Matrix.sign_det_one_sub_pow_succ`, `LinearMap.sign_det_one_sub_pow_succ`: the signs of the
  iterates form a geometric sequence with ratio `(-1) ^ i₋`.
* `Matrix.neg_one_pow_card_roots_charpoly`: the number of real characteristic roots has the parity
  of the size of the matrix.
* `Matrix.neg_one_pow_card_filter_one_lt_add_card_filter_lt_neg_one`,
  `LinearMap.neg_one_pow_card_filter_one_lt_add_card_filter_lt_neg_one`: if `1 - A ^ 2` is
  invertible, `(-1) ^ (i₊ + i₋) = (-1) ^ (n + i₀)`.
* `Matrix.neg_one_pow_card_filter_lt_neg_one_of_det_pos`,
  `LinearMap.neg_one_pow_card_filter_lt_neg_one_of_det_pos`: if `0 < det A` and `1 + A` is
  invertible, the numbers of real eigenvalues in `(-∞, -1)` and in `(-1, 0)` have the same parity.
  For a symplectic `A` this lets `i₋` be read off from the eigenvalues in `(-1, 0)`.
* `LinearMap.det_one_sub_pos_of_not_hasEigenvalue`: no real eigenvalue `μ ≥ 1` gives
  `0 < det (1 - f)`.
* `LinearMap.sign_det_one_sub_of_not_hasEigenvalue`: no real eigenvalue in `[0, 1]` gives
  `sgn det (1 - f) = (-1) ^ (dim V) * sgn det f`.
* `LinearMap.sign_det_one_sub_prodMap_of_not_hasEigenvalue`,
  `LinearMap.det_one_sub_prodMap_ne_zero_of_not_hasEigenvalue`: the sign, and the nonvanishing, of
  `det (1 - f × g)` at an expanding-contracting splitting.
* `LinearMap.det_one_add_ne_zero_of_det_one_sub_pow_ne_zero`: if `k` is even and `1 - f ^ k` has
  nonzero determinant, so does `1 + f`.

## References

* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory and Reidemeister torsion*,
  Geom. Topol. 3 (1999), 369–396 (the signs of closed orbits and their iterates in the product
  formula for the zeta function).
* D. Fried, *Lefschetz formulas for flows*, Contemp. Math. 58, Part III (1987), 19–69.
* A. Dold, *Lectures on Algebraic Topology*, Springer, 1972, Chapter VII, §5 (the fixed-point
  index of a linear map).
-/

public section

open Polynomial

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- For a real square matrix `A` and a real polynomial `f`, `det (f(A))` is a nonnegative multiple
of the product of `f(x)` over the real characteristic roots `x` of `A`, counted with algebraic
multiplicity. -/
theorem exists_det_aeval_eq_mul_prod_roots (A : Matrix n n ℝ) (f : ℝ[X]) :
    ∃ c : ℝ, 0 ≤ c ∧ (aeval A f).det = c * (A.charpoly.roots.map f.eval).prod := by
  obtain ⟨c, hc, h⟩ := A.charpoly.exists_prod_aroots_eq_mul_prod_roots f
  refine ⟨c, hc, Complex.ofReal_injective ?_⟩
  -- Over `ℂ`, `det (f(A))` is the product of `f` over all characteristic roots of `A`.
  have hmap : (algebraMap ℝ ℂ).mapMatrix (aeval A f) = aeval (A.map (algebraMap ℝ ℂ)) f := by
    simpa using (aeval_algHom_apply (Complex.ofRealAm.mapMatrix (m := n)) A f).symm
  -- The complex characteristic roots of `A` are the complex roots of its real charpoly.
  have hroots : (A.map (algebraMap ℝ ℂ)).charpoly.roots = A.charpoly.aroots ℂ := by
    rw [charpoly_map, aroots_def]
  have hdet : ((aeval A f).det : ℂ) =
      (A.charpoly.aroots ℂ |>.map fun z ↦ aeval z f).prod := by
    rw [← Complex.coe_algebraMap, RingHom.map_det, hmap, ← aeval_map_algebraMap ℂ,
      det_aeval_eq_prod_roots_charpoly, hroots]
    simp [eval_map_algebraMap]
  exact hdet.trans h

/-- If `det (f(A)) ≠ 0` for a real square matrix `A` and a real polynomial `f`, its sign is the
product of the signs of `f(x)` over the real characteristic roots `x` of `A`, counted with
algebraic multiplicity. -/
theorem sign_det_aeval (A : Matrix n n ℝ) (f : ℝ[X]) (h : (aeval A f).det ≠ 0) :
    SignType.sign (aeval A f).det =
      (A.charpoly.roots.map fun x ↦ SignType.sign (f.eval x)).prod := by
  obtain ⟨c, hc, hdet⟩ := A.exists_det_aeval_eq_mul_prod_roots f
  have hc : 0 < c := hc.lt_of_ne (by rintro rfl; simp_all)
  rw [hdet, sign_mul, sign_pos hc, one_mul, ← signHom_apply, map_multiset_prod, Multiset.map_map]
  simp

/-- **The sign of an iterate.** If `1 - A ^ k` is invertible for a real square matrix `A`, then
`sgn det (1 - A ^ k) = (-1) ^ i₊ * (-1) ^ ((k + 1) i₋)`, where `i₊` and `i₋` count the real
characteristic roots of `A` in `(1, ∞)` and in `(-∞, -1)`, with algebraic multiplicity. -/
theorem sign_det_one_sub_pow (A : Matrix n n ℝ) (k : ℕ) (h : (1 - A ^ k).det ≠ 0) :
    SignType.sign (1 - A ^ k).det =
      (-1) ^ (A.charpoly.roots.filter (1 < ·)).card *
        (-1) ^ ((k + 1) * (A.charpoly.roots.filter (· < -1)).card) := by
  have haeval : aeval A (1 - X ^ k : ℝ[X]) = 1 - A ^ k := by simp
  rw [← haeval] at h ⊢
  rw [sign_det_aeval A _ h, Multiset.map_congr rfl fun x hx ↦ by
    rw [eval_sub, eval_one, eval_pow, eval_X,
      TauCeti.sign_one_sub_pow (by simpa using eval_ne_zero_of_det_aeval_ne_zero A _ h hx)]]
  rw [Multiset.prod_map_mul, Multiset.prod_map_ite_one, Multiset.prod_map_ite_one, pow_mul]

/-- If `1 - A` is invertible for a real square matrix `A`, then `sgn det (1 - A) = (-1) ^ i₊`, where
`i₊` counts the real characteristic roots of `A` in `(1, ∞)`, with algebraic multiplicity. -/
theorem sign_det_one_sub (A : Matrix n n ℝ) (h : (1 - A).det ≠ 0) :
    SignType.sign (1 - A).det = (-1) ^ (A.charpoly.roots.filter (1 < ·)).card := by
  simpa [pow_mul] using A.sign_det_one_sub_pow 1 (by simpa)

/-- **The signs of the iterates form a geometric sequence.** If `1 - A ^ (k + 1)` is invertible for
a real square matrix `A`, then `sgn det (1 - A ^ (k + 1)) = sgn det (1 - A) * σ ^ k` with ratio
`σ = (-1) ^ i₋`, where `i₋` counts the real characteristic roots of `A` in `(-∞, -1)`, with
algebraic multiplicity. -/
theorem sign_det_one_sub_pow_succ (A : Matrix n n ℝ) (k : ℕ) (h : (1 - A ^ (k + 1)).det ≠ 0) :
    SignType.sign (1 - A ^ (k + 1)).det =
      SignType.sign (1 - A).det * ((-1) ^ (A.charpoly.roots.filter (· < -1)).card) ^ k := by
  have h₁ : (1 - A).det ≠ 0 :=
    left_ne_zero_of_mul (by rwa [← det_mul, mul_neg_geom_sum])
  rw [A.sign_det_one_sub_pow _ h, A.sign_det_one_sub h₁, ← pow_mul,
    ← TauCeti.neg_one_pow_add_two_mul (_ * k) (A.charpoly.roots.filter (· < -1)).card]
  ring_nf

/-- The number of real characteristic roots of a real square matrix, counted with algebraic
multiplicity, has the parity of its size: the nonreal roots come in conjugate pairs. -/
theorem neg_one_pow_card_roots_charpoly (A : Matrix n n ℝ) :
    (-1 : SignType) ^ A.charpoly.roots.card = (-1) ^ Fintype.card n := by
  have h : (aeval A (C (-1 : ℝ))).det = (-1) ^ Fintype.card n := by simp [det_neg]
  have h0 : (aeval A (C (-1 : ℝ))).det ≠ 0 := by rw [h]; simp
  have := sign_det_aeval A _ h0
  rw [h, sign_pow] at this
  simpa using this.symm

/-- If `1 - A ^ 2` is invertible for a real `n × n` matrix `A`, so that no eigenvalue is `± 1`,
then `(-1) ^ (i₊ + i₋) = (-1) ^ (n + i₀)`, where `i₊`, `i₋` and `i₀` count the real characteristic
roots of `A` in `(1, ∞)`, in `(-∞, -1)` and in `(-1, 1)`, with algebraic multiplicity. -/
theorem neg_one_pow_card_filter_one_lt_add_card_filter_lt_neg_one (A : Matrix n n ℝ)
    (h : (1 - A ^ 2).det ≠ 0) :
    (-1 : SignType) ^ ((A.charpoly.roots.filter (1 < ·)).card +
        (A.charpoly.roots.filter (· < -1)).card) =
      (-1) ^ (Fintype.card n + (A.charpoly.roots.filter (|·| < 1)).card) := by
  have haeval : aeval A (1 - X ^ 2 : ℝ[X]) = 1 - A ^ 2 := by simp
  rw [← haeval] at h
  -- No characteristic root is `± 1`, so each lies in exactly one of the three ranges.
  have hroots : (-1 : SignType) ^ A.charpoly.roots.card =
      (-1) ^ (A.charpoly.roots.filter (1 < ·)).card *
        (-1) ^ (A.charpoly.roots.filter (· < -1)).card *
          (-1) ^ (A.charpoly.roots.filter (|·| < 1)).card := by
    rw [← Multiset.prod_map_ite_one, ← Multiset.prod_map_ite_one, ← Multiset.prod_map_ite_one,
      ← Multiset.prod_map_mul, ← Multiset.prod_map_mul, ← Multiset.prod_replicate,
      ← Multiset.map_const']
    refine congrArg _ (Multiset.map_congr rfl fun x hx ↦ ?_)
    have hx := eval_ne_zero_of_det_aeval_ne_zero A _ h hx
    simp only [eval_sub, eval_one, eval_pow, eval_X] at hx
    have h1 : x ≠ 1 := by rintro rfl; simp at hx
    have h2 : x ≠ -1 := by rintro rfl; simp at hx
    rcases lt_trichotomy x 1 with hx1 | rfl | hx1
    · rcases lt_trichotomy x (-1) with hx2 | rfl | hx2
      · simp [hx2, (by linarith : ¬ 1 < x), abs_lt, (by linarith : ¬ -1 < x)]
      · exact absurd rfl h2
      · simp [hx1.not_gt, hx2.not_gt, abs_lt, hx1, hx2]
    · exact absurd rfl h1
    · simp [hx1, (by linarith : ¬ x < -1), abs_lt, hx1.not_gt]
  rw [pow_add, pow_add (-1 : SignType), ← neg_one_pow_card_roots_charpoly A, hroots, mul_assoc,
    pow_mul_pow_eq_one _ (by simp), mul_one]

/-- If `0 < det A` for a real square matrix `A` and `1 + A` is invertible, the numbers of real
characteristic roots of `A` in `(-∞, -1)` and in `(-1, 0)`, counted with algebraic multiplicity,
have the same parity: a positive determinant forces an even number of negative real roots. -/
theorem neg_one_pow_card_filter_lt_neg_one_of_det_pos (A : Matrix n n ℝ) (hA : 0 < A.det)
    (h : (1 + A).det ≠ 0) :
    (-1 : SignType) ^ (A.charpoly.roots.filter (· < -1)).card =
      (-1) ^ (A.charpoly.roots.filter (· ∈ Set.Ioo (-1) 0)).card := by
  have hX : (aeval A (X : ℝ[X])).det ≠ 0 := by rw [aeval_X]; exact hA.ne'
  have h1X : (aeval A (1 + X : ℝ[X])).det ≠ 0 := by simpa using h
  -- The sign of a real root `x ≠ 0, -1` records whether it lies in `(-∞, -1)` or `(-1, 0)`.
  have hsign : A.charpoly.roots.map (fun x ↦ SignType.sign (eval x X)) =
      A.charpoly.roots.map fun x ↦
        (if x < -1 then -1 else 1) * (if x ∈ Set.Ioo (-1) 0 then -1 else 1) := by
    refine Multiset.map_congr rfl fun x hx ↦ ?_
    have h0 : x ≠ 0 := by simpa using eval_ne_zero_of_det_aeval_ne_zero A _ hX hx
    have h1 : x ≠ -1 := by
      rintro rfl
      simpa using eval_ne_zero_of_det_aeval_ne_zero A _ h1X hx
    rw [eval_X]
    rcases h0.lt_or_gt with hx0 | hx0
    · rcases h1.lt_or_gt with hx1 | hx1 <;> simp [hx0, hx1, hx1.not_gt]
    · simp [hx0, hx0.not_gt, (by linarith : ¬ x < -1)]
  have hdet := sign_det_aeval A X hX
  rw [aeval_X, sign_pos hA, hsign, Multiset.prod_map_mul, Multiset.prod_map_ite_one,
    Multiset.prod_map_ite_one] at hdet
  calc (-1 : SignType) ^ (A.charpoly.roots.filter (· < -1)).card
      = (-1) ^ (A.charpoly.roots.filter (· < -1)).card *
          ((-1) ^ (A.charpoly.roots.filter (· < -1)).card *
            (-1) ^ (A.charpoly.roots.filter (· ∈ Set.Ioo (-1) 0)).card) := by
        rw [← hdet, mul_one]
    _ = (-1) ^ (A.charpoly.roots.filter (· ∈ Set.Ioo (-1) 0)).card := by
        exact TauCeti.neg_one_pow_mul_neg_one_pow_mul _ _

end Matrix

namespace LinearMap

/-- If `k` is even and `1 - f ^ k` has nonzero determinant, then so does `1 + f`: the factor
`1 + f` divides `1 - f ^ k`. -/
theorem det_one_add_ne_zero_of_det_one_sub_pow_ne_zero {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (f : Module.End R M) {k : ℕ} (hk : Even k)
    (h : (1 - f ^ k).det ≠ 0) : (1 + f).det ≠ 0 := by
  obtain ⟨m, rfl⟩ := hk
  have hfac : (1 + f) * ((1 - f) * ∑ i ∈ Finset.range m, (f ^ 2) ^ i) = 1 - f ^ (m + m) := by
    rw [← two_mul, pow_mul, ← mul_neg_geom_sum, ← mul_assoc]
    congr 1
    noncomm_ring
  exact left_ne_zero_of_mul (by rwa [← map_mul, hfac])

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- **The sign of an iterate**, for an endomorphism `f` of a finite-dimensional real vector space:
if `1 - f ^ k` is invertible, then `sgn det (1 - f ^ k) = (-1) ^ i₊ * (-1) ^ ((k + 1) i₋)`, where
`i₊` and `i₋` count the real roots of the characteristic polynomial of `f` in `(1, ∞)` and in
`(-∞, -1)`, with multiplicity. -/
theorem sign_det_one_sub_pow (f : Module.End ℝ V) (k : ℕ) (h : (1 - f ^ k).det ≠ 0) :
    SignType.sign (1 - f ^ k).det =
      (-1) ^ (f.charpoly.roots.filter (1 < ·)).card *
        (-1) ^ ((k + 1) * (f.charpoly.roots.filter (· < -1)).card) := by
  let b := Module.finBasis ℝ V
  have hmat : toMatrix b b (1 - f ^ k) = 1 - toMatrix b b f ^ k := by
    rw [map_sub, toMatrix_one, toMatrix_pow]
  rw [← det_toMatrix b, hmat] at h ⊢
  rw [← charpoly_toMatrix f b]
  exact (toMatrix b b f).sign_det_one_sub_pow k h

/-- If `1 - f` is invertible for an endomorphism `f` of a finite-dimensional real vector space,
then `sgn det (1 - f) = (-1) ^ i₊`, where `i₊` counts the real roots of the characteristic
polynomial of `f` in `(1, ∞)`, with multiplicity. -/
theorem sign_det_one_sub (f : Module.End ℝ V) (h : (1 - f).det ≠ 0) :
    SignType.sign (1 - f).det = (-1) ^ (f.charpoly.roots.filter (1 < ·)).card := by
  simpa [pow_mul] using f.sign_det_one_sub_pow 1 (by simpa)

/-- **The signs of the iterates form a geometric sequence**, for an endomorphism `f` of a
finite-dimensional real vector space: if `1 - f ^ (k + 1)` is invertible, then
`sgn det (1 - f ^ (k + 1)) = sgn det (1 - f) * σ ^ k` with ratio `σ = (-1) ^ i₋`, where `i₋` counts
the real roots of the characteristic polynomial of `f` in `(-∞, -1)`, with multiplicity. -/
theorem sign_det_one_sub_pow_succ (f : Module.End ℝ V) (k : ℕ) (h : (1 - f ^ (k + 1)).det ≠ 0) :
    SignType.sign (1 - f ^ (k + 1)).det =
      SignType.sign (1 - f).det * ((-1) ^ (f.charpoly.roots.filter (· < -1)).card) ^ k := by
  have h₁ : (1 - f).det ≠ 0 :=
    left_ne_zero_of_mul (by rwa [← map_mul, mul_neg_geom_sum])
  rw [f.sign_det_one_sub_pow _ h, f.sign_det_one_sub h₁, ← pow_mul,
    ← TauCeti.neg_one_pow_add_two_mul (_ * k) (f.charpoly.roots.filter (· < -1)).card]
  ring_nf

/-- If `1 - f ^ 2` is invertible for an endomorphism `f` of a finite-dimensional real vector space
`V`, so that no eigenvalue is `± 1`, then `(-1) ^ (i₊ + i₋) = (-1) ^ (dim V + i₀)`, where `i₊`,
`i₋` and `i₀` count the real roots of the characteristic polynomial of `f` in `(1, ∞)`, in
`(-∞, -1)` and in `(-1, 1)`, with multiplicity. -/
theorem neg_one_pow_card_filter_one_lt_add_card_filter_lt_neg_one (f : Module.End ℝ V)
    (h : (1 - f ^ 2).det ≠ 0) :
    (-1 : SignType) ^ ((f.charpoly.roots.filter (1 < ·)).card +
        (f.charpoly.roots.filter (· < -1)).card) =
      (-1) ^ (Module.finrank ℝ V + (f.charpoly.roots.filter (|·| < 1)).card) := by
  let b := Module.finBasis ℝ V
  have hmat : toMatrix b b (1 - f ^ 2) = 1 - toMatrix b b f ^ 2 := by
    rw [map_sub, toMatrix_one, toMatrix_pow]
  rw [← det_toMatrix b, hmat] at h
  have := (toMatrix b b f).neg_one_pow_card_filter_one_lt_add_card_filter_lt_neg_one h
  rwa [charpoly_toMatrix f b, Fintype.card_fin] at this

/-- If `0 < det f` for an endomorphism `f` of a finite-dimensional real vector space and `1 + f`
is invertible, the numbers of real roots of the characteristic polynomial of `f` in `(-∞, -1)`
and in `(-1, 0)`, counted with multiplicity, have the same parity. -/
theorem neg_one_pow_card_filter_lt_neg_one_of_det_pos (f : Module.End ℝ V) (hf : 0 < f.det)
    (h : (1 + f).det ≠ 0) :
    (-1 : SignType) ^ (f.charpoly.roots.filter (· < -1)).card =
      (-1) ^ (f.charpoly.roots.filter (· ∈ Set.Ioo (-1) 0)).card := by
  let b := Module.finBasis ℝ V
  rw [← det_toMatrix b] at hf h
  rw [map_add, toMatrix_one] at h
  rw [← charpoly_toMatrix f b]
  exact (toMatrix b b f).neg_one_pow_card_filter_lt_neg_one_of_det_pos hf h

section EigenvalueLocation

open Set

variable {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

/-- If `f` has no real eigenvalue `μ ≥ 1`, then `det (1 - f) > 0`: the characteristic polynomial
`det (t - f)` is monic and has no root `t ≥ 1`. -/
theorem det_one_sub_pos_of_not_hasEigenvalue {f : Module.End ℝ V}
    (hf : ∀ μ : ℝ, 1 ≤ μ → ¬ f.HasEigenvalue μ) : 0 < (1 - f).det := by
  have h := zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg (P := f.charpoly) (x := 1)
    (fun y hy ↦ lt_of_not_ge fun h1 ↦
      hf y h1 ((Module.End.hasEigenvalue_iff_isRoot_charpoly f y).mpr hy))
    (f.charpoly_monic.leadingCoeff ▸ zero_le_one)
  rwa [eval_charpoly, map_one] at h

/-- If `f` has no real eigenvalue in `[0, 1]`, then `sign det (1 - f) = (-1)ⁿ sign det f`, where
`n = dim V`: `f` is invertible, `1 - f = (-f) (1 - f⁻¹)`, and `det (1 - f⁻¹) > 0` because `f⁻¹`
has no real eigenvalue `μ ≥ 1`. -/
theorem sign_det_one_sub_of_not_hasEigenvalue {f : Module.End ℝ V}
    (hf : ∀ μ ∈ Icc (0 : ℝ) 1, ¬ f.HasEigenvalue μ) :
    SignType.sign (1 - f).det = (-1) ^ Module.finrank ℝ V * SignType.sign f.det := by
  have hinj : Function.Injective f := by
    rw [← ker_eq_bot]
    exact ((not_hasEigenvalue_zero_tfae f).out 1 5).mp (hf 0 ⟨le_rfl, zero_le_one⟩)
  set g : Module.End ℝ V := ((LinearEquiv.ofInjectiveEndo f hinj).symm : V →ₗ[ℝ] V)
  have hfg : f * g = 1 := LinearEquiv.ofInjectiveEndo_right_inv f hinj
  -- An eigenvector of `g` for `μ ≥ 1` is an eigenvector of `f` for `μ⁻¹ ∈ (0, 1]`.
  have hg : ∀ μ : ℝ, 1 ≤ μ → ¬ g.HasEigenvalue μ := fun μ hμ h ↦ by
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    have hgv : g v = μ • v := Module.End.mem_eigenspace_iff.mp hv.1
    have h : μ • f v = v := by
      simpa [hgv] using congr($hfg v)
    have hfv : f v = μ⁻¹ • v := by
      conv_rhs => rw [← h, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
    exact hf μ⁻¹ ⟨by positivity, inv_le_one_of_one_le₀ hμ⟩
      (Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.mpr hfv, hv.2⟩)
  have hsplit : 1 - f = -f * (1 - g) := by
    rw [neg_mul, mul_sub, mul_one, hfg]
    abel
  rw [hsplit, ← neg_one_smul ℝ f, smul_mul_assoc, det_smul]
  simp [sign_mul, sign_pow, sign_pos (det_one_sub_pos_of_not_hasEigenvalue hg)]

/-- **The sign of `det (1 - A)` at an expanding-contracting splitting.** If `f` has no real
eigenvalue in `[0, 1]` and `g` has no real eigenvalue `μ ≥ 1`, then
`sign det (1 - f × g) = (-1)^(dim V) sign det f`. -/
theorem sign_det_one_sub_prodMap_of_not_hasEigenvalue {f : Module.End ℝ V} {g : Module.End ℝ W}
    (hf : ∀ μ ∈ Icc (0 : ℝ) 1, ¬ f.HasEigenvalue μ) (hg : ∀ μ : ℝ, 1 ≤ μ → ¬ g.HasEigenvalue μ) :
    SignType.sign (1 - f.prodMap g).det = (-1) ^ Module.finrank ℝ V * SignType.sign f.det := by
  have h : (1 : Module.End ℝ (V × W)) - f.prodMap g = (1 - f).prodMap (1 - g) := by
    ext <;> simp
  rw [h, det_prodMap, sign_mul, sign_det_one_sub_of_not_hasEigenvalue hf,
    sign_pos (det_one_sub_pos_of_not_hasEigenvalue hg), mul_one]

/-- Under the hypotheses of `LinearMap.sign_det_one_sub_prodMap_of_not_hasEigenvalue`,
`1 - f × g` is invertible: `f` has no eigenvalue `0`, so `det f ≠ 0`. -/
theorem det_one_sub_prodMap_ne_zero_of_not_hasEigenvalue {f : Module.End ℝ V}
    {g : Module.End ℝ W} (hf : ∀ μ ∈ Icc (0 : ℝ) 1, ¬ f.HasEigenvalue μ)
    (hg : ∀ μ : ℝ, 1 ≤ μ → ¬ g.HasEigenvalue μ) : (1 - f.prodMap g).det ≠ 0 := by
  have hdet : f.det ≠ 0 :=
    ((not_hasEigenvalue_zero_tfae f).out 1 4).mp (hf 0 ⟨le_rfl, zero_le_one⟩)
  rw [← sign_ne_zero, sign_det_one_sub_prodMap_of_not_hasEigenvalue hf hg]
  simp [hdet]

end EigenvalueLocation

end LinearMap
