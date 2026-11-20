/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.Derivation.DifferentialRing
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Jacobson.Ideal
import TauCeti.RingTheory.Derivation.Basic
import TauCeti.LinearAlgebra.Matrix.Polynomial
import TauCeti.LinearAlgebra.PolynomialFamily
import TauCeti.RingTheory.Jacobson.Polynomial

/-!
# Katz's explicit cyclic vectors

Let `R` be a commutative ring with a derivation `r ↦ r′` and let `M` be a free `R`-module of rank
`n` with an additive map `D : M → M` satisfying the Leibniz rule `D (r • m) = r′ • m + r • D m`,
a differential module over `R`. A *cyclic vector* is a vector `v` such that
`v, D v, …, D^(n-1) v` form a basis of `M` (`TauCeti.IsCyclicVector`).

For a basis `e₀, …, eₙ₋₁` and an element `x : R`, Katz's candidate is

`c(e, x) = ∑_{j < n} (x ^ j / j!) ∑_{k ≤ j} (-1) ^ k (j choose k) D^k (e_{j-k})`

(`TauCeti.katzCandidate`). Katz proved that when `(n - 1)!` is invertible and `x′ = 1` (for
instance `x = t - a` with `t′ = 1` and `a′ = 0`), this candidate is cyclic as soon as `x` is small,
and that finitely many translates of it are cyclic locally everywhere.

The proof writes the iterates of the candidate as `D^i c(e, x) = ∑_{j < n} (x ^ j / j!) c(i, j)`
for vectors `c(i, j)` defined by `c(i + 1, j) = D c(i, j) + c(i, j + 1)`
(`TauCeti.katzJetCoeff`, `TauCeti.pow_apply_katzCandidate`). For `i + j < n` the vectors `c(i, j)`
are given by the same alternating binomial sums, shifted by `i`
(`TauCeti.katzJetCoeff_eq_sum`), so `c(i, 0) = eᵢ`. Hence the determinant of the iterates in
the basis `e` is `P(x)` for a polynomial `P` (`TauCeti.katzPolynomial`) with `P(0) = 1` and degree
at most `n (n - 1)`, which depends only on `D` and `e`.

## Main definitions

* `TauCeti.IsCyclicVector R D n v`: the vectors `v, D v, …, D^(n-1) v` form a basis.
* `TauCeti.katzJetCoeff D e i j`: the vectors `c(i, j)`.
* `TauCeti.katzCandidate D e x`: Katz's candidate `c(e, x)`.
* `TauCeti.katzPolynomial D b`: the polynomial `P` whose value at `x` is the determinant of the
  iterates of `c(b, x)` in the basis `b`.

## Main results

* `TauCeti.eval_katzPolynomial_eq_det`: for every `x`, `P(x)` is the determinant of the vectors
  `∑_{j < n} (x ^ j / j!) c(i, j)` in the basis `b`.
* `TauCeti.eval_katzPolynomial`: `P(x) = det (D^i c(b, x))_{i < n}` when `D` satisfies the
  Leibniz rule, `(n - 1)!` is a unit and `x′ = 1`.
* `TauCeti.coeff_katzPolynomial_zero`, `TauCeti.natDegree_katzPolynomial_le`: `P(0) = 1` and
  `deg P ≤ n (n - 1)`.
* `TauCeti.isCyclicVector_katzCandidate_iff`: `c(b, x)` is cyclic if and only if `P(x)` is a unit.
* `TauCeti.isCyclicVector_katzCandidate_of_mem_jacobson`: if `x` lies in the Jacobson radical,
  for instance in the maximal ideal of a local ring
  (`TauCeti.isCyclicVector_katzCandidate_of_mem_maximalIdeal`), then `c(b, x)` is cyclic.
* `TauCeti.span_eval_katzPolynomial_eq_top`: for `N > n (n - 1)` elements `xᵢ` whose pairwise
  differences are units, the values `P(xᵢ)` generate the unit ideal.
* `TauCeti.span_det_pow_apply_katzCandidate_eq_top`: if moreover `D` satisfies the Leibniz rule,
  `(n - 1)!` is a unit and `xᵢ′ = 1`, the determinants of the iterates of the candidates
  `c(b, xᵢ)` generate the unit ideal, so the loci where these candidates are cyclic cover
  `Spec R`.

## References

* N. M. Katz, *A simple algorithm for cyclic vectors*, Amer. J. Math. 109 (1987), 65–70,
  Theorems 1 and 2 and their proofs.
-/

public noncomputable section

open Finset Module Polynomial
open scoped Differential Nat Ring

namespace TauCeti

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-! ## Cyclic vectors -/

section IsCyclicVector

variable {D : AddMonoid.End M} {n : ℕ} {v : M}

variable (R) in
/-- A *cyclic vector* of rank `n` for an additive endomorphism `D` of an `R`-module `M`: a vector
`v` such that `v, D v, …, D^(n-1) v` form a basis of `M`. -/
def IsCyclicVector (D : AddMonoid.End M) (n : ℕ) (v : M) : Prop :=
  LinearIndependent R (fun i : Fin n ↦ (D ^ (i : ℕ)) v) ∧
    Submodule.span R (Set.range fun i : Fin n ↦ (D ^ (i : ℕ)) v) = ⊤

/-- Unfolds `IsCyclicVector`: the first `n` iterates are linearly independent and span `M`. -/
theorem isCyclicVector_iff : IsCyclicVector R D n v ↔
    LinearIndependent R (fun i : Fin n ↦ (D ^ (i : ℕ)) v) ∧
      Submodule.span R (Set.range fun i : Fin n ↦ (D ^ (i : ℕ)) v) = ⊤ :=
  Iff.rfl

/-- A vector whose first `n` iterates form a basis is cyclic of rank `n`. -/
theorem IsCyclicVector.of_basis (b : Basis (Fin n) R M) (hb : ∀ i, b i = (D ^ (i : ℕ)) v) :
    IsCyclicVector R D n v := by
  have : ⇑b = fun i : Fin n ↦ (D ^ (i : ℕ)) v := funext hb
  exact ⟨this ▸ b.linearIndependent, this ▸ b.span_eq⟩

/-- A vector is cyclic of rank `n` if and only if the determinant of its first `n` iterates in a
basis indexed by `Fin n` is a unit. -/
theorem isCyclicVector_iff_isUnit_det (b : Basis (Fin n) R M) :
    IsCyclicVector R D n v ↔ IsUnit (b.det fun i ↦ (D ^ (i : ℕ)) v) :=
  b.is_basis_iff_det

/-- The basis `v, D v, …, D^(n-1) v` given by a cyclic vector `v`. -/
def IsCyclicVector.basis (h : IsCyclicVector R D n v) : Basis (Fin n) R M :=
  Basis.mk h.1 h.2.ge

@[simp]
theorem IsCyclicVector.coe_basis (h : IsCyclicVector R D n v) :
    ⇑h.basis = fun i : Fin n ↦ (D ^ (i : ℕ)) v :=
  Basis.coe_mk _ _

end IsCyclicVector

/-! ## Katz's candidate -/

section Katz

variable (D : AddMonoid.End M) {n : ℕ} (e : Fin n → M)

/-- The vectors `c(i, j)` of Katz's construction, for a family `e₀, …, eₙ₋₁`: for `j < n`,
`c(0, j) = ∑_{k ≤ j} (-1) ^ k (j choose k) D^k (e_{j-k})`, while `c(0, j) = 0` for `j ≥ n`, and
`c(i + 1, j) = D c(i, j) + c(i, j + 1)`. If `D` satisfies the Leibniz rule, `(n - 1)!` is a unit
and `x′ = 1`, the `i`-th iterate of Katz's candidate is `∑_{j < n} (x ^ j / j!) c(i, j)`
(`TauCeti.pow_apply_katzCandidate`). -/
def katzJetCoeff : ℕ → ℕ → M
  | 0, j =>
    if j < n then
      ∑ k ∈ range (j + 1), j.choose k • (-1 : ℤ) ^ k • (D ^ k) (Function.extend Fin.val e 0 (j - k))
    else 0
  | i + 1, j => D (katzJetCoeff i j) + katzJetCoeff i (j + 1)

theorem katzJetCoeff_zero (j : ℕ) :
    katzJetCoeff D e 0 j = if j < n then
      ∑ k ∈ range (j + 1), j.choose k • (-1 : ℤ) ^ k • (D ^ k) (Function.extend Fin.val e 0 (j - k))
    else 0 := by
  rw [katzJetCoeff]

theorem katzJetCoeff_succ (i j : ℕ) :
    katzJetCoeff D e (i + 1) j = D (katzJetCoeff D e i j) + katzJetCoeff D e i (j + 1) := by
  rw [katzJetCoeff]

/-- The vectors `c(i, j)` vanish for `j ≥ n`. -/
theorem katzJetCoeff_eq_zero_of_le {j : ℕ} (hj : n ≤ j) (i : ℕ) : katzJetCoeff D e i j = 0 := by
  induction i generalizing j with
  | zero => simp [katzJetCoeff_zero, hj.not_gt]
  | succ i ih => rw [katzJetCoeff_succ, ih hj, ih (hj.trans j.le_succ), map_zero, add_zero]

/-- Pascal's rule for the alternating binomial sums `∑_{k ≤ j} (-1) ^ k (j choose k) D^k (h_{j-k})`
of a sequence `h`: the sum for `j + 1` is the sum for the shifted sequence minus `D` of the sum
for `j`. -/
private theorem sum_choose_succ (h : ℕ → M) (i j : ℕ) :
    ∑ k ∈ range (j + 1 + 1), (j + 1).choose k • (-1 : ℤ) ^ k • (D ^ k) (h (i + (j + 1 - k))) =
      ∑ k ∈ range (j + 1), j.choose k • (-1 : ℤ) ^ k • (D ^ k) (h (i + 1 + (j - k))) -
        D (∑ k ∈ range (j + 1), j.choose k • (-1 : ℤ) ^ k • (D ^ k) (h (i + (j - k)))) := by
  rw [show j + 1 + 1 = j + 2 by omega,
    sum_choose_succ_nsmul (fun k l ↦ (-1 : ℤ) ^ k • (D ^ k) (h (i + l))) j, sub_eq_add_neg,
    map_sum, ← sum_neg_distrib]
  congr 1
  · refine sum_congr rfl fun k hk ↦ ?_
    have := mem_range.mp hk
    rw [show i + (j + 1 - k) = i + 1 + (j - k) by omega]
  · refine sum_congr rfl fun k _ ↦ ?_
    simp [pow_succ, pow_succ' D, smul_neg]

/-- For `i + j < n`, the vector `c(i, j)` is the alternating binomial sum
`∑_{k ≤ j} (-1) ^ k (j choose k) D^k (e_{i+j-k})`. -/
theorem katzJetCoeff_eq_sum {i j : ℕ} (hij : i + j < n) :
    katzJetCoeff D e i j = ∑ k ∈ range (j + 1),
      j.choose k • (-1 : ℤ) ^ k • (D ^ k) (Function.extend Fin.val e 0 (i + (j - k))) := by
  induction i generalizing j with
  | zero => simp [katzJetCoeff_zero, show j < n by omega]
  | succ i ih =>
    rw [katzJetCoeff_succ, ih (by omega), ih (by omega), sum_choose_succ, add_sub_cancel]

/-- The vector `c(i, 0)` is `eᵢ`. -/
@[simp]
theorem katzJetCoeff_zero_right (i : Fin n) : katzJetCoeff D e i 0 = e i := by
  rw [katzJetCoeff_eq_sum D e (by simp)]
  simp [Fin.val_injective.extend_apply]

/-- Katz's candidate
`c(e, x) = ∑_{j < n} (x ^ j / j!) ∑_{k ≤ j} (-1) ^ k (j choose k) D^k (e_{j-k})`
for a family `e₀, …, eₙ₋₁` and `x : R`, where `1 / j!` is read as `Ring.inverse j!`. -/
def katzCandidate (x : R) : M :=
  ∑ j ∈ range n, ((j ! : R)⁻¹ʳ * x ^ j) • katzJetCoeff D e 0 j

theorem katzCandidate_def (x : R) :
    katzCandidate D e x = ∑ j ∈ range n, ((j ! : R)⁻¹ʳ * x ^ j) • katzJetCoeff D e 0 j :=
  (rfl)

/-- In rank zero the candidate is zero. -/
@[simp]
theorem katzCandidate_fin_zero (e : Fin 0 → M) (x : R) : katzCandidate D e x = 0 := by
  simp [katzCandidate]

/-- In rank one the candidate is `e₀`. -/
@[simp]
theorem katzCandidate_fin_one (e : Fin 1 → M) (x : R) : katzCandidate D e x = e 0 := by
  simpa [katzCandidate] using katzJetCoeff_zero_right D e 0

/-- An additive map intertwining two additive endomorphisms carries the vectors `c(i, j)` of a
family to those of its image. -/
theorem map_katzJetCoeff {N F : Type*} [AddCommGroup N] [FunLike F M N] [AddMonoidHomClass F M N]
    (D' : AddMonoid.End N) (f : F) (hf : ∀ m, f (D m) = D' (f m)) (i j : ℕ) :
    f (katzJetCoeff D e i j) = katzJetCoeff D' (f ∘ e) i j := by
  have hpow (k : ℕ) (m : M) : f ((D ^ k) m) = (D' ^ k) (f m) := by
    rw [AddMonoid.End.coe_pow, AddMonoid.End.coe_pow]
    exact Function.Semiconj.iterate_right hf k m
  have hext (l : ℕ) : f (Function.extend Fin.val e 0 l) = Function.extend Fin.val (f ∘ e) 0 l := by
    rw [Function.apply_extend f]
    congr
    exact funext fun _ ↦ map_zero f
  induction i generalizing j with
  | zero =>
    rw [katzJetCoeff_zero, katzJetCoeff_zero]
    split_ifs
    · simp only [map_sum, map_nsmul, map_zsmul, hpow, hext]
    · exact map_zero f
  | succ i ih => rw [katzJetCoeff_succ, katzJetCoeff_succ, map_add, hf, ih, ih]

/-- A linear map intertwining two additive endomorphisms, for instance an isomorphism of
differential modules, carries Katz's candidate of a family to that of its image. -/
theorem map_katzCandidate {N : Type*} [AddCommGroup N] [Module R N] (D' : AddMonoid.End N)
    (f : M →ₗ[R] N) (hf : ∀ m, f (D m) = D' (f m)) (x : R) :
    f (katzCandidate D e x) = katzCandidate D' (f ∘ e) x := by
  simp only [katzCandidate, map_sum, map_smul]
  exact sum_congr rfl fun j _ ↦ by rw [map_katzJetCoeff D e D' f hf]

/-- The coordinates of Katz's candidate in a basis `b` are the sums
`∑_{j < n} (x ^ j / j!) b.repr (c(0, j)) k`. -/
theorem repr_katzCandidate {ι : Type*} (b : Basis ι R M) (x : R) (k : ι) :
    b.repr (katzCandidate D e x) k =
      ∑ j ∈ range n, (j ! : R)⁻¹ʳ * x ^ j * b.repr (katzJetCoeff D e 0 j) k := by
  simp [katzCandidate_def, mul_assoc]

/-! ### Iterates of the candidate -/

section Iterates

variable [Differential R] {x : R}

variable {D}

/-- Applying `D` to `∑_{j < n} (x ^ j / j!) c(i, j)` gives
`∑_{j < n} (x ^ j / j!) c(i + 1, j)`. -/
private theorem apply_sum_katzJetCoeff (hD : ∀ (r : R) (m : M), D (r • m) = r′ • m + r • D m)
    (hn : IsUnit ((n - 1)! : R)) (hx : x′ = 1) (i : ℕ) :
    D (∑ j ∈ range n, ((j ! : R)⁻¹ʳ * x ^ j) • katzJetCoeff D e i j) =
      ∑ j ∈ range n, ((j ! : R)⁻¹ʳ * x ^ j) • katzJetCoeff D e (i + 1) j := by
  simp only [map_sum, hD, sum_add_distrib, katzJetCoeff_succ, smul_add]
  rw [add_comm]
  congr 1
  -- The derivatives of the coefficients shift the index `j` down by one.
  obtain _ | m := n
  · simp
  rw [sum_range_succ', sum_range_succ, katzJetCoeff_eq_zero_of_le D e le_rfl]
  simp only [Nat.factorial_zero, Nat.cast_one, Ring.inverse_one, pow_zero, mul_one,
    Derivation.map_one_eq_zero, zero_smul, smul_zero, add_zero]
  refine sum_congr rfl fun j hj ↦ ?_
  rw [Differential.deriv.leibniz_ringInverse_factorial_mul_pow_succ hx (isUnit_of_dvd_unit
    (Nat.cast_dvd_cast (Nat.factorial_dvd_factorial (by simp at hj ⊢; omega))) hn)]

/-- **The iterates of Katz's candidate.** If `D` satisfies the Leibniz rule, `(n - 1)!` is a unit
and `x′ = 1`, then `D^i c(e, x) = ∑_{j < n} (x ^ j / j!) c(i, j)`. -/
theorem pow_apply_katzCandidate (hD : ∀ (r : R) (m : M), D (r • m) = r′ • m + r • D m)
    (hn : IsUnit ((n - 1)! : R)) (hx : x′ = 1) (i : ℕ) :
    (D ^ i) (katzCandidate D e x) =
      ∑ j ∈ range n, ((j ! : R)⁻¹ʳ * x ^ j) • katzJetCoeff D e i j := by
  induction i with
  | zero => rw [pow_zero, AddMonoid.End.coe_one, id, katzCandidate_def]
  | succ i ih =>
    rw [pow_succ', AddMonoid.End.coe_mul, Function.comp_apply, ih,
      apply_sum_katzJetCoeff e hD hn hx]

end Iterates

/-! ### The determinant polynomial -/

section Polynomial

variable (b : Basis (Fin n) R M)

/-- The polynomial `P` of Katz's construction for a basis `b`: the determinant of the matrix
whose `(k, i)` entry is `∑_{j < n} (X ^ j / j!) bₖ*(c(i, j))`, with `bₖ*` the `k`-th coordinate.
If `D` satisfies the Leibniz rule, `(n - 1)!` is a unit and `x′ = 1`, its value at `x` is the
determinant of the iterates of `c(b, x)` in the basis `b` (`TauCeti.eval_katzPolynomial`). -/
def katzPolynomial : R[X] :=
  (Matrix.of fun k i : Fin n ↦
    ∑ j ∈ range n, C ((j ! : R)⁻¹ʳ * b.repr (katzJetCoeff D b i j) k) * X ^ j).det

theorem katzPolynomial_def : katzPolynomial D b = (Matrix.of fun k i : Fin n ↦
    ∑ j ∈ range n, C ((j ! : R)⁻¹ʳ * b.repr (katzJetCoeff D b i j) k) * X ^ j).det :=
  (rfl)

/-- The value at `x` of `katzPolynomial D b`, for any `x`, is the determinant of the vectors
`∑_{j < n} (x ^ j / j!) c(i, j)` in the basis `b`. -/
theorem eval_katzPolynomial_eq_det (x : R) : (katzPolynomial D b).eval x =
    b.det fun i : Fin n ↦ ∑ j ∈ range n, ((j ! : R)⁻¹ʳ * x ^ j) • katzJetCoeff D b i j := by
  rw [katzPolynomial, ← coe_evalRingHom, RingHom.map_det, Basis.det_apply]
  congr 1
  ext k i
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Basis.toMatrix_apply,
    map_sum, coe_evalRingHom, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, map_smul,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact sum_congr rfl fun j _ ↦ by ring

/-- **Katz's determinant.** If `D` satisfies the Leibniz rule, `(n - 1)!` is a unit and `x′ = 1`,
then the value of `katzPolynomial D b` at `x` is the determinant in the basis `b` of the iterates
`c(b, x), D c(b, x), …, D^(n-1) c(b, x)` of Katz's candidate. -/
theorem eval_katzPolynomial [Differential R] {x : R}
    (hD : ∀ (r : R) (m : M), D (r • m) = r′ • m + r • D m) (hn : IsUnit ((n - 1)! : R))
    (hx : x′ = 1) :
    (katzPolynomial D b).eval x = b.det fun i : Fin n ↦ (D ^ (i : ℕ)) (katzCandidate D b x) := by
  simp only [pow_apply_katzCandidate _ hD hn hx, eval_katzPolynomial_eq_det]

/-- The polynomial `katzPolynomial D b` has constant term `1`: at `x = 0` the vectors
`∑_{j < n} (x ^ j / j!) c(i, j)` are `c(i, 0) = bᵢ`. -/
@[simp]
theorem coeff_katzPolynomial_zero : (katzPolynomial D b).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero, eval_katzPolynomial_eq_det, ← b.det_self]
  congr 1
  ext i
  rw [sum_eq_single_of_mem 0 (mem_range.mpr (i.pos))]
  · simp
  · intro j _ hj
    rw [zero_pow hj, mul_zero, zero_smul]

/-- The polynomial `katzPolynomial D b` has degree at most `n (n - 1)`. -/
theorem natDegree_katzPolynomial_le : (katzPolynomial D b).natDegree ≤ n * (n - 1) := by
  rw [katzPolynomial]
  refine (Matrix.natDegree_det_le_of_natDegree_le _ (fun _ ↦ n - 1) fun k i ↦ ?_).trans_eq
    (by simp)
  rw [Matrix.of_apply]
  refine natDegree_sum_le_of_forall_le _ _ fun j hj ↦
    (natDegree_C_mul_X_pow_le (R := R) _ _).trans ?_
  have := mem_range.mp hj
  omega

end Polynomial

/-! ### Katz's cyclic-vector theorems -/

section Cyclic

variable [Differential R] {D} (b : Basis (Fin n) R M) {x : R}

/-- **Katz's criterion.** If `D` satisfies the Leibniz rule, `(n - 1)!` is a unit and `x′ = 1`,
then Katz's candidate `c(b, x)` is a cyclic vector if and only if `P(x)` is a unit, for the
polynomial `P = katzPolynomial D b` with `P(0) = 1` and degree at most `n (n - 1)`. -/
theorem isCyclicVector_katzCandidate_iff (hD : ∀ (r : R) (m : M), D (r • m) = r′ • m + r • D m)
    (hn : IsUnit ((n - 1)! : R)) (hx : x′ = 1) :
    IsCyclicVector R D n (katzCandidate D b x) ↔ IsUnit ((katzPolynomial D b).eval x) := by
  rw [isCyclicVector_iff_isUnit_det b, eval_katzPolynomial D b hD hn hx]

omit [Differential R] in
/-- The value at `x` of `katzPolynomial D b` is a unit when `x` lies in the Jacobson radical. -/
theorem isUnit_eval_katzPolynomial_of_mem_jacobson (hx : x ∈ Ring.jacobson R) :
    IsUnit ((katzPolynomial D b).eval x) :=
  isUnit_eval_of_isUnit_coeff_zero_of_mem_jacobson (by simp) hx

/-- **Katz's cyclic-vector theorem, local form.** If `D` satisfies the Leibniz rule, `(n - 1)!` is
a unit, `x′ = 1` and `x` lies in the Jacobson radical of `R`, then Katz's candidate `c(b, x)` is a
cyclic vector. -/
theorem isCyclicVector_katzCandidate_of_mem_jacobson
    (hD : ∀ (r : R) (m : M), D (r • m) = r′ • m + r • D m) (hn : IsUnit ((n - 1)! : R))
    (hx : x′ = 1) (hxJ : x ∈ Ring.jacobson R) :
    IsCyclicVector R D n (katzCandidate D b x) :=
  (isCyclicVector_katzCandidate_iff b hD hn hx).mpr
    (isUnit_eval_katzPolynomial_of_mem_jacobson b hxJ)

/-- **Katz's cyclic-vector theorem over a local ring.** If `R` is local, `D` satisfies the Leibniz
rule, `(n - 1)!` is a unit, `x′ = 1` and `x` lies in the maximal ideal (for instance `x = t - a`
with `t′ = 1`, `a′ = 0` and `t - a` in the maximal ideal), then Katz's candidate `c(b, x)` is a
cyclic vector. -/
theorem isCyclicVector_katzCandidate_of_mem_maximalIdeal [IsLocalRing R]
    (hD : ∀ (r : R) (m : M), D (r • m) = r′ • m + r • D m) (hn : IsUnit ((n - 1)! : R))
    (hx : x′ = 1) (hxm : x ∈ IsLocalRing.maximalIdeal R) :
    IsCyclicVector R D n (katzCandidate D b x) :=
  isCyclicVector_katzCandidate_of_mem_jacobson b hD hn hx
    (IsLocalRing.ringJacobson_eq_maximalIdeal R ▸ hxm)

omit [Differential R] in
/-- If `N > n (n - 1)` elements `xᵢ` have pairwise differences that are units, the values of
`katzPolynomial D b` at them generate the unit ideal. -/
theorem span_eval_katzPolynomial_eq_top {N : ℕ} (hN : n * (n - 1) < N) {x : Fin N → R}
    (hx : Pairwise fun i j ↦ IsUnit (x i - x j)) :
    Ideal.span (Set.range fun i ↦ (katzPolynomial D b).eval (x i)) = ⊤ := by
  rw [span_eval_eq_contentIdeal_of_natDegree_lt _ ((natDegree_katzPolynomial_le D b).trans_lt hN)
    hx, Ideal.eq_top_iff_one, ← coeff_katzPolynomial_zero D b]
  exact coeff_mem_contentIdeal _ 0

/-- **Katz's cyclic-vector theorem, global form.** Suppose `D` satisfies the Leibniz rule,
`(n - 1)!` is a unit, and `x₀, …, x_{N-1}` are `N > n (n - 1)` elements with `xᵢ′ = 1` whose
pairwise differences are units (for instance `xᵢ = t - aᵢ` with `t′ = 1` and distinct constants
`aᵢ` in a subfield of the constants). Then the determinants of the iterates of the candidates
`c(b, xᵢ)` generate the unit ideal: every prime ideal of `R` avoids one of them, so the loci where
the candidates are cyclic cover `Spec R`. -/
theorem span_det_pow_apply_katzCandidate_eq_top
    (hD : ∀ (r : R) (m : M), D (r • m) = r′ • m + r • D m) (hn : IsUnit ((n - 1)! : R))
    {N : ℕ} (hN : n * (n - 1) < N) {x : Fin N → R} (hx : ∀ i, (x i)′ = 1)
    (hxx : Pairwise fun i j ↦ IsUnit (x i - x j)) :
    Ideal.span (Set.range fun i ↦ b.det fun k : Fin n ↦ (D ^ (k : ℕ)) (katzCandidate D b (x i))) =
      ⊤ := by
  simp only [← eval_katzPolynomial D b hD hn (hx _)]
  exact span_eval_katzPolynomial_eq_top b hN hxx

end Cyclic

end Katz

end TauCeti
