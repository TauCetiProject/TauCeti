/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Charpoly.Reverse
public import Mathlib.LinearAlgebra.Trace
public import TauCeti.RingTheory.MvPolynomial.Symmetric.PowerSum.NewtonPolynomial
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import TauCeti.LinearAlgebra.Charpoly.Nilpotent
import TauCeti.LinearAlgebra.Matrix.Charpoly.Roots
import TauCeti.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

/-!
# Newton's identities for the traces of the powers of a matrix

For a square matrix `A` over a commutative ring, write `c_r` for the coefficients of
`det (1 - X A) = Matrix.charpolyRev A` and `p_j = tr (A ^ j)` for the traces of its powers.
Newton's identities specialise to the integral recurrence

`r c_r = -(c_(r-1) p_1 + c_(r-2) p_2 + ⋯ + c_0 p_r)`

in every degree `r`, over every commutative ring and in every characteristic. Over a domain in
which the characteristic polynomial splits, `c_r = (-1) ^ r e_r` and `p_j = ∑ λ ^ j`, where `e_r`
is the `r`-th elementary symmetric function of the characteristic roots `λ`, and the recurrence is
Newton's identity for that multiset (`Multiset.mul_esymm_eq_sum`). The general case follows from the
universal matrix `Matrix.mvPolynomialX` over `ℤ`, whose coefficient ring embeds into an
algebraically closed field.

The same reduction expresses the traces through the coefficients: `p_k` is the Newton polynomial
`TauCeti.newtonMvPolynomial`, the universal integer polynomial giving the power sum `p_k` in terms
of the elementary symmetric functions, evaluated at `e_j = (-1) ^ j c_j`.

When division by the integers `1, …, r` is unique, the recurrence determines `c_r` from the traces
`p_1, …, p_r`. So over a ring without additive torsion, such as a field of characteristic zero,
the traces of the first `d` powers of a `d × d` matrix determine its characteristic polynomial.

## Main results

* `Matrix.mul_coeff_charpolyRev_eq_neg_sum`: **Newton's identities** for the traces of the powers
  of a matrix over any commutative ring; `LinearMap.mul_coeff_reverse_charpoly_eq_neg_sum` is the
  same statement for an endomorphism of a finite free module.
* `Matrix.trace_pow_eq_aeval_newtonMvPolynomial`: over any commutative ring, `tr (A ^ k)` is the
  integer Newton polynomial `TauCeti.newtonMvPolynomial ℤ d k` evaluated at the signed
  coefficients `(-1) ^ j c_j` of `det (1 - X A)`, for `j = 1, …, d`.
* `Matrix.trace_pow_eq_of_charpolyRev_eq`: over any commutative ring, `det (1 - X A)` determines
  the traces of all positive powers of `A`.
* `Matrix.trace_pow_eq_of_charpoly_eq`: over any commutative ring, the characteristic polynomial
  determines the traces of all powers of `A`.
* `Matrix.coeff_charpolyRev_eq_of_trace_pow_eq`, `Matrix.charpolyRev_eq_iff_trace_pow_eq`,
  `Matrix.charpoly_eq_iff_trace_pow_eq`: conversely, without additive torsion, the traces of the
  positive powers determine `det (1 - X A)` and the characteristic polynomial.
* `Matrix.charpoly_eq_of_trace_pow_eq`, `LinearMap.charpoly_eq_of_trace_pow_eq`: without additive
  torsion, the traces of `A ^ j` for `0 < j ≤ d` already determine the characteristic polynomial
  of a `d × d` matrix, or of an endomorphism of a free module of rank `d`.
* `LinearMap.trace_pow_eq_of_charpoly_eq`, `LinearMap.charpoly_eq_iff_trace_pow_eq`: the same
  comparisons for endomorphisms of finite free modules.
* `Matrix.charpoly_eq_of_sq_eq_one`, `LinearMap.charpoly_eq_of_sq_eq_one`: without additive
  torsion, an involution has characteristic polynomial `(X - 1) ^ a * (X + 1) ^ b` whenever
  `a + b = d` and `a - b` is its trace.
* `Matrix.pow_card_eq_zero_of_trace_pow_eq_zero` and
  `LinearMap.pow_finrank_eq_zero_of_trace_pow_eq_zero`: without additive torsion, if these traces
  all vanish then `A ^ d = 0`, by `Matrix.pow_eq_zero_of_charpoly_eq_X_pow`.

## References

* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, 2nd ed., Oxford (1995), Ch. I,
  §2, (2.11′).
-/

public section

open Finset Polynomial

namespace Matrix

section Splits

variable {n K : Type*} [Fintype n] [DecidableEq n] [CommRing K] [IsDomain K] {A : Matrix n n K}

/-- Newton's identities over a domain in which the characteristic polynomial splits; see
`Matrix.mul_coeff_charpolyRev_eq_neg_sum` for the general case. -/
private theorem mul_coeff_charpolyRev_eq_neg_sum_of_splits (hA : A.charpoly.Splits) (r : ℕ) :
    (r : K) * A.charpolyRev.coeff r =
      -∑ j ∈ range r, A.charpolyRev.coeff (r - (j + 1)) * (A ^ (j + 1)).trace := by
  set s := A.charpoly.roots
  have htrace (j : ℕ) : (A ^ j).trace = (s.map (· ^ j)).sum := by
    simpa using trace_aeval_eq_sum_roots_charpoly_of_splits hA (X ^ j)
  simp only [coeff_charpolyRev_eq_esymm_roots_charpoly_of_splits hA, htrace]
  -- Reindex the sum over the antidiagonal in `Multiset.mul_esymm_eq_sum` by `j = r - i - 1`.
  have hsum : ∑ a ∈ antidiagonal r with a.1 < r, (-1) ^ a.1 * s.esymm a.1 * (s.map (· ^ a.2)).sum =
      ∑ j ∈ range r, (-1) ^ (r - (j + 1)) * s.esymm (r - (j + 1)) *
        (s.map (· ^ (j + 1))).sum := by
    rcases r with _ | k
    · simp
    simp_rw [Nat.lt_succ_iff, Nat.antidiagonal_filter_fst_le_of_le k.le_succ, sum_map]
    rw [← Nat.sum_antidiagonal_swap, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp
  have hsign : (-1 : K) ^ r * (-1) ^ (r + 1) = -1 := by
    rw [← pow_add]
    exact Odd.neg_one_pow ⟨r, by ring⟩
  rw [mul_left_comm, s.mul_esymm_eq_sum r, hsum, ← mul_assoc, hsign, neg_one_mul]

/-- The traces of the powers as Newton polynomials in the coefficients, over a domain in which the
characteristic polynomial splits; see `Matrix.trace_pow_eq_aeval_newtonMvPolynomial` for the
general case. Any `ℤ`-algebra structure on `K` is allowed, so that the lemma applies to the
instance found on an algebraic closure. -/
private theorem trace_pow_eq_aeval_newtonMvPolynomial_of_splits [Algebra ℤ K]
    (hA : A.charpoly.Splits) (k : ℕ) :
    (A ^ k).trace = MvPolynomial.aeval
      (fun j : Fin (Fintype.card n) ↦ (-1) ^ (j.val + 1) * A.charpolyRev.coeff (j + 1))
      (TauCeti.newtonMvPolynomial ℤ (Fintype.card n) k) := by
  have hcard : Multiset.card A.charpoly.roots = Fintype.card n := by
    rw [← hA.natDegree_eq_card_roots, charpoly_natDegree_eq_dim]
  have he (j : Fin (Fintype.card n)) : (-1) ^ (j.val + 1) * A.charpolyRev.coeff (j + 1) =
      A.charpoly.roots.esymm (j + 1) := by
    simp [coeff_charpolyRev_eq_esymm_roots_charpoly_of_splits hA, ← mul_assoc, ← pow_add]
  simp only [he, Multiset.aeval_esymm_newtonMvPolynomial _ hcard]
  simpa using trace_aeval_eq_sum_roots_charpoly_of_splits hA (X ^ k)

end Splits

/-- The coefficient ring `ℤ[Xᵢⱼ]` of the universal matrix `Matrix.mvPolynomialX n n ℤ` embeds into
an algebraically closed field, in which the characteristic polynomial of the universal matrix
splits. Identities in the coefficients of `det (1 - X A)` and the traces of the powers of `A`
proved in the split case pull back along this embedding, then specialise to every matrix along
`Xᵢⱼ ↦ Aᵢⱼ` (`Matrix.mvPolynomialX_map_eval₂`). -/
private noncomputable def universalEmbedding (n : Type*) :
    MvPolynomial (n × n) ℤ →+* AlgebraicClosure (FractionRing (MvPolynomial (n × n) ℤ)) :=
  (algebraMap (FractionRing (MvPolynomial (n × n) ℤ)) _).comp
    (algebraMap (MvPolynomial (n × n) ℤ) (FractionRing (MvPolynomial (n × n) ℤ)))

private theorem universalEmbedding_injective (n : Type*) :
    Function.Injective (universalEmbedding n) :=
  (algebraMap (FractionRing (MvPolynomial (n × n) ℤ)) _).injective.comp
    (IsFractionRing.injective _ _)

variable {n m R : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [CommRing R]

/-- **Newton's identities** for the traces of the powers of a matrix: over any commutative ring,
the coefficients `c_r` of `det (1 - X A)` and the traces `p_j = tr (A ^ j)` satisfy
`r c_r = -(c_(r-1) p_1 + c_(r-2) p_2 + ⋯ + c_0 p_r)`. -/
theorem mul_coeff_charpolyRev_eq_neg_sum (A : Matrix n n R) (r : ℕ) :
    (r : R) * A.charpolyRev.coeff r =
      -∑ j ∈ range r, A.charpolyRev.coeff (r - (j + 1)) * (A ^ (j + 1)).trace := by
  -- The universal matrix over `ℤ[Xᵢⱼ]`, whose characteristic polynomial splits after
  -- `universalEmbedding`.
  let U := mvPolynomialX n n ℤ
  have hU : (r : MvPolynomial (n × n) ℤ) * U.charpolyRev.coeff r =
      -∑ j ∈ range r, U.charpolyRev.coeff (r - (j + 1)) * (U ^ (j + 1)).trace := by
    apply universalEmbedding_injective n
    have h := mul_coeff_charpolyRev_eq_neg_sum_of_splits
      (IsAlgClosed.splits (U.map (universalEmbedding n)).charpoly) r
    simpa [charpolyRev_map, coeff_map, ← Matrix.map_pow, AddMonoidHom.map_trace] using h
  -- Specialise the universal identity along `Xᵢⱼ ↦ Aᵢⱼ`.
  let φ : MvPolynomial (n × n) ℤ →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R)
    fun p ↦ A p.1 p.2
  have hφ : U.map φ = A := mvPolynomialX_map_eval₂ _ A
  have h := congrArg φ hU
  simpa [← hφ, charpolyRev_map, coeff_map, ← Matrix.map_pow, AddMonoidHom.map_trace] using h

/-- **The power sums are integer polynomials in the coefficients.** Over any commutative ring, the
trace of the `k`-th power of a `d × d` matrix `A` is the integer Newton polynomial
`TauCeti.newtonMvPolynomial ℤ d k` evaluated at `e_j = (-1) ^ j c_j`, `j = 1, …, d`, where `c_j`
are the coefficients of `det (1 - X A)`. Over a field in which the characteristic polynomial
splits, `e_j` is the `j`-th elementary symmetric function of the eigenvalues. -/
theorem trace_pow_eq_aeval_newtonMvPolynomial (A : Matrix n n R) (k : ℕ) :
    (A ^ k).trace = MvPolynomial.aeval
      (fun j : Fin (Fintype.card n) ↦ (-1) ^ (j.val + 1) * A.charpolyRev.coeff (j + 1))
      (TauCeti.newtonMvPolynomial ℤ (Fintype.card n) k) := by
  -- The universal matrix over `ℤ[Xᵢⱼ]`, whose characteristic polynomial splits after
  -- `universalEmbedding`.
  let U := mvPolynomialX n n ℤ
  have hU : (U ^ k).trace = MvPolynomial.aeval
      (fun j : Fin (Fintype.card n) ↦ (-1) ^ (j.val + 1) * U.charpolyRev.coeff (j + 1))
      (TauCeti.newtonMvPolynomial ℤ (Fintype.card n) k) := by
    apply universalEmbedding_injective n
    have h := trace_pow_eq_aeval_newtonMvPolynomial_of_splits
      (IsAlgClosed.splits (U.map (universalEmbedding n)).charpoly) k
    -- Every ring homomorphism commutes with evaluating an integer polynomial.
    rw [MvPolynomial.map_aeval_eq_aeval_map (RingHom.id ℤ) _ (Subsingleton.elim _ _),
      MvPolynomial.map_id]
    simpa [charpolyRev_map, coeff_map, ← Matrix.map_pow, AddMonoidHom.map_trace] using h
  -- Specialise the universal identity along `Xᵢⱼ ↦ Aᵢⱼ`.
  let φ : MvPolynomial (n × n) ℤ →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R)
    fun p ↦ A p.1 p.2
  have hφ : U.map φ = A := mvPolynomialX_map_eval₂ _ A
  have h := congrArg φ hU
  rw [MvPolynomial.map_aeval_eq_aeval_map (RingHom.id ℤ) φ (Subsingleton.elim _ _),
    MvPolynomial.map_id] at h
  simpa [← hφ, charpolyRev_map, coeff_map, ← Matrix.map_pow, AddMonoidHom.map_trace] using h

/-- Over any commutative ring, `det (1 - X A)` determines the traces of all positive powers of `A`:
matrices with the same `det (1 - X A)`, possibly of different sizes, have the same `tr (A ^ j)`
for `0 < j`. -/
theorem trace_pow_eq_of_charpolyRev_eq {A : Matrix n n R} {B : Matrix m m R}
    (h : A.charpolyRev = B.charpolyRev) {j : ℕ} (hj : 0 < j) :
    (A ^ j).trace = (B ^ j).trace := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  obtain ⟨r, rfl⟩ : ∃ r, j = r + 1 := ⟨j - 1, by omega⟩
  -- The last term of Newton's identity in degree `r + 1` is `c_0 p_(r + 1) = p_(r + 1)`.
  have hA := A.mul_coeff_charpolyRev_eq_neg_sum (r + 1)
  have hB := B.mul_coeff_charpolyRev_eq_neg_sum (r + 1)
  rw [sum_range_succ, Nat.sub_self, coeff_charpolyRev_zero, one_mul] at hA hB
  rw [h] at hA
  have hsum : ∑ i ∈ range r, B.charpolyRev.coeff (r + 1 - (i + 1)) * (A ^ (i + 1)).trace =
      ∑ i ∈ range r, B.charpolyRev.coeff (r + 1 - (i + 1)) * (B ^ (i + 1)).trace :=
    sum_congr rfl fun i hi ↦ by rw [ih (i + 1) (by have := mem_range.1 hi; omega) (by omega)]
  linear_combination hA - hB - hsum

/-- Over any commutative ring, matrices with the same characteristic polynomial, possibly of
different sizes, have the same traces of all powers. -/
theorem trace_pow_eq_of_charpoly_eq {A : Matrix n n R} {B : Matrix m m R}
    (h : A.charpoly = B.charpoly) (j : ℕ) : (A ^ j).trace = (B ^ j).trace := by
  nontriviality R
  rcases j.eq_zero_or_pos with rfl | hj
  · have hnm := congrArg natDegree h
    rw [charpoly_natDegree_eq_dim, charpoly_natDegree_eq_dim] at hnm
    simp [hnm]
  exact trace_pow_eq_of_charpolyRev_eq (by rw [← reverse_charpoly, ← reverse_charpoly, h]) hj

/-- Without additive torsion in the scalars, the traces of `A ^ j` for `0 < j ≤ r` determine the
`r`-th coefficient of `det (1 - X A)`. -/
theorem coeff_charpolyRev_eq_of_trace_pow_eq [IsAddTorsionFree R] {A : Matrix n n R}
    {B : Matrix m m R} {r : ℕ} (h : ∀ j, 0 < j → j ≤ r → (A ^ j).trace = (B ^ j).trace) :
    A.charpolyRev.coeff r = B.charpolyRev.coeff r := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  have hA := A.mul_coeff_charpolyRev_eq_neg_sum r
  have hB := B.mul_coeff_charpolyRev_eq_neg_sum r
  have hsum : ∑ j ∈ range r, A.charpolyRev.coeff (r - (j + 1)) * (A ^ (j + 1)).trace =
      ∑ j ∈ range r, B.charpolyRev.coeff (r - (j + 1)) * (B ^ (j + 1)).trace :=
    sum_congr rfl fun j hj ↦ by
      rw [mem_range] at hj
      rw [ih _ (by omega) fun i hi hir ↦ h i hi (by omega), h _ (by omega) (by omega)]
  rw [hsum, ← hB, ← nsmul_eq_mul, ← nsmul_eq_mul] at hA
  exact ((AddCommute.all _ _).nsmul_right_inj hr.ne').1 hA

/-- Without additive torsion in the scalars, `det (1 - X A)` and `det (1 - X B)` agree if and only
if `A` and `B` have the same traces of all positive powers. The matrices may have different
sizes. -/
theorem charpolyRev_eq_iff_trace_pow_eq [IsAddTorsionFree R] {A : Matrix n n R}
    {B : Matrix m m R} :
    A.charpolyRev = B.charpolyRev ↔ ∀ j, 0 < j → (A ^ j).trace = (B ^ j).trace :=
  ⟨fun h _ ↦ trace_pow_eq_of_charpolyRev_eq h, fun h ↦ AddMonoidAlgebra.ext <| Finsupp.ext fun _ ↦
    coeff_charpolyRev_eq_of_trace_pow_eq fun j hj _ ↦ h j hj⟩

/-- Without additive torsion in the scalars, two square matrices of the same size have the same
characteristic polynomial if and only if they have the same traces of all positive powers. -/
theorem charpoly_eq_iff_trace_pow_eq [IsAddTorsionFree R] {A : Matrix n n R}
    {B : Matrix m m R} (hnm : Fintype.card n = Fintype.card m) :
    A.charpoly = B.charpoly ↔ ∀ j, 0 < j → (A ^ j).trace = (B ^ j).trace := by
  rw [← charpolyRev_eq_charpolyRev_iff hnm, charpolyRev_eq_iff_trace_pow_eq]

/-- Without additive torsion in the scalars, the traces of `A ^ j` for `0 < j ≤ d` determine the
characteristic polynomial of a `d × d` matrix `A`. -/
theorem charpoly_eq_of_trace_pow_eq [IsAddTorsionFree R] {A : Matrix n n R} {B : Matrix m m R}
    (hnm : Fintype.card n = Fintype.card m)
    (h : ∀ j, 0 < j → j ≤ Fintype.card n → (A ^ j).trace = (B ^ j).trace) :
    A.charpoly = B.charpoly := by
  have hrev : A.charpolyRev = B.charpolyRev := AddMonoidAlgebra.ext <| Finsupp.ext fun r ↦ by
    rcases le_or_gt r (Fintype.card n) with hr | hr
    · exact coeff_charpolyRev_eq_of_trace_pow_eq fun j hj hjr ↦ h j hj (hjr.trans hr)
    · rw [coeff_charpolyRev_eq_zero A hr, coeff_charpolyRev_eq_zero B (hnm ▸ hr)]
  exact (charpolyRev_eq_charpolyRev_iff hnm).1 hrev

/-- Without additive torsion in the scalars, a `d × d` matrix `A` whose powers `A ^ j` for
`0 < j ≤ d` all have trace zero satisfies `A ^ d = 0`. Its characteristic polynomial is then
`X ^ d`, so this is the Cayley–Hamilton theorem. -/
theorem pow_card_eq_zero_of_trace_pow_eq_zero [IsAddTorsionFree R] {A : Matrix n n R}
    (h : ∀ j, 0 < j → j ≤ Fintype.card n → (A ^ j).trace = 0) : A ^ Fintype.card n = 0 := by
  refine pow_eq_zero_of_charpoly_eq_X_pow ?_
  rw [← charpoly_zero]
  exact charpoly_eq_of_trace_pow_eq rfl fun j hj hjn ↦ by
    rw [h j hj hjn, zero_pow hj.ne', trace_zero]

/-- Without additive torsion in the scalars, if `A ^ 2 = 1`, then the characteristic polynomial of
`A` is `(X - 1) ^ a * (X + 1) ^ b` for any `a` and `b` with `a + b = d` and `a - b = tr A`. -/
theorem charpoly_eq_of_sq_eq_one [IsAddTorsionFree R] {A : Matrix n n R} (hA : A ^ 2 = 1)
    {a b : ℕ} (hab : a + b = Fintype.card n) (htr : (a : R) - b = A.trace) :
    A.charpoly = (X - 1) ^ a * (X + 1) ^ b := by
  -- Compare `A` with the diagonal matrix with `a` entries `1` and `b` entries `-1`.
  let D : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R := diagonal (Sum.elim (fun _ ↦ 1) fun _ ↦ -1)
  have hD : D.charpoly = (X - 1) ^ a * (X + 1) ^ b := by
    simp [D, charpoly_diagonal, Fintype.prod_sum_type, sub_eq_add_neg]
  have hDtrace (j : ℕ) : (D ^ j).trace = a + (-1) ^ j * b := by
    simp [D, diagonal_pow, trace_diagonal, Fintype.sum_sum_type, mul_comm]
  rw [← hD]
  refine charpoly_eq_of_trace_pow_eq (by simp [hab]) fun j _ _ ↦ ?_
  rw [hDtrace]
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' j
  · simp [pow_mul, hA, ← hab]
  · simp [pow_succ, pow_mul, hA, ← htr, sub_eq_add_neg]

end Matrix

namespace LinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M]
  [Module.Finite R M]

/-- **Newton's identities** for the traces of the powers of an endomorphism `f` of a finite free
module: the coefficients `c_r` of `det (1 - X f)`, the reverse of the characteristic polynomial,
and the traces `p_j = tr (f ^ j)` satisfy `r c_r = -(c_(r-1) p_1 + c_(r-2) p_2 + ⋯ + c_0 p_r)`. -/
theorem mul_coeff_reverse_charpoly_eq_neg_sum (f : Module.End R M) (r : ℕ) :
    (r : R) * f.charpoly.reverse.coeff r =
      -∑ j ∈ Finset.range r, f.charpoly.reverse.coeff (r - (j + 1)) * trace R M (f ^ (j + 1)) := by
  rw [charpoly_def, Matrix.reverse_charpoly]
  simp only [trace_eq_matrix_trace R (Module.Free.chooseBasis R M), ← LinearMap.toMatrix_pow]
  exact Matrix.mul_coeff_charpolyRev_eq_neg_sum _ r

/-- Over any commutative ring, endomorphisms of finite free modules with the same characteristic
polynomial have the same traces of all powers. The modules may be different. -/
theorem trace_pow_eq_of_charpoly_eq {N : Type*} [AddCommGroup N] [Module R N] [Module.Free R N]
    [Module.Finite R N] {f : Module.End R M} {g : Module.End R N} (h : f.charpoly = g.charpoly)
    (j : ℕ) : trace R M (f ^ j) = trace R N (g ^ j) := by
  rw [charpoly_def, charpoly_def] at h
  simp only [trace_eq_matrix_trace R (Module.Free.chooseBasis R M),
    trace_eq_matrix_trace R (Module.Free.chooseBasis R N), ← LinearMap.toMatrix_pow]
  exact Matrix.trace_pow_eq_of_charpoly_eq h j

/-- Without additive torsion in the scalars, the traces of `f ^ j` for `0 < j ≤ d` determine the
characteristic polynomial of an endomorphism `f` of a free module of rank `d`. -/
theorem charpoly_eq_of_trace_pow_eq {N : Type*} [AddCommGroup N] [Module R N] [Module.Free R N]
    [Module.Finite R N] [IsAddTorsionFree R] {f : Module.End R M} {g : Module.End R N}
    (hMN : Module.finrank R M = Module.finrank R N)
    (h : ∀ j, 0 < j → j ≤ Module.finrank R M → trace R M (f ^ j) = trace R N (g ^ j)) :
    f.charpoly = g.charpoly := by
  nontriviality R
  simp only [trace_eq_matrix_trace R (Module.Free.chooseBasis R M),
    trace_eq_matrix_trace R (Module.Free.chooseBasis R N), ← LinearMap.toMatrix_pow,
    Module.finrank_eq_card_chooseBasisIndex] at h hMN
  rw [charpoly_def, charpoly_def]
  exact Matrix.charpoly_eq_of_trace_pow_eq hMN h

/-- Without additive torsion in the scalars, an endomorphism `f` of a free module of rank `d`
whose powers `f ^ j` for `0 < j ≤ d` all have trace zero satisfies `f ^ d = 0`. -/
theorem pow_finrank_eq_zero_of_trace_pow_eq_zero [IsAddTorsionFree R] {f : Module.End R M}
    (h : ∀ j, 0 < j → j ≤ Module.finrank R M → trace R M (f ^ j) = 0) :
    f ^ Module.finrank R M = 0 := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have := Module.subsingleton R M
    exact Subsingleton.elim _ _
  let b := Module.Free.chooseBasis R M
  simp only [trace_eq_matrix_trace R b, ← LinearMap.toMatrix_pow,
    Module.finrank_eq_card_chooseBasisIndex] at h ⊢
  rw [← (toMatrix b b).map_eq_zero_iff, ← LinearMap.toMatrix_pow]
  exact Matrix.pow_card_eq_zero_of_trace_pow_eq_zero h

/-- Without additive torsion in the scalars, endomorphisms of free modules of the same finite rank
have the same characteristic polynomial if and only if they have the same traces of all positive
powers. -/
theorem charpoly_eq_iff_trace_pow_eq {N : Type*} [AddCommGroup N] [Module R N] [Module.Free R N]
    [Module.Finite R N] [IsAddTorsionFree R] {f : Module.End R M} {g : Module.End R N}
    (hMN : Module.finrank R M = Module.finrank R N) :
    f.charpoly = g.charpoly ↔ ∀ j, 0 < j → trace R M (f ^ j) = trace R N (g ^ j) :=
  ⟨fun h j _ ↦ trace_pow_eq_of_charpoly_eq h j, fun h ↦
    charpoly_eq_of_trace_pow_eq hMN fun j hj _ ↦ h j hj⟩

/-- Without additive torsion in the scalars, if `f ^ 2 = 1`, then the characteristic polynomial of
`f` is `(X - 1) ^ a * (X + 1) ^ b` for any `a` and `b` with `a + b = finrank R M` and
`a - b = tr f`. -/
theorem charpoly_eq_of_sq_eq_one [IsAddTorsionFree R] {f : Module.End R M} (hf : f ^ 2 = 1)
    {a b : ℕ} (hab : a + b = Module.finrank R M) (htr : (a : R) - b = trace R M f) :
    f.charpoly = (X - 1) ^ a * (X + 1) ^ b := by
  nontriviality R
  let e := Module.Free.chooseBasis R M
  rw [charpoly_def]
  refine Matrix.charpoly_eq_of_sq_eq_one ?_ (by rw [hab, Module.finrank_eq_card_chooseBasisIndex])
    (by rw [htr, trace_eq_matrix_trace R e])
  rw [LinearMap.toMatrix_pow, hf, LinearMap.toMatrix_one]

end LinearMap
