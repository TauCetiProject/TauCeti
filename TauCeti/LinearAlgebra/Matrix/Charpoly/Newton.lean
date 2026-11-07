/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Charpoly.Reverse
public import Mathlib.LinearAlgebra.Trace
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
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

When division by the integers `1, …, r` is unique, the recurrence determines `c_r` from the traces
`p_1, …, p_r`. So over a ring without additive torsion, such as a field of characteristic zero,
the traces of the first `d` powers of a `d × d` matrix determine its characteristic polynomial.

## Main results

* `Matrix.mul_coeff_charpolyRev_eq_neg_sum`: **Newton's identities** for the traces of the powers
  of a matrix over any commutative ring; `LinearMap.mul_coeff_reverse_charpoly_eq_neg_sum` is the
  same statement for an endomorphism of a finite free module.
* `Matrix.trace_pow_eq_of_charpolyRev_eq`: over any commutative ring, `det (1 - X A)` determines
  the traces of all positive powers of `A`.
* `Matrix.coeff_charpolyRev_eq_of_trace_pow_eq`, `Matrix.charpolyRev_eq_iff_trace_pow_eq`,
  `Matrix.charpoly_eq_iff_trace_pow_eq`: conversely, without additive torsion, the traces of the
  positive powers determine `det (1 - X A)` and the characteristic polynomial.
* `Matrix.charpoly_eq_of_trace_pow_eq`, `LinearMap.charpoly_eq_of_trace_pow_eq`: without additive
  torsion, the traces of `A ^ j` for `0 < j ≤ d` already determine the characteristic polynomial
  of a `d × d` matrix, or of an endomorphism of a free module of rank `d`.

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
    refine sum_nbij' (fun a ↦ a.2 - 1) (fun j ↦ (r - (j + 1), j + 1)) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [mem_filter, mem_antidiagonal] at ha
      simp only [mem_range]
      omega
    · intro j hj
      simp only [mem_range] at hj
      simp only [mem_filter, mem_antidiagonal]
      omega
    · intro a ha
      simp only [mem_filter, mem_antidiagonal] at ha
      ext <;> simp <;> omega
    · intro j hj
      simp
    · intro a ha
      simp only [mem_filter, mem_antidiagonal] at ha
      have h₁ : a.2 - 1 + 1 = a.2 := by omega
      have h₂ : r - a.2 = a.1 := by omega
      simp only [h₁, h₂]
  have h := s.mul_esymm_eq_sum r
  rw [hsum] at h
  calc (r : K) * ((-1) ^ r * s.esymm r) = (-1) ^ r * (r * s.esymm r) := by ring
    _ = _ := by
      rw [h, ← mul_assoc, ← pow_add, show r + (r + 1) = 2 * r + 1 by ring, pow_succ, pow_mul]
      simp [s]

end Splits

variable {n m R : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [CommRing R]

/-- **Newton's identities** for the traces of the powers of a matrix: over any commutative ring,
the coefficients `c_r` of `det (1 - X A)` and the traces `p_j = tr (A ^ j)` satisfy
`r c_r = -(c_(r-1) p_1 + c_(r-2) p_2 + ⋯ + c_0 p_r)`. -/
theorem mul_coeff_charpolyRev_eq_neg_sum (A : Matrix n n R) (r : ℕ) :
    (r : R) * A.charpolyRev.coeff r =
      -∑ j ∈ range r, A.charpolyRev.coeff (r - (j + 1)) * (A ^ (j + 1)).trace := by
  -- The universal matrix over `ℤ[Xᵢⱼ]`, whose coefficient ring embeds into an algebraically
  -- closed field, where the characteristic polynomial splits.
  let U := mvPolynomialX n n ℤ
  let K := AlgebraicClosure (FractionRing (MvPolynomial (n × n) ℤ))
  let ι : MvPolynomial (n × n) ℤ →+* K :=
    (algebraMap (FractionRing (MvPolynomial (n × n) ℤ)) K).comp
      (algebraMap (MvPolynomial (n × n) ℤ) (FractionRing (MvPolynomial (n × n) ℤ)))
  have hι : Function.Injective ι :=
    (algebraMap (FractionRing (MvPolynomial (n × n) ℤ)) K).injective.comp
      (IsFractionRing.injective _ _)
  have hU : (r : MvPolynomial (n × n) ℤ) * U.charpolyRev.coeff r =
      -∑ j ∈ range r, U.charpolyRev.coeff (r - (j + 1)) * (U ^ (j + 1)).trace := by
    apply hι
    have h := mul_coeff_charpolyRev_eq_neg_sum_of_splits (IsAlgClosed.splits (U.map ι).charpoly) r
    simpa [charpolyRev_map, coeff_map, ← Matrix.map_pow, AddMonoidHom.map_trace] using h
  -- Specialise the universal identity along `Xᵢⱼ ↦ Aᵢⱼ`.
  let φ : MvPolynomial (n × n) ℤ →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R)
    fun p ↦ A p.1 p.2
  have hφ : U.map φ = A := mvPolynomialX_map_eval₂ _ A
  have h := congrArg φ hU
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
  ⟨fun h _ ↦ trace_pow_eq_of_charpolyRev_eq h, fun h ↦ Polynomial.ext fun _ ↦
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
  have hrev : A.charpolyRev = B.charpolyRev := Polynomial.ext fun r ↦ by
    rcases le_or_gt r (Fintype.card n) with hr | hr
    · exact coeff_charpolyRev_eq_of_trace_pow_eq fun j hj hjr ↦ h j hj (hjr.trans hr)
    · rw [coeff_charpolyRev_eq_zero A hr, coeff_charpolyRev_eq_zero B (hnm ▸ hr)]
  exact (charpolyRev_eq_charpolyRev_iff hnm).1 hrev

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

end LinearMap
