/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.RingTheory.Polynomial.Basic
public import TauCeti.LinearAlgebra.Matrix.Hankel
import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Positive Hankel forms and the Riesz functional

A sequence `m : ℕ → R` defines the *Riesz functional* `L_m` on `R[X]`, the linear functional with
`L_m (X ^ k) = m k`, and the Hankel quadratic forms `∑_{i,j<n} m (i + j) ξᵢ ξⱼ`. The two are tied
together by the identity `ξ ⬝ᵥ (hankelMatrix m n *ᵥ η) = L_m (p_ξ * p_η)` for the polynomials
`p_ξ = ∑_{i<n} ξᵢ Xⁱ` and `p_η` of degree less than `n`. So the Hankel matrix of size `n` is
positive semidefinite (respectively definite) exactly when `L_m (p * p)` is nonnegative (positive)
for every (nonzero) polynomial `p` of degree less than `n`, and the infinite Hankel matrix
`(m (i + j))_{i,j ∈ ℕ}` is positive semidefinite exactly when every finite section is, that is,
exactly when `L_m` is nonnegative on all squares.

Over a linearly ordered ring a positive Hankel form satisfies the Cauchy–Schwarz inequality
`L_m (p * q) ^ 2 ≤ L_m (p * p) * L_m (q * q)`, and consequently the polynomials `p` with
`L_m (p * p) = 0` form an ideal: they satisfy `L_m (p * q) = 0` for every `q`. These statements
are the algebraic input of the Hamburger moment problem, whose representing measures are
recovered from positive semidefinite Hankel matrices.

## Main definitions

* `TauCeti.rieszFunctional m`: the Riesz functional `L_m : R[X] →ₗ[R] R` of a sequence `m`.

## Main results

* `TauCeti.rieszFunctional_moments`: every linear functional on `R[X]` is the Riesz functional of
  its moments.
* `TauCeti.dotProduct_hankelMatrix_mulVec`: the Hankel form of a section is a value of the Riesz
  functional.
* `TauCeti.posSemidef_hankelMatrix_iff`, `TauCeti.posDef_hankelMatrix_iff`: positivity of a
  Hankel section in terms of the Riesz functional.
* `TauCeti.posSemidef_hankel_iff_forall_posSemidef_hankelMatrix`,
  `TauCeti.posSemidef_hankel_iff`: the infinite Hankel matrix is positive semidefinite iff all
  its sections are, iff the Riesz functional is nonnegative on squares.
* `TauCeti.sq_rieszFunctional_mul_le_of_posSemidef_hankel`: the Cauchy–Schwarz inequality.
* `TauCeti.rieszFunctional_mul_eq_zero_of_posSemidef_hankel`: the kernel of a positive Riesz
  functional is an ideal.

Both inequalities are also stated for a single positive semidefinite section and polynomials of
degree less than its size.

## References

* K. Schmüdgen, *Ten Lectures on the Moment Problem*, arXiv:2008.12698, Theorem 1.12,
  pp. 14–15, and Propositions 9.2 and 9.3, pp. 68–69.
-/

public section

open Polynomial Matrix

namespace TauCeti

variable {R : Type*}

section Riesz

variable [CommRing R]

/-- The Riesz functional `L_m` of a sequence `m`: the linear functional on `R[X]` sending `X ^ k`
to `m k`, that is `L_m (∑ₖ aₖ Xᵏ) = ∑ₖ aₖ m k`. -/
noncomputable def rieszFunctional (m : ℕ → R) : R[X] →ₗ[R] R :=
  Polynomial.lsum fun k => LinearMap.mulRight R (m k)

theorem rieszFunctional_apply (m : ℕ → R) (p : R[X]) :
    rieszFunctional m p = p.sum fun k a => a * m k := by
  simp [rieszFunctional]

@[simp]
theorem rieszFunctional_monomial (m : ℕ → R) (k : ℕ) (a : R) :
    rieszFunctional m (monomial k a) = a * m k := by
  rw [rieszFunctional_apply, sum_monomial_index a (fun k a => a * m k) (zero_mul _)]

@[simp]
theorem rieszFunctional_C (m : ℕ → R) (a : R) : rieszFunctional m (C a) = a * m 0 := by
  rw [← monomial_zero_left, rieszFunctional_monomial]

@[simp]
theorem rieszFunctional_X_pow (m : ℕ → R) (k : ℕ) : rieszFunctional m (X ^ k) = m k := by
  rw [← monomial_one_right_eq_X_pow, rieszFunctional_monomial, one_mul]

@[simp]
theorem rieszFunctional_one (m : ℕ → R) : rieszFunctional m 1 = m 0 := by
  simpa using rieszFunctional_X_pow m 0

@[simp]
theorem rieszFunctional_X (m : ℕ → R) : rieszFunctional m X = m 1 := by
  simpa using rieszFunctional_X_pow m 1

/-- Every linear functional on `R[X]` is the Riesz functional of its moments `L (X ^ k)`. -/
@[simp]
theorem rieszFunctional_moments (L : R[X] →ₗ[R] R) :
    rieszFunctional (fun k => L (X ^ k)) = L := by
  ext k
  simp [monomial_one_right_eq_X_pow]

/-- The Hankel form of the section of size `n` is a value of the Riesz functional:
`ξ ⬝ᵥ (hankelMatrix m n *ᵥ η) = L_m (p_ξ * p_η)` with `p_ξ = ∑_{i<n} ξᵢ Xⁱ`. -/
theorem dotProduct_hankelMatrix_mulVec (m : ℕ → R) {n : ℕ} (ξ η : Fin n → R) :
    ξ ⬝ᵥ (hankelMatrix m n *ᵥ η) =
      rieszFunctional m ((∑ i : Fin n, monomial i (ξ i)) * ∑ j : Fin n, monomial j (η j)) := by
  rw [Finset.sum_mul_sum]
  simp only [dotProduct, mulVec, hankelMatrix_apply, Finset.mul_sum, map_sum,
    monomial_mul_monomial, rieszFunctional_monomial]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Riesz

/-- A polynomial of degree less than `n` is the sum of its first `n` monomials. -/
private theorem sum_monomial_coeff_of_degree_lt [CommRing R] {n : ℕ} {p : R[X]}
    (hp : p.degree < n) : ∑ i : Fin n, monomial i (p.coeff i) = p := by
  rw [sum_fin (fun i a => monomial i a) (fun i => monomial_zero_right i) hp, sum_monomial_eq]

/-- The polynomial `∑_{i<n} ξᵢ Xⁱ` has degree less than `n`. -/
private theorem degree_sum_monomial_lt [CommRing R] {n : ℕ} (ξ : Fin n → R) :
    (∑ i : Fin n, monomial i (ξ i)).degree < n :=
  mem_degreeLT.mp <| (degreeLT R n).sum_mem fun i _ => monomial_coe_mem_degreeLT i (ξ i)

private theorem degree_lt_natDegree_add_one [CommRing R] (p : R[X]) :
    p.degree < ↑(p.natDegree + 1) :=
  degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr p.natDegree.lt_succ_self)

/-- Two polynomials have degree less than `max p.natDegree q.natDegree + 1`. -/
private theorem degree_lt_max_natDegree_add_one [CommRing R] (p q : R[X]) :
    p.degree < ↑(max p.natDegree q.natDegree + 1) ∧
      q.degree < ↑(max p.natDegree q.natDegree + 1) :=
  ⟨(degree_lt_natDegree_add_one p).trans_le (Nat.cast_le.mpr (by omega)),
    (degree_lt_natDegree_add_one q).trans_le (Nat.cast_le.mpr (by omega))⟩

/-- Over a ring with trivial star, a Hankel section is Hermitian. -/
theorem isHermitian_hankelMatrix [Star R] [TrivialStar R] (m : ℕ → R) (n : ℕ) :
    (hankelMatrix m n).IsHermitian :=
  isHermitian_iff_isSymm.mpr (isSymm_hankelMatrix m n)

section Sections

variable [CommRing R] [PartialOrder R] [StarRing R] [TrivialStar R]

/-- The Hankel section of size `n` is positive semidefinite iff the Riesz functional is
nonnegative on the squares of the polynomials of degree less than `n`. -/
theorem posSemidef_hankelMatrix_iff (m : ℕ → R) (n : ℕ) :
    (hankelMatrix m n).PosSemidef ↔
      ∀ p : R[X], p.degree < n → 0 ≤ rieszFunctional m (p * p) := by
  refine ⟨fun h p hp => ?_, fun h => .of_dotProduct_mulVec_nonneg
    (isHermitian_hankelMatrix m n) fun ξ => ?_⟩
  · simpa [dotProduct_hankelMatrix_mulVec, sum_monomial_coeff_of_degree_lt hp] using
      h.dotProduct_mulVec_nonneg fun i : Fin n => p.coeff i
  · simpa [dotProduct_hankelMatrix_mulVec] using h _ (degree_sum_monomial_lt ξ)

/-- The Hankel section of size `n` is positive definite iff the Riesz functional is positive on
the squares of the nonzero polynomials of degree less than `n`. -/
theorem posDef_hankelMatrix_iff (m : ℕ → R) (n : ℕ) :
    (hankelMatrix m n).PosDef ↔
      ∀ p : R[X], p ≠ 0 → p.degree < n → 0 < rieszFunctional m (p * p) := by
  refine ⟨fun h p hp0 hp => ?_, fun h => .of_dotProduct_mulVec_pos
    (isHermitian_hankelMatrix m n) fun ξ hξ => ?_⟩
  · have hξ : (fun i : Fin n => p.coeff i) ≠ 0 := fun hξ => hp0 <| by
      rw [← sum_monomial_coeff_of_degree_lt hp]
      simp [funext_iff.mp hξ]
    simpa [dotProduct_hankelMatrix_mulVec, sum_monomial_coeff_of_degree_lt hp] using
      h.dotProduct_mulVec_pos hξ
  · have hp0 : ∑ i : Fin n, monomial i (ξ i) ≠ 0 := fun h0 => hξ <| funext fun i => by
      simpa [finsetSum_coeff, coeff_monomial, Finsupp.single_apply, Fin.val_inj] using
        congr_arg (·.coeff (i : ℕ)) h0
    simpa [dotProduct_hankelMatrix_mulVec] using h _ hp0 (degree_sum_monomial_lt ξ)

end Sections

section Infinite

/-- The infinite Hankel matrix `(m (i + j))_{i,j ∈ ℕ}` is positive semidefinite iff all its
finite sections `hankelMatrix m n` are. -/
theorem posSemidef_hankel_iff_forall_posSemidef_hankelMatrix [Ring R] [PartialOrder R]
    [StarRing R] (m : ℕ → R) :
    (Matrix.of fun i j : ℕ => m (i + j)).PosSemidef ↔ ∀ n, (hankelMatrix m n).PosSemidef :=
  (posSemidef_iff_submatrix_of_forall_finset (fun n (i : Fin n) => (i : ℕ))
    (fun s => ⟨s.sup id + 1, fun x hx =>
      ⟨⟨x, Nat.lt_succ_of_le (Finset.le_sup (f := id) hx)⟩, rfl⟩⟩)).trans <|
    forall_congr' fun n => by
      rw [show (Matrix.of fun i j : ℕ => m (i + j)).submatrix (fun i : Fin n => (i : ℕ))
        (fun i : Fin n => (i : ℕ)) = hankelMatrix m n by ext; simp]

variable [CommRing R] [PartialOrder R] [StarRing R] [TrivialStar R]

/-- The infinite Hankel matrix `(m (i + j))_{i,j ∈ ℕ}` is positive semidefinite iff the Riesz
functional `L_m` is nonnegative on every square `p * p`. -/
theorem posSemidef_hankel_iff (m : ℕ → R) :
    (Matrix.of fun i j : ℕ => m (i + j)).PosSemidef ↔
      ∀ p : R[X], 0 ≤ rieszFunctional m (p * p) := by
  simp_rw [posSemidef_hankel_iff_forall_posSemidef_hankelMatrix, posSemidef_hankelMatrix_iff]
  exact ⟨fun h p => h _ p (degree_lt_natDegree_add_one p), fun h _ p _ => h p⟩

end Infinite

section CauchySchwarz

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] [StarRing R] [TrivialStar R]

/-- The **Cauchy–Schwarz inequality** for a positive semidefinite Hankel section: for polynomials
`p` and `q` of degree less than `n`, `L_m (p * q) ^ 2 ≤ L_m (p * p) * L_m (q * q)`. -/
theorem sq_rieszFunctional_mul_le_of_posSemidef_hankelMatrix {m : ℕ → R} {n : ℕ}
    (hm : (hankelMatrix m n).PosSemidef) {p q : R[X]} (hp : p.degree < n) (hq : q.degree < n) :
    rieszFunctional m (p * q) ^ 2 ≤ rieszFunctional m (p * p) * rieszFunctional m (q * q) := by
  -- the form `(p, q) ↦ L_m (p * q)` on the polynomials of degree less than `n`
  let B : LinearMap.BilinForm R (degreeLT R n) :=
    ((LinearMap.mul R R[X]).compr₂ (rieszFunctional m)).domRestrict₁₂ _ _
  have hB (x y : degreeLT R n) : B x y = rieszFunctional m (x * y) := by
    rw [LinearMap.domRestrict₁₂_apply, LinearMap.compr₂_apply, LinearMap.mul_apply']
  have h := B.apply_mul_apply_le_of_forall_zero_le (fun x => by
    rw [hB]
    exact (posSemidef_hankelMatrix_iff m n).mp hm x (mem_degreeLT.mp x.property))
    ⟨p, mem_degreeLT.mpr hp⟩ ⟨q, mem_degreeLT.mpr hq⟩
  simpa only [hB, mul_comm q p, ← sq] using h

/-- **The kernel of a positive Hankel form is an ideal**, for one section: if the section of
size `n` is positive semidefinite, `p` and `q` have degree less than `n` and `L_m (p * p) = 0`,
then `L_m (p * q) = 0`. -/
theorem rieszFunctional_mul_eq_zero_of_posSemidef_hankelMatrix {m : ℕ → R} {n : ℕ}
    (hm : (hankelMatrix m n).PosSemidef) {p q : R[X]} (hp : p.degree < n) (hq : q.degree < n)
    (hpp : rieszFunctional m (p * p) = 0) : rieszFunctional m (p * q) = 0 := by
  have h := sq_rieszFunctional_mul_le_of_posSemidef_hankelMatrix hm hp hq
  rw [hpp, zero_mul] at h
  exact pow_eq_zero_iff two_ne_zero |>.mp <| le_antisymm h (sq_nonneg _)

/-- The **Cauchy–Schwarz inequality** for a positive semidefinite infinite Hankel matrix:
`L_m (p * q) ^ 2 ≤ L_m (p * p) * L_m (q * q)` for all polynomials `p` and `q`. -/
theorem sq_rieszFunctional_mul_le_of_posSemidef_hankel {m : ℕ → R}
    (hm : (Matrix.of fun i j : ℕ => m (i + j)).PosSemidef) (p q : R[X]) :
    rieszFunctional m (p * q) ^ 2 ≤ rieszFunctional m (p * p) * rieszFunctional m (q * q) :=
  sq_rieszFunctional_mul_le_of_posSemidef_hankelMatrix
    ((posSemidef_hankel_iff_forall_posSemidef_hankelMatrix m).mp hm _)
    (degree_lt_max_natDegree_add_one p q).1 (degree_lt_max_natDegree_add_one p q).2

/-- **The kernel of a positive Hankel form is an ideal:** if the infinite Hankel matrix of `m` is
positive semidefinite and `L_m (p * p) = 0`, then `L_m (p * q) = 0` for every polynomial `q`. -/
theorem rieszFunctional_mul_eq_zero_of_posSemidef_hankel {m : ℕ → R}
    (hm : (Matrix.of fun i j : ℕ => m (i + j)).PosSemidef) {p : R[X]}
    (hpp : rieszFunctional m (p * p) = 0) (q : R[X]) : rieszFunctional m (p * q) = 0 :=
  rieszFunctional_mul_eq_zero_of_posSemidef_hankelMatrix
    ((posSemidef_hankel_iff_forall_posSemidef_hankelMatrix m).mp hm _)
    (degree_lt_max_natDegree_add_one p q).1 (degree_lt_max_natDegree_add_one p q).2 hpp

end CauchySchwarz

/-! ### Checks -/

/-- The moments `1, 0, 0, …` of the point mass at `0`: the Riesz functional is the constant
coefficient, the Hankel matrix is positive semidefinite, `L_m (X * X) = 0`, and indeed
`L_m (X * q) = 0` for every `q`. -/
example :
    rieszFunctional (fun k => if k = 0 then (1 : ℝ) else 0) = lcoeff ℝ 0 ∧
      (Matrix.of fun i j : ℕ => if i + j = 0 then (1 : ℝ) else 0).PosSemidef ∧
      ∀ q, rieszFunctional (fun k => if k = 0 then (1 : ℝ) else 0) (X * q) = 0 := by
  have hL : rieszFunctional (fun k => if k = 0 then (1 : ℝ) else 0) = lcoeff ℝ 0 := by
    ext k
    simp [coeff_monomial, Finsupp.single_apply]
  have hm : (Matrix.of fun i j : ℕ => if i + j = 0 then (1 : ℝ) else 0).PosSemidef :=
    (posSemidef_hankel_iff _).mpr fun p => by
      rw [hL, lcoeff_apply, mul_coeff_zero]
      exact mul_self_nonneg _
  exact ⟨hL, hm, rieszFunctional_mul_eq_zero_of_posSemidef_hankel hm (by simp [hL])⟩

/-- Positive semidefiniteness is needed for the kernel to be an ideal: for `m = 1, 0, -1, 0, 0, …`
the section of size `2` is `diag(1, -1)`, and `p = 1 + X` has `L_m (p * p) = 0` but
`L_m (p * 1) = 1`. -/
example :
    ¬ (hankelMatrix (fun k => if k = 0 then (1 : ℝ) else if k = 2 then -1 else 0) 2).PosSemidef ∧
      rieszFunctional (fun k => if k = 0 then (1 : ℝ) else if k = 2 then -1 else 0)
        ((1 + X) * (1 + X)) = 0 ∧
      rieszFunctional (fun k => if k = 0 then (1 : ℝ) else if k = 2 then -1 else 0)
        ((1 + X) * 1) = 1 := by
  refine ⟨fun h => ?_, ?_, ?_⟩
  · have := h.diag_nonneg (i := 1)
    norm_num at this
  · rw [show (1 + X : ℝ[X]) * (1 + X) = 1 + X + X + X ^ 2 by ring]
    simp
  · simp

end TauCeti
