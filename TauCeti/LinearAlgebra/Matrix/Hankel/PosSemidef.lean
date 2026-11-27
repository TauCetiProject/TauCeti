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
# Positive Hankel forms

A sequence `m : ℕ → R` defines the *Riesz functional* `L_m` on `R[X]`, the linear functional with
`L_m (X ^ k) = m k` (`TauCeti.rieszFunctional`), and the Hankel quadratic forms
`∑_{i,j<n} m (i + j) ξᵢ ξⱼ`. The two are tied together by the identity
`ξ ⬝ᵥ (hankelMatrix m n *ᵥ η) = L_m (p_ξ * p_η)` for the polynomials `p_ξ = ∑_{i<n} ξᵢ Xⁱ` and
`p_η` of degree less than `n` (`TauCeti.dotProduct_hankelMatrix_mulVec`). So the Hankel matrix of
size `n` is positive semidefinite (respectively definite) exactly when `L_m (p * p)` is nonnegative
(positive) for every (nonzero) polynomial `p` of degree less than `n`, and the infinite Hankel
matrix `(m (i + j))_{i,j ∈ ℕ}` is positive semidefinite exactly when every finite section is, that
is, exactly when `L_m` is nonnegative on all squares.

Over a linearly ordered ring a positive Hankel form satisfies the Cauchy–Schwarz inequality
`L_m (p * q) ^ 2 ≤ L_m (p * p) * L_m (q * q)`, and consequently the polynomials `p` with
`L_m (p * p) = 0` form an ideal: they satisfy `L_m (p * q) = 0` for every `q`. These statements
are the algebraic input of the Hamburger moment problem, whose representing measures are
recovered from positive semidefinite Hankel matrices.

## Main results

* `TauCeti.posSemidef_hankelMatrix_iff`, `TauCeti.posDef_hankelMatrix_iff`: positivity of a
  Hankel section in terms of the Riesz functional.
* `TauCeti.posSemidef_hankel_iff_forall_posSemidef_hankelMatrix`,
  `TauCeti.posSemidef_hankel_iff`: the infinite Hankel matrix is positive semidefinite iff all
  its sections are, iff the Riesz functional is nonnegative on squares.
* `TauCeti.sq_rieszFunctional_mul_le_of_posSemidef_hankel`: the Cauchy–Schwarz inequality.
* `TauCeti.rieszFunctional_mul_eq_zero_of_posSemidef_hankel`: the polynomials `p` with
  `L_m (p * p) = 0` satisfy `L_m (p * q) = 0` for every `q`, so they form an ideal.

Both results are also stated for a single positive semidefinite section and polynomials of
degree less than its size.

## References

* K. Schmüdgen, *Ten Lectures on the Moment Problem*, arXiv:2008.12698, Theorem 1.12,
  pp. 14–15, and Propositions 9.2 and 9.3, pp. 68–69.
-/

public section

open Polynomial Matrix

namespace TauCeti

variable {R : Type*}

section Form

variable [CommSemiring R]

/-- The Hankel form on the coefficient vectors of two polynomials of degree less than `n` is the
value `L_m (p * q)` of the Riesz functional. -/
private theorem dotProduct_hankelMatrix_mulVec_degreeLTEquiv (m : ℕ → R) {n : ℕ}
    (p q : degreeLT R n) :
    degreeLTEquiv R n p ⬝ᵥ (hankelMatrix m n *ᵥ degreeLTEquiv R n q) =
      rieszFunctional m (p * q) := by
  -- the inverse of `degreeLTEquiv R n` is `ξ ↦ ∑ i, monomial i (ξ i)` by definition
  have h (r : degreeLT R n) : (r : R[X]) = ∑ i : Fin n, monomial i (degreeLTEquiv R n r i) :=
    congrArg Subtype.val ((degreeLTEquiv R n).symm_apply_apply r).symm
  rw [dotProduct_hankelMatrix_mulVec, ← h, ← h]

/-- The Hankel form `(p, q) ↦ L_m (p * q)` on the polynomials of degree less than `n`. -/
private noncomputable def hankelForm (m : ℕ → R) (n : ℕ) :
    LinearMap.BilinForm R (degreeLT R n) :=
  ((LinearMap.mul R R[X]).compr₂ (rieszFunctional m)).domRestrict₁₂ _ _

private theorem hankelForm_apply (m : ℕ → R) {n : ℕ} (p q : degreeLT R n) :
    hankelForm m n p q = rieszFunctional m (p * q) := by
  rw [hankelForm, LinearMap.domRestrict₁₂_apply, LinearMap.compr₂_apply, LinearMap.mul_apply']

private theorem isSymm_hankelForm (m : ℕ → R) (n : ℕ) : LinearMap.IsSymm (hankelForm m n) :=
  ⟨fun p q => by simp [hankelForm_apply, mul_comm]⟩

end Form

section Sections

variable [CommRing R] [PartialOrder R] [StarRing R] [TrivialStar R]

/-- The Hankel section of size `n` is positive semidefinite iff the Riesz functional is
nonnegative on the squares of the polynomials of degree less than `n`. -/
theorem posSemidef_hankelMatrix_iff (m : ℕ → R) (n : ℕ) :
    (hankelMatrix m n).PosSemidef ↔
      ∀ p : R[X], p.degree < n → 0 ≤ rieszFunctional m (p * p) := by
  refine ⟨fun h p hp => ?_, fun h => .of_dotProduct_mulVec_nonneg
    (isHermitian_hankelMatrix m n) fun ξ => ?_⟩
  · have := h.dotProduct_mulVec_nonneg (degreeLTEquiv R n ⟨p, mem_degreeLT.mpr hp⟩)
    rwa [star_trivial, dotProduct_hankelMatrix_mulVec_degreeLTEquiv] at this
  · obtain ⟨p, rfl⟩ := (degreeLTEquiv R n).surjective ξ
    rw [star_trivial, dotProduct_hankelMatrix_mulVec_degreeLTEquiv]
    exact h p (mem_degreeLT.mp p.property)

/-- The Hankel section of size `n` is positive definite iff the Riesz functional is positive on
the squares of the nonzero polynomials of degree less than `n`. -/
theorem posDef_hankelMatrix_iff (m : ℕ → R) (n : ℕ) :
    (hankelMatrix m n).PosDef ↔
      ∀ p : R[X], p ≠ 0 → p.degree < n → 0 < rieszFunctional m (p * p) := by
  refine ⟨fun h p hp0 hp => ?_, fun h => .of_dotProduct_mulVec_pos
    (isHermitian_hankelMatrix m n) fun ξ hξ => ?_⟩
  · have := h.dotProduct_mulVec_pos
      ((degreeLTEquiv_eq_zero_iff_eq_zero (mem_degreeLT.mpr hp)).not.mpr hp0)
    rwa [star_trivial, dotProduct_hankelMatrix_mulVec_degreeLTEquiv] at this
  · obtain ⟨p, rfl⟩ := (degreeLTEquiv R n).surjective ξ
    rw [star_trivial, dotProduct_hankelMatrix_mulVec_degreeLTEquiv]
    exact h p (ZeroMemClass.coe_eq_zero.not.mpr ((degreeLTEquiv R n).map_ne_zero_iff.mp hξ))
      (mem_degreeLT.mp p.property)

private theorem hankelForm_self_nonneg {m : ℕ → R} {n : ℕ} (hm : (hankelMatrix m n).PosSemidef)
    (p : degreeLT R n) : 0 ≤ hankelForm m n p p := by
  rw [hankelForm_apply]
  exact (posSemidef_hankelMatrix_iff m n).mp hm p (mem_degreeLT.mp p.property)

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
    forall_congr' fun n => by rw [submatrix_hankel_eq_hankelMatrix]

variable [CommRing R] [PartialOrder R] [StarRing R] [TrivialStar R]

/-- The infinite Hankel matrix `(m (i + j))_{i,j ∈ ℕ}` is positive semidefinite iff the Riesz
functional `L_m` is nonnegative on every square `p * p`. -/
theorem posSemidef_hankel_iff (m : ℕ → R) :
    (Matrix.of fun i j : ℕ => m (i + j)).PosSemidef ↔
      ∀ p : R[X], 0 ≤ rieszFunctional m (p * p) := by
  simp_rw [posSemidef_hankel_iff_forall_posSemidef_hankelMatrix, posSemidef_hankelMatrix_iff]
  exact ⟨fun h p => h _ p <| degree_le_natDegree.trans_lt <| Nat.cast_lt.mpr <| Nat.lt_succ_self _,
    fun h _ p _ => h p⟩

end Infinite

section CauchySchwarz

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] [StarRing R] [TrivialStar R]

/-- The **Cauchy–Schwarz inequality** for a positive semidefinite Hankel section: for polynomials
`p` and `q` of degree less than `n`, `L_m (p * q) ^ 2 ≤ L_m (p * p) * L_m (q * q)`. -/
theorem sq_rieszFunctional_mul_le_of_posSemidef_hankelMatrix {m : ℕ → R} {n : ℕ}
    (hm : (hankelMatrix m n).PosSemidef) {p q : R[X]} (hp : p.degree < n) (hq : q.degree < n) :
    rieszFunctional m (p * q) ^ 2 ≤ rieszFunctional m (p * p) * rieszFunctional m (q * q) := by
  simpa only [hankelForm_apply] using (hankelForm m n).apply_sq_le_of_symm
    (hankelForm_self_nonneg hm) (isSymm_hankelForm m n) ⟨p, mem_degreeLT.mpr hp⟩
    ⟨q, mem_degreeLT.mpr hq⟩

/-- **Isotropic vectors of a positive semidefinite Hankel section lie in its radical:** if the
section of size `n` is positive semidefinite, `p` and `q` have degree less than `n` and
`L_m (p * p) = 0`, then `L_m (p * q) = 0`. -/
theorem rieszFunctional_mul_eq_zero_of_posSemidef_hankelMatrix {m : ℕ → R} {n : ℕ}
    (hm : (hankelMatrix m n).PosSemidef) {p q : R[X]} (hp : p.degree < n) (hq : q.degree < n)
    (hpp : rieszFunctional m (p * p) = 0) : rieszFunctional m (p * q) = 0 := by
  have h := ((hankelForm m n).apply_apply_same_eq_zero_iff (hankelForm_self_nonneg hm)
    (isSymm_hankelForm m n) (x := ⟨p, mem_degreeLT.mpr hp⟩)).mp (by rwa [hankelForm_apply])
  simpa only [hankelForm_apply, LinearMap.zero_apply] using
    LinearMap.congr_fun (LinearMap.mem_ker.mp h) ⟨q, mem_degreeLT.mpr hq⟩

/-- The **Cauchy–Schwarz inequality** for a positive semidefinite infinite Hankel matrix:
`L_m (p * q) ^ 2 ≤ L_m (p * p) * L_m (q * q)` for all polynomials `p` and `q`. -/
theorem sq_rieszFunctional_mul_le_of_posSemidef_hankel {m : ℕ → R}
    (hm : (Matrix.of fun i j : ℕ => m (i + j)).PosSemidef) (p q : R[X]) :
    rieszFunctional m (p * q) ^ 2 ≤ rieszFunctional m (p * p) * rieszFunctional m (q * q) :=
  sq_rieszFunctional_mul_le_of_posSemidef_hankelMatrix
    ((posSemidef_hankel_iff_forall_posSemidef_hankelMatrix m).mp hm
      (max p.natDegree q.natDegree + 1))
    (degree_le_natDegree.trans_lt (Nat.cast_lt.mpr (by omega)))
    (degree_le_natDegree.trans_lt (Nat.cast_lt.mpr (by omega)))

/-- **The kernel of a positive Hankel form is an ideal:** if the infinite Hankel matrix of `m` is
positive semidefinite and `L_m (p * p) = 0`, then `L_m (p * q) = 0` for every polynomial `q`, so
the polynomials `p` with `L_m (p * p) = 0` form an ideal. -/
theorem rieszFunctional_mul_eq_zero_of_posSemidef_hankel {m : ℕ → R}
    (hm : (Matrix.of fun i j : ℕ => m (i + j)).PosSemidef) {p : R[X]}
    (hpp : rieszFunctional m (p * p) = 0) (q : R[X]) : rieszFunctional m (p * q) = 0 :=
  rieszFunctional_mul_eq_zero_of_posSemidef_hankelMatrix
    ((posSemidef_hankel_iff_forall_posSemidef_hankelMatrix m).mp hm
      (max p.natDegree q.natDegree + 1))
    (degree_le_natDegree.trans_lt (Nat.cast_lt.mpr (by omega)))
    (degree_le_natDegree.trans_lt (Nat.cast_lt.mpr (by omega))) hpp

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
