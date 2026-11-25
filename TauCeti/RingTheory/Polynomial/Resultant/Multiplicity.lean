/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.Polynomial.Taylor
import TauCeti.Algebra.Polynomial.Roots
import TauCeti.LinearAlgebra.Matrix.Determinant.IdealDivisibility
import TauCeti.LinearAlgebra.Matrix.Polynomial
import TauCeti.RingTheory.Polynomial.Resultant.Basic

/-!
# Multiplicities of a plane curve along its fibres, bounded by a resultant

Let `F(z, z')` be a polynomial in two variables, viewed as a polynomial in `z` whose coefficients
are polynomials in `z'`, so `F : R[X][X]`. Freezing `z' = b` gives the one-variable polynomial
`F(·, b) = F.map (evalRingHom b)`. If `F(·, b)` has a root `a` of multiplicity `k + 1`, then
`F(·, b)` and its derivative share the root `a` with multiplicity `k`, and the discriminant-type
resultant `Res_z(F, ∂_z F) ∈ R[X]` vanishes to order at least `k` at `z' = b`.

Summed over points with *distinct* second coordinates, the excess multiplicities
`mult_a F(·, b) - 1` are therefore bounded by the degree of `Res_z(F, ∂_z F)` in `z'`, which is
at most `(2 deg_z F - 1) deg_{z'} F`. For a squarefree `F` over a characteristic-zero GCD domain
(for instance an irreducible `F` over `K[z']`, `K` a field of characteristic zero) the resultant
is nonzero by `Squarefree.resultant_derivative_ne_zero`, so the bound applies.

This is the resultant multiplicity bound of the determinant method for real zeros of quadratic
Dirichlet `L`-functions (Ben Green, *On Landau–Siegel zeros*, Hexagon 2610.00311, 2026,
Appendix A): it controls how often an irreducible curve can vanish to high order in `z` at the
points of a grid.

The underlying general fact is that the Sylvester matrix has `k` rows divisible by `t` as soon as
the coefficients of index below `k` of both polynomials are divisible by `t`; translating the root
to the origin (`Polynomial.resultant_taylor`) puts us in this situation with `t = X - C b`.

## Main results

* `Polynomial.pow_dvd_resultant_of_dvd_coeff`: if `t` divides the coefficients of index below `k`
  of `f` and `g`, then `t ^ k` divides `resultant f g m n`.
* `Polynomial.pow_dvd_resultant_derivative`: if `(X - C a) ^ (k + 1)` divides `F(·, b) ≠ 0`, then
  `(X - C b) ^ k` divides `Res_z(F, ∂_z F)`.
* `Polynomial.rootMultiplicity_map_sub_one_le_rootMultiplicity_resultant_derivative`: the same in
  terms of root multiplicities.
* `Polynomial.natDegree_resultant_le`: the degree of a resultant of bivariate polynomials in the
  coefficient variable is at most `m b + n a`, where `a` and `b` bound the coefficient degrees of
  the two polynomials and `m` and `n` are the degree bounds used for the Sylvester matrix.
* `Polynomial.sum_rootMultiplicity_map_sub_one_le`: over a domain, for points with distinct
  second coordinates the excess multiplicities sum to at most `(2 deg_z F - 1) d` when every
  coefficient of `F` has degree at most `d` and `Res_z(F, ∂_z F) ≠ 0`.
* `Polynomial.sum_rootMultiplicity_map_le`: the same bound for the multiplicities themselves,
  plus the number of the points lying on the curve `F = 0`.
-/

public section

open Finset

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- If `t` divides every coefficient of index below `k` of both `f` and `g`, then `t ^ k` divides
the resultant `resultant f g m n`, for any degree bounds with `k ≤ m + n`: the first `k` rows of the
Sylvester matrix only involve those coefficients. -/
theorem pow_dvd_resultant_of_dvd_coeff {f g : R[X]} {m n k : ℕ} {t : R} (hk : k ≤ m + n)
    (hf : ∀ l < k, t ∣ f.coeff l) (hg : ∀ l < k, t ∣ g.coeff l) :
    t ^ k ∣ resultant f g m n := by
  have hrow : ∀ i j : Fin (m + n), (if (i : ℕ) < k then t else 1) ∣ sylvester f g m n i j := by
    intro i j
    split_ifs with hi
    · by_cases hj : (j : ℕ) < m
      · rw [sylvester_apply_of_lt _ _ _ _ hj]
        split_ifs
        exacts [hg _ (by omega), dvd_zero t]
      · rw [sylvester_apply_of_le _ _ _ _ (not_lt.mp hj)]
        split_ifs
        exacts [hf _ (by omega), dvd_zero t]
    · exact one_dvd _
  have hcard : #{i : Fin (m + n) | (i : ℕ) < k} = k := by
    rw [Fin.card_filter_val_lt, min_eq_right hk]
  simpa [resultant, prod_ite, hcard] using Matrix.prod_dvd_det_of_dvd_row _ _ hrow

/-- **The resultant multiplicity bound, pointwise.** Let `F : R[X][X]` be a polynomial in `z` with
coefficients in `R[z']`. If the fibre `F(·, b)` is nonzero and has a root `a` of multiplicity at
least `k + 1`, then `(z' - b) ^ k` divides the resultant `Res_z(F, ∂_z F)`. -/
theorem pow_dvd_resultant_derivative {F : R[X][X]} {a b : R} {k : ℕ}
    (hF : F.map (evalRingHom b) ≠ 0) (h : (X - C a) ^ (k + 1) ∣ F.map (evalRingHom b)) :
    (X - C b) ^ k ∣ resultant F (derivative F) := by
  have : Nontrivial R := by
    by_contra hR
    rw [not_nontrivial_iff_subsingleton] at hR
    exact hF (Subsingleton.elim _ _)
  have hkF : k + 1 ≤ F.natDegree := by
    have := ((monic_X_sub_C a).pow (k + 1)).natDegree_le_of_dvd hF h
    rw [(monic_X_sub_C a).natDegree_pow, natDegree_X_sub_C, mul_one] at this
    exact this.trans natDegree_map_le
  -- Translate the root `a` to the origin: the resultant is unchanged.
  set G := F.taylor (C a)
  have hres : resultant G (derivative G) = resultant F (derivative F) := by
    rw [← taylor_derivative, resultant_taylor]
  -- The coefficients of `G` of index at most `k` vanish at `z' = b`.
  obtain ⟨q, hq⟩ := h
  have hG : ∀ l ≤ k, X - C b ∣ G.coeff l := by
    intro l hl
    have hmap : G.map (evalRingHom b) = X ^ (k + 1) * q.taylor a := by
      simp only [G, map_taylor, coe_evalRingHom, eval_C, hq, taylor_mul, taylor_pow, map_sub,
        taylor_X, taylor_C, add_sub_cancel_right]
    have := congrArg (fun p : R[X] ↦ p.coeff l) hmap
    simp only [coeff_map, coe_evalRingHom, coeff_X_pow_mul'] at this
    exact dvd_iff_isRoot.2 (this.trans (ite_eq_right (by omega)))
  rw [← hres]
  refine pow_dvd_resultant_of_dvd_coeff (by simp [G]; omega) (fun l hl ↦ hG l hl.le)
    fun l hl ↦ ?_
  rw [coeff_derivative]
  exact (hG (l + 1) hl).mul_right _

/-- **The resultant multiplicity bound, multiplicity form.** If `Res_z(F, ∂_z F)` is nonzero, the
multiplicity of a root `a` of the fibre `F(·, b)` exceeds the order of vanishing of
`Res_z(F, ∂_z F)` at `z' = b` by at most one. -/
theorem rootMultiplicity_map_sub_one_le_rootMultiplicity_resultant_derivative {F : R[X][X]}
    (hF : resultant F (derivative F) ≠ 0) (a b : R) :
    (F.map (evalRingHom b)).rootMultiplicity a - 1 ≤
      (resultant F (derivative F)).rootMultiplicity b := by
  by_cases h0 : F.map (evalRingHom b) = 0
  · simp [h0]
  rcases Nat.eq_zero_or_pos ((F.map (evalRingHom b)).rootMultiplicity a) with hμ | hμ
  · simp [hμ]
  rw [le_rootMultiplicity_iff hF]
  refine pow_dvd_resultant_derivative (a := a) h0 ?_
  rw [Nat.sub_add_cancel hμ]
  exact pow_rootMultiplicity_dvd _ _

/-- **Degree of a bivariate resultant.** If every coefficient of `F : R[X][X]` has degree at most
`a` and every coefficient of `G` has degree at most `b` in the coefficient variable, then the
resultant `resultant F G m n` has degree at most `m * b + n * a`: the Sylvester matrix has `m`
columns of coefficients of `G` and `n` columns of coefficients of `F`. -/
theorem natDegree_resultant_le {F G : R[X][X]} {a b : ℕ} (hF : ∀ i, (F.coeff i).natDegree ≤ a)
    (hG : ∀ i, (G.coeff i).natDegree ≤ b) (m n : ℕ) :
    (resultant F G m n).natDegree ≤ m * b + n * a := by
  have h := Matrix.natDegree_det_le_of_natDegree_le (sylvester F G m n)
    (fun j ↦ if (j : ℕ) < m then b else a) fun i j ↦ by
      split_ifs with hj
      · rw [sylvester_apply_of_lt _ _ _ _ hj]
        split_ifs <;> simp [hG]
      · rw [sylvester_apply_of_le _ _ _ _ (not_lt.mp hj)]
        split_ifs <;> simp [hF]
  simpa [resultant, Fin.sum_univ_add] using h

/-- **The resultant multiplicity bound.** Let `F : R[X][X]` be a polynomial in `z` over `R[z']`
whose coefficients have degree at most `d` in `z'`, with `Res_z(F, ∂_z F) ≠ 0`. For finitely
many points `(a i, b i)` with pairwise distinct second coordinates, the excess multiplicities
`mult_{a i} F(·, b i) - 1` sum to at most `(2 deg_z F - 1) d`. -/
theorem sum_rootMultiplicity_map_sub_one_le [IsDomain R] {ι : Type*} {s : Finset ι}
    {a b : ι → R} (hb : Set.InjOn b s) {F : R[X][X]} (hF : resultant F (derivative F) ≠ 0)
    {d : ℕ} (hd : ∀ i, (F.coeff i).natDegree ≤ d) :
    ∑ i ∈ s, ((F.map (evalRingHom (b i))).rootMultiplicity (a i) - 1) ≤
      (2 * F.natDegree - 1) * d := by
  classical
  have hd' : ∀ i, ((derivative F).coeff i).natDegree ≤ d := fun i ↦ by
    rw [coeff_derivative]
    exact natDegree_mul_le.trans (by simpa using hd (i + 1))
  calc ∑ i ∈ s, ((F.map (evalRingHom (b i))).rootMultiplicity (a i) - 1)
      ≤ ∑ i ∈ s, (resultant F (derivative F)).rootMultiplicity (b i) := sum_le_sum fun i _ ↦
        rootMultiplicity_map_sub_one_le_rootMultiplicity_resultant_derivative hF _ _
    _ = ∑ x ∈ s.image b, (resultant F (derivative F)).rootMultiplicity x := by
        rw [sum_image hb]
    _ ≤ (resultant F (derivative F)).natDegree := sum_rootMultiplicity_le_natDegree _ _
    _ ≤ F.natDegree * d + (derivative F).natDegree * d := natDegree_resultant_le hd hd' _ _
    _ ≤ (2 * F.natDegree - 1) * d := by
      rw [← add_mul]
      exact Nat.mul_le_mul_right _ (by have := natDegree_derivative_le F; omega)

/-- **The resultant multiplicity bound, counting form.** Under the hypotheses of
`Polynomial.sum_rootMultiplicity_map_sub_one_le`, the multiplicities `mult_{a i} F(·, b i)` sum
to at most the number of the points `(a i, b i)` on the curve `F = 0` plus
`(2 deg_z F - 1) d`. -/
theorem sum_rootMultiplicity_map_le [IsDomain R] [DecidableEq R] {ι : Type*} {s : Finset ι}
    {a b : ι → R} (hb : Set.InjOn b s) {F : R[X][X]} (hF : resultant F (derivative F) ≠ 0)
    {d : ℕ} (hd : ∀ i, (F.coeff i).natDegree ≤ d) :
    ∑ i ∈ s, (F.map (evalRingHom (b i))).rootMultiplicity (a i) ≤
      #{i ∈ s | (F.map (evalRingHom (b i))).IsRoot (a i)} +
        (2 * F.natDegree - 1) * d := by
  calc ∑ i ∈ s, (F.map (evalRingHom (b i))).rootMultiplicity (a i)
      ≤ ∑ i ∈ s, ((if (F.map (evalRingHom (b i))).IsRoot (a i) then 1 else 0) +
          ((F.map (evalRingHom (b i))).rootMultiplicity (a i) - 1)) := sum_le_sum fun i _ ↦ by
        have := (rootMultiplicity_pos' (p := F.map (evalRingHom (b i))) (x := a i)).1
        split_ifs <;> grind
    _ ≤ _ := by
      rw [sum_add_distrib, sum_boole, Nat.cast_id]
      exact Nat.add_le_add_left (sum_rootMultiplicity_map_sub_one_le hb hF hd) _

end Polynomial
