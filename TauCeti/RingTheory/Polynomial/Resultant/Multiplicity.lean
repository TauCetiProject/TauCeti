/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import TauCeti.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import TauCeti.Algebra.Polynomial.Bivariate
import TauCeti.Algebra.Polynomial.Bivariate.SchwartzZippel
import TauCeti.LinearAlgebra.Matrix.Determinant.IdealDivisibility
import TauCeti.LinearAlgebra.Matrix.Polynomial
import TauCeti.RingTheory.Polynomial.Resultant.Basic
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

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
Proposition 4.1 and Appendix A): it controls how often an irreducible curve can vanish to high
order in `z` at the points of a grid.

The underlying general fact is that the Sylvester matrix has `k` rows divisible by `t` as soon as
the coefficients of index below `k` of both polynomials are divisible by `t`; translating the root
to the origin (`Polynomial.resultant_taylor`) puts us in this situation with `t = X - C b`.

Over a characteristic-zero field `K`, unique factorization in `K[X][X]` combines this resultant
bound with a point-set zero bound to estimate high-order vanishing along fibers with distinct
base coordinates (`Polynomial.card_mul_le_of_pow_dvd_map_evalRingHom`), together with its
specialization to planar grids via the Schwartz–Zippel lemma
(`Polynomial.eq_zero_of_pow_dvd_map_evalRingHom_of_lt_card_cube`).

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
* `Polynomial.sum_cappedRootMultiplicity_map_evalRingHom_le`,
  `Polynomial.card_mul_le_of_pow_dvd_map_evalRingHom`: summed capped bivariate multiplicity
  bound along fibers with injective base coordinates, and its uniform-order specialization.
* `Polynomial.eq_zero_of_pow_dvd_map_evalRingHom_of_lt_card_cube`: vanishing criterion on
  planar grids under an invertible linear or affine change of coordinates.
-/

public section

open Finset

namespace Polynomial

section

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

end

section BivariateMultiplicityBound

/-- The fiber root multiplicity of `P : R[X][X]` at `(α, β)`, capped at `N` (equal to `N` when the
fiber polynomial `P.map (evalRingHom β)` vanishes identically). -/
private noncomputable def cappedFiberMult {R : Type*} [CommRing R] (α β : R)
    (N : ℕ) (P : R[X][X]) : ℕ :=
  (P.map (evalRingHom β)).cappedRootMultiplicity α N

private theorem cappedFiberMult_of_isUnit {R : Type*} [CommRing R] [IsDomain R] (α β : R)
    (N : ℕ) {u : R[X][X]} (hu : IsUnit u) : cappedFiberMult α β N u = 0 :=
  cappedRootMultiplicity_of_isUnit (hu.map (mapRingHom (evalRingHom β))) α N

private theorem cappedFiberMult_mul_le {R : Type*} [CommRing R] [IsDomain R] (α β : R) (N : ℕ)
    (A B : R[X][X]) :
    cappedFiberMult α β N (A * B) ≤ cappedFiberMult α β N A + cappedFiberMult α β N B := by
  rw [cappedFiberMult, Polynomial.map_mul]
  exact cappedRootMultiplicity_mul_le _ _ α N

/-- The bivariate multiplicity bound for an outer-constant polynomial `C q` (`q ≠ 0`). -/
private theorem sum_cappedFiberMult_C_le {K ι : Type*} [Field K] [Fintype ι]
    {α β : ι → K} (hβ : Function.Injective β) (N : ℕ) {q : K[X]} (hq : q ≠ 0) :
    ∑ i : ι, cappedFiberMult (α i) (β i) N (C q) ≤
      N * ((C q : K[X][X]).natDegree + (Bivariate.swap (C q : K[X][X])).natDegree) +
        2 * (C q : K[X][X]).natDegree * (Bivariate.swap (C q : K[X][X])).natDegree := by
  classical
  have hswap : (Bivariate.swap (C q : K[X][X])).natDegree = q.natDegree := by
    rw [Bivariate.swap_C, natDegree_map_eq_of_injective C_injective]
  let Z := Finset.univ.filter fun i : ι ↦ q.eval (β i) = 0
  have hterm (i : ι) : cappedFiberMult (α i) (β i) N (C q) = if i ∈ Z then N else 0 := by
    by_cases h0 : q.eval (β i) = 0
    · simp [cappedFiberMult, Z, h0]
    · simp [cappedFiberMult, Z, h0]
  have hZ : Z.card ≤ q.natDegree := by
    calc Z.card = ∑ i ∈ Z, 1 := by simp
      _ ≤ ∑ i ∈ Z, q.rootMultiplicity (β i) := Finset.sum_le_sum fun i hi ↦
          Nat.succ_le_of_lt ((rootMultiplicity_pos hq).mpr (Finset.mem_filter.mp hi).2)
      _ ≤ q.natDegree := q.sum_rootMultiplicity_comp_le_natDegree Z hβ.injOn
  calc ∑ i : ι, cappedFiberMult (α i) (β i) N (C q)
      = ∑ i : ι, if i ∈ Z then N else 0 := Finset.sum_congr rfl fun i _ ↦ hterm i
    _ = N * Z.card := by rw [Fintype.sum_ite_mem]; simp [mul_comm]
    _ ≤ N * q.natDegree := Nat.mul_le_mul_left N hZ
    _ = N * ((C q : K[X][X]).natDegree + (Bivariate.swap (C q : K[X][X])).natDegree) +
          2 * (C q : K[X][X]).natDegree * (Bivariate.swap (C q : K[X][X])).natDegree := by
        rw [natDegree_C, hswap]
        ring

/-- The bivariate multiplicity bound on a single irreducible factor `Q : K[X][X]`. -/
private theorem sum_cappedFiberMult_le_of_irreducible {K ι : Type*} [Field K] [CharZero K]
    [DecidableEq K] [Fintype ι] {α β : ι → K} (hβ : Function.Injective β) {N : ℕ}
    (hzero : ∀ H : K[X][X], H ≠ 0 →
      #{i : ι | (H.map (evalRingHom (β i))).eval (α i) = 0} ≤
        N * (H.natDegree + (Bivariate.swap H).natDegree))
    {Q : K[X][X]} (hQ : Irreducible Q) :
    ∑ i : ι, cappedFiberMult (α i) (β i) N Q ≤
      N * (Q.natDegree + (Bivariate.swap Q).natDegree) +
        2 * Q.natDegree * (Bivariate.swap Q).natDegree := by
  classical
  rcases Nat.eq_zero_or_pos Q.natDegree with hdeg0 | hdeg
  · obtain ⟨q, rfl⟩ := natDegree_eq_zero.mp hdeg0
    exact sum_cappedFiberMult_C_le hβ N (fun h ↦ hQ.ne_zero (by simp [h]))
  · let Z := Finset.univ.filter fun i : ι ↦ (Q.map (evalRingHom (β i))).eval (α i) = 0
    have hne (i : ι) : Q.map (evalRingHom (β i)) ≠ 0 := hQ.map_evalRingHom_ne_zero hdeg _
    have hout (i : ι) (hi : i ∉ Z) : cappedFiberMult (α i) (β i) N Q = 0 :=
      cappedRootMultiplicity_eq_zero_of_not_isRoot (by simpa [Z, IsRoot.def] using hi) N
    have hin (i : ι) :
        cappedFiberMult (α i) (β i) N Q ≤ (Q.map (evalRingHom (β i))).rootMultiplicity (α i) := by
      rw [cappedFiberMult, cappedRootMultiplicity_of_ne_zero (hne i)]
      exact min_le_right _ _
    have hsum := sum_rootMultiplicity_map_le (s := Z) (a := α) (b := β) hβ.injOn
      hQ.squarefree.resultant_derivative_ne_zero (Bivariate.natDegree_coeff_le_natDegree_swap Q)
    have hZ_roots :
        #{i ∈ Z | (Q.map (evalRingHom (β i))).IsRoot (α i)} ≤
          N * (Q.natDegree + (Bivariate.swap Q).natDegree) :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans (hzero Q hQ.ne_zero)
    have hdeg_mul : (2 * Q.natDegree - 1) * (Bivariate.swap Q).natDegree ≤
        2 * Q.natDegree * (Bivariate.swap Q).natDegree :=
      Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    calc ∑ i : ι, cappedFiberMult (α i) (β i) N Q
        = ∑ i ∈ Z, cappedFiberMult (α i) (β i) N Q :=
          (Finset.sum_subset (Finset.subset_univ Z) fun i _ hi ↦ hout i hi).symm
      _ ≤ ∑ i ∈ Z, (Q.map (evalRingHom (β i))).rootMultiplicity (α i) :=
          Finset.sum_le_sum fun i _ ↦ hin i
      _ ≤ #{i ∈ Z | (Q.map (evalRingHom (β i))).IsRoot (α i)} +
            (2 * Q.natDegree - 1) * (Bivariate.swap Q).natDegree := hsum
      _ ≤ N * (Q.natDegree + (Bivariate.swap Q).natDegree) +
            2 * Q.natDegree * (Bivariate.swap Q).natDegree := add_le_add hZ_roots hdeg_mul

/-- Private form of `sum_cappedRootMultiplicity_map_evalRingHom_le` phrased via `cappedFiberMult`
for prime-factorization induction with an explicit nonzero premise. -/
private theorem sum_cappedFiberMult_le {K ι : Type*} [Field K] [CharZero K]
    [DecidableEq K] [Fintype ι] {α β : ι → K} (hβ : Function.Injective β) {N : ℕ}
    (hzero : ∀ H : K[X][X], H ≠ 0 →
      #{i : ι | (H.map (evalRingHom (β i))).eval (α i) = 0} ≤
        N * (H.natDegree + (Bivariate.swap H).natDegree))
    (F : K[X][X]) :
    F ≠ 0 →
      ∑ i : ι, cappedFiberMult (α i) (β i) N F ≤
        N * (F.natDegree + (Bivariate.swap F).natDegree) +
          2 * F.natDegree * (Bivariate.swap F).natDegree := by
  refine UniqueFactorizationMonoid.induction_on_prime
    (P := fun P ↦ P ≠ 0 →
      ∑ i : ι, cappedFiberMult (α i) (β i) N P ≤
        N * (P.natDegree + (Bivariate.swap P).natDegree) +
          2 * P.natDegree * (Bivariate.swap P).natDegree)
    F (fun h ↦ absurd rfl h) (fun u hu _ ↦ ?_) (fun a p ha0 hp ih _ ↦ ?_)
  · simp [cappedFiberMult_of_isUnit _ _ N hu]
  · have hp0 : p ≠ 0 := hp.ne_zero
    have hdeg_z : (p * a).natDegree = p.natDegree + a.natDegree := natDegree_mul hp0 ha0
    have hswap_a : Bivariate.swap a ≠ 0 := (map_ne_zero_iff _ Bivariate.swap.injective).mpr ha0
    have hswap_p : Bivariate.swap p ≠ 0 := (map_ne_zero_iff _ Bivariate.swap.injective).mpr hp0
    have hdeg_y : (Bivariate.swap (p * a)).natDegree =
        (Bivariate.swap p).natDegree + (Bivariate.swap a).natDegree := by
      rw [map_mul, natDegree_mul hswap_p hswap_a]
    have hp_bound := sum_cappedFiberMult_le_of_irreducible hβ hzero hp.irreducible
    have ha_bound := ih ha0
    calc ∑ i : ι, cappedFiberMult (α i) (β i) N (p * a)
        ≤ ∑ i : ι, (cappedFiberMult (α i) (β i) N p + cappedFiberMult (α i) (β i) N a) :=
          Finset.sum_le_sum fun i _ ↦ cappedFiberMult_mul_le (α i) (β i) N p a
      _ = (∑ i : ι, cappedFiberMult (α i) (β i) N p) +
            ∑ i : ι, cappedFiberMult (α i) (β i) N a := Finset.sum_add_distrib
      _ ≤ N * ((p * a).natDegree + (Bivariate.swap (p * a)).natDegree) +
            2 * (p * a).natDegree * (Bivariate.swap (p * a)).natDegree := by
          rw [hdeg_z, hdeg_y]
          nlinarith

/-- **Summed capped fiber multiplicity bound** (Green, Proposition 4.1). Let `(α i, β i)` be a
finite family of points in `K × K` over a characteristic-zero field `K`, with `β` injective, such
that every nonzero bivariate polynomial `H : K[X][X]` vanishes at no more than
`N * (H.natDegree + (Bivariate.swap H).natDegree)` of the points. Then for every nonzero
`F : K[X][X]`,
`∑ i : ι, (F.map (evalRingHom (β i))).cappedRootMultiplicity (α i) N ≤
  N * (F.natDegree + (Bivariate.swap F).natDegree) +
    2 * F.natDegree * (Bivariate.swap F).natDegree`. -/
theorem sum_cappedRootMultiplicity_map_evalRingHom_le {K ι : Type*} [Field K] [CharZero K]
    [DecidableEq K] [Fintype ι] {α β : ι → K} (hβ : Function.Injective β) {N : ℕ}
    (hzero : ∀ H : K[X][X], H ≠ 0 →
      #{i : ι | (H.map (evalRingHom (β i))).eval (α i) = 0} ≤
        N * (H.natDegree + (Bivariate.swap H).natDegree))
    {F : K[X][X]} (hF : F ≠ 0) :
    ∑ i : ι, (F.map (evalRingHom (β i))).cappedRootMultiplicity (α i) N ≤
      N * (F.natDegree + (Bivariate.swap F).natDegree) +
        2 * F.natDegree * (Bivariate.swap F).natDegree := by
  simpa only [cappedFiberMult] using sum_cappedFiberMult_le hβ hzero F hF

/-- **Bivariate multiplicity estimate** (Green, Proposition 4.1). Let `(α i, β i)` be a finite
family of points in `K × K` over a characteristic-zero field `K`, with `β` injective, such that
every nonzero bivariate polynomial `H : K[X][X]` vanishes at no more than
`N * (H.natDegree + (Bivariate.swap H).natDegree)` of the points. If `F ≠ 0` vanishes to order at
least `N` in the outer coordinate along every fiber `X = β i`, then
`Fintype.card ι * N ≤ N * (F.natDegree + (Bivariate.swap F).natDegree) +
  2 * F.natDegree * (Bivariate.swap F).natDegree`. -/
theorem card_mul_le_of_pow_dvd_map_evalRingHom {K ι : Type*} [Field K] [CharZero K]
    [DecidableEq K] [Fintype ι] {α β : ι → K} (hβ : Function.Injective β) {N : ℕ}
    (hzero : ∀ H : K[X][X], H ≠ 0 →
      #{i : ι | (H.map (evalRingHom (β i))).eval (α i) = 0} ≤
        N * (H.natDegree + (Bivariate.swap H).natDegree))
    {F : K[X][X]} (hF : F ≠ 0)
    (hmult : ∀ i : ι, (X - C (α i)) ^ N ∣ F.map (evalRingHom (β i))) :
    Fintype.card ι * N ≤
      N * (F.natDegree + (Bivariate.swap F).natDegree) +
        2 * F.natDegree * (Bivariate.swap F).natDegree := by
  have hsum_F : Fintype.card ι * N =
      ∑ i : ι, (F.map (evalRingHom (β i))).cappedRootMultiplicity (α i) N := by
    have hpt (i : ι) : (F.map (evalRingHom (β i))).cappedRootMultiplicity (α i) N = N :=
      cappedRootMultiplicity_eq_self_iff.mpr (hmult i)
    simp [hpt]
  rw [hsum_F]
  exact sum_cappedRootMultiplicity_map_evalRingHom_le hβ hzero hF

/-- **Planar grid vanishing criterion.** Let `S` be a finite subset of a characteristic-zero field
`K`, and let `L₁, L₂ : MvPolynomial (Fin 2) K` have total degree at most `1` such that substitution
`aevalAeval L₂ L₁ : K[X][X] →ₐ[K] MvPolynomial (Fin 2) K` is injective and `L₂` takes distinct
values on `S ×ˢ S`. If `F : K[X][X]` vanishes to order at least `#S` in the outer coordinate at
`(L₁(x, y), L₂(x, y))` for all `x, y ∈ S`, and
`#S * (F.natDegree + (Bivariate.swap F).natDegree) +
  2 * F.natDegree * (Bivariate.swap F).natDegree < #S ^ 3`, then `F = 0`. -/
theorem eq_zero_of_pow_dvd_map_evalRingHom_of_lt_card_cube {K : Type*} [Field K] [CharZero K]
    (S : Finset K) {L₁ L₂ : MvPolynomial (Fin 2) K}
    (hL₁ : L₁.totalDegree ≤ 1) (hL₂ : L₂.totalDegree ≤ 1)
    (hinj_hom : Function.Injective (aevalAeval L₂ L₁ : K[X][X] →ₐ[K] MvPolynomial (Fin 2) K))
    (hinj_β : ∀ x₁ ∈ S, ∀ y₁ ∈ S, ∀ x₂ ∈ S, ∀ y₂ ∈ S,
      MvPolynomial.eval ![x₁, y₁] L₂ = MvPolynomial.eval ![x₂, y₂] L₂ → x₁ = x₂ ∧ y₁ = y₂)
    {F : K[X][X]}
    (hmult : ∀ x ∈ S, ∀ y ∈ S,
      (X - C (MvPolynomial.eval ![x, y] L₁)) ^ S.card ∣
        F.map (evalRingHom (MvPolynomial.eval ![x, y] L₂)))
    (hdeg : S.card * (F.natDegree + (Bivariate.swap F).natDegree) +
      2 * F.natDegree * (Bivariate.swap F).natDegree < S.card ^ 3) :
    F = 0 := by
  classical
  by_contra hF
  let α : ↥S × ↥S → K := fun p ↦ MvPolynomial.eval ![p.1.val, p.2.val] L₁
  let β : ↥S × ↥S → K := fun p ↦ MvPolynomial.eval ![p.1.val, p.2.val] L₂
  have hβ : Function.Injective β := fun p q hpq ↦ by
    obtain ⟨hx, hy⟩ :=
      hinj_β p.1.val p.1.property p.2.val p.2.property q.1.val q.1.property q.2.val q.2.property hpq
    exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)
  have hzero (H : K[X][X]) (hH : H ≠ 0) :
      #{p : ↥S × ↥S | (H.map (evalRingHom (β p))).eval (α p) = 0} ≤
        S.card * (H.natDegree + (Bivariate.swap H).natDegree) :=
    card_grid_eval_eq_zero_le hL₁ hL₂ hinj_hom hH
  have hbound := card_mul_le_of_pow_dvd_map_evalRingHom hβ hzero hF
    (fun p ↦ hmult p.1.val p.1.property p.2.val p.2.property)
  have hcard : Fintype.card (↥S × ↥S) * S.card = S.card ^ 3 := by
    simp only [Fintype.card_prod, Fintype.card_coe]
    ring
  omega

end BivariateMultiplicityBound

end Polynomial
