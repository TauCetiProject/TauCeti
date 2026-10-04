/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Matrix.Scaling
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The Sinkhorn–Knopp theorem

Let `K` be a real matrix indexed by finite types `ι` and `κ` with strictly positive entries, and
let `a : ι → ℝ` and `b : κ → ℝ` be strictly positive vectors of equal total mass. The
Sinkhorn–Knopp theorem says that there are strictly positive row factors `u` and column factors
`v` such that the matrix `u i * K i j * v j` has row sums `a` and column sums `b`, and that this
scaled matrix is unique; the factors themselves are unique up to the common rescaling
`IsDiagonalScaling.rescale_factors`.

The existence proof is the entropic one. By `exists_relEntropy_minOn_of_pos` and
`pos_of_relEntropy_minOn`, the relative entropy against `K` has a minimiser `P` among the
nonnegative matrices with the prescribed marginals, and `P` has strictly positive entries. The
minimiser is therefore an interior point of the transport polytope, so the relative entropy has
vanishing derivative along every direction of zero row and column sums. Along the rectangle
directions this says that `log (P i j) - log (K i j)` is the sum of a function of `i` and a
function of `j`, that is `P` is a diagonal scaling of `K`. The same uniqueness then identifies
every positive diagonal scaling of `K` with this minimiser.

## Main results

* `Matrix.exists_isDiagonalScaling_of_relEntropy_minOn`: a strictly positive minimiser of the
  relative entropy against a strictly positive `K`, with prescribed marginals, is a diagonal
  scaling of `K` by strictly positive factors.
* `Matrix.exists_sinkhorn_scaling`: the Sinkhorn–Knopp theorem, existence of strictly positive
  scaling factors.
* `Matrix.IsDiagonalScaling.mul_eq_one_of_hasMarginals`: a positive diagonal scaling of a strictly
  positive matrix that preserves its row and column sums has factors with `x i * y j = 1`.
* `Matrix.IsDiagonalScaling.eq_of_hasMarginals`: two positive diagonal scalings of a strictly
  positive `K` with the same marginals are equal, and
  `Matrix.IsDiagonalScaling.exists_eq_mul_of_hasMarginals`: their factors differ by one common
  positive scalar.
* `Matrix.IsDiagonalScaling.relEntropy_le`: a positive diagonal scaling of a strictly positive `K`
  minimises the relative entropy against `K` among the nonnegative matrices with its marginals.

## References

* R. Sinkhorn, *A relationship between arbitrary positive matrices and doubly stochastic
  matrices*, Ann. Math. Statist. 35 (1964).
* R. Sinkhorn, *Diagonal equivalence to matrices with prescribed row and column sums*,
  Amer. Math. Monthly 74 (1967).
* G. Peyré and M. Cuturi, *Computational Optimal Transport*, Found. Trends Mach. Learn. 11
  (2019), Proposition 4.3.
-/

public section

open scoped BigOperators Topology
open Filter

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! ### Uniqueness of positive diagonal scalings -/

/-- If a strictly positive matrix `P` and its diagonal scaling `Q` by strictly positive factors `x`
and `y` have the same row sums and the same column sums, then `x i * y j = 1` for all `i` and
`j`. -/
theorem IsDiagonalScaling.mul_eq_one_of_hasMarginals {P Q : Matrix ι κ ℝ} {x : ι → ℝ}
    {y : κ → ℝ} (hQ : IsDiagonalScaling Q P x y) (hP : ∀ i j, 0 < P i j) (hx : ∀ i, 0 < x i)
    (hy : ∀ j, 0 < y j) {a : ι → ℝ} {b : κ → ℝ} (hPm : HasMarginals P a b)
    (hQm : HasMarginals Q a b) (i : ι) (j : κ) : x i * y j = 1 := by
  rw [isDiagonalScaling_def] at hQ
  rw [hasMarginals_def] at hPm hQm
  -- Choose `i₀` minimising `x` and `j₀` maximising `y`. Comparing the sums of row `i₀` and of
  -- column `j₀` of `P` and `Q` forces `x i₀ * y j₀ = 1`, and then every term of these two sums,
  -- which all have the same sign, has `x i * y j₀ = 1` and `x i₀ * y j = 1`.
  have : Nonempty ι := ⟨i⟩
  have : Nonempty κ := ⟨j⟩
  obtain ⟨i₀, hi₀⟩ := Finite.exists_min x
  obtain ⟨j₀, hj₀⟩ := Finite.exists_max y
  -- The differences of the row sums and of the column sums of `Q` and `P` vanish.
  have hrow : ∀ i, ∑ j, P i j * (x i * y j - 1) = 0 := fun i => by
    have h : ∑ j, P i j * (x i * y j - 1) = ∑ j, Q i j - ∑ j, P i j := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [hQ i j]; ring
    rw [h, hQm.1 i, hPm.1 i, sub_self]
  have hcol : ∀ j, ∑ i, P i j * (x i * y j - 1) = 0 := fun j => by
    have h : ∑ i, P i j * (x i * y j - 1) = ∑ i, Q i j - ∑ i, P i j := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [hQ i j]; ring
    rw [h, hQm.2 j, hPm.2 j, sub_self]
  have hle_row : ∀ j, x i₀ * y j ≤ x i₀ * y j₀ := fun j =>
    mul_le_mul_of_nonneg_left (hj₀ j) (hx i₀).le
  have hle_col : ∀ i, x i₀ * y j₀ ≤ x i * y j₀ := fun i =>
    mul_le_mul_of_nonneg_right (hi₀ i) (hy j₀).le
  have h₀ : x i₀ * y j₀ = 1 := by
    refine le_antisymm (not_lt.mp fun hlt => ?_) (not_lt.mp fun hlt => ?_)
    · -- Every term of column `j₀` would be positive.
      have : 0 < ∑ i, P i j₀ * (x i * y j₀ - 1) := Finset.sum_pos
        (fun i _ => mul_pos (hP i j₀) (by linarith [hle_col i])) Finset.univ_nonempty
      linarith [hcol j₀]
    · -- Every term of row `i₀` would be negative.
      have : ∑ j, P i₀ j * (x i₀ * y j - 1) < 0 := Finset.sum_neg
        (fun j _ => mul_neg_of_pos_of_neg (hP i₀ j) (by linarith [hle_row j]))
        Finset.univ_nonempty
      linarith [hrow i₀]
  -- The terms of column `j₀` are nonnegative and those of row `i₀` are nonpositive, so they all
  -- vanish.
  have hcol₀ : x i * y j₀ = 1 := by
    have h := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      mul_nonneg (hP i j₀).le (by linarith [hle_col i])).mp (hcol j₀) i (Finset.mem_univ i)
    have := (mul_eq_zero.mp h).resolve_left (hP i j₀).ne'
    linarith
  have hrow₀ : x i₀ * y j = 1 := by
    have h := (Finset.sum_eq_zero_iff_of_nonpos fun j _ =>
      mul_nonpos_of_nonneg_of_nonpos (hP i₀ j).le (by linarith [hle_row j])).mp (hrow i₀) j
        (Finset.mem_univ j)
    have := (mul_eq_zero.mp h).resolve_left (hP i₀ j).ne'
    linarith
  have hxi : x i = x i₀ := mul_right_cancel₀ (hy j₀).ne' (hcol₀.trans h₀.symm)
  rw [hxi, hrow₀]

/-- Two diagonal scalings of a strictly positive matrix `K` by strictly positive factors, with the
same row sums and the same column sums, are equal. -/
theorem IsDiagonalScaling.eq_of_hasMarginals {P P' K : Matrix ι κ ℝ} {u u' : ι → ℝ}
    {v v' : κ → ℝ} (h : IsDiagonalScaling P K u v) (h' : IsDiagonalScaling P' K u' v')
    (hK : ∀ i j, 0 < K i j) (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j) (hu' : ∀ i, 0 < u' i)
    (hv' : ∀ j, 0 < v' j) {a : ι → ℝ} {b : κ → ℝ} (hm : HasMarginals P a b)
    (hm' : HasMarginals P' a b) : P' = P := by
  have hP : ∀ i j, 0 < P i j := fun i j => by
    rw [(isDiagonalScaling_def _ _ _ _).mp h i j]
    exact mul_pos (mul_pos (hu i) (hK i j)) (hv j)
  have hdiv := h.div h' (fun i => (hu i).ne') fun j => (hv j).ne'
  ext i j
  rw [(isDiagonalScaling_def _ _ _ _).mp hdiv i j, mul_right_comm,
    hdiv.mul_eq_one_of_hasMarginals hP (fun i => div_pos (hu' i) (hu i))
      (fun j => div_pos (hv' j) (hv j)) hm hm', one_mul]

/-- The factors of two diagonal scalings of a strictly positive matrix `K` by strictly positive
factors, with the same row sums and the same column sums, differ by one common positive scalar:
this is exactly the ambiguity of `IsDiagonalScaling.rescale_factors`. -/
theorem IsDiagonalScaling.exists_eq_mul_of_hasMarginals [Nonempty ι] [Nonempty κ]
    {P P' K : Matrix ι κ ℝ} {u u' : ι → ℝ} {v v' : κ → ℝ} (h : IsDiagonalScaling P K u v)
    (h' : IsDiagonalScaling P' K u' v') (hK : ∀ i j, 0 < K i j) (hu : ∀ i, 0 < u i)
    (hv : ∀ j, 0 < v j) (hu' : ∀ i, 0 < u' i) (hv' : ∀ j, 0 < v' j) {a : ι → ℝ} {b : κ → ℝ}
    (hm : HasMarginals P a b) (hm' : HasMarginals P' a b) :
    ∃ c : ℝ, 0 < c ∧ (∀ i, u' i = c * u i) ∧ ∀ j, v' j = c⁻¹ * v j := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨j₀⟩ := ‹Nonempty κ›
  have hP : ∀ i j, 0 < P i j := fun i j => by
    rw [(isDiagonalScaling_def _ _ _ _).mp h i j]
    exact mul_pos (mul_pos (hu i) (hK i j)) (hv j)
  have hone := (h.div h' (fun i => (hu i).ne') fun j => (hv j).ne').mul_eq_one_of_hasMarginals
    hP (fun i => div_pos (hu' i) (hu i)) (fun j => div_pos (hv' j) (hv j)) hm hm'
  refine ⟨u' i₀ / u i₀, div_pos (hu' i₀) (hu i₀), fun i => ?_, fun j => ?_⟩
  · -- Both quotients `u' i / u i` and `u' i₀ / u i₀` are inverse to `v' j₀ / v j₀`.
    have h₁ := hone i j₀
    have h₂ := hone i₀ j₀
    have hi : u' i / u i = u' i₀ / u i₀ :=
      mul_right_cancel₀ (div_pos (hv' j₀) (hv j₀)).ne' (h₁.trans h₂.symm)
    rw [← hi]
    field_simp [(hu i).ne']
  · have h₁ := hone i₀ j
    rw [inv_div]
    have hj : v' j / v j = u i₀ / u' i₀ := by
      rw [eq_inv_of_mul_eq_one_right h₁, inv_div]
    rw [← hj]
    field_simp [(hv j).ne']

/-! ### Existence of a positive diagonal scaling -/

/-- At a minimiser `P` with strictly positive entries of the relative entropy against `K`, among
the nonnegative matrices with the marginals of `P`, the derivative along the outer product of two
weights `r` and `c` of total sum `0` vanishes. -/
private theorem sum_mul_mul_log_sub_log_eq_zero {K P : Matrix ι κ ℝ} {a : ι → ℝ} {b : κ → ℝ}
    (hP : ∀ i j, 0 < P i j) (hPa : HasMarginals P a b)
    (hmin : ∀ Q : Matrix ι κ ℝ, (∀ i j, 0 ≤ Q i j) → HasMarginals Q a b →
      relEntropy P K ≤ relEntropy Q K)
    (r : ι → ℝ) (c : κ → ℝ) (hr : ∑ x, r x = 0) (hc : ∑ y, c y = 0) :
    ∑ x, ∑ y, r x * c y * (Real.log (P x y) - Real.log (K x y)) = 0 := by
  set f : ℝ → ℝ := fun t => relEntropy (P + vecMulVec (fun x => t * r x) c) K with hf
  have hf' : f = fun t => ∑ x, ∑ y, ((P x y + t * (r x * c y)) *
      Real.log (P x y + t * (r x * c y)) - (P x y + t * (r x * c y)) * Real.log (K x y)) := by
    funext t
    simp only [hf, relEntropy_def, add_apply, vecMulVec_apply, mul_assoc]
  -- `f` has a local minimum at `0`: near `0` the perturbed matrix is a nonnegative competitor.
  have hloc : IsLocalMin f 0 := by
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ x y, 0 ≤ P x y + t * (r x * c y) := by
      simp only [Filter.eventually_all]
      intro x y
      have ht : Tendsto (fun t : ℝ => P x y + t * (r x * c y)) (𝓝 0) (𝓝 (P x y)) := by
        have hcont : Continuous fun t : ℝ => P x y + t * (r x * c y) := by fun_prop
        simpa using hcont.tendsto 0
      exact (ht.eventually_const_lt (hP x y)).mono fun t ht => ht.le
    filter_upwards [hev] with t ht
    have h0 : f 0 = relEntropy P K := by
      rw [hf', relEntropy_def]
      simp
    rw [h0]
    refine hmin _ (fun x y => ?_) (HasMarginals.add_vecMulVec_of_sum_eq_zero a b P hPa r c hr hc t)
    simpa only [add_apply, vecMulVec_apply, mul_assoc] using ht x y
  have hderiv : HasDerivAt f
      (∑ x, ∑ y, r x * c y * (Real.log (P x y) + 1 - Real.log (K x y))) 0 := by
    rw [hf']
    refine HasDerivAt.fun_sum fun x _ => HasDerivAt.fun_sum fun y _ => ?_
    have hg : HasDerivAt (fun t : ℝ => P x y + t * (r x * c y)) (r x * c y) 0 :=
      (hasDerivAt_mul_const _).const_add _
    have hl : HasDerivAt (fun s : ℝ => s * Real.log s) (Real.log (P x y) + 1)
        (P x y + 0 * (r x * c y)) := by
      simpa using Real.hasDerivAt_mul_log (hP x y).ne'
    refine ((hl.comp 0 hg).sub (hg.mul_const (Real.log (K x y)))).congr_deriv ?_
    ring
  have hzero := hloc.hasDerivAt_eq_zero hderiv
  have hsplit : ∑ x, ∑ y, r x * c y * (Real.log (P x y) + 1 - Real.log (K x y))
      = ∑ x, ∑ y, r x * c y * (Real.log (P x y) - Real.log (K x y))
        + (∑ x, r x) * ∑ y, c y := by
    rw [Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  rwa [hsplit, hr, zero_mul, add_zero] at hzero

/-- A minimiser with strictly positive entries of the relative entropy against a strictly positive
matrix `K`, among the nonnegative matrices with its row and column sums, is a diagonal scaling of
`K` by strictly positive factors. -/
theorem exists_isDiagonalScaling_of_relEntropy_minOn {K P : Matrix ι κ ℝ} {a : ι → ℝ}
    {b : κ → ℝ} (hK : ∀ i j, 0 < K i j) (hP : ∀ i j, 0 < P i j) (hPa : HasMarginals P a b)
    (hmin : ∀ Q : Matrix ι κ ℝ, (∀ i j, 0 ≤ Q i j) → HasMarginals Q a b →
      relEntropy P K ≤ relEntropy Q K) :
    ∃ (u : ι → ℝ) (v : κ → ℝ), (∀ i, 0 < u i) ∧ (∀ j, 0 < v j) ∧ IsDiagonalScaling P K u v := by
  classical
  simp only [isDiagonalScaling_def]
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · exact ⟨fun _ => 1, fun _ => 1, fun _ => one_pos, fun _ => one_pos, fun i => isEmptyElim i⟩
  rcases isEmpty_or_nonempty κ with hκ | ⟨⟨j₀⟩⟩
  · exact ⟨fun _ => 1, fun _ => 1, fun _ => one_pos, fun _ => one_pos, fun _ j => isEmptyElim j⟩
  -- The first-order condition along the rectangle directions makes `log (P i j) - log (K i j)` the
  -- sum of a function of `i` and a function of `j`; their exponentials are the factors.
  set g : ι → κ → ℝ := fun x y => Real.log (P x y) - Real.log (K x y) with hg
  -- The double sum of a function against the outer product of two differences of sparse vectors.
  have hsum : ∀ (h : ι → κ → ℝ) (i : ι) (j : κ),
      ∑ x, ∑ y, (Pi.single i 1 - Pi.single i₀ 1 : ι → ℝ) x *
        (Pi.single j 1 - Pi.single j₀ 1 : κ → ℝ) y * h x y = h i j - h i j₀ - h i₀ j + h i₀ j₀ := by
    intro h i j
    simp only [Pi.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib, Pi.single_apply, ite_mul,
      one_mul, zero_mul, mul_ite, mul_one, mul_zero]
    simp
    ring
  -- The first-order condition along the rectangle with corners `(i, j)` and `(i₀, j₀)`.
  have hrect : ∀ i j, g i j = g i j₀ + g i₀ j - g i₀ j₀ := fun i j => by
    have h := sum_mul_mul_log_sub_log_eq_zero hP hPa hmin
      (Pi.single i 1 - Pi.single i₀ 1) (Pi.single j 1 - Pi.single j₀ 1)
      (by simp [Finset.sum_sub_distrib]) (by simp [Finset.sum_sub_distrib])
    rw [hsum g i j] at h
    linarith
  refine ⟨fun i => Real.exp (g i j₀), fun j => Real.exp (g i₀ j - g i₀ j₀),
    fun i => Real.exp_pos _, fun j => Real.exp_pos _, fun i j => ?_⟩
  have hPK : P i j = Real.exp (g i j + Real.log (K i j)) := by
    rw [hg, sub_add_cancel, Real.exp_log (hP i j)]
  rw [hPK, hrect i j, show g i j₀ + g i₀ j - g i₀ j₀ + Real.log (K i j)
      = g i j₀ + Real.log (K i j) + (g i₀ j - g i₀ j₀) by ring,
    Real.exp_add, Real.exp_add, Real.exp_log (hK i j)]

/-- **The Sinkhorn–Knopp theorem.** A strictly positive matrix `K` and strictly positive vectors
`a` and `b` of equal total mass admit strictly positive row factors `u` and column factors `v` for
which the scaled matrix `u i * K i j * v j` has row sums `a` and column sums `b`.

The scaled matrix is unique, by `IsDiagonalScaling.eq_of_hasMarginals`, and the factors are unique
up to one common positive scalar, by `IsDiagonalScaling.exists_eq_mul_of_hasMarginals`. -/
theorem exists_sinkhorn_scaling (K : Matrix ι κ ℝ) (a : ι → ℝ) (b : κ → ℝ)
    (hK : ∀ i j, 0 < K i j) (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (hmass : ∑ i, a i = ∑ j, b j) :
    ∃ (u : ι → ℝ) (v : κ → ℝ), (∀ i, 0 < u i) ∧ (∀ j, 0 < v j) ∧
      (∀ i, ∑ j, u i * K i j * v j = a i) ∧ ∀ j, ∑ i, u i * K i j * v j = b j := by
  obtain ⟨P, hP0, hPa, hmin⟩ := exists_relEntropy_minOn_of_pos K a b ha hb hmass
  have hP := pos_of_relEntropy_minOn K a b ha hb hP0 hPa hmin
  obtain ⟨u, v, hu, hv, huv⟩ := exists_isDiagonalScaling_of_relEntropy_minOn hK hP hPa hmin
  rw [isDiagonalScaling_def] at huv
  rw [hasMarginals_def] at hPa
  refine ⟨u, v, hu, hv, fun i => ?_, fun j => ?_⟩
  · simpa only [huv] using hPa.1 i
  · simpa only [huv] using hPa.2 j

/-- A diagonal scaling of a strictly positive matrix `K` by strictly positive factors minimises the
relative entropy against `K` among the nonnegative matrices with its row and column sums: the
diagonal scaling of `K` with prescribed marginals is the entropic projection of `K` onto the
matrices with those marginals. -/
theorem IsDiagonalScaling.relEntropy_le {P K : Matrix ι κ ℝ} {u : ι → ℝ} {v : κ → ℝ}
    (h : IsDiagonalScaling P K u v) (hK : ∀ i j, 0 < K i j) (hu : ∀ i, 0 < u i)
    (hv : ∀ j, 0 < v j) {a : ι → ℝ} {b : κ → ℝ} (hm : HasMarginals P a b) {Q : Matrix ι κ ℝ}
    (hQ : ∀ i j, 0 ≤ Q i j) (hQm : HasMarginals Q a b) : relEntropy P K ≤ relEntropy Q K := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [Subsingleton.elim Q P]
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · rw [Subsingleton.elim Q P]
  have hP : ∀ i j, 0 < P i j := fun i j => by
    rw [(isDiagonalScaling_def _ _ _ _).mp h i j]
    exact mul_pos (mul_pos (hu i) (hK i j)) (hv j)
  have ha : ∀ i, 0 < a i := fun i => by
    rw [← ((hasMarginals_def _ _ _).mp hm).1 i]
    exact Finset.sum_pos (fun j _ => hP i j) Finset.univ_nonempty
  have hb : ∀ j, 0 < b j := fun j => by
    rw [← ((hasMarginals_def _ _ _).mp hm).2 j]
    exact Finset.sum_pos (fun i _ => hP i j) Finset.univ_nonempty
  -- The minimiser of the relative entropy is a positive diagonal scaling of `K`, hence is `P`.
  obtain ⟨P₀, hP₀0, hP₀m, hmin⟩ :=
    exists_relEntropy_minOn K a b ⟨P, fun i j => (hP i j).le, hm⟩
  have hP₀ := pos_of_relEntropy_minOn K a b ha hb hP₀0 hP₀m hmin
  obtain ⟨u₀, v₀, hu₀, hv₀, h₀⟩ := exists_isDiagonalScaling_of_relEntropy_minOn hK hP₀ hP₀m hmin
  rw [← h.eq_of_hasMarginals h₀ hK hu hv hu₀ hv₀ hm hP₀m]
  exact hmin Q hQ hQm

end Matrix
