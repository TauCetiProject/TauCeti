/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.SetTheory.Cardinal.ENat
public import TauCeti.RingTheory.MvPolynomial.Dehomogenization

/-!
# Polynomials in two variables

For `φ : MvPolynomial (Fin 2) R` the monomial with exponent `s : Fin 2 →₀ ℕ` is
`X₀ ^ s 0 * X₁ ^ s 1`, of degree `s 0 + s 1`.  This file records the evaluation of `φ` at a pair
`(a, b)` as a sum over these monomials, and the description of the total degree of `φ` as the
largest `s 0 + s 1` over its support.  These are the forms in which a plane curve equation
`φ(x, y) = 0` of degree `n` is manipulated term by term.

## Main results

* `MvPolynomial.aeval_fin_two_eq_sum`: `φ(a, b) = ∑ₛ cₛ a ^ s 0 b ^ s 1`.
* `MvPolynomial.aeval_monomial_fin_two`: the monomial `c X₀ ^ s 0 X₁ ^ s 1` evaluates at `(a, b)`
  to `c a ^ s 0 b ^ s 1`.
* `MvPolynomial.add_le_totalDegree_of_mem_support`: every monomial of `φ` has degree at most the
  total degree of `φ`.
* `MvPolynomial.exists_mem_support_add_eq_totalDegree`: a nonzero `φ` has a monomial of degree
  exactly its total degree.
* `MvPolynomial.eq_single_one_of_mem_support`: if `φ` has total degree at most `n`, its only
  possible monomial with exponent `n` in `X₁` is `X₁ ^ n`.
* `MvPolynomial.totalDegree_pos_of_aeval_eq_zero`: if the coefficient of `X₁ ^ n` in `φ` is `1`,
  where `n` is the total degree of `φ`, and `φ` has a zero, then `n` is positive.
* `MvPolynomial.exists_sum_coeff_mul_pow_ne_zero`: over a domain with more than `deg φ` elements,
  the leading form `φ_n` of `φ` satisfies `φ_n(c, 1) ≠ 0` for some `c`.
* `MvPolynomial.natDegree_minpoly_le_totalDegree`: if `φ(u + c y, y) = 0` with `u ∈ K` and
  `φ_n(c, 1) ≠ 0`, then `y` has degree at most `deg φ` over `K`.
* `Polynomial.Bivariate.aeval_equivMvPolynomial`: evaluating `p ∈ R[X][Y]` at `y` over an
  `R[X]`-algebra is evaluating the corresponding `φ ∈ R[X₀, X₁]` at `(X, y)`; this reads a plane
  curve equation `φ` as a polynomial in `X₁` over `R[X₀]`.
* `Polynomial.Bivariate.aeval_map_eq_aeval_equivMvPolynomial`: the same, after mapping `p` to
  `K[Y]` for an `R[X]`-algebra `K`.
* `Polynomial.Bivariate.monic_equivMvPolynomial_symm` and
  `Polynomial.Bivariate.natDegree_equivMvPolynomial_symm`: if `φ` has total degree at most `n` and
  the coefficient of `X₁ ^ n` is `1`, then `φ`, read as a polynomial in `X₁` over `R[X₀]`, is monic
  of degree `n`.
* `Polynomial.Bivariate.isAlgebraic_of_aeval_algebraMap_eq_zero`: if `φ(a, T) ≠ 0` and
  `φ(a, y) = 0` for a constant `a ∈ k`, then `y` is algebraic over `k`.

## The chart at infinity

For `n` at least the total degree of `φ`, the degree-`n` homogenization of `φ` is
`Φ(X₀, X₁, X₂) = ∑ₛ cₛ X₀ ^ s 0 X₁ ^ s 1 X₂ ^ (n - s 0 - s 1)`, and `φ = Φ(X₀, X₁, 1)`.  In the
affine chart where the first homogeneous coordinate does not vanish, with coordinates
`(X₂ / X₀, X₁ / X₀)`, the equation `Φ = 0` reads `MvPolynomial.inftyChart n φ = Φ(1, X₁, X₀)`,
that is `X₀ ^ n φ(1 / X₀, X₁ / X₀)`.  When `n` is the total degree of `φ`, `Φ = 0` is the
projective closure of the curve `φ = 0`; for larger `n` it also contains the line at infinity
`X₂ = 0`.  In the case `n = φ.totalDegree`, this chart contains the points at infinity of
`φ = 0` other than `(0 : 1 : 0)`, and when the coefficient of `X₁ ^ n` is nonzero that point is
not on the curve.

* `MvPolynomial.coeff_inftyChart` and `MvPolynomial.inftyChart_monomial`: the coefficients of
  the chart equation.
* `MvPolynomial.inftyChart_dehomogenize`: for `G` homogeneous of degree `n` in three variables,
  the chart at infinity of the affine equation `TauCeti.dehomogenize 2 G` is the dehomogenization
  `TauCeti.dehomogenize 0 G` with its two coordinates swapped.
* `MvPolynomial.aeval_inftyChart`: `ψ(x⁻¹, y x⁻¹) = x⁻ⁿ φ(x, y)` for `ψ = inftyChart n φ`.
* `MvPolynomial.aeval_pderiv_one_inftyChart`: `∂ψ/∂X₁ (x⁻¹, y x⁻¹) = x^(1 - n) ∂φ/∂X₁ (x, y)`.
* `MvPolynomial.totalDegree_inftyChart_le` and `MvPolynomial.coeff_single_one_inftyChart`: the
  chart equation again has total degree at most `n`, with the same coefficient of `X₁ ^ n`.
-/

public section

namespace MvPolynomial

variable {R : Type*} [CommSemiring R]

/-- A polynomial in two variables evaluated at `(a, b)` is the sum of its terms
`c_s a ^ s 0 b ^ s 1`. -/
theorem aeval_fin_two_eq_sum {A : Type*} [CommSemiring A] [Algebra R A]
    (φ : MvPolynomial (Fin 2) R) (a b : A) :
    aeval ![a, b] φ = ∑ s ∈ φ.support, algebraMap R A (φ.coeff s) * (a ^ s 0 * b ^ s 1) := by
  rw [aeval_def, eval₂_eq']
  simp [Fin.prod_univ_two]

/-- Evaluating the monomial `c X₀ ^ s 0 X₁ ^ s 1` at `(a, b)` gives `c a ^ s 0 b ^ s 1`. -/
theorem aeval_monomial_fin_two {A : Type*} [CommSemiring A] [Algebra R A] (a b : A)
    (s : Fin 2 →₀ ℕ) (c : R) :
    aeval ![a, b] (monomial s c) = algebraMap R A c * (a ^ s 0 * b ^ s 1) := by
  rw [aeval_monomial, Finsupp.prod_fintype _ _ fun _ => pow_zero _, Fin.prod_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero]

/-- Every monomial of a polynomial in two variables has degree at most its total degree. -/
theorem add_le_totalDegree_of_mem_support {φ : MvPolynomial (Fin 2) R} {s : Fin 2 →₀ ℕ}
    (hs : s ∈ φ.support) : s 0 + s 1 ≤ φ.totalDegree := by
  simpa [Finsupp.sum_fintype, Fin.sum_univ_two] using le_totalDegree hs

/-- A nonzero polynomial in two variables has a monomial whose degree is its total degree. -/
theorem exists_mem_support_add_eq_totalDegree {φ : MvPolynomial (Fin 2) R} (hφ : φ ≠ 0) :
    ∃ s ∈ φ.support, s 0 + s 1 = φ.totalDegree := by
  obtain ⟨s, hs, hsup⟩ := Finset.exists_mem_eq_sup φ.support
    (Finset.nonempty_iff_ne_empty.mpr (mt support_eq_empty.mp hφ)) fun s ↦ s.sum fun _ e ↦ e
  exact ⟨s, hs, by simpa [totalDegree, Finsupp.sum_fintype, Fin.sum_univ_two] using hsup.symm⟩

/-- A monomial of a polynomial in two variables of total degree at most `n` whose exponent of
`X₁` is `n` is `X₁ ^ n`. -/
theorem eq_single_one_of_mem_support {φ : MvPolynomial (Fin 2) R} {n : ℕ}
    (hφ : φ.totalDegree ≤ n) {s : Fin 2 →₀ ℕ} (hs : s ∈ φ.support) (h1 : s 1 = n) :
    s = Finsupp.single 1 n := by
  have := (add_le_totalDegree_of_mem_support hs).trans hφ
  ext i
  fin_cases i <;> simp <;> omega

/-- If the coefficient of `X₁ ^ n` in a polynomial in two variables of total degree `n` is `1`,
and the polynomial has a zero, then `n` is positive. -/
theorem totalDegree_pos_of_aeval_eq_zero {φ : MvPolynomial (Fin 2) R}
    (hc : φ.coeff (Finsupp.single 1 φ.totalDegree) = 1) {A : Type*} [CommSemiring A]
    [Nontrivial A] [Algebra R A] {v : Fin 2 → A} (hv : aeval v φ = 0) : 0 < φ.totalDegree := by
  refine Nat.pos_of_ne_zero fun h0 ↦ one_ne_zero (α := A) ?_
  rw [h0, Finsupp.single_zero] at hc
  rw [← hv, totalDegree_eq_zero_iff_eq_C.mp h0, hc, map_one, map_one]

/-! ### The chart at infinity -/

/-- **The equation of a plane curve in the chart at infinity**: for `φ = ∑ₛ cₛ X₀ ^ s 0 X₁ ^ s 1`,
`inftyChart n φ = ∑ₛ cₛ X₀ ^ (n - s 0 - s 1) X₁ ^ s 1`, which is `X₀ ^ n φ(1 / X₀, X₁ / X₀)` when
`n` is at least the total degree of `φ`.  It is the degree-`n` homogenization of `φ`,
dehomogenized in the affine chart where the first homogeneous coordinate does not vanish; when
`n = φ.totalDegree` this is the equation of the projective closure of `φ = 0` in that chart. -/
noncomputable def inftyChart (n : ℕ) (φ : MvPolynomial (Fin 2) R) : MvPolynomial (Fin 2) R :=
  ∑ s ∈ φ.support, monomial (Finsupp.single 0 (n - (s 0 + s 1)) + Finsupp.single 1 (s 1))
    (φ.coeff s)

/-- Passing to the chart at infinity is additive. -/
theorem inftyChart_add (n : ℕ) (φ ψ : MvPolynomial (Fin 2) R) :
    inftyChart n (φ + ψ) = inftyChart n φ + inftyChart n ψ :=
  Finsupp.sum_add_index' (fun _ ↦ by simp) (fun _ _ _ ↦ by simp)

/-- The chart equation at infinity of the monomial `c X₀ ^ s 0 X₁ ^ s 1` is
`c X₀ ^ (n - s 0 - s 1) X₁ ^ s 1`. -/
@[simp]
theorem inftyChart_monomial (n : ℕ) (s : Fin 2 →₀ ℕ) (c : R) :
    inftyChart n (monomial s c) =
      monomial (Finsupp.single 0 (n - (s 0 + s 1)) + Finsupp.single 1 (s 1)) c := by
  classical
  by_cases hc : c = 0
  · simp [hc, inftyChart]
  · simp [inftyChart, support_monomial, hc]

/-- **The coefficients of the chart equation at infinity**: for `φ` of total degree at most `n`,
the coefficient of `X₀ ^ a X₁ ^ b` in `inftyChart n φ` is the coefficient of
`X₀ ^ (n - a - b) X₁ ^ b` in `φ` if `a + b ≤ n`, and `0` otherwise. -/
theorem coeff_inftyChart {φ : MvPolynomial (Fin 2) R} {n : ℕ} (hφ : φ.totalDegree ≤ n)
    (s : Fin 2 →₀ ℕ) :
    (inftyChart n φ).coeff s = if s 0 + s 1 ≤ n then
      φ.coeff (Finsupp.single 0 (n - (s 0 + s 1)) + Finsupp.single 1 (s 1)) else 0 := by
  classical
  rw [inftyChart, coeff_sum]
  simp_rw [coeff_monomial]
  split_ifs with hs
  · rw [Finset.sum_eq_single (Finsupp.single 0 (n - (s 0 + s 1)) + Finsupp.single 1 (s 1))]
    · rw [ite_eq_left_iff]
      intro h
      exact (h (by ext i; fin_cases i <;> simp; omega)).elim
    · refine fun t ht hne ↦ ite_eq_right_iff.mpr fun h ↦ (hne ?_).elim
      have := (add_le_totalDegree_of_mem_support ht).trans hφ
      have h0 := congrArg (· 0) h
      have h1 := congrArg (· 1) h
      simp at h0 h1
      ext i
      fin_cases i <;> simp <;> omega
    · intro h
      rw [notMem_support_iff.mp h]
      simp
  · refine Finset.sum_eq_zero fun t ht ↦ ite_eq_right_iff.mpr fun h ↦ (hs ?_).elim
    have := (add_le_totalDegree_of_mem_support ht).trans hφ
    rw [← h]
    simp
    omega

/-- **The chart at infinity as a dehomogenization**: let `G` be homogeneous of degree `n` in the
homogeneous coordinates `(X₀ : X₁ : X₂)`. The chart at infinity of the affine equation
`G(X₀, X₁, 1)` is `G(1, X₁, X₀)`, that is the dehomogenization of `G` at the first coordinate
with its two remaining coordinates swapped. -/
theorem inftyChart_dehomogenize {G : MvPolynomial (Fin 3) R} {n : ℕ} (hG : G.IsHomogeneous n) :
    inftyChart n (TauCeti.dehomogenize 2 G) =
      rename (Equiv.swap 0 1) (TauCeti.dehomogenize 0 G) := by
  -- Both sides are additive in `G`, so it suffices to compare them on the monomials of `G`.
  let L : MvPolynomial (Fin 2) R →+ MvPolynomial (Fin 2) R :=
    { toFun := inftyChart n, map_zero' := by simp [inftyChart], map_add' := inftyChart_add n }
  -- Use the bundled additive map to rewrite the sum without unfolding its definition.
  change L _ = _
  conv_lhs => rw [G.as_sum]
  conv_rhs => rw [G.as_sum]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  have hs : s 0 + s 1 + s 2 = n := by
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_three] using
      hG (mem_support_iff.mp hs)
  simp only [L, AddMonoidHom.coe_mk, ZeroHom.coe_mk, TauCeti.dehomogenize_monomial,
    inftyChart_monomial, rename_monomial]
  refine congrArg (fun t ↦ monomial t (G.coeff s)) ?_
  -- Dehomogenizing at `X₂` keeps the coordinates `(X₀, X₁)`, at `X₀` it keeps `(X₁, X₂)`.
  have h21 : (2 : Fin 3).succAbove 1 = 1 := by decide
  ext i
  fin_cases i <;> simp [Finsupp.mapDomain_equiv_apply, h21]
  omega

/-- The chart equation at infinity of a polynomial of total degree at most `n` again has total
degree at most `n`. -/
theorem totalDegree_inftyChart_le {φ : MvPolynomial (Fin 2) R} {n : ℕ}
    (hφ : φ.totalDegree ≤ n) : (inftyChart n φ).totalDegree ≤ n := by
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs ↦ ?_)
  refine (totalDegree_monomial_le _ _).trans ?_
  rw [Finsupp.sum_add_index' (by simp) (by simp), Finsupp.sum_single_index rfl,
    Finsupp.sum_single_index rfl, id_eq, id_eq]
  have := (add_le_totalDegree_of_mem_support hs).trans hφ
  omega

/-- Passing to the chart at infinity keeps the coefficient of `X₁ ^ n`. -/
@[simp]
theorem coeff_single_one_inftyChart {φ : MvPolynomial (Fin 2) R} {n : ℕ}
    (hφ : φ.totalDegree ≤ n) :
    (inftyChart n φ).coeff (Finsupp.single 1 n) = φ.coeff (Finsupp.single 1 n) := by
  simpa using coeff_inftyChart hφ (Finsupp.single 1 n)

section Semifield

variable {L : Type*} [Semifield L] [Algebra R L] {φ : MvPolynomial (Fin 2) R} {n : ℕ}

/-- **Evaluating the chart equation at infinity**: for `x ≠ 0` and `φ` of total degree at most
`n`, `inftyChart n φ (x⁻¹, y x⁻¹) = x⁻ⁿ φ(x, y)`. -/
theorem aeval_inftyChart (hφ : φ.totalDegree ≤ n) {x : L} (hx : x ≠ 0) (y : L) :
    aeval ![x⁻¹, y * x⁻¹] (inftyChart n φ) = x⁻¹ ^ n * aeval ![x, y] φ := by
  rw [inftyChart, map_sum, aeval_fin_two_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le ((add_le_totalDegree_of_mem_support hs).trans hφ)
  rw [aeval_monomial, Finsupp.prod_add_index' (by simp) (by simp [pow_add]),
    Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp), hm,
    Nat.add_sub_cancel_left]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [mul_pow, pow_add, inv_pow]
  field_simp [hx]

/-- **The partial derivative in `X₁` in the chart at infinity**: for `x ≠ 0` and `φ` of total
degree at most `n`, `∂(inftyChart n φ)/∂X₁ (x⁻¹, y x⁻¹) = x^(1 - n) ∂φ/∂X₁ (x, y)`. -/
theorem aeval_pderiv_one_inftyChart (hφ : φ.totalDegree ≤ n) {x : L} (hx : x ≠ 0) (y : L) :
    aeval ![x⁻¹, y * x⁻¹] (pderiv 1 (inftyChart n φ)) =
      x⁻¹ ^ (n - 1) * aeval ![x, y] (pderiv 1 φ) := by
  conv_rhs => rw [φ.as_sum]
  rw [inftyChart, map_sum, map_sum, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le ((add_le_totalDegree_of_mem_support hs).trans hφ)
  simp only [pderiv_monomial, aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]
  simp only [Fin.prod_univ_two, Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_apply]
  simp only [Fin.isValue, zero_ne_one, one_ne_zero, ite_true, ite_false, Matrix.cons_val_zero,
    Matrix.cons_val_one, add_zero, zero_add, tsub_zero, map_mul, map_natCast]
  rcases Nat.eq_zero_or_eq_succ_pred (s 1) with h0 | hj
  · simp [h0]
  · set j := (s 1).pred
    -- Normalize the natural exponents before cancelling powers.
    rw [hm, hj, Nat.succ_sub_one, show s 0 + j.succ + m - 1 = s 0 + j + m by omega,
      show s 0 + j.succ + m - (s 0 + j.succ) = m by omega]
    simp only [mul_pow, pow_add, inv_pow]
    field_simp [hx]

end Semifield

section Algebra

variable {k : Type*}

open scoped Polynomial

/-- Over a domain with more than `n` elements, the leading form `φ_n` of a nonzero polynomial `φ`
of total degree `n` satisfies `φ_n(c, 1) ≠ 0` for some `c`. -/
theorem exists_sum_coeff_mul_pow_ne_zero [CommRing k] [IsDomain k]
    {φ : MvPolynomial (Fin 2) k} (hφ : φ ≠ 0)
    (hcard : (φ.totalDegree : ℕ∞) < ENat.card k) :
    ∃ c : k, ∑ s ∈ φ.support with s 0 + s 1 = φ.totalDegree, φ.coeff s * c ^ s 0 ≠ 0 := by
  classical
  set n := φ.totalDegree
  -- The dehomogenized leading form `φ_n(X, 1)`.
  let g : k[X] := ∑ s ∈ φ.support with s 0 + s 1 = n, Polynomial.C (φ.coeff s) * Polynomial.X ^ s 0
  have hdeg : g.natDegree ≤ n := Polynomial.natDegree_sum_le_of_forall_le _ _ fun s hs ↦
    (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by have := (Finset.mem_filter.1 hs).2; omega)
  -- A monomial `s₀` of top degree contributes the coefficient of `X ^ s₀ 0` alone.
  obtain ⟨s₀, hs₀, hs₀n⟩ := exists_mem_support_add_eq_totalDegree hφ
  have hs₀S : s₀ ∈ φ.support.filter fun s ↦ s 0 + s 1 = n := Finset.mem_filter.2 ⟨hs₀, hs₀n⟩
  have hg : g ≠ 0 := by
    intro h0
    have := congrArg (Polynomial.coeff · (s₀ 0)) h0
    simp only [g, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at this
    rw [Finset.sum_eq_single s₀ (fun s hs hne ↦ ite_eq_right_iff.mpr fun h ↦ (hne ?_).elim)
      (fun h ↦ (h hs₀S).elim)] at this
    · simp only [↓reduceIte] at this
      exact (MvPolynomial.mem_support_iff.mp hs₀) this
    · have h1 := (Finset.mem_filter.1 hs).2
      ext i
      fin_cases i <;> simp <;> omega
  obtain ⟨c, hc⟩ := g.exists_eval_ne_zero_of_natDegree_lt_card hg
    (lt_of_le_of_lt (Nat.cast_le.mpr hdeg) (Cardinal.natCast_lt_toENat.mp hcard))
  exact ⟨c, by simpa [g, Polynomial.eval_finsetSum] using hc⟩

/-- If `φ(u + c y, y) = 0` with `u ∈ K` and the leading form of `φ` does not vanish at `(c, 1)`,
then `y` has degree at most `deg φ` over `K`: it is a root of `φ(u + c Y, Y)`, whose coefficient of
`Y ^ n` is `φ_n(c, 1)`. The coefficients may lie in any commutative semiring mapping faithfully
into `K`, and `y` may lie in any commutative `K`-algebra. -/
theorem natDegree_minpoly_le_totalDegree [CommSemiring k] {K F : Type*} [Field K] [CommRing F]
    [Algebra k K] [FaithfulSMul k K] [Algebra K F] [Algebra k F] [IsScalarTower k K F]
    {φ : MvPolynomial (Fin 2) k} {u : K} {y : F}
    {c : k} (hφ : aeval ![algebraMap K F u + algebraMap k F c * y, y] φ = 0)
    (hc : ∑ s ∈ φ.support with s 0 + s 1 = φ.totalDegree, φ.coeff s * c ^ s 0 ≠ 0) :
    (minpoly K y).natDegree ≤ φ.totalDegree := by
  classical
  set n := φ.totalDegree
  let L : K[X] := Polynomial.C (algebraMap k K c) * Polynomial.X +
    Polynomial.C u
  let ψ : K[X] := ∑ s ∈ φ.support,
    Polynomial.C (algebraMap k K (φ.coeff s)) * (L ^ s 0 * Polynomial.X ^ s 1)
  have hL : L.natDegree ≤ 1 := Polynomial.natDegree_linear_le
  have hterm : ∀ s : Fin 2 →₀ ℕ, (L ^ s 0 * Polynomial.X ^ s 1).natDegree ≤ s 0 + s 1 :=
    fun s ↦ Polynomial.natDegree_mul_le.trans (add_le_add
      ((Polynomial.natDegree_pow_le_of_le _ hL).trans (by rw [mul_one]))
      (Polynomial.natDegree_X_pow_le _))
  have hψdeg : ψ.natDegree ≤ n := Polynomial.natDegree_sum_le_of_forall_le _ _ fun s hs ↦
    (Polynomial.natDegree_C_mul_le _ _).trans
      ((hterm s).trans (add_le_totalDegree_of_mem_support hs))
  have hcoeff : ψ.coeff n =
      algebraMap k K (∑ s ∈ φ.support with s 0 + s 1 = n, φ.coeff s * c ^ s 0) := by
    rw [Polynomial.finsetSum_coeff, map_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun s hs ↦ ?_
    rw [Polynomial.coeff_C_mul]
    split_ifs with hsn
    · have hpow := Polynomial.coeff_pow_of_natDegree_le (m := s 0) hL
      rw [mul_one] at hpow
      rw [← hsn, Polynomial.coeff_mul_X_pow, hpow]
      simp [L]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((hterm s).trans_lt
        (lt_of_le_of_ne (add_le_totalDegree_of_mem_support hs) hsn)), mul_zero]
  have hψ0 : ψ ≠ 0 := fun h ↦ hc <| FaithfulSMul.algebraMap_injective k K <| by
    rw [← hcoeff, h, Polynomial.coeff_zero, map_zero]
  have hψy : Polynomial.aeval y ψ = 0 := by
    rw [← hφ, aeval_fin_two_eq_sum]
    simp [ψ, L, ← IsScalarTower.algebraMap_apply, add_comm]
  exact (Polynomial.natDegree_le_natDegree (minpoly.degree_le_of_ne_zero _ y hψ0 hψy)).trans hψdeg

end Algebra

end MvPolynomial

namespace Polynomial.Bivariate

open scoped Polynomial

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] [Algebra R[X] A]
  [IsScalarTower R R[X] A]

/-- Evaluating `p ∈ R[X][Y]` at `y` in an `R[X]`-algebra `A` is evaluating the corresponding
polynomial in two variables at the image of `X` and at `y`. -/
@[simp]
theorem aeval_equivMvPolynomial (y : A) (p : R[X][Y]) :
    MvPolynomial.aeval ![algebraMap R[X] A X, y] (equivMvPolynomial R p) = aeval y p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
    induction a using Polynomial.induction_on' with
    | add a b ha hb => simp_all
    | monomial m c =>
      simp_rw [← C_mul_X_pow_eq_monomial]
      simp [equivMvPolynomial, IsScalarTower.algebraMap_apply R R[X] A]

/-- Evaluating `p ∈ R[X][Y]`, mapped to `K[Y]` for an `R[X]`-algebra `K`, at `y` in a `K`-algebra
`F` is evaluating the corresponding polynomial in two variables at the image of `X` and at `y`. -/
theorem aeval_map_eq_aeval_equivMvPolynomial {K F : Type*} [CommSemiring K] [CommSemiring F]
    [Algebra R K] [Algebra R[X] K] [IsScalarTower R R[X] K] [Algebra K F] [Algebra R F]
    [IsScalarTower R K F] (p : R[X][X]) (y : F) :
    aeval y (p.map (algebraMap R[X] K)) =
      MvPolynomial.aeval ![algebraMap K F (algebraMap R[X] K X), y] (equivMvPolynomial R p) := by
  -- View `F` as an `R[X]`-algebra through `K`.
  let _ : Algebra R[X] F := ((algebraMap K F).comp (algebraMap R[X] K)).toAlgebra
  have : IsScalarTower R[X] K F := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R R[X] F := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply R[X] K F, ← IsScalarTower.algebraMap_apply R R[X] K,
      ← IsScalarTower.algebraMap_apply R K F]
  rw [aeval_map_algebraMap, ← aeval_equivMvPolynomial, IsScalarTower.algebraMap_apply R[X] K F]

section MvPolynomial

variable {R : Type*} [CommSemiring R]

/-- The monomial `c X₀ ^ s 0 X₁ ^ s 1`, read as a polynomial in `X₁` over `R[X₀]`. -/
@[simp]
theorem equivMvPolynomial_symm_monomial (s : Fin 2 →₀ ℕ) (c : R) :
    (equivMvPolynomial R).symm (MvPolynomial.monomial s c) = C (C c * X ^ s 0) * X ^ s 1 := by
  rw [MvPolynomial.monomial_eq]
  simp [Finsupp.prod_fintype, Fin.prod_univ_two, mul_assoc]

/-- A polynomial in two variables of total degree at most `n` has degree at most `n` in `X₁`. -/
theorem natDegree_equivMvPolynomial_symm_le {φ : MvPolynomial (Fin 2) R} {n : ℕ}
    (hφ : φ.totalDegree ≤ n) : ((equivMvPolynomial R).symm φ).natDegree ≤ n := by
  conv_lhs => rw [φ.as_sum]
  rw [map_sum]
  refine natDegree_sum_le_of_forall_le _ _ fun s hs ↦ ?_
  rw [equivMvPolynomial_symm_monomial]
  exact (natDegree_C_mul_X_pow_le _ _).trans
    (by have := (MvPolynomial.add_le_totalDegree_of_mem_support hs).trans hφ; omega)

/-- For a polynomial in two variables of total degree at most `n`, the coefficient of `X₁ ^ n`
over `R[X₀]` is the constant polynomial given by the coefficient of `X₁ ^ n`. -/
theorem coeff_equivMvPolynomial_symm_of_totalDegree_le {φ : MvPolynomial (Fin 2) R} {n : ℕ}
    (hφ : φ.totalDegree ≤ n) :
    ((equivMvPolynomial R).symm φ).coeff n = C (φ.coeff (Finsupp.single 1 n)) := by
  classical
  conv_lhs => rw [φ.as_sum]
  rw [map_sum, finsetSum_coeff]
  simp_rw [equivMvPolynomial_symm_monomial, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single (Finsupp.single 1 n)]
  · simp
  · exact fun s hs hne ↦ ite_eq_right_iff.mpr fun h ↦
      (hne (MvPolynomial.eq_single_one_of_mem_support hφ hs h.symm)).elim
  · intro h
    rw [MvPolynomial.notMem_support_iff.mp h]
    simp

/-- A polynomial in two variables of total degree at most `n` in which `X₁ ^ n` has coefficient
`1` is monic as a polynomial in `X₁` over `R[X₀]`. -/
theorem monic_equivMvPolynomial_symm {φ : MvPolynomial (Fin 2) R} {n : ℕ}
    (hφ : φ.totalDegree ≤ n) (hc : φ.coeff (Finsupp.single 1 n) = 1) :
    ((equivMvPolynomial R).symm φ).Monic :=
  monic_of_natDegree_le_of_coeff_eq_one n (natDegree_equivMvPolynomial_symm_le hφ)
    (by rw [coeff_equivMvPolynomial_symm_of_totalDegree_le hφ, hc, map_one])

/-- A polynomial in two variables of total degree at most `n` in which `X₁ ^ n` has coefficient
`1` has degree `n` as a polynomial in `X₁` over `R[X₀]`. -/
theorem natDegree_equivMvPolynomial_symm [Nontrivial R] {φ : MvPolynomial (Fin 2) R} {n : ℕ}
    (hφ : φ.totalDegree ≤ n) (hc : φ.coeff (Finsupp.single 1 n) = 1) :
    ((equivMvPolynomial R).symm φ).natDegree = n :=
  natDegree_eq_of_le_of_coeff_ne_zero (natDegree_equivMvPolynomial_symm_le hφ)
    (by rw [coeff_equivMvPolynomial_symm_of_totalDegree_le hφ, hc, map_one]; exact one_ne_zero)

end MvPolynomial

/-- If `φ ∈ k[X₀, X₁]` and `a ∈ k` are such that `φ(a, T) ≠ 0` and `φ(a, y) = 0`, then `y` is
algebraic over `k`: it is a root of the nonzero polynomial `φ(a, T)`. This applies in particular
when `φ` is monic in `X₁` over `k[X₀]` and `k` is nontrivial. -/
theorem isAlgebraic_of_aeval_algebraMap_eq_zero {k F : Type*} [CommRing k] [CommRing F]
    [Algebra k F] {φ : MvPolynomial (Fin 2) k} {a : k}
    (hq : ((equivMvPolynomial k).symm φ).map (evalRingHom a) ≠ 0) {y : F}
    (hy : MvPolynomial.aeval ![algebraMap k F a, y] φ = 0) : IsAlgebraic k y := by
  set q := (equivMvPolynomial k).symm φ
  refine ⟨q.map (evalRingHom a), hq, ?_⟩
  -- View `F` as a `k[X]`-algebra with `X ↦ a`.
  let _ : Algebra k[X] F := (aeval (algebraMap k F a)).toRingHom.toAlgebra
  have : IsScalarTower k k[X] F := .of_algebraMap_eq fun c ↦ by
    simp [RingHom.algebraMap_toAlgebra]
  have h := aeval_equivMvPolynomial (R := k) (A := F) y q
  rw [AlgEquiv.apply_symm_apply, RingHom.algebraMap_toAlgebra] at h
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, hy] at h
  rw [aeval_def, eval₂_map]
  rw [aeval_def] at h
  convert h.symm using 2
  refine ringHom_ext (fun r ↦ ?_) ?_ <;> simp [RingHom.algebraMap_toAlgebra]

end Polynomial.Bivariate
