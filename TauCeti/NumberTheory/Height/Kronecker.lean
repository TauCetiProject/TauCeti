/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Absolute
public import TauCeti.NumberTheory.Height.ProjectiveTuple
import TauCeti.NumberTheory.Height.FiniteOrder

/-!
# Kronecker's theorem for projective tuples and the height gap

Kronecker's criterion `NumberField.absMulHeight₁_eq_one_iff` says that an algebraic number has
absolute height one exactly when it is zero or a root of unity. This file proves its projective
form and the quantitative consequence at bounded degree.

* **Projective Kronecker.** A tuple `x` with algebraic coordinates has absolute projective height
  one exactly when every ratio `x i / x j` with `x j ≠ 0` is zero or a root of unity. For a tuple
  of zeros and roots of unity, a common exponent `N` makes `x ^ N` a tuple of zeros and ones; such
  a tuple is its own square, so its height is an idempotent real number at least one.
* **The height gap.** An algebraic number that is neither zero nor a root of unity has absolute
  height strictly above one (`NumberField.one_lt_absMulHeight₁`). Among such numbers of degree at
  most `D` the absolute logarithmic height is bounded below by a positive constant depending on
  `D`. The constant is ineffective:
  it is the minimum over the finitely many such numbers of absolute height at most `2`, which
  bounded-degree Northcott (`TauCeti.finite_setOf_absMulHeight₁_le`) provides.
* **The degree dependence is essential.** The real numbers `2 ^ (1 / N)` are algebraic, not
  roots of unity, and have absolute logarithmic height `log 2 / N`, so no positive lower bound
  holds uniformly in the degree.

## Main results

* `TauCeti.absoluteProjectiveTupleHeight_eq_one_iff`: projective Kronecker.
* `TauCeti.absoluteProjectiveTupleHeight_eq_one_of_forall_eq_zero_or_isOfFinOrder`: a tuple of
  zeros and roots of unity has absolute height one.
* `TauCeti.exists_pos_forall_le_absLogHeight₁`: the height gap at bounded degree.
* `TauCeti.exists_absLogHeight₁_lt`: without a degree bound there is no gap.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry* (2006), Theorem 1.5.9 and
  Corollary 1.6.15.
* M. Hindry and J. H. Silverman, *Diophantine Geometry: An Introduction* (2000),
  Theorem B.2.3 and Corollary B.2.3.1.
* A prior formalization of these results is Ralf Stephan's `ArithmeticHeights/Kronecker.lean`
  and `ArithmeticHeights/LowerBound.lean` in
  [`rwst/Subspace-Theorems`](https://github.com/rwst/Subspace-Theorems/tree/e443c2479e19f7665b31d8e94e2317c8ced1ca06/ArithmeticHeights),
  commit `e443c2479e19f7665b31d8e94e2317c8ced1ca06` (Apache 2.0).
-/

public section

open Height IntermediateField NumberField

namespace TauCeti

variable {F : Type*} [Field F] [CharZero F] {ι : Type*} [Finite ι]

/-- A tuple whose coordinates are each zero or of finite multiplicative order has absolute
projective height one. -/
theorem absoluteProjectiveTupleHeight_eq_one_of_forall_eq_zero_or_isOfFinOrder {x : ι → F}
    (hx : ∀ i, x i = 0 ∨ IsOfFinOrder (x i)) : absoluteProjectiveTupleHeight x = 1 := by
  classical
  have := Fintype.ofFinite ι
  -- A common multiple `N` of the orders of the nonzero coordinates.
  let n : ι → ℕ := fun i ↦ if x i = 0 then 1 else orderOf (x i)
  have hN : 0 < ∏ i, n i := Finset.prod_pos fun i _ ↦ by
    by_cases h : x i = 0
    · simp [n, h]
    · simpa [n, h] using ((hx i).resolve_left h).orderOf_pos
  set N := ∏ i, n i
  -- `x ^ N` is a tuple of zeros and ones, hence its own square.
  have hsq : (x ^ N) ^ 2 = x ^ N := by
    ext i
    by_cases h : x i = 0
    · simp [h, zero_pow hN.ne']
    · obtain ⟨k, hk⟩ : orderOf (x i) ∣ N := by
        simpa [n, h] using Finset.dvd_prod_of_mem n (Finset.mem_univ i)
      simp [hk, pow_mul, pow_orderOf_eq_one]
  have h := absoluteProjectiveTupleHeight_pow (x ^ N) 2
  rw [hsq, absoluteProjectiveTupleHeight_pow, sq] at h
  -- `H(x) ^ N` is a positive idempotent, so it is `1`.
  have hpos := absoluteProjectiveTupleHeight_pos x
  exact (pow_eq_one_iff_of_nonneg hpos.le hN.ne').mp
    ((mul_eq_left₀ (pow_pos hpos N).ne').mp h.symm)

/-- **Kronecker's theorem for projective tuples.** A tuple with algebraic coordinates has absolute
projective height one if and only if, for every nonzero coordinate `x j`, each ratio `x i / x j`
is zero or of finite multiplicative order. This includes the zero tuple. -/
theorem absoluteProjectiveTupleHeight_eq_one_iff {x : ι → F} (hx : ∀ i, IsAlgebraic ℚ (x i)) :
    absoluteProjectiveTupleHeight x = 1 ↔
      ∀ i j, x j ≠ 0 → x i = 0 ∨ IsOfFinOrder (x i / x j) := by
  constructor
  · intro h i j hj
    have hxj : IsAlgebraic ℚ (x j)⁻¹ := (hx j).isIntegral.inv.isAlgebraic
    -- `(x i / x j, 1)` is `(x j)⁻¹ • x` restricted along `![i, j]`.
    have hle : absMulHeight₁ (x i / x j) ≤ 1 := by
      have hcomp : ((x j)⁻¹ • x) ∘ ![i, j] = ![x i / x j, 1] := by
        ext k
        fin_cases k <;> simp [div_eq_inv_mul, hj]
      rw [absMulHeight₁_eq_absoluteProjectiveTupleHeight, ← hcomp, ← h,
        ← absoluteProjectiveTupleHeight_smul x (inv_ne_zero hj) hxj]
      exact absoluteProjectiveTupleHeight_comp_le
        (fun k ↦ (hxj.isIntegral.mul (hx k).isIntegral).isAlgebraic) ![i, j]
    have hint : IsIntegral ℚ (x i / x j) := by
      rw [div_eq_mul_inv]
      exact (hx i).isIntegral.mul (hx j).isIntegral.inv
    rcases (absMulHeight₁_eq_one_iff hint).mp (le_antisymm hle (one_le_absMulHeight₁ _)) with
      h0 | h0
    · exact .inl (by simpa [hj] using h0)
    · exact .inr h0
  · intro h
    by_cases h0 : x = 0
    · rw [h0, absoluteProjectiveTupleHeight_zero]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp h0
    have hx' : x = x j • fun i ↦ x i / x j := by
      ext i
      simp [mul_div_cancel₀ _ hj]
    rw [hx', absoluteProjectiveTupleHeight_smul _ hj (hx j)]
    exact absoluteProjectiveTupleHeight_eq_one_of_forall_eq_zero_or_isOfFinOrder fun i ↦
      (h i j hj).imp (by simp [·]) id

variable (F) in
/-- **The height gap at bounded degree.** For every `D` there is `c > 0` such that every
algebraic number of degree at most `D` that is neither zero nor of finite multiplicative order has
absolute logarithmic height at least `c`. The constant is ineffective. -/
theorem exists_pos_forall_le_absLogHeight₁ (D : ℕ) :
    ∃ c > 0, ∀ x : F, IsIntegral ℚ x → x ≠ 0 → ¬IsOfFinOrder x →
      Module.finrank ℚ ℚ⟮x⟯ ≤ D → c ≤ absLogHeight₁ x := by
  -- The finitely many candidates of absolute height at most `2`.
  set T := {x : F | IsAlgebraic ℚ x ∧ (minpoly ℚ x).natDegree ≤ D ∧ absMulHeight₁ x ≤ 2} ∩
    {x | x ≠ 0 ∧ ¬IsOfFinOrder x}
  have hT : T.Finite := (finite_setOf_absMulHeight₁_le D 2).inter_of_left _
  obtain ⟨c, hc, hmin⟩ := Set.exists_min_image (insert (Real.log 2) (absLogHeight₁ '' T)) id
    ((hT.image _).insert _) (Set.insert_nonempty _ _)
  refine ⟨c, ?_, fun x hx h0 hfin hD ↦ ?_⟩
  · rcases hc with rfl | ⟨y, ⟨⟨hy, -, -⟩, hy0, hyfin⟩, rfl⟩
    · exact Real.log_pos one_lt_two
    · exact absLogHeight₁_pos hy.isIntegral hy0 hyfin
  · by_cases h2 : absMulHeight₁ x ≤ 2
    · rw [adjoin.finrank hx] at hD
      exact hmin _ (Set.mem_insert_of_mem _ ⟨x, ⟨⟨hx.isAlgebraic, hD, h2⟩, h0, hfin⟩, rfl⟩)
    · calc c ≤ Real.log 2 := hmin _ (Set.mem_insert _ _)
        _ ≤ absLogHeight₁ x := by
          rw [absLogHeight₁]
          exact Real.log_le_log two_pos (not_le.mp h2).le

/-- The real number `2 ^ (1 / N)` has absolute logarithmic height `log 2 / N`. For `N = 0` both
sides are `0`. -/
theorem absLogHeight₁_two_rpow_inv (N : ℕ) :
    absLogHeight₁ ((2 : ℝ) ^ (N : ℝ)⁻¹) = Real.log 2 / N := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp
  have h := absLogHeight₁_pow ((2 : ℝ) ^ (N : ℝ)⁻¹) N
  rw [Real.rpow_inv_natCast_pow zero_le_two hN] at h
  have h2 : absLogHeight₁ (2 : ℝ) = Real.log 2 := by exact_mod_cast absLogHeight₁_natCast 2
  rw [h2] at h
  rw [h, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hN)]

/-- **No gap without a degree bound.** For every `c > 0` some algebraic number that is neither
zero nor of finite multiplicative order has absolute logarithmic height below `c`: one may take
`2 ^ (1 / N)` for `N` large. -/
theorem exists_absLogHeight₁_lt {c : ℝ} (hc : 0 < c) :
    ∃ x : ℝ, IsIntegral ℚ x ∧ x ≠ 0 ∧ ¬IsOfFinOrder x ∧ absLogHeight₁ x < c := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.log 2 / c)
  have hN0 : (0 : ℝ) < N := (div_pos (Real.log_pos one_lt_two) hc).trans hN
  have hN0' : N ≠ 0 := by exact_mod_cast hN0.ne'
  set x : ℝ := 2 ^ (N : ℝ)⁻¹
  have hxN : x ^ N = 2 := Real.rpow_inv_natCast_pow zero_le_two hN0'
  have hx1 : 1 < x := Real.one_lt_rpow one_lt_two (inv_pos.mpr hN0)
  refine ⟨x, ?_, by positivity, ?_, ?_⟩
  · refine IsIntegral.of_pow (Nat.pos_of_ne_zero hN0') ?_
    rw [hxN]
    exact_mod_cast isIntegral_natCast 2
  · rw [isOfFinOrder_iff_pow_eq_one]
    rintro ⟨m, hm, hxm⟩
    exact (one_lt_pow₀ hx1 hm.ne').ne' hxm
  · rw [absLogHeight₁_two_rpow_inv, div_lt_iff₀ hN0]
    exact (div_lt_iff₀ hc).mp hN |>.trans_eq (mul_comm _ _)

/-- The rational numbers `-1` and `2` have absolute heights `1` and `2`. -/
example : absMulHeight₁ (-1 : ℚ) = 1 ∧ absMulHeight₁ (2 : ℚ) = 2 := by
  refine ⟨(absMulHeight₁_eq_one_iff (.of_finite ℚ _)).mpr (.inr ?_), ?_⟩
  · exact isOfFinOrder_iff_pow_eq_one.mpr ⟨2, two_pos, by norm_num⟩
  · exact_mod_cast absMulHeight₁_natCast 2

/-- The rational tuples `(1, -1)` and `(1, 2)` have absolute heights `1` and `2`. -/
example : absoluteProjectiveTupleHeight ![(1 : ℚ), -1] = 1 ∧
    absoluteProjectiveTupleHeight ![(1 : ℚ), 2] = 2 := by
  refine ⟨absoluteProjectiveTupleHeight_eq_one_of_forall_eq_zero_or_isOfFinOrder fun i ↦ ?_, ?_⟩
  · refine .inr (isOfFinOrder_iff_pow_eq_one.mpr ⟨2, two_pos, ?_⟩)
    fin_cases i <;> norm_num
  · have h : ![(1 : ℚ), 2] = (↑) ∘ ![(1 : ℤ), 2] := by
      ext i
      fin_cases i <;> simp
    rw [h, absoluteProjectiveTupleHeight_eq, Module.finrank_self,
      Rat.mulHeight_eq_max_abs_of_gcd_eq_one (by decide),
      le_antisymm (ciSup_le fun i ↦ by fin_cases i <;> simp) (Finite.le_ciSup_of_le 1 le_rfl)]
    norm_num

end TauCeti
