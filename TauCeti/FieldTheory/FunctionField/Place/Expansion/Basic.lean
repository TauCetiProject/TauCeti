/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Filtration
public import TauCeti.Algebra.BigOperators.Finset.Pairs
public import Mathlib.Algebra.Polynomial.OfFn

/-!
# Truncated uniformizer expansions at rational places

Let `P` be a rational place of `F / k` and let `t` have order one at `P`. Every function
integral at `P` has a unique expansion modulo the `n`-th order filtration as a polynomial in
`t` with `n` coefficients in `k`. This file constructs these finite coefficient vectors and
characterizes them by the order of the remainder. The coefficients depend only on the
function modulo the same filtration, and successive truncations agree. Constants have only
a constant coefficient, the chosen uniformizer has only a degree-one coefficient, and
multiplication of integral functions gives coefficient convolution.

Peeling off leading terms one at a time also shows that a `k`-linear map on `F` is determined
by its values on a step of the order filtration and on the powers of the uniformizer below it.

These are finite truncations: no completeness assumption or infinite series is used. They
provide the finite approximation and uniqueness statements for the power-series construction
in a completed valuation ring. In particular, the statements also apply to the place on a
completion once that place and its constant-field algebra have been supplied.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section IV.2.
-/

public section

open scoped BigOperators

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable (P : Place k F) {t : F}

private theorem div_uniformizer_mem_filtration_iff (ht : P.ord t = 1) (a : ℤ) (x : F) :
    x / t ∈ P.filtration a ↔ x ∈ P.filtration (a + 1) := by
  have ht0 : t ≠ 0 := by
    intro h
    simp [h] at ht
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [P.mem_filtration_iff_le_ord (div_ne_zero hx ht0),
      P.mem_filtration_iff_le_ord hx, P.ord_div hx ht0, ht]
    omega

private theorem constant_sub_mem_filtration_one_iff (c d : k) :
    algebraMap k F c - algebraMap k F d ∈ P.filtration 1 ↔ c = d := by
  rw [← map_sub]
  rcases eq_or_ne c d with rfl | hcd
  · simp
  · have h0 : algebraMap k F (c - d) ≠ 0 :=
      (map_ne_zero (algebraMap k F)).mpr (sub_ne_zero.mpr hcd)
    rw [P.mem_filtration_iff_le_ord h0, P.ord_algebraMap]
    simp [hcd]

private theorem exists_sub_sum_mem_filtration (hP : P.degree = 1) (ht : P.ord t = 1)
    (n : ℕ) (x : F) (hx : x ∈ P.integers) :
    ∃ c : Fin n → k, x - ∑ i, algebraMap k F (c i) * t ^ (i : ℕ) ∈ P.filtration n := by
  induction n generalizing x with
  | zero =>
    exact ⟨Fin.elim0, by simpa using P.mem_filtration_zero_iff.mpr hx⟩
  | succ n ih =>
    obtain ⟨c₀, hc₀⟩ :=
      (P.degree_eq_one_iff_forall_exists_valuation_sub_lt_one.mp hP) x hx
    have hy : (x - algebraMap k F c₀) / t ∈ P.integers := by
      apply P.mem_filtration_zero_iff.mp
      exact (P.div_uniformizer_mem_filtration_iff ht 0 _).mpr
        (P.mem_filtration_one_iff.mpr hc₀)
    obtain ⟨c, hc⟩ := ih _ hy
    refine ⟨Fin.cons c₀ c, ?_⟩
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero,
      pow_zero, mul_one, Fin.val_succ, pow_succ, ← mul_assoc, ← Finset.sum_mul]
    have ht0 : t ≠ 0 := by
      intro h
      simp [h] at ht
    have hm := P.mul_mem_filtration hc (P.mem_filtration_ord t)
    rw [ht] at hm
    simpa only [Nat.cast_add, Nat.cast_one, sub_mul, div_mul_cancel₀ _ ht0,
      sub_add_eq_sub_sub] using hm

private theorem sum_mem_filtration_iff (ht : P.ord t = 1) (n : ℕ) (c : Fin n → k) :
    (∑ i, algebraMap k F (c i) * t ^ (i : ℕ)) ∈ P.filtration n ↔ c = 0 := by
  induction n with
  | zero =>
    constructor
    · intro _
      ext i
      exact Fin.elim0 i
    · intro _
      simp
  | succ n ih =>
    simp only [Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ,
      pow_succ, ← mul_assoc, ← Finset.sum_mul]
    have ht0 : t ∈ P.filtration 1 := by
      simpa [ht] using P.mem_filtration_ord t
    have hsum0 : (∑ i : Fin n, algebraMap k F (c i.succ) * t ^ (i : ℕ)) ∈
        P.filtration 0 := by
      apply Submodule.sum_mem
      intro i _
      exact P.mem_filtration_zero_iff.mpr
        (mul_mem (P.algebraMap_mem_integers _) (pow_mem
          (P.mem_integers_iff_ord_nonneg.mpr (by omega : 0 ≤ P.ord t)) _))
    constructor
    · intro h
      have htail1 : (∑ i : Fin n, algebraMap k F (c i.succ) * t ^ (i : ℕ)) * t ∈
          P.filtration 1 := by simpa using P.mul_mem_filtration hsum0 ht0
      have hconstant := (P.filtration 1).sub_mem
        (P.filtration_antitone (by omega) h) htail1
      have hc₀ : c 0 = 0 := by
        apply (P.constant_sub_mem_filtration_one_iff (c 0) 0).mp
        simpa using hconstant
      have htail : (∑ i : Fin n, algebraMap k F (c i.succ) * t ^ (i : ℕ)) ∈
          P.filtration n := by
        have htne : t ≠ 0 := by
          intro h
          simp [h] at ht
        have hh := (P.div_uniformizer_mem_filtration_iff ht n
          ((∑ i : Fin n, algebraMap k F (c i.succ) * t ^ (i : ℕ)) * t)).mpr
          (by simpa [hc₀] using h)
        simpa [mul_div_cancel_right₀ _ htne] using hh
      have hcz := (ih fun i ↦ c i.succ).mp htail
      ext i
      exact Fin.cases hc₀ (fun j ↦ congrFun hcz j) i
    · intro hc
      simp [hc]

/-- At a rational place, an integral function has a unique polynomial expansion of length
`n` in a chosen uniformizer, with remainder vanishing to order at least `n`. The filtration
condition includes the zero remainder, unlike an unguarded inequality for `ord`. -/
theorem existsUnique_sub_sum_mem_filtration (hP : P.degree = 1) (ht : P.ord t = 1)
    (n : ℕ) (x : F) (hx : x ∈ P.integers) :
    ∃! c : Fin n → k, x - ∑ i, algebraMap k F (c i) * t ^ (i : ℕ) ∈ P.filtration n := by
  obtain ⟨c, hc⟩ := P.exists_sub_sum_mem_filtration hP ht n x hx
  refine ⟨c, hc, fun d hd ↦ ?_⟩
  have h := (P.filtration n).sub_mem hc hd
  have hz : (∑ i, algebraMap k F ((d - c) i) * t ^ (i : ℕ)) ∈ P.filtration n := by
    convert h using 1
    simp only [Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  exact sub_eq_zero.mp ((P.sum_mem_filtration_iff ht n (d - c)).mp hz)

/-! ### Canonical finite coefficient vectors -/

/-- The coefficients of the unique length-`n` uniformizer expansion of an integral function
at a rational place. Its remainder is characterized by
`TauCeti.Place.truncatedExpansion_eq_iff`; successive lengths agree on their common indices. -/
noncomputable def truncatedExpansion (hP : P.degree = 1) (ht : P.ord t = 1)
    (n : ℕ) (x : P.integers) : Fin n → k :=
  (P.existsUnique_sub_sum_mem_filtration hP ht n x x.2).exists.choose

/-- Subtracting the truncated expansion leaves a function vanishing to the stated order. -/
theorem sub_sum_truncatedExpansion_mem_filtration (hP : P.degree = 1) (ht : P.ord t = 1)
    (n : ℕ) (x : P.integers) :
    (x : F) - ∑ i, algebraMap k F (P.truncatedExpansion hP ht n x i) * t ^ (i : ℕ) ∈
      P.filtration n :=
  (P.existsUnique_sub_sum_mem_filtration hP ht n x x.2).exists.choose_spec

/-- A coefficient vector is the truncated expansion precisely when its remainder vanishes
to order at least the length of the vector. This characterizes the coefficients without
unfolding their construction. -/
theorem truncatedExpansion_eq_iff (hP : P.degree = 1) (ht : P.ord t = 1)
    (n : ℕ) (x : P.integers) (c : Fin n → k) :
    P.truncatedExpansion hP ht n x = c ↔
      (x : F) - ∑ i, algebraMap k F (c i) * t ^ (i : ℕ) ∈ P.filtration n := by
  constructor
  · intro h
    rw [← h]
    exact P.sub_sum_truncatedExpansion_mem_filtration hP ht n x
  · intro hc
    exact (P.existsUnique_sub_sum_mem_filtration hP ht n x x.2).unique
      (P.sub_sum_truncatedExpansion_mem_filtration hP ht n x) hc

/-- The zero function has zero coefficients at every truncation length. -/
@[simp]
theorem truncatedExpansion_zero (hP : P.degree = 1) (ht : P.ord t = 1) (n : ℕ) :
    P.truncatedExpansion hP ht n 0 = 0 := by
  apply (P.truncatedExpansion_eq_iff hP ht n 0 0).mpr
  simp

/-- Uniformizer coefficients respect addition of integral functions. -/
@[simp]
theorem truncatedExpansion_add (hP : P.degree = 1) (ht : P.ord t = 1)
    (n : ℕ) (x y : P.integers) :
    P.truncatedExpansion hP ht n (x + y) =
      P.truncatedExpansion hP ht n x + P.truncatedExpansion hP ht n y := by
  apply (P.truncatedExpansion_eq_iff hP ht n (x + y) _).mpr
  have h := (P.filtration n).add_mem
    (P.sub_sum_truncatedExpansion_mem_filtration hP ht n x)
    (P.sub_sum_truncatedExpansion_mem_filtration hP ht n y)
  convert h using 1
  rw [← ValuationSubring.algebraMap_apply P.integers (x + y)]
  simp only [map_add, ValuationSubring.algebraMap_apply, Pi.add_apply, add_mul,
    Finset.sum_add_distrib]
  ring

/-- Uniformizer coefficients respect multiplication by constants. -/
@[simp]
theorem truncatedExpansion_smul (hP : P.degree = 1) (ht : P.ord t = 1)
    (n : ℕ) (c : k) (x : P.integers) :
    P.truncatedExpansion hP ht n (c • x) = c • P.truncatedExpansion hP ht n x := by
  apply (P.truncatedExpansion_eq_iff hP ht n (c • x) _).mpr
  have h := (P.filtration n).smul_mem c
    (P.sub_sum_truncatedExpansion_mem_filtration hP ht n x)
  convert h using 1
  simp only [Pi.smul_apply, smul_eq_mul, Algebra.smul_def, map_mul,
    mul_sub, mul_assoc, Finset.mul_sum]
  rw [← ValuationSubring.algebraMap_apply P.integers ((algebraMap k P.integers c) * x)]
  simp only [map_mul, ValuationSubring.algebraMap_apply, P.coe_algebraMap_constants]

/-- Uniformizer coefficients respect negation of integral functions. -/
@[simp]
theorem truncatedExpansion_neg (hP : P.degree = 1) (ht : P.ord t = 1)
    (n : ℕ) (x : P.integers) :
    P.truncatedExpansion hP ht n (-x) = -P.truncatedExpansion hP ht n x := by
  simpa only [neg_one_smul] using P.truncatedExpansion_smul hP ht n (-1 : k) x

/-- Uniformizer coefficients respect subtraction of integral functions. -/
@[simp]
theorem truncatedExpansion_sub (hP : P.degree = 1) (ht : P.ord t = 1)
    (n : ℕ) (x y : P.integers) :
    P.truncatedExpansion hP ht n (x - y) =
      P.truncatedExpansion hP ht n x - P.truncatedExpansion hP ht n y := by
  simp only [sub_eq_add_neg, P.truncatedExpansion_add, P.truncatedExpansion_neg]

/-- The unit has constant coefficient one and all positive-degree coefficients zero. -/
@[simp]
theorem truncatedExpansion_one (hP : P.degree = 1) (ht : P.ord t = 1) (n : ℕ) :
    P.truncatedExpansion hP ht n 1 = fun i : Fin n ↦ if (i : ℕ) = 0 then 1 else 0 := by
  apply (P.truncatedExpansion_eq_iff hP ht n 1 _).mpr
  cases n <;> simp [P.mem_filtration_zero_iff]

/-- Constants have their given constant coefficient and zero positive-degree coefficients. -/
@[simp]
theorem truncatedExpansion_algebraMap (hP : P.degree = 1) (ht : P.ord t = 1)
    (n : ℕ) (c : k) :
    P.truncatedExpansion hP ht n (algebraMap k P.integers c) =
      fun i : Fin n ↦ if (i : ℕ) = 0 then c else 0 := by
  rw [Algebra.algebraMap_eq_smul_one, P.truncatedExpansion_smul hP ht,
    P.truncatedExpansion_one hP ht]
  ext i
  by_cases hi : (i : ℕ) = 0 <;> simp [hi]

/-- The chosen uniformizer has coefficient one in degree one and zero in every other degree,
including at truncation lengths zero and one. -/
@[simp]
theorem truncatedExpansion_uniformizer (hP : P.degree = 1) (ht : P.ord t = 1) (n : ℕ) :
    P.truncatedExpansion hP ht n
      ⟨t, P.mem_integers_iff_ord_nonneg.mpr (by omega)⟩ =
      fun i : Fin n ↦ if (i : ℕ) = 1 then 1 else 0 := by
  apply (P.truncatedExpansion_eq_iff hP ht n _ _).mpr
  cases n with
  | zero =>
    simpa using P.mem_filtration_zero_iff.mpr
      (P.mem_integers_iff_ord_nonneg.mpr (by omega : 0 ≤ P.ord t))
  | succ n =>
    cases n with
    | zero => simpa [Fin.sum_univ_succ, ht] using P.mem_filtration_ord t
    | succ n => simp [Fin.sum_univ_succ]

/-- The coefficient of a product is the convolution of the coefficients of its factors.
The sum ranges over bounded pairs of indices whose degrees add to the requested degree;
terms of degree at least `n` vanish modulo the `n`-th order filtration. -/
@[simp]
theorem truncatedExpansion_mul (hP : P.degree = 1) (ht : P.ord t = 1)
    (n : ℕ) (x y : P.integers) (i : Fin n) :
    P.truncatedExpansion hP ht n (x * y) i =
      ∑ j : Fin n × Fin n with (j.1 : ℕ) + (j.2 : ℕ) = (i : ℕ),
        P.truncatedExpansion hP ht n x j.1 * P.truncatedExpansion hP ht n y j.2 := by
  classical
  let a := P.truncatedExpansion hP ht n x
  let b := P.truncatedExpansion hP ht n y
  -- Encode the finite vectors as polynomials without unfolding coefficient extraction.
  let polynomial := Polynomial.ofFn (R := k) n
  let u := (polynomial a).eval₂ (algebraMap k F) t
  let v := (polynomial b).eval₂ (algebraMap k F) t
  have heval (c : Fin n → k) :
      (polynomial c).eval₂ (algebraMap k F) t =
        ∑ j, algebraMap k F (c j) * t ^ (j : ℕ) := by
    simp only [polynomial, Polynomial.ofFn_eq_sum_monomial,
      Polynomial.eval₂_finsetSum, Polynomial.eval₂_monomial]
  have hcoeff (c : Fin n → k) (j : Fin n) : (polynomial c).coeff j = c j := by
    exact Polynomial.ofFn_coeff_eq_val_of_lt c j.isLt
  have hu : u ∈ P.filtration 0 := by
    dsimp only [u]
    rw [heval]
    apply Submodule.sum_mem
    intro j _
    exact P.mem_filtration_zero_iff.mpr
      (mul_mem (P.algebraMap_mem_integers _) (pow_mem
        (P.mem_integers_iff_ord_nonneg.mpr (by omega : 0 ≤ P.ord t)) _))
  -- Replacing either integral factor by its finite expansion preserves the product modulo
  -- the filtration, since multiplying a remainder by an integral function preserves its order.
  have hrem : (x : F) * (y : F) - u * v ∈ P.filtration n := by
    have hx := P.mul_mem_filtration
      (P.sub_sum_truncatedExpansion_mem_filtration hP ht n x)
      (P.mem_filtration_zero_iff.mpr y.2)
    have hy := P.mul_mem_filtration hu
      (P.sub_sum_truncatedExpansion_mem_filtration hP ht n y)
    rw [← heval a, add_zero] at hx
    rw [← heval b, zero_add] at hy
    convert (P.filtration n).add_mem hx hy using 1
    ring
  let q := polynomial a * polynomial b
  -- Mathlib supplies both multiplication of evaluations and coefficient convolution.
  -- Reindex its antidiagonal only to retain the bounded-pair public formula.
  have hconvolution (j : Fin n) : q.coeff j =
      ∑ l : Fin n × Fin n with (l.1 : ℕ) + (l.2 : ℕ) = (j : ℕ), a l.1 * b l.2 := by
    rw [Polynomial.coeff_mul]
    symm
    apply sum_fin_product_eq_sum_antidiagonal j.isLt
    intro l _
    simp only [hcoeff]
  -- Evaluate the product polynomial and discard only terms of degree at least `n`.
  -- Include missing low degrees as zero terms so the truncation ranges over all `Fin n`.
  let s := q.support ∪ Finset.range n
  let f := fun d : ℕ ↦ algebraMap k F (q.coeff d) * t ^ d
  have hprod : u * v = ∑ d ∈ s, f d := by
    rw [← Polynomial.eval₂_mul, Polynomial.eval₂_eq_sum]
    exact Polynomial.sum_eq_of_subset _ (by simp) Finset.subset_union_left
  have hlow : (∑ d ∈ s with d < n, f d) = ∑ j : Fin n, f j := by
    rw [Fin.sum_univ_eq_sum_range]
    congr 1
    ext d
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_range, s]
    tauto
  have hhigh : (∑ d ∈ s with ¬d < n, f d) ∈ P.filtration n := by
    apply Submodule.sum_mem
    intro d hd
    have hdegree : (n : ℤ) ≤ (d : ℤ) := by
      exact_mod_cast Nat.le_of_not_lt (Finset.mem_filter.mp hd).2
    have hpow := P.mem_filtration_ord (t ^ d)
    simp only [P.ord_pow, ht, mul_one] at hpow
    apply P.filtration_antitone hdegree
    have hm := P.mul_mem_filtration
      (P.mem_filtration_zero_iff.mpr (P.algebraMap_mem_integers (q.coeff d))) hpow
    simpa only [zero_add] using hm
  have heq := (P.truncatedExpansion_eq_iff hP ht n (x * y)
    (fun j ↦ q.coeff j)).mpr (by
      have hsplit := Finset.sum_filter_add_sum_filter_not s (fun d ↦ d < n) f
      rw [hlow] at hsplit
      convert (P.filtration n).add_mem hrem hhigh using 1
      rw [hprod, ← hsplit]
      -- Coercing the product in the valuation ring gives multiplication in `F`.
      change (x : F) * (y : F) - _ = _
      ring)
  exact (congrFun heq i).trans (hconvolution i)

/-- Increasing the truncation length preserves every coefficient already extracted. This
compatibility allows the finite vectors to determine a single power-series coefficient
sequence. -/
@[simp]
theorem truncatedExpansion_castSucc (hP : P.degree = 1) (ht : P.ord t = 1)
    (n : ℕ) (x : P.integers) (i : Fin n) :
    P.truncatedExpansion hP ht (n + 1) x i.castSucc = P.truncatedExpansion hP ht n x i := by
  have hhigh := P.sub_sum_truncatedExpansion_mem_filtration hP ht (n + 1) x
  have hlast : algebraMap k F (P.truncatedExpansion hP ht (n + 1) x (Fin.last n)) * t ^ n ∈
      P.filtration n := by
    have hpow : t ^ n ∈ P.filtration n := by
      simpa [P.ord_pow, ht] using P.mem_filtration_ord (t ^ n)
    simpa using P.mul_mem_filtration
      (P.mem_filtration_zero_iff.mpr (P.algebraMap_mem_integers _)) hpow
  have hlow := (P.filtration n).add_mem
    (P.filtration_antitone (by omega) hhigh) hlast
  rw [Fin.sum_univ_castSucc] at hlow
  simp only [Fin.val_castSucc, Fin.val_last] at hlow
  have heq := (P.truncatedExpansion_eq_iff hP ht n x
    (fun j ↦ P.truncatedExpansion hP ht (n + 1) x j.castSucc)).mpr
    (by convert hlow using 1; ring)
  exact (congrFun heq i).symm

/-- Increasing the truncation length preserves the coefficients at all indices of the
shorter expansion. -/
@[simp]
theorem truncatedExpansion_castLE (hP : P.degree = 1) (ht : P.ord t = 1)
    {n m : ℕ} (hnm : n ≤ m)
    (x : P.integers) (i : Fin n) :
    P.truncatedExpansion hP ht m x (i.castLE hnm) = P.truncatedExpansion hP ht n x i := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    -- Both casts preserve the underlying natural index; expose the successor cast so the
    -- finite-expansion compatibility lemma applies.
    rw [show i.castLE (Nat.le_succ_of_le hnm) = (i.castLE hnm).castSucc from rfl,
      P.truncatedExpansion_castSucc hP ht]
    exact ih

/-- Two integral functions have the same length-`n` coefficient vector exactly when they
agree modulo the `n`-th order filtration. Thus coefficient extraction descends to finite
jets, with no choices of representatives visible in the coefficients. -/
theorem truncatedExpansion_eq_iff_sub_mem_filtration (hP : P.degree = 1)
    (ht : P.ord t = 1) (n : ℕ) (x y : P.integers) :
    P.truncatedExpansion hP ht n x = P.truncatedExpansion hP ht n y ↔
      (x : F) - (y : F) ∈ P.filtration n := by
  have hx := P.sub_sum_truncatedExpansion_mem_filtration hP ht n x
  have hy := P.sub_sum_truncatedExpansion_mem_filtration hP ht n y
  constructor
  · intro h
    rw [h] at hx
    convert (P.filtration n).sub_mem hx hy using 1
    ring
  · intro h
    apply (P.truncatedExpansion_eq_iff hP ht n x _).mpr
    convert (P.filtration n).add_mem h hy using 1
    ring

/-! ### Linear maps determined on powers of a uniformizer -/

/-- At a rational place, two `k`-linear maps on `F` that agree on the step `𝔪_P^m` of the order
filtration and on every power `t ^ j`, `j < m`, of a uniformizer `t` are equal: subtracting
the leading term `c * t ^ j` of a function of order `j < m` raises its order. -/
theorem linearMap_ext_zpow {M : Type*} [AddCommGroup M] [Module k M] (hP : P.degree = 1)
    (ht : P.ord t = 1) {m : ℤ} {f g : F →ₗ[k] M}
    (hfg : ∀ z ∈ P.filtration m, f z = g z) (h : ∀ j < m, f (t ^ j) = g (t ^ j)) : f = g := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
  have htj (j : ℤ) : t ^ j ∈ P.filtration j := by
    simpa [P.ord_zpow, ht] using P.mem_filtration_ord (t ^ j)
  -- Induction on how far below `m` the order of the function may lie.
  have key (d : ℕ) : ∀ z ∈ P.filtration (m - d), f z = g z := by
    induction d with
    | zero =>
      intro z hz
      rw [Nat.cast_zero, sub_zero] at hz
      exact hfg z hz
    | succ d ih =>
      intro z hz
      generalize hj' : m - ((d + 1 : ℕ) : ℤ) = j at hz
      have hj : j < m := by omega
      have hint := P.mul_mem_filtration (htj (-j)) hz
      rw [neg_add_cancel, mem_filtration_zero_iff] at hint
      obtain ⟨c, hc, -⟩ := P.existsUnique_sub_sum_mem_filtration hP ht 1 _ hint
      -- `z - c 0 • t ^ j = t ^ j * (t ^ (-j) * z - c 0)` has order at least `j + 1`.
      have heq : t ^ j * (t ^ (-j) * z - ∑ i : Fin 1, algebraMap k F (c i) * t ^ (i : ℕ)) =
          z - c 0 • t ^ j := by
        rw [Fin.sum_univ_one, Algebra.smul_def, mul_sub, ← mul_assoc, ← zpow_add₀ ht0]
        simp [mul_comm]
      have hrem : z - c 0 • t ^ j ∈ P.filtration (m - d) := by
        rw [← heq, show m - d = j + ((1 : ℕ) : ℤ) by omega]
        exact P.mul_mem_filtration (htj j) hc
      calc f z = f (z - c 0 • t ^ j) + c 0 • f (t ^ j) := by
            rw [← map_smul, ← map_add, sub_add_cancel]
        _ = g z := by
            rw [ih _ hrem, h _ hj, ← map_smul, ← map_add, sub_add_cancel]
  ext z
  exact key _ z (P.filtration_antitone (show m - ((m - P.ord z).toNat : ℕ) ≤ P.ord z by omega)
    (P.mem_filtration_ord z))

end TauCeti.Place
