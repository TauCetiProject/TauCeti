/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Filtration

/-!
# Truncated uniformizer expansions at rational places

Let `P` be a rational place of `F / k` and let `t` have order one at `P`. Every function
integral at `P` has a unique expansion modulo the `n`-th order filtration as a polynomial in
`t` with `n` coefficients in `k`. This file constructs these finite coefficient vectors and
characterizes them by the order of the remainder. The coefficients depend only on the
function modulo the same filtration, and successive truncations agree.

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

end TauCeti.Place
