/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import TauCeti.NumberTheory.Height.Affine

import all Mathlib.NumberTheory.Height.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Int

/-!
# Heights of values of linear forms and of determinants

The value `∑ i, a i * x i` of a linear form and the determinant of a matrix are not homogeneous
of degree zero in their arguments: scaling the coefficient tuple `a` by `c` multiplies the value
by `c` but leaves the projective height `Height.mulHeight a` unchanged. So no bound on the height
of such a value in terms of projective heights can hold (`Height.exists_not_mulHeight₁_det_le`
records this for determinants). The bounds that do hold use the affine height
`Height.mulHeightAff`, whose local factor at a place `v` is `max (⨆ i, v (x i)) 1`.

Both bounds come from one estimate, `Height.mulHeight₁_sum_le_prod_mulHeightAff`: if every term
of a finite sum is bounded, at every absolute value, by the product of the affine local factors
of a fixed family of tuples, then the height of the sum is at most `#s ^ totalWeight K` times the
product of the affine heights of the tuples. The factor `#s` is paid only at the archimedean
places; at the nonarchimedean places the ultrametric inequality makes it disappear.

## Main results

* `Height.mulHeight₁_sum_mul_le`, `Height.logHeight₁_sum_mul_le`: the height of the value of a
  linear form is at most `Nat.card ι ^ totalWeight K * (mulHeightAff a * mulHeightAff x)`.
* `Height.exists_mulHeight₁_sum_mul_eq`: over `ℚ` the constant `Nat.card ι ^ totalWeight K` is
  attained, by `a = x = 1`, for every nonempty finite `ι`.
* `Matrix.mulHeight₁_det_le`, `Matrix.logHeight₁_det_le`: the height of a determinant is at most
  `(Nat.card n)! ^ totalWeight K` times the product of the affine heights of the columns, by the
  Leibniz expansion; `Matrix.mulHeight₁_det_le_mulHeightAff_pow` and
  `Matrix.logHeight₁_det_le_logHeightAff` bound it by the affine height of all the entries.
* `Height.exists_not_mulHeight₁_det_le`: the determinant is not bounded by any multiple of the
  projective height of the entries, already for `1 × 1` matrices over `ℚ`.

## Implementation notes

The global step needs the finiteness of the multiplicative support of the nonarchimedean local
factors `max (v x) 1` of `Height.mulHeight₁`, which Mathlib proves by the `private`
`fun_prop` lemma `Height.hasFiniteMulSupport_max_nonarchAbsVal` in
`Mathlib/NumberTheory/Height/Basic.lean`; it is reached by `import all`, as Mathlib's own
`Mathlib/NumberTheory/Height/MvPolynomial.lean` does. The affine counterpart is the public
`Height.hasFiniteMulSupport_max_iSup_nonarchAbsVal`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press,
  2006, §1.5 (Proposition 1.5.15) and §1.6.
* The statements follow `ArithmeticHeights/LinearForm.lean` and `ArithmeticHeights/Matrix.lean`
  of `rwst/Subspace-Theorems` (commit `ad93117`, Apache 2.0); the proofs here are local, term by
  term, and do not go through a tuple sum bound.
-/

public section

open Finset Real

namespace Height

open AdmissibleAbsValues

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {ι : Type*}

/-- **Local-to-global bound for sums.** Let `y : κ → ι → K` be a finite family of tuples, and let
every term `t a`, `a ∈ s`, of a nonempty finite sum satisfy `v (t a) ≤ ∏ k, max (⨆ i, v (y k i)) 1`
at every absolute value `v`. Then the height of the sum is at most `#s ^ totalWeight K` times the
product of the affine heights of the tuples `y k`. -/
theorem mulHeight₁_sum_le_prod_mulHeightAff {α κ : Type*} [Fintype κ] [Finite ι]
    {s : Finset α} (hs : s.Nonempty) (t : α → K) (y : κ → ι → K)
    (ht : ∀ v : AbsoluteValue K ℝ, ∀ a ∈ s, v (t a) ≤ ∏ k, max (⨆ i, v (y k i)) 1) :
    mulHeight₁ (∑ a ∈ s, t a) ≤ #s ^ totalWeight K * ∏ k, mulHeightAff (y k) := by
  -- `M v` is the product of the affine local factors at `v`; it is at least `1`.
  set M : AbsoluteValue K ℝ → ℝ := fun v ↦ ∏ k, max (⨆ i, v (y k i)) 1
  have hM1 (v : AbsoluteValue K ℝ) : 1 ≤ M v :=
    one_le_prod₀ fun _ _ ↦ le_max_right _ _
  -- At an arbitrary place the triangle inequality costs the factor `#s`.
  have harch (v : AbsoluteValue K ℝ) : max (v (∑ a ∈ s, t a)) 1 ≤ #s * M v := by
    have hcard : (1 : ℝ) ≤ #s := by exact_mod_cast hs.card_pos
    refine max_le ?_ (one_le_mul_of_one_le_of_one_le hcard (hM1 v))
    calc v (∑ a ∈ s, t a) ≤ ∑ a ∈ s, v (t a) := v.sum_le _ _
      _ ≤ ∑ _a ∈ s, M v := sum_le_sum (ht v)
      _ = #s * M v := by rw [sum_const, nsmul_eq_mul]
  -- At a nonarchimedean place the ultrametric inequality removes it.
  have hnonarch {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v) :
      max (v (∑ a ∈ s, t a)) 1 ≤ M v :=
    max_le ((hv.apply_sum_le_sup hs).trans (sup'_le hs _ (ht v))) (hM1 v)
  -- Split both sides place by place, and absorb `#s ^ totalWeight K` into the archimedean product
  -- as one factor `#s` per archimedean place.
  simp only [mulHeight₁_eq, prod_mulHeightAff_eq, totalWeight]
  rw [← Multiset.prod_replicate, ← Multiset.map_const, ← mul_assoc, ← Multiset.prod_map_mul]
  simp only [Function.const_apply]
  gcongr
  · exact finprod_nonneg fun _ ↦ by positivity
  · exact Multiset.prod_map_nonneg fun _ _ ↦ by positivity
  · exact Multiset.prod_map_le_prod_map₀ _ _ (fun _ _ ↦ zero_le_one.trans (le_max_right _ _))
      fun v _ ↦ harch v
  · exact finprod_le_finprod₀ (by fun_prop) (fun _ ↦ zero_le_one.trans (le_max_right _ _))
      (Function.HasFiniteMulSupport.prod (fun k ↦ hasFiniteMulSupport_max_iSup_nonarchAbsVal (y k))
        univ)
      fun v ↦ hnonarch (isNonarchimedean _ v.prop)

/-! ### The value of a linear form -/

/-- **The height of the value of a linear form.** The height of `∑ i, a i * x i` is at most
`Nat.card ι ^ totalWeight K` times the product of the affine heights of the coefficient tuple `a`
and of the point `x`.

The heights on the right have to be affine: scaling `a` by `c` multiplies the value by `c` and
leaves the projective height `mulHeight a` unchanged. The constant is attained over `ℚ`
(`Height.exists_mulHeight₁_sum_mul_eq`). -/
theorem mulHeight₁_sum_mul_le [Fintype ι] [Nonempty ι] (a x : ι → K) :
    mulHeight₁ (∑ i, a i * x i) ≤
      Nat.card ι ^ totalWeight K * (mulHeightAff a * mulHeightAff x) := by
  have key := mulHeight₁_sum_le_prod_mulHeightAff univ_nonempty (fun i ↦ a i * x i) ![a, x]
    fun v i _ ↦ by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, map_mul]
      gcongr
      · exact le_max_of_le_left (Finite.le_ciSup_of_le i le_rfl)
      · exact le_max_of_le_left (Finite.le_ciSup_of_le i le_rfl)
  simpa [Fin.prod_univ_two, Nat.card_eq_fintype_card] using key

/-- The logarithmic form of `Height.mulHeight₁_sum_mul_le`. It needs no nonemptiness hypothesis,
thanks to the junk value `log 0 = 0`. -/
theorem logHeight₁_sum_mul_le [Fintype ι] (a x : ι → K) :
    logHeight₁ (∑ i, a i * x i) ≤
      totalWeight K * log (Nat.card ι) + (logHeightAff a + logHeightAff x) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp only [univ_eq_empty, sum_empty, logHeight₁_zero]
    have := logHeightAff_nonneg a
    have := logHeightAff_nonneg x
    simp only [Nat.card_of_isEmpty, CharP.cast_eq_zero, log_zero, mul_zero, zero_add]
    positivity
  simp only [logHeight₁_eq_log_mulHeight₁, logHeightAff_eq_log_mulHeightAff]
  have hcard : (0 : ℝ) < Nat.card ι := by exact_mod_cast Nat.card_pos
  rw [← log_pow, ← log_mul (mulHeightAff_ne_zero a) (mulHeightAff_ne_zero x),
    ← log_mul (by positivity) (mul_ne_zero (mulHeightAff_ne_zero a) (mulHeightAff_ne_zero x))]
  exact log_le_log (mulHeight₁_pos _) (mulHeight₁_sum_mul_le a x)

/-- **The constant of `Height.mulHeight₁_sum_mul_le` is sharp.** Over `ℚ`, for every nonempty
finite `ι`, the tuples `a = x = 1` have affine height `1` while the value `∑ i, a i * x i` is
`Nat.card ι`, of height `Nat.card ι = Nat.card ι ^ totalWeight ℚ`. -/
theorem exists_mulHeight₁_sum_mul_eq [Fintype ι] [Nonempty ι] :
    ∃ a x : ι → ℚ, mulHeight₁ (∑ i, a i * x i) =
      Nat.card ι ^ totalWeight ℚ * (mulHeightAff a * mulHeightAff x) := by
  refine ⟨1, 1, ?_⟩
  have : NeZero (Fintype.card ι) := ⟨Fintype.card_ne_zero⟩
  simp [NumberField.totalWeight_eq_finrank, Nat.card_eq_fintype_card, Rat.mulHeight₁_natCast]

end Height

/-! ### The determinant -/

namespace Matrix

open Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {n : Type*} [Fintype n] [DecidableEq n]

/-- **The height of a determinant.** The height of `A.det` is at most
`(Nat.card n)! ^ totalWeight K` times the product of the affine heights of the columns of `A`.
This is the Leibniz expansion: the determinant is a sum of `(Nat.card n)!` signed products, each
taking one entry from every column.

The heights of the columns have to be affine: `A ↦ c • A` fixes the projective height of the
entries and multiplies the determinant by `c ^ Nat.card n` (see
`Height.exists_not_mulHeight₁_det_le`). -/
theorem mulHeight₁_det_le (A : Matrix n n K) :
    mulHeight₁ A.det ≤
      (Nat.card n).factorial ^ totalWeight K * ∏ j, mulHeightAff fun i ↦ A i j := by
  rw [det_apply]
  have key := mulHeight₁_sum_le_prod_mulHeightAff univ_nonempty
    (fun σ : Equiv.Perm n ↦ Equiv.Perm.sign σ • ∏ j, A (σ j) j) (fun j i ↦ A i j)
    fun v σ _ ↦ by
      rw [v.map_units_int_smul, map_prod]
      gcongr with j
      exact le_max_of_le_left (Finite.le_ciSup_of_le (σ j) le_rfl)
  simpa [Fintype.card_perm, Nat.card_eq_fintype_card] using key

/-- The logarithmic form of `Matrix.mulHeight₁_det_le`. -/
theorem logHeight₁_det_le (A : Matrix n n K) :
    logHeight₁ A.det ≤
      totalWeight K * log (Nat.card n).factorial + ∑ j, logHeightAff fun i ↦ A i j := by
  simp only [logHeight₁_eq_log_mulHeight₁, logHeightAff_eq_log_mulHeightAff]
  rw [← log_pow, ← log_prod fun _ _ ↦ mulHeightAff_ne_zero _,
    ← log_mul (by positivity) (prod_ne_zero_iff.mpr fun _ _ ↦ mulHeightAff_ne_zero _)]
  exact log_le_log (mulHeight₁_pos _) (mulHeight₁_det_le A)

/-- The height of a determinant against the affine height of the tuple of all entries:
`mulHeight₁ A.det ≤ (Nat.card n)! ^ totalWeight K * mulHeightAff (entries A) ^ Nat.card n`. -/
theorem mulHeight₁_det_le_mulHeightAff_pow (A : Matrix n n K) :
    mulHeight₁ A.det ≤ (Nat.card n).factorial ^ totalWeight K *
      mulHeightAff (fun p : n × n ↦ A p.1 p.2) ^ Nat.card n := by
  refine (mulHeight₁_det_le A).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rw [Nat.card_eq_fintype_card, ← card_univ, ← prod_const]
  exact prod_le_prod₀ (fun _ _ ↦ (mulHeightAff_pos _).le) fun j _ ↦
    mulHeightAff_comp_le (fun i ↦ (i, j)) (fun p : n × n ↦ A p.1 p.2)

/-- The logarithmic form of `Matrix.mulHeight₁_det_le_mulHeightAff_pow`. -/
theorem logHeight₁_det_le_logHeightAff (A : Matrix n n K) :
    logHeight₁ A.det ≤ totalWeight K * log (Nat.card n).factorial +
      Nat.card n * logHeightAff fun p : n × n ↦ A p.1 p.2 := by
  simp only [logHeight₁_eq_log_mulHeight₁, logHeightAff_eq_log_mulHeightAff]
  rw [← log_pow, ← log_pow, ← log_mul (by positivity) (pow_ne_zero _ (mulHeightAff_ne_zero _))]
  exact log_le_log (mulHeight₁_pos _) (mulHeight₁_det_le_mulHeightAff_pow A)

end Matrix

namespace Height

/-- **The determinant is not bounded by the projective height of the entries.** For every
constant `C` some `1 × 1` matrix over `ℚ` violates `mulHeight₁ A.det ≤ C * mulHeight (entries A)`:
a single entry has projective height `1`, while the determinant is that entry. This is why
`Matrix.mulHeight₁_det_le` uses affine heights. -/
theorem exists_not_mulHeight₁_det_le (C : ℝ) :
    ∃ A : Matrix (Fin 1) (Fin 1) ℚ,
      ¬ mulHeight₁ A.det ≤ C * mulHeight fun p : Fin 1 × Fin 1 ↦ A p.1 p.2 := by
  obtain ⟨m, hm⟩ := exists_nat_gt C
  refine ⟨!![((m + 1 : ℕ) : ℚ)], ?_⟩
  rw [Matrix.det_unique, mulHeight_eq_one_of_subsingleton, mul_one, not_le]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Rat.mulHeight₁_natCast]
  push_cast
  linarith

/-! ### Examples -/

/-- Over `ℚ`, the linear form with coefficients `![1, 1]` at the point `![1, 1]` takes the value
`2`, of height `2 = 2 ^ totalWeight ℚ * 1 * 1`: the constant of `Height.mulHeight₁_sum_mul_le`
is attained. -/
example :
    mulHeight₁ (∑ i, (![1, 1] : Fin 2 → ℚ) i * (![1, 1] : Fin 2 → ℚ) i) = 2 ∧
      (2 : ℝ) ^ totalWeight ℚ * (mulHeightAff (![1, 1] : Fin 2 → ℚ) *
        mulHeightAff (![1, 1] : Fin 2 → ℚ)) = 2 := by
  have h11 : (![1, 1] : Fin 2 → ℚ) = 1 := by
    ext i
    fin_cases i <;> rfl
  have h2 : mulHeight₁ (2 : ℚ) = 2 := by exact_mod_cast Rat.mulHeight₁_natCast 2
  refine ⟨?_, ?_⟩
  · norm_num [Fin.sum_univ_two, h2]
  · simp [h11, NumberField.totalWeight_eq_finrank]

end Height
