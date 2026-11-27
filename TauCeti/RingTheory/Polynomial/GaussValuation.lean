/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Lifts
import TauCeti.RingTheory.LocalRing.InfiniteResidueField
import TauCeti.RingTheory.Valuation.Polynomial

/-!
# Gauss valuation of polynomials

Given a valuation `v : Valuation R Γ₀` and a radius `r : Γ₀`, `Polynomial.gaussValuation p v r` is
the maximum of `v (p.coeff i) * r ^ i` over all `i : ℕ`. Unlike `Polynomial.gaussNorm`, which
targets real-valued absolute values `AbsoluteValue R ℝ`, `Polynomial.gaussValuation` applies to
arbitrary value monoids and groups `Γ₀`.

## Main results

* `Polynomial.gaussValuation_le_iff`, `Polynomial.gaussValuation_add_le`,
  `Polynomial.valuation_eval_le_gaussValuation`: coefficient characterization, ultrametric
  addition bound, and evaluation bound `v (p.eval x) ≤ p.gaussValuation v r` for `v x ≤ r`.
* `Polynomial.gaussValuation_mul`: multiplicativity `(p * q).gaussValuation v r =
  p.gaussValuation v r * q.gaussValuation v r`.
* `Polynomial.gaussValuation_eq_mul_prod_roots`,
  `Polynomial.valuation_eval_eq_gaussValuation_of_forall_roots_ne`: root-product formula for split
  polynomials and sphere-evaluation equality away from root valuations.
* `Polynomial.exists_forall_valuation_eval_eq_gaussValuation`: simultaneous attainment of the Gauss
  valuation at a point of prescribed valuation `v c` over valued fields with infinite residue field.

## References

* S. Bosch, U. Güntzer, and R. Remmert, *Non-Archimedean Analysis*, §5.1.
* L. Alpöge, `New.Selmer.gaussVal` and `New.Selmer.gaussVal_eq_mul_prod_roots` in
  `src/Lib/General/NumberTheory/GaussValuation.lean`,
  <https://github.com/leanprover-community/riemann-hypothesis/tree/dba5aded4bf7>.
-/

public section

namespace Polynomial

section Ring

variable {R Γ₀ : Type*} [Ring R]

section Monoid

variable [LinearOrderedCommMonoidWithZero Γ₀]

/-- The Gauss valuation of a polynomial `p` at a valuation `v` and radius `r`:
the maximum of `v (p.coeff i) * r ^ i` over all `i ∈ p.support` (and `0` when `p = 0`). -/
def gaussValuation (p : R[X]) (v : Valuation R Γ₀) (r : Γ₀) : Γ₀ :=
  p.support.fold max 0 fun i ↦ v (p.coeff i) * r ^ i

/-- Definitional unfolding of `Polynomial.gaussValuation`. -/
theorem gaussValuation_def (p : R[X]) (v : Valuation R Γ₀) (r : Γ₀) :
    p.gaussValuation v r = p.support.fold max 0 fun i ↦ v (p.coeff i) * r ^ i := by
  rfl

variable (v : Valuation R Γ₀) (r : Γ₀)

/-- The Gauss valuation of `0` is `0`. -/
@[simp]
theorem gaussValuation_zero : (0 : R[X]).gaussValuation v r = 0 := by
  simp [gaussValuation_def]

/-- The Gauss valuation of `p` is at most `c` iff every weighted coefficient
`v (p.coeff i) * r ^ i` is at most `c`. -/
theorem gaussValuation_le_iff {p : R[X]} {c : Γ₀} :
    p.gaussValuation v r ≤ c ↔ ∀ i, v (p.coeff i) * r ^ i ≤ c := by
  rw [gaussValuation_def, Finset.fold_max_le]
  refine ⟨fun ⟨_, h⟩ i ↦ ?_, fun h ↦ ⟨zero_le, fun i _ ↦ h i⟩⟩
  by_cases hi : i ∈ p.support
  · exact h i hi
  · rw [notMem_support_iff.mp hi, map_zero, zero_mul]
    exact zero_le

/-- Each weighted coefficient `v (p.coeff i) * r ^ i` is bounded above by the Gauss valuation. -/
theorem le_gaussValuation (p : R[X]) (i : ℕ) :
    v (p.coeff i) * r ^ i ≤ p.gaussValuation v r :=
  (gaussValuation_le_iff v r).mp le_rfl i

/-- If `p.gaussValuation v r ≠ 0`, some index in `p.support` attains the Gauss valuation. -/
theorem exists_eq_gaussValuation {p : R[X]} (hp : p.gaussValuation v r ≠ 0) :
    ∃ i ∈ p.support, v (p.coeff i) * r ^ i = p.gaussValuation v r := by
  have hne : p.support.Nonempty := by
    by_contra h
    exact hp (by simp [gaussValuation_def, Finset.not_nonempty_iff_eq_empty.mp h])
  obtain ⟨i, hi, hmax⟩ := p.support.exists_max_image (fun i ↦ v (p.coeff i) * r ^ i) hne
  exact ⟨i, hi, le_antisymm (le_gaussValuation v r p i)
    (by rw [gaussValuation_def, Finset.fold_max_le]; exact ⟨zero_le, fun j hj ↦ hmax j hj⟩)⟩

/-- The Gauss valuation of a constant polynomial `C a` is `v a`. -/
@[simp]
theorem gaussValuation_C (a : R) : (C a).gaussValuation v r = v a :=
  le_antisymm ((gaussValuation_le_iff v r).mpr fun i ↦ by cases i <;> simp)
    (by simpa using le_gaussValuation v r (C a) 0)

/-- The Gauss valuation of `1` is `1`. -/
@[simp]
theorem gaussValuation_one : (1 : R[X]).gaussValuation v r = 1 := by
  rw [← C_1, gaussValuation_C, map_one]

/-- The Gauss valuation of a monomial `monomial n a` at radius `r` is `v a * r ^ n`. -/
@[simp]
theorem gaussValuation_monomial (n : ℕ) (a : R) :
    (monomial n a).gaussValuation v r = v a * r ^ n := by
  refine le_antisymm ((gaussValuation_le_iff v r).mpr fun i ↦ ?_) ?_
  · rw [coeff_monomial, Finsupp.single_apply]
    split_ifs with h
    · subst h; exact le_rfl
    · simp
  · simpa [coeff_monomial] using le_gaussValuation v r (monomial n a) n

/-- The Gauss valuation of `X` at radius `r` is `r`. -/
@[simp]
theorem gaussValuation_X : (X : R[X]).gaussValuation v r = r := by
  rw [← monomial_one_one_eq_X, gaussValuation_monomial, map_one, one_mul, pow_one]

/-- The Gauss valuation of `X - C a` at radius `r` is `max r (v a)`. -/
@[simp]
theorem gaussValuation_X_sub_C (a : R) : (X - C a).gaussValuation v r = max r (v a) :=
  le_antisymm ((gaussValuation_le_iff v r).mpr fun i ↦ by
      rcases i with _ | _ | n <;> simp [coeff_X])
    (max_le (by have h := le_gaussValuation v r (X - C a) 1; simpa [coeff_sub, coeff_X] using h)
      (by have h := le_gaussValuation v r (X - C a) 0; simpa [coeff_sub, coeff_X] using h))

/-- The Gauss valuation at radius `0` is the valuation of the constant term. -/
@[simp]
theorem gaussValuation_at_zero (p : R[X]) : p.gaussValuation v 0 = v (p.coeff 0) :=
  le_antisymm ((gaussValuation_le_iff v 0).mpr fun i ↦ by cases i <;> simp)
    (by simpa using le_gaussValuation v 0 p 0)

/-- The Gauss valuation satisfies the ultrametric triangle inequality. -/
theorem gaussValuation_add_le (p q : R[X]) :
    (p + q).gaussValuation v r ≤ max (p.gaussValuation v r) (q.gaussValuation v r) := by
  refine (gaussValuation_le_iff v r).mpr fun i ↦ ?_
  rw [coeff_add]
  refine (mul_le_mul_left (v.map_add (p.coeff i) (q.coeff i)) _).trans ?_
  rcases max_choice (v (p.coeff i)) (v (q.coeff i)) with h | h <;> rw [h]
  · exact le_max_of_le_left (le_gaussValuation v r p i)
  · exact le_max_of_le_right (le_gaussValuation v r q i)

/-- Scaling by a constant scales the Gauss valuation by `v a`. -/
theorem gaussValuation_C_mul (a : R) (p : R[X]) :
    (C a * p).gaussValuation v r = v a * p.gaussValuation v r := by
  refine le_antisymm ((gaussValuation_le_iff v r).mpr fun i ↦ by
      rw [coeff_C_mul, map_mul, mul_assoc]; exact mul_le_mul_right (le_gaussValuation v r p i) _) ?_
  rcases eq_or_ne (p.gaussValuation v r) 0 with hp | hp; · simp [hp]
  obtain ⟨i, -, hi⟩ := exists_eq_gaussValuation v r hp
  calc v a * p.gaussValuation v r
      = v ((C a * p).coeff i) * r ^ i := by rw [← hi, coeff_C_mul, map_mul, mul_assoc]
    _ ≤ (C a * p).gaussValuation v r := le_gaussValuation v r (C a * p) i

/-- Evaluating `p` at `x` with `v x ≤ r` gives valuation at most `p.gaussValuation v r`. -/
theorem valuation_eval_le_gaussValuation (p : R[X]) {x : R} (hx : v x ≤ r) :
    v (p.eval x) ≤ p.gaussValuation v r := by
  rw [eval_eq_sum]
  refine v.map_sum_le fun i _ ↦ ?_
  rw [map_mul, map_pow]
  exact (mul_le_mul_right (pow_le_pow_left' hx i) _).trans (le_gaussValuation v r p i)

/-- Rescaling the variable by `C a * X` transforms the radius-`1` Gauss valuation to the
radius-`v a` Gauss valuation. -/
theorem gaussValuation_one_comp_C_mul_X (p : R[X]) (a : R) :
    (p.comp (C a * X)).gaussValuation v 1 = p.gaussValuation v (v a) :=
  le_antisymm ((gaussValuation_le_iff v 1).mpr fun i ↦ by
      rw [one_pow, mul_one, comp_C_mul_X_coeff, map_mul, map_pow]
      exact le_gaussValuation v (v a) p i)
    ((gaussValuation_le_iff v (v a)).mpr fun i ↦ by
      have h1 := le_gaussValuation v 1 (p.comp (C a * X)) i
      rwa [one_pow, mul_one, comp_C_mul_X_coeff, map_mul, map_pow] at h1)

/-- The least index attaining a nonzero Gauss valuation has strictly smaller weighted coefficients
at all lower indices. -/
private lemma exists_min_eq_gaussValuation {p : R[X]} (hp : p.gaussValuation v r ≠ 0) :
    ∃ i₀, v (p.coeff i₀) * r ^ i₀ = p.gaussValuation v r ∧
      ∀ i < i₀, v (p.coeff i) * r ^ i < p.gaussValuation v r := by
  classical
  set s := p.support.filter fun i ↦ v (p.coeff i) * r ^ i = p.gaussValuation v r
  have hs : s.Nonempty := let ⟨i, hi, h⟩ := exists_eq_gaussValuation v r hp
    ⟨i, Finset.mem_filter.mpr ⟨hi, h⟩⟩
  refine ⟨s.min' hs, (Finset.mem_filter.mp (Finset.min'_mem s hs)).2, fun i hi ↦ ?_⟩
  refine lt_of_le_of_ne (le_gaussValuation v r p i) fun heq ↦ ?_
  have hmem : i ∈ s := Finset.mem_filter.mpr
    ⟨mem_support_iff.mpr fun h0 ↦ by simp [h0] at heq; exact hp heq.symm, heq⟩
  exact (not_le_of_gt hi) (Finset.min'_le s i hmem)

end Monoid

/-- **Gauss's lemma for valuations**: the Gauss valuation of a product of polynomials is the
product of their Gauss valuations. -/
theorem gaussValuation_mul [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation R Γ₀) (r : Γ₀) (p q : R[X]) :
    (p * q).gaussValuation v r = p.gaussValuation v r * q.gaussValuation v r := by
  rcases eq_or_ne r 0 with rfl | hr; · simp [mul_coeff_zero]
  refine le_antisymm ((gaussValuation_le_iff v r).mpr fun k ↦ ?_) ?_
  · have hrk : 0 < r ^ k := pos_iff_ne_zero.mpr (pow_ne_zero k hr)
    rw [coeff_mul, ← le_div_iff₀ hrk]
    refine v.map_sum_le fun x hx ↦ (le_div_iff₀ hrk).mpr ?_
    rw [map_mul, ← Finset.mem_antidiagonal.mp hx, pow_add, mul_mul_mul_comm]
    exact mul_le_mul' (le_gaussValuation v r p x.1) (le_gaussValuation v r q x.2)
  rcases eq_or_ne (p.gaussValuation v r) 0 with hp | hp; · simp [hp]
  rcases eq_or_ne (q.gaussValuation v r) 0 with hq | hq; · simp [hq]
  -- Pick the least attaining indices `i₀` for `p` and `j₀` for `q`; then `(i₀, j₀)` strictly
  -- dominates every other antidiagonal term in `(p * q).coeff (i₀ + j₀)`.
  obtain ⟨i₀, hi₀, hlt_p⟩ := exists_min_eq_gaussValuation v r hp
  obtain ⟨j₀, hj₀, hlt_q⟩ := exists_min_eq_gaussValuation v r hq
  have hlead : v (p.coeff i₀ * q.coeff j₀) * r ^ (i₀ + j₀) =
      p.gaussValuation v r * q.gaussValuation v r := by
    rw [map_mul, pow_add, mul_mul_mul_comm, hi₀, hj₀]
  have hlead_ne : v (p.coeff i₀ * q.coeff j₀) ≠ 0 := fun h0 ↦ by
    rw [h0, zero_mul] at hlead; exact mul_ne_zero hp hq hlead.symm
  have hrest_lt : v (∑ x ∈ (Finset.antidiagonal (i₀ + j₀)).erase (i₀, j₀),
      p.coeff x.1 * q.coeff x.2) < v (p.coeff i₀ * q.coeff j₀) := by
    refine v.map_sum_lt hlead_ne fun x hx ↦ lt_of_mul_lt_mul_right' (a := r ^ (i₀ + j₀)) ?_
    have hne : x ≠ (i₀, j₀) := (Finset.mem_erase.mp hx).1
    have hsum : x.1 + x.2 = i₀ + j₀ := Finset.mem_antidiagonal.mp (Finset.mem_erase.mp hx).2
    rw [hlead, map_mul, ← hsum, pow_add, mul_mul_mul_comm]
    rcases lt_or_ge x.1 i₀ with h1 | h1
    · exact (mul_le_mul_right (le_gaussValuation v r q x.2) _).trans_lt <|
        lt_of_le_of_ne (mul_le_mul_left (hlt_p x.1 h1).le _) fun heq ↦
          (hlt_p x.1 h1).ne (mul_right_cancel₀ hq heq)
    · have h2 : x.2 < j₀ := by
        have hne' : x.1 ≠ i₀ ∨ x.2 ≠ j₀ := by contrapose! hne; exact Prod.ext hne.1 hne.2
        omega
      exact (mul_le_mul_left (le_gaussValuation v r p x.1) _).trans_lt <|
        lt_of_le_of_ne (mul_le_mul_right (hlt_q x.2 h2).le _) fun heq ↦
          (hlt_q x.2 h2).ne (mul_left_cancel₀ hp heq)
  have hcoeff : v ((p * q).coeff (i₀ + j₀)) = v (p.coeff i₀ * q.coeff j₀) := by
    rw [coeff_mul, ← Finset.add_sum_erase (Finset.antidiagonal (i₀ + j₀))
      (fun x ↦ p.coeff x.1 * q.coeff x.2)
      ((Finset.mem_antidiagonal (n := i₀ + j₀) (a := (i₀, j₀))).mpr rfl)]
    exact v.map_add_eq_of_lt_left hrest_lt
  calc p.gaussValuation v r * q.gaussValuation v r
      = v ((p * q).coeff (i₀ + j₀)) * r ^ (i₀ + j₀) := by rw [hcoeff, hlead]
    _ ≤ (p * q).gaussValuation v r := le_gaussValuation v r (p * q) (i₀ + j₀)

end Ring

section CommRing

variable {R Γ₀ : Type*} [CommRing R]

/-- The Gauss valuation of a multiset product of polynomials is the product of their Gauss
valuations. -/
theorem gaussValuation_multiset_prod [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation R Γ₀) (r : Γ₀) (s : Multiset R[X]) :
    s.prod.gaussValuation v r = (s.map fun p ↦ p.gaussValuation v r).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons p s ih => simp [gaussValuation_mul, ih]

/-- For a split polynomial `p`, the Gauss valuation at radius `r` is the valuation of the leading
coefficient times the product of `max r (v α)` over all roots `α` of `p`. -/
theorem gaussValuation_eq_mul_prod_roots [IsDomain R] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation R Γ₀) (p : R[X]) (hp : p.Splits) (r : Γ₀) :
    p.gaussValuation v r = v p.leadingCoeff * (p.roots.map fun α ↦ max r (v α)).prod := by
  conv_lhs => rw [hp.eq_prod_roots]
  rw [gaussValuation_C_mul, gaussValuation_multiset_prod, Multiset.map_map]; simp

/-- If a split polynomial `p` has no root of valuation `v x`, then `v (p.eval x)` equals the Gauss
valuation `p.gaussValuation v (v x)`. -/
theorem valuation_eval_eq_gaussValuation_of_forall_roots_ne [IsDomain R]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀) (p : R[X]) (hp : p.Splits) {x : R}
    (hroots : ∀ α ∈ p.roots, v α ≠ v x) :
    v (p.eval x) = p.gaussValuation v (v x) := by
  rw [valuation_eval_eq_mul_prod_roots v p hp x, gaussValuation_eq_mul_prod_roots v p hp (v x)]
  congr 2; refine Multiset.map_congr rfl fun α hα ↦ ?_
  rcases lt_or_gt_of_ne (hroots α hα) with hlt | hgt
  · rw [v.map_sub_eq_of_lt_left hlt, max_eq_left hlt.le]
  · rw [v.map_sub_eq_of_lt_right hgt, max_eq_right hgt.le]

end CommRing

section GenericEvaluation

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

/-- Every polynomial `p` over a valued field `K` factors as `C c * q.map _` where
`v c = p.gaussValuation v 1` and `q` has coefficients in `v.valuationSubring` with nonzero
reduction modulo the maximal ideal. -/
theorem exists_eq_C_mul_map_residue_ne_zero (p : K[X]) :
    ∃ (c : K) (q : v.valuationSubring[X]),
      v c = p.gaussValuation v 1 ∧
      p = C c * q.map (algebraMap v.valuationSubring K) ∧
      q.map (IsLocalRing.residue v.valuationSubring) ≠ 0 := by
  rcases eq_or_ne p 0 with rfl | hp
  · exact ⟨0, 1, by simp, by simp, by simp⟩
  have hpos : p.gaussValuation v 1 ≠ 0 := fun h0 ↦ by
    obtain ⟨i, hi⟩ := support_nonempty.mpr hp
    have hle := le_gaussValuation v 1 p i
    rw [h0, one_pow, mul_one] at hle
    exact mem_support_iff.mp hi (v.zero_iff.mp (le_antisymm hle zero_le))
  obtain ⟨i₀, hi₀, hc_val⟩ := exists_eq_gaussValuation v 1 hpos
  rw [one_pow, mul_one] at hc_val
  set c : K := p.coeff i₀
  have hc_ne : c ≠ 0 := mem_support_iff.mp hi₀
  have hmem : ∀ i, c⁻¹ * p.coeff i ∈ v.valuationSubring := fun i ↦ by
    rw [Valuation.mem_valuationSubring_iff, map_mul, map_inv₀, hc_val, inv_mul_eq_div]
    exact div_le_one_of_le₀ (by simpa using le_gaussValuation v 1 p i) zero_le
  have hlifts : C c⁻¹ * p ∈ lifts (algebraMap v.valuationSubring K) :=
    (lifts_iff_coeff_lifts _).mpr fun i ↦ by
      rw [coeff_C_mul]
      exact ⟨⟨c⁻¹ * p.coeff i, hmem i⟩, rfl⟩
  obtain ⟨q, hq⟩ := (mem_lifts _).mp hlifts
  refine ⟨c, q, hc_val, ?_, fun hzero ↦ ?_⟩
  · rw [hq, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hc_ne, C_1, one_mul]
  · have hcoeff : (q.map (IsLocalRing.residue v.valuationSubring)).coeff i₀ = 0 := by simp [hzero]
    rw [coeff_map] at hcoeff
    have hqi : q.coeff i₀ = 1 := by
      apply Subtype.ext
      have hmap := congrArg (fun f ↦ f.coeff i₀) hq
      rw [coeff_map, coeff_C_mul] at hmap
      simpa [c, inv_mul_cancel₀ hc_ne] using hmap
    exact one_ne_zero (by rwa [hqi, map_one] at hcoeff)

/-- Over a valued field with infinite residue field, finitely many polynomials simultaneously
attain their Gauss valuations at a point of prescribed valuation `v c`. -/
theorem exists_forall_valuation_eval_eq_gaussValuation
    [Infinite (IsLocalRing.ResidueField v.valuationSubring)] {ι : Type*}
    (s : Finset ι) (p : ι → K[X]) (c : K) :
    ∃ x : K, v x = v c ∧ ∀ j ∈ s, v ((p j).eval x) = (p j).gaussValuation v (v c) := by
  classical
  choose a q ha hfac hres using fun j : ι ↦
    exists_eq_C_mul_map_residue_ne_zero v ((p j).comp (C c * X))
  have hF : ∀ o ∈ insert none (s.image some),
      (Option.elim' X q o).map (IsLocalRing.residue v.valuationSubring) ≠ 0 := by
    intro o ho
    rcases Finset.mem_insert.mp ho with rfl | ho'
    · simp
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ho'
      exact hres j
  obtain ⟨u, hu⟩ := exists_forall_isUnit_eval (insert none (s.image some)) (Option.elim' X q) hF
  have hval_unit : ∀ w : v.valuationSubring, IsUnit w → v (w : K) = 1 := fun _ hw ↦
    (Valuation.valuationSubring.integers v).one_of_isUnit hw
  refine ⟨c * (u : K),
    by rw [map_mul, hval_unit u (by simpa using hu none (Finset.mem_insert_self none _)), mul_one],
    fun j hj ↦ ?_⟩
  have hqu : IsUnit ((q j).eval u) := by
    simpa using hu (some j) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem some hj))
  have heval : (p j).eval (c * (u : K)) = a j * (((q j).eval u : v.valuationSubring) : K) := by
    have h1 : (p j).eval (c * (u : K)) = ((p j).comp (C c * X)).eval (u : K) := by simp [eval_comp]
    rw [h1, hfac j, eval_mul, eval_C, eval_map]
    exact congrArg (a j * ·) (eval₂_at_apply (algebraMap v.valuationSubring K) u)
  rw [heval, map_mul, hval_unit _ hqu, mul_one, ha j, gaussValuation_one_comp_C_mul_X]

end GenericEvaluation

end Polynomial
