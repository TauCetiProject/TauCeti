/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.NNRat.BigOperators
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import TauCeti.Data.Finsupp.Weight
public import TauCeti.RingTheory.MvPolynomial.HasseDeriv.Taylor

/-!
# Weighted indices of multivariate polynomials

The index at a point with natural weights `r` is the infimum of `∑ j, d j / r j` over
nonzero Hasse jets. Thus an index lower bound specifies exactly which jets must vanish.
For a nonzero polynomial over a ring the infimum is attained, and positive weights make
it finite. The reciprocal weights distinguish this index from a weighted total degree.

Division takes place in `ℝ≥0∞`: a positive exponent in a coordinate of weight zero has
infinite cost. The constant jet has cost zero, even when some weights vanish.

The index behaves like an order of vanishing. Over a semiring without zero divisors it is
additive on products, because the lowest weighted homogeneous components of the Taylor shifts
multiply to a nonzero component of the product. A Hasse derivative `∂^d` lowers it by at most
the weight of `d`, scaling all weights by `c` divides it by `c`, and renaming the variables
injectively preserves it. A univariate polynomial placed in one coordinate has its root
multiplicity divided by that coordinate's weight as index. These rules are the calculus of
indices used for auxiliary polynomials in the proof of Roth's theorem.

## Main results

* `Finsupp.weight_inv_natCast_eq_ofReal_sum_div`: for `d ≤ r`, the reciprocal weight of `d`
  is the real sum `∑ j, d j / r j`.
* `MvPolynomial.ofReal_le_weightedIndex_of_eval_hasseDeriv_eq_zero`: for a polynomial with
  partial degrees at most `r`, the index is at least a real threshold `t` once the jets `∂^d P`
  with `d ≤ r` and `∑ j, d j / r j < t` vanish.
* `MvPolynomial.le_sum_div_of_le_weightedIndex`: a nonzero jet `∂^d P` at a point where the
  index is at least `t` has `d ≤ r` and real weight `t ≤ ∑ j, d j / r j`.
* `MvPolynomial.weightedIndex_mul`: `Ind(P Q) = Ind(P) + Ind(Q)` without zero divisors.
* `MvPolynomial.le_weightedIndex_det`: the index of a determinant is at least the sum over the
  columns of lower bounds for the indices of their entries.
* `MvPolynomial.weightedIndex_le_weightedIndex_hasseDeriv_add`:
  `Ind(P) ≤ Ind(∂^d P) + ∑ j, d j / r j`.
* `MvPolynomial.weightedIndex_smul_weight`: the index for the weights `c • r` is the index
  for `r` divided by `c`.
* `MvPolynomial.weightedIndex_rename`: renaming along an injective map preserves the index.
* `MvPolynomial.weightedIndex_toMvPolynomial`: a univariate polynomial placed in the
  coordinate `i` has index `rootMultiplicity / r i`.
* `MvPolynomial.exists_hasseDeriv_eval_ne_zero`: if a polynomial `P` has finite index at `b`,
  some Hasse derivative `Q = ∂^d P` satisfies `Q(b) ≠ 0` and
  `Ind_a(P) - Ind_b(P) ≤ Ind_a(Q)` at every other point `a`, and has the same partial degree
  bounds and coefficients at most `2 ^ ∑ᵢ rᵢ` times as large.

## References

* L. Pottmeyer, [*Diophantine Approximation*](https://esaga.uni-due.de/f/lukas.pottmeyer/DioApp.pdf)
  (2022), §2.6, Definition 2.6.2, Example 2.6.3 and Exercise 2.19; §3.4, Lemma 3.4.3 and
  §§3.4.6–3.4.7; §3.5, Lemma 3.5.7.
* The determinant bound `MvPolynomial.le_weightedIndex_det` follows `MvPolynomial.le_index_det` in
  `DiophantineApproximation/RothDeterminant.lean` of Ralf Stephan's `rwst/Subspace-Theorems`,
  snapshot `c26d909dc48cf7fe` (Apache 2.0).
-/

public section

namespace MvPolynomial

open scoped ENNReal NNReal

variable {σ R : Type*}

section Semiring

variable [CommSemiring R]

/-- The weighted index is the least reciprocal-weighted order of a nonzero Hasse jet;
the infimum of the empty set is `⊤`. -/
noncomputable def weightedIndex (r : σ → ℕ) (a : σ → R) (P : MvPolynomial σ R) : ℝ≥0∞ :=
  ⨅ (d : σ →₀ ℕ) (_ : eval a (hasseDeriv d P) ≠ 0),
    d.weight (fun j ↦ (r j : ℝ≥0∞)⁻¹)

/-- The defining infimum, expressed as a sum of ratios over the derivative's support. -/
theorem weightedIndex_def (r : σ → ℕ) (a : σ → R) (P : MvPolynomial σ R) :
    weightedIndex r a P = ⨅ (d : σ →₀ ℕ) (_ : eval a (hasseDeriv d P) ≠ 0),
      ∑ j ∈ d.support, (d j : ℝ≥0∞) / (r j : ℝ≥0∞) := by
  simp only [weightedIndex, Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul,
    div_eq_mul_inv]

/-- A nonzero jet bounds the index from above by its weight. -/
theorem weightedIndex_le {r : σ → ℕ} {a : σ → R} {P : MvPolynomial σ R}
    {d : σ →₀ ℕ} (hd : eval a (hasseDeriv d P) ≠ 0) :
    weightedIndex r a P ≤ d.weight (fun j ↦ (r j : ℝ≥0∞)⁻¹) :=
  iInf_le_of_le d (iInf_le_of_le hd le_rfl)

/-- For `d ≤ r`, the reciprocal weight of `d` defining the index is the real sum
`∑ᵢ dᵢ / rᵢ`. -/
theorem _root_.Finsupp.weight_inv_natCast_eq_ofReal_sum_div [Fintype σ] {r : σ → ℕ}
    {d : σ →₀ ℕ} (hdr : ∀ i, d i ≤ r i) :
    d.weight (fun j ↦ (r j : ℝ≥0∞)⁻¹) = ENNReal.ofReal (∑ i, (d i : ℝ) / r i) := by
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ ↦ by positivity, Finsupp.weight_apply,
    Finsupp.sum_fintype _ _ (by simp)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rcases Nat.eq_zero_or_pos (d i) with h | h
  · simp [h]
  · rw [ENNReal.ofReal_div_of_pos (Nat.cast_pos.2 (h.trans_le (hdr i))),
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, nsmul_eq_mul, div_eq_mul_inv]

/-- A nonzero jet of a polynomial with partial degrees `degreeOf i P ≤ r i` and index at least
`t` satisfies `d ≤ r` and has weight `t ≤ ∑ᵢ dᵢ / rᵢ`, computed in `ℝ`. -/
theorem le_sum_div_of_le_weightedIndex [Fintype σ] {P : MvPolynomial σ R} {r : σ → ℕ}
    (hdeg : ∀ i, P.degreeOf i ≤ r i) {a : σ → R} {t : ℝ}
    (ht : ENNReal.ofReal t ≤ weightedIndex r a P) {d : σ →₀ ℕ}
    (hd : eval a (hasseDeriv d P) ≠ 0) :
    (∀ i, d i ≤ r i) ∧ t ≤ ∑ i, (d i : ℝ) / r i := by
  have hdr (i : σ) : d i ≤ r i := by
    by_contra h
    exact hd (by rw [hasseDeriv_eq_zero_of_degreeOf_lt (i := i) (by have := hdeg i; omega),
      map_zero])
  refine ⟨hdr, ?_⟩
  exact (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun i _ ↦ by positivity)).1
    (ht.trans ((weightedIndex_le hd).trans_eq (Finsupp.weight_inv_natCast_eq_ofReal_sum_div hdr)))

/-- An index lower bound is equivalent to the vanishing of all jets of strictly smaller
weight. The strict inequality also covers the threshold `⊤`. -/
theorem le_weightedIndex_iff (r : σ → ℕ) (a : σ → R) (P : MvPolynomial σ R)
    (t : ℝ≥0∞) :
    t ≤ weightedIndex r a P ↔ ∀ d : σ →₀ ℕ,
      (∑ j ∈ d.support, (d j : ℝ≥0∞) / (r j : ℝ≥0∞)) < t →
        eval a (hasseDeriv d P) = 0 := by
  rw [weightedIndex_def]
  constructor
  · intro h d hd
    by_contra hn
    exact (not_lt_of_ge (h.trans (iInf_le_of_le d (iInf_le_of_le hn le_rfl)))) hd
  · intro h
    refine le_iInf fun d ↦ le_iInf fun hd ↦ ?_
    exact le_of_not_gt fun ht ↦ hd (h d ht)

/-- For a polynomial with partial degrees `degreeOf i P ≤ r i`, the index is at least a real
threshold `t` as soon as the jets `∂^d P (a)` vanish for every `d ≤ r` of real weight
`∑ᵢ dᵢ / rᵢ < t`. -/
theorem ofReal_le_weightedIndex_of_eval_hasseDeriv_eq_zero [Fintype σ] {P : MvPolynomial σ R}
    {r : σ → ℕ} (hdeg : ∀ i, P.degreeOf i ≤ r i) {a : σ → R} {t : ℝ}
    (h : ∀ d : σ →₀ ℕ, (∀ i, d i ≤ r i) → ∑ i, (d i : ℝ) / r i < t →
      eval a (hasseDeriv d P) = 0) :
    ENNReal.ofReal t ≤ weightedIndex r a P := by
  refine le_iInf fun d ↦ le_iInf fun hd ↦ le_of_not_gt fun hlt ↦ hd ?_
  by_cases hdr : ∀ i, d i ≤ r i
  · rw [Finsupp.weight_inv_natCast_eq_ofReal_sum_div hdr] at hlt
    exact h d hdr (ENNReal.ofReal_lt_ofReal_iff'.mp hlt).1
  · push Not at hdr
    obtain ⟨j, hj⟩ := hdr
    rw [hasseDeriv_eq_zero_of_degreeOf_lt ((hdeg j).trans_lt hj), map_zero]

@[simp]
theorem weightedIndex_zero (r : σ → ℕ) (a : σ → R) :
    weightedIndex r a (0 : MvPolynomial σ R) = ⊤ := by
  simp [weightedIndex]

/-- The index of a sum is at least the smaller index. -/
theorem min_weightedIndex_le_add (r : σ → ℕ) (a : σ → R) (P Q : MvPolynomial σ R) :
    min (weightedIndex r a P) (weightedIndex r a Q) ≤ weightedIndex r a (P + Q) := by
  rw [le_weightedIndex_iff]
  intro d hd
  have hP := (le_weightedIndex_iff r a P _).mp le_rfl d (hd.trans_le (min_le_left _ _))
  have hQ := (le_weightedIndex_iff r a Q _).mp le_rfl d (hd.trans_le (min_le_right _ _))
  simp [hP, hQ]

/-- The index of a finite sum is at least every common lower bound for the indices of the
summands. -/
theorem le_weightedIndex_sum {ι : Type*} (r : σ → ℕ) (a : σ → R) {s : Finset ι}
    {P : ι → MvPolynomial σ R} {t : ℝ≥0∞} (h : ∀ i ∈ s, t ≤ weightedIndex r a (P i)) :
    t ≤ weightedIndex r a (∑ i ∈ s, P i) := by
  rw [le_weightedIndex_iff]
  intro d hd
  rw [map_sum, map_sum]
  exact Finset.sum_eq_zero fun i hi ↦ (le_weightedIndex_iff r a (P i) t).mp (h i hi) d hd

/-- Injective coefficient maps preserve the index when the center is mapped as well. -/
theorem weightedIndex_map {S : Type*} [CommSemiring S] (f : R →+* S)
    (hf : Function.Injective f) (r : σ → ℕ) (a : σ → R) (P : MvPolynomial σ R) :
    weightedIndex r (fun j ↦ f (a j)) (map f P) = weightedIndex r a P := by
  apply eq_of_forall_le_iff
  intro t
  simp only [le_weightedIndex_iff, ← coeff_taylor, ← map_taylor, coeff_map,
    map_eq_zero_iff f hf]

/-- Taylor translation of the polynomial translates the center of its index. -/
theorem weightedIndex_taylor (r : σ → ℕ) (a b : σ → R) (P : MvPolynomial σ R) :
    weightedIndex r b (taylor a P) = weightedIndex r (b + a) P := by
  apply eq_of_forall_le_iff
  intro t
  simp only [le_weightedIndex_iff, ← coeff_taylor, taylor_taylor]

/-- The index is attained by a nonzero Taylor coefficient whenever the Taylor shift is
nonzero. This statement also permits zero weights and infinite index. -/
theorem exists_weightedIndex_eq_weight {r : σ → ℕ} {a : σ → R}
    {P : MvPolynomial σ R} (hP : taylor a P ≠ 0) :
    ∃ d : σ →₀ ℕ, eval a (hasseDeriv d P) ≠ 0 ∧
      weightedIndex r a P = d.weight (fun j ↦ (r j : ℝ≥0∞)⁻¹) := by
  classical
  obtain ⟨d, hd, hmin⟩ := (taylor a P).support.exists_min_image
    (fun d ↦ d.weight (fun j ↦ (r j : ℝ≥0∞)⁻¹)) (support_nonempty.mpr hP)
  have hjet : eval a (hasseDeriv d P) ≠ 0 := by
    simpa only [mem_support_iff, coeff_taylor] using hd
  refine ⟨d, hjet, (weightedIndex_le hjet).antisymm ?_⟩
  refine le_iInf fun e ↦ le_iInf fun he ↦ hmin e ?_
  simpa only [mem_support_iff, coeff_taylor] using he

/-- A polynomial whose Taylor shift vanishes has infinite index. Over a ring this happens only
for the zero polynomial. -/
theorem weightedIndex_eq_top_of_taylor_eq_zero (r : σ → ℕ) {a : σ → R}
    {P : MvPolynomial σ R} (hP : taylor a P = 0) : weightedIndex r a P = ⊤ :=
  top_unique <| le_iInf₂ fun d hd ↦ (hd (by rw [← coeff_taylor, hP]; simp)).elim

/-- Index zero detects nonvanishing at the center, without a positivity condition on the
weights. -/
@[simp]
theorem weightedIndex_eq_zero_iff (r : σ → ℕ) (a : σ → R) (P : MvPolynomial σ R) :
    weightedIndex r a P = 0 ↔ eval a P ≠ 0 := by
  constructor
  · intro h
    have ht : taylor a P ≠ 0 := by
      intro ht
      have htop : weightedIndex r a P = ⊤ := by
        apply top_le_iff.mp
        rw [le_weightedIndex_iff]
        intro d _
        simp [← coeff_taylor, ht]
      simp [h] at htop
    obtain ⟨d, hd, he⟩ := exists_weightedIndex_eq_weight (r := r) ht
    let : Finsupp.NonTorsionWeight ℕ (fun j ↦ (r j : ℝ≥0∞)⁻¹) :=
      ⟨by intro n j h; simpa [nsmul_eq_mul] using h⟩
    have hz : d = 0 := (Finsupp.weight_eq_zero_iff_eq_zero _).mp (he.symm.trans h)
    simpa [hz] using hd
  · intro hP
    apply le_antisymm _ zero_le
    simpa using (weightedIndex_le (r := r) (d := 0) (by simpa using hP))

@[simp]
theorem weightedIndex_one [Nontrivial R] (r : σ → ℕ) (a : σ → R) :
    weightedIndex r a (1 : MvPolynomial σ R) = 0 :=
  (weightedIndex_eq_zero_iff r a 1).mpr (by simp)

/-- At the origin a monomial has exactly the reciprocal-weighted degree of its exponent. -/
theorem weightedIndex_monomial_zero (r : σ → ℕ) (d : σ →₀ ℕ) {c : R} (hc : c ≠ 0) :
    weightedIndex r 0 (monomial d c) = d.weight (fun j ↦ (r j : ℝ≥0∞)⁻¹) := by
  classical
  apply le_antisymm
  · apply weightedIndex_le
    rw [← coeff_taylor, taylor_zero, coeff_monomial, ite_eq_left rfl]
    exact hc
  · rw [le_weightedIndex_iff]
    intro e he
    rw [← coeff_taylor, taylor_zero, coeff_monomial, ite_eq_right]
    rintro rfl
    have he' : d.weight (fun j ↦ (r j : ℝ≥0∞)⁻¹) <
        d.weight (fun j ↦ (r j : ℝ≥0∞)⁻¹) := by
      simpa only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, div_eq_mul_inv] using he
    exact lt_irrefl _ he'

/-- The index of a product is at least the sum of the indices of the factors. -/
theorem le_weightedIndex_mul (r : σ → ℕ) (a : σ → R) (P Q : MvPolynomial σ R) :
    weightedIndex r a P + weightedIndex r a Q ≤ weightedIndex r a (P * Q) := by
  classical
  refine le_iInf₂ fun d hd ↦ ?_
  rw [hasseDeriv_mul, map_sum] at hd
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
  rw [map_mul] at hne
  rw [← Finset.mem_antidiagonal.mp hx, map_add]
  exact add_le_add (weightedIndex_le (left_ne_zero_of_mul hne))
    (weightedIndex_le (right_ne_zero_of_mul hne))

/-- The index of a finite product is at least the sum of the indices of its factors. -/
theorem le_weightedIndex_prod {ι : Type*} (r : σ → ℕ) (a : σ → R) (P : ι → MvPolynomial σ R)
    (s : Finset ι) : ∑ i ∈ s, weightedIndex r a (P i) ≤ weightedIndex r a (∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (add_le_add le_rfl ih).trans (le_weightedIndex_mul r a _ _)

/-- A Hasse derivative `∂^d` lowers the index by at most the weight of `d`:
`Ind(P) ≤ Ind(∂^d P) + ∑ j, d j / r j`. -/
theorem weightedIndex_le_weightedIndex_hasseDeriv_add (r : σ → ℕ) (a : σ → R)
    (d : σ →₀ ℕ) (P : MvPolynomial σ R) :
    weightedIndex r a P ≤
      weightedIndex r a (hasseDeriv d P) + d.weight (fun j ↦ (r j : ℝ≥0∞)⁻¹) := by
  rw [← tsub_le_iff_right]
  refine le_iInf₂ fun e he ↦ ?_
  have hcomp := congrArg (eval a) (LinearMap.congr_fun (hasseDeriv_comp e d) P)
  rw [LinearMap.comp_apply, LinearMap.smul_apply, map_nsmul] at hcomp
  have hne : eval a (hasseDeriv (e + d) P) ≠ 0 := fun h ↦ he (by rw [hcomp, h, smul_zero])
  rw [tsub_le_iff_right, ← map_add]
  exact weightedIndex_le hne

/-- Multiplying every weight by a positive integer `c` divides the index by `c`. -/
theorem weightedIndex_smul_weight {c : ℕ} (hc : c ≠ 0) (r : σ → ℕ) (a : σ → R)
    (P : MvPolynomial σ R) :
    weightedIndex (c • r) a P = weightedIndex r a P / c := by
  have hw : (fun j ↦ (((c • r) j : ℕ) : ℝ≥0∞)⁻¹) =
      (c : ℝ≥0∞)⁻¹ • fun j ↦ (r j : ℝ≥0∞)⁻¹ := by
    ext j
    simp [ENNReal.mul_inv]
  simp only [weightedIndex, hw, Finsupp.weight_smul_left, smul_eq_mul,
    ENNReal.iInf_div_of_ne (Nat.cast_ne_zero.mpr hc) (ENNReal.natCast_ne_top c),
    ENNReal.div_eq_inv_mul]

/-- Renaming the variables along an injective map preserves the index, when the center and the
weights are pulled back along the map. -/
theorem weightedIndex_rename {τ : Type*} {f : σ → τ} (hf : Function.Injective f)
    (r : τ → ℕ) (b : τ → R) (P : MvPolynomial σ R) :
    weightedIndex r b (rename f P) = weightedIndex (r ∘ f) (b ∘ f) P := by
  apply le_antisymm
  · refine le_iInf₂ fun d hd ↦ ?_
    have hd' : eval b (hasseDeriv (d.mapDomain f) (rename f P)) ≠ 0 := by
      rwa [TauCeti.eval_hasseDeriv_rename hf]
    exact (weightedIndex_le hd').trans_eq
      (Finsupp.linearCombination_mapDomain (v' := fun j ↦ (r j : ℝ≥0∞)⁻¹) (f := f) (l := d))
  · refine le_iInf₂ fun d hd ↦ ?_
    rw [← coeff_taylor, taylor_rename] at hd
    obtain ⟨u, rfl, hu⟩ : ∃ u, u.mapDomain f = d ∧ (taylor (b ∘ f) P).coeff u ≠ 0 := by
      by_contra! h
      exact hd (coeff_rename_eq_zero f _ d h)
    rw [coeff_taylor] at hu
    exact (weightedIndex_le hu).trans_eq
      (Finsupp.linearCombination_mapDomain (v' := fun j ↦ (r j : ℝ≥0∞)⁻¹) (f := f) (l := u)).symm

example : weightedIndex ![1, 2] 0
    (X 0 * X 1 : MvPolynomial (Fin 2) ℚ) = 3 / 2 := by
  have hm : (X 0 * X 1 : MvPolynomial (Fin 2) ℚ) =
      monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 := by
    rw [monomial_add_single, ← X_pow_eq_monomial, pow_one, pow_one]
  rw [hm, weightedIndex_monomial_zero _ _ one_ne_zero, map_add,
    Finsupp.weight_single, Finsupp.weight_single]
  norm_num
  calc
    (1 : ℝ≥0∞) + 2⁻¹ = 2 / 2 + 1 / 2 := by
      rw [ENNReal.div_self (by norm_num) (by norm_num), one_div]
    _ = (2 + 1) / 2 := (ENNReal.add_div).symm
    _ = 3 / 2 := by norm_num

section NoZeroDivisors

variable [NoZeroDivisors R]

/-- Over a semiring without zero divisors, the index of a product is the sum of the indices.
This holds for all weights, including zero weights and infinite indices. -/
theorem weightedIndex_mul (r : σ → ℕ) (a : σ → R) (P Q : MvPolynomial σ R) :
    weightedIndex r a (P * Q) = weightedIndex r a P + weightedIndex r a Q := by
  classical
  refine le_antisymm ?_ (le_weightedIndex_mul r a P Q)
  by_cases hP : taylor a P = 0
  · simp [weightedIndex_eq_top_of_taylor_eq_zero r hP]
  by_cases hQ : taylor a Q = 0
  · simp [weightedIndex_eq_top_of_taylor_eq_zero r hQ]
  obtain ⟨d, hd, hPd⟩ := exists_weightedIndex_eq_weight (r := r) hP
  obtain ⟨e, he, hQe⟩ := exists_weightedIndex_eq_weight (r := r) hQ
  set w : σ → ℝ≥0∞ := fun j ↦ (r j : ℝ≥0∞)⁻¹
  rw [hPd, hQe]
  by_cases hp : d.weight w = ⊤
  · simp [hp]
  by_cases hq : e.weight w = ⊤
  · simp [hq]
  -- The product of the lowest weighted homogeneous components of the Taylor shifts is
  -- nonzero, and it is the lowest weighted homogeneous component of the shifted product.
  set P₀ := weightedHomogeneousComponent w (d.weight w) (taylor a P)
  set Q₀ := weightedHomogeneousComponent w (e.weight w) (taylor a Q)
  have hP₀ : P₀.coeff d ≠ 0 := by
    simpa [P₀, coeff_weightedHomogeneousComponent, coeff_taylor] using hd
  have hQ₀ : Q₀.coeff e ≠ 0 := by
    simpa [Q₀, coeff_weightedHomogeneousComponent, coeff_taylor] using he
  obtain ⟨g, hg⟩ := ne_zero_iff.mp
    (mul_ne_zero (ne_zero_iff.mpr ⟨d, hP₀⟩) (ne_zero_iff.mpr ⟨e, hQ₀⟩))
  have hwg : g.weight w = d.weight w + e.weight w :=
    ((weightedHomogeneousComponent_isWeightedHomogeneous _ _).mul
      (weightedHomogeneousComponent_isWeightedHomogeneous _ _)) hg
  have hcoeff : (P₀ * Q₀).coeff g = (taylor a (P * Q)).coeff g := by
    rw [map_mul, coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    simp only [P₀, Q₀, coeff_weightedHomogeneousComponent]
    by_cases h0 : (taylor a P).coeff x.1 * (taylor a Q).coeff x.2 = 0
    · split_ifs <;> simp [h0]
    have h₁ : d.weight w ≤ x.1.weight w := hPd ▸
      weightedIndex_le (by rw [← coeff_taylor]; exact left_ne_zero_of_mul h0)
    have h₂ : e.weight w ≤ x.2.weight w := hQe ▸
      weightedIndex_le (by rw [← coeff_taylor]; exact right_ne_zero_of_mul h0)
    have hsum : x.1.weight w + x.2.weight w = d.weight w + e.weight w := by
      rw [← map_add, Finset.mem_antidiagonal.mp hx, hwg]
    have e₁ : x.1.weight w = d.weight w :=
      (ENNReal.le_of_add_le_add_right hq (hsum ▸ add_le_add le_rfl h₂)).antisymm h₁
    have e₂ : x.2.weight w = e.weight w :=
      (ENNReal.le_of_add_le_add_left hp (hsum ▸ add_le_add h₁ le_rfl)).antisymm h₂
    simp [e₁, e₂]
  rw [← hwg]
  exact weightedIndex_le (by rw [← coeff_taylor, ← hcoeff]; exact hg)

/-- Over a nontrivial semiring without zero divisors, the index of `P ^ n` is `n` times the
index of `P`. -/
theorem weightedIndex_pow [Nontrivial R] (r : σ → ℕ) (a : σ → R) (P : MvPolynomial σ R)
    (n : ℕ) : weightedIndex r a (P ^ n) = n • weightedIndex r a P := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, weightedIndex_mul, ih, succ_nsmul]

/-- Over a nontrivial semiring without zero divisors, the index of a finite product is the sum
of the indices of its factors. -/
theorem weightedIndex_prod [Nontrivial R] {ι : Type*} (r : σ → ℕ) (a : σ → R)
    (P : ι → MvPolynomial σ R) (s : Finset ι) :
    weightedIndex r a (∏ i ∈ s, P i) = ∑ i ∈ s, weightedIndex r a (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, weightedIndex_mul, ih]

end NoZeroDivisors

end Semiring

section Ring

variable [CommRing R]

@[simp]
theorem weightedIndex_neg (r : σ → ℕ) (a : σ → R) (P : MvPolynomial σ R) :
    weightedIndex r a (-P) = weightedIndex r a P := by
  simp only [weightedIndex, map_neg, neg_ne_zero]

/-- The index of a determinant is at least the sum over the columns of lower bounds for the
indices of the entries of each column. -/
theorem le_weightedIndex_det {n : Type*} [Fintype n] [DecidableEq n] (r : σ → ℕ) (a : σ → R)
    (A : Matrix n n (MvPolynomial σ R)) {c : n → ℝ≥0∞}
    (h : ∀ k l, c l ≤ weightedIndex r a (A k l)) : ∑ l, c l ≤ weightedIndex r a A.det := by
  rw [Matrix.det_apply]
  refine le_weightedIndex_sum r a fun τ _ ↦ ?_
  -- Each term of the Leibniz expansion takes the entry in the row `τ l` from the column `l`.
  have hτ := (Finset.sum_le_sum fun l _ ↦ h (τ l) l).trans (le_weightedIndex_prod r a _ Finset.univ)
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with hs | hs <;> simpa [hs] using hτ

/-- A nonzero univariate polynomial placed in the coordinate `i` has as index its root
multiplicity at `a i` divided by the weight of `i`. This includes zero weights. -/
theorem weightedIndex_toMvPolynomial (r : σ → ℕ) (a : σ → R) (i : σ) {p : Polynomial R}
    (hp : p ≠ 0) :
    weightedIndex r a (p.toMvPolynomial i) =
      (p.rootMultiplicity (a i) : ℝ≥0∞) / (r i : ℝ≥0∞) := by
  classical
  have hwt (k : ℕ) : (Finsupp.single i k).weight (fun j ↦ (r j : ℝ≥0∞)⁻¹) =
      (k : ℝ≥0∞) / (r i : ℝ≥0∞) := by
    rw [Finsupp.weight_single, nsmul_eq_mul, div_eq_mul_inv]
  have hjet (k : ℕ) : eval a (hasseDeriv (Finsupp.single i k) (p.toMvPolynomial i)) =
      (Polynomial.taylor (a i) p).coeff k := by
    rw [hasseDeriv_single_toMvPolynomial, eval_toMvPolynomial, Polynomial.taylor_coeff]
  have hm : p.rootMultiplicity (a i) = (Polynomial.taylor (a i) p).natTrailingDegree := by
    rw [Polynomial.rootMultiplicity_eq_natTrailingDegree, Polynomial.taylor_apply]
  apply le_antisymm
  · rw [hm, ← hwt]
    refine weightedIndex_le ?_
    rw [hjet]
    exact mt Polynomial.trailingCoeff_eq_zero.mp (by simpa using hp)
  · refine le_iInf₂ fun d hd ↦ ?_
    have hd' : d = Finsupp.single i (d i) := by
      ext j
      by_cases hj : j = i
      · subst hj
        simp
      · rw [Finsupp.single_eq_of_ne hj]
        by_contra h
        exact hd (by rw [hasseDeriv_toMvPolynomial_eq_zero (Ne.symm hj) h, map_zero])
    rw [hd', hjet] at hd
    rw [hd', hwt, hm]
    gcongr
    exact_mod_cast Polynomial.natTrailingDegree_le_of_ne_zero hd

/-- A power of a centered coordinate has its exponent divided by the coordinate's weight
as index. This includes exponent zero and zero weights. -/
theorem weightedIndex_X_sub_C_pow [Nontrivial R] (r : σ → ℕ) (a : σ → R) (i : σ)
    (m : ℕ) : weightedIndex r a ((X i - C (a i)) ^ m) =
      (m : ℝ≥0∞) / (r i : ℝ≥0∞) := by
  simpa [Polynomial.rootMultiplicity_X_sub_C_pow] using
    weightedIndex_toMvPolynomial r a i ((Polynomial.monic_X_sub_C (a i)).pow m).ne_zero

/-- Positive weights make the index of every nonzero polynomial finite. -/
theorem weightedIndex_ne_top {r : σ → ℕ} (hr : ∀ j, r j ≠ 0) (a : σ → R)
    {P : MvPolynomial σ R} (hP : P ≠ 0) : weightedIndex r a P ≠ ⊤ := by
  obtain ⟨d, hd⟩ := ne_zero_iff.mp (taylor_eq_zero.not.mpr hP : taylor a P ≠ 0)
  apply ne_top_of_le_ne_top _ (weightedIndex_le (r := r) (by simpa [coeff_taylor] using hd))
  rw [Finsupp.weight_apply, Finsupp.sum]
  exact ENNReal.sum_ne_top.mpr fun j _ ↦ by
    simpa [nsmul_eq_mul, ← div_eq_mul_inv] using
      ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by simpa using hr j)

/-- With positive natural weights, the finite index is a nonnegative rational number. -/
theorem exists_weightedIndex_eq_nnrat {r : σ → ℕ} (hr : ∀ j, r j ≠ 0) (a : σ → R)
    {P : MvPolynomial σ R} (hP : P ≠ 0) :
    ∃ q : ℚ≥0, weightedIndex r a P = ((q : ℝ≥0) : ℝ≥0∞) := by
  obtain ⟨d, hd, he⟩ := exists_weightedIndex_eq_weight (r := r) (taylor_eq_zero.not.mpr hP)
  refine ⟨∑ j ∈ d.support, (d j : ℚ≥0) / (r j : ℚ≥0), ?_⟩
  rw [he, Finsupp.weight_apply, Finsupp.sum, NNRat.cast_sum, ENNReal.ofNNReal_finsetSum]
  apply Finset.sum_congr rfl
  intro j _
  rw [NNRat.cast_div, NNRat.cast_natCast, NNRat.cast_natCast,
    ENNReal.coe_div (by simpa using hr j)]
  simp [nsmul_eq_mul, div_eq_mul_inv]

/-- With positive weights, infinite index characterizes the zero polynomial. -/
@[simp]
theorem weightedIndex_eq_top_iff {r : σ → ℕ} (hr : ∀ j, r j ≠ 0) (a : σ → R)
    (P : MvPolynomial σ R) : weightedIndex r a P = ⊤ ↔ P = 0 := by
  constructor
  · exact fun h ↦ by_contra fun hP ↦ weightedIndex_ne_top hr a hP h
  · rintro rfl
    exact weightedIndex_zero r a

/-- A nonzero polynomial's index is bounded by the sum of its partial degrees divided
by the corresponding weights. -/
theorem weightedIndex_le_sum_degreeOf [Fintype σ] (r : σ → ℕ) (a : σ → R)
    {P : MvPolynomial σ R} (hP : P ≠ 0) :
    weightedIndex r a P ≤ ∑ j, (P.degreeOf j : ℝ≥0∞) / (r j : ℝ≥0∞) := by
  obtain ⟨d, hd, he⟩ := exists_weightedIndex_eq_weight (r := r) (taylor_eq_zero.not.mpr hP)
  rw [he, Finsupp.weight_eq_sum]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  have hj : d j ≤ P.degreeOf j :=
    (monomial_le_degreeOf j (mem_support_iff.mpr (by simpa [coeff_taylor] using hd))).trans
      (degreeOf_taylor_le a j P)
  simpa [nsmul_eq_mul, ← div_eq_mul_inv] using
    ENNReal.div_le_div_right (by exact_mod_cast hj) (r j)

end Ring

section AbsoluteValue

variable {F K S : Type*} [Fintype σ] [CommRing R] [CommRing F] [CommRing K] [Semiring S]
  [PartialOrder S] [IsOrderedRing S] [IsDomain S]

/-- **Choice of a nonvanishing Hasse derivative** (the proof of Pottmeyer, Lemma 3.5.7). Let `P`
be a polynomial with partial degrees `degreeOf i P ≤ r i` and coefficients of absolute value at
most `B`. If the index of the image of `P` under `g` at a point `b` is finite, then some Hasse
derivative `Q = ∂^d P` does not vanish at `b` after applying `g`, loses at most the index at `b`
from its index at every point `a` after applying `f`, still has partial degrees at most `r i`,
and has coefficients of absolute value at most `2 ^ ∑ᵢ rᵢ * B`. -/
theorem exists_hasseDeriv_eval_ne_zero {P : MvPolynomial σ R} {r : σ → ℕ}
    (hdeg : ∀ i, P.degreeOf i ≤ r i) (abv : AbsoluteValue R S) {B : S}
    (hB : ∀ μ, abv (P.coeff μ) ≤ B) (f : R →+* F) (a : σ → F) (g : R →+* K) {b : σ → K}
    (hb : weightedIndex r b (P.map g) ≠ ⊤) :
    ∃ d : σ →₀ ℕ, eval b ((hasseDeriv d P).map g) ≠ 0 ∧
      weightedIndex r a (P.map f) - weightedIndex r b (P.map g) ≤
        weightedIndex r a ((hasseDeriv d P).map f) ∧
      (∀ i, (hasseDeriv d P).degreeOf i ≤ r i) ∧
      ∀ μ, abv ((hasseDeriv d P).coeff μ) ≤ 2 ^ (∑ i, r i) * B := by
  -- A jet of minimal weight at `b` is nonzero, and its weight is the index at `b`.
  obtain ⟨d, hd, hbd⟩ := exists_weightedIndex_eq_weight (r := r)
    (mt (weightedIndex_eq_top_of_taylor_eq_zero r) hb)
  rw [hasseDeriv_map] at hd
  refine ⟨d, hd, ?_, fun i ↦ (degreeOf_hasseDeriv_le d P i).trans ((Nat.sub_le _ _).trans (hdeg i)),
    fun μ ↦ ?_⟩
  · rw [hbd, tsub_le_iff_right, ← hasseDeriv_map]
    exact weightedIndex_le_weightedIndex_hasseDeriv_add r a d _
  -- `|[X^μ] ∂^d P| ≤ 2 ^ |μ + d| |[X^(μ + d)] P|`, and `|μ + d| ≤ ∑ᵢ rᵢ` when
  -- `[X^(μ + d)] P ≠ 0`.
  refine (abv_coeff_hasseDeriv_le abv d μ P).trans ?_
  by_cases hμ : P.coeff (μ + d) = 0
  · simpa [hμ] using mul_nonneg (pow_nonneg zero_le_two (∑ i, r i)) ((abv.nonneg _).trans (hB 0))
  refine mul_le_mul (pow_le_pow_right₀ one_le_two ?_) (hB _) (abv.nonneg _)
    (pow_nonneg zero_le_two _)
  rw [Finsupp.degree_eq_sum]
  exact Finset.sum_le_sum fun j _ ↦ (monomial_le_degreeOf j (mem_support_iff.2 hμ)).trans (hdeg j)

end AbsoluteValue

end MvPolynomial
