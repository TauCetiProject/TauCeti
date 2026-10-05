/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
public import Mathlib.RingTheory.MvPowerSeries.LexOrder
public import TauCeti.Data.Finsupp.Weight
public import TauCeti.RingTheory.MvPolynomial.OrderAt

/-!
# The Lazard valuation of a multivariate polynomial at a point

Fix a linear order on the variables `σ`, well-founded for `>` (for instance `Fin n`). The
*Lazard valuation* `p.lazardValuation a` of a polynomial `p` at a point `a` is the
lexicographically least exponent of a nonzero Taylor coefficient of `p` at `a`, that is, of a
nonzero coefficient of the translate `taylor a p = p(X + a)`, and `⊤` when `p = 0`. The
lexicographic order is Mathlib's order on `Lex (σ →₀ ℕ)`, in which the least variable is the
most significant; this is the order in which Lazard evaluation divides out the powers of the
`Xᵢ - aᵢ`. It is Mathlib's `MvPowerSeries.lexOrder` of the Taylor
shift, just as the order of vanishing `MvPolynomial.orderAt` is the order of the Taylor shift;
the two invariants differ in that the Lazard valuation retains the whole lexicographically
leading exponent rather than only a total degree. The Lazard valuation is additive on products
over a domain, it is zero exactly where `p` does not vanish, and its coordinates are bounded by
the degrees of `p`, so a fixed polynomial takes only finitely many Lazard valuations.

Valuations turn into orders of vanishing along monomial curves. An *evaluator* for a set `V` of
exponents is a weight vector `c : σ → ℕ`, positive everywhere, such that for every `v ∈ V` and
every variable `i`, the `c`-weight of the coordinates of `v` less significant than `i` is less
than `c i` (`TauCeti.IsLazardEvaluator`). Such weights turn the lexicographic comparison of an
exponent in `V` with any other exponent into a comparison of `c`-weights
(`TauCeti.IsLazardEvaluator.weight_lt_weight`). Every finite set of exponents has an evaluator
(`TauCeti.exists_isLazardEvaluator`). Consequently, if the Lazard valuation `v` of `p` at `a`
lies in `V`, then along the monomial curve `y ↦ a + y ^ c` with coordinates `aᵢ + y ^ cᵢ`
(`MvPolynomial.monomialCurve`) the polynomial `p` restricts to a nonzero polynomial in `y`
whose order of vanishing at `y = 0` is the `c`-weight `∑ i, cᵢ vᵢ` of `v`, with lowest
coefficient the Taylor coefficient of `p` at `a` of exponent `v`
(`MvPolynomial.natTrailingDegree_aeval_monomialCurve`). This is how Lazard's method for
cylindrical algebraic decomposition converts constancy of Lazard valuations into constancy of
orders of vanishing of one-variable restrictions.

## Main definitions

* `MvPolynomial.lazardValuation`: the Lazard valuation of `p` at `a`.
* `TauCeti.IsLazardEvaluator`: `c` is an evaluator for the set of exponents `V`.
* `MvPolynomial.monomialCurve`: the monomial curve `y ↦ a + y ^ c`.

## Main results

* `MvPolynomial.lazardValuation_eq_coe_iff`: the characterization of the Lazard valuation by
  Taylor coefficients.
* `MvPolynomial.lazardValuation_mul`: over a domain, the Lazard valuation is additive on
  products.
* `MvPolynomial.lazardValuation_eq_zero_iff`: the valuation is zero exactly where `p` does not
  vanish.
* `MvPolynomial.finite_range_lazardValuation`, `MvPolynomial.finite_setOf_lazardValuation_eq`:
  a polynomial has only finitely many Lazard valuations.
* `TauCeti.exists_isLazardEvaluator`: every finite set of exponents has an evaluator.
* `MvPolynomial.natTrailingDegree_aeval_monomialCurve`: the order of `y ↦ p (a + y ^ c)` at `0`
  is the `c`-weight of the Lazard valuation of `p` at `a`.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), 52–69, Section 2 (Lazard
  valuation) and Section 5.1 (evaluators and monomial test curves).
-/

public section

open Finsupp

section Evaluator

namespace TauCeti

variable {σ : Type*} [LinearOrder σ] {V W : Set (σ →₀ ℕ)} {c : σ → ℕ}

/-- `c` is an *evaluator* for the set of exponents `V`: every weight `c i` is positive and, for
every `v ∈ V` and every variable `i`, the `c`-weight `∑ j > i, c j * v j` of the coordinates of
`v` less significant than `i` is less than `c i`. -/
structure IsLazardEvaluator (V : Set (σ →₀ ℕ)) (c : σ → ℕ) : Prop where
  pos : ∀ i, 0 < c i
  weight_filter_lt : ∀ v ∈ V, ∀ i, weight c (v.filter (i < ·)) < c i

namespace IsLazardEvaluator

/-- An evaluator for `W` is an evaluator for every subset of `W`. -/
theorem mono (hc : IsLazardEvaluator W c) (h : V ⊆ W) : IsLazardEvaluator V c :=
  ⟨hc.pos, fun v hv ↦ hc.weight_filter_lt v (h hv)⟩

/-- Positive multiples of an evaluator are evaluators. -/
theorem smul (hc : IsLazardEvaluator V c) {k : ℕ} (hk : 0 < k) : IsLazardEvaluator V (k • c) := by
  refine ⟨fun i ↦ Nat.mul_pos hk (hc.pos i), fun v hv i ↦ ?_⟩
  rw [weight_smul_left, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  exact Nat.mul_lt_mul_of_pos_left (hc.weight_filter_lt v hv i) hk

/-- An evaluator for `V` turns the lexicographic comparison of an exponent in `V` with any
other exponent into a comparison of `c`-weights. -/
theorem weight_lt_weight (hc : IsLazardEvaluator V c) {v u : σ →₀ ℕ} (hv : v ∈ V)
    (h : toLex v < toLex u) : weight c v < weight c u := by
  obtain ⟨i, heq, hlt⟩ := Finsupp.Lex.lt_iff.1 h
  simp only [ofLex_toLex] at heq hlt
  have hbefore : v.filter (· < i) = u.filter (· < i) := by
    ext j
    simp only [filter_apply]
    split_ifs with hj
    · exact heq j hj
    · rfl
  rw [← weight_filter_gt_add_smul_add_weight_filter_lt c v i,
    ← weight_filter_gt_add_smul_add_weight_filter_lt c u i, hbefore, smul_eq_mul, smul_eq_mul,
    add_assoc, add_assoc]
  refine Nat.add_lt_add_left ?_ _
  calc v i * c i + weight c (v.filter (i < ·)) < v i * c i + c i :=
        Nat.add_lt_add_left (hc.weight_filter_lt v hv i) _
    _ = (v i + 1) * c i := by ring
    _ ≤ u i * c i := Nat.mul_le_mul_right _ hlt
    _ ≤ u i * c i + weight c (u.filter (i < ·)) := Nat.le_add_right _ _

end IsLazardEvaluator

/-- Every finite set of exponents has an evaluator. -/
theorem exists_isLazardEvaluator (hV : V.Finite) :
    ∃ c : σ → ℕ, IsLazardEvaluator V c := by
  classical
  -- The variables occurring in some exponent of `V`.
  set S : Finset σ := hV.toFinset.biUnion Finsupp.support
  have hS {v : σ →₀ ℕ} (hv : v ∈ V) : v.support ⊆ S := fun j hj ↦
    Finset.mem_biUnion.2 ⟨v, hV.mem_toFinset.2 hv, hj⟩
  -- `K` bounds every coordinate of every exponent in `V`.
  obtain ⟨K, hK⟩ := (hV.biUnion fun v _ ↦ v.finite_range).bddAbove
  replace hK (v) (hv : v ∈ V) (i : σ) : v i ≤ K :=
    hK (Set.mem_biUnion hv (Set.mem_range_self i))
  -- The weights are positional in base `M`: `c i = M ^ rk i`, where `rk i` counts the occurring
  -- variables less significant than `i`, so `c j` for `i < j` in `S` is at most `c i / M`.
  set M := S.card * K + 1
  set rk : σ → ℕ := fun i ↦ (S.filter (i < ·)).card
  have hrk {i j : σ} (hjS : j ∈ S) (h : i < j) : rk j + 1 ≤ rk i := by
    refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun k hk ↦ ?_).2 ⟨j, ?_, ?_⟩)
    · simp only [Finset.mem_filter] at hk ⊢
      exact ⟨hk.1, h.trans hk.2⟩
    · simpa [hjS] using h
    · simp
  refine ⟨fun i ↦ M ^ rk i, ⟨fun i ↦ by positivity, fun v hv i ↦ ?_⟩⟩
  rw [weight_apply, sum_of_support_subset _ ((Finset.filter_subset _ _).trans (hS hv))
    (fun j n ↦ n • M ^ rk j) fun _ _ ↦ zero_smul _ _]
  -- After multiplying by `M`, each of the at most `S.card` less significant terms is at most
  -- `K * c i`, and `M > S.card * K` makes their sum less than `M * c i`.
  refine Nat.lt_of_mul_lt_mul_left (a := M) ?_
  calc M * ∑ j ∈ S, (v.filter (i < ·)) j • M ^ rk j
      = ∑ j ∈ S, if i < j then v j * M ^ (rk j + 1) else 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        split_ifs with hj
        · rw [filter_apply_pos _ _ hj, smul_eq_mul, pow_succ]
          ring
        · rw [filter_apply_neg _ _ hj, zero_smul, mul_zero]
    _ ≤ ∑ _j ∈ S, K * M ^ rk i := Finset.sum_le_sum fun j hjS ↦ by
        split_ifs with hj
        · exact Nat.mul_le_mul (hK v hv j) (Nat.pow_le_pow_right (by omega) (hrk hjS hj))
        · exact Nat.zero_le _
    _ = S.card * K * M ^ rk i := by simp [mul_assoc]
    _ < M * M ^ rk i := Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)

end TauCeti

end Evaluator

namespace MvPolynomial

section Substitution

variable {σ R : Type*} [CommSemiring R]

/-- The monomial curve `y ↦ a + y ^ c`, given by its coordinates `aᵢ + y ^ cᵢ` as polynomials in
`y`. Substituting it into a multivariate polynomial `p` with `aeval` restricts `p` to the
curve. -/
noncomputable def monomialCurve (a : σ → R) (c : σ → ℕ) : σ → Polynomial R :=
  fun i ↦ Polynomial.C (a i) + Polynomial.X ^ c i

@[simp]
theorem monomialCurve_apply (a : σ → R) (c : σ → ℕ) (i : σ) :
    monomialCurve a c i = Polynomial.C (a i) + Polynomial.X ^ c i :=
  (rfl)

/-- Substituting `y ^ cᵢ` for each variable `Xᵢ` sends the monomial `X ^ m` to `y` to the power
of the `c`-weight of `m`. -/
theorem aeval_X_pow_left_monomial (c : σ → ℕ) (m : σ →₀ ℕ) (r : R) :
    aeval (fun i ↦ (Polynomial.X : Polynomial R) ^ c i) (monomial m r) =
      Polynomial.monomial (weight c m) r := by
  rw [aeval_monomial, Polynomial.algebraMap_eq, ← Polynomial.C_mul_X_pow_eq_monomial]
  congr 1
  simp only [Finsupp.prod, ← pow_mul, Finset.prod_pow_eq_pow_sum, weight_apply, Finsupp.sum,
    smul_eq_mul, mul_comm]

/-- Restricting `p` to the curve `y ↦ a + y ^ c`, with coordinates `aᵢ + y ^ cᵢ`, amounts to
substituting `y ^ cᵢ` for each variable in the Taylor shift of `p` at `a`. -/
theorem aeval_monomialCurve (a : σ → R) (c : σ → ℕ) (p : MvPolynomial σ R) :
    aeval (monomialCurve a c) p =
      aeval (fun i ↦ (Polynomial.X : Polynomial R) ^ c i) (taylor a p) := by
  rw [taylor_apply, ← AlgHom.comp_apply, comp_aeval]
  congr 1
  ext i : 1
  simp [Polynomial.algebraMap_eq, add_comm]

/-- The coefficients of the restriction of `p` to the curve `y ↦ a + y ^ c`: the coefficient
of `y ^ k` is the sum of the Taylor coefficients of `p` at `a` with exponents of `c`-weight
`k`. -/
theorem coeff_aeval_monomialCurve (a : σ → R) (c : σ → ℕ) (p : MvPolynomial σ R) (k : ℕ) :
    (aeval (monomialCurve a c) p).coeff k =
      ∑ m ∈ (taylor a p).support with weight c m = k, (taylor a p).coeff m := by
  conv_lhs => rw [aeval_monomialCurve, (taylor a p).as_sum, map_sum]
  simp only [aeval_X_pow_left_monomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Finset.sum_ite, Finset.sum_const_zero, add_zero]

end Substitution

variable {σ R : Type*} [LinearOrder σ] [WellFoundedGT σ]

section CommSemiring

variable [CommSemiring R] {p q : MvPolynomial σ R} {a : σ → R} {v : σ →₀ ℕ}

/-- The Lazard valuation of `p` at `a`: the lexicographically least exponent of a nonzero
Taylor coefficient of `p` at `a`, and `⊤` if there is none. In the lexicographic order on
`Lex (σ →₀ ℕ)` the least variable is the most significant. -/
noncomputable def lazardValuation (p : MvPolynomial σ R) (a : σ → R) :
    WithTop (Lex (σ →₀ ℕ)) :=
  (taylor a p : MvPowerSeries σ R).lexOrder

theorem lazardValuation_def (p : MvPolynomial σ R) (a : σ → R) :
    p.lazardValuation a = (taylor a p : MvPowerSeries σ R).lexOrder :=
  (rfl)

/-- The Taylor coefficient of `p` at `a` whose exponent is the Lazard valuation is nonzero. -/
theorem coeff_taylor_ne_zero_of_lazardValuation_eq (h : p.lazardValuation a = toLex v) :
    (taylor a p).coeff v ≠ 0 := by
  simpa using MvPowerSeries.coeff_ne_zero_of_lexOrder h.symm

/-- The Taylor coefficients of `p` at `a` with exponents below the Lazard valuation vanish. -/
theorem coeff_taylor_eq_zero_of_lt_lazardValuation (h : toLex v < p.lazardValuation a) :
    (taylor a p).coeff v = 0 := by
  simpa using MvPowerSeries.coeff_eq_zero_of_lt_lexOrder h

theorem lazardValuation_le_of_coeff_taylor_ne_zero (h : (taylor a p).coeff v ≠ 0) :
    p.lazardValuation a ≤ toLex v :=
  MvPowerSeries.lexOrder_le_of_coeff_ne_zero (by simpa using h)

/-- The Lazard valuation of `p` at `a` is at least `w` exactly when every Taylor coefficient of
`p` at `a` with exponent below `w` vanishes. -/
theorem le_lazardValuation_iff {w : WithTop (Lex (σ →₀ ℕ))} :
    w ≤ p.lazardValuation a ↔ ∀ d : σ →₀ ℕ, toLex d < w → (taylor a p).coeff d = 0 := by
  simp [lazardValuation_def, MvPowerSeries.le_lexOrder_iff]

/-- The Lazard valuation of `p` at `a` is `v` exactly when the Taylor coefficient of `p` at `a`
with exponent `v` is nonzero and those with lexicographically smaller exponents vanish. -/
theorem lazardValuation_eq_coe_iff :
    p.lazardValuation a = toLex v ↔
      (taylor a p).coeff v ≠ 0 ∧ ∀ d : σ →₀ ℕ, toLex d < toLex v → (taylor a p).coeff d = 0 := by
  refine ⟨fun h ↦ ⟨coeff_taylor_ne_zero_of_lazardValuation_eq h, fun d hd ↦
    coeff_taylor_eq_zero_of_lt_lazardValuation (h ▸ WithTop.coe_lt_coe.2 hd)⟩, fun h ↦ ?_⟩
  refine (lazardValuation_le_of_coeff_taylor_ne_zero h.1).antisymm (le_lazardValuation_iff.2 ?_)
  exact fun d hd ↦ h.2 d (WithTop.coe_lt_coe.1 hd)

/-- A nonzero Taylor coefficient of `p` at `a` with exponent other than the Lazard valuation has
a lexicographically larger exponent. -/
theorem toLex_lt_of_coeff_taylor_ne_zero (h : p.lazardValuation a = toLex v)
    {d : σ →₀ ℕ} (hd : (taylor a p).coeff d ≠ 0) (hdv : d ≠ v) : toLex v < toLex d :=
  lt_of_le_of_ne (WithTop.coe_le_coe.1 (h ▸ lazardValuation_le_of_coeff_taylor_ne_zero hd))
    (toLex.injective.ne hdv.symm)

@[simp]
theorem lazardValuation_zero (a : σ → R) : (0 : MvPolynomial σ R).lazardValuation a = ⊤ := by
  simp [lazardValuation_def]

theorem zero_le_lazardValuation (p : MvPolynomial σ R) (a : σ → R) :
    0 ≤ p.lazardValuation a := by
  rw [← WithTop.coe_zero, ← toLex_zero]
  exact le_lazardValuation_iff.2 fun d hd ↦
    absurd hd (WithTop.coe_le_coe.2 (toLex_monotone (zero_le : (0 : σ →₀ ℕ) ≤ d))).not_gt

/-- The Lazard valuation of `p` at `a` is zero exactly when `p` does not vanish at `a`. -/
theorem lazardValuation_eq_zero_iff : p.lazardValuation a = 0 ↔ eval a p ≠ 0 := by
  rw [← constantCoeff_taylor, constantCoeff_eq]
  refine ⟨fun h ↦ coeff_taylor_ne_zero_of_lazardValuation_eq
    (by rw [h, toLex_zero, WithTop.coe_zero]), fun h ↦ (zero_le_lazardValuation p a).antisymm' ?_⟩
  simpa using lazardValuation_le_of_coeff_taylor_ne_zero h

/-- The Lazard valuation of `p` at `a` is positive exactly when `p` vanishes at `a`. -/
theorem lazardValuation_pos_iff : 0 < p.lazardValuation a ↔ eval a p = 0 := by
  rw [(zero_le_lazardValuation p a).lt_iff_ne, ne_comm, Ne, lazardValuation_eq_zero_iff, not_not]

theorem lazardValuation_C_of_ne_zero {r : R} (hr : r ≠ 0) (a : σ → R) :
    (C r).lazardValuation a = 0 :=
  lazardValuation_eq_zero_iff.2 (by simpa using hr)

@[simp]
theorem lazardValuation_one [Nontrivial R] (a : σ → R) :
    (1 : MvPolynomial σ R).lazardValuation a = 0 := by
  simpa using lazardValuation_C_of_ne_zero (one_ne_zero (α := R)) a

theorem min_lazardValuation_le_lazardValuation_add (p q : MvPolynomial σ R) (a : σ → R) :
    min (p.lazardValuation a) (q.lazardValuation a) ≤ (p + q).lazardValuation a := by
  simpa [lazardValuation_def] using
    MvPowerSeries.min_lexOrder_le (φ := (taylor a p : MvPowerSeries σ R)) (ψ := taylor a q)

theorem le_lazardValuation_mul (p q : MvPolynomial σ R) (a : σ → R) :
    p.lazardValuation a + q.lazardValuation a ≤ (p * q).lazardValuation a := by
  simpa [lazardValuation_def] using MvPowerSeries.le_lexOrder_mul _ _

/-- Over a domain, the Lazard valuation of a product is the sum of the Lazard valuations. -/
theorem lazardValuation_mul [NoZeroDivisors R] (p q : MvPolynomial σ R) (a : σ → R) :
    (p * q).lazardValuation a = p.lazardValuation a + q.lazardValuation a := by
  simpa [lazardValuation_def] using MvPowerSeries.lexOrder_mul _ _

/-- Over a domain, the Lazard valuation of `p ^ n` is `n` times that of `p`. -/
theorem lazardValuation_pow [NoZeroDivisors R] [Nontrivial R] (p : MvPolynomial σ R)
    (a : σ → R) (n : ℕ) : (p ^ n).lazardValuation a = n • p.lazardValuation a := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, lazardValuation_mul, ih, succ_nsmul]

/-- Each coordinate of the Lazard valuation of `p` is at most the degree of `p` in that
variable. -/
theorem lazardValuation_apply_le_degreeOf (h : p.lazardValuation a = toLex v) (i : σ) :
    v i ≤ p.degreeOf i :=
  (monomial_le_degreeOf i (mem_support_iff.2 (coeff_taylor_ne_zero_of_lazardValuation_eq h))).trans
    (degreeOf_taylor_le a i p)

/-- A polynomial has only finitely many Lazard valuations. -/
theorem finite_range_lazardValuation (p : MvPolynomial σ R) :
    (Set.range p.lazardValuation).Finite := by
  classical
  refine (((Set.finite_Iic p.degrees.toFinsupp).image
    fun v ↦ ((toLex v : Lex (σ →₀ ℕ)) : WithTop _)).insert ⊤).subset ?_
  rintro _ ⟨a, rfl⟩
  induction h : p.lazardValuation a with
  | top => exact Set.mem_insert _ _
  | coe w =>
    refine Set.mem_insert_of_mem _ ⟨ofLex w, Set.mem_Iic.2 (Finsupp.le_def.2 fun i ↦ ?_), by simp⟩
    simpa [degreeOf_def] using
      lazardValuation_apply_le_degreeOf (v := ofLex w) (by rw [toLex_ofLex]; exact h) i

/-- The exponents occurring as Lazard valuations of a fixed polynomial form a finite set. -/
theorem finite_setOf_lazardValuation_eq (p : MvPolynomial σ R) :
    {v : σ →₀ ℕ | ∃ a, p.lazardValuation a = toLex v}.Finite :=
  ((finite_range_lazardValuation p).preimage
    (WithTop.coe_injective.comp toLex.injective).injOn).subset fun _ ⟨a, ha⟩ ↦ ⟨a, ha⟩

end CommSemiring

section CommRing

variable [CommRing R] {p : MvPolynomial σ R} {a : σ → R}

/-- Only the zero polynomial has Lazard valuation `⊤`. -/
@[simp]
theorem lazardValuation_eq_top_iff : p.lazardValuation a = ⊤ ↔ p = 0 := by
  simp [lazardValuation_def, coe_eq_zero_iff]

@[simp]
theorem lazardValuation_neg (p : MvPolynomial σ R) (a : σ → R) :
    (-p).lazardValuation a = p.lazardValuation a := by
  refine le_antisymm (le_lazardValuation_iff.2 fun d hd ↦ ?_)
    (le_lazardValuation_iff.2 fun d hd ↦ ?_)
  · simpa using coeff_taylor_eq_zero_of_lt_lazardValuation (p := -p) hd
  · simpa using coeff_taylor_eq_zero_of_lt_lazardValuation (p := p) hd

theorem exists_lazardValuation_eq (hp : p ≠ 0) (a : σ → R) :
    ∃ v : σ →₀ ℕ, p.lazardValuation a = toLex v :=
  MvPowerSeries.exists_finsupp_eq_lexOrder_of_ne_zero (by simpa [coe_eq_zero_iff] using hp)

/-- The Lazard valuation of the coordinate function `Xᵢ - aᵢ` at `a` is the exponent of `Xᵢ`. -/
theorem lazardValuation_X_sub_C [Nontrivial R] (a : σ → R) (i : σ) :
    (X i - C (a i) : MvPolynomial σ R).lazardValuation a = toLex (single i 1) := by
  classical
  rw [lazardValuation_eq_coe_iff, map_sub, taylor_X, taylor_C, add_sub_cancel_right]
  refine ⟨by simp, fun d hd ↦ ?_⟩
  rw [coeff_X, ite_eq_right_iff]
  rintro rfl
  exact (lt_irrefl _ hd).elim

end CommRing

section MonomialCurve

variable [CommSemiring R]

variable {V : Set (σ →₀ ℕ)} {c : σ → ℕ} {p : MvPolynomial σ R} {a : σ → R} {v : σ →₀ ℕ}

/-- If the Lazard valuation `v` of `p` at `a` lies in `V` and `c` is an evaluator for `V`, then
every other exponent of a nonzero Taylor coefficient of `p` at `a` has larger `c`-weight than
`v`. -/
theorem weight_lt_weight_of_coeff_taylor_ne_zero (h : p.lazardValuation a = toLex v) (hv : v ∈ V)
    (hc : TauCeti.IsLazardEvaluator V c) {m : σ →₀ ℕ} (hm : (taylor a p).coeff m ≠ 0)
    (hmv : m ≠ v) : weight c v < weight c m :=
  hc.weight_lt_weight hv (toLex_lt_of_coeff_taylor_ne_zero h hm hmv)

/-- If the Lazard valuation `v` of `p` at `a` lies in `V` and `c` is an evaluator for `V`, then
the restriction of `p` to the curve `y ↦ a + y ^ c` has no terms of degree below the `c`-weight
of `v`. -/
theorem coeff_aeval_monomialCurve_eq_zero_of_lt_weight (h : p.lazardValuation a = toLex v)
    (hv : v ∈ V) (hc : TauCeti.IsLazardEvaluator V c) {k : ℕ} (hk : k < weight c v) :
    (aeval (monomialCurve a c) p).coeff k = 0 := by
  rw [coeff_aeval_monomialCurve]
  refine Finset.sum_eq_zero fun m hm ↦ ?_
  rw [Finset.mem_filter, mem_support_iff] at hm
  obtain rfl | hmv := eq_or_ne m v
  · exact absurd hm.2 hk.ne'
  · exact absurd (weight_lt_weight_of_coeff_taylor_ne_zero h hv hc hm.1 hmv) (hm.2 ▸ hk).not_gt

/-- If the Lazard valuation `v` of `p` at `a` lies in `V` and `c` is an evaluator for `V`, then
the coefficient of `y` to the `c`-weight of `v` in the restriction of `p` to the curve
`y ↦ a + y ^ c` is the Taylor coefficient of `p` at `a` with exponent `v`. -/
theorem coeff_aeval_monomialCurve_weight (h : p.lazardValuation a = toLex v) (hv : v ∈ V)
    (hc : TauCeti.IsLazardEvaluator V c) :
    (aeval (monomialCurve a c) p).coeff (weight c v) =
      (taylor a p).coeff v := by
  rw [coeff_aeval_monomialCurve]
  refine Finset.sum_eq_single_of_mem v (Finset.mem_filter.2
    ⟨mem_support_iff.2 (coeff_taylor_ne_zero_of_lazardValuation_eq h), rfl⟩) fun m hm hmv ↦ ?_
  rw [Finset.mem_filter, mem_support_iff] at hm
  exact absurd hm.2 (weight_lt_weight_of_coeff_taylor_ne_zero h hv hc hm.1 hmv).ne'

/-- If the Lazard valuation of `p` at `a` lies in a set with evaluator `c`, then `p` does not
vanish identically on the curve `y ↦ a + y ^ c`. -/
theorem aeval_monomialCurve_ne_zero (h : p.lazardValuation a = toLex v) (hv : v ∈ V)
    (hc : TauCeti.IsLazardEvaluator V c) :
    aeval (monomialCurve a c) p ≠ 0 := fun h₀ ↦
  coeff_taylor_ne_zero_of_lazardValuation_eq h <| by
    rw [← coeff_aeval_monomialCurve_weight h hv hc, h₀, Polynomial.coeff_zero]

/-- **Lazard valuations along monomial curves.** If the Lazard valuation `v` of `p` at `a` lies
in `V` and `c` is an evaluator for `V`, then the restriction `y ↦ p (a + y ^ c)` of `p` to the
curve with coordinates `aᵢ + y ^ cᵢ` vanishes at `y = 0` to order exactly the `c`-weight
`∑ i, cᵢ vᵢ` of `v`. -/
theorem natTrailingDegree_aeval_monomialCurve (h : p.lazardValuation a = toLex v) (hv : v ∈ V)
    (hc : TauCeti.IsLazardEvaluator V c) :
    (aeval (monomialCurve a c) p).natTrailingDegree =
      weight c v := by
  refine le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero ?_)
    (Polynomial.le_natTrailingDegree (aeval_monomialCurve_ne_zero h hv hc)
      fun k hk ↦ coeff_aeval_monomialCurve_eq_zero_of_lt_weight h hv hc hk)
  rw [coeff_aeval_monomialCurve_weight h hv hc]
  exact coeff_taylor_ne_zero_of_lazardValuation_eq h

/-- If the Lazard valuation `v` of `p` at `a` lies in `V` and `c` is an evaluator for `V`, then
the lowest coefficient of `y ↦ p (a + y ^ c)` is the Taylor coefficient of `p` at `a` with
exponent `v`. -/
theorem trailingCoeff_aeval_monomialCurve (h : p.lazardValuation a = toLex v) (hv : v ∈ V)
    (hc : TauCeti.IsLazardEvaluator V c) :
    (aeval (monomialCurve a c) p).trailingCoeff =
      (taylor a p).coeff v := by
  rw [Polynomial.trailingCoeff, natTrailingDegree_aeval_monomialCurve h hv hc,
    coeff_aeval_monomialCurve_weight h hv hc]

end MonomialCurve

end MvPolynomial
