/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Polynomial
public import Mathlib.Algebra.Polynomial.Reverse
public import TauCeti.Algebra.MvPolynomial.Equiv
public import TauCeti.Algebra.Polynomial.Taylor
public import TauCeti.Data.Finsupp.Fin
public import TauCeti.RingTheory.MvPolynomial.LazardValuation
public import TauCeti.RingTheory.MvPolynomial.OrderAt
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Lazard evaluation

Let `p` be a polynomial in variables `X₀, …, Xₙ₋₁` over a commutative ring `S`, and let
`a : Fin n → S`. *Lazard evaluation* of `p` at `a` eliminates the variables one at a time, in
the order `X₀, X₁, …`: it divides `p` by the largest power of `X₀ - a₀` dividing it, sets
`X₀ = a₀`, and continues with the result at the remaining coordinates. The outcome
`p.lazardEval a : S` is nonzero whenever `p` is, unlike the ordinary value `eval a p`, and the
exponents of the removed powers form the vector `p.lazardExponent a : Fin n →₀ ℕ`.

The intended use is `S = R[X]`, with `a` the constant polynomials `C αᵢ` at a point `α ∈ Rⁿ`:
then `p` is a polynomial in the base coordinates `x` and one further variable `z`, and its Lazard
evaluation is a nonzero polynomial in `z` even where the ordinary specialization `p(α, z)`
vanishes identically. This replaces ordinary specialization in Lazard's projection for
cylindrical algebraic decomposition, which needs no well-orientedness hypothesis.

Each step of the elimination is described by the univariate identity
`Polynomial.trailingCoeff_taylor`: dividing `q` by the largest power of `X - r` and evaluating
at `r` gives the trailing coefficient of the Taylor expansion `q(X + r)`, which is its lowest
nonzero coefficient when `q ≠ 0`. Iterating it, the
removed exponents are the lexicographically least exponent `u` of a nonzero Taylor coefficient
of `p` at `a`, and the Lazard evaluation is that coefficient (`lazardExponent_eq_iff`,
`coeff_taylor_lazardExponent`). Here the lexicographic order on `Fin n →₀ ℕ` makes coordinate
`0` the most significant, matching the order of elimination. For nonzero `p` the removed
exponents are therefore the Lazard valuation `p.lazardValuation a`.

Lazard's method uses these exponents along monomial curves `y ↦ α + y ^ c`. For a set `T` of
points `α ∈ Rⁿ`, take `v` lexicographically least among the exponents removed from `f` at the
points of `T` (read in `S` along a ring map `R →+* S`, such as `C : R →+* R[z]`), and `c` an
evaluator for the finitely many exponents removed from `f` and from finitely many further
polynomials `g` over `R` at the points of `T`. Then
`f (α + y ^ c) = y ^ (∑ i, cᵢ vᵢ) * (f_{α,v} + y * Q (α, y))` on `T` with a single polynomial
`Q`, and each `y ↦ g (α + y ^ c)` vanishes at `y = 0` to the order given by the `c`-weight of
the exponents removed from `g` at `α`
(`exists_isLazardEvaluator_forall_aeval_monomialCurve_eq`).

## Main definitions

* `MvPolynomial.lazardEval`: the Lazard evaluation of `p` at `a`.
* `MvPolynomial.lazardExponent`: the exponents of the powers of `Xᵢ - aᵢ` it removes.

## Main results

* `MvPolynomial.lazardEval_ne_zero`: the Lazard evaluation of a nonzero polynomial is nonzero.
* `MvPolynomial.lazardEval_eq_eval`, `MvPolynomial.lazardExponent_eq_zero_iff`: where `p` does
  not vanish, Lazard evaluation is ordinary evaluation, and these are exactly the points where
  no power is removed.
* `MvPolynomial.coeff_taylor_lazardExponent`,
  `MvPolynomial.coeff_taylor_eq_zero_of_lt_lazardExponent`, `MvPolynomial.lazardExponent_eq_iff`:
  the removed exponents are the lexicographically least exponent of a nonzero Taylor coefficient
  of `p` at `a`, and the Lazard evaluation is that Taylor coefficient.
* `MvPolynomial.lazardEval_mul`, `MvPolynomial.lazardExponent_mul`: without zero divisors, Lazard
  evaluation is multiplicative and the removed exponents add.
* `MvPolynomial.lazardValuation_eq_toLex_lazardExponent`,
  `MvPolynomial.finite_range_lazardExponent`: the removed exponents are the Lazard valuation, and
  a polynomial has only finitely many of them.
* `MvPolynomial.exists_isLazardEvaluator_forall_aeval_monomialCurve_eq`: the uniform
  parameterized identity along monomial curves on a set of points, together with the orders of
  vanishing along those curves.

## References

* D. Lazard, *An improved projection for cylindrical algebraic decomposition*, in
  *Algebraic Geometry and its Applications*, Springer (1994), 467–476.
* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), 52–69, Section 2 and Section 5.1.
-/

public section

namespace MvPolynomial

variable {S : Type*} [CommRing S] {n : ℕ}

/-- The **Lazard evaluation** of `p` at `a`. Divide `p` by the largest power of `X₀ - a₀`
dividing it and set `X₀ = a₀`; then continue with the result, a polynomial in the remaining
variables, at the remaining coordinates `Fin.tail a`. With no variables left it is the constant
value of `p`.

It is nonzero whenever `p` is (`MvPolynomial.lazardEval_ne_zero`), and it agrees with `eval a p`
when that is nonzero (`MvPolynomial.lazardEval_eq_eval`). -/
noncomputable def lazardEval : {n : ℕ} → MvPolynomial (Fin n) S → (Fin n → S) → S
  | 0, p, a => eval a p
  | n + 1, p, a =>
    lazardEval ((finSuccEquiv S n p /ₘ (Polynomial.X - Polynomial.C (C (a 0))) ^
      (finSuccEquiv S n p).rootMultiplicity (C (a 0))).eval (C (a 0))) (Fin.tail a)

/-- The exponents of the powers of `Xᵢ - aᵢ` removed by the Lazard evaluation of `p` at `a`
(`MvPolynomial.lazardEval`). Its value at `i` is the exponent of the largest power of `Xᵢ - aᵢ`
dividing the polynomial left after eliminating `X₀, …, Xᵢ₋₁`. -/
noncomputable def lazardExponent : {n : ℕ} → MvPolynomial (Fin n) S → (Fin n → S) → Fin n →₀ ℕ
  | 0, _, _ => 0
  | n + 1, p, a =>
    .cons ((finSuccEquiv S n p).rootMultiplicity (C (a 0)))
      (lazardExponent ((finSuccEquiv S n p /ₘ (Polynomial.X - Polynomial.C (C (a 0))) ^
        (finSuccEquiv S n p).rootMultiplicity (C (a 0))).eval (C (a 0))) (Fin.tail a))

theorem lazardEval_fin_zero (p : MvPolynomial (Fin 0) S) (a : Fin 0 → S) :
    p.lazardEval a = eval a p :=
  (rfl)

theorem lazardEval_fin_succ (p : MvPolynomial (Fin (n + 1)) S) (a : Fin (n + 1) → S) :
    p.lazardEval a =
      ((finSuccEquiv S n p /ₘ (Polynomial.X - Polynomial.C (C (a 0))) ^
        (finSuccEquiv S n p).rootMultiplicity (C (a 0))).eval (C (a 0))).lazardEval
        (Fin.tail a) :=
  (rfl)

theorem lazardExponent_fin_zero (p : MvPolynomial (Fin 0) S) (a : Fin 0 → S) :
    p.lazardExponent a = 0 :=
  (rfl)

theorem lazardExponent_fin_succ (p : MvPolynomial (Fin (n + 1)) S) (a : Fin (n + 1) → S) :
    p.lazardExponent a =
      .cons ((finSuccEquiv S n p).rootMultiplicity (C (a 0)))
        (((finSuccEquiv S n p /ₘ (Polynomial.X - Polynomial.C (C (a 0))) ^
          (finSuccEquiv S n p).rootMultiplicity (C (a 0))).eval (C (a 0))).lazardExponent
          (Fin.tail a)) :=
  (rfl)

@[simp]
theorem lazardEval_zero (a : Fin n → S) : (0 : MvPolynomial (Fin n) S).lazardEval a = 0 := by
  induction n with
  | zero => simp [lazardEval_fin_zero]
  | succ n ih => simp [lazardEval_fin_succ, ih]

@[simp]
theorem lazardExponent_zero (a : Fin n → S) :
    (0 : MvPolynomial (Fin n) S).lazardExponent a = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [lazardExponent_fin_succ, ih]

@[simp]
theorem lazardEval_C (s : S) (a : Fin n → S) : (C s : MvPolynomial (Fin n) S).lazardEval a = s := by
  induction n with
  | zero => simp [lazardEval_fin_zero]
  | succ n ih => simp [lazardEval_fin_succ, finSuccEquiv_apply, ih]

@[simp]
theorem lazardExponent_C (s : S) (a : Fin n → S) :
    (C s : MvPolynomial (Fin n) S).lazardExponent a = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [lazardExponent_fin_succ, finSuccEquiv_apply, ih]

/-- The Lazard evaluation of a nonzero polynomial is nonzero. -/
theorem lazardEval_ne_zero {p : MvPolynomial (Fin n) S} (hp : p ≠ 0) (a : Fin n → S) :
    p.lazardEval a ≠ 0 := by
  induction n with
  | zero =>
    rw [lazardEval_fin_zero, eq_C_of_isEmpty p, eval_C]
    rwa [eq_C_of_isEmpty p, Ne, C_eq_zero] at hp
  | succ n ih =>
    rw [lazardEval_fin_succ]
    exact ih (Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero _ (by simpa using hp)) _

/-- The Lazard evaluation of `p` at `a` is the Taylor coefficient of `p` at `a` whose exponent is
the vector of removed exponents. -/
theorem coeff_taylor_lazardExponent (p : MvPolynomial (Fin n) S) (a : Fin n → S) :
    (taylor a p).coeff (p.lazardExponent a) = p.lazardEval a := by
  induction n with
  | zero =>
    rw [lazardExponent_fin_zero, lazardEval_fin_zero, ← constantCoeff_taylor, constantCoeff_eq]
  | succ n ih =>
    rw [lazardExponent_fin_succ, lazardEval_fin_succ, coeff_taylor_cons,
      ← Polynomial.coeff_taylor_rootMultiplicity, ih]

/-- Every Taylor coefficient of `p` at `a` whose exponent is lexicographically less than the
vector of removed exponents vanishes. -/
theorem coeff_taylor_eq_zero_of_lt_lazardExponent {p : MvPolynomial (Fin n) S} {a : Fin n → S}
    {w : Fin n →₀ ℕ} (hw : toLex w < toLex (p.lazardExponent a)) : (taylor a p).coeff w = 0 := by
  induction n with
  | zero => exact absurd hw (by simp [Subsingleton.elim w (p.lazardExponent a)])
  | succ n ih =>
    rw [lazardExponent_fin_succ, ← Finsupp.cons_tail w,
      Finsupp.toLex_cons_lt_toLex_cons_iff] at hw
    rw [← Finsupp.cons_tail w, coeff_taylor_cons]
    obtain hw | ⟨hw, hw'⟩ := hw
    · rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree
        (by rwa [Polynomial.natTrailingDegree_taylor]), map_zero]
      simp
    · rw [hw, Polynomial.coeff_taylor_rootMultiplicity]
      exact ih hw'

/-- **Lazard exponents as a lexicographic minimum.** For `p ≠ 0`, the vector of exponents
removed by Lazard evaluation at `a` is the lexicographically least exponent of a nonzero Taylor
coefficient of `p` at `a`. -/
theorem lazardExponent_eq_iff {p : MvPolynomial (Fin n) S} (hp : p ≠ 0) {a : Fin n → S}
    {u : Fin n →₀ ℕ} :
    p.lazardExponent a = u ↔
      (taylor a p).coeff u ≠ 0 ∧ ∀ w, toLex w < toLex u → (taylor a p).coeff w = 0 := by
  have hne : (taylor a p).coeff (p.lazardExponent a) ≠ 0 := by
    rw [coeff_taylor_lazardExponent]
    exact lazardEval_ne_zero hp a
  constructor
  · rintro rfl
    exact ⟨hne, fun w hw ↦ coeff_taylor_eq_zero_of_lt_lazardExponent hw⟩
  · rintro ⟨hu, hlt⟩
    obtain h | h | h := lt_trichotomy (toLex (p.lazardExponent a)) (toLex u)
    · exact absurd (hlt _ h) hne
    · exact toLex.injective h
    · exact absurd (coeff_taylor_eq_zero_of_lt_lazardExponent h) hu

/-- No power is removed by Lazard evaluation at a point where `p` does not vanish. -/
theorem lazardExponent_eq_zero_of_eval_ne_zero {p : MvPolynomial (Fin n) S} {a : Fin n → S}
    (h : eval a p ≠ 0) : p.lazardExponent a = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    replace h : eval (Fin.tail a) ((finSuccEquiv S n p).eval (C (a 0))) ≠ 0 := by
      rw [← Fin.cons_self_tail a] at h
      rwa [eval_polynomial_eval_finSuccEquiv, eval_C]
    have h0 : (finSuccEquiv S n p).rootMultiplicity (C (a 0)) = 0 :=
      Polynomial.rootMultiplicity_eq_zero fun hr ↦ h (by rw [hr.eq_zero, map_zero])
    rw [lazardExponent_fin_succ, h0, pow_zero, Polynomial.divByMonic_one, ih h,
      Finsupp.cons_zero_zero]

/-- **Agreement with ordinary specialization.** Where `p` does not vanish, its Lazard evaluation
is its value. -/
theorem lazardEval_eq_eval {p : MvPolynomial (Fin n) S} {a : Fin n → S} (h : eval a p ≠ 0) :
    p.lazardEval a = eval a p := by
  rw [← coeff_taylor_lazardExponent, lazardExponent_eq_zero_of_eval_ne_zero h,
    ← constantCoeff_eq, constantCoeff_taylor]

/-- A nonzero polynomial loses no power under Lazard evaluation at `a` exactly when it does not
vanish at `a`. -/
theorem lazardExponent_eq_zero_iff {p : MvPolynomial (Fin n) S} (hp : p ≠ 0) {a : Fin n → S} :
    p.lazardExponent a = 0 ↔ eval a p ≠ 0 := by
  refine ⟨fun h ↦ ?_, lazardExponent_eq_zero_of_eval_ne_zero⟩
  rw [← constantCoeff_taylor, constantCoeff_eq, ← h, coeff_taylor_lazardExponent]
  exact lazardEval_ne_zero hp a

/-- Lazard evaluation removes exactly one power of `Xᵢ - aᵢ` from `Xᵢ - aᵢ`. -/
@[simp]
theorem lazardExponent_X_sub_C [Nontrivial S] (a : Fin n → S) (i : Fin n) :
    (X i - C (a i)).lazardExponent a = Finsupp.single i 1 := by
  classical
  have hX : taylor a (X i - C (a i)) = X i := by simp
  have hne : X i - C (a i) ≠ 0 := by
    rw [Ne, ← taylor_eq_zero (a := a), hX]
    exact X_ne_zero i
  rw [lazardExponent_eq_iff hne, hX]
  refine ⟨by simp, fun w hw ↦ ?_⟩
  rw [coeff_X, ite_eq_right_iff]
  rintro rfl
  exact absurd hw (lt_irrefl _)

@[simp]
theorem lazardEval_X_sub_C (a : Fin n → S) (i : Fin n) :
    (X i - C (a i)).lazardEval a = 1 := by
  nontriviality S
  rw [← coeff_taylor_lazardExponent, lazardExponent_X_sub_C]
  simp

section NoZeroDivisors

variable [NoZeroDivisors S]

/-- Over a ring without zero divisors, Lazard evaluation is multiplicative. -/
theorem lazardEval_mul (p q : MvPolynomial (Fin n) S) (a : Fin n → S) :
    (p * q).lazardEval a = p.lazardEval a * q.lazardEval a := by
  induction n with
  | zero => simp [lazardEval_fin_zero]
  | succ n ih =>
    simp only [lazardEval_fin_succ, ← Polynomial.trailingCoeff_taylor, map_mul,
      Polynomial.taylor_mul, Polynomial.trailingCoeff_mul, ih]

/-- Over a ring without zero divisors, the exponents removed by Lazard evaluation of a product
of nonzero polynomials are the sums of those removed from the factors. -/
theorem lazardExponent_mul {p q : MvPolynomial (Fin n) S} (hp : p ≠ 0) (hq : q ≠ 0)
    (a : Fin n → S) :
    (p * q).lazardExponent a = p.lazardExponent a + q.lazardExponent a := by
  induction n with
  | zero => simp [lazardExponent_fin_zero]
  | succ n ih =>
    have hP : Polynomial.taylor (C (a 0)) (finSuccEquiv S n p) ≠ 0 := by simpa using hp
    have hQ : Polynomial.taylor (C (a 0)) (finSuccEquiv S n q) ≠ 0 := by simpa using hq
    simp only [lazardExponent_fin_succ, ← Polynomial.trailingCoeff_taylor]
    simp only [← Polynomial.natTrailingDegree_taylor, map_mul, Polynomial.taylor_mul,
      Polynomial.trailingCoeff_mul, Polynomial.natTrailingDegree_mul hP hQ, Finsupp.cons_add_cons]
    rw [ih (by simpa using hP) (by simpa using hQ)]

end NoZeroDivisors

/-! ### Lazard valuations and the uniform parameterized identity -/

section Valuation

open Finsupp

/-- For a nonzero polynomial, the exponents removed by Lazard evaluation at `a` are its Lazard
valuation at `a`. -/
theorem lazardValuation_eq_toLex_lazardExponent {p : MvPolynomial (Fin n) S} (hp : p ≠ 0)
    (a : Fin n → S) : p.lazardValuation a = toLex (p.lazardExponent a) :=
  lazardValuation_eq_coe_iff.2 ((lazardExponent_eq_iff hp).1 rfl)

/-- A polynomial has only finitely many vectors of exponents removed by Lazard evaluation. -/
theorem finite_range_lazardExponent (p : MvPolynomial (Fin n) S) :
    (Set.range p.lazardExponent).Finite := by
  obtain rfl | hp := eq_or_ne p 0
  · exact (Set.finite_singleton 0).subset <| Set.range_subset_iff.2 lazardExponent_zero
  · exact (finite_setOf_lazardValuation_eq p).subset fun _ ⟨a, ha⟩ ↦
      ⟨a, ha ▸ lazardValuation_eq_toLex_lazardExponent hp a⟩

/-- If `c` is an evaluator for a set containing the exponents removed by Lazard evaluation of `p`
at `a`, then `y ↦ p (a + y ^ c)` vanishes at `y = 0` to order exactly their `c`-weight. For
`p = 0` both sides are zero. -/
theorem natTrailingDegree_aeval_monomialCurve_lazardExponent {V : Set (Fin n →₀ ℕ)}
    {c : Fin n → ℕ} (hc : TauCeti.IsLazardEvaluator V c) {p : MvPolynomial (Fin n) S}
    {a : Fin n → S} (ha : p.lazardExponent a ∈ V) :
    (aeval (monomialCurve a c) p).natTrailingDegree = weight c (p.lazardExponent a) := by
  obtain rfl | hp := eq_or_ne p 0
  · simp
  · exact natTrailingDegree_aeval_monomialCurve (lazardValuation_eq_toLex_lazardExponent hp a) ha hc

/-- **The uniform parameterized identity for Lazard evaluation.** Let `φ : R →+* S`, let `f` be a
polynomial over `S` (for instance over `S = R[z]`, with `φ = C`), let `G` be a finite family of
polynomials over `R`, and let `T` be a nonempty set of points of `Rⁿ`, read in `Sⁿ` along `φ` when
evaluating `f`. There is an evaluator `c` for the exponents removed by Lazard evaluation of `f`
and of the members of `G` at the points of `T`, such that for every `α ∈ T`:
* each `g ∈ G` restricts to `y ↦ g (α + y ^ c)` vanishing at `y = 0` to order exactly the
  `c`-weight of the exponents removed by Lazard evaluation of `g` at `α`; in particular this
  order is constant on `T` when the Lazard valuation of `g` is;
* with `v` the lexicographically least vector of exponents removed from `f` at the points of `T`,
  `f (α + y ^ c) = y ^ (∑ i, cᵢ vᵢ) * (f_{α,v} + y * Q (α, y))` for a single polynomial `Q`
  independent of `α`. Here `f_{α,v}` is the Taylor coefficient of `f` at `α` with exponent `v`,
  which is the Lazard evaluation of `f` at `α` wherever `v` is the exponent removed there. -/
theorem exists_isLazardEvaluator_forall_aeval_monomialCurve_eq {R : Type*} [CommRing R]
    (φ : R →+* S) (f : MvPolynomial (Fin n) S) (G : Finset (MvPolynomial (Fin n) R))
    {T : Set (Fin n → R)} (hT : T.Nonempty) :
    ∃ c, TauCeti.IsLazardEvaluator
        ((fun α ↦ f.lazardExponent (φ ∘ α)) '' T ∪ ⋃ g ∈ G, g.lazardExponent '' T) c ∧
      (∀ g ∈ G, ∀ α ∈ T,
        (aeval (monomialCurve α c) g).natTrailingDegree = weight c (g.lazardExponent α)) ∧
      ∃ v ∈ (fun α ↦ f.lazardExponent (φ ∘ α)) '' T,
        (∀ α ∈ T, toLex v ≤ toLex (f.lazardExponent (φ ∘ α))) ∧
        ∃ Q : Polynomial (MvPolynomial (Fin n) S), ∀ α ∈ T,
          aeval (monomialCurve (φ ∘ α) c) f = Polynomial.X ^ weight c v *
            (Polynomial.C ((taylor (φ ∘ α) f).coeff v) +
              Polynomial.X * Q.map (eval (φ ∘ α))) := by
  have hfin : ((fun α ↦ f.lazardExponent (φ ∘ α)) '' T).Finite :=
    (finite_range_lazardExponent f).subset <| Set.image_subset_iff.2 fun α _ ↦ ⟨φ ∘ α, rfl⟩
  obtain ⟨c, hc⟩ := TauCeti.exists_isLazardEvaluator <| hfin.union <|
    G.finite_toSet.biUnion fun g _ ↦
      (finite_range_lazardExponent g).subset (Set.image_subset_range _ _)
  obtain ⟨v, hvT, hv⟩ := Set.exists_min_image _ toLex hfin (hT.image _)
  have hv' (α) (hα : α ∈ T) : toLex v ≤ toLex (f.lazardExponent (φ ∘ α)) := hv _ ⟨α, hα, rfl⟩
  obtain ⟨Q, hQ⟩ := exists_forall_aeval_monomialCurve_eq_X_pow_mul f hc (Or.inl hvT)
  refine ⟨c, hc, fun g hg α hα ↦ ?_, v, hvT, hv', Q, fun α hα ↦ hQ _ fun u hu ↦
    coeff_taylor_eq_zero_of_lt_lazardExponent (hu.trans_le (hv' α hα))⟩
  exact natTrailingDegree_aeval_monomialCurve_lazardExponent hc
    (Or.inr (Set.mem_biUnion hg ⟨α, hα, rfl⟩))

end Valuation

end MvPolynomial
