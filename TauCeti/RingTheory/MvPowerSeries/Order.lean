/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPowerSeries.Order
public import Mathlib.RingTheory.MvPowerSeries.Substitution
-- Proof-only: coefficients of a difference of substitutions.
import TauCeti.RingTheory.MvPowerSeries.Substitution

import Mathlib.Tactic.LinearCombination

/-!
# Lowest-degree homogeneous components of powers, products and substitutions

If a series has order at least `p`, the degree-`n * p` homogeneous component of its `n`-th power
is the `n`-th power of its degree-`p` component, and similarly for finite products. This reduces
lowest-degree coefficient computations for powers to homogeneous series, over arbitrary semirings.

The same holds for substitution: if `f` has order at least `p` and the series `a i` have zero
constant coefficient, the degree-`p` component of `f(a)` only depends on the degree-`p` component
of `f` and on the linear parts of the `a i`, into which it is substituted
(`MvPowerSeries.homogeneousComponent_subst_of_le_order`). This is how the lowest-degree term of an
expression such as `f(F(X, Y), Z)`, for a formal group law `F(X, Y) = X + Y + ⋯`, is read off as
the polynomial `f_p(X + Y, Z)`. In finitely many variables the degree-`p` component is a
polynomial (`MvPowerSeries.homogeneousComponentPolynomial`), and the lowest-degree component of
`f(a)` is that polynomial evaluated at the linear parts of the `a i`
(`MvPowerSeries.homogeneousComponent_subst_eq_coe_aeval`).

Products and powers of close series are close: the order of `x y - x' y'` is bounded through
those of `x - x'` and `y - y'` (`MvPowerSeries.le_order_mul_sub_mul`), and if `x` and `y` have
zero constant coefficient and `x - y` has order at least `n`, then `xᵏ - yᵏ` has order at least
`n + k - 1` for `k ≥ 1` (`MvPowerSeries.le_order_pow_sub_pow`). Substitution is Lipschitz for the
order: if every `a i` and `b i` has zero constant coefficient and `a i - b i` has order at least
`n` for all `i`, then `f(a) - f(b)` has order at least `n + k - 1` when `f` has order at least `k`
(`MvPowerSeries.le_order_subst_sub_subst`), and under the same hypotheses, in degrees at most `n`
it agrees with the linear part `∑ᵢ fᵢ (a i - b i)` of `f` applied to the differences
(`MvPowerSeries.coeff_subst_sub_subst_of_degree_le`).

Perturbing one entry `a s` by a series `e` of order at least `n ≥ 1` changes `f(a)` by `c e`, where
`c` is the coefficient of `Xₛ` in `f`, up to terms of degree greater than `n`
(`MvPowerSeries.le_order_subst_update_add_sub`). For a formal group law this says that
`F(x + e, y) ≡ F(x, y) + e` to lowest order. The proof uses that below degree `n + 1`, multiplying
`e` by a series `q` scales it by the constant coefficient of `q`
(`MvPowerSeries.coeff_mul_eq_coeff_mul_constantCoeff_of_le_order`).

A common lower bound on the orders of two series bounds the orders of their sum and difference
(`MvPowerSeries.le_order_add`, `MvPowerSeries.le_order_sub`). Over a commutative ring, if `f` and
`g` have zero constant coefficient, then `f ^ n - g ^ n` has order larger than that of `f - g` for
`n ≥ 2` (`MvPowerSeries.order_sub_add_one_le_order_pow_sub_pow`).
The degree-zero component of a series is its constant term
(`MvPowerSeries.homogeneousComponent_zero`).

For two-variable series with linear coefficients one, the degree-one component is `X + Y`.
Over a ring, vanishing of the constant coefficient then puts the remainder after subtracting
`X + Y` in order at least two, and over a commutative ring the linear part of `f(x, y)` is the
sum of the linear parts of `x` and `y` (`MvPowerSeries.homogeneousComponent_one_subst_pair`).
-/

public section

namespace MvPowerSeries

section AddSub

variable {σ R : Type*} {n : ℕ∞}

/-- A lower bound on the orders of two series bounds the order of their sum. -/
theorem le_order_add [Semiring R] {f g : MvPowerSeries σ R} (hf : n ≤ f.order)
    (hg : n ≤ g.order) : n ≤ (f + g).order :=
  (le_min hf hg).trans min_order_le_add

/-- A lower bound on the orders of two series bounds the order of their difference. -/
theorem le_order_sub [Ring R] {f g : MvPowerSeries σ R} (hf : n ≤ f.order)
    (hg : n ≤ g.order) : n ≤ (f - g).order := by
  rw [sub_eq_add_neg]
  exact le_order_add hf (by rwa [order_neg])

/-- If `f` and `g` have zero constant coefficient and `2 ≤ n`, then the order of `f ^ n - g ^ n`
exceeds that of `f - g`: it is `f - g` times `∑ fⁱ gⁿ⁻¹⁻ⁱ`, whose constant coefficient vanishes. -/
theorem order_sub_add_one_le_order_pow_sub_pow [CommRing R] {f g : MvPowerSeries σ R}
    (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) {n : ℕ} (hn : 2 ≤ n) :
    (f - g).order + 1 ≤ (f ^ n - g ^ n).order := by
  rw [← geom_sum₂_mul, add_comm]
  refine (add_le_add ?_ le_rfl).trans le_order_mul
  refine one_le_order_iff_constCoeff_eq_zero.mpr ?_
  rw [map_sum]
  refine Finset.sum_eq_zero fun i hi ↦ ?_
  rw [Finset.mem_range] at hi
  rcases Nat.eq_zero_or_pos i with rfl | hi₀
  · rw [map_mul, map_pow, map_pow, hg, zero_pow (by omega), mul_zero]
  · rw [map_mul, map_pow, hf, zero_pow hi₀.ne', zero_mul]

end AddSub

section Powers

variable {σ R : Type*} [Semiring R] {f : MvPowerSeries σ R}

/-- A variable is its own degree-one homogeneous component. -/
@[simp]
theorem homogeneousComponent_one_X (i : σ) :
    homogeneousComponent 1 (X i : MvPowerSeries σ R) = X i := by
  classical
  ext d
  rw [coeff_homogeneousComponent, coeff_X]
  split_ifs with h₁ h₂ h₂ <;> simp_all

/-- In one variable, the degree-one homogeneous component of `f` is `c X`, where `c` is the
coefficient of `X` in `f`. -/
theorem homogeneousComponent_one_eq_C_mul_X (f : MvPowerSeries Unit R) :
    homogeneousComponent 1 f = C (coeff (Finsupp.single () 1) f) * X () := by
  classical
  refine ext fun d ↦ ?_
  rw [coeff_homogeneousComponent, coeff_C_mul, coeff_X]
  by_cases h : d = Finsupp.single () 1
  · subst h
    simp
  · have hd : d.degree ≠ 1 := fun hd ↦ h <| by
      ext
      simpa [Finsupp.degree_eq_sum] using hd
    simp [h, hd]

/-- A homogeneous component of positive degree has no constant coefficient. -/
@[simp]
theorem constantCoeff_homogeneousComponent {p : ℕ} (hp : p ≠ 0) (f : MvPowerSeries σ R) :
    constantCoeff (homogeneousComponent p f) = 0 := by
  simp [← coeff_zero_eq_constantCoeff_apply, coeff_homogeneousComponent, hp.symm]

/-- A series of order at least `n` without degree-`n` component has order at least `n + 1`. -/
theorem succ_le_order_of_homogeneousComponent_eq_zero {n : ℕ} (hn : n ≤ f.order)
    (h : homogeneousComponent n f = 0) : ((n + 1 : ℕ) : ℕ∞) ≤ f.order := by
  refine nat_le_order fun d hd ↦ ?_
  rcases Nat.lt_succ_iff_lt_or_eq.mp hd with hd | hd
  · exact coeff_of_lt_order ((Nat.cast_lt.mpr hd).trans_le hn)
  · simpa [coeff_homogeneousComponent, hd] using congrArg (coeff d) h

/-- The lowest possible homogeneous component of a power is the corresponding power of the
lowest possible homogeneous component. -/
theorem homogeneousComponent_pow_of_le_order {p : ℕ} (hf : p ≤ f.order) (n : ℕ) :
    homogeneousComponent (n * p) (f ^ n) = (homogeneousComponent p f) ^ n := by
  classical
  induction n with
  | zero =>
    ext d
    by_cases hd : d = 0 <;>
      simp [coeff_homogeneousComponent, coeff_one, Finsupp.degree_eq_zero_iff, hd]
  | succ n ih =>
    have hn : (n * p : ℕ) ≤ (f ^ n).order := by
      simpa only [nsmul_eq_mul, Nat.cast_mul] using
        (nsmul_le_nsmul_right hf n).trans (le_order_pow n)
    rw [pow_succ, Nat.succ_mul, homogeneousComponent_mul_of_le_order hn hf, ih, pow_succ]

/-- For a series without constant coefficient, the degree-`n` component of its `n`-th power is the
`n`-th power of its linear part. -/
theorem homogeneousComponent_pow_of_constantCoeff_eq_zero (hf : constantCoeff f = 0) (n : ℕ) :
    homogeneousComponent n (f ^ n) = homogeneousComponent 1 f ^ n := by
  simpa using homogeneousComponent_pow_of_le_order (p := 1)
    (by simpa using one_le_order_iff_constCoeff_eq_zero.mpr hf) n

end Powers

section Components

variable {σ R : Type*} [Semiring R]

/-- The degree-zero homogeneous component of a power series is its constant term. -/
@[simp]
theorem homogeneousComponent_zero (f : MvPowerSeries σ R) :
    homogeneousComponent 0 f = C (constantCoeff f) := by
  classical
  ext d
  simp only [coeff_homogeneousComponent, coeff_C, Finsupp.degree_eq_zero_iff]
  split_ifs with h
  · rw [h, coeff_zero_eq_constantCoeff_apply]
  · rfl

end Components

section Products

variable {σ R : Type*} [CommSemiring R]

/-- The lowest possible homogeneous component of a finite product is the product of the lowest
possible homogeneous components of the factors. -/
theorem homogeneousComponent_prod_of_le_order {ι : Type*} (s : Finset ι)
    {f : ι → MvPowerSeries σ R} {p : ι → ℕ} (hf : ∀ i ∈ s, p i ≤ (f i).order) :
    homogeneousComponent (∑ i ∈ s, p i) (∏ i ∈ s, f i) =
      ∏ i ∈ s, homogeneousComponent (p i) (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hs : ((∑ i ∈ s, p i : ℕ) : ℕ∞) ≤ (∏ i ∈ s, f i).order := by
      push_cast
      exact (Finset.sum_le_sum fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)).trans
        (le_order_prod f s)
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Finset.prod_insert ha,
      homogeneousComponent_mul_of_le_order (hf a (Finset.mem_insert_self a s)) hs,
      ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)]

/-- The monomial `aᵈ = ∏ᵢ (a i) ^ (d i)` in series without constant coefficient has order at least
the degree of `d`. -/
theorem degree_le_order_prod_pow {ι : Type*} {a : ι → MvPowerSeries σ R}
    (ha₀ : ∀ i, constantCoeff (a i) = 0) (d : ι →₀ ℕ) :
    (d.degree : ℕ∞) ≤ (d.prod fun i k ↦ a i ^ k).order := by
  rw [Finsupp.prod, Finsupp.degree_apply]
  push_cast
  refine (Finset.sum_le_sum fun i _ ↦ ?_).trans (le_order_prod _ _)
  simpa using le_order_pow_of_constantCoeff_eq_zero (d i) (ha₀ i)

/-- The degree-`|d|` component of the monomial `aᵈ = ∏ᵢ (a i) ^ (d i)` in series without constant
coefficient is the same monomial in their linear parts. -/
theorem homogeneousComponent_degree_prod_pow {ι : Type*} {a : ι → MvPowerSeries σ R}
    (ha₀ : ∀ i, constantCoeff (a i) = 0) (d : ι →₀ ℕ) :
    homogeneousComponent d.degree (d.prod fun i k ↦ a i ^ k) =
      d.prod fun i k ↦ homogeneousComponent 1 (a i) ^ k := by
  rw [Finsupp.prod, Finsupp.prod, Finsupp.degree_apply,
    homogeneousComponent_prod_of_le_order _ fun i _ ↦ ?_]
  · exact Finset.prod_congr rfl fun i _ ↦
      homogeneousComponent_pow_of_constantCoeff_eq_zero (ha₀ i) _
  · simpa using le_order_pow_of_constantCoeff_eq_zero (d i) (ha₀ i)

end Products

section Subst

variable {σ τ R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The linear parts of a substitutable family can be substituted. -/
theorem HasSubst.homogeneousComponent_one {a : σ → MvPowerSeries τ S} (ha : HasSubst a) :
    HasSubst fun i ↦ homogeneousComponent 1 (a i) where
  const_coeff s := by simp
  coeff_zero d := (ha.coeff_zero d).subset fun s hs ↦ by
    simp only [Set.mem_ofPred_eq, coeff_homogeneousComponent] at hs ⊢
    split_ifs at hs
    exacts [hs, (hs rfl).elim]

/-- **The lowest-degree component of a substitution.** If `f` has order at least `p` and the series
`a i` have zero constant coefficient, the degree-`p` component of `f(a)` is the degree-`p` component
of `f` evaluated at the linear parts of the `a i`. -/
theorem homogeneousComponent_subst_of_le_order {f : MvPowerSeries σ R} {p : ℕ}
    (hf : p ≤ f.order) {a : σ → MvPowerSeries τ S} (ha : HasSubst a)
    (ha₀ : ∀ i, constantCoeff (a i) = 0) :
    homogeneousComponent p (f.subst a) =
      (homogeneousComponent p f).subst fun i ↦ homogeneousComponent 1 (a i) := by
  ext e
  rw [coeff_homogeneousComponent, coeff_subst ha, coeff_subst ha.homogeneousComponent_one]
  split_ifs with he
  · refine finsum_congr fun d ↦ ?_
    rw [coeff_homogeneousComponent]
    split_ifs with hd
    · rw [← homogeneousComponent_degree_prod_pow ha₀, coeff_homogeneousComponent,
        ite_eq_left (he.trans hd.symm)]
    · rcases lt_or_gt_of_ne hd with hlt | hgt
      · rw [coeff_of_lt_order ((Nat.cast_lt.mpr hlt).trans_le hf), zero_smul, zero_smul]
      · rw [coeff_of_lt_order ((Nat.cast_lt.mpr (he.trans_lt hgt)).trans_le
          (degree_le_order_prod_pow ha₀ d)), smul_zero, zero_smul]
  · refine (finsum_eq_zero_of_forall_eq_zero fun d ↦ ?_).symm
    rw [coeff_homogeneousComponent]
    split_ifs with hd
    · rw [← homogeneousComponent_degree_prod_pow ha₀, coeff_homogeneousComponent,
        ite_eq_right (hd ▸ he), smul_zero]
    · rw [zero_smul]

end Subst

section Polynomial

variable {σ τ R : Type*} [Finite σ]

/-- The degree-`n` homogeneous component of a power series in finitely many variables, as a
polynomial. -/
noncomputable def homogeneousComponentPolynomial [CommSemiring R] (n : ℕ)
    (f : MvPowerSeries σ R) :
    MvPolynomial σ R :=
  MvPolynomial.homogeneousComponent n (truncTotal (n + 1) f)

@[simp]
theorem coe_homogeneousComponentPolynomial [CommSemiring R] (n : ℕ) (f : MvPowerSeries σ R) :
    (homogeneousComponentPolynomial n f : MvPowerSeries σ R) = homogeneousComponent n f := by
  ext d
  rw [MvPolynomial.coeff_coe, homogeneousComponentPolynomial,
    MvPolynomial.coeff_homogeneousComponent, coeff_homogeneousComponent]
  split_ifs with hd
  · exact coeff_truncTotal _ (by omega)
  · rfl

theorem isHomogeneous_homogeneousComponentPolynomial [CommSemiring R] (n : ℕ)
    (f : MvPowerSeries σ R) :
    (homogeneousComponentPolynomial n f).IsHomogeneous n :=
  MvPolynomial.homogeneousComponent_isHomogeneous _ _

/-- If `f` vanishes below degree `n` and the series `a i` have no constant term, the degree-`n`
part of `f(a)` is the polynomial degree-`n` part of `f` evaluated at polynomials `l i` equal to the
linear parts of the `a i`. -/
theorem homogeneousComponent_subst_eq_coe_aeval [CommRing R] {n : ℕ} {f : MvPowerSeries σ R}
    (hn : n ≤ f.order) {a : σ → MvPowerSeries τ R} (ha : HasSubst a)
    (ha₀ : ∀ i, constantCoeff (a i) = 0) {l : σ → MvPolynomial τ R}
    (hl : ∀ i, homogeneousComponent 1 (a i) = l i) :
    homogeneousComponent n (f.subst a) =
      (MvPolynomial.aeval l (homogeneousComponentPolynomial n f) : MvPowerSeries τ R) := by
  rw [homogeneousComponent_subst_of_le_order hn ha ha₀, ← coe_homogeneousComponentPolynomial,
    subst_coe]
  simp_rw [hl]
  simpa using (MvPolynomial.comp_aeval_apply (MvPolynomial.coeToMvPowerSeries.algHom R)
    (homogeneousComponentPolynomial n f) (f := l)).symm

end Polynomial

section Differences

variable {σ τ R : Type*} {n : ℕ}

section Ring

variable [Ring R]

/-- The order of `x y - x' y'` is at least the smaller of the orders of `(x - x') y` and
`x' (y - y')`. -/
theorem le_order_mul_sub_mul {x x' y y' : MvPowerSeries τ R} {m : ℕ∞}
    (h₁ : m ≤ (x - x').order + y.order) (h₂ : m ≤ x'.order + (y - y').order) :
    m ≤ (x * y - x' * y').order := by
  rw [show x * y - x' * y' = (x - x') * y + x' * (y - y') by
    rw [sub_mul, mul_sub, sub_add_sub_cancel]]
  exact le_order_add (h₁.trans le_order_mul) (h₂.trans le_order_mul)

/-- If `x - y` has order at least `n` and `x`, `y` have zero constant coefficient, then
`xᵏ - yᵏ` has order at least `n + k - 1` for `k ≥ 1`. -/
theorem le_order_pow_sub_pow {x y : MvPowerSeries τ R} (hx : constantCoeff x = 0)
    (hy : constantCoeff y = 0) (hxy : (n : ℕ∞) ≤ (x - y).order) {k : ℕ} (hk : k ≠ 0) :
    ((n + k - 1 : ℕ) : ℕ∞) ≤ (x ^ k - y ^ k).order := by
  induction k with
  | zero => exact absurd rfl hk
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk₀
    · simpa using hxy
    rw [pow_succ, pow_succ]
    refine le_order_mul_sub_mul ((add_le_add (ih hk₀.ne') (one_le_order_iff_constCoeff_eq_zero.mpr
      hx)).trans' ?_) ((add_le_add (le_order_pow_of_constantCoeff_eq_zero k hy) hxy).trans' ?_)
    · exact_mod_cast (by omega : n + (k + 1) - 1 ≤ n + k - 1 + 1)
    · exact_mod_cast (by omega : n + (k + 1) - 1 ≤ k + n)

end Ring

variable [CommRing R]

/-- **Monomials in close arguments are closer.** If the series `a i` and `b i` have zero constant
coefficient and `a i - b i` has order at least `n` for every `i`, then for `d ≠ 0` the monomials
`aᵈ` and `bᵈ` differ by a series of order at least `n + |d| - 1`. -/
theorem le_order_prod_pow_sub_prod_pow {ι : Type*} {a b : ι → MvPowerSeries τ R}
    (ha₀ : ∀ i, constantCoeff (a i) = 0) (hb₀ : ∀ i, constantCoeff (b i) = 0)
    (hab : ∀ i, (n : ℕ∞) ≤ (a i - b i).order) {d : ι →₀ ℕ} (hd : d ≠ 0) :
    ((n + d.degree - 1 : ℕ) : ℕ∞) ≤
      ((d.prod fun i k ↦ a i ^ k) - d.prod fun i k ↦ b i ^ k).order := by
  classical
  induction d using Finsupp.induction with
  | zero => exact absurd rfl hd
  | single_add i k f hi hk ih =>
    have hprod (c : ι → MvPowerSeries τ R) : ((Finsupp.single i k + f).prod fun i k ↦ c i ^ k) =
        c i ^ k * f.prod fun i k ↦ c i ^ k := by
      rw [Finsupp.prod_add_index' (fun _ ↦ pow_zero _) (fun _ _ _ ↦ pow_add _ _ _),
        Finsupp.prod_single_index (h := fun i k ↦ c i ^ k) (pow_zero _)]
    rw [hprod, hprod, map_add, Finsupp.degree_single]
    rcases eq_or_ne f 0 with rfl | hf
    · simpa using le_order_pow_sub_pow (ha₀ i) (hb₀ i) (hab i) hk
    have hf₀ : f.degree ≠ 0 := fun h ↦ hf ((Finsupp.degree_eq_zero_iff f).mp h)
    refine le_order_mul_sub_mul ((add_le_add (le_order_pow_sub_pow (ha₀ i) (hb₀ i) (hab i) hk)
      (degree_le_order_prod_pow ha₀ f)).trans' ?_)
      ((add_le_add (le_order_pow_of_constantCoeff_eq_zero k (hb₀ i)) (ih hf)).trans' ?_)
    · exact_mod_cast (by omega : n + (k + f.degree) - 1 ≤ n + k - 1 + f.degree)
    · exact_mod_cast (by omega : n + (k + f.degree) - 1 ≤ k + (n + f.degree - 1))

/-- **Substitution is Lipschitz for the order.** Let `H` have order at least `k`, and let the
series `a i` and `b i` have zero constant coefficient, with `a i - b i` of order at least `n`.
Then `H(a) - H(b)` has order at least `n + k - 1`. -/
theorem le_order_subst_sub_subst {H : MvPowerSeries σ R} {k : ℕ}
    (hH : (k : ℕ∞) ≤ H.order) {a b : σ → MvPowerSeries τ R} (ha : HasSubst a) (hb : HasSubst b)
    (ha₀ : ∀ i, constantCoeff (a i) = 0) (hb₀ : ∀ i, constantCoeff (b i) = 0)
    (hab : ∀ i, (n : ℕ∞) ≤ (a i - b i).order) :
    ((n + k - 1 : ℕ) : ℕ∞) ≤ (H.subst a - H.subst b).order := by
  refine nat_le_order fun e he ↦ ?_
  rw [coeff_subst_sub_subst ha hb]
  refine finsum_eq_zero_of_forall_eq_zero fun d ↦ ?_
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  by_cases hdk : d.degree < k
  · rw [coeff_of_lt_order (hH.trans_lt' (by exact_mod_cast hdk)), zero_smul]
  · rw [coeff_of_lt_order ((le_order_prod_pow_sub_prod_pow ha₀ hb₀ hab hd).trans_lt'
      (by exact_mod_cast (by omega : e.degree < n + d.degree - 1))), smul_zero]

/-- **The linear part of a difference of substitutions.** If the series `a i` and `b i` have zero
constant coefficient and `a i - b i` has order at least `n`, then in degrees at most `n` the
coefficients of `H(a) - H(b)` are those of `∑ᵢ hᵢ (a i - b i)`, where `hᵢ` is the coefficient of
`Xᵢ` in `H`. -/
theorem coeff_subst_sub_subst_of_degree_le [Fintype σ] (H : MvPowerSeries σ R)
    {a b : σ → MvPowerSeries τ R} (ha : HasSubst a) (hb : HasSubst b)
    (ha₀ : ∀ i, constantCoeff (a i) = 0) (hb₀ : ∀ i, constantCoeff (b i) = 0)
    (hab : ∀ i, (n : ℕ∞) ≤ (a i - b i).order) {e : τ →₀ ℕ} (he : e.degree ≤ n) :
    coeff e (H.subst a - H.subst b) =
      ∑ i, coeff (Finsupp.single i 1) H * coeff e (a i - b i) := by
  classical
  rw [coeff_subst_sub_subst ha hb, finsum_eq_sum_of_support_subset (s := Finset.univ.image
    fun i ↦ Finsupp.single i 1), Finset.sum_image fun i _ j _ h ↦ by
      simpa using Finsupp.single_left_inj (one_ne_zero (α := ℕ)) |>.mp h]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finsupp.prod_single_index (h := fun i k ↦ a i ^ k) (pow_zero _),
      Finsupp.prod_single_index (h := fun i k ↦ b i ^ k) (pow_zero _), pow_one, pow_one,
      smul_eq_mul]
  · intro d hd
    rw [Function.mem_support] at hd
    rcases eq_or_ne d 0 with rfl | hd₀
    · simp at hd
    by_cases hd₁ : d.degree = 1
    · obtain ⟨i, rfl⟩ := (Set.ext_iff.mp Finsupp.range_single_one d).mpr hd₁
      simp
    · refine absurd ?_ hd
      rw [coeff_of_lt_order ((le_order_prod_pow_sub_prod_pow ha₀ hb₀ hab hd₀).trans_lt'
        (by exact_mod_cast (by have := (Finsupp.degree_eq_zero_iff d).not.mpr hd₀; omega :
          e.degree < n + d.degree - 1))), smul_zero]

end Differences

/-- Below degree `n + 1`, multiplying a series `e` of order at least `n` by `q` scales it by the
constant coefficient of `q`. -/
theorem coeff_mul_eq_coeff_mul_constantCoeff_of_le_order {σ R : Type*} [Ring R]
    {e : MvPowerSeries σ R} {n : ℕ} (he : n ≤ e.order) (q : MvPowerSeries σ R) {m : σ →₀ ℕ}
    (hm : m.degree ≤ n) :
    coeff m (e * q) = coeff m e * constantCoeff q := by
  have hq : (1 : ℕ∞) ≤ (q - C (constantCoeff q)).order :=
    one_le_order_iff_constCoeff_eq_zero.mpr (by simp)
  have hlt : (m.degree : ℕ∞) < (e * (q - C (constantCoeff q))).order :=
    lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_of_le hm) ((add_le_add he hq).trans le_order_mul)
  have h := coeff_of_lt_order hlt
  rwa [mul_sub, map_sub, coeff_mul_C, sub_eq_zero] at h

section Perturbation

variable {σ τ R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- **The lowest-order effect of perturbing a substitution.** Let the series `a t` have zero
constant coefficient, and perturb the entry `a s` by a series `e` of order at least `n ≥ 1`. Then
`f(a)` changes by `c e`, where `c` is the coefficient of `Xₛ` in `f`, up to terms of degree greater
than `n`. -/
theorem le_order_subst_update_add_sub [DecidableEq σ] (f : MvPowerSeries σ R)
    {a : σ → MvPowerSeries τ S} (ha : HasSubst a) (ha₀ : ∀ t, constantCoeff (a t) = 0) (s : σ)
    {e : MvPowerSeries τ S} {n : ℕ} (hn : n ≠ 0) (he : n ≤ e.order) :
    ((n + 1 : ℕ) : ℕ∞) ≤ (f.subst (Function.update a s (a s + e)) - f.subst a -
      algebraMap R S (coeff (Finsupp.single s 1) f) • e).order := by
  set b := Function.update a s (a s + e) with hb_def
  have he₀ : constantCoeff e = 0 := one_le_order_iff_constCoeff_eq_zero.mp <|
    (Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hn)).trans he
  have hb₀ (t : σ) : constantCoeff (b t) = 0 := by
    rcases eq_or_ne t s with rfl | ht
    · simp [b, ha₀, he₀]
    · simp [b, ht, ha₀]
  have hb : HasSubst b := by
    refine ⟨fun t ↦ by simp [hb₀ t], fun d ↦ ((ha.coeff_zero d).union
      (Set.finite_singleton s)).subset fun t ht ↦ ?_⟩
    rcases eq_or_ne t s with rfl | hts
    · exact Or.inr rfl
    · exact Or.inl (by simpa [b, hts] using ht)
  -- each monomial splits as a power of the perturbed entry times a factor `c d` not involving it
  set c : (σ →₀ ℕ) → MvPowerSeries τ S := fun d ↦ (d.erase s).prod fun t k ↦ a t ^ k
  have hprod (x : σ → MvPowerSeries τ S) (hx : ∀ t ≠ s, x t = a t) (d : σ →₀ ℕ) :
      (d.prod fun t k ↦ x t ^ k) = x s ^ d s * c d := by
    rw [← Finsupp.mul_prod_erase' d s _ fun _ ↦ pow_zero _]
    congr 1
    exact Finsupp.prod_congr fun t ht ↦ by rw [hx t (by rintro rfl; simp at ht)]
  -- so the monomials in `b` and in `a` differ by `e` times `Q d`
  set Q : (σ →₀ ℕ) → MvPowerSeries τ S := fun d ↦
    (∑ i ∈ Finset.range (d s), b s ^ i * a s ^ (d s - 1 - i)) * c d
  have hQ (d : σ →₀ ℕ) : (d.prod fun t k ↦ b t ^ k) = (d.prod fun t k ↦ a t ^ k) + e * Q d := by
    rw [hprod b (fun t ht ↦ Function.update_of_ne ht _ _) d, hprod a (fun _ _ ↦ rfl) d]
    have hbs : b s - a s = e := by rw [hb_def, Function.update_self, add_sub_cancel_left]
    have hpow := geom_sum₂_mul (b s) (a s) (d s)
    rw [hbs] at hpow
    linear_combination -(c d) * hpow
  -- only the monomial `Xₛ` contributes a constant coefficient to `Q`
  have hQ₀ (d : σ →₀ ℕ) : constantCoeff (Q d) = if d = Finsupp.single s 1 then 1 else 0 := by
    have hgeom : constantCoeff (∑ i ∈ Finset.range (d s), b s ^ i * a s ^ (d s - 1 - i)) =
        (d s : S) * 0 ^ (d s - 1) := by
      simp [map_sum, hb₀, ha₀, geom_sum₂_self]
    simp only [Q, map_mul, hgeom]
    split_ifs with hd
    · subst hd
      simp [c]
    · by_cases h₁ : d.erase s = 0
      · have h₀ : d s ≠ 1 := fun h₀ ↦ hd <| by
          rw [← Finsupp.single_add_erase s d, h₁, h₀, add_zero]
        rcases Nat.lt_or_gt_of_ne h₀ with h₀ | h₀
        · simp [show d s = 0 by omega]
        · simp [zero_pow (show d s - 1 ≠ 0 by omega)]
      · obtain ⟨t, ht⟩ := Finsupp.support_nonempty_iff.mpr h₁
        have hc : constantCoeff (c d) = 0 := by
          simp only [c, Finsupp.prod, map_prod, map_pow, ha₀]
          exact Finset.prod_eq_zero ht (zero_pow (Finsupp.mem_support_iff.mp ht))
        simp [hc]
  refine nat_le_order fun m hm ↦ ?_
  have hfin := coeff_subst_finite ha f m
  rw [map_sub, map_sub, coeff_subst hb, coeff_subst ha, coeff_smul, sub_eq_zero, sub_eq_iff_eq_add']
  -- below degree `n + 1`, multiplying `e` by `Q d` scales it by the constant coefficient of `Q d`
  simp_rw [hQ, map_add,
    coeff_mul_eq_coeff_mul_constantCoeff_of_le_order he _ (Nat.lt_succ_iff.mp hm), hQ₀, smul_add]
  rw [finsum_add_distrib hfin, add_right_inj, finsum_eq_single _ (Finsupp.single s 1)]
  · simp [Algebra.smul_def]
  · intro d hd
    simp [hd]
  · refine (Set.finite_singleton (Finsupp.single s 1)).subset fun d hd ↦ ?_
    by_contra h
    exact hd (by simp [show d ≠ Finsupp.single s 1 from h])

end Perturbation

open Finsupp

variable {R : Type*} {f : MvPowerSeries (Fin 2) R}

/-- A series whose two linear coefficients are one has degree-one homogeneous component
`X + Y`, independently of its constant coefficient. -/
theorem homogeneousComponent_one_eq_X_add_X [Semiring R]
    (hX : coeff (single 0 1) f = 1) (hY : coeff (single 1 1) f = 1) :
    homogeneousComponent 1 f = X 0 + X 1 := by
  ext d
  rw [coeff_homogeneousComponent]
  by_cases hdeg : d.degree = 1
  · obtain ⟨j, rfl⟩ := (Set.ext_iff.mp range_single_one d).mpr hdeg
    fin_cases j <;> simp [hX, hY, coeff_X, single_eq_single_iff]
  · have hX' : d ≠ single 0 1 := fun h ↦ hdeg (by simp [h])
    have hY' : d ≠ single 1 1 := fun h ↦ hdeg (by simp [h])
    simp [hdeg, coeff_X, hX', hY']

section Ring

variable [Ring R]

/-- A power series in two variables with zero constant coefficient and linear part `X + Y` differs
from `X + Y` by a series of order at least two. -/
theorem two_le_order_sub_X_add_X (h₀ : f.constantCoeff = 0)
    (hX : coeff (single 0 1) f = 1) (hY : coeff (single 1 1) f = 1) :
    2 ≤ (f - (X 0 + X 1)).order := by
  refine nat_le_order (n := 2) fun d hd => ?_
  have hdeg : d.degree = 0 ∨ d.degree = 1 := by omega
  rcases hdeg with hdeg | hdeg
  · simp [(degree_eq_zero_iff d).mp hdeg, h₀]
  · have hc := congrArg (coeff d) (homogeneousComponent_one_eq_X_add_X hX hY)
    simp only [coeff_homogeneousComponent, ite_eq_left hdeg] at hc
    simp [hc]

end Ring

section CommRing

variable {τ S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- If `f` has zero constant coefficient and linear part `X + Y`, the linear part of `f(x, y)` is
the sum of the linear parts of `x` and `y`, for `x` and `y` without constant coefficient. -/
theorem homogeneousComponent_one_subst_pair (h₀ : f.constantCoeff = 0)
    (hX : coeff (single 0 1) f = 1) (hY : coeff (single 1 1) f = 1) {x y : MvPowerSeries τ S}
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    homogeneousComponent 1 (f.subst ![x, y]) =
      homogeneousComponent 1 x + homogeneousComponent 1 y := by
  have hxy : HasSubst ![x, y] := hasSubst_of_constantCoeff_zero fun i ↦ by
    fin_cases i <;> simp [hx, hy]
  have hl := hxy.homogeneousComponent_one
  rw [homogeneousComponent_subst_of_le_order
      (by simpa using one_le_order_iff_constCoeff_eq_zero.mpr h₀) hxy
      (fun i ↦ by fin_cases i <;> simp [hx, hy]),
    homogeneousComponent_one_eq_X_add_X hX hY, subst_add hl, subst_X hl, subst_X hl]
  simp

end CommRing

end MvPowerSeries
