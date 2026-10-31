/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Order
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
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
the polynomial `f_p(X + Y, Z)`. In finitely many variables `f_p` is a polynomial, the degree-`p`
part of the truncation of `f`, and the degree-`p` component of `f(a)` is its evaluation at the
linear parts of the `a i` (`MvPowerSeries.homogeneousComponent_subst_eq_aeval`). Substituting
series without constant coefficient does not lower the order
(`MvPowerSeries.order_le_order_subst`).

Perturbing one entry `a s` by a series `e` of order at least `n ≥ 1` changes `f(a)` by `c e`, where
`c` is the coefficient of `Xₛ` in `f`, up to terms of degree greater than `n`
(`MvPowerSeries.le_order_subst_update_add_sub`). For a formal group law this says that
`F(x + e, y) ≡ F(x, y) + e` to lowest order.

A common lower bound on the orders of two series bounds the orders of their sum and difference
(`MvPowerSeries.le_order_add`, `MvPowerSeries.le_order_sub`).
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
  ext d
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

section TruncTotal

variable {σ τ R : Type*} [Finite σ] [CommRing R]

/-- The degree-`n` homogeneous component of a power series, read off from its truncation as a
polynomial. -/
theorem coe_homogeneousComponent_truncTotal (n : ℕ) (f : MvPowerSeries σ R) :
    ((MvPolynomial.homogeneousComponent n (truncTotal (n + 1) f) : MvPolynomial σ R) :
      MvPowerSeries σ R) = homogeneousComponent n f := by
  ext d
  rw [MvPolynomial.coeff_coe, MvPolynomial.coeff_homogeneousComponent,
    coeff_homogeneousComponent]
  split_ifs with hd
  · exact coeff_truncTotal f (by omega)
  · rfl

/-- **The lowest-degree component of a substitution, as a polynomial.** If `f` has order at least
`n` and the series `a i` have zero constant coefficient and linear parts `l i`, the degree-`n`
component of `f(a)` is the degree-`n` part of `f` evaluated at the polynomials `l i`. -/
theorem homogeneousComponent_subst_eq_aeval {f : MvPowerSeries σ R} {n : ℕ} (hn : n ≤ f.order)
    {a : σ → MvPowerSeries τ R} (ha : HasSubst a) (ha₀ : ∀ i, constantCoeff (a i) = 0)
    {l : σ → MvPolynomial τ R} (hl : ∀ i, homogeneousComponent 1 (a i) = l i) :
    homogeneousComponent n (f.subst a) =
      (MvPolynomial.aeval l (MvPolynomial.homogeneousComponent n (truncTotal (n + 1) f)) :
        MvPowerSeries τ R) := by
  rw [homogeneousComponent_subst_of_le_order hn ha ha₀, ← coe_homogeneousComponent_truncTotal,
    subst_coe]
  simp_rw [hl]
  simpa using (MvPolynomial.comp_aeval_apply (MvPolynomial.coeToMvPowerSeries.algHom R)
    (MvPolynomial.homogeneousComponent n (truncTotal (n + 1) f)) (f := l)).symm

end TruncTotal

/-- Substituting series without constant coefficient does not lower the order. -/
theorem order_le_order_subst {σ τ R : Type*} [CommRing R] {a : σ → MvPowerSeries τ R}
    (ha : HasSubst a) (ha₀ : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ R) :
    f.order ≤ (f.subst a).order := by
  refine le_trans ?_ (le_order_subst ha f)
  calc f.order = 1 * f.order := (one_mul _).symm
    _ ≤ (⨅ i, (a i).order) * f.order := by
      gcongr
      exact le_iInf fun i ↦ one_le_order_iff_constCoeff_eq_zero.mpr (ha₀ i)

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
  -- below degree `n + 1`, multiplying `e` by `Q d` scales it by the constant coefficient of `Q d`
  have hmul (q : MvPowerSeries τ S) {m : τ →₀ ℕ} (hm : m.degree < n + 1) :
      coeff m (e * q) = constantCoeff q * coeff m e := by
    have hq : (1 : ℕ∞) ≤ (q - C (constantCoeff q)).order :=
      one_le_order_iff_constCoeff_eq_zero.mpr (by simp)
    have hlt : (m.degree : ℕ∞) < (e * (q - C (constantCoeff q))).order :=
      lt_of_lt_of_le (by exact_mod_cast hm) ((add_le_add he hq).trans le_order_mul)
    have h := coeff_of_lt_order hlt
    rw [mul_sub, map_sub, coeff_mul_C, sub_eq_zero] at h
    rw [h, mul_comm]
  refine nat_le_order fun m hm ↦ ?_
  have hfin := coeff_subst_finite ha f m
  rw [map_sub, map_sub, coeff_subst hb, coeff_subst ha, coeff_smul, sub_eq_zero, sub_eq_iff_eq_add']
  simp_rw [hQ, map_add, hmul _ hm, hQ₀, smul_add]
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
