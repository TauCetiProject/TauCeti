/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPowerSeries.Order
public import Mathlib.RingTheory.MvPowerSeries.Substitution

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
the polynomial `f_p(X + Y, Z)`.

A common lower bound on the orders of two series bounds the orders of their sum and difference
(`MvPowerSeries.le_order_add`, `MvPowerSeries.le_order_sub`).

Substitution preserves closeness: if each `a i - b i` has order at least `n ≠ 0` and the `b i`
have no constant coefficient, then `aᵈ - bᵈ` has order at least `n + |d| - 1`
(`MvPowerSeries.le_order_prod_pow_sub_prod_pow`). Expanding the coefficients of `f(a) - f(b)`
along these differences of monomials (`MvPowerSeries.coeff_subst_sub_subst`) shows that
`f(a) - f(b)` has order at least `n` (`MvPowerSeries.le_order_subst_sub_subst`), and that its
degree-`n` component only sees the linear part of `f`
(`MvPowerSeries.homogeneousComponent_subst_sub_subst`). This compares `G(x, y)` and `G(x', y')`
for a formal group law `G` and nearby arguments.

The degree-`n` component of a series is a polynomial, `MvPowerSeries.homogeneousComponentPoly`.

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

section ComponentPoly

variable {σ R : Type*} [Finite σ] [CommSemiring R]

/-- The degree-`n` homogeneous component of a power series in finitely many variables, as a
polynomial. -/
noncomputable def homogeneousComponentPoly (n : ℕ) : MvPowerSeries σ R →ₗ[R] MvPolynomial σ R :=
  (MvPolynomial.homogeneousComponent n).comp (truncTotal (n + 1))

/-- The polynomial `homogeneousComponentPoly n f` is the degree-`n` component of `f`. -/
@[simp]
theorem coe_homogeneousComponentPoly (n : ℕ) (f : MvPowerSeries σ R) :
    (homogeneousComponentPoly n f : MvPowerSeries σ R) = homogeneousComponent n f := by
  ext d
  rw [MvPolynomial.coeff_coe, homogeneousComponentPoly, LinearMap.comp_apply,
    MvPolynomial.coeff_homogeneousComponent, coeff_homogeneousComponent]
  split_ifs with hd
  · exact coeff_truncTotal _ (by omega)
  · rfl

/-- The polynomial `homogeneousComponentPoly n f` is homogeneous of degree `n`. -/
theorem isHomogeneous_homogeneousComponentPoly (n : ℕ) (f : MvPowerSeries σ R) :
    (homogeneousComponentPoly n f).IsHomogeneous n :=
  MvPolynomial.homogeneousComponent_isHomogeneous _ _

end ComponentPoly

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

section Differences

variable {σ R : Type*} [CommRing R]

/-- If `x - y` has order at least `n ≠ 0` and `y` has no constant coefficient, neither has `x`. -/
theorem constantCoeff_eq_zero_of_le_order_sub {n : ℕ} (hn : n ≠ 0) {x y : MvPowerSeries σ R}
    (hy : constantCoeff y = 0) (hxy : (n : ℕ∞) ≤ (x - y).order) : constantCoeff x = 0 := by
  have h := one_le_order_iff_constCoeff_eq_zero.mp
    ((by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn : (1 : ℕ∞) ≤ n).trans hxy)
  rwa [map_sub, hy, sub_zero] at h

/-- If `x - x'` and `y - y'` have orders at least `n + p - 1` and `n + q - 1`, where `n ≠ 0`,
and `x'` and `y` have orders at least `p` and `q`, then `x y - x' y'` has order at least
`n + (p + q) - 1`. -/
private theorem le_order_mul_sub_mul {n p q : ℕ} (hn : n ≠ 0) {x x' y y' : MvPowerSeries σ R}
    (hx : ((n + p - 1 : ℕ) : ℕ∞) ≤ (x - x').order) (hx' : (p : ℕ∞) ≤ x'.order)
    (hy : (q : ℕ∞) ≤ y.order) (hy' : ((n + q - 1 : ℕ) : ℕ∞) ≤ (y - y').order) :
    ((n + (p + q) - 1 : ℕ) : ℕ∞) ≤ (x * y - x' * y').order := by
  rw [show x * y - x' * y' = (x - x') * y + x' * (y - y') by ring]
  refine le_order_add ?_ ?_
  · calc ((n + (p + q) - 1 : ℕ) : ℕ∞) ≤ ((n + p - 1 + q : ℕ) : ℕ∞) := Nat.cast_le.mpr (by omega)
      _ = ((n + p - 1 : ℕ) : ℕ∞) + q := Nat.cast_add _ _
      _ ≤ _ := (add_le_add hx hy).trans le_order_mul
  · calc ((n + (p + q) - 1 : ℕ) : ℕ∞) = ((p + (n + q - 1) : ℕ) : ℕ∞) := by congr 1; omega
      _ = (p : ℕ∞) + ((n + q - 1 : ℕ) : ℕ∞) := Nat.cast_add _ _
      _ ≤ _ := (add_le_add hx' hy').trans le_order_mul

/-- If `x - y` has order at least `n ≠ 0` and `y` has no constant coefficient, then `xᵏ - yᵏ` has
order at least `n + k - 1`. -/
theorem le_order_pow_sub_pow {n : ℕ} (hn : n ≠ 0) {x y : MvPowerSeries σ R}
    (hy : constantCoeff y = 0) (hxy : (n : ℕ∞) ≤ (x - y).order) (k : ℕ) :
    ((n + k - 1 : ℕ) : ℕ∞) ≤ (x ^ k - y ^ k).order := by
  have hx := constantCoeff_eq_zero_of_le_order_sub hn hy hxy
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact le_order_mul_sub_mul hn ih (le_order_pow_of_constantCoeff_eq_zero k hy)
      (by exact_mod_cast one_le_order_iff_constCoeff_eq_zero.mpr hx) (by simpa using hxy)

/-- If each `a i - b i` has order at least `n ≠ 0` and the `b i` have no constant coefficient,
then the difference of the monomials `aᵈ - bᵈ` has order at least `n + |d| - 1`. -/
theorem le_order_prod_pow_sub_prod_pow {ι : Type*} {n : ℕ} (hn : n ≠ 0)
    {a b : ι → MvPowerSeries σ R} (hb : ∀ i, constantCoeff (b i) = 0)
    (hab : ∀ i, (n : ℕ∞) ≤ (a i - b i).order) (d : ι →₀ ℕ) :
    ((n + d.degree - 1 : ℕ) : ℕ∞) ≤
      ((d.prod fun i k ↦ a i ^ k) - d.prod fun i k ↦ b i ^ k).order := by
  have ha (i : ι) := constantCoeff_eq_zero_of_le_order_sub hn (hb i) (hab i)
  induction d using Finsupp.induction with
  | zero => simp
  | single_add i k d _ _ ih =>
    rw [Finsupp.prod_add_index' (fun _ ↦ pow_zero _) (fun _ _ _ ↦ pow_add _ _ _),
      Finsupp.prod_add_index' (fun _ ↦ pow_zero _) (fun _ _ _ ↦ pow_add _ _ _),
      Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp), map_add,
      Finsupp.degree_single]
    exact le_order_mul_sub_mul hn (le_order_pow_sub_pow hn (hb i) (hab i) k)
      (le_order_pow_of_constantCoeff_eq_zero k (hb i)) (degree_le_order_prod_pow ha d) ih

/-- If each `a i - b i` has order at least `n ≠ 0` and the `b i` have no constant coefficient,
then the coefficients of `aᵈ - bᵈ` vanish in degrees `e` with `|e| + 1 < n + |d|`. -/
theorem coeff_prod_pow_sub_prod_pow_eq_zero {ι : Type*} {n : ℕ} (hn : n ≠ 0)
    {a b : ι → MvPowerSeries σ R} (hb : ∀ i, constantCoeff (b i) = 0)
    (hab : ∀ i, (n : ℕ∞) ≤ (a i - b i).order) {d : ι →₀ ℕ} {e : σ →₀ ℕ}
    (he : e.degree + 1 < n + d.degree) :
    coeff e ((d.prod fun i k ↦ a i ^ k) - d.prod fun i k ↦ b i ^ k) = 0 :=
  coeff_of_lt_order ((Nat.cast_lt.mpr (by omega)).trans_le
    (le_order_prod_pow_sub_prod_pow hn hb hab d))

end Differences

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

/-- A coefficient of `f(a) - f(b)` is the sum of the coefficients of `f` against the corresponding
coefficients of the differences of monomials `aᵈ - bᵈ`. -/
theorem coeff_subst_sub_subst {a b : σ → MvPowerSeries τ S} (ha : HasSubst a)
    (hb : HasSubst b) (f : MvPowerSeries σ R) (e : τ →₀ ℕ) :
    coeff e (f.subst a - f.subst b) = ∑ᶠ d, coeff d f •
      coeff e ((d.prod fun i k ↦ a i ^ k) - d.prod fun i k ↦ b i ^ k) := by
  rw [map_sub, coeff_subst ha, coeff_subst hb,
    ← finsum_sub_distrib (coeff_subst_finite ha f e) (coeff_subst_finite hb f e)]
  simp_rw [map_sub, smul_sub]

/-- **Substitution preserves closeness.** If each `a i - b i` has order at least `n` and the `b i`
have no constant coefficient, then `f(a) - f(b)` has order at least `n`. -/
theorem le_order_subst_sub_subst {n : ℕ} {a b : σ → MvPowerSeries τ S} (ha : HasSubst a)
    (hb : HasSubst b) (hb₀ : ∀ i, constantCoeff (b i) = 0)
    (hab : ∀ i, (n : ℕ∞) ≤ (a i - b i).order) (f : MvPowerSeries σ R) :
    (n : ℕ∞) ≤ (f.subst a - f.subst b).order := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  refine nat_le_order fun e he ↦ ?_
  rw [coeff_subst_sub_subst ha hb]
  refine finsum_eq_zero_of_forall_eq_zero fun d ↦ ?_
  obtain rfl | hd := eq_or_ne d 0
  · simp
  have hdeg : d.degree ≠ 0 := by rwa [Ne, Finsupp.degree_eq_zero_iff]
  rw [coeff_prod_pow_sub_prod_pow_eq_zero hn hb₀ hab (by omega), smul_zero]

/-- **The lowest-degree component of a difference of substitutions.** If each `a i - b i` has order
at least `n ≠ 0` and the `b i` have no constant coefficient, then the degree-`n` component of
`f(a) - f(b)` only sees the linear part of `f`: it is `∑ᵢ fᵢ (a i - b i)ₙ`, where `fᵢ` is the
coefficient of `Xᵢ` in `f`. -/
theorem homogeneousComponent_subst_sub_subst [Fintype σ] {n : ℕ} (hn : n ≠ 0)
    {a b : σ → MvPowerSeries τ S} (ha : HasSubst a) (hb : HasSubst b)
    (hb₀ : ∀ i, constantCoeff (b i) = 0) (hab : ∀ i, (n : ℕ∞) ≤ (a i - b i).order)
    (f : MvPowerSeries σ R) :
    homogeneousComponent n (f.subst a - f.subst b) =
      ∑ i, coeff (Finsupp.single i 1) f • homogeneousComponent n (a i - b i) := by
  classical
  ext e
  rw [coeff_homogeneousComponent]
  split_ifs with he
  swap
  · simp [coeff_homogeneousComponent, he]
  set g : (σ →₀ ℕ) → S := fun d ↦ coeff d f •
    coeff e ((d.prod fun i k ↦ a i ^ k) - d.prod fun i k ↦ b i ^ k)
  calc coeff e (f.subst a - f.subst b) = ∑ᶠ d, g d := coeff_subst_sub_subst ha hb f e
    _ = ∑ d ∈ Finset.univ.image fun i : σ ↦ Finsupp.single i 1, g d := by
      refine finsum_eq_sum_of_support_subset _ fun d hd ↦ ?_
      -- only the monomials of degree one contribute in degree `n`
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, Finsupp.range_single_one]
      by_contra hd1
      obtain rfl | hd0 := eq_or_ne d 0
      · simp [g] at hd
      have hdeg : d.degree ≠ 0 := by rwa [Ne, Finsupp.degree_eq_zero_iff]
      rw [Set.mem_ofPred_eq] at hd1
      exact hd (by
        simp only [g]
        rw [coeff_prod_pow_sub_prod_pow_eq_zero hn hb₀ hab (by omega), smul_zero])
    _ = ∑ i, g (Finsupp.single i 1) :=
      Finset.sum_image fun i _ j _ h ↦ Finsupp.single_left_injective one_ne_zero h
    _ = coeff e (∑ i, coeff (Finsupp.single i 1) f • homogeneousComponent n (a i - b i)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp only [g]
      rw [Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp), pow_one,
        pow_one]
      simp [coeff_homogeneousComponent, he]

end Subst

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
