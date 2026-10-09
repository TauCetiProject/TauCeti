/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.RingTheory.PowerSeries.GaussNorm
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Basic
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.Prod
public import TauCeti.RingTheory.PowerSeries.Restricted
import Mathlib.Algebra.Order.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.RingTheory.Polynomial.GaussNorm

/-!
# The Gauss norm of restricted power series

A restricted power series has finite Gauss norm. At a positive radius, a nonzero restricted
series has a last coefficient attaining that norm; the degree of that coefficient is the
*distinguished degree* of the series, and `IsDistinguished` names the property. Over a
nonarchimedean normed ring with multiplicative norm, a pair of distinguished degrees produces a
dominant coefficient in a product, and the Gauss norm is therefore multiplicative on restricted
series.

The distinguished degree is the datum Weierstrass division and preparation for Tate algebras are
organised around. Distinguishedness and its product law need only a seminormed coefficient ring;
nonzero restricted series attain a distinguished degree over a normed ring. No completeness
hypothesis is needed for these norm identities. The radius is any positive real number, including
the unit radius of the usual Tate algebra.

Completeness enters only in the summation section, where a family of restricted series with
summable Gauss norms is summed coefficientwise. This is the convergence statement that
successive-approximation arguments over a complete nonarchimedean ring run on, and it takes the
place of completeness of the Tate algebra for the Gauss norm.

Multiplicativity and the ultrametric inequality together make the Gauss norm a valuation with
values in `ℝ≥0` on the ring of restricted series, `gaussValuation`, whose support is trivial.
Pulled back to the Tate algebra at radii at most one, these valuations give the Gauss points of the
closed unit disc.

The Gauss norm at a positive radius is attained in a finite nonempty set of degrees. Its largest
element is the distinguished degree, and its smallest is the *lowest dominant degree*
(`IsLowestDominant`); both are additive on products. Recording one of them next to the Gauss norm
refines `gaussValuation` to a valuation with values in the lexicographically ordered group
`ℝ≥0ˣ ×ₗ ℤ`: `gaussValuationAbove` records the distinguished degree and `gaussValuationBelow` the
negated lowest dominant degree. They are the Gauss norms at a radius infinitesimally above and
infinitesimally below `c`, and pulled back to the Tate algebra they give the rank-two points of the
closed unit disc next to its Gauss points.

## Main definitions

* `TauCeti.PowerSeries.gaussValuation`: at a positive radius, the Gauss norm as a valuation with
  values in `ℝ≥0` on the ring of restricted series.
* `TauCeti.PowerSeries.IsDistinguished`: the Gauss norm is attained in degree `s` and every later
  coefficient is strictly smaller.
* `TauCeti.PowerSeries.IsLowestDominant`: the Gauss norm is positive and attained in degree `s`,
  and every earlier coefficient is strictly smaller.
* `TauCeti.PowerSeries.gaussValuationAbove` and `TauCeti.PowerSeries.gaussValuationBelow`: the
  Gauss valuations just above and just below a positive radius, with values in `ℝ≥0ˣ ×ₗ ℤ`.

## Main results

* `TauCeti.PowerSeries.hasGaussNorm_add` and `TauCeti.PowerSeries.hasGaussNorm_mul`: bounded
  weighted coefficient norms are preserved by addition and multiplication over an ultrametric
  seminormed ring, at any nonnegative radius.
* `TauCeti.PowerSeries.gaussNorm_eq_of_forall_le`: the Gauss norm is attained at a degree whose
  weighted coefficient dominates.
* `TauCeti.PowerSeries.exists_isDistinguished`: at a positive radius, every nonzero restricted
  series is distinguished of some degree.
* `TauCeti.PowerSeries.IsDistinguished.unique`: of no more than one degree.
* `TauCeti.PowerSeries.isDistinguished_of_norm_coeff_sub_lt`: over an ultrametric ring, a series
  is distinguished once its coefficient in degree `s` is close to an element of maximal norm.
* `TauCeti.PowerSeries.IsDistinguished.trunc`,
  `TauCeti.PowerSeries.IsDistinguished.gaussNorm_trunc` and
  `TauCeti.PowerSeries.IsDistinguished.gaussNorm_sub_trunc_lt`: the polynomial part of a
  distinguished series is distinguished of the same degree and the same Gauss norm, and the
  tail it leaves is strictly smaller.
* `TauCeti.PowerSeries.IsDistinguished.norm_coeff_mul_mul_pow_eq_gaussNorm_mul`: the dominant
  coefficient of a product of distinguished series.
* `TauCeti.PowerSeries.exists_isLowestDominant`, `TauCeti.PowerSeries.IsLowestDominant.unique`
  and `TauCeti.PowerSeries.IsLowestDominant.mul`: a nonzero restricted series has exactly one
  lowest dominant degree, and lowest dominant degrees add under multiplication.
* `TauCeti.PowerSeries.gaussNorm_mul_of_isRestricted`: multiplicativity of the Gauss norm.
* `TauCeti.PowerSeries.gaussValuationAbove_le_iff` and
  `TauCeti.PowerSeries.gaussValuationBelow_le_iff`: the two refined Gauss valuations compare
  Gauss norms first, and then distinguished degrees, respectively lowest dominant degrees in the
  reverse order.
* `TauCeti.PowerSeries.gaussValuation_eq_zero_iff`: the Gauss valuation vanishes only at zero.
* `TauCeti.PowerSeries.summable_coeff_of_summable_gaussNorm` and
  `TauCeti.PowerSeries.isRestricted_mk_tsum_coeff`: over a complete ring, a family of restricted
  series with summable Gauss norms has summable coefficients, and its coefficientwise sum is
  again restricted.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.

The dominant-coefficient argument follows Mathlib's proof of `Polynomial.gaussNorm_mul`;
restrictedness replaces the finite-support argument for attaining the maximum. We use Mathlib's
`PowerSeries.IsRestricted` and `PowerSeries.gaussNorm` throughout.
-/

public section

namespace TauCeti.PowerSeries

open Filter
open scoped Topology

section SeminormedRing

variable {R : Type*} [SeminormedRing R] [IsUltrametricDist R]
  {c : ℝ} {f g : PowerSeries R}

variable (f g) in
/-- Over an ultrametric ring, each weighted coefficient norm of a sum is at most the larger of the
two summands' weighted coefficient norms, at a nonnegative radius. -/
theorem norm_coeff_add_mul_pow_le_max (hc : 0 ≤ c) (m : ℕ) :
    ‖(f + g).coeff m‖ * c ^ m ≤ max (‖f.coeff m‖ * c ^ m) (‖g.coeff m‖ * c ^ m) := by
  rw [map_add, ← max_mul_of_nonneg _ _ (pow_nonneg hc m)]
  exact mul_le_mul_of_nonneg_right (IsUltrametricDist.isNonarchimedean_norm _ _) (pow_nonneg hc m)

/-- The sum of two power series with bounded weighted coefficient norms again has bounded weighted
coefficient norms at a nonnegative radius. -/
theorem hasGaussNorm_add (hc : 0 ≤ c) (hf : f.HasGaussNorm norm c)
    (hg : g.HasGaussNorm norm c) : (f + g).HasGaussNorm norm c :=
  ⟨_, Set.forall_mem_range.mpr fun m ↦ (norm_coeff_add_mul_pow_le_max f g hc m).trans
    (max_le_max (PowerSeries.le_gaussNorm norm c _ hf m) (PowerSeries.le_gaussNorm norm c _ hg m))⟩

/-- The product of two power series with bounded weighted coefficient norms again has bounded
weighted coefficient norms at a nonnegative radius. -/
theorem hasGaussNorm_mul (hc : 0 ≤ c) (hf : f.HasGaussNorm norm c)
    (hg : g.HasGaussNorm norm c) : (f * g).HasGaussNorm norm c := by
  have key (m : ℕ) :
      ‖(f * g).coeff m‖ * c ^ m ≤ f.gaussNorm norm c * g.gaussNorm norm c := by
    rw [PowerSeries.coeff_mul]
    have hne := Finset.HasAntidiagonal.nonempty_antidiagonal m
    calc
      ‖∑ p ∈ Finset.antidiagonal m, f.coeff p.1 * g.coeff p.2‖ * c ^ m
          ≤ (Finset.antidiagonal m).sup' hne
              (fun p : ℕ × ℕ ↦ ‖f.coeff p.1 * g.coeff p.2‖) * c ^ m :=
        mul_le_mul_of_nonneg_right (hne.norm_sum_le_sup'_norm
          (fun p : ℕ × ℕ ↦ f.coeff p.1 * g.coeff p.2)) (pow_nonneg hc m)
      _ = (Finset.antidiagonal m).sup' hne
          (fun p : ℕ × ℕ ↦ ‖f.coeff p.1 * g.coeff p.2‖ * c ^ m) :=
        Finset.sup'_mul₀ (pow_nonneg hc m) _ _ _
      _ ≤ f.gaussNorm norm c * g.gaussNorm norm c :=
        (Finset.sup'_le_iff hne
          (fun p : ℕ × ℕ ↦ ‖f.coeff p.1 * g.coeff p.2‖ * c ^ m)).2 fun p hp ↦ by
          have hsum : p.1 + p.2 = m := Finset.mem_antidiagonal.mp hp
          rw [← hsum, pow_add]
          calc
            ‖f.coeff p.1 * g.coeff p.2‖ * (c ^ p.1 * c ^ p.2)
                ≤ ‖f.coeff p.1‖ * ‖g.coeff p.2‖ * (c ^ p.1 * c ^ p.2) :=
              mul_le_mul_of_nonneg_right (norm_mul_le _ _)
                (mul_nonneg (pow_nonneg hc _) (pow_nonneg hc _))
            _ = (‖f.coeff p.1‖ * c ^ p.1) * (‖g.coeff p.2‖ * c ^ p.2) := by ring
            _ ≤ f.gaussNorm norm c * g.gaussNorm norm c :=
              mul_le_mul (PowerSeries.le_gaussNorm norm c f hf p.1)
                (PowerSeries.le_gaussNorm norm c g hg p.2)
                (mul_nonneg (norm_nonneg _) (pow_nonneg hc _))
                (PowerSeries.gaussNorm_nonneg norm c f norm_nonneg)
  exact ⟨_, Set.forall_mem_range.mpr key⟩

end SeminormedRing

variable {R : Type*} [NormedRing R] {c : ℝ} {i j s t : ℕ} {f g : PowerSeries R}

/-- A restricted power series has bounded weighted coefficient norms. -/
theorem hasGaussNorm_of_isRestricted (hf : f.IsRestricted c) :
    f.HasGaussNorm norm c :=
  ((PowerSeries.isRestricted_iff c f).mp hf).bddAbove_range_of_cofinite

/-- If the weighted coefficient in degree `s` dominates every other one, the Gauss norm is the
value it takes there. -/
theorem gaussNorm_eq_of_forall_le {S : Type*} [Semiring S] {v : S → ℝ} {a : PowerSeries S}
    (h : ∀ m, v (a.coeff m) * c ^ m ≤ v (a.coeff s) * c ^ s) :
    a.gaussNorm v c = v (a.coeff s) * c ^ s :=
  le_antisymm ((PowerSeries.gaussNorm_eq v c a).trans_le (ciSup_le h))
    (PowerSeries.le_gaussNorm v c a ⟨_, Set.forall_mem_range.mpr h⟩ s)

section Distinguished

variable {R : Type*} [SeminormedRing R] {f : PowerSeries R}

section

variable (c) (s) (f)

/-- `f` is **distinguished of degree `s`** at the radius `c` when its Gauss norm at `c` is attained
in degree `s` and every later coefficient is strictly smaller.

At the unit radius this is a norm-theoretic analogue of the classical condition that the leading
coefficient of `f` dominates, in the sense of Bosch–Güntzer–Remmert §5.2. At a positive radius, a
nonzero restricted series is distinguished of exactly one degree
(`TauCeti.PowerSeries.exists_isDistinguished` and
`TauCeti.PowerSeries.IsDistinguished.unique`), so this is a genuine invariant of `f` and `c` rather
than extra data.

The first field is the univariate reading of Mathlib's `MvPowerSeries.AchievesGaussNorm`; the
second is what makes the degree unique and pins down the dominant coefficient of a product.

This is unrelated to `Polynomial.IsDistinguishedAt`, which asks a polynomial to be monic with its
remaining coefficients in an ideal. -/
structure IsDistinguished : Prop where
  /-- The Gauss norm is attained in degree `s`. -/
  norm_coeff_mul_pow_eq : ‖f.coeff s‖ * c ^ s = f.gaussNorm norm c
  /-- Every coefficient in a degree past `s` is strictly smaller. -/
  norm_coeff_mul_pow_lt : ∀ m, s < m → ‖f.coeff m‖ * c ^ m < f.gaussNorm norm c

end

/-- A distinguished series has positive Gauss norm, without any sign assumption on the radius. -/
theorem IsDistinguished.gaussNorm_pos (hf : IsDistinguished c s f) :
    0 < f.gaussNorm norm c := by
  have hpow : 0 ≤ c ^ (2 * (s + 1)) := by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg c) _
  exact lt_of_le_of_lt (mul_nonneg (norm_nonneg _) hpow)
    (hf.norm_coeff_mul_pow_lt (2 * (s + 1)) (by omega))

/-- A distinguished series is nonzero. -/
theorem IsDistinguished.ne_zero (hf : IsDistinguished c s f) : f ≠ 0 := by
  rintro rfl
  have h := hf.gaussNorm_pos
  rw [PowerSeries.gaussNorm_zero norm c (norm_zero : ‖(0 : R)‖ = 0)] at h
  exact absurd h (lt_irrefl 0)

/-- The coefficient of a distinguished series in its distinguished degree is nonzero. -/
theorem IsDistinguished.coeff_ne_zero (hf : IsDistinguished c s f) : f.coeff s ≠ 0 := by
  intro h
  have hpos := hf.gaussNorm_pos
  rw [← hf.norm_coeff_mul_pow_eq, h] at hpos
  simp at hpos

/-- The weighted coefficient norms of a distinguished series are bounded above. -/
theorem IsDistinguished.hasGaussNorm (hf : IsDistinguished c s f) :
    f.HasGaussNorm norm c := by
  refine (Filter.isBoundedUnder_of_eventually_le (a := f.gaussNorm norm c) ?_).bddAbove_range
  filter_upwards [Filter.eventually_gt_atTop s] with n hn
  exact (hf.norm_coeff_mul_pow_lt n hn).le

/-- The distinguished degree is unique: a series cannot be distinguished of two degrees at the
same radius. -/
theorem IsDistinguished.unique (hf : IsDistinguished c s f) (hf' : IsDistinguished c t f) :
    s = t := by
  rcases lt_trichotomy s t with h | h | h
  · exact absurd hf'.norm_coeff_mul_pow_eq (hf.norm_coeff_mul_pow_lt t h).ne
  · exact h
  · exact absurd hf.norm_coeff_mul_pow_eq (hf'.norm_coeff_mul_pow_lt s h).ne

/-- The distinguished degree is at most any degree past which every weighted coefficient norm is
strictly below the Gauss norm. -/
theorem IsDistinguished.le_of_forall_lt (hf : IsDistinguished c s f)
    (h : ∀ m, t < m → ‖f.coeff m‖ * c ^ m < f.gaussNorm norm c) : s ≤ t :=
  not_lt.mp fun hts ↦ (h s hts).ne hf.norm_coeff_mul_pow_eq

end Distinguished

/-- Every nonzero restricted series is distinguished of some degree: its last coefficient
attaining the Gauss norm supplies that degree. -/
theorem exists_isDistinguished (hc : 0 < c) (hf : f.IsRestricted c) (hf0 : f ≠ 0) :
    ∃ s : ℕ, IsDistinguished c s f := by
  classical
  have hex : ∃ i, f.coeff i ≠ 0 := by
    simpa only [not_forall] using (PowerSeries.forall_coeff_eq_zero f).not.mpr hf0
  obtain ⟨i, hi⟩ := hex
  let a : ℕ → ℝ := fun n ↦ ‖f.coeff n‖ * c ^ n
  have hi_pos : 0 < a i := mul_pos (norm_pos_iff.mpr hi) (pow_pos hc _)
  have hfinite : {n | a i ≤ a n}.Finite := by
    have h : ∀ᶠ n in cofinite, a n < a i :=
      ((PowerSeries.isRestricted_iff c f).mp hf).eventually (gt_mem_nhds hi_pos)
    simpa only [eventually_cofinite, not_lt] using h
  let S := hfinite.toFinset
  have hi_mem : i ∈ S := by simp [S]
  obtain ⟨k, hk, hmax⟩ := S.exists_max_image a ⟨i, hi_mem⟩
  have hbound (m : ℕ) : a m ≤ a k := by
    by_cases hm : m ∈ S
    · exact hmax m hm
    · have hm' : a m < a i := by simpa [S] using hm
      exact hm'.le.trans (hmax i hi_mem)
  have heq : a k = f.gaussNorm norm c := (gaussNorm_eq_of_forall_le hbound).symm
  let T := S.filter fun n ↦ a n = a k
  have hk_mem : k ∈ T := by simp [T, hk]
  obtain ⟨n, hn, hnmax⟩ := T.exists_max_image id ⟨k, hk_mem⟩
  have hn_eq : a n = a k := (Finset.mem_filter.mp hn).2
  refine ⟨n, hn_eq.trans heq, fun m hm ↦ ?_⟩
  rw [← heq]
  refine lt_of_le_of_ne (hbound m) fun h ↦ ?_
  have hm_mem : m ∈ T := by
    simp only [T, Finset.mem_filter]
    exact ⟨by simpa [S] using (hmax i hi_mem).trans_eq h.symm, h⟩
  exact (not_le_of_gt hm) (hnmax m hm_mem)

/-! ### The lowest dominant degree -/

section LowestDominant

section

variable {R : Type*} [SeminormedRing R] {f : PowerSeries R}

variable (c) (s) (f) in
/-- `s` is the **lowest dominant degree** of `f` at the radius `c` when the Gauss norm of `f` at
`c` is positive and attained in degree `s`, and every earlier weighted coefficient norm is
strictly smaller.

This is the mirror image of `TauCeti.PowerSeries.IsDistinguished`, which singles out the *last*
degree attaining the Gauss norm. The two degrees agree exactly when the Gauss norm is attained
in a single degree. At a positive radius a nonzero restricted series has exactly one lowest
dominant degree (`TauCeti.PowerSeries.exists_isLowestDominant` and
`TauCeti.PowerSeries.IsLowestDominant.unique`), and over a multiplicative ultrametric norm the
lowest dominant degree of a product is the sum of those of the factors
(`TauCeti.PowerSeries.IsLowestDominant.mul`). -/
structure IsLowestDominant : Prop where
  /-- The Gauss norm is positive. -/
  gaussNorm_pos : 0 < f.gaussNorm norm c
  /-- The Gauss norm is attained in degree `s`. -/
  norm_coeff_mul_pow_eq : ‖f.coeff s‖ * c ^ s = f.gaussNorm norm c
  /-- Every coefficient in a degree before `s` is strictly smaller. -/
  norm_coeff_mul_pow_lt : ∀ m, m < s → ‖f.coeff m‖ * c ^ m < f.gaussNorm norm c

/-- The coefficient of a series in its lowest dominant degree is nonzero. -/
theorem IsLowestDominant.coeff_ne_zero (hf : IsLowestDominant c s f) : f.coeff s ≠ 0 := by
  intro h
  have hpos := hf.gaussNorm_pos
  rw [← hf.norm_coeff_mul_pow_eq, h, norm_zero, zero_mul] at hpos
  exact hpos.false

/-- A series with a lowest dominant degree is nonzero. -/
theorem IsLowestDominant.ne_zero (hf : IsLowestDominant c s f) : f ≠ 0 := by
  rintro rfl
  exact hf.coeff_ne_zero (map_zero _)

/-- The lowest dominant degree is unique. -/
theorem IsLowestDominant.unique (hf : IsLowestDominant c s f) (hf' : IsLowestDominant c t f) :
    s = t := by
  rcases lt_trichotomy s t with h | h | h
  · exact absurd hf.norm_coeff_mul_pow_eq (hf'.norm_coeff_mul_pow_lt s h).ne
  · exact h
  · exact absurd hf'.norm_coeff_mul_pow_eq (hf.norm_coeff_mul_pow_lt t h).ne

/-- The lowest dominant degree is at least any degree before which every weighted coefficient
norm is strictly below the Gauss norm. -/
theorem IsLowestDominant.le_of_forall_lt (hf : IsLowestDominant c s f)
    (h : ∀ m, m < t → ‖f.coeff m‖ * c ^ m < f.gaussNorm norm c) : t ≤ s :=
  not_lt.mp fun hst ↦ (h s hst).ne hf.norm_coeff_mul_pow_eq

end

/-- Every nonzero restricted series has a lowest dominant degree at a positive radius: the first
degree in which its Gauss norm is attained. -/
theorem exists_isLowestDominant (hc : 0 < c) (hf : f.IsRestricted c) (hf0 : f ≠ 0) :
    ∃ s : ℕ, IsLowestDominant c s f := by
  classical
  obtain ⟨k, hk⟩ := exists_isDistinguished hc hf hf0
  have hex : ∃ n, ‖f.coeff n‖ * c ^ n = f.gaussNorm norm c := ⟨k, hk.norm_coeff_mul_pow_eq⟩
  refine ⟨Nat.find hex, hk.gaussNorm_pos, Nat.find_spec hex, fun m hm ↦ ?_⟩
  exact (PowerSeries.le_gaussNorm norm c f (hasGaussNorm_of_isRestricted hf) m).lt_of_ne
      (Nat.find_min hex hm)

end LowestDominant

/-- A monomial `a Xⁿ` with `a ≠ 0` is distinguished of degree `n` at a positive radius. -/
theorem isDistinguished_monomial (hc : 0 < c) {a : R} (ha : a ≠ 0) (n : ℕ) :
    IsDistinguished c n (PowerSeries.monomial n a) := by
  have hnorm : (PowerSeries.monomial n a).gaussNorm norm c = ‖a‖ * c ^ n :=
    PowerSeries.gaussNorm_monomial (v := normRingSeminorm R) (r := a) hc.le n
  refine ⟨by rw [PowerSeries.coeff_monomial_same, hnorm], fun m hm ↦ ?_⟩
  simp only [PowerSeries.coeff_monomial, hm.ne', ite_false, norm_zero, zero_mul, hnorm]
  exact mul_pos (norm_pos_iff.mpr ha) (pow_pos hc n)

/-- A monomial `a Xⁿ` with `a ≠ 0` has lowest dominant degree `n` at a positive radius. -/
theorem isLowestDominant_monomial (hc : 0 < c) {a : R} (ha : a ≠ 0) (n : ℕ) :
    IsLowestDominant c n (PowerSeries.monomial n a) := by
  have hf := isDistinguished_monomial hc ha n
  refine ⟨hf.gaussNorm_pos, hf.norm_coeff_mul_pow_eq, fun m hm ↦ ?_⟩
  simp only [PowerSeries.coeff_monomial, hm.ne, ite_false, norm_zero, zero_mul]
  exact hf.gaussNorm_pos

section Truncation

section

variable {R : Type*} [SeminormedRing R] {f : PowerSeries R}

/-- Truncating a series just past a degree in which its Gauss norm is attained leaves that norm
unchanged. -/
@[simp] theorem IsDistinguished.gaussNorm_trunc (hf : IsDistinguished c s f) :
    ((f.trunc (s + 1) : Polynomial R) : PowerSeries R).gaussNorm norm c
      = f.gaussNorm norm c := by
  refine (gaussNorm_eq_of_forall_le (s := s) fun m ↦ ?_).trans ?_
  · simp only [Polynomial.coeff_coe, PowerSeries.coeff_trunc,
      ite_eq_left (by omega : s < s + 1)]
    rw [hf.norm_coeff_mul_pow_eq]
    split_ifs
    · exact PowerSeries.le_gaussNorm norm c f hf.hasGaussNorm m
    · simpa using PowerSeries.gaussNorm_nonneg norm c f norm_nonneg
  · simpa only [Polynomial.coeff_coe, PowerSeries.coeff_trunc,
      ite_eq_left (by omega : s < s + 1)] using hf.norm_coeff_mul_pow_eq

/-- The truncation of a distinguished series just past its distinguished degree is again
distinguished of that degree. It is the polynomial part `f⁻` a Weierstrass division divides by. -/
theorem IsDistinguished.trunc (hf : IsDistinguished c s f) :
    IsDistinguished c s ((f.trunc (s + 1) : Polynomial R) : PowerSeries R) := by
  refine ⟨?_, fun m hm ↦ ?_⟩
  · rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc,
      ite_eq_left (by omega : s < s + 1), hf.gaussNorm_trunc]
    exact hf.norm_coeff_mul_pow_eq
  · simpa only [Polynomial.coeff_coe, PowerSeries.coeff_trunc,
      ite_eq_right (by omega : ¬ m < s + 1), norm_zero, zero_mul, hf.gaussNorm_trunc]
      using hf.gaussNorm_pos

end

/-- The tail `f⁺` left by truncating a restricted distinguished series just past its
distinguished degree has strictly smaller Gauss norm than the series itself. This is the
contraction factor of the Weierstrass division algorithm. -/
theorem IsDistinguished.gaussNorm_sub_trunc_lt (hf : IsDistinguished c s f) (hc : 0 < c)
    (hfr : f.IsRestricted c) :
    (f - ((f.trunc (s + 1) : Polynomial R) : PowerSeries R)).gaussNorm norm c
      < f.gaussNorm norm c := by
  have hcoeff (m : ℕ) : (f - ((f.trunc (s + 1) : Polynomial R) : PowerSeries R)).coeff m =
      if m < s + 1 then 0 else f.coeff m := by
    rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    split_ifs <;> simp
  have htr : (f - ((f.trunc (s + 1) : Polynomial R) : PowerSeries R)).IsRestricted c := by
    rw [sub_eq_add_neg]
    exact PowerSeries.isRestricted.add c hfr
      (PowerSeries.isRestricted.neg c (isRestricted_polynomial _))
  rcases eq_or_ne (f - ((f.trunc (s + 1) : Polynomial R) : PowerSeries R)) 0 with h0 | h0
  · rw [h0, PowerSeries.gaussNorm_zero norm c (norm_zero : ‖(0 : R)‖ = 0)]
    exact hf.gaussNorm_pos
  · obtain ⟨n, hn⟩ := exists_isDistinguished hc htr h0
    have hns : s < n := by
      by_contra hcon
      exact hn.coeff_ne_zero (by rw [hcoeff n, ite_eq_left (by omega)])
    rw [← hn.norm_coeff_mul_pow_eq, hcoeff n, ite_eq_right (by omega)]
    exact hf.norm_coeff_mul_pow_lt n hns

end Truncation

section Recognition

variable {R : Type*} [SeminormedRing R] [IsUltrametricDist R] {f : PowerSeries R}

/-- **Recognising a distinguished series.** At a positive radius, `f` is distinguished of degree
`s` once its weighted coefficient in degree `s` is closer than the Gauss norm to an element `a`
of weighted norm equal to the Gauss norm, and every later weighted coefficient norm is smaller
than the Gauss norm. -/
theorem isDistinguished_of_norm_coeff_sub_lt (hc : 0 < c) {a : R}
    (ha : ‖a‖ * c ^ s = f.gaussNorm norm c)
    (hs : ‖f.coeff s - a‖ * c ^ s < f.gaussNorm norm c)
    (hm : ∀ m, s < m → ‖f.coeff m‖ * c ^ m < f.gaussNorm norm c) :
    IsDistinguished c s f := by
  have hlt : ‖f.coeff s - a‖ < ‖a‖ := lt_of_mul_lt_mul_right (ha ▸ hs) (pow_pos hc s).le
  refine ⟨?_, hm⟩
  rw [← ha, ← sub_add_cancel (f.coeff s) a,
    IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne, max_eq_right hlt.le]

end Recognition

variable [IsUltrametricDist R]

section Summation

variable [CompleteSpace R] {ι : Type*} {a : ι → PowerSeries R}

omit [IsUltrametricDist R] in
/-- Over a complete ring, a family of power series with summable Gauss norms has summable
coefficients in every degree. -/
theorem summable_coeff_of_summable_gaussNorm (hc : 0 < c)
    (ha : ∀ k, (a k).HasGaussNorm norm c)
    (hs : Summable fun k ↦ (a k).gaussNorm norm c) (i : ℕ) :
    Summable fun k ↦ (a k).coeff i := by
  refine Summable.of_norm_bounded (hs.mul_right (c ^ i)⁻¹) fun k ↦ ?_
  rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hc i)]
  exact PowerSeries.le_gaussNorm norm c _ (ha k) i

/-- **Coefficientwise summation of restricted power series.** Over a complete nonarchimedean
ring, the degreewise sums of a family of restricted power series with summable Gauss norms
assemble into a restricted power series.

This is the convergence statement behind successive-approximation arguments such as Weierstrass
division: it plays the role of completeness of the Tate algebra for the Gauss norm. -/
theorem isRestricted_mk_tsum_coeff (hc : 0 < c) (ha : ∀ k, (a k).IsRestricted c)
    (hs : Summable fun k ↦ (a k).gaussNorm norm c) :
    (PowerSeries.mk fun i ↦ ∑' k, (a k).coeff i).IsRestricted c := by
  classical
  have hsum := summable_coeff_of_summable_gaussNorm hc
    (fun k ↦ hasGaussNorm_of_isRestricted (ha k)) hs
  rw [PowerSeries.isRestricted_iff']
  refine tendsto_order.mpr ⟨fun b hb ↦ .of_forall fun i ↦
    hb.trans_le (by positivity), fun ε hε ↦ ?_⟩
  have hsmall : {k | ¬(a k).gaussNorm norm c < ε / 2}.Finite :=
    Filter.eventually_cofinite.mp
      (hs.tendsto_cofinite_zero.eventually (gt_mem_nhds (half_pos hε)))
  let S := hsmall.toFinset
  have hpartial : (∑ k ∈ S, a k).IsRestricted c :=
    sum_mem (S := PowerSeries.IsRestricted.addSubgroup c) fun k _ ↦ ha k
  filter_upwards [((PowerSeries.isRestricted_iff' c
    (∑ k ∈ S, a k)).mp hpartial).eventually
      (gt_mem_nhds (half_pos hε))] with i hi
  have hsplit : (PowerSeries.mk fun i ↦ ∑' k, (a k).coeff i).coeff i =
      (∑ k ∈ S, a k).coeff i + ∑' k : {k // k ∉ S}, (a k).coeff i := by
    rw [PowerSeries.coeff_mk, ← (hsum i).sum_add_tsum_subtype_compl S, map_sum]
  have htail : ‖∑' k : {k // k ∉ S}, (a k).coeff i‖ * c ^ i ≤ ε / 2 := by
    rw [← le_div_iff₀ (pow_pos hc i)]
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
      (by positivity) fun k ↦ ?_
    rw [le_div_iff₀ (pow_pos hc i)]
    have hk : (a k).gaussNorm norm c < ε / 2 := by simpa [S] using k.property
    exact (PowerSeries.le_gaussNorm norm c _
      (hasGaussNorm_of_isRestricted (ha k)) i).trans hk.le
  rw [hsplit]
  calc ‖(∑ k ∈ S, a k).coeff i + ∑' k : {k // k ∉ S}, (a k).coeff i‖ * c ^ i
      ≤ max ‖(∑ k ∈ S, a k).coeff i‖ ‖∑' k : {k // k ∉ S}, (a k).coeff i‖ * c ^ i :=
        mul_le_mul_of_nonneg_right (IsUltrametricDist.isNonarchimedean_norm _ _)
          (pow_nonneg hc.le i)
    _ = max (‖(∑ k ∈ S, a k).coeff i‖ * c ^ i)
          (‖∑' k : {k // k ∉ S}, (a k).coeff i‖ * c ^ i) :=
        max_mul_of_nonneg _ _ (pow_nonneg hc.le i)
    _ < ε := max_lt (hi.trans (half_lt_self hε)) (htail.trans_lt (half_lt_self hε))

end Summation

section Multiplication

variable {R : Type*} [SeminormedRing R] [IsUltrametricDist R] [NormMulClass R]
  {f g : PowerSeries R}

omit [IsUltrametricDist R] in
/-- A product term is strictly below the product of the Gauss norms, both positive, when one of
its weighted coefficients is strictly below the corresponding Gauss norm. -/
private theorem norm_coeff_mul_mul_pow_lt_of_lt (hc : 0 < c) (hbf : f.HasGaussNorm norm c)
    (hbg : g.HasGaussNorm norm c) (hf0 : 0 < f.gaussNorm norm c) (hg0 : 0 < g.gaussNorm norm c)
    {m n : ℕ}
    (h : ‖f.coeff m‖ * c ^ m < f.gaussNorm norm c ∨ ‖g.coeff n‖ * c ^ n < g.gaussNorm norm c) :
    ‖f.coeff m * g.coeff n‖ * c ^ (m + n) <
      f.gaussNorm norm c * g.gaussNorm norm c := by
  have hweight : ‖f.coeff m * g.coeff n‖ * c ^ (m + n) =
      (‖f.coeff m‖ * c ^ m) * (‖g.coeff n‖ * c ^ n) := by
    rw [norm_mul, pow_add]
    ring
  rw [hweight]
  rcases h with h | h
  · exact (mul_le_mul_of_nonneg_left (PowerSeries.le_gaussNorm norm c g hbg n)
      (mul_nonneg (norm_nonneg _) (pow_nonneg hc.le _))).trans_lt
        (mul_lt_mul_of_pos_right h hg0)
  · exact (mul_le_mul_of_nonneg_right (PowerSeries.le_gaussNorm norm c f hbf m)
      (mul_nonneg (norm_nonneg _) (pow_nonneg hc.le _))).trans_lt
        (mul_lt_mul_of_pos_left h hf0)

/-- If degrees `i` and `j` attain the Gauss norms of `f` and `g`, and every other product term in
degree `i + j` is strictly below the product of the Gauss norms, then the coefficient of `f * g`
in degree `i + j` realises that product. -/
private theorem norm_coeff_mul_mul_pow_eq_of_lt (hc : 0 < c)
    (hfi : ‖f.coeff i‖ * c ^ i = f.gaussNorm norm c)
    (hgj : ‖g.coeff j‖ * c ^ j = g.gaussNorm norm c)
    (hlt : ∀ m n, m + n = i + j → (m, n) ≠ (i, j) →
      ‖f.coeff m * g.coeff n‖ * c ^ (m + n) < f.gaussNorm norm c * g.gaussNorm norm c) :
    ‖(f * g).coeff (i + j)‖ * c ^ (i + j) = f.gaussNorm norm c * g.gaussNorm norm c := by
  have hdom (p : ℕ × ℕ) (hp : p ∈ Finset.antidiagonal (i + j)) (hne : p ≠ (i, j)) :
      ‖f.coeff p.1 * g.coeff p.2‖ < ‖f.coeff i * g.coeff j‖ := by
    have hsum : p.1 + p.2 = i + j := Finset.mem_antidiagonal.mp hp
    apply (mul_lt_mul_iff_left₀ (pow_pos hc (i + j))).mp
    calc
      ‖f.coeff p.1 * g.coeff p.2‖ * c ^ (i + j)
          < f.gaussNorm norm c * g.gaussNorm norm c := by
        simpa only [hsum] using hlt p.1 p.2 hsum hne
      _ = ‖f.coeff i * g.coeff j‖ * c ^ (i + j) := by
        rw [norm_mul, pow_add, ← hfi, ← hgj]
        ring
  have hcoeff : ‖(f * g).coeff (i + j)‖ = ‖f.coeff i * g.coeff j‖ := by
    rw [PowerSeries.coeff_mul]
    exact IsUltrametricDist.isNonarchimedean_norm.apply_sum_eq_of_lt
      (fun p : ℕ × ℕ ↦ f.coeff p.1 * g.coeff p.2) norm_neg
      (Finset.mem_antidiagonal.mpr (rfl : i + j = i + j)) hdom
  rw [hcoeff, norm_mul, pow_add, ← hfi, ← hgj]
  ring

omit [NormMulClass R] in
/-- If every product term in degree `m` is strictly below the product of the Gauss norms, so is
the coefficient of `f * g` in degree `m`. -/
private theorem norm_coeff_mul_mul_pow_lt_of_forall_lt (hc : 0 ≤ c) {m : ℕ}
    (hlt : ∀ m₁ m₂, m₁ + m₂ = m →
      ‖f.coeff m₁ * g.coeff m₂‖ * c ^ (m₁ + m₂) < f.gaussNorm norm c * g.gaussNorm norm c) :
    ‖(f * g).coeff m‖ * c ^ m < f.gaussNorm norm c * g.gaussNorm norm c := by
  rw [PowerSeries.coeff_mul]
  have hne := Finset.HasAntidiagonal.nonempty_antidiagonal m
  calc
    ‖∑ p ∈ Finset.antidiagonal m, f.coeff p.1 * g.coeff p.2‖ * c ^ m
        ≤ (Finset.antidiagonal m).sup' hne
            (fun p : ℕ × ℕ ↦ ‖f.coeff p.1 * g.coeff p.2‖) * c ^ m :=
      mul_le_mul_of_nonneg_right (hne.norm_sum_le_sup'_norm
        (fun p : ℕ × ℕ ↦ f.coeff p.1 * g.coeff p.2)) (pow_nonneg hc m)
    _ = (Finset.antidiagonal m).sup' hne
        (fun p : ℕ × ℕ ↦ ‖f.coeff p.1 * g.coeff p.2‖ * c ^ m) :=
      Finset.sup'_mul₀ (pow_nonneg hc m) _ _ _
    _ < f.gaussNorm norm c * g.gaussNorm norm c :=
      (Finset.sup'_lt_iff hne).2 fun p hp ↦ by
        have hsum : p.1 + p.2 = m := Finset.mem_antidiagonal.mp hp
        simpa only [hsum] using hlt p.1 p.2 hsum

omit [NormMulClass R] in
/-- A degree in which the coefficient of `f * g` realises the product of the Gauss norms makes the
Gauss norm of `f * g` that product. -/
private theorem gaussNorm_mul_eq_of_norm_coeff_mul_pow_eq (hc : 0 < c)
    (hbf : f.HasGaussNorm norm c) (hbg : g.HasGaussNorm norm c) {k : ℕ}
    (hk : ‖(f * g).coeff k‖ * c ^ k = f.gaussNorm norm c * g.gaussNorm norm c) :
    (f * g).gaussNorm norm c = f.gaussNorm norm c * g.gaussNorm norm c :=
  le_antisymm
    (MvPowerSeries.gaussNorm_mul_le norm (fun _ : Unit ↦ c) f g (fun _ ↦ hc.le)
      norm_nonneg norm_mul_le IsUltrametricDist.isNonarchimedean_norm norm_zero
      hbf.hasMvGaussNorm hbg.hasMvGaussNorm)
    (hk.symm.trans_le (PowerSeries.le_gaussNorm norm c (f * g) (hasGaussNorm_mul hc.le hbf hbg) k))

omit [IsUltrametricDist R] in
/-- A product term is strictly below the product of the Gauss norms when one of its
coefficients lies beyond the corresponding distinguished degree. -/
private theorem IsDistinguished.norm_coeff_mul_mul_pow_lt (hf : IsDistinguished c i f)
    (hg : IsDistinguished c j g) (hc : 0 < c) {m n : ℕ} (h : i < m ∨ j < n) :
    ‖f.coeff m * g.coeff n‖ * c ^ (m + n) <
      f.gaussNorm norm c * g.gaussNorm norm c :=
  norm_coeff_mul_mul_pow_lt_of_lt hc hf.hasGaussNorm hg.hasGaussNorm hf.gaussNorm_pos
    hg.gaussNorm_pos (h.imp (hf.norm_coeff_mul_pow_lt _) (hg.norm_coeff_mul_pow_lt _))

/-- **The dominant coefficient of a product of distinguished series.** If `f` is distinguished of
degree `i` and `g` of degree `j`, then the coefficient of `f * g` in degree `i + j` realises the
product of the two Gauss norms. -/
theorem IsDistinguished.norm_coeff_mul_mul_pow_eq_gaussNorm_mul (hf : IsDistinguished c i f)
    (hg : IsDistinguished c j g) (hc : 0 < c) :
    ‖(f * g).coeff (i + j)‖ * c ^ (i + j) = f.gaussNorm norm c * g.gaussNorm norm c :=
  norm_coeff_mul_mul_pow_eq_of_lt hc hf.norm_coeff_mul_pow_eq hg.norm_coeff_mul_pow_eq
    fun m n hmn hne ↦ hf.norm_coeff_mul_mul_pow_lt hg hc <| by
      have : m ≠ i ∨ n ≠ j := by simpa only [Ne, Prod.ext_iff, not_and_or] using hne
      omega

/-- The product of series distinguished in degrees `i` and `j` is distinguished in degree
`i + j` at a positive radius. -/
theorem IsDistinguished.mul (hf : IsDistinguished c i f) (hg : IsDistinguished c j g)
    (hc : 0 < c) :
    IsDistinguished c (i + j) (f * g) := by
  have hdom := hf.norm_coeff_mul_mul_pow_eq_gaussNorm_mul hg hc
  have hmul := gaussNorm_mul_eq_of_norm_coeff_mul_pow_eq hc hf.hasGaussNorm hg.hasGaussNorm hdom
  refine ⟨hdom.trans hmul.symm, fun m hm ↦ hmul ▸ norm_coeff_mul_mul_pow_lt_of_forall_lt hc.le
    fun m₁ m₂ hsum ↦ hf.norm_coeff_mul_mul_pow_lt hg hc (by omega)⟩

omit [IsUltrametricDist R] in
/-- A product term is strictly below the product of the Gauss norms when one of its
coefficients lies before the corresponding lowest dominant degree. -/
private theorem IsLowestDominant.norm_coeff_mul_mul_pow_lt (hf : IsLowestDominant c i f)
    (hg : IsLowestDominant c j g) (hc : 0 < c) (hbf : f.HasGaussNorm norm c)
    (hbg : g.HasGaussNorm norm c) {m n : ℕ} (h : m < i ∨ n < j) :
    ‖f.coeff m * g.coeff n‖ * c ^ (m + n) <
      f.gaussNorm norm c * g.gaussNorm norm c :=
  norm_coeff_mul_mul_pow_lt_of_lt hc hbf hbg hf.gaussNorm_pos hg.gaussNorm_pos
    (h.imp (hf.norm_coeff_mul_pow_lt _) (hg.norm_coeff_mul_pow_lt _))

/-- The product of series with lowest dominant degrees `i` and `j` has lowest dominant degree
`i + j` at a positive radius, provided both have bounded weighted coefficient norms. -/
theorem IsLowestDominant.mul (hf : IsLowestDominant c i f) (hg : IsLowestDominant c j g)
    (hc : 0 < c) (hbf : f.HasGaussNorm norm c) (hbg : g.HasGaussNorm norm c) :
    IsLowestDominant c (i + j) (f * g) := by
  have hdom : ‖(f * g).coeff (i + j)‖ * c ^ (i + j) = f.gaussNorm norm c * g.gaussNorm norm c :=
    norm_coeff_mul_mul_pow_eq_of_lt hc hf.norm_coeff_mul_pow_eq hg.norm_coeff_mul_pow_eq
      fun m n hmn hne ↦ hf.norm_coeff_mul_mul_pow_lt hg hc hbf hbg <| by
        have : m ≠ i ∨ n ≠ j := by simpa only [Ne, Prod.ext_iff, not_and_or] using hne
        omega
  have hmul := gaussNorm_mul_eq_of_norm_coeff_mul_pow_eq hc hbf hbg hdom
  refine ⟨hmul ▸ mul_pos hf.gaussNorm_pos hg.gaussNorm_pos, hdom.trans hmul.symm,
    fun m hm ↦ hmul ▸ norm_coeff_mul_mul_pow_lt_of_forall_lt hc.le
      fun m₁ m₂ hsum ↦ hf.norm_coeff_mul_mul_pow_lt hg hc hbf hbg (by omega)⟩

end Multiplication

variable [NormMulClass R]

/-- The Gauss norm is multiplicative on restricted power series at every positive radius. -/
theorem gaussNorm_mul_of_isRestricted (hc : 0 < c) (hf : f.IsRestricted c)
    (hg : g.IsRestricted c) :
    (f * g).gaussNorm norm c = f.gaussNorm norm c * g.gaussNorm norm c := by
  let : Fact (0 < c) := ⟨hc⟩
  -- Mathlib's univariate predicates and norms abbreviate the Unit-indexed multivariate ones.
  simp only [PowerSeries.IsRestricted] at hf hg
  simpa only [PowerSeries.gaussNorm] using
    (MvPowerSeries.IsRestricted.gaussNorm_mul (c := fun _ : Unit ↦ c) hf hg)

/-! ### The Gauss valuation -/

section Valuation

open scoped NNReal

variable [NormOneClass R]

/-- **The Gauss valuation** at a positive radius `c`: the Gauss norm `f ↦ sup ‖aₙ‖ cⁿ`, as a
valuation with values in `ℝ≥0` on the ring of power series restricted at `c`. -/
noncomputable def gaussValuation (hc : 0 < c) :
    Valuation (PowerSeries.IsRestricted.subring (R := R) c) ℝ≥0 where
  toFun f := ⟨(f : PowerSeries R).gaussNorm norm c,
    PowerSeries.gaussNorm_nonneg norm c _ norm_nonneg⟩
  map_zero' := NNReal.eq <| PowerSeries.gaussNorm_zero norm c norm_zero
  map_one' := NNReal.eq <| by
    -- The subring's one coerces to `PowerSeries.one`; `NNReal.eq` exposes the real Gauss norm.
    change (1 : PowerSeries R).gaussNorm norm c = 1
    rw [← map_one (PowerSeries.C : R →+* PowerSeries R)]
    exact (PowerSeries.gaussNorm_C
      (v := (NormMulClass.isAbsoluteValue_norm (α := R)).toAbsoluteValue)
      (hc := hc.le) (r := (1 : R))).trans norm_one
  map_mul' f g := NNReal.eq <| gaussNorm_mul_of_isRestricted hc f.2 g.2
  map_add_le_max' f g :=
    PowerSeries.gaussNorm_add_le_max norm c _ _ hc.le norm_nonneg
      IsUltrametricDist.isNonarchimedean_norm
      (hasGaussNorm_of_isRestricted f.2) (hasGaussNorm_of_isRestricted g.2)

/-- The Gauss valuation is the Gauss norm, read in `ℝ`. -/
@[simp]
theorem coe_gaussValuation (hc : 0 < c) (f : PowerSeries.IsRestricted.subring (R := R) c) :
    (gaussValuation hc f : ℝ) = (f : PowerSeries R).gaussNorm norm c := (rfl)

/-- The Gauss valuation of a constant series is the norm of its coefficient. -/
@[simp]
theorem gaussValuation_C (hc : 0 < c) (a : R) :
    gaussValuation hc
      (⟨PowerSeries.C a, PowerSeries.isRestricted_C c a⟩ :
        PowerSeries.IsRestricted.subring (R := R) c) = ‖a‖₊ := by
  apply NNReal.eq
  rw [coe_gaussValuation]
  exact PowerSeries.gaussNorm_C
    (v := (NormMulClass.isAbsoluteValue_norm (α := R)).toAbsoluteValue)
    (hc := hc.le) (r := a)

/-- The Gauss valuation of the variable is the radius. -/
@[simp]
theorem gaussValuation_X (hc : 0 < c) :
    gaussValuation hc
      (⟨(PowerSeries.X : PowerSeries R), by
          rw [PowerSeries.X_eq]
          exact PowerSeries.isRestricted_monomial c 1 (1 : R)⟩ :
        PowerSeries.IsRestricted.subring (R := R) c) = ⟨c, hc.le⟩ := by
  apply NNReal.eq
  rw [coe_gaussValuation]
  -- The coercion to reals exposes the Gauss norm and the real radius.
  change (PowerSeries.X : PowerSeries R).gaussNorm norm c = c
  rw [PowerSeries.X_eq]
  have h := PowerSeries.gaussNorm_monomial
      (v := (NormMulClass.isAbsoluteValue_norm (α := R)).toAbsoluteValue)
      (hc := hc.le) (n := 1) (r := (1 : R))
  have hv : (⇑(NormMulClass.isAbsoluteValue_norm (α := R)).toAbsoluteValue : R → ℝ) =
      norm := rfl
  rw [hv] at h
  simpa only [norm_one, one_mul, pow_one] using h

/-- The Gauss valuation vanishes only at zero: its support is trivial. -/
@[simp]
theorem gaussValuation_eq_zero_iff (hc : 0 < c)
    {f : PowerSeries.IsRestricted.subring (R := R) c} :
    gaussValuation hc f = 0 ↔ f = 0 := by
  rw [← NNReal.coe_eq_zero, coe_gaussValuation, PowerSeries.gaussNorm_eq_zero_iff norm c _
    norm_zero norm_nonneg (fun _ ↦ norm_eq_zero.mp) hc (hasGaussNorm_of_isRestricted f.2),
    ZeroMemClass.coe_eq_zero]

/-! ### Gauss valuations just above and just below the radius -/

section LexValuation

variable {f g : PowerSeries.IsRestricted.subring (R := R) c}

/-- The value `(|f|_c, d f)` in the lexicographic group `ℝ≥0ˣ ×ₗ ℤ`, and `0` at `f = 0`. Both
Gauss valuations below are of this form, for two choices of the secondary degree `d`. -/
private noncomputable def lexValue (hc : 0 < c)
    (d : PowerSeries.IsRestricted.subring (R := R) c → ℤ)
    (f : PowerSeries.IsRestricted.subring (R := R) c) : WithZero (ℝ≥0ˣ ×ₗ Multiplicative ℤ) :=
  open Classical in
  if hf : f = 0 then 0 else
    (toLex (Units.mk0 (gaussValuation hc f) ((gaussValuation_eq_zero_iff hc).not.mpr hf),
      Multiplicative.ofAdd (d f)) : ℝ≥0ˣ ×ₗ Multiplicative ℤ)

private theorem lexValue_zero (hc : 0 < c)
    (d : PowerSeries.IsRestricted.subring (R := R) c → ℤ) : lexValue hc d 0 = 0 := by
  simp [lexValue]

private theorem lexValue_of_ne_zero (hc : 0 < c)
    (d : PowerSeries.IsRestricted.subring (R := R) c → ℤ) (hf : f ≠ 0) :
    lexValue hc d f =
      (toLex (Units.mk0 (gaussValuation hc f) ((gaussValuation_eq_zero_iff hc).not.mpr hf),
        Multiplicative.ofAdd (d f)) : ℝ≥0ˣ ×ₗ Multiplicative ℤ) := by
  simp [lexValue, hf]

private theorem lexValue_eq_coe (hc : 0 < c)
    (d : PowerSeries.IsRestricted.subring (R := R) c → ℤ) (hf : f ≠ 0) {u : ℝ≥0ˣ}
    (hu : (u : ℝ≥0) = gaussValuation hc f) :
    lexValue hc d f = (toLex (u, Multiplicative.ofAdd (d f)) : ℝ≥0ˣ ×ₗ Multiplicative ℤ) := by
  rw [lexValue_of_ne_zero hc d hf]
  congr
  exact Units.ext hu.symm

private theorem lexValue_le_lexValue_iff (hc : 0 < c)
    (d : PowerSeries.IsRestricted.subring (R := R) c → ℤ) (hf : f ≠ 0) (hg : g ≠ 0) :
    lexValue hc d f ≤ lexValue hc d g ↔ gaussValuation hc f < gaussValuation hc g ∨
      gaussValuation hc f = gaussValuation hc g ∧ d f ≤ d g := by
  rw [lexValue_of_ne_zero hc d hf, lexValue_of_ne_zero hc d hg, WithZero.coe_le_coe,
    Prod.Lex.toLex_le_toLex]
  simp [← Units.val_lt_val, Units.ext_iff]

private theorem lexValue_lt_coe (hc : 0 < c)
    (d : PowerSeries.IsRestricted.subring (R := R) c → ℤ) {u : ℝ≥0ˣ}
    (h : gaussValuation hc f < u) (n : Multiplicative ℤ) :
    lexValue hc d f < (toLex (u, n) : ℝ≥0ˣ ×ₗ Multiplicative ℤ) := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [lexValue_zero]
    exact WithZero.zero_lt_coe _
  rw [lexValue_of_ne_zero hc d hf, WithZero.coe_lt_coe, Prod.Lex.toLex_lt_toLex]
  exact Or.inl (Units.val_lt_val.mp h)

/-- The valuation `f ↦ (|f|_c, d f)` with values in `ℝ≥0ˣ ×ₗ ℤ`, for a secondary degree `d`
which is additive on nonzero products and satisfies the ultrametric comparison `hd_add` among
series of equal Gauss norm. -/
private noncomputable def lexValuation (hc : 0 < c)
    (d : PowerSeries.IsRestricted.subring (R := R) c → ℤ) (hd_one : d 1 = 0)
    (hd_mul : ∀ f g, f ≠ 0 → g ≠ 0 → d (f * g) = d f + d g)
    (hd_add : ∀ f g, f ≠ 0 → g ≠ 0 → f + g ≠ 0 →
      gaussValuation hc (f + g) = gaussValuation hc f →
      gaussValuation hc g ≤ gaussValuation hc f →
      (gaussValuation hc g = gaussValuation hc f → d g ≤ d f) → d (f + g) ≤ d f) :
    Valuation (PowerSeries.IsRestricted.subring (R := R) c)
      (WithZero (ℝ≥0ˣ ×ₗ Multiplicative ℤ)) where
  toFun := lexValue hc d
  map_zero' := lexValue_zero hc d
  map_one' := by
    have := NormOneClass.nontrivial (G := R)
    rw [lexValue_eq_coe hc d one_ne_zero (u := 1) (by rw [map_one, Units.val_one]), hd_one]
    rfl
  map_mul' f g := by
    rcases eq_or_ne f 0 with rfl | hf
    · simp [lexValue_zero]
    rcases eq_or_ne g 0 with rfl | hg
    · simp [lexValue_zero]
    have hf' := (gaussValuation_eq_zero_iff hc).not.mpr hf
    have hg' := (gaussValuation_eq_zero_iff hc).not.mpr hg
    have hfg : f * g ≠ 0 := by
      rw [Ne, ← gaussValuation_eq_zero_iff hc, map_mul]
      exact mul_ne_zero hf' hg'
    rw [lexValue_eq_coe hc d hfg (u := Units.mk0 _ hf' * Units.mk0 _ hg') (by simp),
      lexValue_of_ne_zero hc d hf, lexValue_of_ne_zero hc d hg, ← WithZero.coe_mul, ← toLex_mul,
      hd_mul f g hf hg]
    rfl
  map_add_le_max' f g := by
    wlog hgf : lexValue hc d g ≤ lexValue hc d f generalizing f g
    · rw [add_comm, max_comm]
      exact this g f (le_of_not_ge hgf)
    rw [max_eq_left hgf]
    rcases eq_or_ne (f + g) 0 with hfg | hfg
    · rw [hfg, lexValue_zero]
      exact zero_le
    rcases eq_or_ne g 0 with rfl | hg
    · rw [add_zero]
    rcases eq_or_ne f 0 with rfl | hf
    · rw [lexValue_zero] at hgf
      refine absurd (le_zero_iff.mp hgf) ?_
      rw [lexValue_of_ne_zero hc d hg]
      exact WithZero.coe_ne_zero
    have hgf' := (lexValue_le_lexValue_iff hc d hg hf).mp hgf
    have hle : gaussValuation hc g ≤ gaussValuation hc f := hgf'.elim le_of_lt fun h ↦ h.1.le
    rw [lexValue_le_lexValue_iff hc d hfg hf]
    rcases (((gaussValuation hc).map_add f g).trans (max_le le_rfl hle)).lt_or_eq with hlt | heq
    · exact Or.inl hlt
    · exact Or.inr ⟨heq, hd_add f g hf hg hfg heq hle fun h ↦
        (hgf'.resolve_left (by rw [h]; exact lt_irrefl _)).2⟩

/-- The weighted coefficients of a sum of two restricted series are bounded, in every degree past
the distinguished degree `s` of the first, by its Gauss norm, when the second has smaller Gauss
norm or equal Gauss norm and distinguished degree at most `s`. -/
private theorem norm_coeff_add_mul_pow_lt_of_isDistinguished (hc : 0 < c)
    {s t : ℕ} (hs : IsDistinguished c s (f : PowerSeries R))
    (ht : IsDistinguished c t (g : PowerSeries R))
    (hle : gaussValuation hc g ≤ gaussValuation hc f)
    (hdeg : gaussValuation hc g = gaussValuation hc f → t ≤ s) {m : ℕ} (hm : s < m) :
    ‖((f : PowerSeries R) + g).coeff m‖ * c ^ m < (f : PowerSeries R).gaussNorm norm c := by
  refine (norm_coeff_add_mul_pow_le_max _ _ hc.le m).trans_lt
    (max_lt (hs.norm_coeff_mul_pow_lt m hm) ?_)
  rcases hle.lt_or_eq with hlt | heq
  · exact (PowerSeries.le_gaussNorm norm c _ ht.hasGaussNorm m).trans_lt hlt
  · rw [← coe_gaussValuation hc, ← heq, coe_gaussValuation]
    exact ht.norm_coeff_mul_pow_lt m ((hdeg heq).trans_lt hm)

/-- The lowest-dominant-degree analogue of `norm_coeff_add_mul_pow_lt_of_isDistinguished`: below
the lowest dominant degree `s` of the first series. -/
private theorem norm_coeff_add_mul_pow_lt_of_isLowestDominant (hc : 0 < c)
    {s t : ℕ} (hs : IsLowestDominant c s (f : PowerSeries R))
    (ht : IsLowestDominant c t (g : PowerSeries R))
    (hle : gaussValuation hc g ≤ gaussValuation hc f)
    (hdeg : gaussValuation hc g = gaussValuation hc f → s ≤ t) {m : ℕ} (hm : m < s) :
    ‖((f : PowerSeries R) + g).coeff m‖ * c ^ m < (f : PowerSeries R).gaussNorm norm c := by
  refine (norm_coeff_add_mul_pow_le_max _ _ hc.le m).trans_lt
    (max_lt (hs.norm_coeff_mul_pow_lt m hm) ?_)
  rcases hle.lt_or_eq with hlt | heq
  · exact (PowerSeries.le_gaussNorm norm c _ (hasGaussNorm_of_isRestricted g.2) m).trans_lt hlt
  · rw [← coe_gaussValuation hc, ← heq, coe_gaussValuation]
    exact ht.norm_coeff_mul_pow_lt m (hm.trans_le (hdeg heq))

/-- The distinguished degree of a nonzero restricted series, and `0` at zero. -/
private noncomputable def distinguishedDegree (hc : 0 < c)
    (f : PowerSeries.IsRestricted.subring (R := R) c) : ℕ :=
  open Classical in
  if hf : f = 0 then 0 else (exists_isDistinguished hc f.2 (by simpa using hf)).choose

omit [NormMulClass R] [NormOneClass R] in
private theorem isDistinguished_distinguishedDegree (hc : 0 < c) (hf : f ≠ 0) :
    IsDistinguished c (distinguishedDegree hc f) (f : PowerSeries R) := by
  simp only [distinguishedDegree, hf, ↓reduceDIte]
  exact (exists_isDistinguished hc f.2 (by simpa using hf)).choose_spec

omit [NormMulClass R] [NormOneClass R] in
private theorem distinguishedDegree_eq (hc : 0 < c) {s : ℕ}
    (hs : IsDistinguished c s (f : PowerSeries R)) : distinguishedDegree hc f = s :=
  (isDistinguished_distinguishedDegree hc
    (fun h ↦ hs.ne_zero (by rw [h, ZeroMemClass.coe_zero]))).unique hs

/-- The lowest dominant degree of a nonzero restricted series, and `0` at zero. -/
private noncomputable def lowestDominantDegree (hc : 0 < c)
    (f : PowerSeries.IsRestricted.subring (R := R) c) : ℕ :=
  open Classical in
  if hf : f = 0 then 0 else (exists_isLowestDominant hc f.2 (by simpa using hf)).choose

omit [NormMulClass R] [NormOneClass R] in
private theorem isLowestDominant_lowestDominantDegree (hc : 0 < c) (hf : f ≠ 0) :
    IsLowestDominant c (lowestDominantDegree hc f) (f : PowerSeries R) := by
  simp only [lowestDominantDegree, hf, ↓reduceDIte]
  exact (exists_isLowestDominant hc f.2 (by simpa using hf)).choose_spec

omit [NormMulClass R] [NormOneClass R] in
private theorem lowestDominantDegree_eq (hc : 0 < c) {s : ℕ}
    (hs : IsLowestDominant c s (f : PowerSeries R)) : lowestDominantDegree hc f = s :=
  (isLowestDominant_lowestDominantDegree hc
    (fun h ↦ hs.ne_zero (by rw [h, ZeroMemClass.coe_zero]))).unique hs

omit [NormMulClass R] [NormOneClass R] in
private theorem coe_one_eq_monomial :
    ((1 : PowerSeries.IsRestricted.subring (R := R) c) : PowerSeries R) =
      PowerSeries.monomial 0 1 := by
  rw [OneMemClass.coe_one, PowerSeries.monomial_zero_eq_C, map_one]

omit [NormMulClass R] in
private theorem distinguishedDegree_one (hc : 0 < c) :
    distinguishedDegree hc (1 : PowerSeries.IsRestricted.subring (R := R) c) = 0 := by
  have := NormOneClass.nontrivial (G := R)
  have h := isDistinguished_monomial (R := R) hc one_ne_zero 0
  rw [← coe_one_eq_monomial (c := c)] at h
  exact distinguishedDegree_eq hc h

omit [NormOneClass R] in
private theorem distinguishedDegree_mul (hc : 0 < c) (hf : f ≠ 0) (hg : g ≠ 0) :
    distinguishedDegree hc (f * g) = distinguishedDegree hc f + distinguishedDegree hc g := by
  have h := (isDistinguished_distinguishedDegree hc hf).mul
    (isDistinguished_distinguishedDegree hc hg) hc
  rw [← MulMemClass.coe_mul] at h
  exact distinguishedDegree_eq hc h

/-- The distinguished degree of a sum of Gauss norm equal to that of the first summand is at
most that of the first summand, once the second is no larger in the lexicographic order. -/
private theorem distinguishedDegree_add_le (hc : 0 < c) (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : f + g ≠ 0) (heq : gaussValuation hc (f + g) = gaussValuation hc f)
    (hle : gaussValuation hc g ≤ gaussValuation hc f)
    (hdeg : gaussValuation hc g = gaussValuation hc f →
      distinguishedDegree hc g ≤ distinguishedDegree hc f) :
    distinguishedDegree hc (f + g) ≤ distinguishedDegree hc f :=
  (isDistinguished_distinguishedDegree hc hfg).le_of_forall_lt fun m hm ↦ by
    rw [← coe_gaussValuation hc, heq, coe_gaussValuation, AddMemClass.coe_add]
    exact norm_coeff_add_mul_pow_lt_of_isDistinguished hc
      (isDistinguished_distinguishedDegree hc hf) (isDistinguished_distinguishedDegree hc hg)
      hle hdeg hm

omit [NormMulClass R] in
private theorem lowestDominantDegree_one (hc : 0 < c) :
    lowestDominantDegree hc (1 : PowerSeries.IsRestricted.subring (R := R) c) = 0 := by
  have := NormOneClass.nontrivial (G := R)
  have h := isLowestDominant_monomial (R := R) hc one_ne_zero 0
  rw [← coe_one_eq_monomial (c := c)] at h
  exact lowestDominantDegree_eq hc h

omit [NormOneClass R] in
private theorem lowestDominantDegree_mul (hc : 0 < c) (hf : f ≠ 0) (hg : g ≠ 0) :
    lowestDominantDegree hc (f * g) = lowestDominantDegree hc f + lowestDominantDegree hc g := by
  have h := (isLowestDominant_lowestDominantDegree hc hf).mul
    (isLowestDominant_lowestDominantDegree hc hg) hc (hasGaussNorm_of_isRestricted f.2)
    (hasGaussNorm_of_isRestricted g.2)
  rw [← MulMemClass.coe_mul] at h
  exact lowestDominantDegree_eq hc h

/-- The lowest dominant degree of a sum of Gauss norm equal to that of the first summand is at
least that of the first summand, once the second is no larger in the order reversing lowest
dominant degrees. -/
private theorem lowestDominantDegree_le_add (hc : 0 < c) (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : f + g ≠ 0) (heq : gaussValuation hc (f + g) = gaussValuation hc f)
    (hle : gaussValuation hc g ≤ gaussValuation hc f)
    (hdeg : gaussValuation hc g = gaussValuation hc f →
      lowestDominantDegree hc f ≤ lowestDominantDegree hc g) :
    lowestDominantDegree hc f ≤ lowestDominantDegree hc (f + g) :=
  (isLowestDominant_lowestDominantDegree hc hfg).le_of_forall_lt fun m hm ↦ by
    rw [← coe_gaussValuation hc, heq, coe_gaussValuation, AddMemClass.coe_add]
    exact norm_coeff_add_mul_pow_lt_of_isLowestDominant hc
      (isLowestDominant_lowestDominantDegree hc hf) (isLowestDominant_lowestDominantDegree hc hg)
      hle hdeg hm

/-- **The Gauss valuation just above the radius `c`**: the valuation
`f ↦ (|f|_c, s)` on the ring of series restricted at `c`, with values in the lexicographically
ordered group `ℝ≥0ˣ ×ₗ ℤ` (written multiplicatively), where `s` is the distinguished degree of
`f`, the last degree in which its Gauss norm is attained.

It is the Gauss norm at a radius `c · γ` for an infinitesimal `γ > 1`: the weighted coefficient
`‖aₙ‖ (cγ)ⁿ` is largest in the last degree attaining `|f|_c`. It refines `gaussValuation`, which
it recovers by forgetting the second coordinate. -/
noncomputable def gaussValuationAbove (hc : 0 < c) :
    Valuation (PowerSeries.IsRestricted.subring (R := R) c)
      (WithZero (ℝ≥0ˣ ×ₗ Multiplicative ℤ)) :=
  lexValuation hc (fun f ↦ distinguishedDegree hc f)
    (by rw [distinguishedDegree_one, Nat.cast_zero])
    (fun f g hf hg ↦ by rw [distinguishedDegree_mul hc hf hg, Nat.cast_add])
    (fun f g hf hg hfg heq hle hdeg ↦ Nat.cast_le.mpr <|
      distinguishedDegree_add_le hc hf hg hfg heq hle fun h ↦ Nat.cast_le.mp (hdeg h))

/-- **The Gauss valuation just below the radius `c`**: the valuation
`f ↦ (|f|_c, -s)` on the ring of series restricted at `c`, with values in the lexicographically
ordered group `ℝ≥0ˣ ×ₗ ℤ` (written multiplicatively), where `s` is the lowest dominant degree of
`f`, the first degree in which its Gauss norm is attained.

It is the Gauss norm at a radius `c · γ` for an infinitesimal `γ < 1`: the weighted coefficient
`‖aₙ‖ (cγ)ⁿ` is largest in the first degree attaining `|f|_c`. It refines `gaussValuation`, which
it recovers by forgetting the second coordinate. -/
noncomputable def gaussValuationBelow (hc : 0 < c) :
    Valuation (PowerSeries.IsRestricted.subring (R := R) c)
      (WithZero (ℝ≥0ˣ ×ₗ Multiplicative ℤ)) :=
  lexValuation hc (fun f ↦ -(lowestDominantDegree hc f : ℤ))
    (by rw [lowestDominantDegree_one, Nat.cast_zero, neg_zero])
    (fun f g hf hg ↦ by rw [lowestDominantDegree_mul hc hf hg, Nat.cast_add, neg_add])
    (fun f g hf hg hfg heq hle hdeg ↦ neg_le_neg <| Nat.cast_le.mpr <|
      lowestDominantDegree_le_add hc hf hg hfg heq hle fun h ↦
        Nat.cast_le.mp (neg_le_neg_iff.mp (hdeg h)))

private theorem gaussValuationAbove_eq_lexValue (hc : 0 < c) :
    gaussValuationAbove hc f = lexValue hc (fun f ↦ (distinguishedDegree hc f : ℤ)) f :=
  (rfl)

private theorem gaussValuationBelow_eq_lexValue (hc : 0 < c) :
    gaussValuationBelow hc f = lexValue hc (fun f ↦ -(lowestDominantDegree hc f : ℤ)) f :=
  (rfl)

/-- The Gauss valuation just above `c` of a series distinguished of degree `s` is
`(|f|_c, s)`. -/
theorem gaussValuationAbove_eq_coe (hc : 0 < c) {s : ℕ}
    (hs : IsDistinguished c s (f : PowerSeries R)) {u : ℝ≥0ˣ}
    (hu : (u : ℝ≥0) = gaussValuation hc f) :
    gaussValuationAbove hc f =
      (toLex (u, Multiplicative.ofAdd (s : ℤ)) : ℝ≥0ˣ ×ₗ Multiplicative ℤ) := by
  rw [gaussValuationAbove_eq_lexValue, ← distinguishedDegree_eq hc hs]
  exact lexValue_eq_coe hc _ (fun h ↦ hs.ne_zero (by rw [h, ZeroMemClass.coe_zero])) hu

/-- The Gauss valuation just below `c` of a series with lowest dominant degree `s` is
`(|f|_c, -s)`. -/
theorem gaussValuationBelow_eq_coe (hc : 0 < c) {s : ℕ}
    (hs : IsLowestDominant c s (f : PowerSeries R)) {u : ℝ≥0ˣ}
    (hu : (u : ℝ≥0) = gaussValuation hc f) :
    gaussValuationBelow hc f =
      (toLex (u, Multiplicative.ofAdd (-(s : ℤ))) : ℝ≥0ˣ ×ₗ Multiplicative ℤ) := by
  rw [gaussValuationBelow_eq_lexValue, ← lowestDominantDegree_eq hc hs]
  exact lexValue_eq_coe hc _ (fun h ↦ hs.ne_zero (by rw [h, ZeroMemClass.coe_zero])) hu

/-- The Gauss valuation just above `c` vanishes only at zero. -/
@[simp]
theorem gaussValuationAbove_eq_zero_iff (hc : 0 < c) : gaussValuationAbove hc f = 0 ↔ f = 0 :=
  ⟨fun h ↦ by_contra fun hf ↦ by
    rw [gaussValuationAbove_eq_lexValue, lexValue_of_ne_zero hc _ hf] at h
    exact WithZero.coe_ne_zero h, fun h ↦ h ▸ map_zero _⟩

/-- The Gauss valuation just below `c` vanishes only at zero. -/
@[simp]
theorem gaussValuationBelow_eq_zero_iff (hc : 0 < c) : gaussValuationBelow hc f = 0 ↔ f = 0 :=
  ⟨fun h ↦ by_contra fun hf ↦ by
    rw [gaussValuationBelow_eq_lexValue, lexValue_of_ne_zero hc _ hf] at h
    exact WithZero.coe_ne_zero h, fun h ↦ h ▸ map_zero _⟩

/-- **Comparison just above `c`.** For series distinguished of degrees `s` and `t`, the Gauss
valuation just above `c` compares Gauss norms first and then distinguished degrees. -/
theorem gaussValuationAbove_le_iff (hc : 0 < c) {s t : ℕ}
    (hs : IsDistinguished c s (f : PowerSeries R)) (ht : IsDistinguished c t (g : PowerSeries R)) :
    gaussValuationAbove hc f ≤ gaussValuationAbove hc g ↔
      gaussValuation hc f < gaussValuation hc g ∨
        gaussValuation hc f = gaussValuation hc g ∧ s ≤ t := by
  have hf : f ≠ 0 := fun h ↦ hs.ne_zero (by rw [h, ZeroMemClass.coe_zero])
  have hg : g ≠ 0 := fun h ↦ ht.ne_zero (by rw [h, ZeroMemClass.coe_zero])
  have := lexValue_le_lexValue_iff hc (fun f ↦ (distinguishedDegree hc f : ℤ)) hf hg
  rw [distinguishedDegree_eq hc hs, distinguishedDegree_eq hc ht, Nat.cast_le] at this
  rwa [gaussValuationAbove_eq_lexValue, gaussValuationAbove_eq_lexValue]

/-- **Comparison just below `c`.** For series with lowest dominant degrees `s` and `t`, the Gauss
valuation just below `c` compares Gauss norms first and then lowest dominant degrees, in the
reverse order. -/
theorem gaussValuationBelow_le_iff (hc : 0 < c) {s t : ℕ}
    (hs : IsLowestDominant c s (f : PowerSeries R))
    (ht : IsLowestDominant c t (g : PowerSeries R)) :
    gaussValuationBelow hc f ≤ gaussValuationBelow hc g ↔
      gaussValuation hc f < gaussValuation hc g ∨
        gaussValuation hc f = gaussValuation hc g ∧ t ≤ s := by
  have hf : f ≠ 0 := fun h ↦ hs.ne_zero (by rw [h, ZeroMemClass.coe_zero])
  have hg : g ≠ 0 := fun h ↦ ht.ne_zero (by rw [h, ZeroMemClass.coe_zero])
  have := lexValue_le_lexValue_iff hc (fun f ↦ -(lowestDominantDegree hc f : ℤ)) hf hg
  rw [lowestDominantDegree_eq hc hs, lowestDominantDegree_eq hc ht, neg_le_neg_iff,
    Nat.cast_le] at this
  rwa [gaussValuationBelow_eq_lexValue, gaussValuationBelow_eq_lexValue]

/-- The Gauss valuation just above `c` is strictly monotone in the Gauss norm: a strictly smaller
Gauss norm gives a strictly smaller value, whatever the distinguished degrees. -/
theorem gaussValuationAbove_lt_of_lt (hc : 0 < c)
    (h : gaussValuation hc f < gaussValuation hc g) :
    gaussValuationAbove hc f < gaussValuationAbove hc g := by
  have hg : gaussValuation hc g ≠ 0 := (pos_of_gt h).ne'
  obtain ⟨t, ht⟩ := exists_isDistinguished hc g.2
    (by simpa using (gaussValuation_eq_zero_iff hc).not.mp hg)
  rw [gaussValuationAbove_eq_coe hc ht (u := Units.mk0 _ hg) rfl, gaussValuationAbove_eq_lexValue]
  exact lexValue_lt_coe hc _ h _

/-- The Gauss valuation just below `c` is strictly monotone in the Gauss norm: a strictly smaller
Gauss norm gives a strictly smaller value, whatever the lowest dominant degrees. -/
theorem gaussValuationBelow_lt_of_lt (hc : 0 < c)
    (h : gaussValuation hc f < gaussValuation hc g) :
    gaussValuationBelow hc f < gaussValuationBelow hc g := by
  have hg : gaussValuation hc g ≠ 0 := (pos_of_gt h).ne'
  obtain ⟨t, ht⟩ := exists_isLowestDominant hc g.2
    (by simpa using (gaussValuation_eq_zero_iff hc).not.mp hg)
  rw [gaussValuationBelow_eq_coe hc ht (u := Units.mk0 _ hg) rfl, gaussValuationBelow_eq_lexValue]
  exact lexValue_lt_coe hc _ h _

end LexValuation

end Valuation

end TauCeti.PowerSeries
