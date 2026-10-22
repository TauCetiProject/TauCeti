/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.RingTheory.PowerSeries.GaussNorm
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Basic
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.Prod
public import TauCeti.RingTheory.PowerSeries.Restricted
import Mathlib.Algebra.Order.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.RingTheory.Polynomial.GaussNorm

/-!
# The Gauss norm of restricted power series

A restricted power series has finite Gauss norm. At a positive radius, a nonzero restricted
series has a last coefficient attaining that norm; the degree of that coefficient is the
*distinguished degree* of the series, and `IsDistinguished` names the property. Over a
nonarchimedean ring, a pair of distinguished degrees produces a dominant coefficient in a product
as soon as the two distinguished coefficients multiply without loss of norm; this is automatic
when the norm is multiplicative, and the Gauss norm is then multiplicative on restricted series.

The distinguished degree is the datum Weierstrass division and preparation for Tate algebras are
organised around. Distinguishedness and its product law need only a seminormed coefficient ring;
nonzero restricted series attain a distinguished degree over a normed ring. No completeness
hypothesis is needed for these norm identities. The radius is any positive real number, including
the unit radius of the usual Tate algebra.

Over a complete seminormed ring, summable Gauss norms ensure summability in every coefficient.
Over any normed ring, the coefficientwise `tsum`s of such a family of restricted series form a
restricted series. For complete coefficients this is the convergence statement behind
successive-approximation arguments, taking the place of completeness of the restricted-series
space for the Gauss norm. Over a complete ultrametric ring, it suffices for the Gauss norms
to tend to zero along the cofinite filter, without absolute summability of those real norms.
The coefficient families are then summable by `summable_coeff_of_tendsto_gaussNorm_zero`.

Multiplicativity and the ultrametric inequality together make the Gauss norm a valuation with
values in `ℝ≥0` on the ring of restricted series, `gaussValuation`, whose support is trivial.
Pulled back to the Tate algebra at radii at most one, these valuations give the Gauss points of the
closed unit disc.

At a positive radius, the Gauss norm of a nonzero restricted series is attained in a finite nonempty
set of degrees. Its largest element is the distinguished degree, and its smallest is the *lowest
dominant degree* (`IsLowestDominant`); both are additive on products. Recording one of them next to
the Gauss norm refines `gaussValuation` to a valuation with values in the lexicographically ordered
group `ℝ≥0ˣ ×ₗ ℤ`: `gaussValuationAbove` records the distinguished degree and `gaussValuationBelow`
the negated lowest dominant degree. They are the Gauss norms at a radius infinitesimally above and
infinitesimally below `c`, and pulled back to the Tate algebra they give refined points of the
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
* `PowerSeries.HasGaussNorm.isRestricted_of_abs_lt`: bounded weighted coefficients at `c'` give
  restrictedness at every `c` with `|c| < c'`.
* `TauCeti.PowerSeries.gaussNorm_eq_of_forall_le`: the Gauss norm is attained at a degree whose
  weighted coefficient dominates.
* `TauCeti.PowerSeries.gaussNorm_le_gaussNorm_of_le` and
  `TauCeti.PowerSeries.tendsto_gaussNorm_of_isRestricted`: the Gauss norm is monotone and, for a
  restricted series, right continuous in the radius.
* `TauCeti.PowerSeries.exists_isDistinguished`: at a positive radius, every nonzero restricted
  series is distinguished of some degree.
* `TauCeti.PowerSeries.IsDistinguished.unique`: of no more than one degree.
* `TauCeti.PowerSeries.isDistinguished_of_norm_coeff_sub_lt`: over an ultrametric ring, a series
  is distinguished once its coefficient in degree `s` is close to an element of maximal norm.
* `Polynomial.Monic.isDistinguished`: a monic polynomial is distinguished of its degree at every
  radius at which its leading term dominates, such as `1 + ∑ᵢ ‖pᵢ‖`
  (`Polynomial.Monic.isDistinguished_one_add_sum_norm_coeff`).
* `TauCeti.PowerSeries.IsDistinguished.trunc`,
  `TauCeti.PowerSeries.IsDistinguished.gaussNorm_trunc` and
  `TauCeti.PowerSeries.IsDistinguished.gaussNorm_sub_trunc_lt`: the polynomial part of a
  distinguished series is distinguished of the same degree and the same Gauss norm, and the
  tail it leaves is strictly smaller.
* `TauCeti.PowerSeries.IsDistinguished.norm_coeff_mul_mul_pow_eq_gaussNorm_mul`,
  `TauCeti.PowerSeries.IsDistinguished.norm_coeff_mul_mul_pow_lt`,
  `TauCeti.PowerSeries.IsDistinguished.gaussNorm_mul` and `TauCeti.PowerSeries.IsDistinguished.mul`:
  the dominant coefficient of a product of distinguished series, the strict estimate for the
  other product terms, and the resulting product law, whenever the two distinguished coefficients
  multiply without loss of norm.
* `TauCeti.PowerSeries.exists_isLowestDominant`, `TauCeti.PowerSeries.IsLowestDominant.unique`
  and `TauCeti.PowerSeries.IsLowestDominant.mul`: a nonzero restricted series has exactly one
  lowest dominant degree, and lowest dominant degrees add under multiplication whenever the two
  lowest dominant coefficients multiply without loss of norm.
* `TauCeti.PowerSeries.gaussNorm_mul_of_isRestricted`: multiplicativity of the Gauss norm.
* `TauCeti.PowerSeries.gaussValuationAbove_le_iff` and
  `TauCeti.PowerSeries.gaussValuationBelow_le_iff`: the two refined Gauss valuations compare
  Gauss norms first, and then distinguished degrees, respectively lowest dominant degrees in the
  reverse order.
* `TauCeti.PowerSeries.gaussValuation_eq_zero_iff`: the Gauss valuation vanishes only at zero.
* `TauCeti.PowerSeries.gaussValuationAbove_monomial_coeff_le` and
  `TauCeti.PowerSeries.gaussValuationBelow_monomial_coeff_le`: every monomial of a series is at
  most the series for both refined Gauss valuations.
* `TauCeti.PowerSeries.summable_coeff_of_tendsto_gaussNorm_zero` and
  `TauCeti.PowerSeries.isRestricted_mk_tsum_coeff_of_tendsto_gaussNorm_zero`: over a complete
  ultrametric ring, cofinite decay of the Gauss norms gives summable coefficients, and the
  coefficientwise sum of restricted series is restricted.
* `TauCeti.PowerSeries.summable_norm_coeff_of_summable_gaussNorm`: summable Gauss norms give
  summable coefficient norms in every degree over a seminormed ring, without completeness.
* `TauCeti.PowerSeries.summable_coeff_of_summable_gaussNorm` and
  `TauCeti.PowerSeries.isRestricted_mk_tsum_coeff`: summable Gauss norms give summable coefficients
  over a complete seminormed ring, and the coefficientwise `tsum`s of restricted series are
  restricted over any normed ring.

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

variable {R : Type*} [SeminormedRing R] {c : ℝ} {i j s t : ℕ} {f g : PowerSeries R}

/-- Coefficientwise convergence to zero implies Gauss-norm convergence when the weighted
coefficient norms are bounded by one null sequence, uniformly over the family. -/
theorem tendsto_gaussNorm_zero_of_coeff_bound {α : Type*} {l : Filter α}
    {F : α → PowerSeries R} {b : ℕ → ℝ}
    (hcoeff : ∀ n, Tendsto (fun a ↦ (F a).coeff n) l (𝓝 0))
    (hbound : ∀ a n, ‖(F a).coeff n‖ * c ^ n ≤ b n)
    (hb : Tendsto b atTop (𝓝 0)) :
    Tendsto (fun a ↦ (F a).gaussNorm norm c) l (𝓝 0) := by
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hb.eventually (gt_mem_nhds (half_pos hε)))
  have hlow : ∀ᶠ a in l, ∀ n ∈ Finset.range N,
      ‖(F a).coeff n‖ * c ^ n < ε / 2 := by
    refine (Finset.eventually_all _).mpr fun n _ ↦ ?_
    have hzero : Tendsto (fun a ↦ ‖(F a).coeff n‖ * c ^ n) l (𝓝 0) := by
      simpa using ((hcoeff n).norm.mul_const (c ^ n))
    exact hzero.eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [hlow] with a ha
  rw [Real.dist_eq, sub_zero, abs_of_nonneg
    (PowerSeries.gaussNorm_nonneg norm c (F a) norm_nonneg)]
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  rw [PowerSeries.gaussNorm_eq]
  refine ciSup_le fun n ↦ ?_
  by_cases hn : n < N
  · exact (ha n (Finset.mem_range.mpr hn)).le
  · exact (hbound a n).trans (hN n (by omega)).le

section Ultrametric

variable [IsUltrametricDist R]

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

end Ultrametric

/-- If the weighted coefficient in degree `s` dominates every other one, the Gauss norm is the
value it takes there. -/
theorem gaussNorm_eq_of_forall_le {S : Type*} [Semiring S] {v : S → ℝ} {a : PowerSeries S}
    (h : ∀ m, v (a.coeff m) * c ^ m ≤ v (a.coeff s) * c ^ s) :
    a.gaussNorm v c = v (a.coeff s) * c ^ s :=
  le_antisymm ((PowerSeries.gaussNorm_eq v c a).trans_le (ciSup_le h))
    (PowerSeries.le_gaussNorm v c a ⟨_, Set.forall_mem_range.mpr h⟩ s)

/-- **The Gauss norm is monotone in the radius**: if the weighted coefficients of `a` at radius
`s` are bounded, the Gauss norm at a radius `0 ≤ r ≤ s` is at most the one at `s`. -/
theorem gaussNorm_le_gaussNorm_of_le {S : Type*} [Semiring S] {v : S → ℝ} {a : PowerSeries S}
    (hv : ∀ x, 0 ≤ v x) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (ha : a.HasGaussNorm v s) :
    a.gaussNorm v r ≤ a.gaussNorm v s :=
  (PowerSeries.gaussNorm_eq v r a).trans_le <| ciSup_le fun n ↦
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hrs n) (hv _)).trans
      (PowerSeries.le_gaussNorm v s a ha n)

end SeminormedRing

section NormedRing

variable {R : Type*} [NormedRing R] {c : ℝ} {f : PowerSeries R}

/-- A restricted power series has bounded weighted coefficient norms. -/
theorem hasGaussNorm_of_isRestricted (hf : f.IsRestricted c) :
    f.HasGaussNorm norm c :=
  ((PowerSeries.isRestricted_iff c f).mp hf).bddAbove_range_of_cofinite

/-- **Bounded weighted coefficients give restrictedness at smaller radii.** If the weighted
coefficient norms `‖aₙ‖ c'ⁿ` are bounded, then `‖aₙ‖ cⁿ → 0` for every `c` with `|c| < c'`, being
dominated by a multiple of `(|c| / c')ⁿ`. -/
theorem _root_.PowerSeries.HasGaussNorm.isRestricted_of_abs_lt {c' : ℝ}
    (hf : f.HasGaussNorm norm c') (h : |c| < c') : f.IsRestricted c := by
  have hc' : 0 < c' := (abs_nonneg c).trans_lt h
  obtain ⟨B, hB⟩ := hf
  rw [← PowerSeries.isRestricted_abs_iff, PowerSeries.isRestricted_iff']
  refine squeeze_zero (fun n ↦ by positivity)
    (TauCeti.mul_abs_pow_le_of_forall_mul_pow_le hc' fun n ↦ hB ⟨n, rfl⟩) ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
    ((div_lt_one hc').mpr h)).const_mul B

/-- **The Gauss norm is right continuous in the radius**: for a series restricted at radius `s`,
if radii `rₙ ∈ [ρ, s]` tend to `ρ > 0`, the Gauss norms at `rₙ` tend to the Gauss norm at `ρ`.
The weighted coefficients of high degree are uniformly small on `[ρ, s]`, and the finitely many of
low degree grow by at most the factor `(rₙ / ρ) ^ N`. -/
theorem tendsto_gaussNorm_of_isRestricted {s ρ : ℝ} {r : ℕ → ℝ} (hρ : 0 < ρ)
    (hρr : ∀ n, ρ ≤ r n) (hrs : ∀ n, r n ≤ s) (hr : Tendsto r atTop (𝓝 ρ))
    (hf : f.IsRestricted s) :
    Tendsto (fun n ↦ f.gaussNorm norm (r n)) atTop (𝓝 (f.gaussNorm norm ρ)) := by
  have hbdd {t : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) : f.HasGaussNorm norm t :=
    hasGaussNorm_of_isRestricted (isRestricted_of_abs_le hf (abs_le_abs_of_nonneg ht hts))
  refine tendsto_order.mpr ⟨fun b hb ↦ Eventually.of_forall fun n ↦ hb.trans_le
    (gaussNorm_le_gaussNorm_of_le (fun _ ↦ norm_nonneg _) hρ.le (hρr n)
      (hbdd (hρ.le.trans (hρr n)) (hrs n))), fun b hb ↦ ?_⟩
  have hG : 0 ≤ f.gaussNorm norm ρ := PowerSeries.gaussNorm_nonneg _ _ _ fun _ ↦ norm_nonneg _
  -- beyond some degree `N`, the weighted coefficients at radius `s` are below `ε`
  have hε : 0 < (b - f.gaussNorm norm ρ) / 2 := half_pos (sub_pos.mpr hb)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (((PowerSeries.isRestricted_iff' s f).mp hf).eventually (gt_mem_nhds hε))
  -- below degree `N`, the weighted coefficients at radius `rₙ` are at most `|f|_ρ (rₙ / ρ) ^ N`
  have hlim : Tendsto (fun n ↦ f.gaussNorm norm ρ * (r n / ρ) ^ N) atTop
      (𝓝 (f.gaussNorm norm ρ)) := by
    simpa [div_self hρ.ne'] using ((hr.div_const ρ).pow N).const_mul (f.gaussNorm norm ρ)
  filter_upwards [hlim.eventually (gt_mem_nhds hb)] with n hn
  refine lt_of_le_of_lt (b := max ((b - f.gaussNorm norm ρ) / 2)
    (f.gaussNorm norm ρ * (r n / ρ) ^ N)) ?_ (max_lt (by linarith) hn)
  rw [PowerSeries.gaussNorm_eq]
  refine ciSup_le fun k ↦ ?_
  rcases le_or_gt N k with hk | hk
  · exact le_max_of_le_left ((mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (hρ.le.trans (hρr n)) (hrs n) k) (norm_nonneg _)).trans (hN k hk).le)
  · refine le_max_of_le_right ?_
    calc ‖f.coeff k‖ * r n ^ k = ‖f.coeff k‖ * ρ ^ k * (r n / ρ) ^ k := by
          rw [div_pow]
          field_simp
      _ ≤ f.gaussNorm norm ρ * (r n / ρ) ^ N :=
          mul_le_mul (PowerSeries.le_gaussNorm _ _ _ (hbdd hρ.le ((hρr 0).trans (hrs 0))) k)
            (pow_le_pow_right₀ ((one_le_div hρ).mpr (hρr n)) hk.le)
            (pow_nonneg (div_nonneg (hρ.le.trans (hρr n)) hρ.le) k) hG

end NormedRing

section Distinguished

section SeminormedRing

variable {R : Type*} [SeminormedRing R] {c : ℝ} {s t : ℕ} {f : PowerSeries R}

variable (c) (s) (f) in
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

end SeminormedRing

section NormedRing

variable {R : Type*} [NormedRing R] {c : ℝ} {f : PowerSeries R}

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

end NormedRing

end Distinguished

/-! ### The lowest dominant degree -/

section LowestDominant

section SeminormedRing

variable {R : Type*} [SeminormedRing R] {c : ℝ} {s t : ℕ} {f : PowerSeries R}

variable (c) (s) (f) in
/-- `s` is the **lowest dominant degree** of `f` at the radius `c` when the Gauss norm of `f` at
`c` is positive and attained in degree `s`, and every earlier weighted coefficient norm is
strictly smaller.

This is the mirror image of `TauCeti.PowerSeries.IsDistinguished`, which singles out the *last*
degree attaining the Gauss norm. The two degrees agree exactly when the Gauss norm is attained
in a single degree. At a positive radius a nonzero restricted series has exactly one lowest
dominant degree (`TauCeti.PowerSeries.exists_isLowestDominant` and
`TauCeti.PowerSeries.IsLowestDominant.unique`), and over an ultrametric norm the lowest dominant
degree of a product is the sum of those of the factors whenever the two lowest dominant
coefficients multiply without loss of norm (`TauCeti.PowerSeries.IsLowestDominant.mul`). -/
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

end SeminormedRing

section NormedRing

variable {R : Type*} [NormedRing R] {c : ℝ} {f : PowerSeries R}

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

end NormedRing

end LowestDominant

section SeminormedRing

variable {R : Type*} [SeminormedRing R] {c : ℝ} {s : ℕ} {f : PowerSeries R}

/-- A monic polynomial of degree `s` whose lower weighted coefficients are at most `c ^ s` is
distinguished of degree `s` at the radius `c > 0`: its Gauss norm `c ^ s` is attained by the
leading coefficient, and every later coefficient vanishes. -/
theorem isDistinguished_of_isMonicOfDegree [NormOneClass R] (hc : 0 < c) {p : Polynomial R}
    (hp : p.IsMonicOfDegree s) (hle : ∀ k < s, ‖p.coeff k‖ * c ^ k ≤ c ^ s) :
    IsDistinguished c s (p : PowerSeries R) := by
  have hs : p.coeff s = 1 := by
    rw [← hp.natDegree_eq]
    exact hp.monic.coeff_natDegree
  have hzero (m : ℕ) (hm : s < m) : p.coeff m = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (hp.natDegree_eq ▸ hm)
  have hnorm : (p : PowerSeries R).gaussNorm norm c = c ^ s := by
    rw [gaussNorm_eq_of_forall_le (s := s)]
    · simp [hs]
    · intro m
      simp only [Polynomial.coeff_coe, hs, norm_one, one_mul]
      rcases lt_trichotomy m s with hm | rfl | hm
      · exact hle m hm
      · simp [hs]
      · simp [hzero m hm, (pow_pos hc s).le]
  refine ⟨by simp [hnorm, hs], fun m hm ↦ ?_⟩
  simp [hnorm, hzero m hm, pow_pos hc s]

/-- A linear polynomial `X - b` whose root lies in the closed disc of radius `c > 0` is
distinguished of degree `1` at `c`: its Gauss norm `max ‖b‖ c` is `c`, attained by the leading
coefficient. -/
theorem isDistinguished_X_sub_C [NormOneClass R] (hc : 0 < c) {b : R} (hb : ‖b‖ ≤ c) :
    IsDistinguished c 1 (PowerSeries.X - PowerSeries.C b) := by
  have : Nontrivial R := NormOneClass.nontrivial
  have h := isDistinguished_of_isMonicOfDegree hc (Polynomial.isMonicOfDegree_X_sub_one b)
    fun k hk ↦ by obtain rfl : k = 0 := by omega
                  simpa using hb
  rwa [← Polynomial.coeToPowerSeries.ringHom_apply, map_sub,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_X, Polynomial.coe_C] at h

/-- A linear polynomial `X - b` whose root lies in the open disc of radius `c > 0` has lowest
dominant degree `1` at `c`: its Gauss norm `c` is attained by the leading coefficient and not by
the constant term `-b`. -/
theorem isLowestDominant_X_sub_C [NormOneClass R] (hc : 0 < c) {b : R} (hb : ‖b‖ < c) :
    IsLowestDominant c 1 (PowerSeries.X - PowerSeries.C b) := by
  have hf := isDistinguished_X_sub_C hc hb.le
  have hnorm : (PowerSeries.X - PowerSeries.C b).gaussNorm norm c = c := by
    simpa using hf.norm_coeff_mul_pow_eq.symm
  refine ⟨hf.gaussNorm_pos, hf.norm_coeff_mul_pow_eq, fun m hm ↦ ?_⟩
  obtain rfl : m = 0 := by omega
  simpa [hnorm] using hb

/-- A monic polynomial `p` is distinguished of its degree at a radius `c > 0` at which no term
`‖pᵢ‖ cⁱ` exceeds `c ^ natDegree p`, the size of the leading term. -/
theorem _root_.Polynomial.Monic.isDistinguished [NormOneClass R] {p : Polynomial R}
    (hp : p.Monic) (hc : 0 < c) (h : ∀ i, ‖p.coeff i‖ * c ^ i ≤ c ^ p.natDegree) :
    IsDistinguished c p.natDegree (p : PowerSeries R) := by
  have hnorm : (p : PowerSeries R).gaussNorm norm c = c ^ p.natDegree := by
    rw [gaussNorm_eq_of_forall_le (s := p.natDegree)]
    · simp [hp.coeff_natDegree]
    · simpa only [Polynomial.coeff_coe, hp.coeff_natDegree, norm_one, one_mul] using h
  refine ⟨by simp [hnorm, hp.coeff_natDegree], fun m hm ↦ ?_⟩
  simp [hnorm, Polynomial.coeff_eq_zero_of_natDegree_lt hm, hc]

/-- A monic polynomial `p` is distinguished of its degree at the radius `1 + ∑ᵢ ‖pᵢ‖`, which
bounds the norms of all its coefficients. -/
theorem _root_.Polynomial.Monic.isDistinguished_one_add_sum_norm_coeff [NormOneClass R]
    {p : Polynomial R} (hp : p.Monic) :
    IsDistinguished (1 + ∑ i ∈ p.support, ‖p.coeff i‖) p.natDegree (p : PowerSeries R) := by
  set c := 1 + ∑ i ∈ p.support, ‖p.coeff i‖
  have hc1 : 1 ≤ c := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
  have hcoeff (i : ℕ) : ‖p.coeff i‖ ≤ c := by
    by_cases hi : i ∈ p.support
    · exact (Finset.single_le_sum (fun j _ ↦ norm_nonneg (p.coeff j)) hi).trans
        (le_add_of_nonneg_left zero_le_one)
    · rw [Polynomial.notMem_support_iff.mp hi, norm_zero]
      exact zero_le_one.trans hc1
  refine hp.isDistinguished (zero_lt_one.trans_le hc1) fun i ↦ ?_
  rcases lt_trichotomy i p.natDegree with hi | rfl | hi
  · calc ‖p.coeff i‖ * c ^ i ≤ c * c ^ i := by gcongr; exact hcoeff i
      _ = c ^ (i + 1) := by ring
      _ ≤ c ^ p.natDegree := pow_le_pow_right₀ hc1 hi
  · simp [hp.coeff_natDegree]
  · simp only [Polynomial.coeff_eq_zero_of_natDegree_lt hi, norm_zero, zero_mul]
    positivity

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

end SeminormedRing

section NormedRing

variable {R : Type*} [NormedRing R] {c : ℝ} {s : ℕ} {f : PowerSeries R}

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
    exact MvPowerSeries.IsRestricted.add hfr
      (MvPowerSeries.IsRestricted.neg (isRestricted_polynomial _))
  rcases eq_or_ne (f - ((f.trunc (s + 1) : Polynomial R) : PowerSeries R)) 0 with h0 | h0
  · rw [h0, PowerSeries.gaussNorm_zero norm c (norm_zero : ‖(0 : R)‖ = 0)]
    exact hf.gaussNorm_pos
  · obtain ⟨n, hn⟩ := exists_isDistinguished hc htr h0
    have hns : s < n := by
      by_contra hcon
      exact hn.coeff_ne_zero (by rw [hcoeff n, ite_eq_left (by omega)])
    rw [← hn.norm_coeff_mul_pow_eq, hcoeff n, ite_eq_right (by omega)]
    exact hf.norm_coeff_mul_pow_lt n hns

end NormedRing

section Recognition

variable {R : Type*} [SeminormedRing R] [IsUltrametricDist R] {c : ℝ} {s : ℕ} {f : PowerSeries R}

/-- **Recognising a distinguished series.** At a nonnegative radius, `f` is distinguished of degree
`s` once its weighted coefficient in degree `s` is closer than the Gauss norm to an element `a`
of weighted norm equal to the Gauss norm, and every later weighted coefficient norm is smaller
than the Gauss norm. -/
theorem isDistinguished_of_norm_coeff_sub_lt (hc : 0 ≤ c) {a : R}
    (ha : ‖a‖ * c ^ s = f.gaussNorm norm c)
    (hs : ‖f.coeff s - a‖ * c ^ s < f.gaussNorm norm c)
    (hm : ∀ m, s < m → ‖f.coeff m‖ * c ^ m < f.gaussNorm norm c) :
    IsDistinguished c s f := by
  have hlt : ‖f.coeff s - a‖ < ‖a‖ := lt_of_mul_lt_mul_right (ha ▸ hs) (pow_nonneg hc s)
  refine ⟨?_, hm⟩
  rw [← ha, ← sub_add_cancel (f.coeff s) a,
    IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne, max_eq_right hlt.le]

end Recognition

section Summation

section SeminormedRing

variable {R : Type*} [SeminormedRing R] {c : ℝ}
  {ι : Type*} {a : ι → PowerSeries R}

/-- Summable Gauss norms give summable coefficient norms in every degree over a seminormed
ring, without any completeness assumption. -/
theorem summable_norm_coeff_of_summable_gaussNorm (hc : 0 < c)
    (ha : ∀ k, (a k).HasGaussNorm norm c)
    (hs : Summable fun k ↦ (a k).gaussNorm norm c) (i : ℕ) :
    Summable fun k ↦ ‖(a k).coeff i‖ := by
  refine (hs.mul_right (c ^ i)⁻¹).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun k ↦ ?_
  rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hc i)]
  exact PowerSeries.le_gaussNorm norm c _ (ha k) i

variable [CompleteSpace R]

/-- Over a complete seminormed ring, a family of power series with summable Gauss norms has
summable coefficients in every degree. -/
theorem summable_coeff_of_summable_gaussNorm (hc : 0 < c)
    (ha : ∀ k, (a k).HasGaussNorm norm c)
    (hs : Summable fun k ↦ (a k).gaussNorm norm c) (i : ℕ) :
    Summable fun k ↦ (a k).coeff i :=
  (summable_norm_coeff_of_summable_gaussNorm hc ha hs i).of_norm

variable [IsUltrametricDist R]

/-- Over a complete ultrametric seminormed ring, a family of power series with finite Gauss
norms tending to zero along the cofinite filter has summable coefficients in every degree. -/
theorem summable_coeff_of_tendsto_gaussNorm_zero (hc : 0 < c)
    (ha : ∀ k, (a k).HasGaussNorm norm c)
    (hs : Tendsto (fun k ↦ (a k).gaussNorm norm c) cofinite (𝓝 0)) (i : ℕ) :
    Summable fun k ↦ (a k).coeff i := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun k ↦ ?_)
    (by simpa using hs.mul_const (c ^ i)⁻¹)
  rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hc i)]
  exact PowerSeries.le_gaussNorm norm c _ (ha k) i

end SeminormedRing

variable {R : Type*} [NormedRing R] {c : ℝ}
  {ι : Type*} {a : ι → PowerSeries R}

/-- The coefficientwise `tsum`s of restricted power series with summable Gauss norms form a
restricted power series over any normed ring.

Over a complete ring, `summable_coeff_of_summable_gaussNorm` ensures that these are sums of the
corresponding coefficient families. The restrictedness estimate itself does not require
completeness. -/
theorem isRestricted_mk_tsum_coeff (hc : 0 < c) (ha : ∀ k, (a k).IsRestricted c)
    (hs : Summable fun k ↦ (a k).gaussNorm norm c) :
    (PowerSeries.mk fun i ↦ ∑' k, (a k).coeff i).IsRestricted c := by
  have hsum (i) : Summable fun k ↦ ‖(a k).coeff i‖ :=
    summable_norm_coeff_of_summable_gaussNorm (R := R) hc
      (fun k ↦ hasGaussNorm_of_isRestricted (ha k)) hs i
  have hlimit : Tendsto (fun i ↦ ∑' k, ‖(a k).coeff i‖ * c ^ i) atTop (𝓝 0) := by
    simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence hs
      (fun k ↦ (PowerSeries.isRestricted_iff' c (a k)).mp (ha k))
      (.of_forall fun i k ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hc.le i))]
        exact PowerSeries.le_gaussNorm norm c _ (hasGaussNorm_of_isRestricted (ha k)) i)
  rw [PowerSeries.isRestricted_iff']
  refine squeeze_zero (fun _ ↦ by positivity) (fun i ↦ ?_) hlimit
  rw [PowerSeries.coeff_mk, tsum_mul_right]
  exact mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm (hsum i)) (pow_nonneg hc.le i)

variable [CompleteSpace R] [IsUltrametricDist R]

/-- Over a complete ultrametric ring, the coefficientwise sum of restricted power series is
restricted whenever their Gauss norms tend to zero along the cofinite filter. Unlike absolute
summability of the real Gauss norms, this is the convergence criterion intrinsic to an
ultrametric norm. The coefficient families are summable by
`summable_coeff_of_tendsto_gaussNorm_zero`. -/
theorem isRestricted_mk_tsum_coeff_of_tendsto_gaussNorm_zero (hc : 0 < c)
    (ha : ∀ k, (a k).IsRestricted c)
    (hs : Tendsto (fun k ↦ (a k).gaussNorm norm c) cofinite (𝓝 0)) :
    (PowerSeries.mk fun i ↦ ∑' k, (a k).coeff i).IsRestricted c := by
  let : Fact (0 < c) := ⟨hc⟩
  -- PowerSeries R is definitionally MvPowerSeries Unit R. Its univariate restricted-subring
  -- normed and complete instances are defined downstream in PowerSeries/TateAlgebra, which
  -- imports this file, so we use the existing multivariate instances on the same carrier here.
  let S := MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Unit ↦ c)
  let A : ι → S := fun k ↦ ⟨a k, ha k⟩
  have hnorm (k) : ‖A k‖ = (a k).gaussNorm norm c :=
    MvPowerSeries.norm_eq_gaussNorm (A k)
  have hA : Summable A := by
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [hnorm] using hs
  have hcoeff (n : ℕ) : (∑' k, (a k).coeff n) =
      PowerSeries.coeff n ((∑' k, A k : S) : PowerSeries R) := by
    let coeffHom : S →+ R :=
      (PowerSeries.coeff n).toAddMonoidHom.comp S.subtype.toAddMonoidHom
    have hcont : Continuous coeffHom :=
      MvPowerSeries.continuous_coeff_isRestrictedSubring (Finsupp.single () n)
    exact (summable_coeff_of_tendsto_gaussNorm_zero (R := R) hc
      (fun k ↦ hasGaussNorm_of_isRestricted (ha k)) hs n).hasSum.unique
      (hA.hasSum.map coeffHom hcont)
  have heq : (PowerSeries.mk fun i ↦ ∑' k, (a k).coeff i) =
      ((∑' k, A k : S) : PowerSeries R) := by
    ext n
    rw [PowerSeries.coeff_mk]
    exact hcoeff n
  rw [heq]
  exact (∑' k, A k).2

end Summation

section SeminormedRing

variable {R : Type*} [SeminormedRing R] {c : ℝ} {i j : ℕ} {f g : PowerSeries R}

section Multiplication

/-- A product term is strictly below the product of the Gauss norms, both positive, when one of
its weighted coefficients is strictly below the corresponding Gauss norm. -/
private theorem norm_coeff_mul_mul_pow_lt_of_lt (hc : 0 < c) (hbf : f.HasGaussNorm norm c)
    (hbg : g.HasGaussNorm norm c) (hf0 : 0 < f.gaussNorm norm c) (hg0 : 0 < g.gaussNorm norm c)
    {m n : ℕ}
    (h : ‖f.coeff m‖ * c ^ m < f.gaussNorm norm c ∨ ‖g.coeff n‖ * c ^ n < g.gaussNorm norm c) :
    ‖f.coeff m * g.coeff n‖ * c ^ (m + n) <
      f.gaussNorm norm c * g.gaussNorm norm c := by
  have hweight : ‖f.coeff m * g.coeff n‖ * c ^ (m + n) ≤
      (‖f.coeff m‖ * c ^ m) * (‖g.coeff n‖ * c ^ n) := by
    rw [pow_add, mul_mul_mul_comm ‖f.coeff m‖]
    exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (by positivity)
  refine hweight.trans_lt ?_
  rcases h with h | h
  · exact (mul_le_mul_of_nonneg_left (PowerSeries.le_gaussNorm norm c g hbg n)
      (mul_nonneg (norm_nonneg _) (pow_nonneg hc.le _))).trans_lt
        (mul_lt_mul_of_pos_right h hg0)
  · exact (mul_le_mul_of_nonneg_right (PowerSeries.le_gaussNorm norm c f hbf m)
      (mul_nonneg (norm_nonneg _) (pow_nonneg hc.le _))).trans_lt
        (mul_lt_mul_of_pos_left h hf0)

/-- **The strict estimate for the other product terms.** If `f` and `g` are distinguished of
degrees `i` and `j`, a product term `f.coeff m * g.coeff n` with `i < m` or `j < n` has weighted
norm strictly below the product of the Gauss norms. In degree `i + j` these are all the terms
except the dominant one. -/
theorem IsDistinguished.norm_coeff_mul_mul_pow_lt (hf : IsDistinguished c i f)
    (hg : IsDistinguished c j g) (hc : 0 < c) {m n : ℕ} (h : i < m ∨ j < n) :
    ‖f.coeff m * g.coeff n‖ * c ^ (m + n) <
      f.gaussNorm norm c * g.gaussNorm norm c :=
  norm_coeff_mul_mul_pow_lt_of_lt hc hf.hasGaussNorm hg.hasGaussNorm hf.gaussNorm_pos
    hg.gaussNorm_pos (h.imp (hf.norm_coeff_mul_pow_lt _) (hg.norm_coeff_mul_pow_lt _))

/-- A product term is strictly below the product of the Gauss norms when one of its
coefficients lies before the corresponding lowest dominant degree. -/
private theorem IsLowestDominant.norm_coeff_mul_mul_pow_lt (hf : IsLowestDominant c i f)
    (hg : IsLowestDominant c j g) (hc : 0 < c) (hbf : f.HasGaussNorm norm c)
    (hbg : g.HasGaussNorm norm c) {m n : ℕ} (h : m < i ∨ n < j) :
    ‖f.coeff m * g.coeff n‖ * c ^ (m + n) <
      f.gaussNorm norm c * g.gaussNorm norm c :=
  norm_coeff_mul_mul_pow_lt_of_lt hc hbf hbg hf.gaussNorm_pos hg.gaussNorm_pos
    (h.imp (hf.norm_coeff_mul_pow_lt _) (hg.norm_coeff_mul_pow_lt _))

variable [IsUltrametricDist R]

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

/-- If degrees `i` and `j` attain the Gauss norms of `f` and `g`, the product of the two
attaining coefficients has the product of their norms, and every other product term in degree
`i + j` is strictly below the product of the Gauss norms, then the coefficient of `f * g` in
degree `i + j` realises that product. -/
private theorem norm_coeff_mul_mul_pow_eq_of_lt (hc : 0 < c)
    (hfi : ‖f.coeff i‖ * c ^ i = f.gaussNorm norm c)
    (hgj : ‖g.coeff j‖ * c ^ j = g.gaussNorm norm c)
    (hij : ‖f.coeff i * g.coeff j‖ = ‖f.coeff i‖ * ‖g.coeff j‖)
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
        rw [hij, pow_add, ← hfi, ← hgj]
        ring
  have hcoeff : ‖(f * g).coeff (i + j)‖ = ‖f.coeff i * g.coeff j‖ := by
    rw [PowerSeries.coeff_mul]
    exact IsUltrametricDist.isNonarchimedean_norm.apply_sum_eq_of_lt
      (fun p : ℕ × ℕ ↦ f.coeff p.1 * g.coeff p.2) norm_neg
      (Finset.mem_antidiagonal.mpr (rfl : i + j = i + j)) hdom
  rw [hcoeff, hij, pow_add, ← hfi, ← hgj]
  ring

/-- **The dominant coefficient of a product of distinguished series.** If `f` is distinguished of
degree `i`, `g` of degree `j`, and the product of their distinguished coefficients has the product
of their norms, then the coefficient of `f * g` in degree `i + j` realises the product of the two
Gauss norms. The norm condition holds when the distinguished coefficient of `f` is a
multiplicative unit, or when the norm of `R` is multiplicative. -/
theorem IsDistinguished.norm_coeff_mul_mul_pow_eq_gaussNorm_mul (hf : IsDistinguished c i f)
    (hg : IsDistinguished c j g) (hc : 0 < c)
    (hij : ‖f.coeff i * g.coeff j‖ = ‖f.coeff i‖ * ‖g.coeff j‖) :
    ‖(f * g).coeff (i + j)‖ * c ^ (i + j) = f.gaussNorm norm c * g.gaussNorm norm c :=
  norm_coeff_mul_mul_pow_eq_of_lt hc hf.norm_coeff_mul_pow_eq hg.norm_coeff_mul_pow_eq hij
    fun m n hmn hne ↦ hf.norm_coeff_mul_mul_pow_lt hg hc <| by
      have : m ≠ i ∨ n ≠ j := by simpa only [Ne, Prod.ext_iff, not_and_or] using hne
      omega

/-- If `f` and `g` are distinguished of degrees `i` and `j` and the product of their
distinguished coefficients has the product of their norms, then the Gauss norm of `f * g` is the
product of the Gauss norms. -/
theorem IsDistinguished.gaussNorm_mul (hf : IsDistinguished c i f) (hg : IsDistinguished c j g)
    (hc : 0 < c) (hij : ‖f.coeff i * g.coeff j‖ = ‖f.coeff i‖ * ‖g.coeff j‖) :
    (f * g).gaussNorm norm c = f.gaussNorm norm c * g.gaussNorm norm c :=
  gaussNorm_mul_eq_of_norm_coeff_mul_pow_eq hc hf.hasGaussNorm hg.hasGaussNorm
    (hf.norm_coeff_mul_mul_pow_eq_gaussNorm_mul hg hc hij)

/-- If `f` and `g` are distinguished of degrees `i` and `j` at a positive radius and the product
of their distinguished coefficients has the product of their norms, then `f * g` is distinguished
of degree `i + j`. -/
theorem IsDistinguished.mul (hf : IsDistinguished c i f) (hg : IsDistinguished c j g)
    (hc : 0 < c) (hij : ‖f.coeff i * g.coeff j‖ = ‖f.coeff i‖ * ‖g.coeff j‖) :
    IsDistinguished c (i + j) (f * g) := by
  have hmul := hf.gaussNorm_mul hg hc hij
  refine ⟨(hf.norm_coeff_mul_mul_pow_eq_gaussNorm_mul hg hc hij).trans hmul.symm, fun m hm ↦
    hmul ▸ norm_coeff_mul_mul_pow_lt_of_forall_lt hc.le
      fun m₁ m₂ hsum ↦ hf.norm_coeff_mul_mul_pow_lt hg hc (by omega)⟩

/-- The product of series with lowest dominant degrees `i` and `j` has lowest dominant degree
`i + j` at a positive radius, provided both have bounded weighted coefficient norms and the
product of their lowest dominant coefficients has the product of their norms. -/
theorem IsLowestDominant.mul (hf : IsLowestDominant c i f) (hg : IsLowestDominant c j g)
    (hc : 0 < c) (hbf : f.HasGaussNorm norm c) (hbg : g.HasGaussNorm norm c)
    (hij : ‖f.coeff i * g.coeff j‖ = ‖f.coeff i‖ * ‖g.coeff j‖) :
    IsLowestDominant c (i + j) (f * g) := by
  have hdom : ‖(f * g).coeff (i + j)‖ * c ^ (i + j) = f.gaussNorm norm c * g.gaussNorm norm c :=
    norm_coeff_mul_mul_pow_eq_of_lt hc hf.norm_coeff_mul_pow_eq hg.norm_coeff_mul_pow_eq
      hij fun m n hmn hne ↦ hf.norm_coeff_mul_mul_pow_lt hg hc hbf hbg <| by
        have : m ≠ i ∨ n ≠ j := by simpa only [Ne, Prod.ext_iff, not_and_or] using hne
        omega
  have hmul := gaussNorm_mul_eq_of_norm_coeff_mul_pow_eq hc hbf hbg hdom
  refine ⟨hmul ▸ mul_pos hf.gaussNorm_pos hg.gaussNorm_pos, hdom.trans hmul.symm,
    fun m hm ↦ hmul ▸ norm_coeff_mul_mul_pow_lt_of_forall_lt hc.le
      fun m₁ m₂ hsum ↦ hf.norm_coeff_mul_mul_pow_lt hg hc hbf hbg (by omega)⟩

end Multiplication

end SeminormedRing

variable {R : Type*} [NormedRing R] [IsUltrametricDist R] {c : ℝ} {f g : PowerSeries R}

/-- The Gauss norm is multiplicative on restricted power series at every positive radius. -/
theorem gaussNorm_mul_of_isRestricted [NormMulClass R] (hc : 0 < c) (hf : f.IsRestricted c)
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

section

variable [NormMulClass R] [NormOneClass R]

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

end

/-! ### Gauss valuations just above and just below the radius -/

section LexValuation

section

variable {f g : PowerSeries.IsRestricted.subring (R := R) c}

/-- The distinguished degree of a nonzero restricted series, and `0` at zero. -/
private noncomputable def distinguishedDegree (hc : 0 < c)
    (f : PowerSeries.IsRestricted.subring (R := R) c) : ℕ :=
  open Classical in
  if hf : f = 0 then 0 else (exists_isDistinguished hc f.2 (by simpa using hf)).choose

private theorem isDistinguished_distinguishedDegree (hc : 0 < c) (hf : f ≠ 0) :
    IsDistinguished c (distinguishedDegree hc f) (f : PowerSeries R) := by
  simp only [distinguishedDegree, hf, ↓reduceDIte]
  exact (exists_isDistinguished hc f.2 (by simpa using hf)).choose_spec

private theorem distinguishedDegree_eq (hc : 0 < c) {s : ℕ}
    (hs : IsDistinguished c s (f : PowerSeries R)) : distinguishedDegree hc f = s :=
  (isDistinguished_distinguishedDegree hc
    (fun h ↦ hs.ne_zero (by rw [h, ZeroMemClass.coe_zero]))).unique hs

/-- The lowest dominant degree of a nonzero restricted series, and `0` at zero. -/
private noncomputable def lowestDominantDegree (hc : 0 < c)
    (f : PowerSeries.IsRestricted.subring (R := R) c) : ℕ :=
  open Classical in
  if hf : f = 0 then 0 else (exists_isLowestDominant hc f.2 (by simpa using hf)).choose

private theorem isLowestDominant_lowestDominantDegree (hc : 0 < c) (hf : f ≠ 0) :
    IsLowestDominant c (lowestDominantDegree hc f) (f : PowerSeries R) := by
  simp only [lowestDominantDegree, hf, ↓reduceDIte]
  exact (exists_isLowestDominant hc f.2 (by simpa using hf)).choose_spec

private theorem lowestDominantDegree_eq (hc : 0 < c) {s : ℕ}
    (hs : IsLowestDominant c s (f : PowerSeries R)) : lowestDominantDegree hc f = s :=
  (isLowestDominant_lowestDominantDegree hc
    (fun h ↦ hs.ne_zero (by rw [h, ZeroMemClass.coe_zero]))).unique hs

private theorem coe_one_eq_monomial :
    ((1 : PowerSeries.IsRestricted.subring (R := R) c) : PowerSeries R) =
      PowerSeries.monomial 0 1 := by
  rw [OneMemClass.coe_one, PowerSeries.monomial_zero_eq_C, map_one]

section

variable [NormOneClass R]

private theorem distinguishedDegree_one (hc : 0 < c) :
    distinguishedDegree hc (1 : PowerSeries.IsRestricted.subring (R := R) c) = 0 := by
  have := NormOneClass.nontrivial (G := R)
  have h := isDistinguished_monomial (R := R) hc one_ne_zero 0
  rw [← coe_one_eq_monomial (c := c)] at h
  exact distinguishedDegree_eq hc h

private theorem lowestDominantDegree_one (hc : 0 < c) :
    lowestDominantDegree hc (1 : PowerSeries.IsRestricted.subring (R := R) c) = 0 := by
  have := NormOneClass.nontrivial (G := R)
  have h := isLowestDominant_monomial (R := R) hc one_ne_zero 0
  rw [← coe_one_eq_monomial (c := c)] at h
  exact lowestDominantDegree_eq hc h

end

variable [NormMulClass R]

private theorem distinguishedDegree_mul (hc : 0 < c) (hf : f ≠ 0) (hg : g ≠ 0) :
    distinguishedDegree hc (f * g) = distinguishedDegree hc f + distinguishedDegree hc g := by
  have h := (isDistinguished_distinguishedDegree hc hf).mul
    (isDistinguished_distinguishedDegree hc hg) hc (norm_mul _ _)
  rw [← MulMemClass.coe_mul] at h
  exact distinguishedDegree_eq hc h

private theorem lowestDominantDegree_mul (hc : 0 < c) (hf : f ≠ 0) (hg : g ≠ 0) :
    lowestDominantDegree hc (f * g) = lowestDominantDegree hc f + lowestDominantDegree hc g := by
  have h := (isLowestDominant_lowestDominantDegree hc hf).mul
    (isLowestDominant_lowestDominantDegree hc hg) hc (hasGaussNorm_of_isRestricted f.2)
    (hasGaussNorm_of_isRestricted g.2) (norm_mul _ _)
  rw [← MulMemClass.coe_mul] at h
  exact lowestDominantDegree_eq hc h

end

variable [NormMulClass R] [NormOneClass R]
  {f g : PowerSeries.IsRestricted.subring (R := R) c}

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

/-- **Every monomial of `f` is at most `f` just above `c`.** The monomial `aₙ Xⁿ` of `f` has Gauss
norm `‖aₙ‖ cⁿ ≤ |f|_c`, and if the two agree then `n` is at most the distinguished degree of `f`,
the last degree in which `f` attains its Gauss norm. -/
theorem gaussValuationAbove_monomial_coeff_le (hc : 0 < c) (n : ℕ) :
    gaussValuationAbove hc ⟨PowerSeries.monomial n ((f : PowerSeries R).coeff n),
      PowerSeries.isRestricted_monomial c n _⟩ ≤ gaussValuationAbove hc f := by
  rcases eq_or_ne ((f : PowerSeries R).coeff n) 0 with ha | ha
  · -- the monomial with zero coefficient is the zero element of the restricted subring
    have h0 : (⟨PowerSeries.monomial n ((f : PowerSeries R).coeff n),
        PowerSeries.isRestricted_monomial c n _⟩ : PowerSeries.IsRestricted.subring (R := R) c) =
        0 :=
      Subtype.ext (by simp [ha])
    rw [h0, map_zero]
    exact zero_le
  obtain ⟨s, hs⟩ := exists_isDistinguished hc f.2 fun h ↦ ha (by simp [h])
  have hm := isDistinguished_monomial hc ha n
  rw [gaussValuationAbove_le_iff hc hm hs, ← NNReal.coe_lt_coe, ← NNReal.coe_inj,
    coe_gaussValuation, coe_gaussValuation, ← hm.norm_coeff_mul_pow_eq,
    PowerSeries.coeff_monomial_same]
  -- the weighted coefficient `‖aₙ‖ cⁿ` attains the Gauss norm only up to the distinguished degree
  exact (PowerSeries.le_gaussNorm norm c _ (hasGaussNorm_of_isRestricted f.2) n).lt_or_eq.imp_right
    fun heq ↦ ⟨heq, not_lt.mp fun hsn ↦ (hs.norm_coeff_mul_pow_lt n hsn).ne heq⟩

/-- **Every monomial of `f` is at most `f` just below `c`.** The monomial `aₙ Xⁿ` of `f` has Gauss
norm `‖aₙ‖ cⁿ ≤ |f|_c`, and if the two agree then `n` is at least the lowest dominant degree of
`f`, the first degree in which `f` attains its Gauss norm. -/
theorem gaussValuationBelow_monomial_coeff_le (hc : 0 < c) (n : ℕ) :
    gaussValuationBelow hc ⟨PowerSeries.monomial n ((f : PowerSeries R).coeff n),
      PowerSeries.isRestricted_monomial c n _⟩ ≤ gaussValuationBelow hc f := by
  rcases eq_or_ne ((f : PowerSeries R).coeff n) 0 with ha | ha
  · -- the monomial with zero coefficient is the zero element of the restricted subring
    have h0 : (⟨PowerSeries.monomial n ((f : PowerSeries R).coeff n),
        PowerSeries.isRestricted_monomial c n _⟩ : PowerSeries.IsRestricted.subring (R := R) c) =
        0 :=
      Subtype.ext (by simp [ha])
    rw [h0, map_zero]
    exact zero_le
  obtain ⟨s, hs⟩ := exists_isLowestDominant hc f.2 fun h ↦ ha (by simp [h])
  have hm := isLowestDominant_monomial hc ha n
  rw [gaussValuationBelow_le_iff hc hm hs, ← NNReal.coe_lt_coe, ← NNReal.coe_inj,
    coe_gaussValuation, coe_gaussValuation, ← hm.norm_coeff_mul_pow_eq,
    PowerSeries.coeff_monomial_same]
  -- the weighted coefficient `‖aₙ‖ cⁿ` attains the Gauss norm only from the lowest dominant degree
  exact (PowerSeries.le_gaussNorm norm c _ (hasGaussNorm_of_isRestricted f.2) n).lt_or_eq.imp_right
    fun heq ↦ ⟨heq, not_lt.mp fun hns ↦ (hs.norm_coeff_mul_pow_lt n hns).ne heq⟩

end LexValuation

end Valuation

end TauCeti.PowerSeries
