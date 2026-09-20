/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.RingTheory.PowerSeries.GaussNorm
public import Mathlib.RingTheory.PowerSeries.Restricted
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Order.LiminfLimsup

/-!
# The Gauss norm of restricted power series

A restricted power series has finite Gauss norm. At a positive radius, a nonzero restricted
series has a last coefficient attaining that norm; the degree of that coefficient is the
*distinguished degree* of the series, and `IsDistinguished` names the property. Over a
nonarchimedean normed ring with multiplicative norm, a pair of distinguished degrees produces a
dominant coefficient in a product, and the Gauss norm is therefore multiplicative on restricted
series.

The distinguished degree is the datum Weierstrass division and preparation for Tate algebras are
organised around. No completeness hypothesis is needed for the norm identities here. The radius is
any positive real number, including the unit radius of the usual Tate algebra.

Completeness enters only at the end of the file, where a family of restricted series with
summable Gauss norms is summed coefficientwise. This is the convergence statement that
successive-approximation arguments over a complete nonarchimedean ring run on, and it takes the
place of completeness of the Tate algebra for the Gauss norm.

## Main definitions

* `TauCeti.PowerSeries.IsDistinguished`: the Gauss norm is attained in degree `s` and every later
  coefficient is strictly smaller.

## Main results

* `TauCeti.PowerSeries.exists_isDistinguished`: at a positive radius, every nonzero restricted
  series is distinguished of some degree.
* `TauCeti.PowerSeries.IsDistinguished.unique`: of no more than one degree.
* `TauCeti.PowerSeries.IsDistinguished.norm_coeff_mul_mul_pow_eq_gaussNorm_mul`: the dominant
  coefficient of a product of distinguished series.
* `TauCeti.PowerSeries.gaussNorm_mul_of_isRestricted`: multiplicativity of the Gauss norm.
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

variable {R : Type*} [NormedRing R] {c : ℝ} {i j s t : ℕ} {f g : PowerSeries R}

/-- A restricted power series has bounded weighted coefficient norms. -/
theorem hasGaussNorm_of_isRestricted (hf : f.IsRestricted c) :
    f.HasGaussNorm norm c :=
  ((PowerSeries.isRestricted_iff c f).mp hf).bddAbove_range_of_cofinite

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
  let a : ℕ → ℝ := fun n ↦ ‖f.coeff n‖ * c ^ n
  have hfinite : Set.Finite (a '' {n | n ≤ s}) := (Set.finite_le_nat s).image a
  obtain ⟨b, hb⟩ := hfinite.bddAbove
  refine ⟨max b (f.gaussNorm norm c), ?_⟩
  rintro _ ⟨n, rfl⟩
  by_cases hn : n ≤ s
  · exact (hb ⟨n, hn, rfl⟩).trans (le_max_left _ _)
  · exact (hf.norm_coeff_mul_pow_lt n (Nat.lt_of_not_ge hn)).le.trans (le_max_right _ _)

/-- The distinguished degree is unique: a series cannot be distinguished of two degrees at the
same radius. -/
theorem IsDistinguished.unique (hf : IsDistinguished c s f) (hf' : IsDistinguished c t f) :
    s = t := by
  rcases lt_trichotomy s t with h | h | h
  · exact absurd hf'.norm_coeff_mul_pow_eq (hf.norm_coeff_mul_pow_lt t h).ne
  · exact h
  · exact absurd hf.norm_coeff_mul_pow_eq (hf'.norm_coeff_mul_pow_lt s h).ne

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
  have heq : a k = f.gaussNorm norm c := by
    rw [PowerSeries.gaussNorm_eq]
    exact (ciSup_eq_of_forall_le_of_forall_lt_exists_gt hbound fun _ h ↦ ⟨k, h⟩).symm
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

variable [IsUltrametricDist R]

/-- The sum of two power series with bounded weighted coefficient norms again has bounded weighted
coefficient norms at a nonnegative radius. -/
theorem hasGaussNorm_add (hc : 0 ≤ c) (hf : f.HasGaussNorm norm c)
    (hg : g.HasGaussNorm norm c) : (f + g).HasGaussNorm norm c := by
  have key (m : ℕ) :
      ‖(f + g).coeff m‖ * c ^ m ≤ max (f.gaussNorm norm c) (g.gaussNorm norm c) := by
    rw [map_add]
    calc
      ‖f.coeff m + g.coeff m‖ * c ^ m ≤ max ‖f.coeff m‖ ‖g.coeff m‖ * c ^ m :=
        mul_le_mul_of_nonneg_right (IsUltrametricDist.isNonarchimedean_norm _ _) (pow_nonneg hc m)
      _ = max (‖f.coeff m‖ * c ^ m) (‖g.coeff m‖ * c ^ m) :=
        max_mul_of_nonneg _ _ (pow_nonneg hc m)
      _ ≤ max (f.gaussNorm norm c) (g.gaussNorm norm c) :=
        max_le_max (PowerSeries.le_gaussNorm norm c _ hf m)
          (PowerSeries.le_gaussNorm norm c _ hg m)
  exact ⟨_, Set.forall_mem_range.mpr key⟩

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

variable [NormMulClass R]

/-- **The dominant coefficient of a product of distinguished series.** If `f` is distinguished of
degree `i` and `g` of degree `j`, then the coefficient of `f * g` in degree `i + j` realises the
product of the two Gauss norms. -/
theorem IsDistinguished.norm_coeff_mul_mul_pow_eq_gaussNorm_mul (hf : IsDistinguished c i f)
    (hg : IsDistinguished c j g) (hc : 0 < c) :
    ‖(f * g).coeff (i + j)‖ * c ^ (i + j) = f.gaussNorm norm c * g.gaussNorm norm c := by
  have hbf := hf.hasGaussNorm
  have hbg := hg.hasGaussNorm
  have hfp := hf.gaussNorm_pos
  have hgp := hg.gaussNorm_pos
  have hdom (p : ℕ × ℕ) (hp : p ∈ Finset.antidiagonal (i + j)) (hne : p ≠ (i, j)) :
      ‖f.coeff p.1 * g.coeff p.2‖ < ‖f.coeff i * g.coeff j‖ := by
    have hsum : p.1 + p.2 = i + j := Finset.mem_antidiagonal.mp hp
    have hweight (x y : ℕ) (hxy : x + y = i + j) :
        ‖f.coeff x * g.coeff y‖ * c ^ (i + j) =
          (‖f.coeff x‖ * c ^ x) * (‖g.coeff y‖ * c ^ y) := by
      rw [norm_mul, ← hxy, pow_add]
      ring
    apply (mul_lt_mul_iff_left₀ (pow_pos hc (i + j))).mp
    rw [hweight _ _ hsum, hweight _ _ rfl, hf.norm_coeff_mul_pow_eq, hg.norm_coeff_mul_pow_eq]
    by_cases hpi : i < p.1
    · exact (mul_le_mul_of_nonneg_left (PowerSeries.le_gaussNorm norm c g hbg p.2)
        (mul_nonneg (norm_nonneg _) (pow_nonneg hc.le _))).trans_lt
          (mul_lt_mul_of_pos_right (hf.norm_coeff_mul_pow_lt _ hpi) hgp)
    · have hpj : j < p.2 := by
        have : p.1 ≠ i ∨ p.2 ≠ j := by simpa only [Ne, Prod.ext_iff, not_and_or] using hne
        omega
      exact (mul_le_mul_of_nonneg_right (PowerSeries.le_gaussNorm norm c f hbf p.1)
        (mul_nonneg (norm_nonneg _) (pow_nonneg hc.le _))).trans_lt
          (mul_lt_mul_of_pos_left (hg.norm_coeff_mul_pow_lt _ hpj) hfp)
  have hcoeff : ‖(f * g).coeff (i + j)‖ = ‖f.coeff i * g.coeff j‖ := by
    rw [PowerSeries.coeff_mul]
    exact IsUltrametricDist.isNonarchimedean_norm.apply_sum_eq_of_lt
      (fun p : ℕ × ℕ ↦ f.coeff p.1 * g.coeff p.2) norm_neg
      (Finset.mem_antidiagonal.mpr (rfl : i + j = i + j)) hdom
  rw [hcoeff, norm_mul, pow_add, ← hf.norm_coeff_mul_pow_eq, ← hg.norm_coeff_mul_pow_eq]
  ring

/-- The Gauss norm is multiplicative on restricted power series at every positive radius. -/
theorem gaussNorm_mul_of_isRestricted (hc : 0 < c) (hf : f.IsRestricted c)
    (hg : g.IsRestricted c) :
    (f * g).gaussNorm norm c = f.gaussNorm norm c * g.gaussNorm norm c := by
  by_cases hf0 : f = 0
  · simp [hf0, PowerSeries.gaussNorm_zero norm c (norm_zero : ‖(0 : R)‖ = 0)]
  by_cases hg0 : g = 0
  · simp [hg0, PowerSeries.gaussNorm_zero norm c (norm_zero : ‖(0 : R)‖ = 0)]
  obtain ⟨i, hi⟩ := exists_isDistinguished hc hf hf0
  obtain ⟨j, hj⟩ := exists_isDistinguished hc hg hg0
  refine le_antisymm (MvPowerSeries.gaussNorm_mul_le norm (fun _ : Unit ↦ c) f g
    (fun _ ↦ hc.le) norm_nonneg norm_mul_le IsUltrametricDist.isNonarchimedean_norm
    norm_zero (hasGaussNorm_of_isRestricted hf).hasMvGaussNorm
    (hasGaussNorm_of_isRestricted hg).hasMvGaussNorm) ?_
  calc
    f.gaussNorm norm c * g.gaussNorm norm c = ‖(f * g).coeff (i + j)‖ * c ^ (i + j) :=
      (hi.norm_coeff_mul_mul_pow_eq_gaussNorm_mul hj hc).symm
    _ ≤ (f * g).gaussNorm norm c := PowerSeries.le_gaussNorm norm c (f * g)
      (hasGaussNorm_of_isRestricted (PowerSeries.isRestricted.mul c hf hg)) _

/-- The product of series distinguished in degrees `i` and `j` is distinguished in degree
`i + j` at a positive radius. -/
theorem IsDistinguished.mul (hf : IsDistinguished c i f) (hg : IsDistinguished c j g)
    (hc : 0 < c) :
    IsDistinguished c (i + j) (f * g) := by
  have hfp := hf.gaussNorm_pos
  have hgp := hg.gaussNorm_pos
  have hbf := hf.hasGaussNorm
  have hbg := hg.hasGaussNorm
  have hbmul := hasGaussNorm_mul hc.le hbf hbg
  have hmul : (f * g).gaussNorm norm c = f.gaussNorm norm c * g.gaussNorm norm c :=
    le_antisymm
      (MvPowerSeries.gaussNorm_mul_le norm (fun _ : Unit ↦ c) f g (fun _ ↦ hc.le)
        norm_nonneg norm_mul_le IsUltrametricDist.isNonarchimedean_norm norm_zero
        hbf.hasMvGaussNorm hbg.hasMvGaussNorm)
      ((hf.norm_coeff_mul_mul_pow_eq_gaussNorm_mul hg hc).symm.trans_le
        (PowerSeries.le_gaussNorm norm c (f * g) hbmul (i + j)))
  refine ⟨(hf.norm_coeff_mul_mul_pow_eq_gaussNorm_mul hg hc).trans hmul.symm,
    fun m hm ↦ ?_⟩
  rw [PowerSeries.coeff_mul]
  have hne := Finset.HasAntidiagonal.nonempty_antidiagonal m
  calc
    ‖∑ p ∈ Finset.antidiagonal m, f.coeff p.1 * g.coeff p.2‖ * c ^ m
        ≤ (Finset.antidiagonal m).sup' hne
            (fun p : ℕ × ℕ ↦ ‖f.coeff p.1 * g.coeff p.2‖) * c ^ m :=
      mul_le_mul_of_nonneg_right (hne.norm_sum_le_sup'_norm
        (fun p : ℕ × ℕ ↦ f.coeff p.1 * g.coeff p.2)) (pow_nonneg hc.le m)
    _ = (Finset.antidiagonal m).sup' hne
        (fun p : ℕ × ℕ ↦ ‖f.coeff p.1 * g.coeff p.2‖ * c ^ m) :=
      Finset.sup'_mul₀ (pow_nonneg hc.le m) _ _ _
    _ < f.gaussNorm norm c * g.gaussNorm norm c :=
      (Finset.sup'_lt_iff hne).2 fun p hp ↦ by
      have hsum : p.1 + p.2 = m := Finset.mem_antidiagonal.mp hp
      rw [← hsum, norm_mul, pow_add]
      have hweight :
          ‖f.coeff p.1‖ * ‖g.coeff p.2‖ * (c ^ p.1 * c ^ p.2) =
            (‖f.coeff p.1‖ * c ^ p.1) * (‖g.coeff p.2‖ * c ^ p.2) := by ring
      rw [hweight]
      by_cases hpi : i < p.1
      · exact (mul_le_mul_of_nonneg_left (PowerSeries.le_gaussNorm norm c g hbg p.2)
            (mul_nonneg (norm_nonneg _) (pow_nonneg hc.le _))).trans_lt
          (mul_lt_mul_of_pos_right (hf.norm_coeff_mul_pow_lt _ hpi) hgp)
      · have hpj : j < p.2 := by omega
        exact (mul_le_mul_of_nonneg_right (PowerSeries.le_gaussNorm norm c f hbf p.1)
              (mul_nonneg (norm_nonneg _) (pow_nonneg hc.le _))).trans_lt
          (mul_lt_mul_of_pos_left (hg.norm_coeff_mul_pow_lt _ hpj) hfp)
    _ = (f * g).gaussNorm norm c := hmul.symm

end TauCeti.PowerSeries
