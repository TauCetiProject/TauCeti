/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.MvPowerSeries.Restricted
public import Mathlib.RingTheory.MvPowerSeries.GaussNorm
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Data.Finsupp.MonomialOrder
import Mathlib.SetTheory.Cardinal.Order

/-!
# The Gauss norm on multivariate restricted power series

For positive polyradii `c : σ → ℝ`, the restricted-series subring of
`MvPowerSeries σ R` carries the Gauss norm, the supremum of the weighted coefficient norms
`‖aₜ‖ * ∏ i ∈ t.support, c i ^ t i`. Over an ultrametric normed ring this makes it a normed
ring, complete when the coefficient ring is complete. A multiplicative coefficient norm gives
a multiplicative Gauss norm. These structures let multivariate Tate algebras serve as coefficient
rings for Weierstrass division in another variable.

No finiteness assumption on the variable type is needed: restrictedness is convergence of the
coefficients along the cofinite filter on the exponent set.

The construction follows `TauCeti.RingTheory.PowerSeries.TateAlgebra`, using Mathlib's
multivariate restricted-series subring and Gauss norm. Multiplicativity selects a largest
Gauss-norm-achieving exponent in a lexicographic order; its product coefficient has a unique
largest summand, so Mathlib's dominant-antidiagonal theorem applies.

## Main results

* `MvPowerSeries.uniformContinuous_coeff_isRestrictedSubring`: coefficient maps are uniformly
  continuous for the Gauss norm at arbitrary positive polyradii.
* `MvPowerSeries.norm_eq_gaussNorm`: the norm is the Gauss norm at the chosen polyradii.
* `Finsupp.prod_pow_le_prod_pow_mul`: shrinking a polyradius from `c` to `c'` divides the
  monomial weight `∏ cⱼ ^ νⱼ` at least by `(cᵢ / c'ᵢ) ^ νᵢ`.
* `MvPowerSeries.norm_le_iff`: a norm bound is equivalent to bounds on every weighted coefficient.
* `MvPowerSeries.norm_lt_iff`: since the norm is attained, the same holds for strict bounds.
* `MvPowerSeries.norm_eq_norm_constantCoeff_of_norm_coeff_mul_prod_le`: a constant coefficient
  dominating every other weighted coefficient attains the Gauss norm.
* `MvPowerSeries.IsRestricted.exists_achievesGaussNorm_max`: a nonzero restricted series has a
  largest norm-achieving exponent for any monomial order, and
  `MvPowerSeries.IsRestricted.norm_coeff_mul_norm_coeff_lt`: the product of the coefficients at
  such exponents of two series dominates every other summand of the product coefficient;
  `MvPowerSeries.IsRestricted.exists_norm_coeff_mul_norm_coeff_lt` chooses such exponents.
* `MvPowerSeries.exists_achievesGaussNorm` and `MvPowerSeries.exists_norm_coeff_mul_prod_gap`: a
  restricted series attains its norm, and its smaller weighted coefficient norms stay below a
  constant smaller than its norm.
* The restricted-series subring inherits `CompleteSpace`, `IsUltrametricDist`, and
  `NormMulClass` from its coefficient ring.
* `MvPowerSeries.dense_closure_monomial`: polynomials with coefficients in a dense subset of the
  coefficient ring are dense.
* `MvPowerSeries.isRestricted_renameEquiv_iff`: renaming the variables along an equivalence
  reindexes the polyradii, and `MvPowerSeries.IsRestricted.renameAlgEquiv` is the resulting
  algebra isomorphism of restricted-series subrings.
* `MvPowerSeries.mk_monomial_eq_algebraMap_mul_prod`: a restricted monomial `r Xᵗ` is the constant
  `r` times the product of the variables.
* The restricted-series subring is an algebra over every algebra `S` of coefficients, through the
  constant series, and over a normed field `K` restricted series over a normed `K`-algebra form a
  `NormedAlgebra` over `K`.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.1.1 and §5.2.1.
-/

public section

namespace MvPowerSeries

open Filter
open scoped Topology

section NormedRing

variable {σ R : Type*} [NormedRing R]

/-- Restricted series have bounded weighted coefficient norms. -/
theorem IsRestricted.hasGaussNorm {c : σ → ℝ} {f : MvPowerSeries σ R}
    (hf : IsRestricted c f) : HasGaussNorm norm c f :=
  hf.bddAbove_range_of_cofinite

/-- The weights `∏ i, |c i| ^ t i` of the absolute polyradii are nonnegative. -/
theorem prod_abs_pow_nonneg {c : σ → ℝ} (t : σ →₀ ℕ) : 0 ≤ t.prod (|c| · ^ ·) :=
  Finset.prod_nonneg fun _ _ ↦ pow_nonneg (abs_nonneg _) _

/-- Decreasing the polyradius `c` to `c'`, the weight of an exponent drops at least by the factor
`(c'ᵢ / cᵢ) ^ νᵢ` coming from the variable `Xᵢ`. -/
theorem _root_.Finsupp.prod_pow_le_prod_pow_mul {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {c c' : σ → K} {i : σ} (hc' : ∀ j, 0 ≤ c' j)
    (hle : ∀ j, c' j ≤ c j) (hi : 0 < c i) (n : σ →₀ ℕ) :
    n.prod (c' · ^ ·) ≤ n.prod (c · ^ ·) * (c' i / c i) ^ n i := by
  classical
  calc n.prod (c' · ^ ·)
      ≤ n.prod fun j k ↦ c j ^ k * (if j = i then (c' i / c i) ^ k else 1) := by
        refine Finset.prod_le_prod₀ (fun j _ ↦ pow_nonneg (hc' j) _) fun j _ ↦ ?_
        dsimp only
        split_ifs with h
        · subst h
          rw [← mul_pow, mul_div_cancel₀ _ hi.ne']
        · rw [mul_one]
          exact pow_le_pow_left₀ (hc' j) (hle j) _
    _ = n.prod (c · ^ ·) * (c' i / c i) ^ n i := by
        rw [Finsupp.prod_mul]
        congr 1
        simp only [Finsupp.prod, Finset.prod_ite_eq', Finsupp.mem_support_iff]
        split_ifs with h
        · rfl
        · rw [not_not.1 h, pow_zero]

variable [IsUltrametricDist R] {c : σ → ℝ} [hc : ∀ i, Fact (0 < c i)]

/-- At positive polyradii, the weight `∏ i, c i ^ t i` of an exponent is positive. -/
theorem prod_pow_pos (t : σ →₀ ℕ) : 0 < t.prod (c · ^ ·) :=
  Finset.prod_pos fun i _ ↦ pow_pos (hc i).out _

omit hc in
/-- The weights of exponents are multiplicative. -/
theorem prod_pow_add (s t : σ →₀ ℕ) :
    (s + t).prod (c · ^ ·) = s.prod (c · ^ ·) * t.prod (c · ^ ·) :=
  Finsupp.prod_add_index' (fun _ ↦ pow_zero _) fun _ _ _ ↦ pow_add _ _ _

/-- At positive polyradii the restricted-series subring carries its Gauss norm. -/
noncomputable instance instNormedRingIsRestrictedSubring :
    NormedRing (IsRestricted.subring (R := R) c) :=
  RingNorm.toNormedRing
    { toFun f := gaussNorm norm c (f : MvPowerSeries σ R)
      map_zero' := gaussNorm_zero norm _ norm_zero
      add_le' f g :=
        (gaussNorm_add_le_max norm c (f : MvPowerSeries σ R) (g : MvPowerSeries σ R)
          (fun i ↦ (hc i).out.le) norm_nonneg
          IsUltrametricDist.isNonarchimedean_norm f.2.hasGaussNorm g.2.hasGaussNorm).trans
          (max_le_add_of_nonneg (gaussNorm_nonneg norm _ _ norm_nonneg)
            (gaussNorm_nonneg norm _ _ norm_nonneg))
      neg' f := gaussNorm_neg (fun x : R ↦ ‖x‖) c (fun x ↦ norm_neg x)
        (f : MvPowerSeries σ R)
      mul_le' f g := gaussNorm_mul_le norm c (f : MvPowerSeries σ R)
        (g : MvPowerSeries σ R) (fun i ↦ (hc i).out.le) norm_nonneg
        norm_mul_le IsUltrametricDist.isNonarchimedean_norm norm_zero
        f.2.hasGaussNorm g.2.hasGaussNorm
      eq_zero_of_map_eq_zero' f h := by
        rwa [gaussNorm_eq_zero_iff norm _ _ norm_zero norm_nonneg
          (fun _ ↦ norm_eq_zero.mp) (fun i ↦ (hc i).out) f.2.hasGaussNorm,
          ZeroMemClass.coe_eq_zero] at h }

/-- The norm of a restricted series is its Gauss norm at the chosen polyradii. -/
theorem norm_eq_gaussNorm (f : IsRestricted.subring (R := R) c) :
    ‖f‖ = gaussNorm norm c (f : MvPowerSeries σ R) := (rfl)

/-- Every weighted coefficient norm is bounded by the Gauss norm of the restricted series. -/
theorem norm_coeff_mul_prod_le (f : IsRestricted.subring (R := R) c) (t : σ →₀ ℕ) :
    ‖coeff t (f : MvPowerSeries σ R)‖ * t.prod (c · ^ ·) ≤ ‖f‖ :=
  le_gaussNorm norm c _ f.2.hasGaussNorm t

/-- Coefficient maps are uniformly continuous for the Gauss norm, with bound `(cᵗ)⁻¹`. -/
theorem uniformContinuous_coeff_isRestrictedSubring (t : σ →₀ ℕ) :
    UniformContinuous fun f : IsRestricted.subring (R := R) c ↦ coeff t (f : MvPowerSeries σ R) :=
  AddMonoidHomClass.uniformContinuous_of_bound
    ((coeff t).toAddMonoidHom.comp (IsRestricted.subring (R := R) c).subtype.toAddMonoidHom)
    (t.prod (c · ^ ·))⁻¹ fun f ↦ by
      rw [inv_mul_eq_div, le_div_iff₀ (prod_pow_pos t)]
      exact norm_coeff_mul_prod_le f t

/-- **Coefficients are continuous for the Gauss norm**: the coefficient of `Xᵗ` is bounded by
`(cᵗ)⁻¹` times the Gauss norm. -/
theorem continuous_coeff_isRestrictedSubring (t : σ →₀ ℕ) :
    Continuous fun f : IsRestricted.subring (R := R) c ↦ coeff t (f : MvPowerSeries σ R) :=
  (uniformContinuous_coeff_isRestrictedSubring t).continuous

/-- A nonnegative bound on the norm is exactly a bound on every weighted coefficient norm. -/
theorem norm_le_iff {f : IsRestricted.subring (R := R) c} {r : ℝ}
    (hr : 0 ≤ r) : ‖f‖ ≤ r ↔ ∀ t, ‖coeff t (f : MvPowerSeries σ R)‖ * t.prod (c · ^ ·) ≤ r := by
  refine ⟨fun h t ↦ (norm_coeff_mul_prod_le f t).trans h, fun h ↦ ?_⟩
  rw [norm_eq_gaussNorm, gaussNorm]
  exact Real.iSup_le (by simpa using h) hr

/-- A constant coefficient dominating the weighted norm of every other coefficient attains the
Gauss norm. -/
theorem norm_eq_norm_constantCoeff_of_norm_coeff_mul_prod_le
    {f : IsRestricted.subring (R := R) c}
    (h : ∀ t ≠ 0, ‖coeff t (f : MvPowerSeries σ R)‖ * t.prod (c · ^ ·) ≤
      ‖constantCoeff (f : MvPowerSeries σ R)‖) :
    ‖f‖ = ‖constantCoeff (f : MvPowerSeries σ R)‖ := by
  refine le_antisymm ((norm_le_iff (norm_nonneg _)).2 fun t ↦ ?_) ?_
  · rcases eq_or_ne t 0 with rfl | ht
    · simp [coeff_zero_eq_constantCoeff_apply]
    · exact h t ht
  · simpa [coeff_zero_eq_constantCoeff_apply] using norm_coeff_mul_prod_le f 0

/-- **The norm gap of a restricted series.** The weighted coefficient norms of a nonzero
restricted series that are smaller than its norm are bounded by a constant smaller than its
norm: only finitely many of them exceed half the norm. -/
theorem exists_norm_coeff_mul_prod_gap (f : IsRestricted.subring (R := R) c) (hf : f ≠ 0) :
    ∃ ε, 0 ≤ ε ∧ ε < ‖f‖ ∧ ∀ t, ‖coeff t (f : MvPowerSeries σ R)‖ * t.prod (c · ^ ·) < ‖f‖ →
      ‖coeff t (f : MvPowerSeries σ R)‖ * t.prod (c · ^ ·) ≤ ε := by
  classical
  set M := ‖f‖
  set w : (σ →₀ ℕ) → ℝ := fun t ↦ ‖coeff t (f : MvPowerSeries σ R)‖ * t.prod (c · ^ ·)
  have hM : 0 < M := norm_pos_iff.mpr hf
  have hF : {t | M / 2 ≤ w t}.Finite := by
    simpa [eventually_cofinite, not_lt] using f.2.eventually (gt_mem_nhds (half_pos hM))
  let F' := hF.toFinset.filter fun t ↦ w t < M
  rcases F'.eq_empty_or_nonempty with hF' | hF'
  · refine ⟨M / 2, (half_pos hM).le, half_lt_self hM, fun t ht ↦ le_of_not_ge fun h ↦ ?_⟩
    have : t ∈ F' := Finset.mem_filter.mpr ⟨hF.mem_toFinset.mpr h, ht⟩
    simp [hF'] at this
  · obtain ⟨t₀, ht₀, hmax⟩ := F'.exists_max_image w hF'
    refine ⟨max (M / 2) (w t₀), (half_pos hM).le.trans (le_max_left _ _),
      max_lt (half_lt_self hM) (Finset.mem_filter.mp ht₀).2, fun t ht ↦ ?_⟩
    by_cases h : M / 2 ≤ w t
    · exact le_max_of_le_right (hmax t (Finset.mem_filter.mpr ⟨hF.mem_toFinset.mpr h, ht⟩))
    · exact le_max_of_le_left (le_of_not_ge h)

/-- A restricted series attains its Gauss norm at some exponent. -/
theorem exists_achievesGaussNorm (f : IsRestricted.subring (R := R) c) :
    ∃ t, AchievesGaussNorm norm c (f : MvPowerSeries σ R) t := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact ⟨0, by simp [AchievesGaussNorm, gaussNorm_zero]⟩
  obtain ⟨ε, hε0, hεM, hε⟩ := exists_norm_coeff_mul_prod_gap f hf
  by_contra! h
  have hM : ‖f‖ ≤ ε := (norm_le_iff hε0).mpr fun t ↦
    hε t ((norm_coeff_mul_prod_le f t).lt_of_ne (h t))
  exact hM.not_gt hεM

/-- A strict bound on the norm is exactly a strict bound on every weighted coefficient norm,
since the norm is attained. -/
theorem norm_lt_iff {f : IsRestricted.subring (R := R) c} {r : ℝ} :
    ‖f‖ < r ↔ ∀ t, ‖coeff t (f : MvPowerSeries σ R)‖ * t.prod (c · ^ ·) < r := by
  refine ⟨fun h t ↦ (norm_coeff_mul_prod_le f t).trans_lt h, fun h ↦ ?_⟩
  obtain ⟨t, ht⟩ := exists_achievesGaussNorm f
  rw [norm_eq_gaussNorm, ← ht]
  exact h t

/-- The norm of a restricted monomial is its weighted coefficient norm. -/
@[simp]
theorem norm_monomial (t : σ →₀ ℕ) (a : R) :
    ‖(⟨monomial t a, isRestricted_monomial _ t a⟩ :
      IsRestricted.subring (R := R) c)‖ = ‖a‖ * t.prod (c · ^ ·) := by
  classical
  apply le_antisymm
  · rw [norm_le_iff (mul_nonneg (norm_nonneg a) (prod_pow_pos t).le)]
    intro s
    by_cases h : s = t <;>
      simp [coeff_monomial, h, mul_nonneg (norm_nonneg a) (prod_pow_pos t).le]
  · simpa using norm_coeff_mul_prod_le
      (⟨monomial t a, isRestricted_monomial _ t a⟩ :
        IsRestricted.subring (R := R) c) t

/-- Constants retain their coefficient norm. -/
@[simp]
theorem norm_C (a : R) :
    ‖(⟨C a, isRestricted_C _ a⟩ :
      IsRestricted.subring (R := R) c)‖ = ‖a‖ := by
  simpa [monomial_zero_eq_C_apply] using norm_monomial (σ := σ) 0 a

/-- Each variable has norm equal to its radius when the coefficient norm of `1` is `1`. -/
@[simp]
theorem norm_X [NormOneClass R] (i : σ) :
    ‖(⟨X i, isRestricted_monomial c (Finsupp.single i 1) (1 : R)⟩ :
      IsRestricted.subring (R := R) c)‖ = c i := by
  classical
  simp [X]

/-- **Polynomials are dense in the restricted series**: every element of `R{X/c}` is a limit of
finite sums of monomials whose coefficients lie in a given dense subset of `R`. -/
theorem dense_closure_monomial {s : Set R} (hs : Dense s) :
    Dense (AddSubgroup.closure ((fun x : (σ →₀ ℕ) × R ↦
      (⟨monomial x.1 x.2, isRestricted_monomial c x.1 x.2⟩ : IsRestricted.subring (R := R) c)) ''
        (Set.univ ×ˢ s)) :
        Set (IsRestricted.subring (R := R) c)) := by
  classical
  refine Metric.dense_iff.mpr fun f ε hε ↦ ?_
  set w : (σ →₀ ℕ) → ℝ := fun t ↦ ‖coeff t (f : MvPowerSeries σ R)‖ * t.prod (c · ^ ·)
  -- only finitely many weighted coefficients are at least `ε / 2`
  have hF : {t | ε / 2 ≤ w t}.Finite := by
    simpa [Filter.eventually_cofinite, not_lt] using f.2.eventually (gt_mem_nhds (half_pos hε))
  -- approximate each of these coefficients by an element of `s` up to `ε / 2` in weighted norm
  have happrox (t : σ →₀ ℕ) : ∃ a ∈ s,
      ‖coeff t (f : MvPowerSeries σ R) - a‖ * t.prod (c · ^ ·) < ε / 2 := by
    obtain ⟨a, ha, has⟩ := Metric.dense_iff.mp hs (coeff t (f : MvPowerSeries σ R))
      (ε / 2 / t.prod (c · ^ ·)) (div_pos (half_pos hε) (prod_pow_pos t))
    exact ⟨a, has, by rwa [Metric.mem_ball, dist_comm, dist_eq_norm, lt_div_iff₀ (prod_pow_pos t)]
      at ha⟩
  choose a has ha using happrox
  set q : IsRestricted.subring (R := R) c := ∑ t ∈ hF.toFinset,
    ⟨monomial t (a t), isRestricted_monomial c _ _⟩
  refine ⟨q, ?_, AddSubgroup.sum_mem _ fun t _ ↦
    AddSubgroup.subset_closure ⟨(t, a t), ⟨trivial, has t⟩, rfl⟩⟩
  rw [Metric.mem_ball, dist_comm, dist_eq_norm]
  refine ((norm_le_iff (half_pos hε).le).mpr fun t ↦ ?_).trans_lt (half_lt_self hε)
  have hq : coeff t (q : MvPowerSeries σ R) = if t ∈ hF.toFinset then a t else 0 := by
    simp [q, coeff_monomial]
  rw [AddSubgroupClass.coe_sub, map_sub, hq]
  split_ifs with ht
  · exact (ha t).le
  · simpa [w] using (not_le.mp fun h ↦ ht (hF.mem_toFinset.mpr h)).le

/-- The Gauss norm is ultrametric when the coefficient norm is. -/
instance : IsUltrametricDist (IsRestricted.subring (R := R) c) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun f g ↦
    gaussNorm_add_le_max norm c (f : MvPowerSeries σ R) (g : MvPowerSeries σ R)
      (fun i ↦ (hc i).out.le) norm_nonneg
      IsUltrametricDist.isNonarchimedean_norm f.2.hasGaussNorm g.2.hasGaussNorm

/-- The Gauss norm preserves the norm of `1` from the coefficient ring. -/
instance [NormOneClass R] : NormOneClass
    (IsRestricted.subring (R := R) c) where
  norm_one := by
    have h : (1 : IsRestricted.subring (R := R) c) =
        ⟨C 1, isRestricted_C _ 1⟩ := Subtype.ext (map_one C).symm
    rw [h, norm_C, norm_one]

/-- The restricted-series Gauss norm is complete over a complete coefficient ring. -/
instance [CompleteSpace R] : CompleteSpace
    (IsRestricted.subring (R := R) c) := by
  refine Metric.complete_of_cauchySeq_tendsto fun F hF ↦ ?_
  have hcoeff (t : σ →₀ ℕ) : CauchySeq fun k ↦ coeff t (F k : MvPowerSeries σ R) :=
    (uniformContinuous_coeff_isRestrictedSubring t).comp_cauchySeq hF
  -- Multivariate power series are coefficient functions; `a` is their coefficientwise limit.
  choose a ha using fun t ↦ cauchySeq_tendsto_of_complete (hcoeff t)
  have hunif : ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ t,
      ‖coeff t (F k : MvPowerSeries σ R) - a t‖ * t.prod (c · ^ ·) ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hF ε hε
    refine ⟨N, fun k hk t ↦ le_of_tendsto
      (((tendsto_const_nhds.sub (ha t)).norm).mul_const (t.prod (c · ^ ·)))
      (eventually_atTop.mpr ⟨N, fun l hl ↦ ?_⟩)⟩
    have h := norm_coeff_mul_prod_le (F k - F l) t
    rw [AddSubgroupClass.coe_sub, map_sub] at h
    exact h.trans ((dist_eq_norm _ _).symm.trans_le (hN k hk l hl).le)
  have hg : IsRestricted c (a : MvPowerSeries σ R) := by
    refine tendsto_order.mpr ⟨fun b hb ↦ .of_forall fun t ↦
      hb.trans_le (mul_nonneg (norm_nonneg _) (prod_pow_pos t).le), fun ε hε ↦ ?_⟩
    obtain ⟨N, hN⟩ := hunif (ε / 2) (half_pos hε)
    filter_upwards [((F N).2).eventually (gt_mem_nhds (half_pos hε))] with t ht
    calc ‖coeff t (a : MvPowerSeries σ R)‖ * t.prod (c · ^ ·)
        ≤ ‖coeff t (F N : MvPowerSeries σ R)‖ * t.prod (c · ^ ·) +
          ‖coeff t (F N : MvPowerSeries σ R) - a t‖ * t.prod (c · ^ ·) := by
            rw [← add_mul]
            exact mul_le_mul_of_nonneg_right
              (by
                rw [coeff_apply (a : MvPowerSeries σ R) t]
                exact norm_le_norm_add_norm_sub
                  (coeff t (F N : MvPowerSeries σ R)) (a t)) (prod_pow_pos t).le
      _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le ht (hN N le_rfl t)
      _ = ε := add_halves ε
  refine ⟨⟨a, hg⟩, Metric.tendsto_atTop.mpr fun ε hε ↦ ?_⟩
  obtain ⟨N, hN⟩ := hunif (ε / 2) (half_pos hε)
  refine ⟨N, fun k hk ↦ (?_ : _ ≤ ε / 2).trans_lt (half_lt_self hε)⟩
  rw [dist_eq_norm, norm_le_iff (half_pos hε).le]
  intro t
  rw [AddSubgroupClass.coe_sub, map_sub, coeff_apply (a : MvPowerSeries σ R) t]
  exact hN k hk t

omit [IsUltrametricDist R] in
/-- A nonzero restricted series has a largest exponent, for a monomial order `m`, achieving its
Gauss norm: at all larger exponents the weighted coefficient norm is smaller. This tie breaking
isolates one product summand. -/
theorem IsRestricted.exists_achievesGaussNorm_max (m : MonomialOrder σ) {f : MvPowerSeries σ R}
    (hf : IsRestricted c f) (hf0 : f ≠ 0) :
    ∃ i, AchievesGaussNorm norm c f i ∧ ∀ t, m.toSyn i < m.toSyn t →
      ‖coeff t f‖ * t.prod (c · ^ ·) < gaussNorm norm c f := by
  classical
  obtain ⟨i, hi⟩ := (ne_zero_iff_exists_coeff_ne_zero f).mp hf0
  let a : (σ →₀ ℕ) → ℝ := fun t ↦ ‖coeff t f‖ * t.prod (c · ^ ·)
  have hi_pos : 0 < a i := mul_pos (norm_pos_iff.mpr hi) (prod_pow_pos i)
  have hfinite : {t | a i ≤ a t}.Finite := by
    have h := hf.eventually (gt_mem_nhds hi_pos)
    simpa only [eventually_cofinite, not_lt] using h
  let S := hfinite.toFinset
  have hi_mem : i ∈ S := by simp [S]
  obtain ⟨j, hj, hmax⟩ := S.exists_max_image a ⟨i, hi_mem⟩
  have hbound (t) : a t ≤ a j := by
    by_cases ht : t ∈ S
    · exact hmax t ht
    · have ht' : a t < a i := by simpa [S] using ht
      exact ht'.le.trans (hmax i hi_mem)
  have heq : a j = gaussNorm norm c f := by
    rw [gaussNorm]
    exact (ciSup_eq_of_forall_le_of_forall_lt_exists_gt hbound fun _ h ↦ ⟨j, h⟩).symm
  let T := S.filter fun t ↦ a t = a j
  have hj_mem : j ∈ T := by simp [T, hj]
  obtain ⟨n, hn, hnmax⟩ := T.exists_max_image m.toSyn ⟨j, hj_mem⟩
  have hn_eq : a n = a j := (Finset.mem_filter.mp hn).2
  refine ⟨n, hn_eq.trans heq, fun t ht ↦ ?_⟩
  rw [← heq]
  refine lt_of_le_of_ne (hbound t) fun h ↦ ?_
  have ht_mem : t ∈ T := by
    simp only [T, Finset.mem_filter]
    exact ⟨by simpa [S] using (hmax i hi_mem).trans_eq h.symm, h⟩
  exact (not_le_of_gt ht) (hnmax t ht_mem)

omit [IsUltrametricDist R] in
/-- A nonzero restricted series has positive Gauss norm. -/
theorem IsRestricted.gaussNorm_pos {f : MvPowerSeries σ R} (hf : IsRestricted c f)
    (hf0 : f ≠ 0) : 0 < gaussNorm norm c f :=
  (gaussNorm_nonneg norm c f norm_nonneg).lt_of_ne' fun h ↦ hf0 <|
    (gaussNorm_eq_zero_iff norm c f norm_zero norm_nonneg (fun _ ↦ norm_eq_zero.mp)
      (fun i ↦ (hc i).out) hf.hasGaussNorm).mp h

omit [IsUltrametricDist R] in
/-- A nonzero restricted series has a nonzero coefficient at every exponent where it attains its
Gauss norm. -/
theorem IsRestricted.coeff_ne_zero_of_achievesGaussNorm {f : MvPowerSeries σ R}
    (hf : IsRestricted c f) (hf0 : f ≠ 0) {i : σ →₀ ℕ} (hi : AchievesGaussNorm norm c f i) :
    coeff i f ≠ 0 := by
  intro h
  rw [AchievesGaussNorm, h, norm_zero, zero_mul] at hi
  exact (hf.gaussNorm_pos hf0).ne hi

omit [IsUltrametricDist R] in
/-- **The dominant product summand.** Let `i` and `j` be the largest exponents, for a monomial
order `m`, at which nonzero restricted series `f` and `g` attain their Gauss norms. Every other
summand `coeff p.1 f * coeff p.2 g` of the coefficient of `f * g` at `i + j` has a strictly
smaller product of coefficient norms than `coeff i f * coeff j g`. -/
theorem IsRestricted.norm_coeff_mul_norm_coeff_lt [DecidableEq σ] (m : MonomialOrder σ)
    {f g : MvPowerSeries σ R} (hf : IsRestricted c f) (hg : IsRestricted c g) (hf0 : f ≠ 0)
    (hg0 : g ≠ 0) {i j : σ →₀ ℕ} (hi : AchievesGaussNorm norm c f i)
    (himax : ∀ t, m.toSyn i < m.toSyn t → ‖coeff t f‖ * t.prod (c · ^ ·) < gaussNorm norm c f)
    (hj : AchievesGaussNorm norm c g j)
    (hjmax : ∀ t, m.toSyn j < m.toSyn t → ‖coeff t g‖ * t.prod (c · ^ ·) < gaussNorm norm c g)
    {p : (σ →₀ ℕ) × (σ →₀ ℕ)} (hp : p ∈ Finset.antidiagonal (i + j)) (hne : p ≠ (i, j)) :
    ‖coeff p.1 f‖ * ‖coeff p.2 g‖ < ‖coeff i f‖ * ‖coeff j g‖ := by
  have hp' : p.1 + p.2 = i + j := Finset.mem_antidiagonal.mp hp
  -- Every summand at this exponent has the same positive weight.
  have hweight : p.1.prod (c · ^ ·) * p.2.prod (c · ^ ·) =
      i.prod (c · ^ ·) * j.prod (c · ^ ·) := by
    simpa [prod_pow_add] using congrArg (fun t ↦ t.prod (c · ^ ·)) hp'
  -- A different pair forces one exponent beyond the chosen maximal norm achiever.
  have hsyn : m.toSyn p.1 + m.toSyn p.2 = m.toSyn i + m.toSyn j := by
    rw [← map_add, ← map_add, hp']
  have hlt : (‖coeff p.1 f‖ * p.1.prod (c · ^ ·)) *
      (‖coeff p.2 g‖ * p.2.prod (c · ^ ·)) < gaussNorm norm c f * gaussNorm norm c g := by
    rcases trichotomy_of_add_eq_add hsyn with h | h | h
    · exact False.elim (hne (Prod.ext (m.toSyn.injective h.1) (m.toSyn.injective h.2)))
    · have hp2 : m.toSyn j < m.toSyn p.2 :=
        lt_of_add_lt_add_left (hsyn ▸ add_lt_add_left h (m.toSyn p.2))
      exact mul_lt_mul' (le_gaussNorm norm c f hf.hasGaussNorm p.1)
        (hjmax p.2 hp2) (mul_nonneg (norm_nonneg _) (prod_pow_pos _).le) (hf.gaussNorm_pos hf0)
    · have hp1 : m.toSyn i < m.toSyn p.1 :=
        lt_of_add_lt_add_right (hsyn ▸ add_lt_add_right h (m.toSyn p.1))
      simpa only [mul_comm] using
        mul_lt_mul' (le_gaussNorm norm c g hg.hasGaussNorm p.2) (himax p.1 hp1)
          (mul_nonneg (norm_nonneg _) (prod_pow_pos _).le) (hg.gaussNorm_pos hg0)
  rw [← hi, ← hj] at hlt
  -- Cancel the common positive weight.
  apply (mul_lt_mul_iff_of_pos_right
    (mul_pos (prod_pow_pos (c := c) i) (prod_pow_pos (c := c) j))).mp
  calc
    _ = (‖coeff p.1 f‖ * p.1.prod (c · ^ ·)) *
        (‖coeff p.2 g‖ * p.2.prod (c · ^ ·)) := by rw [← hweight]; ring
    _ < (‖coeff i f‖ * i.prod (c · ^ ·)) *
        (‖coeff j g‖ * j.prod (c · ^ ·)) := hlt
    _ = _ := by ring

omit [IsUltrametricDist R] in
/-- **A dominant product summand exists.** Nonzero restricted series `f` and `g` attain their
Gauss norms at exponents `i` and `j` that are not attained at any proper multiple
`i + s` or `j + s`, and such that `coeff i f * coeff j g` has a strictly larger product of
coefficient norms than every other summand of the coefficient of `f * g` at `i + j`. -/
theorem IsRestricted.exists_norm_coeff_mul_norm_coeff_lt [DecidableEq σ] {f g : MvPowerSeries σ R}
    (hf : IsRestricted c f) (hg : IsRestricted c g) (hf0 : f ≠ 0) (hg0 : g ≠ 0) :
    ∃ i j, AchievesGaussNorm norm c f i ∧ AchievesGaussNorm norm c g j ∧
      (∀ s ≠ 0, ‖coeff (i + s) f‖ * (i + s).prod (c · ^ ·) < gaussNorm norm c f) ∧
      (∀ s ≠ 0, ‖coeff (j + s) g‖ * (j + s).prod (c · ^ ·) < gaussNorm norm c g) ∧
      ∀ p ∈ Finset.antidiagonal (i + j), p ≠ (i, j) →
        ‖coeff p.1 f‖ * ‖coeff p.2 g‖ < ‖coeff i f‖ * ‖coeff j g‖ := by
  classical
  -- Choose lexicographically largest norm-achieving exponents. The order is only proof data.
  let : LinearOrder σ := linearOrderOfSTO (Function.swap WellOrderingRel)
  have : WellFoundedGT σ := (WellOrderingRel.isWellOrder (α := σ)).wf.mono fun _ _ h ↦ h
  let m : MonomialOrder σ := MonomialOrder.lex
  obtain ⟨i, hi, himax⟩ := hf.exists_achievesGaussNorm_max m hf0
  obtain ⟨j, hj, hjmax⟩ := hg.exists_achievesGaussNorm_max m hg0
  -- A proper multiple is larger in every monomial order.
  have hlt (k s : σ →₀ ℕ) (hs : s ≠ 0) : m.toSyn k < m.toSyn (k + s) := by
    rw [map_add]
    exact lt_add_of_pos_right _
      (m.toSyn_lt_iff_ne_zero.mpr ((m.toSyn_eq_zero_iff s).not.mpr hs))
  exact ⟨i, j, hi, hj, fun s hs ↦ himax _ (hlt i s hs), fun s hs ↦ hjmax _ (hlt j s hs),
    fun p hp hne ↦ hf.norm_coeff_mul_norm_coeff_lt m hg hf0 hg0 hi himax hj hjmax hp hne⟩

/-- The Gauss norm of a product of restricted series is the product of their Gauss norms when
the coefficient norm is multiplicative. Positive polyradii are arbitrary. -/
theorem IsRestricted.gaussNorm_mul [NormMulClass R] {f g : MvPowerSeries σ R}
    (hf : IsRestricted c f) (hg : IsRestricted c g) :
    gaussNorm norm c (f * g) = gaussNorm norm c f * gaussNorm norm c g := by
  classical
  by_cases hf0 : f = 0
  · simp [hf0, gaussNorm_zero (R := R) norm c norm_zero]
  by_cases hg0 : g = 0
  · simp [hg0, gaussNorm_zero (R := R) norm c norm_zero]
  obtain ⟨i, j, hi, hj, -, -, hdom⟩ := hf.exists_norm_coeff_mul_norm_coeff_lt hg hf0 hg0
  refine gaussNorm_mul_eq_mul norm c f g hf.hasGaussNorm hg.hasGaussNorm
    (hf.mul hg).hasGaussNorm norm_nonneg norm_zero
    IsUltrametricDist.isNonarchimedean_norm norm_mul norm_neg
    (fun _ ↦ norm_eq_zero.mp) (fun i ↦ (hc i).out) ⟨i, j, hi, hj, fun p hp hne ↦ ?_⟩
  simpa only [norm_mul] using hdom p hp hne

/-- The Gauss norm inherits multiplicativity from the coefficient norm. -/
instance [NormMulClass R] : NormMulClass (IsRestricted.subring (R := R) c) where
  norm_mul f g := f.2.gaussNorm_mul g.2

end NormedRing

section NormedCommRing

variable {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R] {c : σ → ℝ}

/-- Restricted series form an algebra over every algebra `S` of coefficients, via the
constant-series embedding. For `S = R` this is the coefficient algebra. -/
noncomputable instance instAlgebraIsRestrictedSubring {S : Type*} [CommSemiring S]
    [Algebra S R] : Algebra S (IsRestricted.subring (R := R) c) :=
  ((C.codRestrict _ (isRestricted_C c)).comp (algebraMap S R)).toAlgebra

/-- The algebra structures over `S` and over the coefficients `R` form a scalar tower. -/
instance {S : Type*} [CommSemiring S] [Algebra S R] :
    IsScalarTower S R (IsRestricted.subring (R := R) c) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- The coefficient algebra map into restricted series is the constant-series embedding. -/
@[simp]
theorem coe_algebraMap_isRestrictedSubring (r : R) :
    (algebraMap R (IsRestricted.subring (R := R) c) r : MvPowerSeries σ R) = C r := (rfl)

/-- Without variables every restricted series is a constant. -/
theorem algebraMap_isRestrictedSubring_surjective [IsEmpty σ] :
    Function.Surjective (algebraMap R (IsRestricted.subring (R := R) c)) := fun g ↦
  let ⟨r, hr⟩ := C_surjective (g : MvPowerSeries σ R)
  ⟨r, Subtype.ext hr⟩

/-- A restricted monomial `r Xᵗ` is the constant `r` times the monomial `Xᵗ` in the variables. -/
theorem mk_monomial_eq_algebraMap_mul_prod (t : σ →₀ ℕ) (r : R) :
    (⟨monomial t r, isRestricted_monomial c t r⟩ : IsRestricted.subring (R := R) c) =
      algebraMap R _ r * t.prod fun i k ↦
        (⟨X i, isRestricted_monomial c (Finsupp.single i 1) 1⟩ :
          IsRestricted.subring (R := R) c) ^ k := by
  have h := map_finsuppProd (IsRestricted.subring (R := R) c).subtype t fun i k ↦
    (⟨X i, isRestricted_monomial c (Finsupp.single i 1) 1⟩ : IsRestricted.subring (R := R) c) ^ k
  simp only [Subring.coe_subtype, SubmonoidClass.coe_pow] at h
  apply Subtype.ext
  rw [Subring.coe_mul, h, coe_algebraMap_isRestrictedSubring]
  exact monomial_eq' t r

variable [∀ i, Fact (0 < c i)]

/-- Over a commutative coefficient ring, the Gauss norm gives a normed commutative ring. -/
noncomputable instance instNormedCommRingIsRestrictedSubring :
    NormedCommRing (IsRestricted.subring (R := R) c) :=
  { instNormedRingIsRestrictedSubring with mul_comm := mul_comm }

/-- Constants retain their coefficient norm. -/
@[simp]
theorem norm_algebraMap_isRestrictedSubring (r : R) :
    ‖algebraMap R (IsRestricted.subring (R := R) c) r‖ = ‖r‖ := by
  have h : algebraMap R (IsRestricted.subring (R := R) c) r = ⟨C r, isRestricted_C c r⟩ :=
    Subtype.ext (coe_algebraMap_isRestrictedSubring r)
  rw [h, norm_C]

end NormedCommRing

section Rename

variable {σ τ R : Type*} [NormedCommRing R]

/-- **Restrictedness is invariant under renaming the variables.** Renaming along an equivalence
`e : σ ≃ τ` gives a series restricted at the polyradii `c` exactly when the original series is
restricted at the reindexed polyradii `c ∘ e`. -/
theorem isRestricted_renameEquiv_iff (e : σ ≃ τ) {c : τ → ℝ} {f : MvPowerSeries σ R} :
    IsRestricted c (renameEquiv R e f) ↔ IsRestricted (c ∘ e) f := by
  -- the weighted coefficients of `f` are those of the renamed series, reindexed along `e`
  have h : (fun t : σ →₀ ℕ ↦ ‖coeff t f‖ * t.prod ((c ∘ e) · ^ ·)) =
      (fun u : τ →₀ ℕ ↦ ‖coeff u (renameEquiv R e f)‖ * u.prod (c · ^ ·)) ∘
        Finsupp.equivCongrLeft e := by
    funext t
    have hc : coeff (t.equivMapDomain e) (rename e f) = coeff t f := by
      simpa [Finsupp.embDomain_eq_mapDomain, Finsupp.equivMapDomain_eq_mapDomain] using
        coeff_embDomain_rename e.toEmbedding f t
    simp [hc, Finsupp.prod_equivMapDomain]
  rw [IsRestricted, IsRestricted, h, ← (Finsupp.equivCongrLeft e).injective.comap_cofinite_eq]
  exact (tendsto_comap'_iff (by rw [(Finsupp.equivCongrLeft e).range_eq_univ]; exact univ_mem)).symm

variable [IsUltrametricDist R]

/-- **Renaming the variables of restricted series.** Renaming along an equivalence `e : σ ≃ τ` is
an `R`-algebra isomorphism from the series restricted at the reindexed polyradii `c ∘ e` to the
series restricted at `c`. -/
noncomputable def IsRestricted.renameAlgEquiv (e : σ ≃ τ) (c : τ → ℝ) :
    IsRestricted.subring (R := R) (c ∘ e) ≃ₐ[R] IsRestricted.subring (R := R) c :=
  AlgEquiv.ofRingEquiv (f := (renameEquiv R e).toRingEquiv.restrict _ _ fun _ ↦
    (isRestricted_renameEquiv_iff e).symm) fun r ↦ Subtype.ext (rename_C _ r)

/-- The renaming isomorphism of restricted series is `MvPowerSeries.renameEquiv` on the
underlying series. -/
@[simp]
theorem IsRestricted.coe_renameAlgEquiv (e : σ ≃ τ) (c : τ → ℝ)
    (f : IsRestricted.subring (R := R) (c ∘ e)) :
    (renameAlgEquiv e c f : MvPowerSeries τ R) = renameEquiv R e f := (rfl)

end Rename

end MvPowerSeries

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

section Algebra

variable {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R] {c : σ → ℝ}

/-- Over an algebra `S` of coefficients, the algebra map into restricted series sends a scalar to
the constant series of its image in `R`. -/
theorem coe_algebraMap_isRestrictedSubring_apply {S : Type*} [CommSemiring S] [Algebra S R]
    (s : S) : (algebraMap S (IsRestricted.subring (R := R) c) s : MvPowerSeries σ R) =
      C (algebraMap S R s) := (rfl)

/-- Over an algebra `S` of coefficients, scalars act on restricted series coefficientwise. -/
@[simp]
theorem coe_smul_isRestrictedSubring {S : Type*} [CommSemiring S] [Algebra S R] (s : S)
    (f : IsRestricted.subring (R := R) c) :
    ((s • f : IsRestricted.subring (R := R) c) : MvPowerSeries σ R) =
      s • (f : MvPowerSeries σ R) := by
  ext t
  rw [Algebra.smul_def, Subring.coe_mul, coe_algebraMap_isRestrictedSubring_apply, coeff_C_mul]
  exact (Algebra.smul_def s _).symm

end Algebra

section NormedField

variable {σ K R : Type*} [NormedField K] [NormedCommRing R] [NormedAlgebra K R]
  [IsUltrametricDist R] {c : σ → ℝ} [∀ i, Fact (0 < c i)]

/-- At positive polyradii, restricted series over a normed algebra `R` over a normed field `K`
form a normed `K`-algebra: scalars act coefficientwise. In particular, restricted series form a
normed algebra over an ultrametric coefficient field. -/
noncomputable instance instNormedAlgebraIsRestrictedSubring :
    NormedAlgebra K (IsRestricted.subring (R := R) c) where
  toAlgebra := instAlgebraIsRestrictedSubring
  norm_smul_le r f := by
    refine (norm_le_iff (by positivity)).mpr fun t ↦ ?_
    rw [coe_smul_isRestrictedSubring]
    calc ‖r • coeff t (f : MvPowerSeries σ R)‖ * t.prod (c · ^ ·)
        ≤ ‖r‖ * (‖coeff t (f : MvPowerSeries σ R)‖ * t.prod (c · ^ ·)) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (norm_smul_le r _) (prod_pow_pos t).le
      _ ≤ ‖r‖ * ‖f‖ := mul_le_mul_of_nonneg_left (norm_coeff_mul_prod_le f t) (norm_nonneg r)

end NormedField

end TauCeti.MvPowerSeries
