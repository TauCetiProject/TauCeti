/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Restricted
public import Mathlib.RingTheory.MvPowerSeries.GaussNorm
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Finsupp.MonomialOrder
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

* `MvPowerSeries.norm_eq_gaussNorm`: the norm is the Gauss norm at the chosen polyradii.
* `MvPowerSeries.norm_le_iff`: a norm bound is equivalent to bounds on every weighted coefficient.
* `MvPowerSeries.exists_achievesGaussNorm` and `MvPowerSeries.exists_norm_coeff_mul_prod_gap`: a
  restricted series attains its norm, and its smaller weighted coefficient norms stay below a
  constant smaller than its norm.
* The restricted-series subring inherits `CompleteSpace`, `IsUltrametricDist`, and
  `NormMulClass` from its coefficient ring.
* Over a normed field, the restricted-series subring is a `NormedAlgebra` over its coefficients.

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

variable [IsUltrametricDist R] {c : σ → ℝ} [hc : ∀ i, Fact (0 < c i)]

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

/-- A nonnegative bound on the norm is exactly a bound on every weighted coefficient norm. -/
theorem norm_le_iff {f : IsRestricted.subring (R := R) c} {r : ℝ}
    (hr : 0 ≤ r) : ‖f‖ ≤ r ↔ ∀ t, ‖coeff t (f : MvPowerSeries σ R)‖ * t.prod (c · ^ ·) ≤ r := by
  refine ⟨fun h t ↦ (norm_coeff_mul_prod_le f t).trans h, fun h ↦ ?_⟩
  rw [norm_eq_gaussNorm, gaussNorm]
  exact Real.iSup_le (by simpa using h) hr

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

/-- The norm of a restricted monomial is its weighted coefficient norm. -/
@[simp]
theorem norm_monomial (t : σ →₀ ℕ) (a : R) :
    ‖(⟨monomial t a, isRestricted_monomial _ t a⟩ :
      IsRestricted.subring (R := R) c)‖ = ‖a‖ * t.prod (c · ^ ·) := by
  classical
  have hwpos (t : σ →₀ ℕ) : 0 < t.prod (c · ^ ·) :=
    Finset.prod_pos fun i _ ↦ pow_pos (hc i).out _
  apply le_antisymm
  · rw [norm_le_iff (mul_nonneg (norm_nonneg a) (hwpos t).le)]
    intro s
    by_cases h : s = t <;>
      simp [coeff_monomial, h, mul_nonneg (norm_nonneg a) (hwpos t).le]
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
  have hwpos (t : σ →₀ ℕ) : 0 < t.prod (c · ^ ·) :=
    Finset.prod_pos fun i _ ↦ pow_pos (hc i).out _
  refine Metric.complete_of_cauchySeq_tendsto fun F hF ↦ ?_
  have hcoeff (t : σ →₀ ℕ) : CauchySeq fun k ↦ coeff t (F k : MvPowerSeries σ R) := by
    let coeffHom : IsRestricted.subring (R := R) c →+ R :=
      (coeff t).toAddMonoidHom.comp
        (IsRestricted.subring (R := R) c).subtype.toAddMonoidHom
    refine (AddMonoidHomClass.uniformContinuous_of_bound coeffHom (t.prod (c · ^ ·))⁻¹
      fun f ↦ ?_).comp_cauchySeq hF
    rw [← div_eq_inv_mul, le_div_iff₀ (hwpos t)]
    exact norm_coeff_mul_prod_le f t
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
      hb.trans_le (mul_nonneg (norm_nonneg _) (hwpos t).le), fun ε hε ↦ ?_⟩
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
                  (coeff t (F N : MvPowerSeries σ R)) (a t)) (hwpos t).le
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
/-- Select a largest exponent achieving the norm; all lexicographically larger ones are smaller
in weighted coefficient norm. This tie breaking isolates one product summand. -/
private theorem exists_gaussNorm_max [LinearOrder σ] {f : MvPowerSeries σ R}
    (hf : IsRestricted c f) (hf0 : f ≠ 0) :
    ∃ i, AchievesGaussNorm norm c f i ∧ ∀ t, toLex i < toLex t →
      ‖coeff t f‖ * t.prod (c · ^ ·) < gaussNorm norm c f := by
  classical
  have hwpos (t : σ →₀ ℕ) : 0 < t.prod (c · ^ ·) :=
    Finset.prod_pos fun i _ ↦ pow_pos (hc i).out _
  obtain ⟨i, hi⟩ := (ne_zero_iff_exists_coeff_ne_zero f).mp hf0
  let a : (σ →₀ ℕ) → ℝ := fun t ↦ ‖coeff t f‖ * t.prod (c · ^ ·)
  have hi_pos : 0 < a i := mul_pos (norm_pos_iff.mpr hi) (hwpos i)
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
  obtain ⟨n, hn, hnmax⟩ := T.exists_max_image toLex ⟨j, hj_mem⟩
  have hn_eq : a n = a j := (Finset.mem_filter.mp hn).2
  refine ⟨n, hn_eq.trans heq, fun t ht ↦ ?_⟩
  rw [← heq]
  refine lt_of_le_of_ne (hbound t) fun h ↦ ?_
  have ht_mem : t ∈ T := by
    simp only [T, Finset.mem_filter]
    exact ⟨by simpa [S] using (hmax i hi_mem).trans_eq h.symm, h⟩
  exact (not_le_of_gt ht) (hnmax t ht_mem)

/-- The Gauss norm of a product of restricted series is the product of their Gauss norms when
the coefficient norm is multiplicative. Positive polyradii are arbitrary. -/
theorem IsRestricted.gaussNorm_mul [NormMulClass R] {f g : MvPowerSeries σ R}
    (hf : IsRestricted c f) (hg : IsRestricted c g) :
    gaussNorm norm c (f * g) = gaussNorm norm c f * gaussNorm norm c g := by
  classical
  have hwpos (t : σ →₀ ℕ) : 0 < t.prod (c · ^ ·) :=
    Finset.prod_pos fun i _ ↦ pow_pos (hc i).out _
  by_cases hf0 : f = 0
  · simp [hf0, gaussNorm_zero (R := R) norm c norm_zero]
  by_cases hg0 : g = 0
  · simp [hg0, gaussNorm_zero (R := R) norm c norm_zero]
  -- Choose lexicographically largest norm-achieving exponents. The order is only proof data.
  let : LinearOrder σ := linearOrderOfSTO WellOrderingRel
  obtain ⟨i, hi, himax⟩ := exists_gaussNorm_max hf hf0
  obtain ⟨j, hj, hjmax⟩ := exists_gaussNorm_max hg hg0
  have hfp : 0 < gaussNorm norm c f := by
    rw [← norm_eq_gaussNorm (⟨f, hf⟩ : IsRestricted.subring c)]
    exact norm_pos_iff.mpr fun h ↦ hf0 (congrArg Subtype.val h)
  have hgp : 0 < gaussNorm norm c g := by
    rw [← norm_eq_gaussNorm (⟨g, hg⟩ : IsRestricted.subring c)]
    exact norm_pos_iff.mpr fun h ↦ hg0 (congrArg Subtype.val h)
  refine gaussNorm_mul_eq_mul norm c f g hf.hasGaussNorm hg.hasGaussNorm
    (isRestricted.mul c hf hg).hasGaussNorm norm_nonneg norm_zero
    IsUltrametricDist.isNonarchimedean_norm norm_mul norm_neg
    (fun _ ↦ norm_eq_zero.mp) (fun i ↦ (hc i).out) ⟨i, j, hi, hj, ?_⟩
  intro p hp hne
  have hp' : p.1 + p.2 = i + j := Finset.mem_antidiagonal.mp hp
  -- Every summand at this exponent has the same positive weight.
  have hweight : p.1.prod (c · ^ ·) * p.2.prod (c · ^ ·) =
      i.prod (c · ^ ·) * j.prod (c · ^ ·) := by
    simpa [Finsupp.prod_add_index', pow_add] using
      congrArg (fun t ↦ t.prod (c · ^ ·)) hp'
  -- A different pair forces one exponent beyond the chosen maximal norm achiever.
  have hlt : (‖coeff p.1 f‖ * p.1.prod (c · ^ ·)) *
      (‖coeff p.2 g‖ * p.2.prod (c · ^ ·)) < gaussNorm norm c f * gaussNorm norm c g := by
    rcases trichotomy_of_add_eq_add (α := Lex (σ →₀ ℕ)) (congrArg toLex hp') with h | h | h
    · exact False.elim (hne (Prod.ext (toLex.injective h.1) (toLex.injective h.2)))
    · have hp2 : toLex j < toLex p.2 := by
        have heq : toLex p.1 + toLex p.2 = toLex i + toLex j := congrArg toLex hp'
        exact lt_of_add_lt_add_left (α := Lex (σ →₀ ℕ))
          (heq ▸ add_lt_add_left (α := Lex (σ →₀ ℕ)) h (toLex p.2))
      exact mul_lt_mul' (le_gaussNorm norm c f hf.hasGaussNorm p.1)
        (hjmax p.2 hp2) (mul_nonneg (norm_nonneg _) (hwpos _).le) hfp
    · have hp1 : toLex i < toLex p.1 := by
        have heq : toLex p.1 + toLex p.2 = toLex i + toLex j := congrArg toLex hp'
        exact lt_of_add_lt_add_right (α := Lex (σ →₀ ℕ))
          (heq ▸ add_lt_add_right (α := Lex (σ →₀ ℕ)) h (toLex p.1))
      simpa only [mul_comm] using
        mul_lt_mul' (le_gaussNorm norm c g hg.hasGaussNorm p.2) (himax p.1 hp1)
          (mul_nonneg (norm_nonneg _) (hwpos _).le) hgp
  rw [← hi, ← hj] at hlt
  -- Cancel the common positive weight to apply the dominant-antidiagonal theorem.
  have hlt' : ‖coeff p.1 f‖ * ‖coeff p.2 g‖ < ‖coeff i f‖ * ‖coeff j g‖ := by
    apply (mul_lt_mul_iff_of_pos_right (mul_pos (hwpos i) (hwpos j))).mp
    calc
      _ = (‖coeff p.1 f‖ * p.1.prod (c · ^ ·)) *
          (‖coeff p.2 g‖ * p.2.prod (c · ^ ·)) := by rw [← hweight]; ring
      _ < (‖coeff i f‖ * i.prod (c · ^ ·)) *
          (‖coeff j g‖ * j.prod (c · ^ ·)) := hlt
      _ = _ := by ring
  simpa only [norm_mul] using hlt'

/-- The Gauss norm inherits multiplicativity from the coefficient norm. -/
instance [NormMulClass R] : NormMulClass (IsRestricted.subring (R := R) c) where
  norm_mul f g := f.2.gaussNorm_mul g.2

end NormedRing

section NormedCommRing

variable {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R] {c : σ → ℝ}

/-- Restricted series form a coefficient algebra via the constant-series embedding. -/
noncomputable instance instAlgebraIsRestrictedSubring :
    Algebra R (IsRestricted.subring (R := R) c) :=
  (C.codRestrict _ (isRestricted_C c)).toAlgebra

/-- The coefficient algebra map into restricted series is the constant-series embedding. -/
@[simp]
theorem coe_algebraMap_isRestrictedSubring (r : R) :
    (algebraMap R (IsRestricted.subring (R := R) c) r : MvPowerSeries σ R) = C r := (rfl)

variable [∀ i, Fact (0 < c i)]

/-- Over a commutative coefficient ring, the Gauss norm gives a normed commutative ring. -/
noncomputable instance instNormedCommRingIsRestrictedSubring :
    NormedCommRing (IsRestricted.subring (R := R) c) :=
  { instNormedRingIsRestrictedSubring with mul_comm := mul_comm }

end NormedCommRing

section NormedField

variable {σ R : Type*} [NormedField R] [IsUltrametricDist R] {c : σ → ℝ}
  [∀ i, Fact (0 < c i)]

/-- At positive polyradii, restricted series form a normed algebra over their ultrametric
coefficient field. -/
noncomputable instance instNormedAlgebraIsRestrictedSubring :
    NormedAlgebra R (IsRestricted.subring (R := R) c) where
  toAlgebra := instAlgebraIsRestrictedSubring
  norm_smul_le r f := by
    rw [Algebra.smul_def]
    have h : algebraMap R (IsRestricted.subring (R := R) c) r =
        ⟨C r, isRestricted_C c r⟩ := Subtype.ext (coe_algebraMap_isRestrictedSubring r)
    rw [h]
    simpa only [norm_C] using
      norm_mul_le (⟨C r, isRestricted_C c r⟩ : IsRestricted.subring (R := R) c) f

end NormedField

end MvPowerSeries
