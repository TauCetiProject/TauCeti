/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import TauCeti.Analysis.Convex.Sequence.Face
public import TauCeti.NumberTheory.NewtonPolygon.Slopes
public import TauCeti.RingTheory.PowerSeries.GaussNorm

/-!
# Gauss norms and Newton supporting values

Fix a real additive valuation `v` on a normed division ring and a base `b > 1` with
`‖x‖ = b ^ (-(v x).untop₀)` for nonzero `x`. At the radius `b ^ σ` the weighted coefficient
norm `‖aₙ‖ (b ^ σ) ^ n` is `b ^ (-(v aₙ - σ n))`, the exponential of the negated tilted
coefficient height. Consequently an upper bound `b ^ (-c)` on all weighted coefficient norms is
exactly an affine line of slope `σ` and intercept `c` supporting the coefficient heights, and
a weighted coefficient norm equals `b ^ (-c)` exactly when the coefficient lies on that line.

This identifies the analytic Gauss norm with the convex supporting-line description:

* the weighted coefficient norms are bounded exactly when the supporting value at `σ` is above
  negative infinity, and coefficient heights are admissible exactly when the series is
  restricted at some positive radius;
* for a nonzero series with bounded weighted coefficient norms, the supporting value of its
  coefficient heights, and of its Newton polygon, is `-Real.logb b` of its Gauss norm;
* the coefficients attaining the Gauss norm are exactly the contact points of the supporting
  line of slope `σ`, so the last and the first of them, `TauCeti.PowerSeries.IsDistinguished`
  and `TauCeti.PowerSeries.IsLowestDominant`, are the greatest and least contact indices.

Neither attainment nor restrictedness at the given radius is assumed: at the boundary of
convergence the Gauss norm is still the supporting value, while it need not be attained.
For polynomials the identities hold at every radius, and the purity criterion
`Polynomial.forall_mem_newtonSlopes_eq_iff` becomes a statement about weighted norms: every
finite slope equals `m` exactly when, at the radius `b ^ m`, the weighted leading and trailing
terms have equal norms and bound all other weighted terms. The norm and valuation are compared by
an explicit hypothesis, so no normalisation is hidden in a typeclass instance.

## Main results

* `PowerSeries.isSupportingLine_addValuation_coeff_iff`: affine minorants of the coefficient
  heights are exponential bounds on the weighted coefficient norms.
* `PowerSeries.hasGaussNorm_iff_supportingValue_ne_bot`: bounded weighted coefficient norms
  correspond to a supporting value above negative infinity.
* `PowerSeries.isAdmissible_addValuation_coeff_iff_exists_isRestricted`: coefficient heights
  are admissible exactly when the series is restricted at some positive radius.
* `PowerSeries.supportingValue_newtonPolygon_eq_neg_logb_gaussNorm`: the supporting value of
  the Newton polygon is the negative logarithm of the Gauss norm, with the polynomial case
  `Polynomial.supportingValue_newtonPolygon_eq_neg_logb_gaussNorm` at every radius.
* `Polynomial.forall_mem_newtonSlopes_eq_iff_norm_coeff_mul_rpow_pow_le`: the purity criterion
  in terms of weighted coefficient norms at the radius `b ^ m`.
* `PowerSeries.mem_supportingFace_addValuation_coeff_iff`: the contact indices of the
  supporting line are the indices attaining the Gauss norm.
* `PowerSeries.isDistinguished_iff_isGreatest_supportingFace` and
  `PowerSeries.isLowestDominant_iff_isLeast_supportingFace`: the last and the first coefficient
  attaining the Gauss norm are the greatest and least contact indices.
* `PowerSeries.exists_isSupportingLine_mem_supportingFace_of_isRestricted`: the coefficient
  heights of a nonzero series restricted at `b ^ σ` touch a supporting line of slope `σ`.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §§3–4.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1. Lazard's variable is a valuation
  threshold, corresponding to `-σ` here.
-/

public section

open TauCeti

namespace PowerSeries

variable {K : Type*} [NormedDivisionRing K] (f : PowerSeries K)
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))

include hb hv

/-- At a nonzero coefficient, the weighted norm is the exponential of the negated tilted
coefficient height. -/
theorem norm_coeff_mul_rpow_pow_eq {n : ℕ} (hn : f.coeff n ≠ 0) (σ : ℝ) :
    ‖f.coeff n‖ * (b ^ σ) ^ n = b ^ (-((v (f.coeff n)).untop₀ - σ * n)) := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  rw [hv _ hn, ← Real.rpow_mul_natCast hb0.le, ← Real.rpow_add hb0]
  ring_nf

/-- An exponential upper bound on one weighted coefficient norm is an affine lower bound on
the height of that coefficient. A zero coefficient satisfies both bounds. -/
theorem norm_coeff_mul_rpow_pow_le_iff (n : ℕ) (σ c : ℝ) :
    ‖f.coeff n‖ * (b ^ σ) ^ n ≤ b ^ (-c) ↔
      ((c + σ * n : ℝ) : WithTop ℝ) ≤ v (f.coeff n) := by
  by_cases hn : f.coeff n = 0
  · simp [hn, (Real.rpow_pos_of_pos (zero_lt_one.trans hb) (-c)).le]
  rw [norm_coeff_mul_rpow_pow_eq f v hb hv hn, Real.rpow_le_rpow_left_iff hb,
    ← WithTop.coe_untop₀_of_ne_top ((v.ne_top_iff).mpr hn), WithTop.coe_le_coe,
    WithTop.untop₀_coe]
  constructor <;> intro h <;> linarith

/-- A weighted coefficient norm equals `b ^ (-c)` exactly when the coefficient lies on the line
of slope `σ` and intercept `c`. A zero coefficient satisfies neither condition. -/
theorem norm_coeff_mul_rpow_pow_eq_iff (n : ℕ) (σ c : ℝ) :
    ‖f.coeff n‖ * (b ^ σ) ^ n = b ^ (-c) ↔
      v (f.coeff n) = ((c + σ * n : ℝ) : WithTop ℝ) := by
  by_cases hn : f.coeff n = 0
  · simp only [hn, norm_zero, zero_mul, AddValuation.map_zero, WithTop.top_ne_coe, iff_false]
    exact (Real.rpow_pos_of_pos (zero_lt_one.trans hb) (-c)).ne
  rw [norm_coeff_mul_rpow_pow_eq f v hb hv hn,
    Real.rpow_right_inj (zero_lt_one.trans hb) hb.ne',
    ← WithTop.coe_untop₀_of_ne_top ((v.ne_top_iff).mpr hn), WithTop.coe_eq_coe,
    WithTop.untop₀_coe]
  constructor <;> intro h <;> linarith

/-- A line of slope `σ` and intercept `c` supports the coefficient heights exactly when
`b ^ (-c)` bounds every weighted coefficient norm at the radius `b ^ σ`. No boundedness
assumption is needed. -/
theorem isSupportingLine_addValuation_coeff_iff (σ c : ℝ) :
    IsSupportingLine (fun n => v (f.coeff n)) σ c ↔
      ∀ n, ‖f.coeff n‖ * (b ^ σ) ^ n ≤ b ^ (-c) :=
  isSupportingLine_iff_forall.trans
    (forall_congr' fun n => (norm_coeff_mul_rpow_pow_le_iff f v hb hv n σ c).symm)

/-- Bounded weighted coefficient norms are equivalent to a supporting value above negative
infinity, including for the zero series. This is weaker than restrictedness. -/
theorem hasGaussNorm_iff_supportingValue_ne_bot (σ : ℝ) :
    f.HasGaussNorm norm (b ^ σ) ↔ supportingValue (fun n => v (f.coeff n)) σ ≠ ⊥ := by
  constructor
  · rintro ⟨B, hB⟩
    have hB1 : 0 < max B 1 := zero_lt_one.trans_le (le_max_right _ _)
    refine ne_bot_of_le_ne_bot (EReal.coe_ne_bot (-Real.logb b (max B 1)))
      (isSupportingLine_iff.mp ((isSupportingLine_addValuation_coeff_iff f v hb hv σ _).mpr
        fun n => ?_))
    rw [neg_neg, Real.rpow_logb (zero_lt_one.trans hb) hb.ne' hB1]
    exact (hB ⟨n, rfl⟩).trans (le_max_left _ _)
  · intro h
    obtain ⟨c, hc⟩ := supportingValue_ne_bot_iff.mp h
    exact ⟨b ^ (-c), by
      rintro _ ⟨n, rfl⟩
      exact (norm_coeff_mul_rpow_pow_le_iff f v hb hv n σ c).mpr (hc n)⟩

/-- For bounded weighted coefficient norms, a line of slope `σ` and intercept `c` supports the
coefficient heights exactly when `b ^ (-c)` bounds the Gauss norm at the radius `b ^ σ`. -/
theorem isSupportingLine_addValuation_coeff_iff_gaussNorm_le {σ : ℝ}
    (hf : f.HasGaussNorm norm (b ^ σ)) (c : ℝ) :
    IsSupportingLine (fun n => v (f.coeff n)) σ c ↔ f.gaussNorm norm (b ^ σ) ≤ b ^ (-c) := by
  rw [isSupportingLine_addValuation_coeff_iff f v hb hv, gaussNorm_eq, ciSup_le_iff hf]

/-- Coefficient heights are admissible exactly when the series is restricted at some positive
radius. This includes the zero series, whose heights are all infinite. -/
theorem isAdmissible_addValuation_coeff_iff_exists_isRestricted :
    IsAdmissible (fun n => v (f.coeff n)) ↔ ∃ r : ℝ, 0 < r ∧ f.IsRestricted r := by
  rw [isAdmissible_iff_exists_supportingValue_ne_bot]
  constructor
  · rintro ⟨σ, hσ⟩
    have hr : 0 < b ^ σ := Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ
    refine ⟨b ^ σ / 2, half_pos hr,
      ((hasGaussNorm_iff_supportingValue_ne_bot f v hb hv σ).mpr hσ).isRestricted_of_abs_lt ?_⟩
    rw [abs_of_pos (half_pos hr)]
    exact half_lt_self hr
  · rintro ⟨r, hr, hf⟩
    refine ⟨Real.logb b r, (hasGaussNorm_iff_supportingValue_ne_bot f v hb hv _).mp ?_⟩
    rw [Real.rpow_logb (zero_lt_one.trans hb) hb.ne' hr]
    exact TauCeti.PowerSeries.hasGaussNorm_of_isRestricted hf

/-- For a nonzero series with bounded weighted coefficient norms, the supporting value of its
coefficient heights is the negative base-`b` logarithm of its Gauss norm. The Gauss norm need
not be attained. -/
theorem supportingValue_addValuation_coeff_eq_neg_logb_gaussNorm {σ : ℝ}
    (hf : f.HasGaussNorm norm (b ^ σ)) (hf0 : f ≠ 0) :
    supportingValue (fun n => v (f.coeff n)) σ =
      ((-Real.logb b (f.gaussNorm norm (b ^ σ)) : ℝ) : EReal) := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hpow : b ^ (-(-Real.logb b (f.gaussNorm norm (b ^ σ)))) = f.gaussNorm norm (b ^ σ) := by
    rw [neg_neg, Real.rpow_logb hb0 hb.ne'
      (TauCeti.PowerSeries.gaussNorm_pos (Real.rpow_pos_of_pos hb0 σ) hf hf0)]
  refine le_antisymm ?_ (isSupportingLine_iff.mp
    ((isSupportingLine_addValuation_coeff_iff_gaussNorm_le f v hb hv hf _).mpr hpow.ge))
  by_contra h
  obtain ⟨c, hc, hc'⟩ := EReal.exists_between_coe_real (lt_of_not_ge h)
  have hle := (isSupportingLine_addValuation_coeff_iff_gaussNorm_le f v hb hv hf c).mp
    (isSupportingLine_iff.mpr hc'.le)
  rw [← hpow, Real.rpow_le_rpow_left_iff hb, neg_le_neg_iff] at hle
  exact (EReal.coe_lt_coe_iff.mp hc).not_ge hle

/-- The Newton polygon of a nonzero series with bounded weighted coefficient norms has
supporting value equal to the negative base-`b` logarithm of the Gauss norm. Boundedness at
this radius already makes the coefficient heights admissible. -/
theorem supportingValue_newtonPolygon_eq_neg_logb_gaussNorm {σ : ℝ}
    (hf : f.HasGaussNorm norm (b ^ σ)) (hf0 : f ≠ 0) :
    supportingValue (f.newtonPolygon v) σ =
      ((-Real.logb b (f.gaussNorm norm (b ^ σ)) : ℝ) : EReal) := by
  rw [supportingValue_newtonPolygon (isAdmissible_iff_exists_supportingValue_ne_bot.mpr
    ⟨σ, (hasGaussNorm_iff_supportingValue_ne_bot f v hb hv σ).mp hf⟩)]
  exact supportingValue_addValuation_coeff_eq_neg_logb_gaussNorm f v hb hv hf hf0

/-- For a nonzero series with bounded weighted coefficient norms, the coefficients touching the
supporting line of slope `σ` are exactly those attaining the Gauss norm at the radius
`b ^ σ`. The intercept of that line is the supporting value
`-Real.logb b (f.gaussNorm norm (b ^ σ))`. -/
theorem mem_supportingFace_addValuation_coeff_iff {σ : ℝ}
    (hf : f.HasGaussNorm norm (b ^ σ)) (hf0 : f ≠ 0) (n : ℕ) :
    n ∈ supportingFace (fun n => v (f.coeff n)) σ (-Real.logb b (f.gaussNorm norm (b ^ σ))) ↔
      ‖f.coeff n‖ * (b ^ σ) ^ n = f.gaussNorm norm (b ^ σ) := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  rw [mem_supportingFace, ← norm_coeff_mul_rpow_pow_eq_iff f v hb hv, neg_neg,
    Real.rpow_logb hb0 hb.ne'
      (TauCeti.PowerSeries.gaussNorm_pos (Real.rpow_pos_of_pos hb0 σ) hf hf0)]

/-- The distinguished degree at the radius `b ^ σ`, the last index attaining the Gauss norm, is
the greatest contact index of the supporting line of slope `σ` with the coefficient heights. -/
theorem isDistinguished_iff_isGreatest_supportingFace {σ : ℝ}
    (hf : f.HasGaussNorm norm (b ^ σ)) (hf0 : f ≠ 0) (s : ℕ) :
    TauCeti.PowerSeries.IsDistinguished (b ^ σ) s f ↔
      IsGreatest (supportingFace (fun n => v (f.coeff n)) σ
        (-Real.logb b (f.gaussNorm norm (b ^ σ)))) s := by
  simp only [IsGreatest, mem_upperBounds,
    mem_supportingFace_addValuation_coeff_iff f v hb hv hf hf0]
  refine ⟨fun hs => ⟨hs.norm_coeff_mul_pow_eq, fun m hm => not_lt.mp fun hsm =>
    (hs.norm_coeff_mul_pow_lt m hsm).ne hm⟩, fun hs => ⟨hs.1, fun m hsm => ?_⟩⟩
  exact (le_gaussNorm norm _ f hf m).lt_of_ne fun hm => (hs.2 m hm).not_gt hsm

/-- The lowest dominant degree at the radius `b ^ σ`, the first index attaining the Gauss norm,
is the least contact index of the supporting line of slope `σ` with the coefficient heights. -/
theorem isLowestDominant_iff_isLeast_supportingFace {σ : ℝ}
    (hf : f.HasGaussNorm norm (b ^ σ)) (hf0 : f ≠ 0) (s : ℕ) :
    TauCeti.PowerSeries.IsLowestDominant (b ^ σ) s f ↔
      IsLeast (supportingFace (fun n => v (f.coeff n)) σ
        (-Real.logb b (f.gaussNorm norm (b ^ σ)))) s := by
  simp only [IsLeast, mem_lowerBounds,
    mem_supportingFace_addValuation_coeff_iff f v hb hv hf hf0]
  refine ⟨fun hs => ⟨hs.norm_coeff_mul_pow_eq, fun m hm => not_lt.mp fun hms =>
    (hs.norm_coeff_mul_pow_lt m hms).ne hm⟩, fun hs => ⟨?_, hs.1, fun m hms => ?_⟩⟩
  · exact TauCeti.PowerSeries.gaussNorm_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ)
      hf hf0
  · exact (le_gaussNorm norm _ f hf m).lt_of_ne fun hm => (hs.2 m hm).not_gt hms

/-- The coefficient heights of a nonzero series restricted at the radius `b ^ σ` touch a
supporting line of slope `σ`. -/
theorem exists_isSupportingLine_mem_supportingFace_of_isRestricted {σ : ℝ}
    (hf : f.IsRestricted (b ^ σ)) (hf0 : f ≠ 0) :
    ∃ (c : ℝ) (i : ℕ), IsSupportingLine (fun n => v (coeff n f)) σ c ∧
      i ∈ supportingFace (fun n => v (coeff n f)) σ c := by
  have hfn := TauCeti.PowerSeries.hasGaussNorm_of_isRestricted hf
  obtain ⟨s, hs⟩ := TauCeti.PowerSeries.exists_isDistinguished
    (Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ) hf hf0
  exact ⟨_, s, isSupportingLine_iff.mpr
    (supportingValue_addValuation_coeff_eq_neg_logb_gaussNorm f v hb hv hfn hf0).ge,
    ((isDistinguished_iff_isGreatest_supportingFace f v hb hv hfn hf0 s).mp hs).1⟩

/-- A series restricted at the radius `b ^ σ` has a Newton polygon whose supporting value at `σ`
is above `⊥`. -/
theorem supportingValue_newtonPolygon_ne_bot_of_isRestricted {σ : ℝ}
    (hf : f.IsRestricted (b ^ σ)) : supportingValue (f.newtonPolygon v) σ ≠ ⊥ := by
  have h := (hasGaussNorm_iff_supportingValue_ne_bot f v hb hv σ).mp
    (TauCeti.PowerSeries.hasGaussNorm_of_isRestricted hf)
  rwa [supportingValue_newtonPolygon (isAdmissible_iff_exists_supportingValue_ne_bot.mpr ⟨σ, h⟩)]

end PowerSeries

namespace Polynomial

section SupportingValue

variable {K : Type*} [NormedDivisionRing K] (p : Polynomial K)
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))

include hb hv

/-- At every slope `σ`, the Newton polygon of a nonzero polynomial has supporting value equal
to the negative base-`b` logarithm of its Gauss norm at the radius `b ^ σ`. -/
theorem supportingValue_newtonPolygon_eq_neg_logb_gaussNorm (hp : p ≠ 0) (σ : ℝ) :
    supportingValue (p.newtonPolygon v) σ =
      ((-Real.logb b ((p : PowerSeries K).gaussNorm norm (b ^ σ)) : ℝ) : EReal) := by
  rw [← newtonPolygon_coe]
  exact PowerSeries.supportingValue_newtonPolygon_eq_neg_logb_gaussNorm _ v hb hv
    (TauCeti.PowerSeries.hasGaussNorm_of_isRestricted
      (TauCeti.PowerSeries.isRestricted_polynomial p))
    (Polynomial.coe_eq_zero_iff.not.mpr hp)

end SupportingValue

section Pure

variable {K : Type*} [NormedDivisionRing K] {v : AddValuation K (WithTop ℝ)} {b : ℝ}

/-- **Purity criterion, Gauss form.** Let the norm be `‖x‖ = b ^ (-v x)` for `x ≠ 0`, with
`1 < b`. Every finite slope of `f` equals `m` exactly when, at the radius `b ^ m`, the weighted
leading and trailing terms have the same norm and every weighted term has norm at most that of
the trailing term. -/
theorem forall_mem_newtonSlopes_eq_iff_norm_coeff_mul_rpow_pow_le (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) {f : K[X]} {m : ℝ} :
    (∀ s ∈ f.newtonSlopes v, s = m) ↔
      ‖f.leadingCoeff‖ * (b ^ m) ^ f.natDegree =
          ‖f.trailingCoeff‖ * (b ^ m) ^ f.natTrailingDegree ∧
        ∀ n, ‖f.coeff n‖ * (b ^ m) ^ n ≤ ‖f.trailingCoeff‖ * (b ^ m) ^ f.natTrailingDegree := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have hnorm {n : ℕ} (hn : f.coeff n ≠ 0) :
      ‖f.coeff n‖ * (b ^ m) ^ n = b ^ (-((v (f.coeff n)).untop₀ - m * n)) := by
    simpa using (f : PowerSeries K).norm_coeff_mul_rpow_pow_eq v hb hv (by simpa using hn) m
  rw [forall_mem_newtonSlopes_eq_iff (mt v.top_iff.mp (trailingCoeff_nonzero_iff_nonzero.mpr hf))
    (mt v.top_iff.mp (leadingCoeff_ne_zero.mpr hf)), ← coeff_natDegree, trailingCoeff,
    hnorm (coeff_natTrailingDegree_ne_zero.mpr hf),
    hnorm (by rw [coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hf),
    Real.rpow_right_inj (zero_lt_one.trans hb) hb.ne']
  refine and_congr ⟨fun h => by rw [h]; ring, fun h => by linarith⟩ (forall_congr' fun n => ?_)
  have hle := PowerSeries.norm_coeff_mul_rpow_pow_le_iff (f : PowerSeries K) v hb hv n m
    ((v (f.coeff f.natTrailingDegree)).untop₀ - m * f.natTrailingDegree)
  rw [coeff_coe] at hle
  rw [hle]
  convert Iff.rfl using 3
  ring

end Pure

end Polynomial
