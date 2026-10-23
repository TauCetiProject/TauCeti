/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import TauCeti.NumberTheory.NewtonPolygon.Basic
public import TauCeti.RingTheory.PowerSeries.GaussNorm

/-!
# Gauss norms and Newton supporting values

Fix a real additive valuation `v` and a base `b > 1` with
`‖x‖ = b ^ (-(v x).untop₀)` for nonzero `x`. At radius `b ^ σ`, an upper bound
`b ^ (-c)` on weighted coefficient norms is exactly an affine lower bound with
intercept `c` and slope `σ` on coefficient heights. Thus boundedness of these
norms is equivalent to the supporting value being above negative infinity.
For a nonzero series with bounded weighted coefficients, the supporting value
is `-Real.logb b` of the Gauss norm.

Coefficient heights are admissible exactly when the series is restricted at
some positive radius. Boundedness at one radius gives restrictedness at every
strictly smaller positive radius; restrictedness at the original radius is not
needed for the supporting-value identity. The zero series is included in the
admissibility criterion but excluded from the logarithmic identity.

The norm and valuation are compared by an explicit hypothesis, so no choice of
normalisation is hidden in a typeclass instance. These comparisons identify the
convex supporting-line description with the analytic Gauss norm.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §§3–4.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1. Our positive abscissae give
  slope `σ` at radius `b ^ σ`.
-/

public section

open TauCeti

namespace PowerSeries

variable {K : Type*} [NormedDivisionRing K] (f : PowerSeries K)
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))

include hb hv

/-- At a nonzero coefficient, the weighted norm is the exponential of the negative
tilted coefficient height. -/
theorem norm_coeff_mul_rpow_eq (n : ℕ) (σ : ℝ) (hn : f.coeff n ≠ 0) :
    ‖f.coeff n‖ * (b ^ σ) ^ n = b ^ (-((v (f.coeff n)).untop₀ - σ * n)) := by
  rw [hv _ hn, ← Real.rpow_mul_natCast (le_of_lt (lt_trans zero_lt_one hb)),
    ← Real.rpow_add (lt_trans zero_lt_one hb)]
  congr 1
  ring

/-- An exponential upper bound on one weighted coefficient norm is equivalent to an
affine lower bound on its valuation. A zero coefficient satisfies both bounds. -/
theorem norm_coeff_mul_rpow_le_iff (n : ℕ) (σ c : ℝ) :
    ‖f.coeff n‖ * (b ^ σ) ^ n ≤ b ^ (-c) ↔
      ((c + σ * n : ℝ) : WithTop ℝ) ≤ v (f.coeff n) := by
  by_cases hn : f.coeff n = 0
  · simp [hn, (Real.rpow_pos_of_pos (lt_trans zero_lt_one hb) (-c)).le]
  · rw [norm_coeff_mul_rpow_eq f v hb hv n σ hn,
      Real.rpow_le_rpow_left_iff hb,
      ← WithTop.coe_untop₀_of_ne_top ((v.ne_top_iff).mpr hn), WithTop.coe_le_coe,
      WithTop.untop₀_coe]
    constructor <;> intro h <;> linarith

/-- A real intercept lies below the supporting value exactly when its exponential
bounds all weighted coefficient norms. No boundedness assumption is needed. -/
theorem coe_le_supportingValue_coeff_iff (σ c : ℝ) :
    (c : EReal) ≤ supportingValue (fun n => v (f.coeff n)) σ ↔
      ∀ n, ‖f.coeff n‖ * (b ^ σ) ^ n ≤ b ^ (-c) := by
  rw [coe_le_supportingValue_iff]
  exact forall_congr' fun n => (norm_coeff_mul_rpow_le_iff f v hb hv n σ c).symm

/-- Bounded weighted coefficient norms are equivalent to a supporting value above
negative infinity, including for the zero series. This is weaker than restrictedness. -/
theorem hasGaussNorm_iff_supportingValue_ne_bot (σ : ℝ) :
    f.HasGaussNorm norm (b ^ σ) ↔
      supportingValue (fun n => v (f.coeff n)) σ ≠ ⊥ := by
  constructor
  · rintro ⟨B, hB⟩
    have hBpos : 0 < max B 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    apply ne_bot_of_le_ne_bot (EReal.coe_ne_bot (-Real.logb b (max B 1)))
    apply (coe_le_supportingValue_coeff_iff f v hb hv σ _).mpr
    intro n
    rw [neg_neg, Real.rpow_logb (lt_trans zero_lt_one hb) (ne_of_gt hb) hBpos]
    exact (hB ⟨n, rfl⟩).trans (le_max_left _ _)
  · intro h
    obtain ⟨c, hc⟩ := supportingValue_ne_bot_iff.mp h
    refine ⟨b ^ (-c), ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (norm_coeff_mul_rpow_le_iff f v hb hv n σ c).mpr (hc n)

/-- For bounded weighted coefficients, real lower bounds on the supporting value
correspond to exponential upper bounds on the Gauss norm. -/
theorem coe_le_supportingValue_coeff_iff_gaussNorm_le (σ c : ℝ)
    (hf : f.HasGaussNorm norm (b ^ σ)) :
    (c : EReal) ≤ supportingValue (fun n => v (f.coeff n)) σ ↔
      f.gaussNorm norm (b ^ σ) ≤ b ^ (-c) := by
  rw [coe_le_supportingValue_coeff_iff f v hb hv, gaussNorm_eq, ciSup_le_iff hf]

/-- Admissible coefficient heights are exactly the series restricted at some positive
radius. An affine lower bound suffices because one may decrease its associated radius. -/
theorem isAdmissible_addValuation_coeff_iff_exists_isRestricted :
    IsAdmissible (fun n => v (f.coeff n)) ↔ ∃ r : ℝ, 0 < r ∧ f.IsRestricted r := by
  rw [isAdmissible_iff_exists_supportingValue_ne_bot]
  constructor
  · rintro ⟨σ, hσ⟩
    have hr : 0 < b ^ σ := Real.rpow_pos_of_pos (lt_trans zero_lt_one hb) σ
    refine ⟨b ^ σ / 2, by positivity, ?_⟩
    apply ((hasGaussNorm_iff_supportingValue_ne_bot f v hb hv σ).mpr hσ).isRestricted_of_abs_lt
    rw [abs_of_pos (by positivity : 0 < b ^ σ / 2)]
    linarith
  · rintro ⟨r, hr, hf⟩
    refine ⟨Real.logb b r, (hasGaussNorm_iff_supportingValue_ne_bot f v hb hv _).mp ?_⟩
    rw [Real.rpow_logb (lt_trans zero_lt_one hb) (ne_of_gt hb) hr]
    exact TauCeti.PowerSeries.hasGaussNorm_of_isRestricted hf

/-- For a nonzero series with bounded weighted coefficient norms, its supporting value
is the negative base-`b` logarithm of its Gauss norm. No attainment is assumed. -/
theorem supportingValue_coeff_eq_neg_logb_gaussNorm (σ : ℝ)
    (hf : f.HasGaussNorm norm (b ^ σ)) (hf0 : f ≠ 0) :
    supportingValue (fun n => v (f.coeff n)) σ =
      ((-Real.logb b (f.gaussNorm norm (b ^ σ)) : ℝ) : EReal) := by
  have hbpos : 0 < b := lt_trans zero_lt_one hb
  have hGpos : 0 < f.gaussNorm norm (b ^ σ) := by
    apply lt_of_le_of_ne (gaussNorm_nonneg norm _ f norm_nonneg)
    exact Ne.symm ((gaussNorm_eq_zero_iff norm _ f norm_zero norm_nonneg
      (fun x hx => norm_eq_zero.mp hx) (Real.rpow_pos_of_pos hbpos σ) hf).not.mpr hf0)
  have hpow : b ^ (-(-Real.logb b (f.gaussNorm norm (b ^ σ)))) =
      f.gaussNorm norm (b ^ σ) := by
    rw [neg_neg, Real.rpow_logb hbpos (ne_of_gt hb) hGpos]
  apply le_antisymm
  · by_contra h
    obtain ⟨c, hc, hc'⟩ := EReal.exists_between_coe_real (lt_of_not_ge h)
    have hbound := (coe_le_supportingValue_coeff_iff_gaussNorm_le f v hb hv σ c hf).mp hc'.le
    have hlt : b ^ (-c) < f.gaussNorm norm (b ^ σ) := by
      rw [← hpow, Real.rpow_lt_rpow_left_iff hb]
      exact neg_lt_neg (EReal.coe_lt_coe_iff.mp hc)
    exact (not_lt_of_ge hbound) hlt
  · apply (coe_le_supportingValue_coeff_iff_gaussNorm_le f v hb hv σ _ hf).mpr
    exact hpow.ge

/-- The Newton polygon of a nonzero series with bounded weighted coefficients has
supporting value equal to the negative logarithm of the Gauss norm. Boundedness at
this radius already guarantees an admissible polygon. -/
theorem supportingValue_newtonPolygon_eq_neg_logb_gaussNorm (σ : ℝ)
    (hf : f.HasGaussNorm norm (b ^ σ)) (hf0 : f ≠ 0) :
    supportingValue (f.newtonPolygon v) σ =
      ((-Real.logb b (f.gaussNorm norm (b ^ σ)) : ℝ) : EReal) := by
  have ha : IsAdmissible (fun n => v (f.coeff n)) :=
    isAdmissible_iff_exists_supportingValue_ne_bot.mpr
      ⟨σ, (hasGaussNorm_iff_supportingValue_ne_bot f v hb hv σ).mp hf⟩
  rw [supportingValue_newtonPolygon ha]
  exact supportingValue_coeff_eq_neg_logb_gaussNorm f v hb hv σ hf hf0

end PowerSeries
