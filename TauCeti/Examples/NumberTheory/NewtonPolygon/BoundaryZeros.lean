/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import TauCeti.NumberTheory.NewtonPolygon.Multiplicity
public import TauCeti.NumberTheory.Padics.LogGauge
public import TauCeti.RingTheory.PowerSeries.Radius
public import TauCeti.RingTheory.PowerSeries.Weierstrass.ZeroCount
import TauCeti.NumberTheory.NewtonPolygon.Radius
import TauCeti.RingTheory.PowerSeries.Perturbation.Basic

/-!
# Boundary zeros along an infinite horizontal Newton ray over `ℚ_[p]` and `ℂ_[p]`

Inside the disc of convergence (`‖b ^ σ‖ₑ < f.radius`), the Newton polygon of a nonzero series has
a finite face of slope `σ` (`PowerSeries.exists_isFiniteFace_newtonPolygon_iff_lt_radius`), and its
endpoints determine the exact closed-disc, open-disc, and sphere zero counts
(`PowerSeries.card_zeroMultiset_eq_toNat_order_add_ncard_unitSlope_le_of_lt_radius`,
`PowerSeries.card_filter_zeroMultiset_norm_lt_eq_toNat_order_add_ncard_unitSlope_lt_of_lt_radius`,
`PowerSeries.newtonSlopeMultiplicity_eq_card_filter_zeroMultiset_norm_eq_of_lt_radius`).

At the boundary of convergence (`‖b ^ σ‖ₑ = f.radius`), a restricted series need not have a finite
face of slope `σ`, and the Newton polygon alone no longer determines the boundary zero count. This
file constructs two restricted series over `ℚ_[p]` at the unit boundary `r = 1` (`σ = 0`):

* `unitRaySeries p = 1 + ∑_{n ≥ 1} p ^ ⌈√n⌉ X ^ n`, and
* `perturbedUnitRaySeries p = 1 + X + ∑_{n ≥ 2} p ^ ⌈√n⌉ X ^ n`.

Both series are restricted at `1` with exact radius of convergence `1`, and both have the same
Newton polygon with respect to `TauCeti.padicRealValuation p`: the identically zero sequence `0`,
an infinite horizontal ray of slope `0` with no finite face of slope `0` and
`newtonSlopeMultiplicity = 0`.

However, their active indices at `r = 1` differ:

* `‖unitRaySeries p - 1‖_1 = p⁻¹ < 1`, so `unitRaySeries p` has lowest dominant and distinguished
  degrees `(0, 0)` at `1`, and hence `0` zeros in `‖x‖ ≤ 1` in `ℂ_[p]` (and in `ℚ_[p]`);
* `‖perturbedUnitRaySeries p - (1 + X)‖_1 = p⁻² < 1`, so `perturbedUnitRaySeries p` has lowest
  dominant degree `0` and distinguished degree `1` at `1`. By the nonarchimedean Rouché theorem it
  has `0` zeros in `‖x‖ < 1` and `1` zero on the unit sphere `‖x‖ = 1` of `ℂ_[p]`; moreover, its
  normalised disc polynomial at `1` over `ℚ_[p]` has degree `1` and therefore splits over `ℚ_[p]`,
  so it has a unique zero in `‖x‖ ≤ 1` of `ℚ_[p]` and that zero lies on `‖x‖ = 1`.

## References

* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1.
* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, Springer,
  1984, §5.2.2.
-/

public section

open Filter PowerSeries TauCeti
open scoped NNReal ENNReal

namespace TauCeti.NewtonPolygonBoundaryZerosExample

variable {p : ℕ} [Fact p.Prime]

/-! ### Definitions and coefficients -/

/-- The restricted `p`-adic power series `1 + ∑_{n ≥ 1} p ^ ⌈√n⌉ X ^ n` over `ℚ_[p]`. -/
noncomputable def unitRaySeries (p : ℕ) [Fact p.Prime] : ℚ_[p]⟦X⟧ :=
  PowerSeries.mk fun n => if n = 0 then 1 else (p : ℚ_[p]) ^ ⌈Real.sqrt n⌉₊

/-- The perturbed restricted `p`-adic power series `1 + X + ∑_{n ≥ 2} p ^ ⌈√n⌉ X ^ n` over
`ℚ_[p]`, obtained by replacing the linear coefficient `p` of `unitRaySeries p` with `1`. -/
noncomputable def perturbedUnitRaySeries (p : ℕ) [Fact p.Prime] : ℚ_[p]⟦X⟧ :=
  PowerSeries.mk fun n => if n = 0 then 1 else if n = 1 then 1 else (p : ℚ_[p]) ^ ⌈Real.sqrt n⌉₊

/-- Coefficient formula for `unitRaySeries p`. -/
@[simp]
theorem coeff_unitRaySeries (n : ℕ) :
    coeff n (unitRaySeries p) = if n = 0 then 1 else (p : ℚ_[p]) ^ ⌈Real.sqrt n⌉₊ :=
  coeff_mk n _

/-- The constant coefficient of `unitRaySeries p` is `1`. -/
@[simp]
theorem constantCoeff_unitRaySeries : constantCoeff (unitRaySeries p) = 1 := by
  simp [← coeff_zero_eq_constantCoeff_apply]

/-- Coefficient formula for `perturbedUnitRaySeries p`. -/
@[simp]
theorem coeff_perturbedUnitRaySeries (n : ℕ) :
    coeff n (perturbedUnitRaySeries p) =
      if n = 0 then 1 else if n = 1 then 1 else (p : ℚ_[p]) ^ ⌈Real.sqrt n⌉₊ :=
  coeff_mk n _

/-- The constant coefficient of `perturbedUnitRaySeries p` is `1`. -/
@[simp]
theorem constantCoeff_perturbedUnitRaySeries : constantCoeff (perturbedUnitRaySeries p) = 1 := by
  simp [← coeff_zero_eq_constantCoeff_apply]

/-- `perturbedUnitRaySeries p` differs from `unitRaySeries p` by `(1 - p) X`. -/
theorem perturbedUnitRaySeries_eq_add :
    perturbedUnitRaySeries p = unitRaySeries p + (1 - (p : ℚ_[p])) • X := by
  ext n
  rcases n with _ | _ | n
  · simp
  · simp [Real.sqrt_one]
  · simp [coeff_X]

private theorem one_add_X_eq_X_sub_C_neg_one : (1 + X : ℚ_[p]⟦X⟧) = X - C (-1) := by
  rw [map_neg, map_one, sub_neg_eq_add, add_comm]

private theorem isRestricted_one_add_X : (1 + X : ℚ_[p]⟦X⟧).IsRestricted 1 := by
  rw [one_add_X_eq_X_sub_C_neg_one]
  exact TauCeti.PowerSeries.isRestricted_X_sub_C (-1 : ℚ_[p])

/-! ### Restrictedness at the boundary -/

/-- `unitRaySeries p` is restricted on the closed unit disc `r = 1`. -/
theorem isRestricted_unitRaySeries : (unitRaySeries p).IsRestricted 1 := by
  rw [isRestricted_iff, Nat.cofinite_eq_atTop]
  have hp1 : (p : ℝ)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  have h0 : Tendsto (fun n : ℕ => ((p : ℝ)⁻¹) ^ ⌈Real.sqrt n⌉₊) atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hp1).comp
      (tendsto_nat_ceil_atTop.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))
  refine h0.congr' (eventually_atTop.mpr ⟨1, fun n hn => ?_⟩)
  have hn0 : n ≠ 0 := by omega
  simp [hn0]

/-- `perturbedUnitRaySeries p` is restricted on the closed unit disc `r = 1`. -/
theorem isRestricted_perturbedUnitRaySeries : (perturbedUnitRaySeries p).IsRestricted 1 := by
  rw [perturbedUnitRaySeries_eq_add, smul_eq_C_mul]
  exact (IsRestricted.subring (R := ℚ_[p]) 1).add_mem isRestricted_unitRaySeries
    ((IsRestricted.subring (R := ℚ_[p]) 1).mul_mem (isRestricted_C 1 _)
      (X_eq (R := ℚ_[p]) ▸ isRestricted_monomial 1 1 1))

/-! ### Identical infinite-ray Newton polygons, exact radius `1`, and absence of finite faces -/

private theorem newtonPolygon_eq_zero_of_sq {f : ℚ_[p]⟦X⟧}
    (hnonneg : ∀ n, 0 ≤ padicRealValuation p (coeff n f)) (hc0 : coeff 0 f = 1)
    (hsq : ∀ k, 2 ≤ k → coeff (k ^ 2) f = (p : ℚ_[p]) ^ k) :
    f.newtonPolygon (padicRealValuation p) = 0 := by
  set v := padicRealValuation p
  have hadm : IsAdmissible fun n => v (coeff n f) :=
    isAdmissible_iff.mpr ⟨0, 0, fun n => by simpa using hnonneg n⟩
  have hge0 : (0 : ℕ → WithTop ℝ) ≤ f.newtonPolygon v := fun n => by
    simpa using le_newtonPolygon (isConvexSeq_affine 0 0) (fun k => by simpa using hnonneg k) n
  have h0eq : f.newtonPolygon v 0 = 0 :=
    le_antisymm (by simpa [hc0] using f.newtonPolygon_le hadm 0) (hge0 0)
  ext n
  refine le_antisymm ?_ (hge0 n)
  have hsq_le (k : ℕ) (hk : 2 ≤ k) : f.newtonPolygon v (k ^ 2) ≤ ((k : ℝ) : WithTop ℝ) := by
    refine (f.newtonPolygon_le hadm (k ^ 2)).trans ?_
    rw [hsq k hk, v.map_pow, padicRealValuation_p, nsmul_one]
    exact_mod_cast le_rfl
  have hntop : f.newtonPolygon v n ≠ ⊤ := by
    refine ne_top_of_le_ne_top (WithTop.coe_ne_top (a := ((max n 2 : ℕ) : ℝ))) ?_
    have hk2 : 2 ≤ max n 2 := le_max_right n 2
    have hnk : n ≤ (max n 2) ^ 2 :=
      (le_max_left n 2).trans (Nat.le_self_pow two_ne_zero _)
    exact ((f.isConvexSeq_newtonPolygon v).le_max (Nat.zero_le n) hnk).trans
      (max_le (h0eq.trans_le (WithTop.coe_le_coe.mpr (Nat.cast_nonneg _))) (hsq_le _ hk2))
  rw [← WithTop.coe_untop₀_of_ne_top hntop, Pi.zero_apply, ← WithTop.coe_zero, WithTop.coe_le_coe]
  by_contra! hpos
  obtain ⟨m, hm⟩ := exists_nat_gt ((n : ℝ) / (f.newtonPolygon v n).untop₀)
  let k := max m (max n 2)
  have hk2 : 2 ≤ k := (le_max_right n 2).trans (le_max_right m _)
  have hnk : n ≤ k ^ 2 :=
    ((le_max_left n 2).trans (le_max_right m _)).trans (Nat.le_self_pow two_ne_zero k)
  have hk_top : f.newtonPolygon v (k ^ 2) ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (hsq_le k hk2)
  have hchord : ((k : ℝ) ^ 2) * (f.newtonPolygon v n).untop₀ ≤
      (n : ℝ) * (f.newtonPolygon v (k ^ 2)).untop₀ := by
    simpa [h0eq] using (f.isConvexSeq_newtonPolygon v).chord_inequality
      (by simp [h0eq]) hk_top (Nat.zero_le n) hnk
  have hkuntop : (f.newtonPolygon v (k ^ 2)).untop₀ ≤ k := by
    have h := hsq_le k hk2
    rwa [← WithTop.coe_untop₀_of_ne_top hk_top, WithTop.coe_le_coe] at h
  have hle : ((k : ℝ) ^ 2) * (f.newtonPolygon v n).untop₀ ≤ (n : ℝ) * k :=
    hchord.trans (mul_le_mul_of_nonneg_left hkuntop (Nat.cast_nonneg n))
  have hk0 : (0 : ℝ) < k := by positivity
  have hmul : (n : ℝ) < (k : ℝ) * (f.newtonPolygon v n).untop₀ := by
    have hmk : (m : ℝ) ≤ k := Nat.cast_le.mpr (le_max_left m _)
    exact ((div_lt_iff₀ hpos).mp hm).trans_le (mul_le_mul_of_nonneg_right hmk hpos.le)
  nlinarith

/-- The Newton polygon of `unitRaySeries p` is the infinite horizontal ray `0`. -/
@[simp]
theorem newtonPolygon_unitRaySeries :
    (unitRaySeries p).newtonPolygon (padicRealValuation p) = 0 := by
  refine newtonPolygon_eq_zero_of_sq (fun n => ?_) ?_ fun k hk => ?_
  · by_cases hn : n = 0
    · simp [hn]
    · simp [hn, padicRealValuation_p]
  · simp
  · have hk0 : k ≠ 0 := by omega
    simp [hk0]

/-- The Newton polygon of `perturbedUnitRaySeries p` is also the infinite horizontal ray `0`. -/
@[simp]
theorem newtonPolygon_perturbedUnitRaySeries :
    (perturbedUnitRaySeries p).newtonPolygon (padicRealValuation p) = 0 := by
  refine newtonPolygon_eq_zero_of_sq (fun n => ?_) ?_ fun k hk => ?_
  · rcases n with _ | _ | n <;> simp [padicRealValuation_p]
  · simp
  · have hk0 : k ≠ 0 := by omega
    have hk1 : k ≠ 1 := by omega
    simp [hk0, hk1]

private theorem radius_eq_one_of_newtonPolygon_eq_zero {f : ℚ_[p]⟦X⟧}
    (hres : f.IsRestricted 1) (hinf : {n | coeff n f ≠ 0}.Infinite)
    (hnp : f.newtonPolygon (padicRealValuation p) = 0) :
    f.radius = 1 := by
  have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt
  have hadm : IsAdmissible fun n => padicRealValuation p (coeff n f) :=
    (f.isAdmissible_addValuation_coeff_iff_exists_isRestricted (padicRealValuation p) hp1
      fun _ hx => norm_eq_rpow_neg_padicRealValuation hx).mpr ⟨1, zero_lt_one, hres⟩
  have : Nonempty (finiteEdges (0 : ℕ → WithTop ℝ)) := ⟨⟨0, by simp⟩⟩
  have hslope : (⨆ i : finiteEdges (0 : ℕ → WithTop ℝ),
      (unitSlope (0 : ℕ → WithTop ℝ) i : EReal)) = 0 := by
    simp [unitSlope_def]
  rw [f.radius_eq_exp_iSup_unitSlope_newtonPolygon (padicRealValuation p) hp1
    (fun _ hx => norm_eq_rpow_neg_padicRealValuation hx) hadm hinf, hnp, hslope, zero_mul,
    EReal.exp_zero]

/-- `unitRaySeries p` has exact radius of convergence `1`. -/
@[simp]
theorem radius_unitRaySeries : (unitRaySeries p).radius = 1 := by
  refine radius_eq_one_of_newtonPolygon_eq_zero isRestricted_unitRaySeries
    (Set.infinite_univ.mono fun n _ => ?_) newtonPolygon_unitRaySeries
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  by_cases hn : n = 0 <;> simp [hn, hp0]

/-- `perturbedUnitRaySeries p` has exact radius of convergence `1`. -/
@[simp]
theorem radius_perturbedUnitRaySeries : (perturbedUnitRaySeries p).radius = 1 := by
  refine radius_eq_one_of_newtonPolygon_eq_zero isRestricted_perturbedUnitRaySeries
    (Set.infinite_univ.mono fun n _ => ?_) newtonPolygon_perturbedUnitRaySeries
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rcases n with _ | _ | n <;> simp [hp0]

/-- `unitRaySeries p` has no finite face of slope `0`. -/
theorem not_exists_isFiniteFace_unitRaySeries_zero :
    ¬∃ l u : ℕ, IsFiniteFace ((unitRaySeries p).newtonPolygon (padicRealValuation p)) 0 l u := by
  rintro ⟨l, u, h⟩
  exact not_isFiniteFace_affine 0 0 l u
    (by simpa [newtonPolygon_unitRaySeries, Pi.zero_def] using h)

/-- `perturbedUnitRaySeries p` has no finite face of slope `0`. -/
theorem not_exists_isFiniteFace_perturbedUnitRaySeries_zero :
    ¬∃ l u : ℕ,
      IsFiniteFace ((perturbedUnitRaySeries p).newtonPolygon (padicRealValuation p)) 0 l u := by
  rintro ⟨l, u, h⟩
  exact not_isFiniteFace_affine 0 0 l u
    (by simpa [newtonPolygon_perturbedUnitRaySeries, Pi.zero_def] using h)

/-- The slope multiplicity at `0` of `unitRaySeries p` is the `Set.ncard` junk value `0`, because
infinitely many unit edges have slope `0`. -/
@[simp]
theorem newtonSlopeMultiplicity_unitRaySeries_zero :
    (unitRaySeries p).newtonSlopeMultiplicity (padicRealValuation p) 0 = 0 := by
  rw [newtonSlopeMultiplicity_def, newtonPolygon_unitRaySeries]
  refine Set.Infinite.ncard (Set.infinite_univ.mono fun n _ => ?_)
  simp [unitSlope_def]

/-- The slope multiplicity at `0` of `perturbedUnitRaySeries p` is likewise `0`. -/
@[simp]
theorem newtonSlopeMultiplicity_perturbedUnitRaySeries_zero :
    (perturbedUnitRaySeries p).newtonSlopeMultiplicity (padicRealValuation p) 0 = 0 := by
  rw [newtonSlopeMultiplicity_def, newtonPolygon_perturbedUnitRaySeries]
  refine Set.Infinite.ncard (Set.infinite_univ.mono fun n _ => ?_)
  simp [unitSlope_def]

/-! ### Gauss-norm perturbations and active indices at `r = 1` -/

/-- At radius `1`, `unitRaySeries p` is within `p⁻¹ < 1` of the constant series `1`. -/
theorem gaussNorm_unitRaySeries_sub_one :
    (unitRaySeries p - 1).gaussNorm norm 1 = (p : ℝ)⁻¹ := by
  have hp1 : (p : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr (Fact.out : p.Prime).pos)
  have hc1 : ‖coeff 1 (unitRaySeries p - 1)‖ * 1 ^ 1 = (p : ℝ)⁻¹ := by
    simp [Real.sqrt_one]
  refine (TauCeti.PowerSeries.gaussNorm_eq_of_forall_le (s := 1) fun n => ?_).trans hc1
  rw [hc1]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hne : ⌈Real.sqrt n⌉₊ ≠ 0 :=
      (Nat.ceil_pos.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)))).ne'
    have hcoeff : coeff n (unitRaySeries p - 1) = (p : ℚ_[p]) ^ ⌈Real.sqrt n⌉₊ := by
      simp [hn]
    rw [hcoeff, one_pow, mul_one, norm_pow, Padic.norm_p]
    exact pow_le_of_le_one (by positivity) hp1 hne

/-- At radius `1`, `perturbedUnitRaySeries p` is within `p⁻² < 1` of `1 + X`. -/
theorem gaussNorm_perturbedUnitRaySeries_sub_one_add_X :
    (perturbedUnitRaySeries p - (1 + X)).gaussNorm norm 1 = ((p : ℝ)⁻¹) ^ 2 := by
  have hp1 : (p : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr (Fact.out : p.Prime).pos)
  have hceil2 : ⌈Real.sqrt 2⌉₊ = 2 := by
    refine le_antisymm (Nat.ceil_le.mpr ?_) (Nat.lt_ceil.mpr ?_)
    · rw [Real.sqrt_le_iff]
      norm_num
    · rw [Nat.cast_one, Real.lt_sqrt zero_le_one]
      norm_num
  have hc2 : ‖coeff 2 (perturbedUnitRaySeries p - (1 + X))‖ * 1 ^ 2 = ((p : ℝ)⁻¹) ^ 2 := by
    simp [coeff_X, hceil2]
  refine (TauCeti.PowerSeries.gaussNorm_eq_of_forall_le (s := 2) fun n => ?_).trans hc2
  rw [hc2]
  rcases n with _ | _ | n
  · simp
  · simp
  · have h2 : 2 ≤ ⌈Real.sqrt (n + 2 : ℕ)⌉₊ := by
      refine Nat.lt_ceil.mpr ?_
      rw [Nat.cast_one, Real.lt_sqrt zero_le_one, one_pow]
      exact_mod_cast (by omega : 1 < n + 2)
    have hn1 : n + 2 ≠ 1 := by omega
    have hcoeff : coeff (n + 2) (perturbedUnitRaySeries p - (1 + X)) =
        (p : ℚ_[p]) ^ ⌈Real.sqrt (n + 2 : ℕ)⌉₊ := by
      simp [hn1, coeff_X]
    rw [hcoeff, one_pow, mul_one, norm_pow, Padic.norm_p]
    exact pow_le_pow_of_le_one (by positivity) hp1 h2

private theorem gaussNorm_one_add_X_eq_one : (1 + X : ℚ_[p]⟦X⟧).gaussNorm norm 1 = 1 := by
  rw [one_add_X_eq_X_sub_C_neg_one, TauCeti.PowerSeries.gaussNorm_X_sub_C]
  simp

private theorem isDistinguished_one_add_X :
    TauCeti.PowerSeries.IsDistinguished 1 1 (1 + X : ℚ_[p]⟦X⟧) := by
  rw [one_add_X_eq_X_sub_C_neg_one]
  exact TauCeti.PowerSeries.isDistinguished_X_sub_C zero_lt_one (by simp)

private theorem isLowestDominant_one_add_X :
    TauCeti.PowerSeries.IsLowestDominant 1 0 (1 + X : ℚ_[p]⟦X⟧) := by
  rw [one_add_X_eq_X_sub_C_neg_one]
  exact TauCeti.PowerSeries.isLowestDominant_zero_X_sub_C zero_lt_one (by simp)

private theorem gaussNorm_one_add_X_sub_perturbedUnitRaySeries_lt :
    ((1 + X : ℚ_[p]⟦X⟧) - perturbedUnitRaySeries p).gaussNorm norm 1 <
      (1 + X : ℚ_[p]⟦X⟧).gaussNorm norm 1 := by
  rw [TauCeti.PowerSeries.gaussNorm_sub_comm, gaussNorm_perturbedUnitRaySeries_sub_one_add_X,
    gaussNorm_one_add_X_eq_one]
  exact pow_lt_one₀ (by positivity)
    (inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)) (by decide)

/-- `unitRaySeries p` is distinguished of degree `0` at radius `1`. -/
theorem isDistinguished_unitRaySeries :
    TauCeti.PowerSeries.IsDistinguished 1 0 (unitRaySeries p) := by
  refine (TauCeti.PowerSeries.gaussNorm_sub_one_lt_one_iff zero_lt_one
    isRestricted_unitRaySeries constantCoeff_unitRaySeries).mp ?_
  rw [gaussNorm_unitRaySeries_sub_one]
  exact inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)

/-- `unitRaySeries p` has lowest dominant degree `0` at radius `1`. -/
theorem isLowestDominant_unitRaySeries :
    TauCeti.PowerSeries.IsLowestDominant 1 0 (unitRaySeries p) :=
  isDistinguished_unitRaySeries.isLowestDominant_zero

/-- `perturbedUnitRaySeries p` is distinguished of degree `1` at radius `1`. -/
theorem isDistinguished_perturbedUnitRaySeries :
    TauCeti.PowerSeries.IsDistinguished 1 1 (perturbedUnitRaySeries p) :=
  (TauCeti.PowerSeries.isDistinguished_iff_of_gaussNorm_sub_lt (R := ℚ_[p]) zero_le_one
    (isDistinguished_one_add_X (p := p)).hasGaussNorm
    (TauCeti.PowerSeries.hasGaussNorm_of_isRestricted (R := ℚ_[p])
      isRestricted_perturbedUnitRaySeries)
    gaussNorm_one_add_X_sub_perturbedUnitRaySeries_lt).mp isDistinguished_one_add_X

/-- `perturbedUnitRaySeries p` has lowest dominant degree `0` at radius `1`. -/
theorem isLowestDominant_perturbedUnitRaySeries :
    TauCeti.PowerSeries.IsLowestDominant 1 0 (perturbedUnitRaySeries p) :=
  (TauCeti.PowerSeries.isLowestDominant_iff_of_gaussNorm_sub_lt (R := ℚ_[p]) zero_le_one
    (isDistinguished_one_add_X (p := p)).hasGaussNorm
    (TauCeti.PowerSeries.hasGaussNorm_of_isRestricted (R := ℚ_[p])
      isRestricted_perturbedUnitRaySeries)
    gaussNorm_one_add_X_sub_perturbedUnitRaySeries_lt).mp isLowestDominant_one_add_X

/-! ### Exact zero counts over `ℂ_[p]` and `ℚ_[p]` -/

/-- `unitRaySeries p` has empty zero multiset on the closed unit disc of `ℂ_[p]`. -/
@[simp]
theorem zeroMultiset_unitRaySeries_padicComplex :
    (unitRaySeries p).zeroMultiset 1 ℂ_[p] = 0 :=
  Multiset.card_eq_zero.mp
    (isDistinguished_unitRaySeries.card_zeroMultiset_eq zero_lt_one isRestricted_unitRaySeries)

/-- `unitRaySeries p` has no zeros anywhere in the closed unit disc `‖x‖ ≤ 1` of `ℂ_[p]`. -/
theorem setOf_norm_le_one_and_evalAt_unitRaySeries_eq_zero :
    {x : ℂ_[p] | ‖x‖ ≤ 1 ∧ (unitRaySeries p).evalAt x = 0} = ∅ := by
  classical
  rw [isRestricted_unitRaySeries.setOf_norm_le_and_evalAt_eq_zero_eq_toFinset_zeroMultiset
    zero_lt_one isDistinguished_unitRaySeries.ne_zero, zeroMultiset_unitRaySeries_padicComplex]
  simp

/-- `perturbedUnitRaySeries p` has `1` zero in the closed unit disc `‖x‖ ≤ 1` of `ℂ_[p]`, counted
with multiplicity. -/
theorem card_zeroMultiset_perturbedUnitRaySeries_padicComplex :
    ((perturbedUnitRaySeries p).zeroMultiset 1 ℂ_[p]).card = 1 := by
  rw [(TauCeti.PowerSeries.card_zeroMultiset_eq_of_gaussNorm_sub_lt (L := ℂ_[p]) zero_lt_one
    isRestricted_one_add_X isRestricted_perturbedUnitRaySeries
    gaussNorm_one_add_X_sub_perturbedUnitRaySeries_lt).symm]
  exact isDistinguished_one_add_X.card_zeroMultiset_eq zero_lt_one isRestricted_one_add_X

/-- `perturbedUnitRaySeries p` has `0` zeros in the open unit disc `‖x‖ < 1` of `ℂ_[p]`. -/
theorem card_filter_zeroMultiset_perturbedUnitRaySeries_norm_lt_one_padicComplex :
    (((perturbedUnitRaySeries p).zeroMultiset 1 ℂ_[p]).filter (‖·‖ < 1)).card = 0 :=
  isLowestDominant_perturbedUnitRaySeries.card_filter_zeroMultiset_norm_lt_eq zero_lt_one
    isRestricted_perturbedUnitRaySeries

/-- Although `(perturbedUnitRaySeries p).newtonSlopeMultiplicity (padicRealValuation p) 0 = 0`,
`perturbedUnitRaySeries p` has `1` zero on the unit sphere `‖x‖ = 1` of `ℂ_[p]`, counted with
multiplicity. -/
theorem card_filter_zeroMultiset_perturbedUnitRaySeries_norm_eq_one_padicComplex :
    (((perturbedUnitRaySeries p).zeroMultiset 1 ℂ_[p]).filter (‖·‖ = 1)).card = 1 :=
  TauCeti.PowerSeries.card_filter_zeroMultiset_norm_eq_eq isDistinguished_perturbedUnitRaySeries
    isLowestDominant_perturbedUnitRaySeries zero_lt_one isRestricted_perturbedUnitRaySeries

private theorem exists_isDiscPreparation_perturbedUnitRaySeries_splits :
    ∃ (P : Polynomial ℚ_[p]) (U : ℚ_[p]⟦X⟧),
      TauCeti.PowerSeries.IsDiscPreparation 1 1 (perturbedUnitRaySeries p) P U ∧
        (P.map (algebraMap ℚ_[p] ℚ_[p])).Splits := by
  obtain ⟨P, U, hP⟩ := (isDistinguished_perturbedUnitRaySeries (p := p)).exists_isDiscPreparation
    zero_lt_one isRestricted_perturbedUnitRaySeries constantCoeff_perturbedUnitRaySeries
  exact ⟨P, U, hP, Polynomial.Splits.of_natDegree_le_one
    (Polynomial.natDegree_map_le.trans hP.natDegree_eq.le)⟩

/-- `perturbedUnitRaySeries p` has `1` zero on the unit sphere `‖x‖ = 1` of `ℚ_[p]`, counted with
multiplicity. -/
theorem card_filter_zeroMultiset_perturbedUnitRaySeries_norm_eq_one_padic :
    (((perturbedUnitRaySeries p).zeroMultiset 1 ℚ_[p]).filter (‖·‖ = 1)).card = 1 := by
  obtain ⟨P, U, hP, hs⟩ := exists_isDiscPreparation_perturbedUnitRaySeries_splits (p := p)
  exact hP.card_filter_zeroMultiset_norm_eq_eq_of_splits
    isLowestDominant_perturbedUnitRaySeries zero_lt_one hs

/-- Every zero of `perturbedUnitRaySeries p` in the closed unit disc `‖x‖ ≤ 1` of `ℚ_[p]` lies on
the unit sphere `‖x‖ = 1`. -/
theorem norm_eq_one_of_norm_le_one_of_evalAt_perturbedUnitRaySeries_eq_zero {x : ℚ_[p]}
    (hx : ‖x‖ ≤ 1) (h0 : (perturbedUnitRaySeries p).evalAt x = 0) : ‖x‖ = 1 := by
  classical
  obtain ⟨P, U, hP, hs⟩ := exists_isDiscPreparation_perturbedUnitRaySeries_splits (p := p)
  have hopen : ((perturbedUnitRaySeries p).zeroMultiset 1 ℚ_[p]).filter (‖·‖ < 1) = 0 :=
    Multiset.card_eq_zero.mp (hP.card_filter_zeroMultiset_norm_lt_eq_of_splits
      isLowestDominant_perturbedUnitRaySeries zero_lt_one hs)
  refine hx.eq_of_not_lt fun hlt => ?_
  have hmem : x ∈ ((perturbedUnitRaySeries p).zeroMultiset 1 ℚ_[p]).filter (‖·‖ < 1) :=
    Multiset.mem_filter.mpr ⟨(isRestricted_perturbedUnitRaySeries.mem_zeroMultiset_iff
      zero_lt_one isDistinguished_perturbedUnitRaySeries.ne_zero).mpr ⟨hx, by simpa using h0⟩, hlt⟩
  simp [hopen] at hmem

/-- `perturbedUnitRaySeries p` has a unique zero in the closed unit disc `‖x‖ ≤ 1` of `ℚ_[p]`. -/
theorem existsUnique_norm_le_one_and_evalAt_perturbedUnitRaySeries_eq_zero :
    ∃! x : ℚ_[p], ‖x‖ ≤ 1 ∧ (perturbedUnitRaySeries p).evalAt x = 0 := by
  classical
  obtain ⟨P, U, hP, hs⟩ := exists_isDiscPreparation_perturbedUnitRaySeries_splits (p := p)
  obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp (hP.card_zeroMultiset_eq_of_splits zero_lt_one hs)
  have hset : {x : ℚ_[p] | ‖x‖ ≤ 1 ∧ (perturbedUnitRaySeries p).evalAt x = 0} = {a} := by
    simpa [ha] using
      isRestricted_perturbedUnitRaySeries.setOf_norm_le_and_evalAt_eq_zero_eq_toFinset_zeroMultiset
        (L := ℚ_[p]) zero_lt_one (isDistinguished_perturbedUnitRaySeries (p := p)).ne_zero
  refine ⟨a, ?_, fun y hy => ?_⟩
  · have : a ∈ ({a} : Set ℚ_[p]) := Set.mem_singleton a
    rwa [← hset] at this
  · have : y ∈ {x : ℚ_[p] | ‖x‖ ≤ 1 ∧ (perturbedUnitRaySeries p).evalAt x = 0} := hy
    simpa [hset] using this

end TauCeti.NewtonPolygonBoundaryZerosExample
