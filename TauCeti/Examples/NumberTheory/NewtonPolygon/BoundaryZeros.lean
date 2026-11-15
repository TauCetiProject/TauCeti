/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import TauCeti.NumberTheory.NewtonPolygon.ZeroCount
public import TauCeti.NumberTheory.Padics.LogGauge
import TauCeti.RingTheory.PowerSeries.Perturbation.Basic

/-!
# Boundary zeros along an infinite horizontal Newton ray over `ℚ_[p]` and `ℂ_[p]`

Inside the disc of convergence (`‖b ^ σ‖ₑ < f.radius`), the Newton polygon of a nonzero series has
a finite face of slope `σ` (`PowerSeries.exists_isFiniteFace_newtonPolygon_of_lt_radius`), and its
endpoints determine the exact closed-disc, open-disc, and sphere zero counts
(`PowerSeries.card_zeroMultiset_eq_of_lt_radius`,
`PowerSeries.card_filter_zeroMultiset_norm_lt_eq_of_lt_radius`,
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
  so this unique unit-sphere zero already lies in `ℚ_[p]`.

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

private theorem ceil_sqrt_sq (k : ℕ) : ⌈Real.sqrt ((k ^ 2 : ℕ) : ℝ)⌉₊ = k := by
  rw [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg k), Nat.ceil_natCast]

private theorem tendsto_ceil_sqrt_atTop : Tendsto (fun n : ℕ => ⌈Real.sqrt n⌉₊) atTop atTop := by
  refine tendsto_atTop_atTop.mpr fun k => ⟨k ^ 2, fun n hn => ?_⟩
  calc k = ⌈Real.sqrt ((k ^ 2 : ℕ) : ℝ)⌉₊ := (ceil_sqrt_sq k).symm
    _ ≤ ⌈Real.sqrt n⌉₊ := Nat.ceil_mono (Real.sqrt_le_sqrt (by exact_mod_cast hn))

private theorem isRestricted_X_one : (X : ℚ_[p]⟦X⟧).IsRestricted 1 := by
  rw [← Polynomial.coe_X]
  exact TauCeti.PowerSeries.isRestricted_polynomial Polynomial.X

private theorem isRestricted_one_add_X : (1 + X : ℚ_[p]⟦X⟧).IsRestricted 1 :=
  (IsRestricted.subring (R := ℚ_[p]) 1).add_mem
    (IsRestricted.subring (R := ℚ_[p]) 1).one_mem isRestricted_X_one

/-! ### Restrictedness at the boundary and exact radius `1` -/

/-- `unitRaySeries p` is restricted on the closed unit disc `r = 1`. -/
theorem isRestricted_unitRaySeries : (unitRaySeries p).IsRestricted 1 := by
  rw [isRestricted_iff, Nat.cofinite_eq_atTop]
  have hp1 : (p : ℝ)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  have h0 : Tendsto (fun n : ℕ => ((p : ℝ)⁻¹) ^ ⌈Real.sqrt n⌉₊) atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hp1).comp tendsto_ceil_sqrt_atTop
  refine h0.congr' (eventually_atTop.mpr ⟨1, fun n hn => ?_⟩)
  have hn0 : n ≠ 0 := by omega
  simp [hn0]

/-- `perturbedUnitRaySeries p` is restricted on the closed unit disc `r = 1`. -/
theorem isRestricted_perturbedUnitRaySeries : (perturbedUnitRaySeries p).IsRestricted 1 := by
  rw [perturbedUnitRaySeries_eq_add, smul_eq_C_mul]
  have hC : (C (1 - (p : ℚ_[p])) : ℚ_[p]⟦X⟧).IsRestricted 1 := by
    rw [← Polynomial.coe_C]
    exact TauCeti.PowerSeries.isRestricted_polynomial _
  exact (IsRestricted.subring (R := ℚ_[p]) 1).add_mem isRestricted_unitRaySeries
    ((IsRestricted.subring (R := ℚ_[p]) 1).mul_mem hC isRestricted_X_one)

/-- Any series agreeing with `(p : ℚ_[p]) ^ k` along squares `k ^ 2` for `k ≥ 2` is not restricted
at any radius `r > 1`. -/
private theorem not_isRestricted_of_one_lt {f : ℚ_[p]⟦X⟧}
    (hsq : ∀ k, 2 ≤ k → coeff (k ^ 2) f = (p : ℚ_[p]) ^ k) {r : ℝ} (hr : 1 < r) :
    ¬f.IsRestricted r := by
  intro hfr
  have htend0 : Tendsto (fun n : ℕ => ‖coeff n f‖ * r ^ n) atTop (nhds 0) :=
    Nat.cofinite_eq_atTop ▸ (isRestricted_iff r f).mp hfr
  have htend : Tendsto (fun k : ℕ => ‖coeff (k ^ 2) f‖ * r ^ (k ^ 2)) atTop (nhds 0) :=
    htend0.comp (tendsto_atTop_atTop.mpr fun N =>
      ⟨N, fun k hk => hk.trans (Nat.le_self_pow two_ne_zero k)⟩)
  have hlt1 : ∀ᶠ k in atTop, ‖coeff (k ^ 2) f‖ * r ^ (k ^ 2) < 1 :=
    htend.eventually (gt_mem_nhds zero_lt_one)
  have hbig : ∀ᶠ k in atTop, (p : ℝ) ≤ r ^ k :=
    (tendsto_pow_atTop_atTop_of_one_lt hr).eventually (Filter.eventually_ge_atTop (p : ℝ))
  obtain ⟨k, ⟨hk2, hklt⟩, hkp⟩ :=
    ((eventually_ge_atTop 2).and hlt1 |>.and hbig).exists
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hge1 : 1 ≤ ‖coeff (k ^ 2) f‖ * r ^ (k ^ 2) := by
    rw [hsq k hk2, norm_pow, Padic.norm_p, sq, pow_mul, ← mul_pow]
    exact one_le_pow₀ ((le_inv_mul_iff₀ hp0).mpr (by linarith))
  exact hklt.not_ge hge1

/-- `unitRaySeries p` has exact radius of convergence `1`. -/
@[simp]
theorem radius_unitRaySeries : (unitRaySeries p).radius = 1 := by
  refine le_antisymm (le_of_not_gt fun hlt => ?_) ?_
  · obtain ⟨r, h1r, hrf⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hlt
    have hr1 : 1 < (r : ℝ) := by exact_mod_cast h1r
    refine not_isRestricted_of_one_lt (fun k hk => ?_) hr1
      (isRestricted_of_lt_radius (by simpa using hrf))
    have hk0 : k ≠ 0 := by omega
    simp [hk0]
  · simpa using le_radius_of_isRestricted (isRestricted_unitRaySeries (p := p))

/-- `perturbedUnitRaySeries p` has exact radius of convergence `1`. -/
@[simp]
theorem radius_perturbedUnitRaySeries : (perturbedUnitRaySeries p).radius = 1 := by
  refine le_antisymm (le_of_not_gt fun hlt => ?_) ?_
  · obtain ⟨r, h1r, hrf⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hlt
    have hr1 : 1 < (r : ℝ) := by exact_mod_cast h1r
    refine not_isRestricted_of_one_lt (fun k hk => ?_) hr1
      (isRestricted_of_lt_radius (by simpa using hrf))
    have hk0 : k ≠ 0 := by omega
    have hk1 : k ≠ 1 := by omega
    simp [hk0, hk1]
  · simpa using le_radius_of_isRestricted (isRestricted_perturbedUnitRaySeries (p := p))

/-! ### Identical infinite-ray Newton polygons and absence of finite faces -/

private theorem newtonPolygon_eq_zero_of_sq {f : ℚ_[p]⟦X⟧}
    (hnonneg : ∀ n, 0 ≤ padicRealValuation p (coeff n f)) (hc0 : coeff 0 f = 1)
    (hsq : ∀ k, 2 ≤ k → coeff (k ^ 2) f = (p : ℚ_[p]) ^ k) :
    f.newtonPolygon (padicRealValuation p) = 0 := by
  set v := padicRealValuation p
  have hadm : IsAdmissible fun n => v (coeff n f) :=
    isAdmissible_iff.mpr ⟨0, 0, fun n => by simpa using hnonneg n⟩
  have hconv0 : IsConvexSeq (0 : ℕ → WithTop ℝ) := by
    convert isConvexSeq_affine 0 0 with n
    simp
  have hge0 : (0 : ℕ → WithTop ℝ) ≤ f.newtonPolygon v :=
    le_newtonPolygon hconv0 hnonneg
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
  have hchord := (f.isConvexSeq_newtonPolygon v).chord_inequality
    (by simp [h0eq]) hk_top (Nat.zero_le n) hnk
  have hkuntop : (f.newtonPolygon v (k ^ 2)).untop₀ ≤ k := by
    have h := hsq_le k hk2
    rwa [← WithTop.coe_untop₀_of_ne_top hk_top, WithTop.coe_le_coe] at h
  rw [Nat.cast_zero, sub_zero, sub_zero, h0eq, WithTop.untop₀_zero, mul_zero, zero_add,
    Nat.cast_pow] at hchord
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

private theorem not_isFiniteFace_zero_seq {l u : ℕ} :
    ¬IsFiniteFace (0 : ℕ → WithTop ℝ) 0 l u := by
  intro h
  obtain ⟨hl, c, _, hface⟩ := isFiniteFace_iff.mp h
  have hlc : l ∈ supportingFace (0 : ℕ → WithTop ℝ) 0 c := hface.symm.subset ⟨le_rfl, hl⟩
  have hc0 : c = 0 := by
    rw [mem_supportingFace, Pi.zero_apply, zero_mul, add_zero, ← WithTop.coe_zero,
      WithTop.coe_eq_coe] at hlc
    exact hlc.symm
  have hu1 : u + 1 ∈ supportingFace (0 : ℕ → WithTop ℝ) 0 c := by
    simp [mem_supportingFace, hc0]
  exact absurd (hface.subset hu1).2 (Nat.not_succ_le_self u)

/-- `unitRaySeries p` has no finite face of slope `0`. -/
theorem not_exists_isFiniteFace_unitRaySeries :
    ¬∃ l u : ℕ, IsFiniteFace ((unitRaySeries p).newtonPolygon (padicRealValuation p)) 0 l u := by
  rintro ⟨l, u, h⟩
  rw [newtonPolygon_unitRaySeries] at h
  exact not_isFiniteFace_zero_seq h

/-- `perturbedUnitRaySeries p` has no finite face of slope `0`. -/
theorem not_exists_isFiniteFace_perturbedUnitRaySeries :
    ¬∃ l u : ℕ,
      IsFiniteFace ((perturbedUnitRaySeries p).newtonPolygon (padicRealValuation p)) 0 l u := by
  rintro ⟨l, u, h⟩
  rw [newtonPolygon_perturbedUnitRaySeries] at h
  exact not_isFiniteFace_zero_seq h

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
  apply le_antisymm
  · rw [PowerSeries.gaussNorm_eq]
    refine ciSup_le fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hne : ⌈Real.sqrt n⌉₊ ≠ 0 :=
        (Nat.ceil_pos.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)))).ne'
      have hcoeff : coeff n (unitRaySeries p - 1) = (p : ℚ_[p]) ^ ⌈Real.sqrt n⌉₊ := by
        simp [hn]
      rw [hcoeff, one_pow, mul_one, norm_pow, Padic.norm_p]
      exact pow_le_of_le_one (by positivity) hp1 hne
  · have hsub_res : (unitRaySeries p - 1).IsRestricted 1 :=
      (IsRestricted.subring (R := ℚ_[p]) 1).sub_mem isRestricted_unitRaySeries
        (IsRestricted.subring (R := ℚ_[p]) 1).one_mem
    have hbd : (unitRaySeries p - 1).HasGaussNorm (norm : ℚ_[p] → ℝ) 1 :=
      TauCeti.PowerSeries.hasGaussNorm_of_isRestricted (R := ℚ_[p]) hsub_res
    have h1 := PowerSeries.le_gaussNorm (R := ℚ_[p]) norm 1 (unitRaySeries p - 1) hbd 1
    have hc1 : ‖coeff 1 (unitRaySeries p - 1)‖ * 1 ^ 1 = (p : ℝ)⁻¹ := by
      simp [Real.sqrt_one]
    rwa [hc1] at h1

/-- At radius `1`, `perturbedUnitRaySeries p` is within `p⁻² < 1` of `1 + X`. -/
theorem gaussNorm_perturbedUnitRaySeries_sub_one_add_X :
    (perturbedUnitRaySeries p - (1 + X)).gaussNorm norm 1 = ((p : ℝ)⁻¹) ^ 2 := by
  have hp1 : (p : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr (Fact.out : p.Prime).pos)
  apply le_antisymm
  · rw [PowerSeries.gaussNorm_eq]
    refine ciSup_le fun n => ?_
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
  · have hsub_res : (perturbedUnitRaySeries p - (1 + X)).IsRestricted 1 :=
      (IsRestricted.subring (R := ℚ_[p]) 1).sub_mem
        isRestricted_perturbedUnitRaySeries isRestricted_one_add_X
    have hbd : (perturbedUnitRaySeries p - (1 + X)).HasGaussNorm (norm : ℚ_[p] → ℝ) 1 :=
      TauCeti.PowerSeries.hasGaussNorm_of_isRestricted (R := ℚ_[p]) hsub_res
    have h2 := PowerSeries.le_gaussNorm (R := ℚ_[p]) norm 1
      (perturbedUnitRaySeries p - (1 + X)) hbd 2
    have hceil2 : ⌈Real.sqrt 2⌉₊ = 2 := by
      refine le_antisymm (Nat.ceil_le.mpr ?_) (Nat.lt_ceil.mpr ?_)
      · rw [Real.sqrt_le_iff]
        norm_num
      · rw [Nat.cast_one, Real.lt_sqrt zero_le_one]
        norm_num
    have hc2 : ‖coeff 2 (perturbedUnitRaySeries p - (1 + X))‖ * 1 ^ 2 = ((p : ℝ)⁻¹) ^ 2 := by
      simp [coeff_X, hceil2]
    rwa [hc2] at h2

private theorem isDistinguished_one_series :
    TauCeti.PowerSeries.IsDistinguished 1 0 (1 : ℚ_[p]⟦X⟧) := by
  have h := TauCeti.PowerSeries.isDistinguished_monomial (R := ℚ_[p]) zero_lt_one
    (one_ne_zero : (1 : ℚ_[p]) ≠ 0) 0
  rwa [monomial_zero_eq_C_apply, map_one] at h

private theorem gaussNorm_one_eq_one : (1 : ℚ_[p]⟦X⟧).gaussNorm norm 1 = 1 := by
  have h := (isDistinguished_one_series (p := p)).norm_coeff_mul_pow_eq.symm
  simpa [coeff_one] using h

private theorem isDistinguished_one_add_X :
    TauCeti.PowerSeries.IsDistinguished 1 1 (1 + X : ℚ_[p]⟦X⟧) := by
  have hbd : (1 + X : ℚ_[p]⟦X⟧).HasGaussNorm (norm : ℚ_[p] → ℝ) 1 :=
    TauCeti.PowerSeries.hasGaussNorm_of_isRestricted (R := ℚ_[p]) isRestricted_one_add_X
  have hgn : (1 + X : ℚ_[p]⟦X⟧).gaussNorm norm 1 = 1 := by
    apply le_antisymm
    · rw [PowerSeries.gaussNorm_eq]
      refine ciSup_le fun n => ?_
      rcases n with _ | _ | n <;> simp [coeff_X]
    · have h1 := PowerSeries.le_gaussNorm (R := ℚ_[p]) norm 1 (1 + X) hbd 1
      have hc1 : ‖coeff 1 (1 + X : ℚ_[p]⟦X⟧)‖ * 1 ^ 1 = 1 := by simp [coeff_X]
      rwa [hc1] at h1
  refine ⟨?_, fun m hm => ?_⟩
  · rw [hgn]
    simp [coeff_X]
  · rw [hgn]
    rcases m with _ | _ | m
    · omega
    · omega
    · simp [coeff_X]

private theorem gaussNorm_one_add_X_eq_one : (1 + X : ℚ_[p]⟦X⟧).gaussNorm norm 1 = 1 := by
  have h := (isDistinguished_one_add_X (p := p)).norm_coeff_mul_pow_eq.symm
  have hc1 : ‖coeff 1 (1 + X : ℚ_[p]⟦X⟧)‖ * 1 ^ 1 = 1 := by simp [coeff_X]
  rwa [hc1] at h

private theorem isLowestDominant_one_add_X :
    TauCeti.PowerSeries.IsLowestDominant 1 0 (1 + X : ℚ_[p]⟦X⟧) := by
  have hd := isDistinguished_one_add_X (p := p)
  refine ⟨hd.gaussNorm_pos, ?_, fun m hm => absurd hm m.not_lt_zero⟩
  rw [gaussNorm_one_add_X_eq_one]
  simp

/-- `unitRaySeries p` is distinguished of degree `0` at radius `1`. -/
theorem isDistinguished_unitRaySeries :
    TauCeti.PowerSeries.IsDistinguished 1 0 (unitRaySeries p) := by
  have h1d := isDistinguished_one_series (p := p)
  have hsub : (1 - unitRaySeries p).gaussNorm norm 1 < (1 : ℚ_[p]⟦X⟧).gaussNorm norm 1 := by
    have hrev : (1 - unitRaySeries p).gaussNorm norm 1 =
        (unitRaySeries p - 1).gaussNorm norm 1 := by
      simp_rw [PowerSeries.gaussNorm_eq, map_sub, norm_sub_rev]
    rw [hrev, gaussNorm_unitRaySeries_sub_one, gaussNorm_one_eq_one]
    exact inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  exact (TauCeti.PowerSeries.isDistinguished_iff_of_gaussNorm_sub_lt (R := ℚ_[p]) zero_le_one
    h1d.hasGaussNorm (TauCeti.PowerSeries.hasGaussNorm_of_isRestricted (R := ℚ_[p])
      isRestricted_unitRaySeries) hsub).mp h1d

/-- `unitRaySeries p` has lowest dominant degree `0` at radius `1`. -/
theorem isLowestDominant_unitRaySeries :
    TauCeti.PowerSeries.IsLowestDominant 1 0 (unitRaySeries p) :=
  isDistinguished_unitRaySeries.isLowestDominant_zero

/-- `perturbedUnitRaySeries p` is distinguished of degree `1` at radius `1`. -/
theorem isDistinguished_perturbedUnitRaySeries :
    TauCeti.PowerSeries.IsDistinguished 1 1 (perturbedUnitRaySeries p) := by
  have h1Xd := isDistinguished_one_add_X (p := p)
  have hsub : ((1 + X : ℚ_[p]⟦X⟧) - perturbedUnitRaySeries p).gaussNorm norm 1 <
      (1 + X : ℚ_[p]⟦X⟧).gaussNorm norm 1 := by
    have hrev : ((1 + X : ℚ_[p]⟦X⟧) - perturbedUnitRaySeries p).gaussNorm norm 1 =
        (perturbedUnitRaySeries p - (1 + X)).gaussNorm norm 1 := by
      simp_rw [PowerSeries.gaussNorm_eq, map_sub, norm_sub_rev]
    rw [hrev, gaussNorm_perturbedUnitRaySeries_sub_one_add_X, gaussNorm_one_add_X_eq_one]
    exact pow_lt_one₀ (by positivity)
      (inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)) (by decide)
  exact (TauCeti.PowerSeries.isDistinguished_iff_of_gaussNorm_sub_lt (R := ℚ_[p]) zero_le_one
    h1Xd.hasGaussNorm (TauCeti.PowerSeries.hasGaussNorm_of_isRestricted (R := ℚ_[p])
      isRestricted_perturbedUnitRaySeries) hsub).mp h1Xd

/-- `perturbedUnitRaySeries p` has lowest dominant degree `0` at radius `1`. -/
theorem isLowestDominant_perturbedUnitRaySeries :
    TauCeti.PowerSeries.IsLowestDominant 1 0 (perturbedUnitRaySeries p) := by
  have h1Xd := isDistinguished_one_add_X (p := p)
  have h1Xl := isLowestDominant_one_add_X (p := p)
  have hsub : ((1 + X : ℚ_[p]⟦X⟧) - perturbedUnitRaySeries p).gaussNorm norm 1 <
      (1 + X : ℚ_[p]⟦X⟧).gaussNorm norm 1 := by
    have hrev : ((1 + X : ℚ_[p]⟦X⟧) - perturbedUnitRaySeries p).gaussNorm norm 1 =
        (perturbedUnitRaySeries p - (1 + X)).gaussNorm norm 1 := by
      simp_rw [PowerSeries.gaussNorm_eq, map_sub, norm_sub_rev]
    rw [hrev, gaussNorm_perturbedUnitRaySeries_sub_one_add_X, gaussNorm_one_add_X_eq_one]
    exact pow_lt_one₀ (by positivity)
      (inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)) (by decide)
  exact (TauCeti.PowerSeries.isLowestDominant_iff_of_gaussNorm_sub_lt (R := ℚ_[p]) zero_le_one
    h1Xd.hasGaussNorm (TauCeti.PowerSeries.hasGaussNorm_of_isRestricted (R := ℚ_[p])
      isRestricted_perturbedUnitRaySeries) hsub).mp h1Xl

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
  rw [isRestricted_unitRaySeries.setOf_norm_le_and_evalAt_eq_zero zero_lt_one
    isDistinguished_unitRaySeries.ne_zero, zeroMultiset_unitRaySeries_padicComplex]
  simp

/-- By the nonarchimedean Rouché theorem on `‖x‖ ≤ 1`, `perturbedUnitRaySeries p` has the same
closed-disc zero count in `ℂ_[p]` as `1 + X`, namely `1`. -/
theorem card_zeroMultiset_perturbedUnitRaySeries_padicComplex :
    ((perturbedUnitRaySeries p).zeroMultiset 1 ℂ_[p]).card = 1 := by
  have hsub : (perturbedUnitRaySeries p - (1 + X)).gaussNorm norm 1 <
      (perturbedUnitRaySeries p).gaussNorm norm 1 := by
    have hgn : (perturbedUnitRaySeries p).gaussNorm norm 1 = 1 := by
      have h := (isLowestDominant_perturbedUnitRaySeries (p := p)).norm_coeff_mul_pow_eq.symm
      have hc0 : ‖coeff 0 (perturbedUnitRaySeries p)‖ * 1 ^ 0 = 1 := by simp
      rwa [hc0] at h
    rw [gaussNorm_perturbedUnitRaySeries_sub_one_add_X, hgn]
    exact pow_lt_one₀ (by positivity)
      (inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)) (by decide)
  rw [TauCeti.PowerSeries.card_zeroMultiset_eq_of_gaussNorm_sub_lt (L := ℂ_[p]) zero_lt_one
    isRestricted_perturbedUnitRaySeries isRestricted_one_add_X hsub]
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

/-- Because the normalised disc polynomial of `perturbedUnitRaySeries p` at `r = 1` over `ℚ_[p]`
has degree `1` and therefore splits over `ℚ_[p]`, `perturbedUnitRaySeries p` already has `1` zero
on the unit sphere `‖x‖ = 1` of `ℚ_[p]`, counted with multiplicity. -/
theorem card_filter_zeroMultiset_perturbedUnitRaySeries_norm_eq_one_padic :
    (((perturbedUnitRaySeries p).zeroMultiset 1 ℚ_[p]).filter (‖·‖ = 1)).card = 1 := by
  obtain ⟨P, U, hP⟩ := (isDistinguished_perturbedUnitRaySeries (p := p)).exists_isDiscPreparation
    zero_lt_one isRestricted_perturbedUnitRaySeries constantCoeff_perturbedUnitRaySeries
  have hs : (P.map (algebraMap ℚ_[p] ℚ_[p])).Splits :=
    Polynomial.Splits.of_natDegree_le_one (Polynomial.natDegree_map_le.trans hP.natDegree_eq.le)
  exact hP.card_filter_zeroMultiset_norm_eq_eq_of_splits
    isLowestDominant_perturbedUnitRaySeries zero_lt_one hs

/-- `perturbedUnitRaySeries p` has a unique zero in the closed unit disc of `ℚ_[p]`, and that zero
lies on the unit sphere `‖x‖ = 1`. -/
theorem existsUnique_norm_le_one_and_evalAt_perturbedUnitRaySeries_eq_zero :
    ∃! x : ℚ_[p], ‖x‖ ≤ 1 ∧ (perturbedUnitRaySeries p).evalAt x = 0 ∧ ‖x‖ = 1 := by
  classical
  obtain ⟨P, U, hP⟩ := (isDistinguished_perturbedUnitRaySeries (p := p)).exists_isDiscPreparation
    zero_lt_one isRestricted_perturbedUnitRaySeries constantCoeff_perturbedUnitRaySeries
  have hs : (P.map (algebraMap ℚ_[p] ℚ_[p])).Splits :=
    Polynomial.Splits.of_natDegree_le_one (Polynomial.natDegree_map_le.trans hP.natDegree_eq.le)
  have hcard1 : ((perturbedUnitRaySeries p).zeroMultiset 1 ℚ_[p]).card = 1 :=
    hP.card_zeroMultiset_eq_of_splits zero_lt_one hs
  have hsphere : (((perturbedUnitRaySeries p).zeroMultiset 1 ℚ_[p]).filter (‖·‖ = 1)).card = 1 :=
    card_filter_zeroMultiset_perturbedUnitRaySeries_norm_eq_one_padic
  obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp hcard1
  have hnorm : ‖a‖ = 1 := by
    rw [ha] at hsphere
    by_contra hne
    simp [Multiset.filter_singleton, hne] at hsphere
  have hset : {x : ℚ_[p] | ‖x‖ ≤ 1 ∧ (perturbedUnitRaySeries p).evalAt x = 0} = {a} := by
    rw [isRestricted_perturbedUnitRaySeries.setOf_norm_le_and_evalAt_eq_zero (L := ℚ_[p])
      zero_lt_one isDistinguished_perturbedUnitRaySeries.ne_zero, ha]
    simp
  refine ⟨a, ?_, fun y ⟨hy1, hy0, _⟩ => ?_⟩
  · have ha_mem : a ∈ {x : ℚ_[p] | ‖x‖ ≤ 1 ∧ (perturbedUnitRaySeries p).evalAt x = 0} := by
      simp [hset]
    exact ⟨ha_mem.1, ha_mem.2, hnorm⟩
  · have hy_mem : y ∈ {x : ℚ_[p] | ‖x‖ ≤ 1 ∧ (perturbedUnitRaySeries p).evalAt x = 0} :=
      ⟨hy1, hy0⟩
    simpa [hset] using hy_mem

end TauCeti.NewtonPolygonBoundaryZerosExample
