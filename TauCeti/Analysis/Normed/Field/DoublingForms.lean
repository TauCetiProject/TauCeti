/-
Copyright (c) 2026 Tau Ceti Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Ring

/-!
# Quartic doubling forms and ultrametric norm preservation

For a ring element `c`, the pair of homogeneous quartic forms
`doublingForms c (u, v) = ((u ^ 2 - v ^ 2) ^ 2, u * v * (4 * u ^ 2 + c ^ 2 * u * v + 4 * v ^ 2))`
encodes the duplication map on the projective coordinates `(θ², σ²)` of the elliptic curve
`y² + c x y = x³ + x`. Over an ultrametric normed field `K` in which `c` is integral (`‖c‖ ≤ 1`)
and the discriminant `c ^ 4 - 64` is a unit (`‖c ^ 4 - 64‖ = 1`), the resultant identity
`(c ^ 4 - 64) u⁵ = (c² u - 8 v) Q(u, v) + ((c² u - 8 v)(c² u + 4 v) - 64 u²) u (u² - v²)`
shows that `doublingForms c` preserves the unit sphere and hence raises the maximum norm of any
pair `w : K × K` to the fourth power.

## Main definitions and results

* `TauCeti.doublingForms`: the pair of quartic forms of duplication for parameter `c`.
* `TauCeti.doublingForms_zero`, `TauCeti.doublingForms_smul`: zero evaluation and degree-`4`
  homogeneity over any commutative ring.
* `TauCeti.norm_lt_one_of_doublingForms_lt_one`: resultant step for the unit sphere.
* `TauCeti.norm_doublingForms_eq_one`: unit-sphere preservation under good reduction.
* `TauCeti.norm_doublingForms`: `‖doublingForms c w‖ = ‖w‖ ^ 4` for all `w : K × K`.

## Provenance

Adapted from `grh-lean` (<https://github.com/lsernau/grh-lean>, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), file `src/Lib/CM/Integrality/Doubling.lean`,
declarations `New.doublingForms`, `New.doublingForms_smul`, `New.norm_doublingForms_eq_one`, and
`New.norm_doublingForms`, generalized from `ℂ_[p]` to an arbitrary ultrametric normed field.
-/

@[expose] public section

namespace TauCeti

/-- The pair of quartic forms of duplication for the curve `y² + c x y = x³ + x`, sending
`(u, v)` to `((u ^ 2 - v ^ 2) ^ 2, u * v * (4 * u ^ 2 + c ^ 2 * u * v + 4 * v ^ 2))`. -/
def doublingForms {R : Type*} [CommRing R] (c : R) (w : R × R) : R × R :=
  ((w.fst ^ 2 - w.snd ^ 2) ^ 2,
    w.fst * w.snd * (4 * w.fst ^ 2 + c ^ 2 * w.fst * w.snd + 4 * w.snd ^ 2))

@[simp]
theorem doublingForms_zero {R : Type*} [CommRing R] (c : R) : doublingForms c 0 = 0 := by
  simp [doublingForms]

theorem doublingForms_smul {R : Type*} [CommRing R] (c a : R) (w : R × R) :
    doublingForms c (a • w) = a ^ 4 • doublingForms c w := by
  ext <;> simp [doublingForms] <;> ring

/-- Resultant step for `doublingForms`: if `‖c‖ ≤ 1`, `‖c ^ 4 - 64‖ = 1`, `‖u‖ ≤ 1`, `‖v‖ ≤ 1`,
and both `u ^ 2 - v ^ 2` and `u * v * (4 * u ^ 2 + c ^ 2 * u * v + 4 * v ^ 2)` have norm `< 1`,
then `‖u‖ < 1`. -/
theorem norm_lt_one_of_doublingForms_lt_one {K : Type*} [NormedField K] [IsUltrametricDist K]
    {c u v : K} (hc : ‖c‖ ≤ 1) (h_disc : ‖c ^ 4 - 64‖ = 1) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (h₀ : ‖u ^ 2 - v ^ 2‖ < 1) (h₁ : ‖u * v * (4 * u ^ 2 + c ^ 2 * u * v + 4 * v ^ 2)‖ < 1) :
    ‖u‖ < 1 := by
  let O : Subring K := (NormedField.valuation (K := K)).integer
  have hO {a : K} : a ∈ O ↔ ‖a‖ ≤ 1 := by simp [O, Valuation.mem_integer_iff, ← NNReal.coe_le_one]
  let x : K := c ^ 2 * u - 8 * v
  let y : K := (x * (c ^ 2 * u + 4 * v) - 64 * u ^ 2) * u
  have hx' : x ∈ O :=
    sub_mem (mul_mem (pow_mem (hO.mpr hc) 2) (hO.mpr hu)) (mul_mem (ofNat_mem O 8) (hO.mpr hv))
  have hy' : y ∈ O := mul_mem (sub_mem (mul_mem hx' (add_mem
    (mul_mem (pow_mem (hO.mpr hc) 2) (hO.mpr hu)) (mul_mem (ofNat_mem O 4) (hO.mpr hv))))
    (mul_mem (ofNat_mem O 64) (pow_mem (hO.mpr hu) 2))) (hO.mpr hu)
  have hx : ‖x‖ ≤ 1 := hO.mp hx'
  have hy : ‖y‖ ≤ 1 := hO.mp hy'
  have h_eq : (c ^ 4 - 64) * u ^ 5 =
      x * (u * v * (4 * u ^ 2 + c ^ 2 * u * v + 4 * v ^ 2)) + y * (u ^ 2 - v ^ 2) := by
    simp only [x, y]; ring
  have h_lt : ‖(c ^ 4 - 64) * u ^ 5‖ < 1 := by
    rw [h_eq]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans_lt h₁
    · rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) hy).trans_lt h₀
  rw [norm_mul, h_disc, one_mul, norm_pow] at h_lt
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg u) (by decide)).mp h_lt

/-- If `c` is integral and `c ^ 4 - 64` is a unit in an ultrametric normed field, then
`doublingForms c` preserves the unit sphere `‖w‖ = 1`. -/
theorem norm_doublingForms_eq_one {K : Type*} [NormedField K] [IsUltrametricDist K] {c : K}
    (hc : ‖c‖ ≤ 1) (h_disc : ‖c ^ 4 - 64‖ = 1) {w : K × K} (hw : ‖w‖ = 1) :
    ‖doublingForms c w‖ = 1 := by
  let O : Subring K := (NormedField.valuation (K := K)).integer
  have hO {a : K} : a ∈ O ↔ ‖a‖ ≤ 1 := by simp [O, Valuation.mem_integer_iff, ← NNReal.coe_le_one]
  obtain ⟨u, v⟩ := w
  have hu : ‖u‖ ≤ 1 := (norm_fst_le (u, v)).trans hw.le
  have hv : ‖v‖ ≤ 1 := (norm_snd_le (u, v)).trans hw.le
  have hc' : c ∈ O := hO.mpr hc
  have hu' : u ∈ O := hO.mpr hu
  have hv' : v ∈ O := hO.mpr hv
  refine le_antisymm (max_le ?_ ?_) (not_lt.mp fun h_lt ↦ ?_)
  · exact hO.mp (pow_mem (sub_mem (pow_mem hu' 2) (pow_mem hv' 2)) 2)
  · exact hO.mp (mul_mem (mul_mem hu' hv')
      (add_mem (add_mem (mul_mem (ofNat_mem O 4) (pow_mem hu' 2))
        (mul_mem (mul_mem (pow_mem hc' 2) hu') hv')) (mul_mem (ofNat_mem O 4) (pow_mem hv' 2))))
  · obtain ⟨h₀, h₁⟩ : ‖(u ^ 2 - v ^ 2) ^ 2‖ < 1 ∧
        ‖u * v * (4 * u ^ 2 + c ^ 2 * u * v + 4 * v ^ 2)‖ < 1 := max_lt_iff.mp h_lt
    rw [norm_pow, pow_lt_one_iff_of_nonneg (norm_nonneg _) two_ne_zero] at h₀
    have hu_lt := norm_lt_one_of_doublingForms_lt_one hc h_disc hu hv h₀ h₁
    have hv_lt := norm_lt_one_of_doublingForms_lt_one hc h_disc hv hu (by rwa [norm_sub_rev]) (by
      rwa [show v * u * (4 * v ^ 2 + c ^ 2 * v * u + 4 * u ^ 2) =
        u * v * (4 * u ^ 2 + c ^ 2 * u * v + 4 * v ^ 2) by ring])
    exact (max_lt hu_lt hv_lt).ne hw

/-- If `c` is integral and `c ^ 4 - 64` is a unit in an ultrametric normed field, then the quartic
duplication forms `doublingForms c` raise the maximum norm of any pair to the fourth power. -/
theorem norm_doublingForms {K : Type*} [NormedField K] [IsUltrametricDist K] {c : K}
    (hc : ‖c‖ ≤ 1) (h_disc : ‖c ^ 4 - 64‖ = 1) (w : K × K) :
    ‖doublingForms c w‖ = ‖w‖ ^ 4 := by
  obtain ⟨a, ha⟩ : ∃ a : K, ‖w‖ = ‖a‖ :=
    (max_choice ‖w.fst‖ ‖w.snd‖).elim (fun h ↦ ⟨w.fst, h⟩) (fun h ↦ ⟨w.snd, h⟩)
  obtain rfl | ha_ne := eq_or_ne a 0
  · obtain rfl : w = 0 := by simpa using ha
    simp
  · have h_unit : ‖a⁻¹ • w‖ = 1 := by simp [norm_smul, ha, ha_ne]
    calc ‖doublingForms c w‖ = ‖doublingForms c (a • a⁻¹ • w)‖ := by rw [smul_inv_smul₀ ha_ne]
      _ = ‖a‖ ^ 4 * ‖doublingForms c (a⁻¹ • w)‖ := by rw [doublingForms_smul, norm_smul, norm_pow]
      _ = ‖w‖ ^ 4 := by rw [norm_doublingForms_eq_one hc h_disc h_unit, mul_one, ha]

end TauCeti
