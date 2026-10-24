/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.RingTheory.Jacobson.Radical

/-!
# Units and the Jacobson radical of normed rings

In a normed ring with summable geometric series, `Ring.inverse` is continuous at every unit
(`NormedRing.inverse_continuousAt`), but it jumps to `0` at the boundary of the open set of units.
When the nonunits also form an open set, as in a complete discretely valued ring such as `ℤ_p`,
there is no such boundary and `Ring.inverse` is continuous everywhere.

The Neumann series also gives explicit bounds: `‖(1 - x)⁻¹‖ ≤ ‖1‖ - 1 + (1 - ‖x‖)⁻¹` when
`‖x‖ < 1`, and, when `‖1‖ = 1`, `‖(u + t)⁻¹‖ ≤ ‖u⁻¹‖ / (1 - ‖u⁻¹‖ * ‖t‖)` for a unit `u` with
`‖u⁻¹‖ * ‖t‖ < 1`; in particular `(1 - w) * u + d` is a unit with
`‖((1 - w) * u + d)⁻¹‖ ≤ 4 M` when `‖u⁻¹‖ ≤ M`, `‖w‖ ≤ 1 / 2` and `‖d‖ * (2 * M) ≤ 1 / 2`.
Mathlib records these inverses only through asymptotic `O`-bounds such as
`NormedRing.inverse_add_norm`; the explicit constants are needed for inductive constructions
that perturb a unit infinitely often, such as Cohen–Hewitt factorization.

The Jacobson radical is closed, as an intersection of maximal left ideals, using
Mathlib's `Ring.jacobson_eq_sInf_isMaximal` and `Ideal.IsMaximal.isClosed`.
See Dales, *Banach Algebras and Automatic Continuity*, §§1.3–1.5.
-/

public section

namespace NormedRing

variable {R : Type*} [NormedRing R] [HasSummableGeomSeries R]

/-- If the nonunits of a normed ring with summable geometric series form an open set, then
`Ring.inverse` is continuous: it is continuous at every unit, and locally zero at every nonunit. -/
theorem continuous_inverse_of_isOpen_nonunits (h : IsOpen (nonunits R)) :
    Continuous (Ring.inverse : R → R) := by
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    exact inverse_continuousAt u
  · have hx' : Ring.inverse =ᶠ[nhds x] fun _ ↦ (0 : R) :=
      Filter.mem_of_superset (h.mem_nhds hx) fun y hy ↦ Ring.inverse_non_unit y hy
    exact continuousAt_const.congr hx'.symm

/-- The Neumann-series bound for the inverse of `1 - x` when `‖x‖ < 1`. The identity need not have
norm one; when it does, the bound reads `‖(1 - x)⁻¹‖ ≤ (1 - ‖x‖)⁻¹`. -/
theorem norm_inverse_one_sub_le {x : R} (hx : ‖x‖ < 1) :
    ‖Ring.inverse (1 - x)‖ ≤ ‖(1 : R)‖ - 1 + (1 - ‖x‖)⁻¹ := by
  rw [inverse_one_sub x hx]
  exact tsum_geometric_le_of_norm_lt_one x hx

/-- In a normed ring with `‖1‖ = 1` and summable geometric series, perturbing a unit `u` by `t`
with `‖u⁻¹‖ * ‖t‖ < 1` gives an element whose inverse has norm at most
`‖u⁻¹‖ / (1 - ‖u⁻¹‖ * ‖t‖)`. The perturbed element is a unit by `Units.add`. -/
theorem norm_inverse_add_le [NormOneClass R] (u : Rˣ) {t : R}
    (ht : ‖(↑u⁻¹ : R)‖ * ‖t‖ < 1) :
    ‖Ring.inverse (↑u + t)‖ ≤ ‖(↑u⁻¹ : R)‖ / (1 - ‖(↑u⁻¹ : R)‖ * ‖t‖) := by
  have hs : ‖-(↑u⁻¹ * t)‖ ≤ ‖(↑u⁻¹ : R)‖ * ‖t‖ := (norm_neg _).trans_le (norm_mul_le _ _)
  have hs₁ : ‖-(↑u⁻¹ * t)‖ < 1 := hs.trans_lt ht
  have hv : ‖Ring.inverse (1 - -(↑u⁻¹ * t))‖ ≤ (1 - ‖(↑u⁻¹ : R)‖ * ‖t‖)⁻¹ := by
    refine (norm_inverse_one_sub_le hs₁).trans ?_
    rw [norm_one, sub_self, zero_add]
    gcongr
  rw [inverse_one_sub _ hs₁] at hv
  have key : (↑u + t : R) = ↑(u * Units.oneSub _ hs₁) := by simp [mul_add]
  rw [key, Ring.inverse_unit, mul_inv_rev, Units.val_mul, div_eq_inv_mul]
  exact (norm_mul_le _ _).trans (by gcongr)

/-- A halving form of the perturbation bounds, for constructions that perturb a unit repeatedly:
if `‖a⁻¹‖ ≤ M`, `‖w‖ ≤ 1 / 2` and `‖d‖ * (2 * M) ≤ 1 / 2`, then `(1 - w) * a + d` is a unit
whose inverse has norm at most `4 * M`. -/
theorem isUnit_one_sub_mul_add_and_norm_inverse_le [NormOneClass R] {a w d : R} {M : ℝ}
    (ha : IsUnit a) (hM : ‖Ring.inverse a‖ ≤ M) (hw : ‖w‖ ≤ 1 / 2)
    (hd : ‖d‖ * (2 * M) ≤ 1 / 2) :
    IsUnit ((1 - w) * a + d) ∧ ‖Ring.inverse ((1 - w) * a + d)‖ ≤ 4 * M := by
  have := NormOneClass.nontrivial (G := R)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have hw₁ : ‖w‖ < 1 := by linarith
  obtain ⟨v, hv⟩ := IsUnit.one_sub_of_norm_lt_one hw₁
  have hvn : ‖(↑v⁻¹ : R)‖ ≤ 2 := by
    rw [← Ring.inverse_unit, hv]
    refine (norm_inverse_one_sub_le hw₁).trans ?_
    rw [norm_one, sub_self, zero_add]
    exact inv_le_of_inv_le₀ (by norm_num) (by linarith)
  obtain ⟨u, rfl⟩ := ha
  rw [Ring.inverse_unit] at hM
  have hvu : ‖(↑(v * u)⁻¹ : R)‖ ≤ 2 * M := by
    rw [mul_inv_rev, Units.val_mul]
    calc _ ≤ ‖(↑u⁻¹ : R)‖ * ‖(↑v⁻¹ : R)‖ := norm_mul_le _ _
      _ ≤ M * 2 := by gcongr
      _ = 2 * M := mul_comm _ _
  have hd' : ‖(↑(v * u)⁻¹ : R)‖ * ‖d‖ ≤ 1 / 2 := by nlinarith [norm_nonneg d]
  have hkey : (1 - w) * ↑u + d = ↑(v * u) + d := by rw [Units.val_mul, hv]
  rw [hkey]
  refine ⟨?_, ?_⟩
  · have hpos := Units.norm_pos (v * u)⁻¹
    have h := ((v * u).add d (by rw [inv_eq_one_div, lt_div_iff₀ hpos]; linarith)).isUnit
    rwa [Units.val_add] at h
  · refine (norm_inverse_add_le (v * u) (by linarith)).trans ?_
    calc _ ≤ 2 * M / (1 / 2) := div_le_div₀ (by positivity) hvu (by norm_num) (by linarith)
      _ = 4 * M := by ring

end NormedRing

namespace TauCeti.Ring

/-- The Jacobson radical of a normed ring with summable geometric series is closed. -/
theorem isClosed_jacobson (A : Type*) [NormedRing A] [HasSummableGeomSeries A] :
    IsClosed (Ring.jacobson A : Set A) := by
  rw [Ring.jacobson_eq_sInf_isMaximal, Submodule.coe_sInf]
  exact isClosed_biInter fun I hI => by
    have : Ideal.IsMaximal I := hI
    exact Ideal.IsMaximal.isClosed

end TauCeti.Ring
