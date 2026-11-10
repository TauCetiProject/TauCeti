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
`‖x‖ < 1`, and `‖(u + t)⁻¹‖ ≤ ‖u⁻¹‖ / (1 - ‖u⁻¹‖ * ‖t‖)` for a unit `u` with
`‖u⁻¹‖ * ‖t‖ < 1`; in particular `(1 - w) * u + d` is a unit with
`‖((1 - w) * u + d)⁻¹‖ ≤ M / (1 - ‖w‖ - M * ‖d‖)` when `‖u⁻¹‖ ≤ M`, `‖w‖ < 1` and
`M * ‖d‖ < 1 - ‖w‖`.
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

/-- In a normed ring with summable geometric series, perturbing a unit `u` by `t`
with `‖u⁻¹‖ * ‖t‖ < 1` gives an element whose inverse has norm at most
`‖u⁻¹‖ / (1 - ‖u⁻¹‖ * ‖t‖)`. The perturbed element is a unit by `Units.oneSub`. -/
theorem norm_inverse_add_le (u : Rˣ) {t : R}
    (ht : ‖(↑u⁻¹ : R)‖ * ‖t‖ < 1) :
    ‖Ring.inverse (↑u + t)‖ ≤ ‖(↑u⁻¹ : R)‖ / (1 - ‖(↑u⁻¹ : R)‖ * ‖t‖) := by
  have hs : ‖-(↑u⁻¹ * t)‖ ≤ ‖(↑u⁻¹ : R)‖ * ‖t‖ := (norm_neg _).trans_le (norm_mul_le _ _)
  have hs₁ : ‖-(↑u⁻¹ * t)‖ < 1 := hs.trans_lt ht
  have key : (↑u + t : R) = ↑(u * Units.oneSub _ hs₁) := by simp [mul_add]
  set v : Rˣ := u * Units.oneSub _ hs₁
  have hy : (↑v⁻¹ : R) = ↑u⁻¹ - ↑u⁻¹ * t * ↑v⁻¹ := by
    calc (↑v⁻¹ : R) = ↑u⁻¹ * ↑u * ↑v⁻¹ := by simp
      _ = ↑u⁻¹ * (↑v - t) * ↑v⁻¹ := by rw [← key, add_sub_cancel_right]
      _ = ↑u⁻¹ - ↑u⁻¹ * t * ↑v⁻¹ := by simp [mul_sub, sub_mul, mul_assoc]
  have h1 : ‖(↑v⁻¹ : R)‖ ≤ ‖(↑u⁻¹ : R)‖ + ‖(↑u⁻¹ : R)‖ * ‖t‖ * ‖(↑v⁻¹ : R)‖ := by
    conv_lhs => rw [hy]
    refine (norm_sub_le _ _).trans ?_
    gcongr
    exact (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
  rw [key, Ring.inverse_unit, le_div_iff₀ (by linarith)]
  nlinarith

/-- Perturbing a unit `a` with `‖a⁻¹‖ ≤ M` to `(1 - w) * a + d`, where `‖w‖ < 1` and
`M * ‖d‖ < 1 - ‖w‖`, gives a unit whose inverse has norm at most `M / (1 - ‖w‖ - M * ‖d‖)`. -/
theorem isUnit_one_sub_mul_add_and_norm_inverse_le {a w d : R} {M : ℝ}
    (ha : IsUnit a) (hM : ‖Ring.inverse a‖ ≤ M) (hw : ‖w‖ < 1) (hd : M * ‖d‖ < 1 - ‖w‖) :
    IsUnit ((1 - w) * a + d) ∧
      ‖Ring.inverse ((1 - w) * a + d)‖ ≤ M / (1 - ‖w‖ - M * ‖d‖) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨isUnit_of_subsingleton _, by simpa [norm_of_subsingleton] using hM0⟩
  have hw₀ : 0 < 1 - ‖w‖ := by linarith
  obtain ⟨v, hv⟩ := IsUnit.one_sub_of_norm_lt_one hw
  obtain ⟨u, rfl⟩ := ha
  rw [Ring.inverse_unit] at hM
  have hN : ‖(↑(v * u)⁻¹ : R)‖ * (1 - ‖w‖) ≤ M := by
    set S := ∑' i : ℕ, (· * w)^[i] w
    have hvS : (↑v⁻¹ : R) = 1 + S := by
      have h1 : (↑v : R) * (1 + S) = 1 := by
        have := add_self_mul_geom_series hw
        calc (↑v : R) * (1 + S) = 1 + (S - (w + w * S)) := by rw [hv]; noncomm_ring
          _ = 1 := by rw [this, sub_self, add_zero]
      calc (↑v⁻¹ : R) = ↑v⁻¹ * (↑v * (1 + S)) := by rw [h1, mul_one]
        _ = 1 + S := by rw [← mul_assoc, Units.inv_mul, one_mul]
    have hS : ‖S‖ ≤ ‖w‖ / (1 - ‖w‖) := tsum_iterate_mul_le_of_norm_lt_one w hw
    have h : ‖(↑(v * u)⁻¹ : R)‖ ≤ M * (1 - ‖w‖)⁻¹ := by
      rw [mul_inv_rev, Units.val_mul, hvS, mul_add, mul_one]
      refine (norm_add_le _ _).trans ?_
      calc _ ≤ M + M * (‖w‖ / (1 - ‖w‖)) := by
            gcongr
            exact (norm_mul_le _ _).trans (by gcongr)
        _ = M * (1 - ‖w‖)⁻¹ := by field_simp; ring
    rwa [← div_eq_mul_inv, le_div_iff₀ hw₀] at h
  set N := ‖(↑(v * u)⁻¹ : R)‖
  have hNd : N * ‖d‖ < 1 := by nlinarith [norm_nonneg d, norm_nonneg w]
  have hkey : (1 - w) * ↑u + d = ↑(v * u) + d := by rw [Units.val_mul, hv]
  rw [hkey]
  refine ⟨?_, ?_⟩
  · have hpos := Units.norm_pos (v * u)⁻¹
    have h := ((v * u).add d (by rw [inv_eq_one_div, lt_div_iff₀ hpos, mul_comm]; exact hNd)).isUnit
    rwa [Units.val_add] at h
  · refine (norm_inverse_add_le (v * u) hNd).trans ?_
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [norm_nonneg d]

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
