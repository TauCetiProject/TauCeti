/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.ClosedDisc

/-!
# The closed unit disc with Cayley charts centred at boundary points

The closed unit disc `Complex.UnitClosedDisc` is a Riemann surface with boundary whose atlas
consists of the Cayley charts `Complex.UnitClosedDisc.cayleyChart ζ`, `z ↦ I (ζ - z) / (ζ + z)`,
one for each point `ζ` of the unit circle. Its preferred chart at a point uses only `ζ = ±1`. The
type synonym `TauCeti.CentredClosedDisc` carries the same atlas but a different choice of
preferred charts: at a point `ζ` of the unit circle it is the Cayley chart centred at `ζ`, which
sends `ζ` to `0`, and at an interior point it is the preferred chart of `𝕔𝔻`. So finite bundle
atlases over `TauCeti.CentredClosedDisc` can use the Cayley chart centred at any boundary point,
as in the half-disc charts of `TauCeti.CentredClosedDisc.cayleyChart_image_setOf_lt`.

The Cayley chart centred at `ζ` maps the points `z` of the closed disc with
`‖ζ - z‖ < r ‖ζ + z‖` onto the half-disc `D⁺_r = {w : ‖w‖ < r, 0 ≤ im w}`
(`TauCeti.CentredClosedDisc.cayleyChart_image_setOf_lt`), since `‖I (ζ - z) / (ζ + z)‖` is
`‖ζ - z‖ / ‖ζ + z‖`.

## Main declarations

* `TauCeti.CentredClosedDisc`: the closed unit disc with the Cayley charts centred at boundary
  points as preferred charts.
* `TauCeti.CentredClosedDisc.instHasGroupoid`: it is a Riemann surface with boundary, with the
  same atlas as `Complex.UnitClosedDisc` (`TauCeti.CentredClosedDisc.mem_atlas_iff`).
* `TauCeti.CentredClosedDisc.chartAt_of_norm_eq_one`: at a point `ζ` of the unit circle, the
  preferred chart is the Cayley chart centred at `ζ`.
* `TauCeti.CentredClosedDisc.cayleyChart_image_setOf_lt`: half-disc chart images.
-/

public section

noncomputable section

open Set Complex Complex.UnitClosedDisc
open scoped Manifold Complex.UnitDisc

namespace TauCeti

/-- The closed unit disc with the Cayley charts centred at boundary points as preferred charts:
a type synonym for `Complex.UnitClosedDisc` with the same topology and atlas. -/
@[expose] def CentredClosedDisc : Type := 𝕔𝔻

namespace CentredClosedDisc

instance : TopologicalSpace CentredClosedDisc := inferInstanceAs (TopologicalSpace 𝕔𝔻)

instance : CompactSpace CentredClosedDisc := inferInstanceAs (CompactSpace 𝕔𝔻)

instance : T2Space CentredClosedDisc := inferInstanceAs (T2Space 𝕔𝔻)

/-- A point of the closed disc as a point of `TauCeti.CentredClosedDisc`. -/
@[expose] def ofDisc : 𝕔𝔻 ≃ CentredClosedDisc := Equiv.refl _

/-- A point of `TauCeti.CentredClosedDisc` as a point of `ℂ`. -/
@[coe, expose] def toComplex (z : CentredClosedDisc) : ℂ := ((ofDisc.symm z : 𝕔𝔻) : ℂ)

instance : CoeOut CentredClosedDisc ℂ := ⟨toComplex⟩

theorem continuous_coe : Continuous ((↑) : CentredClosedDisc → ℂ) :=
  Complex.UnitClosedDisc.continuous_coe

theorem norm_le_one (z : CentredClosedDisc) : ‖(z : ℂ)‖ ≤ 1 :=
  (ofDisc.symm z).norm_le_one

/-- The point of `TauCeti.CentredClosedDisc` with coordinate `z`, for `‖z‖ ≤ 1`. -/
def mk (z : ℂ) (hz : ‖z‖ ≤ 1) : CentredClosedDisc := ofDisc (Complex.UnitClosedDisc.mk z hz)

@[simp]
theorem coe_mk (z : ℂ) (hz : ‖z‖ ≤ 1) : (mk z hz : ℂ) = z :=
  Complex.UnitClosedDisc.coe_mk z hz

/-- The centre of the preferred Cayley chart at `z`: `z` itself on the unit circle, and the
centre `Complex.UnitClosedDisc.chartCenter z` of the preferred chart of `𝕔𝔻` otherwise. -/
def centre (z : CentredClosedDisc) : ℂ :=
  open Classical in if ‖(z : ℂ)‖ = 1 then z else chartCenter (ofDisc.symm z)

theorem norm_centre (z : CentredClosedDisc) : ‖centre z‖ = 1 := by
  rw [centre]
  split_ifs with h
  exacts [h, norm_chartCenter _]

/-- At a point of the unit circle, the preferred chart is centred at that point. -/
theorem centre_of_norm_eq_one {z : CentredClosedDisc} (hz : ‖(z : ℂ)‖ = 1) : centre z = z := by
  simp [centre, hz]

/-- At `0` the preferred chart is centred at `1`. -/
@[simp]
theorem centre_mk_zero : centre (mk 0 (by simp)) = 1 := by
  have h0 : ((mk 0 (by simp) : CentredClosedDisc) : ℂ) = 0 := coe_mk _ _
  have h0' : ((ofDisc.symm (mk 0 (by simp)) : 𝕔𝔻) : ℂ) = 0 := h0
  simp [centre, chartCenter_def, h0, h0']

theorem coe_ne_neg_centre (z : CentredClosedDisc) : (z : ℂ) ≠ -centre z := by
  rw [centre]
  split_ifs with h
  · intro hz
    have : (z : ℂ) = 0 := by linear_combination hz / 2
    rw [this, norm_zero] at h
    exact zero_ne_one h
  · exact coe_ne_neg_chartCenter _

/-- The Cayley chart centred at `ζ`, on `TauCeti.CentredClosedDisc`. -/
@[expose] def cayleyChart (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    OpenPartialHomeomorph CentredClosedDisc ClosedUpperHalfPlane :=
  Complex.UnitClosedDisc.cayleyChart ζ hζ

@[simp]
theorem coe_cayleyChart_apply {ζ : ℂ} {hζ : ‖ζ‖ = 1} (z : CentredClosedDisc) :
    (cayleyChart ζ hζ z : ℂ) = I * (ζ - z) / (ζ + z) :=
  Complex.UnitClosedDisc.coe_cayleyChart_apply _

@[simp]
theorem cayleyChart_source {ζ : ℂ} {hζ : ‖ζ‖ = 1} :
    (cayleyChart ζ hζ).source = {z : CentredClosedDisc | (z : ℂ) ≠ -ζ} :=
  Complex.UnitClosedDisc.cayleyChart_source

@[simp]
theorem cayleyChart_target {ζ : ℂ} {hζ : ‖ζ‖ = 1} : (cayleyChart ζ hζ).target = univ :=
  Complex.UnitClosedDisc.cayleyChart_target

/-- The closed unit disc with the Cayley charts as atlas, the preferred chart at `z` being centred
at `TauCeti.CentredClosedDisc.centre z`. -/
instance instChartedSpace : ChartedSpace ClosedUpperHalfPlane CentredClosedDisc where
  atlas := {e | ∃ (ζ : ℂ) (hζ : ‖ζ‖ = 1), e = cayleyChart ζ hζ}
  chartAt z := cayleyChart (centre z) (norm_centre z)
  mem_chart_source z := by rw [cayleyChart_source]; exact coe_ne_neg_centre z
  chart_mem_atlas _ := ⟨_, _, rfl⟩

theorem chartAt_eq (z : CentredClosedDisc) :
    chartAt ClosedUpperHalfPlane z = cayleyChart (centre z) (norm_centre z) :=
  (rfl)

/-- At a point `ζ` of the unit circle, the preferred chart is the Cayley chart centred at `ζ`. -/
theorem chartAt_of_norm_eq_one {z : CentredClosedDisc} (hz : ‖(z : ℂ)‖ = 1) :
    chartAt ClosedUpperHalfPlane z = cayleyChart z hz := by
  rw [chartAt_eq]
  congr 1
  simp [centre, hz]

/-- The charts of the atlas are the Cayley charts, as for `Complex.UnitClosedDisc`. -/
theorem mem_atlas_iff {e : OpenPartialHomeomorph CentredClosedDisc ClosedUpperHalfPlane} :
    e ∈ atlas ClosedUpperHalfPlane CentredClosedDisc ↔
      ∃ (ζ : ℂ) (hζ : ‖ζ‖ = 1), e = cayleyChart ζ hζ :=
  Iff.rfl

/-- The closed disc with Cayley charts centred at boundary points is a Riemann surface with
boundary. -/
instance instHasGroupoid : HasGroupoid CentredClosedDisc borderedHolomorphicGroupoid where
  compatible := by
    rintro _ _ ⟨ζ, hζ, rfl⟩ ⟨ζ', hζ', rfl⟩
    exact cayleyChart_symm_trans_mem_borderedHolomorphicGroupoid ζ ζ' hζ hζ'

/-- **Half-disc charts.** The Cayley chart centred at `ζ` maps the points `z` of the closed disc
with `‖ζ - z‖ < r ‖ζ + z‖` onto the half-disc `{w : ‖w‖ < r}` of the closed upper half-plane. -/
theorem cayleyChart_image_setOf_lt {ζ : ℂ} (hζ : ‖ζ‖ = 1) (r : ℝ) :
    cayleyChart ζ hζ '' {z | ‖ζ - z‖ < r * ‖ζ + z‖} =
      {w : ClosedUpperHalfPlane | ‖(w : ℂ)‖ < r} := by
  have hset : {z : CentredClosedDisc | ‖ζ - z‖ < r * ‖ζ + z‖} =
      (cayleyChart ζ hζ).source ∩ cayleyChart ζ hζ ⁻¹' {w | ‖(w : ℂ)‖ < r} := by
    ext z
    simp only [mem_ofPred_eq, mem_inter_iff, cayleyChart_source, mem_preimage,
      coe_cayleyChart_apply]
    constructor
    · intro h
      have hz : (z : ℂ) ≠ -ζ := fun hz ↦ by
        rw [hz, sub_neg_eq_add, add_neg_cancel, norm_zero, mul_zero] at h
        exact (norm_nonneg _).not_gt h
      have hpos : 0 < ‖ζ + z‖ := norm_pos_iff.2 fun h0 ↦ hz (eq_neg_of_add_eq_zero_right h0)
      refine ⟨hz, ?_⟩
      rwa [norm_div, norm_mul, norm_I, one_mul, div_lt_iff₀ hpos]
    · rintro ⟨hz, h⟩
      have hpos : 0 < ‖ζ + z‖ := norm_pos_iff.2 fun h0 ↦ hz (eq_neg_of_add_eq_zero_right h0)
      rwa [norm_div, norm_mul, norm_I, one_mul, div_lt_iff₀ hpos] at h
  rw [hset]
  ext w
  have hwt : w ∈ (cayleyChart ζ hζ).target := by rw [cayleyChart_target]; exact mem_univ w
  refine ⟨fun ⟨_, ⟨_, h⟩, hzw⟩ ↦ hzw ▸ h, fun hw ↦ ⟨(cayleyChart ζ hζ).symm w,
    ⟨(cayleyChart ζ hζ).map_target hwt, ?_⟩, (cayleyChart ζ hζ).right_inv hwt⟩⟩
  rwa [mem_preimage, (cayleyChart ζ hζ).right_inv hwt]

end CentredClosedDisc

end TauCeti
