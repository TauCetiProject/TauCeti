/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.ClosedDisc

/-!
# The closed unit disc with Cayley charts centered at boundary points

The closed unit disc `Complex.UnitClosedDisc` is a Riemann surface with boundary whose atlas
consists of the Cayley charts `Complex.UnitClosedDisc.cayleyChart ζ`, `z ↦ I (ζ - z) / (ζ + z)`,
one for each point `ζ` of the unit circle. Its preferred chart at a point uses only `ζ = ±1`. The
type synonym `TauCeti.CenteredClosedDisc` carries the same atlas but a different choice of
preferred charts: at a point `ζ` of the unit circle it is the Cayley chart centered at `ζ`, which
sends `ζ` to `0`, and at an interior point it is the preferred chart of `𝕔𝔻`. So finite bundle
atlases over `TauCeti.CenteredClosedDisc` can use the Cayley chart centered at any boundary point,
as in the half-disc charts of `TauCeti.CenteredClosedDisc.cayleyChart_image_halfDiscDom`.

The Cayley chart centered at `ζ` maps the points `z` of the closed disc with
`‖ζ - z‖ < r ‖ζ + z‖` onto the half-disc `D⁺_r = {w : ‖w‖ < r, 0 ≤ im w}`
(`Complex.UnitClosedDisc.cayleyChart_image_setOf_lt`), since `‖I (ζ - z) / (ζ + z)‖` is
`‖ζ - z‖ / ‖ζ + z‖`.

## Main declarations

* `TauCeti.CenteredClosedDisc`: the closed unit disc with the Cayley charts centered at boundary
  points as preferred charts.
* `TauCeti.CenteredClosedDisc.instHasGroupoid`: it is a Riemann surface with boundary, with the
  same atlas as `Complex.UnitClosedDisc` (`TauCeti.CenteredClosedDisc.mem_atlas_iff`).
* `TauCeti.CenteredClosedDisc.chartAt_of_norm_eq_one`: at a point `ζ` of the unit circle, the
  preferred chart is the Cayley chart centered at `ζ`.
* `TauCeti.CenteredClosedDisc.halfDiscDom`,
  `TauCeti.CenteredClosedDisc.cayleyChart_image_halfDiscDom`: half-disc chart domains and their
  images.
-/

public section

noncomputable section

open Set Complex Complex.UnitClosedDisc
open scoped Manifold Complex.UnitDisc

namespace TauCeti

/-- The closed unit disc with the Cayley charts centered at boundary points as preferred charts:
a type synonym for `Complex.UnitClosedDisc` with the same topology and atlas. -/
@[expose] def CenteredClosedDisc : Type := 𝕔𝔻

namespace CenteredClosedDisc

instance : TopologicalSpace CenteredClosedDisc := inferInstanceAs (TopologicalSpace 𝕔𝔻)

instance : CompactSpace CenteredClosedDisc := inferInstanceAs (CompactSpace 𝕔𝔻)

instance : T2Space CenteredClosedDisc := inferInstanceAs (T2Space 𝕔𝔻)

/-- A point of the closed disc as a point of `TauCeti.CenteredClosedDisc`. -/
def ofDisc : 𝕔𝔻 ≃ CenteredClosedDisc := Equiv.refl _

/-- A point of `TauCeti.CenteredClosedDisc` as a point of `ℂ`. -/
@[coe] def toComplex (z : CenteredClosedDisc) : ℂ := ((ofDisc.symm z : 𝕔𝔻) : ℂ)

instance : CoeOut CenteredClosedDisc ℂ := ⟨toComplex⟩

@[simp]
theorem coe_ofDisc (z : 𝕔𝔻) : ((ofDisc z : CenteredClosedDisc) : ℂ) = z :=
  (rfl)

@[simp]
theorem coe_ofDisc_symm (z : CenteredClosedDisc) : ((ofDisc.symm z : 𝕔𝔻) : ℂ) = z :=
  (rfl)

theorem continuous_coe : Continuous ((↑) : CenteredClosedDisc → ℂ) :=
  Complex.UnitClosedDisc.continuous_coe

theorem norm_le_one (z : CenteredClosedDisc) : ‖(z : ℂ)‖ ≤ 1 := by
  rw [← coe_ofDisc_symm]
  exact (ofDisc.symm z).norm_le_one

theorem coe_injective : Function.Injective ((↑) : CenteredClosedDisc → ℂ) := fun z w h ↦
  ofDisc.symm.injective (Complex.UnitClosedDisc.coe_injective (by simpa using h))

@[simp, norm_cast]
theorem coe_inj {z w : CenteredClosedDisc} : (z : ℂ) = w ↔ z = w :=
  coe_injective.eq_iff

@[ext]
theorem ext {z w : CenteredClosedDisc} (h : (z : ℂ) = w) : z = w :=
  coe_injective h

/-- The point of `TauCeti.CenteredClosedDisc` with coordinate `z`, for `‖z‖ ≤ 1`. -/
def mk (z : ℂ) (hz : ‖z‖ ≤ 1) : CenteredClosedDisc := ofDisc (Complex.UnitClosedDisc.mk z hz)

@[simp]
theorem coe_mk (z : ℂ) (hz : ‖z‖ ≤ 1) : (mk z hz : ℂ) = z := by
  rw [mk, coe_ofDisc, Complex.UnitClosedDisc.coe_mk]

@[simp]
theorem mk_coe (z : CenteredClosedDisc) (hz : ‖(z : ℂ)‖ ≤ 1 := norm_le_one z) : mk z hz = z :=
  ext (coe_mk _ _)

/-- The center of the preferred Cayley chart at `z`: `z` itself on the unit circle, and the
center `Complex.UnitClosedDisc.chartCenter z` of the preferred chart of `𝕔𝔻` otherwise. -/
def chartCenter (z : CenteredClosedDisc) : ℂ :=
  open Classical in
  if ‖(z : ℂ)‖ = 1 then z else Complex.UnitClosedDisc.chartCenter (ofDisc.symm z)

/-- The defining formula of `TauCeti.CenteredClosedDisc.chartCenter`. -/
theorem chartCenter_def (z : CenteredClosedDisc) :
    chartCenter z = open Classical in
      if ‖(z : ℂ)‖ = 1 then (z : ℂ) else Complex.UnitClosedDisc.chartCenter (ofDisc.symm z) :=
  (rfl)

/-- At a point off the unit circle, the preferred chart is that of `𝕔𝔻`. -/
theorem chartCenter_of_norm_ne_one {z : CenteredClosedDisc} (hz : ‖(z : ℂ)‖ ≠ 1) :
    chartCenter z = Complex.UnitClosedDisc.chartCenter (ofDisc.symm z) := by
  simp [chartCenter_def, hz]

/-- The center of the preferred chart lies on the unit circle. -/
@[simp]
theorem norm_chartCenter (z : CenteredClosedDisc) : ‖chartCenter z‖ = 1 := by
  rw [chartCenter_def]
  split_ifs with h
  exacts [h, Complex.UnitClosedDisc.norm_chartCenter _]

/-- At a point of the unit circle, the preferred chart is centered at that point. -/
theorem chartCenter_of_norm_eq_one {z : CenteredClosedDisc} (hz : ‖(z : ℂ)‖ = 1) :
    chartCenter z = z := by
  simp [chartCenter_def, hz]

/-- At `0` the preferred chart is centered at `1`. -/
@[simp]
theorem chartCenter_mk_zero : chartCenter (mk 0 (by simp)) = 1 := by
  rw [chartCenter_of_norm_ne_one (by simp), Complex.UnitClosedDisc.chartCenter_def]
  simp [mk]

theorem coe_ne_neg_chartCenter (z : CenteredClosedDisc) : (z : ℂ) ≠ -chartCenter z := by
  by_cases h : ‖(z : ℂ)‖ = 1
  · rw [chartCenter_of_norm_eq_one h]
    intro hz
    have : (z : ℂ) = 0 := by linear_combination hz / 2
    simp [this] at h
  · rw [chartCenter_of_norm_ne_one h, ← coe_ofDisc_symm]
    exact Complex.UnitClosedDisc.coe_ne_neg_chartCenter _

/-- The Cayley chart centered at `ζ`, on `TauCeti.CenteredClosedDisc`. -/
def cayleyChart (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    OpenPartialHomeomorph CenteredClosedDisc ClosedUpperHalfPlane :=
  Complex.UnitClosedDisc.cayleyChart ζ hζ

@[simp]
theorem coe_cayleyChart_apply {ζ : ℂ} {hζ : ‖ζ‖ = 1} (z : CenteredClosedDisc) :
    (cayleyChart ζ hζ z : ℂ) = I * (ζ - z) / (ζ + z) :=
  Complex.UnitClosedDisc.coe_cayleyChart_apply _

/-- The inverse of a Cayley chart is `w ↦ ζ (I - w) / (w + I)`. -/
@[simp]
theorem coe_cayleyChart_symm_apply {ζ : ℂ} {hζ : ‖ζ‖ = 1} (w : ClosedUpperHalfPlane) :
    ((cayleyChart ζ hζ).symm w : ℂ) = ζ * (I - w) / (w + I) :=
  Complex.UnitClosedDisc.coe_cayleyChart_symm_apply _

@[simp]
theorem cayleyChart_source {ζ : ℂ} {hζ : ‖ζ‖ = 1} :
    (cayleyChart ζ hζ).source = {z : CenteredClosedDisc | (z : ℂ) ≠ -ζ} :=
  Complex.UnitClosedDisc.cayleyChart_source

@[simp]
theorem cayleyChart_target {ζ : ℂ} {hζ : ‖ζ‖ = 1} : (cayleyChart ζ hζ).target = univ :=
  Complex.UnitClosedDisc.cayleyChart_target

/-- The image of a point under a Cayley chart has positive imaginary part exactly when the point
lies in the open unit disc (`Complex.UnitClosedDisc.im_cayleyChart_pos_iff`). -/
theorem im_cayleyChart_pos_iff {ζ : ℂ} {hζ : ‖ζ‖ = 1} {z : CenteredClosedDisc} :
    0 < (cayleyChart ζ hζ z : ℂ).im ↔ ‖(z : ℂ)‖ < 1 :=
  -- `CenteredClosedDisc` and its `cayleyChart` are by definition `𝕔𝔻` and its Cayley chart.
  Complex.UnitClosedDisc.im_cayleyChart_pos_iff

/-- The closed unit disc with the Cayley charts as atlas, the preferred chart at `z` being centered
at `TauCeti.CenteredClosedDisc.chartCenter z`. -/
instance instChartedSpace : ChartedSpace ClosedUpperHalfPlane CenteredClosedDisc where
  atlas := {e | ∃ (ζ : ℂ) (hζ : ‖ζ‖ = 1), e = cayleyChart ζ hζ}
  chartAt z := cayleyChart (chartCenter z) (norm_chartCenter z)
  mem_chart_source z := by rw [cayleyChart_source]; exact coe_ne_neg_chartCenter z
  chart_mem_atlas _ := ⟨_, _, rfl⟩

theorem chartAt_eq (z : CenteredClosedDisc) :
    chartAt ClosedUpperHalfPlane z = cayleyChart (chartCenter z) (norm_chartCenter z) :=
  (rfl)

/-- The preferred chart at `z` is the Cayley chart centered at `ζ` whenever `chartCenter z = ζ`. -/
theorem chartAt_eq_cayleyChart {z : CenteredClosedDisc} {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (h : chartCenter z = ζ) : chartAt ClosedUpperHalfPlane z = cayleyChart ζ hζ := by
  subst h
  rfl

/-- At a point `ζ` of the unit circle, the preferred chart is the Cayley chart centered at `ζ`. -/
theorem chartAt_of_norm_eq_one {z : CenteredClosedDisc} (hz : ‖(z : ℂ)‖ = 1) :
    chartAt ClosedUpperHalfPlane z = cayleyChart z hz :=
  chartAt_eq_cayleyChart hz (chartCenter_of_norm_eq_one hz)

/-- The charts of the atlas are the Cayley charts, as for `Complex.UnitClosedDisc`. -/
theorem mem_atlas_iff {e : OpenPartialHomeomorph CenteredClosedDisc ClosedUpperHalfPlane} :
    e ∈ atlas ClosedUpperHalfPlane CenteredClosedDisc ↔
      ∃ (ζ : ℂ) (hζ : ‖ζ‖ = 1), e = cayleyChart ζ hζ :=
  Iff.rfl

/-- Every Cayley chart belongs to the atlas. -/
@[simp]
theorem cayleyChart_mem_atlas (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    cayleyChart ζ hζ ∈ atlas ClosedUpperHalfPlane CenteredClosedDisc :=
  mem_atlas_iff.2 ⟨ζ, hζ, rfl⟩

/-- The closed disc with Cayley charts centered at boundary points is a Riemann surface with
boundary. -/
instance instHasGroupoid : HasGroupoid CenteredClosedDisc borderedHolomorphicGroupoid where
  compatible := by
    rintro _ _ ⟨ζ, hζ, rfl⟩ ⟨ζ', hζ', rfl⟩
    exact cayleyChart_symm_trans_mem_borderedHolomorphicGroupoid ζ ζ' hζ hζ'

/-- The domain `{z : ‖ζ - z‖ < r ‖ζ + z‖}` of the half-disc chart centered at `ζ`. -/
def halfDiscDom (ζ : ℂ) (r : ℝ) : Set CenteredClosedDisc := {z | ‖ζ - z‖ < r * ‖ζ + z‖}

@[simp]
theorem mem_halfDiscDom {ζ : ℂ} {r : ℝ} {z : CenteredClosedDisc} :
    z ∈ halfDiscDom ζ r ↔ ‖ζ - z‖ < r * ‖ζ + z‖ :=
  Iff.rfl

/-- Half-disc domains are open. -/
theorem isOpen_halfDiscDom (ζ : ℂ) (r : ℝ) : IsOpen (halfDiscDom ζ r) :=
  isOpen_lt (continuous_const.sub continuous_coe).norm
    (continuous_const.mul (continuous_const.add continuous_coe).norm)

/-- The closure of a half-disc domain does not contain `-ζ`, for `ζ ≠ 0`. -/
theorem closure_halfDiscDom_subset {ζ : ℂ} (hζ : ζ ≠ 0) (r : ℝ) :
    closure (halfDiscDom ζ r) ⊆ {z | (z : ℂ) ≠ -ζ} := by
  refine (closure_lt_subset_le (continuous_const.sub continuous_coe).norm
    (continuous_const.mul (continuous_const.add continuous_coe).norm)).trans fun z hz hzζ ↦ ?_
  -- `hz` is the inequality `‖ζ - z‖ ≤ r ‖ζ + z‖`, stated with pointwise operations on functions.
  replace hz : ‖ζ - (z : ℂ)‖ ≤ r * ‖ζ + z‖ := hz
  simp only [hzζ, sub_neg_eq_add, add_neg_cancel, norm_zero, mul_zero, ← two_mul, norm_mul] at hz
  linarith [mul_pos (norm_pos_iff.2 (two_ne_zero : (2 : ℂ) ≠ 0)) (norm_pos_iff.2 hζ)]

/-- **Half-disc charts.** The Cayley chart centered at `ζ` maps the half-disc domain
`TauCeti.CenteredClosedDisc.halfDiscDom ζ r` onto the half-disc `{w : ‖w‖ < r}` of the closed upper
half-plane (`Complex.UnitClosedDisc.cayleyChart_image_setOf_lt`). -/
theorem cayleyChart_image_halfDiscDom {ζ : ℂ} (hζ : ‖ζ‖ = 1) (r : ℝ) :
    cayleyChart ζ hζ '' halfDiscDom ζ r = {w : ClosedUpperHalfPlane | ‖(w : ℂ)‖ < r} :=
  Complex.UnitClosedDisc.cayleyChart_image_setOf_lt r

end CenteredClosedDisc

end TauCeti
