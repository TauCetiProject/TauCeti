/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Cayley
public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.Interior
public import TauCeti.Topology.Constructions.DoubleAlong.Disc

/-!
# The closed unit disc as a Riemann surface with boundary

The closed unit disc `Complex.UnitClosedDisc` is a Riemann surface with boundary, modelled on the
closed upper half-plane. For a point `ζ` of the unit circle, the Cayley chart
`Complex.UnitClosedDisc.cayleyChart ζ` is `z ↦ I (ζ - z) / (ζ + z)`. It is defined on the closed
disc minus `-ζ`, its image is the whole closed upper half-plane, and its inverse is
`w ↦ ζ (I - w) / (w + I)`: the imaginary part of `I (ζ - z) / (ζ + z)` is
`(1 - ‖z‖²) / ‖ζ + z‖²`, so the image of `z` is real exactly when `‖z‖ = 1`. The atlas consists of
the Cayley charts for all `ζ`; the chart at `z` uses `ζ = 1` when `0 ≤ re z` and `ζ = -1`
otherwise. The transition maps are Möbius maps preserving the closed upper half-plane, with their
pole on the real axis, so they are holomorphic on their domains, up to the boundary, and lie in
the bordered holomorphic groupoid.

The manifold interior is the open unit disc, and the manifold boundary is the unit circle, which
`Complex.UnitClosedDisc.homeomorphClosedBall` identifies with `TauCeti.DoubleAlong.discBoundary`,
the boundary along which `TauCeti.DoubleAlong` doubles the disc to the Riemann sphere. The
inclusion of the closed disc into `ℂ` is smooth up to the boundary, and the inclusion of the
interior into `ℂ` is analytic for the complex structure induced on the interior.

Mathlib's `closedBall (0 : ℂ) 1` already carries the half-space atlas
`TauCeti.instChartedSpaceClosedBallComplex` modelled on `EuclideanHalfSpace 2`, and the model of a
charted space is an `outParam`, so the Cayley atlas is put on the type synonym
`Complex.UnitClosedDisc` instead.

## Main declarations

* `Complex.UnitClosedDisc.cayleyChart`: the Cayley chart attached to a point of the unit circle.
* `Complex.UnitClosedDisc.instChartedSpace`: the atlas of Cayley charts.
* `Complex.UnitClosedDisc.instHasGroupoid`: the Cayley charts have bordered holomorphic
  transition maps, so the closed disc is a Riemann surface with boundary.
* `Complex.UnitClosedDisc.mem_borderedInterior_iff` and
  `Complex.UnitClosedDisc.compl_borderedInterior`: the interior is the open disc and its
  complement is the unit circle, which `Complex.UnitClosedDisc.image_compl_borderedInterior`
  identifies with `TauCeti.DoubleAlong.discBoundary`.
* `Complex.UnitClosedDisc.contMDiff_coe`: the inclusion of the closed disc into `ℂ` is smooth up
  to the boundary.
* `Complex.UnitClosedDisc.contMDiff_coe_borderedInterior`: the inclusion of the interior into
  `ℂ` is analytic for the induced complex structure.

## References

* L. V. Ahlfors and L. Sario, *Riemann Surfaces*, Princeton University Press, 1960, Ch. II, for
  bordered Riemann surfaces.
-/

public section

noncomputable section

open Set Metric Filter TauCeti
open scoped Manifold ContDiff Topology Complex.UnitDisc

namespace Complex.UnitClosedDisc

/-- The identity, from the closed unit disc to the subtype `closedBall (0 : ℂ) 1` it is a type
synonym of. -/
def homeomorphClosedBall : 𝕔𝔻 ≃ₜ closedBall (0 : ℂ) 1 :=
  Homeomorph.refl _

@[simp]
theorem coe_homeomorphClosedBall (z : 𝕔𝔻) : (homeomorphClosedBall z : ℂ) = z :=
  (rfl)

@[simp]
theorem coe_homeomorphClosedBall_symm (z : closedBall (0 : ℂ) 1) :
    (homeomorphClosedBall.symm z : ℂ) = z :=
  (rfl)

/-! ### Cayley charts -/

private theorem ne_zero_of_norm_eq_one {ζ : ℂ} (hζ : ‖ζ‖ = 1) : ζ ≠ 0 :=
  ne_zero_of_norm_ne_zero (hζ ▸ one_ne_zero)

private theorem add_ne_zero_of_ne_neg {ζ z : ℂ} (hz : z ≠ -ζ) : ζ + z ≠ 0 :=
  fun h ↦ hz (eq_neg_of_add_eq_zero_right h)

/-- The map `z ↦ I (ζ - z) / (ζ + z)` is analytic away from its pole `-ζ`. -/
private theorem contDiffAt_I_mul_sub_div_add {n : ℕ∞ω} (ζ : ℂ) {z : ℂ} (hz : ζ + z ≠ 0) :
    ContDiffAt ℂ n (fun z : ℂ ↦ I * (ζ - z) / (ζ + z)) z :=
  (contDiffAt_const.mul (contDiffAt_const.sub contDiffAt_id)).div
    (contDiffAt_const.add contDiffAt_id) hz

/-- The map `w ↦ ζ (I - w) / (w + I)` is analytic away from its pole `-I`. -/
private theorem contDiffAt_mul_I_sub_div_add_I {n : ℕ∞ω} (ζ : ℂ) {w : ℂ} (hw : w + I ≠ 0) :
    ContDiffAt ℂ n (fun w : ℂ ↦ ζ * (I - w) / (w + I)) w :=
  (contDiffAt_const.mul (contDiffAt_const.sub contDiffAt_id)).div
    (contDiffAt_id.add contDiffAt_const) hw

/-- The Cayley chart attached to a point `ζ` of the unit circle: the map
`z ↦ I (ζ - z) / (ζ + z)` from the closed unit disc minus `-ζ` onto the closed upper half-plane,
with inverse `w ↦ ζ (I - w) / (w + I)`. It sends `ζ` to `0` and `0` to `I`. -/
def cayleyChart (ζ : ℂ) (hζ : ‖ζ‖ = 1) : OpenPartialHomeomorph 𝕔𝔻 ClosedUpperHalfPlane where
  toFun z := ⟨I * (ζ - z) / (ζ + z), im_I_mul_sub_div_add_nonneg (hζ ▸ z.norm_le_one)⟩
  invFun w := mk (ζ * (I - w) / (w + I)) (norm_mul_I_sub_div_add_I_le_one hζ.le w.2)
  source := {z : 𝕔𝔻 | (z : ℂ) ≠ -ζ}
  target := univ
  map_source' _ _ := mem_univ _
  map_target' w _ := by
    rw [mem_ofPred_eq, coe_mk]
    exact mul_I_sub_div_add_I_ne_neg (ne_zero_of_norm_eq_one hζ) _
  left_inv' z hz := coe_injective <| by
    rw [coe_mk]
    exact mul_I_sub_I_mul_sub_div_add_div_add_I (ne_zero_of_norm_eq_one hζ)
      (add_ne_zero_of_ne_neg hz)
  right_inv' w _ := Subtype.ext <| by
    simp only [coe_mk]
    exact I_mul_sub_mul_I_sub_div_add_I_div_add (ne_zero_of_norm_eq_one hζ)
      (add_I_ne_zero_of_im_nonneg w.2)
  open_source := isOpen_ne_fun continuous_coe continuous_const
  open_target := isOpen_univ
  continuousOn_toFun := by
    refine (Topology.IsEmbedding.subtypeVal.isInducing.continuousOn_iff).2 fun z hz ↦ ?_
    exact ((contDiffAt_I_mul_sub_div_add (n := 0) ζ (add_ne_zero_of_ne_neg hz)).continuousAt.comp
      continuous_coe.continuousAt).continuousWithinAt
  continuousOn_invFun := by
    refine (isEmbedding_coe.isInducing.continuousOn_iff).2 ?_
    refine Continuous.continuousOn (continuous_iff_continuousAt.2 fun w ↦ ?_)
    simp only [Function.comp_def, coe_mk]
    exact (contDiffAt_mul_I_sub_div_add_I (n := 0) ζ
      (add_I_ne_zero_of_im_nonneg w.2)).continuousAt.comp continuous_subtype_val.continuousAt

variable {ζ : ℂ} {hζ : ‖ζ‖ = 1}

/-- A Cayley chart is `z ↦ I (ζ - z) / (ζ + z)`. -/
@[simp]
theorem coe_cayleyChart_apply (z : 𝕔𝔻) :
    (cayleyChart ζ hζ z : ℂ) = I * (ζ - z) / (ζ + z) :=
  (rfl)

/-- The inverse of a Cayley chart is `w ↦ ζ (I - w) / (w + I)`. -/
@[simp]
theorem coe_cayleyChart_symm_apply (w : ClosedUpperHalfPlane) :
    ((cayleyChart ζ hζ).symm w : ℂ) = ζ * (I - w) / (w + I) :=
  (rfl)

/-- A Cayley chart is defined on the closed unit disc minus `-ζ`. -/
@[simp]
theorem cayleyChart_source : (cayleyChart ζ hζ).source = {z : 𝕔𝔻 | (z : ℂ) ≠ -ζ} :=
  (rfl)

/-- A Cayley chart takes values in the whole closed upper half-plane. -/
@[simp]
theorem cayleyChart_target : (cayleyChart ζ hζ).target = univ :=
  (rfl)

/-- The imaginary part of a Cayley chart is `(1 - ‖z‖²) / ‖ζ + z‖²`. -/
theorem im_cayleyChart_apply (z : 𝕔𝔻) :
    (cayleyChart ζ hζ z : ℂ).im = (1 - ‖(z : ℂ)‖ ^ 2) / ‖ζ + z‖ ^ 2 := by
  rw [coe_cayleyChart_apply, im_I_mul_sub_div_add, normSq_eq_norm_sq, normSq_eq_norm_sq,
    normSq_eq_norm_sq, hζ, one_pow]

/-- A point of the source of a Cayley chart has image of positive imaginary part exactly when it
lies in the open unit disc. -/
theorem im_cayleyChart_pos_iff {z : 𝕔𝔻} (hz : z ∈ (cayleyChart ζ hζ).source) :
    0 < (cayleyChart ζ hζ z : ℂ).im ↔ ‖(z : ℂ)‖ < 1 := by
  rw [cayleyChart_source] at hz
  have hz0 : ‖ζ + z‖ ≠ 0 := norm_ne_zero_iff.2 (add_ne_zero_of_ne_neg hz)
  rw [im_cayleyChart_apply, div_pos_iff_of_pos_right (by positivity), sub_pos,
    sq_lt_one_iff₀ (norm_nonneg _)]

/-- A point of the source of a Cayley chart has real image exactly when it lies on the unit
circle. -/
theorem im_cayleyChart_eq_zero_iff {z : 𝕔𝔻} (hz : z ∈ (cayleyChart ζ hζ).source) :
    (cayleyChart ζ hζ z : ℂ).im = 0 ↔ ‖(z : ℂ)‖ = 1 := by
  rw [cayleyChart_source] at hz
  have hz0 : ‖ζ + z‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 (add_ne_zero_of_ne_neg hz))
  rw [im_cayleyChart_apply, div_eq_zero_iff, or_iff_left hz0, sub_eq_zero, eq_comm,
    pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero]

/-! ### The atlas -/

/-- The center of the preferred chart at `z`: `1` if `0 ≤ re z`, and `-1` otherwise. -/
def chartCenter (z : 𝕔𝔻) : ℂ :=
  if 0 ≤ (z : ℂ).re then 1 else -1

/-- The defining formula of `chartCenter`. -/
theorem chartCenter_def (z : 𝕔𝔻) : chartCenter z = if 0 ≤ (z : ℂ).re then 1 else -1 :=
  (rfl)

/-- The center of the preferred chart lies on the unit circle. -/
@[simp]
theorem norm_chartCenter (z : 𝕔𝔻) : ‖chartCenter z‖ = 1 := by
  rw [chartCenter_def]
  split_ifs <;> simp

/-- A point lies in the source of its preferred chart. -/
theorem coe_ne_neg_chartCenter (z : 𝕔𝔻) : (z : ℂ) ≠ -chartCenter z := by
  rw [chartCenter_def]
  split_ifs with h <;>
  · intro hz
    rw [hz] at h
    norm_num at h

/-- The closed unit disc is a charted space modelled on the closed upper half-plane: the atlas
consists of the Cayley charts, and the chart at `z` has center `1` if `0 ≤ re z` and `-1`
otherwise. -/
instance instChartedSpace : ChartedSpace ClosedUpperHalfPlane 𝕔𝔻 where
  atlas := {e | ∃ (ζ : ℂ) (hζ : ‖ζ‖ = 1), e = cayleyChart ζ hζ}
  chartAt z := cayleyChart (chartCenter z) (norm_chartCenter z)
  mem_chart_source z := by
    rw [cayleyChart_source]
    exact coe_ne_neg_chartCenter z
  chart_mem_atlas _ := ⟨_, _, rfl⟩

/-- The chart at `z` is the Cayley chart centered at `chartCenter z`. -/
theorem chartAt_eq (z : 𝕔𝔻) :
    chartAt ClosedUpperHalfPlane z = cayleyChart (chartCenter z) (norm_chartCenter z) :=
  (rfl)

/-- The charts of the atlas are the Cayley charts. -/
theorem mem_atlas_iff {e : OpenPartialHomeomorph 𝕔𝔻 ClosedUpperHalfPlane} :
    e ∈ atlas ClosedUpperHalfPlane 𝕔𝔻 ↔ ∃ (ζ : ℂ) (hζ : ‖ζ‖ = 1), e = cayleyChart ζ hζ :=
  Iff.rfl

/-- Every Cayley chart belongs to the atlas. -/
@[simp]
theorem cayleyChart_mem_atlas (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    cayleyChart ζ hζ ∈ atlas ClosedUpperHalfPlane 𝕔𝔻 :=
  mem_atlas_iff.2 ⟨ζ, hζ, rfl⟩

/-! ### Transition maps -/

/-- The transition map between two Cayley charts is, on its source, the Möbius map
`w ↦ I (ζ' - u) / (ζ' + u)` with `u = ζ (I - w) / (w + I)`, which is analytic there. -/
private theorem cayleyChart_symm_trans_apply (ζ ζ' : ℂ) (hζ : ‖ζ‖ = 1) (hζ' : ‖ζ'‖ = 1) :
    ∀ w ∈ ((cayleyChart ζ hζ).symm ≫ₕ cayleyChart ζ' hζ').source,
      ContDiffAt ℂ ∞ (fun w : ℂ ↦ I * (ζ' - ζ * (I - w) / (w + I)) / (ζ' + ζ * (I - w) / (w + I)))
          (w : ℂ) ∧
        (((cayleyChart ζ hζ).symm ≫ₕ cayleyChart ζ' hζ') w : ℂ) =
          I * (ζ' - ζ * (I - w) / (w + I)) / (ζ' + ζ * (I - w) / (w + I)) := by
  intro w hw
  simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    cayleyChart_target, univ_inter, mem_preimage, cayleyChart_source, mem_ofPred_eq,
    coe_cayleyChart_symm_apply] at hw
  refine ⟨?_, by simp⟩
  exact (contDiffAt_I_mul_sub_div_add ζ' (add_ne_zero_of_ne_neg hw)).comp (w : ℂ)
    (contDiffAt_mul_I_sub_div_add_I ζ (add_I_ne_zero_of_im_nonneg w.2))

/-- The transition map between two Cayley charts lies in the bordered holomorphic groupoid. -/
theorem cayleyChart_symm_trans_mem_borderedHolomorphicGroupoid (ζ ζ' : ℂ) (hζ : ‖ζ‖ = 1)
    (hζ' : ‖ζ'‖ = 1) :
    (cayleyChart ζ hζ).symm ≫ₕ cayleyChart ζ' hζ' ∈ borderedHolomorphicGroupoid := by
  have hsymm : ((cayleyChart ζ hζ).symm ≫ₕ cayleyChart ζ' hζ').symm =
      (cayleyChart ζ' hζ').symm ≫ₕ cayleyChart ζ hζ := by
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm]
  refine ClosedUpperHalfPlane.mem_borderedHolomorphicGroupoid_of_contDiffAt
    (G := fun w ↦ I * (ζ - ζ' * (I - w) / (w + I)) / (ζ + ζ' * (I - w) / (w + I)))
    (cayleyChart_symm_trans_apply ζ ζ' hζ hζ') ?_
  rw [← OpenPartialHomeomorph.symm_source, hsymm]
  exact cayleyChart_symm_trans_apply ζ' ζ hζ' hζ

/-- The closed unit disc, with its Cayley charts, is a Riemann surface with boundary. -/
instance instHasGroupoid : HasGroupoid 𝕔𝔻 borderedHolomorphicGroupoid where
  compatible := by
    rintro _ _ ⟨ζ, hζ, rfl⟩ ⟨ζ', hζ', rfl⟩
    exact cayleyChart_symm_trans_mem_borderedHolomorphicGroupoid ζ ζ' hζ hζ'

/-! ### Interior and boundary -/

/-- The interior of the closed unit disc is the open unit disc. -/
@[simp]
theorem mem_borderedInterior_iff {z : 𝕔𝔻} : z ∈ borderedInterior 𝕔𝔻 ↔ ‖(z : ℂ)‖ < 1 := by
  rw [mem_borderedInterior_iff_im_chartAt_pos, chartAt_eq,
    im_cayleyChart_pos_iff (by rw [cayleyChart_source]; exact coe_ne_neg_chartCenter z)]

/-- The interior of the closed unit disc is the open unit disc. -/
theorem coe_borderedInterior :
    (borderedInterior 𝕔𝔻 : Set 𝕔𝔻) = {z : 𝕔𝔻 | ‖(z : ℂ)‖ < 1} :=
  Set.ext fun _ ↦ mem_borderedInterior_iff

/-- The complement of the interior of the closed unit disc is the unit circle. -/
theorem compl_borderedInterior :
    (borderedInterior 𝕔𝔻 : Set 𝕔𝔻)ᶜ = {z : 𝕔𝔻 | ‖(z : ℂ)‖ = 1} := by
  ext z
  rw [mem_compl_iff, SetLike.mem_coe, mem_borderedInterior_iff, not_lt, mem_ofPred_eq]
  exact ⟨fun h ↦ le_antisymm z.norm_le_one h, fun h ↦ h.ge⟩

/-- The complement of the interior of the closed unit disc is the boundary circle
`TauCeti.DoubleAlong.discBoundary` along which `TauCeti.DoubleAlong` doubles the disc to the
Riemann sphere. -/
theorem image_compl_borderedInterior :
    homeomorphClosedBall '' (borderedInterior 𝕔𝔻 : Set 𝕔𝔻)ᶜ = DoubleAlong.discBoundary := by
  rw [compl_borderedInterior, homeomorphClosedBall.image_eq_preimage_symm]
  ext z
  rw [mem_preimage, mem_ofPred_eq, coe_homeomorphClosedBall_symm, DoubleAlong.mem_discBoundary]

/-- The inclusion of the closed unit disc into `ℂ` is smooth up to the boundary. -/
theorem contMDiff_coe {n : ℕ∞ω} : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ, ℂ) n ((↑) : 𝕔𝔻 → ℂ) := by
  intro x
  refine contMDiffAt_iff.2 ⟨continuous_coe.continuousAt, ?_⟩
  simp only [mfld_simps]
  rw [range_closedUpperHalfPlaneModel, chartAt_eq]
  have hcoe : ∀ v : ℂ, 0 ≤ v.im →
      (((↑) : 𝕔𝔻 → ℂ) ∘ (cayleyChart (chartCenter x) (norm_chartCenter x)).symm ∘
        closedUpperHalfPlaneModel.symm) v = chartCenter x * (I - v) / (v + I) := fun v hv ↦ by
    rw [Function.comp_apply, Function.comp_apply, coe_cayleyChart_symm_apply,
      coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hv]
  have hx := (cayleyChart (chartCenter x) (norm_chartCenter x) x).2
  exact ((contDiffAt_mul_I_sub_div_add_I _ (add_I_ne_zero_of_im_nonneg hx)).restrict_scalars
    ℝ).contDiffWithinAt.congr hcoe (hcoe _ hx)

/-- The inclusion of the interior of the closed unit disc into `ℂ` is analytic for the complex
structure induced on the interior by the Cayley charts. -/
theorem contMDiff_coe_borderedInterior {n : ℕ∞ω} :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) n (fun z : borderedInterior 𝕔𝔻 ↦ ((z : 𝕔𝔻) : ℂ)) := by
  refine ContMDiff.of_le (fun x ↦ ?_) le_top
  refine contMDiffAt_iff.2 ⟨(continuous_coe.comp continuous_subtype_val).continuousAt, ?_⟩
  simp only [mfld_simps]
  refine ContDiffAt.contDiffWithinAt ?_
  set w := chartAt ℂ x x
  have hw : w ∈ (chartAt ℂ x).target := mem_chart_target ℂ x
  rw [chartAt_borderedInterior_target] at hw
  have hev : (fun v ↦ (((chartAt ℂ x).symm v : 𝕔𝔻) : ℂ)) =ᶠ[𝓝 w]
      fun v ↦ chartCenter (x : 𝕔𝔻) * (I - v) / (v + I) := by
    filter_upwards [(chartAt ℂ x).open_target.mem_nhds (mem_chart_target ℂ x)] with v hv
    rw [chartAt_borderedInterior_symm_apply x hv, chartAt_eq, coe_cayleyChart_symm_apply]
    rw [chartAt_borderedInterior_target] at hv
    rw [coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hv.2.le]
  exact (contDiffAt_mul_I_sub_div_add_I _
    (add_I_ne_zero_of_im_nonneg hw.2.le)).congr_of_eventuallyEq hev

end Complex.UnitClosedDisc
