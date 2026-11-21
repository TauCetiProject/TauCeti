/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Euclidean.Plane
public import TauCeti.Analysis.Complex.ReImTopology
public import TauCeti.Analysis.Sobolev.LipschitzDomain.HalfDisc.Basic
import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Complex coordinates for the model half-disc

The affine isometry `TauCeti.halfDiscChart x` takes an upper half-disc about a real point `x`
to `TauCeti.halfDisc r`, with normal coordinate first. This file provides its coordinate,
closure, flat-segment and measure-transport formulas independently of Sobolev traces and Morrey
theory.
-/

public section

noncomputable section

open Metric Set MeasureTheory TopologicalSpace Filter Topology

namespace TauCeti

/-! ### The chart at a real point -/

/-- The chart at `x ∈ ℂ` for the model half-disc: the affine isometry
`z ↦ (im (z - x), re (z - x))` from `ℂ` to `WithLp 2 (ℝ × ℝ)`, whose first coordinate is the
normal coordinate of `TauCeti.halfDisc`. For real `x` it takes `D_r(x) ∩ {0 < im}` onto
`TauCeti.halfDisc r` (`TauCeti.halfDiscChart_symm_preimage`). -/
def halfDiscChart (x : ℂ) : ℂ ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × ℝ) :=
  (AffineIsometryEquiv.vaddConst ℝ x).symm.trans
    Complex.equivRealProdL2Swap.toAffineIsometryEquiv

/-- The chart in coordinates. -/
@[simp]
theorem halfDiscChart_apply (x z : ℂ) :
    halfDiscChart x z = WithLp.toLp 2 ((z - x).im, (z - x).re) := by
  simp [halfDiscChart]

/-- The inverse chart in coordinates. -/
@[simp]
theorem halfDiscChart_symm_apply (x : ℂ) (w : WithLp 2 (ℝ × ℝ)) :
    (halfDiscChart x).symm w = ⟨w.snd, w.fst⟩ + x := by
  rw [AffineIsometryEquiv.symm_apply_eq, halfDiscChart_apply]
  cases w
  simp

/-- The chart at `x` sends `x` to the origin. -/
theorem halfDiscChart_self (x : ℂ) : halfDiscChart x x = 0 := by
  simp only [halfDiscChart_apply, sub_self, Complex.zero_im, Complex.zero_re]
  rfl

/-- The inverse chart preserves the norm of displacement from its centre. -/
theorem norm_halfDiscChart_symm_sub (x : ℂ) (w : WithLp 2 (ℝ × ℝ)) :
    ‖(halfDiscChart x).symm w - x‖ = ‖w‖ := by
  rw [halfDiscChart_symm_apply, add_sub_cancel_right, ← Complex.equivRealProdL2Swap_symm_apply,
    LinearIsometryEquiv.norm_map]

/-- At a real centre, the imaginary part is the normal coordinate of the inverse chart. -/
theorem im_halfDiscChart_symm {x : ℂ} (hx : x.im = 0) (w : WithLp 2 (ℝ × ℝ)) :
    ((halfDiscChart x).symm w).im = w.fst := by
  simp [hx]

/-- The upper half-disc `D_r(x) ∩ {0 < im}` about a real point `x`, as an open set. -/
abbrev upperHalfDisc (x : ℂ) (r : ℝ) : Opens ℂ :=
  Opens.upperHalf ⟨ball x r, isOpen_ball⟩

/-- For real `x` the chart pulls the upper half-disc `D_r(x) ∩ {0 < im}` back to the model
half-disc `TauCeti.halfDisc r`. -/
theorem halfDiscChart_symm_preimage {x : ℂ} (hx : x.im = 0) (r : ℝ) :
    (halfDisc r : Set (WithLp 2 (ℝ × ℝ))) = (halfDiscChart x).symm ⁻¹' (upperHalfDisc x r) := by
  ext w
  simp only [SetLike.mem_coe, mem_halfDisc, mem_preimage, Opens.mem_upperHalf, Opens.mem_mk,
    mem_ball, dist_eq_norm, norm_halfDiscChart_symm_sub, im_halfDiscChart_symm hx]

/-- The chart maps the closed model half-disc into `closedBall x r ∩ {0 ≤ im}`. -/
theorem halfDiscChart_symm_mapsTo_closure {x : ℂ} (hx : x.im = 0) {r : ℝ} :
    MapsTo (halfDiscChart x).symm (closure (halfDisc r : Set (WithLp 2 (ℝ × ℝ))))
      (closedBall x r ∩ {z | 0 ≤ z.im}) := by
  intro w hw
  by_cases hr : 0 < r
  · rw [closure_halfDisc hr] at hw
    exact ⟨by rw [mem_closedBall, dist_eq_norm, norm_halfDiscChart_symm_sub]
              exact mem_closedBall_zero_iff.1 hw.1,
      by rw [mem_ofPred_eq, im_halfDiscChart_symm hx]; exact hw.2⟩
  · rw [coe_halfDisc, ball_eq_empty.2 (not_lt.1 hr), empty_inter, closure_empty] at hw
    exact hw.elim

/-- The chart maps the flat segment into the real points of `closedBall x r`. -/
theorem halfDiscChart_symm_mapsTo_flatSegment {x : ℂ} (hx : x.im = 0) {r : ℝ} :
    MapsTo (halfDiscChart x).symm (halfDiscFlatSegment r) (closedBall x r ∩ {z | z.im = 0}) :=
  fun w hw => ⟨by rw [mem_closedBall, dist_eq_norm, norm_halfDiscChart_symm_sub]
                  exact (mem_halfDiscFlatSegment.1 hw).1,
    by rw [mem_ofPred_eq, im_halfDiscChart_symm hx]; exact (mem_halfDiscFlatSegment.1 hw).2⟩

/-- Almost-everywhere equality on `U` transports to the model half-disc of an admissible
half-disc. -/
theorem ae_eq_comp_halfDiscChart_symm {β : Type*} {U : Set ℂ} {x : ℂ} (hx : x.im = 0)
    {r : ℝ} (hxr : (upperHalfDisc x r : Set ℂ) ⊆ U) {f g : ℂ → β}
    (hfg : f =ᵐ[volume.restrict U] g) :
    (fun w => f ((halfDiscChart x).symm w)) =ᵐ[volume.restrict (halfDisc r : Set _)]
      fun w => g ((halfDiscChart x).symm w) := by
  have hmp : MeasurePreserving (halfDiscChart x).symm (volume.restrict (halfDisc r : Set _))
      (volume.restrict (upperHalfDisc x r : Set ℂ)) := by
    rw [halfDiscChart_symm_preimage hx r]
    exact (halfDiscChart x).symm.measurePreserving.restrict_preimage
      (upperHalfDisc x r).isOpen.measurableSet
  exact hmp.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae_restrict_of_subset hxr hfg)

/-- The open upper half-disc lies in the closed one. -/
theorem coe_upperHalfDisc_subset_closedBall_inter (x : ℂ) (r : ℝ) :
    (upperHalfDisc x r : Set ℂ) ⊆ closedBall x r ∩ {z | 0 ≤ z.im} :=
  fun _ hz => ⟨ball_subset_closedBall (Opens.mem_upperHalf.1 hz).1,
    le_of_lt (Opens.mem_upperHalf.1 hz).2⟩

end TauCeti
