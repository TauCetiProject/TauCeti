/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

import Mathlib.Topology.Bornology.BoundedOperation
import TauCeti.Analysis.Complex.UpperHalfPlane.Topology

/-!
# Changing the centre of an inverted boundary coordinate

A conformal map onto an unbounded domain can be controlled at all of its accesses to infinity by
a bounded coordinate `g = (f - q)⁻¹`, where `q` is any point outside the closure of the domain.
Local geometry at one access, however, is naturally expressed by inversion about a geometric
centre `c`, followed by a nonzero scale `b`.

The linear fractional change

`g ↦ b * g / (1 + (q - c) * g)`

turns the first coordinate into `b / (f - c)`.  This file records that identity together with the
continuity, holomorphy, zero-set, and injectivity properties needed to change coordinates at a
boundary prevertex.  In particular, near a boundary zero of `g` the denominator is automatically
nonzero, so the recentered coordinate remains continuous up to the boundary and holomorphic in the
upper half-plane.

These facts let a single globally continuous inverted coordinate be recentered separately at the
vertices at infinity of a polygonal domain. Precomposition by `z ↦ x₀ - z⁻¹` also moves a real
boundary parameter to infinity while preserving the coordinate properties.

## Main results

* `TauCeti.recenterInvertedCoordinate` is the linear fractional change of inverted coordinate.
* `TauCeti.recenterInvertedCoordinate_eq_div` identifies it with inversion about the new centre.
* `TauCeti.exists_ball_lt_norm_of_inverted_coordinate`: near a boundary zero, the nonzero values
  of the inverted coordinate correspond to points far from any given centre.
* `TauCeti.add_inv_notMem_image_of_inverted_coordinate`: a nonzero real boundary value of the
  inverted coordinate is not a value of the original map.
* `TauCeti.exists_ball_recenterInvertedCoordinate` supplies all analytic properties near a
  boundary zero.
* `TauCeti.exists_inverted_coordinate_comp_sub_inv` moves a real boundary parameter to infinity.
-/

public section

open Bornology Complex Filter Function Metric Set Topology UpperHalfPlane

namespace TauCeti

/-- Change an inverted coordinate centred at `q` into one centred at `c`, with scale `b`.

When `g = (f - q)⁻¹`, this is `b / (f - c)` wherever `f ≠ q`. -/
noncomputable def recenterInvertedCoordinate (q c b : ℂ) (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  b * g z / (1 + (q - c) * g z)

/-- The defining formula for a recentered inverted coordinate. -/
@[simp]
theorem recenterInvertedCoordinate_apply (q c b : ℂ) (g : ℂ → ℂ) (z : ℂ) :
    recenterInvertedCoordinate q c b g z = b * g z / (1 + (q - c) * g z) :=
  (rfl)

/-- If `g` is inversion about `q`, its recentering is scaled inversion about `c`. -/
theorem recenterInvertedCoordinate_eq_div {f g : ℂ → ℂ} {q c b z : ℂ}
    (hgf : g z = (f z - q)⁻¹) (hq : f z ≠ q) :
    recenterInvertedCoordinate q c b g z = b / (f z - c) := by
  rw [recenterInvertedCoordinate, hgf]
  field_simp [sub_ne_zero.mpr hq]
  ring

/-- The difference formula for the linear fractional change of inverted coordinate. -/
theorem recenterInvertedCoordinate_sub {q c b : ℂ} {g : ℂ → ℂ} {z w : ℂ}
    (hz : 1 + (q - c) * g z ≠ 0) (hw : 1 + (q - c) * g w ≠ 0) :
    recenterInvertedCoordinate q c b g z - recenterInvertedCoordinate q c b g w =
      b * (g z - g w) /
        ((1 + (q - c) * g z) * (1 + (q - c) * g w)) := by
  rw [recenterInvertedCoordinate, recenterInvertedCoordinate]
  rw [div_sub_div (b * g z) (b * g w) hz hw]
  ring

/-- A nondegenerate change of centre preserves injectivity away from its pole. -/
theorem injOn_recenterInvertedCoordinate {S : Set ℂ} {q c b : ℂ} {g : ℂ → ℂ}
    (hg : InjOn g S) (hb : b ≠ 0) (hpole : ∀ z ∈ S, 1 + (q - c) * g z ≠ 0) :
    InjOn (recenterInvertedCoordinate q c b g) S := by
  intro z hz w hw hzw
  have hsub := congrArg (fun u => u - TauCeti.recenterInvertedCoordinate q c b g w) hzw
  rw [sub_self, recenterInvertedCoordinate_sub (hpole z hz) (hpole w hw)] at hsub
  have hnum : b * (g z - g w) = 0 :=
    (div_eq_zero_iff.mp hsub).resolve_right (mul_ne_zero (hpole z hz) (hpole w hw))
  have hgz : g z - g w = 0 := (mul_eq_zero.mp hnum).resolve_left hb
  exact hg hz hw (sub_eq_zero.mp hgz)

/-- Continuity of a recentered coordinate away from its pole. -/
theorem continuousOn_recenterInvertedCoordinate {S : Set ℂ} {q c b : ℂ} {g : ℂ → ℂ}
    (hg : ContinuousOn g S) (hpole : ∀ z ∈ S, 1 + (q - c) * g z ≠ 0) :
    ContinuousOn (recenterInvertedCoordinate q c b g) S := by
  exact (continuousOn_const.mul hg).div
    (continuousOn_const.add (continuousOn_const.mul hg)) hpole

/-- Holomorphy of a recentered coordinate away from its pole. -/
theorem differentiableOn_recenterInvertedCoordinate {S : Set ℂ} {q c b : ℂ} {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g S) (hpole : ∀ z ∈ S, 1 + (q - c) * g z ≠ 0) :
    DifferentiableOn ℂ (recenterInvertedCoordinate q c b g) S := by
  exact (differentiableOn_const b).mul hg |>.div
    ((differentiableOn_const 1).add ((differentiableOn_const (q - c)).mul hg)) hpole

/-- Near a zero of a continuous inverted coordinate, every change-of-centre denominator is
nonzero. -/
theorem exists_ball_recenterInvertedCoordinate_denominator_ne {S : Set ℂ} {g : ℂ → ℂ}
    {x q c : ℂ} (hg : ContinuousWithinAt g S x) (hx : g x = 0) :
    ∃ r > 0, ∀ z ∈ ball x r ∩ S, 1 + (q - c) * g z ≠ 0 := by
  have hcont : ContinuousWithinAt (fun z => 1 + (q - c) * g z) S x :=
    continuousWithinAt_const.add (continuousWithinAt_const.mul hg)
  have hevent : ∀ᶠ z in nhdsWithin x S, 1 + (q - c) * g z ≠ 0 := by
    apply (hcont.tendsto.eventually (isOpen_compl_singleton.mem_nhds ?_))
    simp [hx]
  have hevent' : ∀ᶠ z in nhds x, z ∈ S → 1 + (q - c) * g z ≠ 0 :=
    eventually_nhdsWithin_iff.mp hevent
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hevent'
  exact ⟨r, hr, fun _ hz => hball hz.1 hz.2⟩

/-- Near a zero of a continuous inverted coordinate, the points `q + g⁻¹` at which `g` does not
vanish are far from any given centre `c`. -/
theorem exists_ball_lt_norm_of_inverted_coordinate {g : ℂ → ℂ} {q : ℂ}
    (hgc : ContinuousOn g {z : ℂ | 0 ≤ z.im}) {x : ℝ} (hx : g x = 0) (c : ℂ) (R : ℝ) :
    ∃ r > 0, ∀ z ∈ ball (x : ℂ) r, 0 ≤ z.im → g z ≠ 0 → R < ‖q + (g z)⁻¹ - c‖ := by
  have hg : Tendsto g (𝓝[{z : ℂ | 0 ≤ z.im} ∩ {z | g z ≠ 0}] (x : ℂ)) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hx ▸ ((hgc _ (by simp)).mono inter_subset_left).tendsto,
      eventually_nhdsWithin_of_forall fun z hz => hz.2⟩
  have hfar : Tendsto (fun z => q + (g z)⁻¹ - c)
      (𝓝[{z : ℂ | 0 ≤ z.im} ∩ {z | g z ≠ 0}] (x : ℂ)) (cobounded ℂ) :=
    (tendsto_sub_const_cobounded c).comp
      ((tendsto_const_add_cobounded q).comp (tendsto_inv₀_nhdsNE_zero.comp hg))
  obtain ⟨r, hr, h⟩ := Metric.mem_nhdsWithin_iff.mp
    ((tendsto_norm_cobounded_atTop.comp hfar).eventually_gt_atTop R)
  exact ⟨r, hr, fun z hz hzH hgz => h ⟨hz, hzH, hgz⟩⟩

/-- A nonzero real boundary value `q + g⁻¹` of an inverted coordinate `g = (f - q)⁻¹`, injective
away from its zeros, is not a value of `f` on the upper half-plane. -/
theorem add_inv_notMem_image_of_inverted_coordinate {f g : ℂ → ℂ} {q : ℂ}
    (hgf : EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet)
    (hgi : InjOn g {z : ℂ | 0 ≤ z.im ∧ g z ≠ 0}) {z : ℂ} (hz0 : z.im = 0) (hgz : g z ≠ 0) :
    q + (g z)⁻¹ ∉ f '' upperHalfPlaneSet := by
  rintro ⟨y, hy, hyz⟩
  have hgy : g y = g z := by
    rw [hgf hy]
    dsimp only
    rw [hyz, add_sub_cancel_left, inv_inv]
  have hyz' := hgi ⟨le_of_lt hy, hgy ▸ hgz⟩ ⟨hz0.ge, hgz⟩ hgy
  exact (hyz' ▸ hy : 0 < z.im).ne' hz0

/-- **A recentered coordinate near a boundary prevertex.** Suppose `g = (f - q)⁻¹` in the upper
half-plane, is continuous on the closed upper half-plane and holomorphic and nonzero in its
interior, and vanishes at a real boundary point `x`. For every new centre `c` and nonzero scale
`b`, there is a radius `r > 0` such that on the open disc of radius `r` about `x` intersected
with the closed upper half-plane the recentered coordinate

`b * g / (1 + (q - c) * g)`

has no pole, is continuous, and vanishes at `x`; on the part of that disc inside the open upper
half-plane it is holomorphic and nonzero and agrees with `b / (f - c)`. -/
theorem exists_ball_recenterInvertedCoordinate {f g : ℂ → ℂ} {q c b : ℂ} {x : ℝ}
    (hgc : ContinuousOn g {z : ℂ | 0 ≤ z.im})
    (hgd : DifferentiableOn ℂ g upperHalfPlaneSet)
    (hgf : EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet)
    (hgne : ∀ z ∈ upperHalfPlaneSet, g z ≠ 0) (hx : g x = 0) (hb : b ≠ 0) :
    ∃ r > 0,
      (∀ z ∈ ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}, 1 + (q - c) * g z ≠ 0) ∧
      ContinuousOn (recenterInvertedCoordinate q c b g)
        (ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) ∧
      DifferentiableOn ℂ (recenterInvertedCoordinate q c b g)
        (ball (x : ℂ) r ∩ upperHalfPlaneSet) ∧
      EqOn (recenterInvertedCoordinate q c b g) (fun z => b / (f z - c))
        (ball (x : ℂ) r ∩ upperHalfPlaneSet) ∧
      recenterInvertedCoordinate q c b g x = 0 ∧
      ∀ z ∈ ball (x : ℂ) r ∩ upperHalfPlaneSet,
        recenterInvertedCoordinate q c b g z ≠ 0 := by
  obtain ⟨r, hr, hpole⟩ := exists_ball_recenterInvertedCoordinate_denominator_ne
    (hgc (x : ℂ) (by simp)) hx
  have hopen : ball (x : ℂ) r ∩ upperHalfPlaneSet ⊆
      ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im} :=
    inter_subset_inter_right _ (ofPred_subset_ofPred.mpr fun _ => le_of_lt)
  refine ⟨r, hr, hpole,
    continuousOn_recenterInvertedCoordinate (hgc.mono inter_subset_right) hpole,
    differentiableOn_recenterInvertedCoordinate (hgd.mono inter_subset_right)
      fun z hz => hpole z (hopen hz),
    ?_, (by simp [hx]), ?_⟩
  · intro z hz
    apply recenterInvertedCoordinate_eq_div (hgf hz.2)
    exact fun hzq => hgne z hz.2 (by simp [hgf hz.2, hzq])
  · intro z hz hzero
    exact hgne z hz.2 (by simpa [hb, hpole z (hopen hz)] using hzero)

/-- **Moving a real parameter to infinity.**  Compose a coordinate `g`, continuous on the closed
upper half-plane, holomorphic and nonzero in the open one, injective away from its zeros and
tending to `0` at infinity, with the automorphism `z ↦ x₀ - z⁻¹` of the upper half-plane, and fill
in the value `0` at `z = 0`.  The result has the same properties, the same image of the upper
half-plane, and the limit `g x₀` at infinity. -/
theorem exists_inverted_coordinate_comp_sub_inv {g : ℂ → ℂ}
    (hgc : ContinuousOn g {z : ℂ | 0 ≤ z.im}) (hgd : DifferentiableOn ℂ g upperHalfPlaneSet)
    (hgne : ∀ z ∈ upperHalfPlaneSet, g z ≠ 0)
    (hgi : InjOn g {z : ℂ | 0 ≤ z.im ∧ g z ≠ 0})
    (hg0 : Tendsto g (cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 ≤ z.im}) (𝓝 0)) (x₀ : ℝ) :
    ∃ g₁ : ℂ → ℂ, g₁ 0 = 0 ∧ (∀ z, z ≠ 0 → g₁ z = g (x₀ - z⁻¹)) ∧
      ContinuousOn g₁ {z : ℂ | 0 ≤ z.im} ∧ DifferentiableOn ℂ g₁ upperHalfPlaneSet ∧
      (∀ z ∈ upperHalfPlaneSet, g₁ z ≠ 0) ∧ InjOn g₁ {z : ℂ | 0 ≤ z.im ∧ g₁ z ≠ 0} ∧
      g₁ '' upperHalfPlaneSet = g '' upperHalfPlaneSet ∧
      Tendsto g₁ (cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 ≤ z.im}) (𝓝 (g x₀)) := by
  classical
  set φ : ℂ → ℂ := fun z => (x₀ : ℂ) - z⁻¹
  have hφim (z : ℂ) : (φ z).im = (-z⁻¹).im := by simp [φ]
  have hφH {z : ℂ} (hz : 0 ≤ z.im) : 0 ≤ (φ z).im := hφim z ▸ im_neg_inv_nonneg.mpr hz
  have hφH' {z : ℂ} (hz : 0 < z.im) : 0 < (φ z).im := hφim z ▸ im_neg_inv_pos.mpr hz
  have hne {z : ℂ} (hz : 0 < z.im) : z ≠ 0 := fun h => by simp [h] at hz
  -- `φ` is an automorphism of the upper half-plane, with inverse `w ↦ -(w - x₀)⁻¹`
  have hφimage : φ '' upperHalfPlaneSet = upperHalfPlaneSet := by
    refine (mapsTo_iff_image_subset.mp fun z hz => hφH' hz).antisymm fun w hw => ?_
    refine ⟨-(w - x₀)⁻¹, im_neg_inv_pos.mpr (by simpa using hw), ?_⟩
    simp [φ]
  set g₁ : ℂ → ℂ := update (fun z => g (φ z)) 0 0
  have hg₁ {z : ℂ} (hz : z ≠ 0) : g₁ z = g (φ z) := update_of_ne hz _ _
  refine ⟨g₁, update_self _ _ _, fun z hz => hg₁ hz, ?_, ?_, fun z hz => ?_, ?_, ?_, ?_⟩
  · refine continuousOn_update_iff.mpr ⟨fun z hz => ?_, fun _ => ?_⟩
    · have hz0 : z ≠ 0 := by simpa using hz.2
      exact (hgc _ (hφH hz.1)).comp
        (continuousAt_const.sub (continuousAt_inv₀ hz0)).continuousWithinAt
        fun w hw => hφH hw.1
    · -- at `0`, the map `φ` tends to infinity in the closed upper half-plane
      refine hg0.comp (tendsto_inf.mpr ⟨?_, tendsto_principal.mpr ?_⟩)
      · exact (tendsto_const_sub_cobounded (x₀ : ℂ)).comp
          (tendsto_inv₀_nhdsNE_zero.mono_left (nhdsWithin_mono _ fun w hw => hw.2))
      · exact eventually_nhdsWithin_of_forall fun w hw => hφH hw.1
  · have hφd : DifferentiableOn ℂ φ upperHalfPlaneSet :=
      (differentiableOn_const _).sub (differentiableOn_id.inv fun z (hz : 0 < z.im) => hne hz)
    exact (hgd.comp hφd fun z hz => hφH' hz).congr fun z hz => hg₁ (hne hz)
  · rw [hg₁ (hne hz)]
    exact hgne _ (hφH' hz)
  · rintro z ⟨hz, hgz⟩ z' ⟨hz', hgz'⟩ h
    have hz0 : z ≠ 0 := by rintro rfl; exact hgz (update_self _ _ _)
    have hz0' : z' ≠ 0 := by rintro rfl; exact hgz' (update_self _ _ _)
    rw [hg₁ hz0] at h hgz
    rw [hg₁ hz0'] at h hgz'
    simpa [φ] using hgi ⟨hφH hz, hgz⟩ ⟨hφH hz', hgz'⟩ h
  · calc g₁ '' upperHalfPlaneSet = (fun z => g (φ z)) '' upperHalfPlaneSet :=
        image_congr fun z hz => hg₁ (hne hz)
      _ = g '' upperHalfPlaneSet := by rw [← image_image, hφimage]
  · have hφinf : Tendsto φ (cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 ≤ z.im})
        (𝓝[{z : ℂ | 0 ≤ z.im}] (x₀ : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_inf_principal.mpr
        (Eventually.of_forall fun z hz => hφH hz)⟩
      simpa using (tendsto_const_nhds.sub tendsto_inv₀_cobounded).mono_left
        (inf_le_left (b := 𝓟 {z : ℂ | 0 ≤ z.im}))
    refine ((hgc _ (by simp)).tendsto.comp hφinf).congr' ?_
    filter_upwards [(eventually_ne_cobounded (0 : ℂ)).filter_mono inf_le_left] with z hz
    exact (hg₁ hz).symm

end TauCeti

end
