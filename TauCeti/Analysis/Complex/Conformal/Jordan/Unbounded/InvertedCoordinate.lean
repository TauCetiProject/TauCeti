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
vertices at infinity of a polygonal domain.

## Main results

* `TauCeti.recenterInvertedCoordinate` is the linear fractional change of inverted coordinate.
* `TauCeti.recenterInvertedCoordinate_eq_div` identifies it with inversion about the new centre.
* `TauCeti.exists_ball_lt_norm_of_inverted_coordinate`: near a zero, the nonzero values
  of the inverted coordinate correspond to points far from any given centre.
* `TauCeti.add_inv_notMem_image_of_inverted_coordinate`: a nonzero real boundary value of the
  inverted coordinate is not a value of the original map.
* `TauCeti.exists_ball_recenterInvertedCoordinate` supplies all analytic properties near a
  boundary zero.
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

/-- If `g z` is the inversion `(w - q)⁻¹` of a value `w ≠ q`, its recentering is the scaled
inversion `b / (w - c)`. -/
theorem recenterInvertedCoordinate_eq_div {g : ℂ → ℂ} {q c b z w : ℂ}
    (hgw : g z = (w - q)⁻¹) (hw : w ≠ q) :
    recenterInvertedCoordinate q c b g z = b / (w - c) := by
  rw [recenterInvertedCoordinate, hgw]
  field_simp [sub_ne_zero.mpr hw]
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
  have hsub := recenterInvertedCoordinate_sub (b := b) (hpole z hz) (hpole w hw)
  rw [hzw, sub_self, eq_comm] at hsub
  -- the difference formula vanishes, while `b` and both denominators do not
  exact hg hz hw (by simpa [hb, hpole z hz, hpole w hw, sub_eq_zero] using hsub)

/-- Continuity of a recentered coordinate away from its pole. -/
theorem continuousOn_recenterInvertedCoordinate {S : Set ℂ} {q c b : ℂ} {g : ℂ → ℂ}
    (hg : ContinuousOn g S) (hpole : ∀ z ∈ S, 1 + (q - c) * g z ≠ 0) :
    ContinuousOn (recenterInvertedCoordinate q c b g) S :=
  (continuousOn_const.mul hg).div
    (continuousOn_const.add (continuousOn_const.mul hg)) hpole

/-- Holomorphy of a recentered coordinate away from its pole. -/
theorem differentiableOn_recenterInvertedCoordinate {S : Set ℂ} {q c b : ℂ} {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g S) (hpole : ∀ z ∈ S, 1 + (q - c) * g z ≠ 0) :
    DifferentiableOn ℂ (recenterInvertedCoordinate q c b g) S :=
  (differentiableOn_const b).mul hg |>.div
    ((differentiableOn_const 1).add ((differentiableOn_const (q - c)).mul hg)) hpole

/-- Near a zero of a continuous inverted coordinate, every change-of-centre denominator is
nonzero. -/
theorem exists_ball_recenterInvertedCoordinate_denominator_ne {S : Set ℂ} {g : ℂ → ℂ}
    {x q c : ℂ} (hg : ContinuousWithinAt g S x) (hx : g x = 0) :
    ∃ r > 0, ∀ z ∈ ball x r ∩ S, 1 + (q - c) * g z ≠ 0 := by
  have hcont : ContinuousWithinAt (fun z => 1 + (q - c) * g z) S x :=
    continuousWithinAt_const.add (continuousWithinAt_const.mul hg)
  obtain ⟨r, hr, hball⟩ :=
    Metric.mem_nhdsWithin_iff.mp (hcont.tendsto.eventually_ne (b₂ := 0) (by simp [hx]))
  exact ⟨r, hr, fun _ hz => hball hz⟩

/-- Near a zero of an inverted coordinate continuous within `S`, the points `q + g⁻¹` at which `g`
does not vanish are far from any given centre `c`. -/
theorem exists_ball_lt_norm_of_inverted_coordinate {S : Set ℂ} {g : ℂ → ℂ} {x q : ℂ}
    (hgc : ContinuousWithinAt g S x) (hx : g x = 0) (c : ℂ) (R : ℝ) :
    ∃ r > 0, ∀ z ∈ ball x r ∩ S, g z ≠ 0 → R < ‖q + (g z)⁻¹ - c‖ := by
  have hg : Tendsto g (𝓝[S ∩ {z | g z ≠ 0}] x) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hx ▸ (hgc.mono inter_subset_left).tendsto,
      eventually_nhdsWithin_of_forall fun z hz => hz.2⟩
  have hfar : Tendsto (fun z => q + (g z)⁻¹ - c) (𝓝[S ∩ {z | g z ≠ 0}] x) (cobounded ℂ) :=
    (tendsto_sub_const_cobounded c).comp
      ((tendsto_const_add_cobounded q).comp (tendsto_inv₀_nhdsNE_zero.comp hg))
  obtain ⟨r, hr, h⟩ := Metric.mem_nhdsWithin_iff.mp
    ((tendsto_norm_cobounded_atTop.comp hfar).eventually_gt_atTop R)
  exact ⟨r, hr, fun z hz hgz => h ⟨hz.1, hz.2, hgz⟩⟩

/-- A nonzero real boundary value `q + g⁻¹` of an inverted coordinate `g = (f - q)⁻¹`, injective
away from its zeros, is not a value of `f` on the upper half-plane. -/
theorem add_inv_notMem_image_of_inverted_coordinate {f g : ℂ → ℂ} {q : ℂ}
    (hgf : EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet)
    (hgi : InjOn g {z : ℂ | 0 ≤ z.im ∧ g z ≠ 0}) {z : ℂ} (hz0 : z.im = 0) (hgz : g z ≠ 0) :
    q + (g z)⁻¹ ∉ f '' upperHalfPlaneSet := by
  rintro ⟨y, hy, hyz⟩
  have hgy : g y = g z := by simp [hgf hy, hyz]
  exact hy.ne' (hgi ⟨hy.le, hgy ▸ hgz⟩ ⟨hz0.ge, hgz⟩ hgy ▸ hz0)

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
  · exact fun z hz => recenterInvertedCoordinate_eq_div (hgf hz.2)
      fun hzq => hgne z hz.2 (by simp [hgf hz.2, hzq])
  · intro z hz hzero
    exact hgne z hz.2 (by simpa [hb, hpole z (hopen hz)] using hzero)

end TauCeti

end
