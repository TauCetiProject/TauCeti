/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Jordan.Unbounded.InvertedCoordinate
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

import TauCeti.Analysis.Complex.Conformal.LocalFrontier
import TauCeti.Analysis.Complex.Conformal.Reflection.Corner

/-!
# Sector ends of an inverted coordinate

Let `f` be a conformal map of the upper half-plane onto an unbounded domain with several accesses
to infinity, and let `g = (f - q)⁻¹` be its inverted coordinate, continuous on the closed upper
half-plane and injective away from its zeros.  The real zeros of `g` are the boundary parameters at
which `f` tends to infinity.

This file treats a zero `x` of `g` at which the domain ends in a sector: `f` maps the points of
the upper half-plane near `x` into the far part
`{ρ < ‖w - c‖, |arg ((w - c) / b)| < β * π / 2}` of a sector of opening `β * π`, `0 < β < 2`, and
that far part lies in the image of `f`.  Then the recentered coordinate
`TauCeti.recenterInvertedCoordinate q c b g`, which is `b / (f - c)` in the upper half-plane,
extends continuously and injectively across `x` with value `0` there, carries the nearby upper
half-plane into the sector of the same opening, and has its other boundary values on the two
bounding rays.  These are the local conditions at a vertex at infinity of opening `β * π` in the
Schwarz--Christoffel formula
`TauCeti.eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_boundary`, with turning
exponent `-β - 1`, so they apply to polygonal domains with several sector ends.

With several accesses to infinity, `g` is only injective away from its zeros, so it is not clear a
priori that `x` is the only zero nearby.  This follows from the sector geometry: the boundary zeros
of a sector-valued map are isolated (`TauCeti.eventually_ne_zero_of_sector`).

## Main results

* `TauCeti.exists_ball_sector_end_of_inverted_coordinate`: at a zero of the inverted coordinate
  whose end is a sector, the recentered coordinate satisfies the local conditions at a vertex at
  infinity of the same opening.

## References

* C. Carathéodory, Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung,
  Math. Ann. 73 (1913).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Springer, 1992, Ch. 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

open Bornology Complex Filter Function Metric Set Topology UpperHalfPlane

namespace TauCeti

variable {f g : ℂ → ℂ} {q : ℂ}

/-- **The recentered coordinate at a sector end.**  Let `g = (f - q)⁻¹` be the inverted coordinate
of a map `f` of the upper half-plane: `g` is continuous on the closed upper half-plane, holomorphic
and nonzero in its interior, and injective away from its zeros.  Let `x` be a real zero of `g`, and
suppose that `f` maps the points of the upper half-plane near `x` into the far part
`S = {ρ < ‖w - c‖, |arg ((w - c) / b)| < β * π / 2}` of a sector of opening `β * π`, where
`0 < β < 2`, and that `S` lies in the image of `f`.  Then on a closed upper half-disc about `x` the
recentered coordinate `G = TauCeti.recenterInvertedCoordinate q c b g` agrees with `b / (f - c)`
off the real axis, vanishes at `x`, is continuous and injective, maps the open upper half-disc into
the open sector `|arg| < β * π / 2`, and has its nonzero values on the diameter on the two bounding
rays `|arg| = β * π / 2`.

For `β = -e - 1` these are the local conditions of
`TauCeti.eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_boundary` at a vertex at
infinity with turning exponent `e ∈ (-3, -1)`. -/
theorem exists_ball_sector_end_of_inverted_coordinate
    (hgc : ContinuousOn g {z : ℂ | 0 ≤ z.im}) (hgd : DifferentiableOn ℂ g upperHalfPlaneSet)
    (hgf : EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet)
    (hgne : ∀ z ∈ upperHalfPlaneSet, g z ≠ 0)
    (hgi : InjOn g {z : ℂ | 0 ≤ z.im ∧ g z ≠ 0}) {x : ℝ} (hx : g x = 0)
    {ρ β : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 2) {c b : ℂ} (hb : b ≠ 0)
    (hS : {w : ℂ | ρ < ‖w - c‖ ∧ |((w - c) / b).arg| < β * Real.pi / 2} ⊆
      f '' upperHalfPlaneSet)
    (hfS : ∀ᶠ z in 𝓝[upperHalfPlaneSet] (x : ℂ),
      f z ∈ {w : ℂ | ρ < ‖w - c‖ ∧ |((w - c) / b).arg| < β * Real.pi / 2}) :
    ∃ r > 0,
      EqOn (recenterInvertedCoordinate q c b g) (fun z => b / (f z - c))
        (ball (x : ℂ) r ∩ {z : ℂ | 0 < z.im}) ∧
      recenterInvertedCoordinate q c b g x = 0 ∧
      ContinuousOn (recenterInvertedCoordinate q c b g) (ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) ∧
      InjOn (recenterInvertedCoordinate q c b g) (ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) ∧
      (∀ z ∈ ball (x : ℂ) r, 0 < z.im →
        |(recenterInvertedCoordinate q c b g z).arg| < β * Real.pi / 2) ∧
      ∀ z ∈ ball (x : ℂ) r, z.im = 0 → recenterInvertedCoordinate q c b g z ≠ 0 →
        |(recenterInvertedCoordinate q c b g z).arg| = β * Real.pi / 2 := by
  set S := {w : ℂ | ρ < ‖w - c‖ ∧ |((w - c) / b).arg| < β * Real.pi / 2}
  obtain ⟨r₁, hr₁, hpole, hGc, hGd, hGf, hGx, hGne⟩ :=
    exists_ball_recenterInvertedCoordinate (c := c) hgc hgd hgf hgne hx hb
  set G := recenterInvertedCoordinate q c b g
  obtain ⟨r₂, hr₂, hS₂⟩ := Metric.mem_nhdsWithin_iff.mp hfS
  obtain ⟨r₃, hr₃, hfar⟩ := exists_ball_lt_norm_of_inverted_coordinate (q := q) hgc hx c (max ρ 0)
  set r₄ := min r₁ (min r₂ r₃)
  have hr₄ : 0 < r₄ := lt_min hr₁ (lt_min hr₂ hr₃)
  have h₁ : ball (x : ℂ) r₄ ⊆ ball (x : ℂ) r₁ := ball_subset_ball (min_le_left _ _)
  have h₂ : ball (x : ℂ) r₄ ⊆ ball (x : ℂ) r₂ :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))
  have h₃ : ball (x : ℂ) r₄ ⊆ ball (x : ℂ) r₃ :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))
  have hgG {z : ℂ} (hGz : G z ≠ 0) : g z ≠ 0 := fun h => hGz (by simp [G, h])
  -- inversion about `c` preserves the unoriented angle with the bisector of the sector
  have harg (w : ℂ) : |(b / (w - c)).arg| = |((w - c) / b).arg| := by
    rw [← inv_div, abs_arg_inv]
  -- the open upper half-disc is carried into the sector
  have hsector (z : ℂ) (hz : z ∈ ball (x : ℂ) r₄) (hzH : 0 < z.im) :
      |(G z).arg| < β * Real.pi / 2 := by
    rw [hGf ⟨h₁ hz, hzH⟩, harg]
    exact (hS₂ ⟨h₂ hz, hzH⟩).2
  -- the other boundary values lie on the two bounding rays
  have hrays (z : ℂ) (hz : z ∈ ball (x : ℂ) r₄) (hz0 : z.im = 0) (hGz : G z ≠ 0) :
      |(G z).arg| = β * Real.pi / 2 := by
    have hgz := hgG hGz
    set w := q + (g z)⁻¹
    have hGw : G z = b / (w - c) :=
      recenterInvertedCoordinate_eq_div (f := fun _ => w) (by simp [w]) (by simpa [w] using hgz)
    have hwfar := hfar z (h₃ hz) hz0.ge hgz
    -- `w` is the limit of values of `f` in `S`
    have hwcl : w ∈ closure S := by
      have hzcl : z ∈ closure (ball (x : ℂ) r₂ ∩ upperHalfPlaneSet) :=
        isOpen_ball.inter_closure ⟨h₂ hz, by simp [upperHalfPlaneSet, ← hz0]⟩
      have : (𝓝[ball (x : ℂ) r₂ ∩ upperHalfPlaneSet] z).NeBot :=
        mem_closure_iff_nhdsWithin_neBot.mp hzcl
      have hlim : Tendsto (fun y => q + (g y)⁻¹) (𝓝[ball (x : ℂ) r₂ ∩ upperHalfPlaneSet] z)
          (𝓝 w) :=
        ((continuousWithinAt_const.add ((hgc z hz0.ge).inv₀ hgz)).mono
          fun y (hy : y ∈ ball (x : ℂ) r₂ ∩ upperHalfPlaneSet) =>
            mem_ofPred.mpr (le_of_lt hy.2)).tendsto
      refine mem_closure_of_tendsto hlim (eventually_nhdsWithin_of_forall fun y hy => ?_)
      rw [hgf hy.2, inv_inv, add_sub_cancel]
      exact hS₂ hy
    -- but not a value of `f` at an interior point, since `g` is injective off its zeros
    have hwS : w ∉ S := fun hw =>
      add_inv_notMem_image_of_inverted_coordinate hgf hgi hz0 hgz (hS hw)
    rw [hGw, harg]
    exact abs_arg_div_eq_of_mem_frontier (U := S) (V := {y : ℂ | ρ < ‖y - c‖}) hb
      (isOpen_lt continuous_const (by fun_prop)) (fun y hy _ => and_iff_right hy)
      (le_max_left ρ 0 |>.trans_lt hwfar)
      (sub_ne_zero.mp (norm_pos_iff.mp ((le_max_right ρ 0).trans_lt hwfar)))
      ⟨hwcl, fun h => hwS (interior_subset h)⟩
  -- the sector geometry makes `x` an isolated zero
  obtain ⟨r₅, hr₅, hiso⟩ := Metric.mem_nhdsWithin_iff.mp <| eventually_ne_zero_of_sector hβ hr₄
    (hGc.mono (inter_subset_inter_left _ h₁)) (hGd.mono (inter_subset_inter_left _ h₁))
    (fun z hz hzH => hGne z ⟨h₁ hz, hzH⟩) hsector hrays
  have h₅ : ball (x : ℂ) (min r₄ r₅) ⊆ ball (x : ℂ) r₄ := ball_subset_ball (min_le_left _ _)
  have hzero {z : ℂ} (hz : z ∈ ball (x : ℂ) (min r₄ r₅) ∩ {z : ℂ | 0 ≤ z.im}) (hGz : G z = 0) :
      z = x := by
    by_contra hzx
    exact hiso ⟨ball_subset_ball (min_le_right _ _) hz.1, hz.2, hzx⟩ hGz
  refine ⟨min r₄ r₅, lt_min hr₄ hr₅, fun z hz => hGf ⟨h₁ (h₅ hz.1), hz.2⟩, hGx,
    hGc.mono (inter_subset_inter_left _ (h₅.trans h₁)), fun z hz w hw hzw => ?_,
    fun z hz => hsector z (h₅ hz), fun z hz => hrays z (h₅ hz)⟩
  by_cases hGz : G z = 0
  · exact (hzero hz hGz).trans (hzero hw (hzw ▸ hGz)).symm
  · exact injOn_recenterInvertedCoordinate
      (S := (ball (x : ℂ) r₁ ∩ {z : ℂ | 0 ≤ z.im}) ∩ {z | g z ≠ 0})
      (hgi.mono fun z hz => by exact ⟨hz.1.2, hz.2⟩) hb (fun z hz => hpole z hz.1)
      ⟨⟨h₁ (h₅ hz.1), hz.2⟩, hgG hGz⟩ ⟨⟨h₁ (h₅ hw.1), hw.2⟩, hgG (hzw ▸ hGz)⟩ hzw

end TauCeti
