/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
public import TauCeti.LowDimTopology.SeifertFibration

/-!
# The standard handlebodies

A handlebody of genus `g` is the orientable compact `3`-manifold obtained from the `3`-ball by
attaching `g` one-handles; equivalently, it is the product `F × [-1, 1]` of the interval with a
compact planar surface `F` of Euler characteristic `1 - g` (Hempel, Chapter 2). This file fixes a
concrete model of the second kind inside `ℂ × ℝ`.

The planar surface `TauCeti.planarSurface g` is the closed disc of radius `g + 1` in `ℂ` with `g`
open discs of radius `1 / 2` removed, centred at the real points `2k + 1 - g` for `k < g`. These
holes are pairwise disjoint and lie in the open disc of radius `g`, so the surface is a closed
disc with `g` holes, of Euler characteristic `1 - g`. The standard handlebody
`TauCeti.handlebody g` is its product with the interval `[-1, 1]`. Its manifold boundary is the
closed orientable surface of genus `g` formed by the two copies of the planar surface and the
annuli over the `g + 1` boundary circles.

Handlebodies are the pieces of a Heegaard splitting of a closed orientable `3`-manifold, and a
subset of a space is a genus-`g` handlebody when it is homeomorphic to `TauCeti.handlebody g`.

## Main definitions

* `TauCeti.planarSurface g`: the closed disc with `g` holes.
* `TauCeti.handlebody g`: the standard handlebody of genus `g`, a subset of `ℂ × ℝ`.

## Main results

* `TauCeti.isCompact_handlebody`: the standard handlebodies are compact.
* `TauCeti.handlebody_zero`: the genus-zero handlebody is the closed unit ball of `ℂ × ℝ`.
* `TauCeti.nonempty_homeomorph_handlebody_zero`: the closed unit ball of any real normed space of
  dimension three is homeomorphic to the genus-zero handlebody.
* `TauCeti.nonempty_homeomorph_handlebody_one`: the genus-one handlebody is homeomorphic to the
  solid torus `TauCeti.SolidTorus`.

## References

* J. Hempel, *3-Manifolds*, Annals of Mathematics Studies 86, Princeton University Press (1976),
  Chapter 2.
* M. Scharlemann, *Heegaard splittings of compact 3-manifolds*, in *Handbook of Geometric
  Topology*, North-Holland (2002), Section 2.
-/

public section

noncomputable section

open Metric Set

namespace TauCeti

/-- The closed disc of radius `g + 1` in `ℂ` with `g` open discs of radius `1 / 2` removed,
centred at the real points `2k + 1 - g` for `k < g`. It is a compact planar surface with
`g + 1` boundary circles. -/
def planarSurface (g : ℕ) : Set ℂ :=
  closedBall 0 (g + 1) \ ⋃ k : Fin g, ball ((2 * k + 1 - g : ℝ) : ℂ) 2⁻¹

@[simp]
theorem mem_planarSurface {g : ℕ} {z : ℂ} :
    z ∈ planarSurface g ↔
      ‖z‖ ≤ g + 1 ∧ ∀ k : Fin g, 2⁻¹ ≤ ‖z - ((2 * k + 1 - g : ℝ) : ℂ)‖ := by
  simp [planarSurface, dist_eq_norm]

/-- The closed disc with `g` holes is compact. -/
theorem isCompact_planarSurface (g : ℕ) : IsCompact (planarSurface g) :=
  (isCompact_closedBall _ _).diff (isOpen_iUnion fun _ ↦ isOpen_ball)

/-- The closed disc with no holes is the closed unit disc. -/
@[simp]
theorem planarSurface_zero : planarSurface 0 = closedBall 0 1 := by
  simp [planarSurface]

/-- The standard handlebody of genus `g`: the product of the closed disc with `g` holes,
`TauCeti.planarSurface g`, with the interval `[-1, 1]`. -/
def handlebody (g : ℕ) : Set (ℂ × ℝ) :=
  planarSurface g ×ˢ Icc (-1) 1

@[simp]
theorem mem_handlebody {g : ℕ} {x : ℂ × ℝ} :
    x ∈ handlebody g ↔ x.1 ∈ planarSurface g ∧ x.2 ∈ Icc (-1) 1 :=
  Iff.rfl

/-- The standard handlebodies are compact. -/
theorem isCompact_handlebody (g : ℕ) : IsCompact (handlebody g) :=
  (isCompact_planarSurface g).prod isCompact_Icc

/-- The genus-zero handlebody is the closed unit ball of `ℂ × ℝ`, for the sup norm. -/
theorem handlebody_zero : handlebody 0 = closedBall 0 1 := by
  rw [handlebody, planarSurface_zero, Prod.zero_eq_mk, ← closedBall_prod_same,
    Real.closedBall_eq_Icc]
  norm_num

/-- **The genus-zero handlebody is a ball.** The closed unit ball of any real normed space of
dimension three is homeomorphic to the genus-zero handlebody. -/
theorem nonempty_homeomorph_handlebody_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hF : Module.finrank ℝ F = 3) : Nonempty (closedBall (0 : F) 1 ≃ₜ handlebody 0) :=
  have : FiniteDimensional ℝ F := .of_finrank_eq_succ hF
  ⟨(closedBallHomeomorphOfFinrankEq (F := ℂ × ℝ) (by simp [hF])).trans
    (Homeomorph.setCongr handlebody_zero.symm)⟩

/-! ### The genus-one handlebody -/

/-- The closed disc with one hole is the closed annulus `1 / 2 ≤ ‖z‖ ≤ 2`. -/
theorem planarSurface_one : planarSurface 1 = {z : ℂ | 2⁻¹ ≤ ‖z‖ ∧ ‖z‖ ≤ 2} := by
  ext z
  simp only [mem_planarSurface, Fin.forall_fin_one]
  norm_num [and_comm]

/-- The first coordinate of a point of the genus-one handlebody is nonzero. -/
private theorem ne_zero_of_mem_handlebody_one {x : ℂ × ℝ} (hx : x ∈ handlebody 1) : x.1 ≠ 0 := by
  have h := (mem_handlebody.1 hx).1
  rw [planarSurface_one] at h
  exact norm_pos_iff.1 (lt_of_lt_of_le (by norm_num) h.1)

/-- Polar coordinates on the annulus, and the identity on the interval, identify the genus-one
handlebody with the product of a rectangle and the circle. -/
private def handlebodyOneHomeomorphProd :
    handlebody 1 ≃ₜ (Icc (2⁻¹ : ℝ) 2 ×ˢ Icc (-1 : ℝ) 1 : Set (ℝ × ℝ)) × Circle where
  toFun x :=
    (⟨(‖x.1.1‖, x.1.2), ⟨by simpa [planarSurface_one] using (mem_handlebody.1 x.2).1,
        (mem_handlebody.1 x.2).2⟩⟩,
      ⟨(‖x.1.1‖⁻¹ : ℂ) * x.1.1, mem_sphere_zero_iff_norm.2 <| by
        simp [ne_zero_of_mem_handlebody_one x.2]⟩)
  invFun y := ⟨((y.1.1.1 : ℂ) * y.2, y.1.1.2), mem_handlebody.2
    ⟨by simpa [planarSurface_one, abs_of_pos (lt_of_lt_of_le (by norm_num) y.1.2.1.1)]
      using y.1.2.1, y.1.2.2⟩⟩
  left_inv x := by
    ext <;> simp [ne_zero_of_mem_handlebody_one x.2]
  right_inv y := by
    have hr : 0 < y.1.1.1 := lt_of_lt_of_le (by norm_num) y.1.2.1.1
    ext <;> simp [abs_of_pos hr, hr.ne']
  continuous_toFun := by
    refine .prodMk (by fun_prop) (Continuous.subtype_mk (.mul (.inv₀ (by fun_prop) fun x ↦ ?_)
      (by fun_prop)) _)
    simpa using ne_zero_of_mem_handlebody_one x.2
  continuous_invFun := by fun_prop

/-- The rectangle `[1 / 2, 2] × [-1, 1]` is a closed disc. -/
private theorem nonempty_homeomorph_rectangle_closedBall :
    Nonempty ((Icc (2⁻¹ : ℝ) 2 ×ˢ Icc (-1 : ℝ) 1 : Set (ℝ × ℝ)) ≃ₜ closedBall (0 : ℂ) 1) :=
  nonempty_homeomorph_closedBall_of_convex ((convex_Icc _ _).prod (convex_Icc _ _))
    (isCompact_Icc.prod isCompact_Icc)
    (by rw [interior_prod_eq, interior_Icc, interior_Icc]; exact ⟨(1, 0), by norm_num⟩)
    (by simp)

/-- **The genus-one handlebody is a solid torus.** The standard handlebody of genus one is
homeomorphic to the solid torus `D² × S¹`. -/
theorem nonempty_homeomorph_handlebody_one : Nonempty (handlebody 1 ≃ₜ SolidTorus) :=
  nonempty_homeomorph_rectangle_closedBall.map fun e ↦
    handlebodyOneHomeomorphProd.trans (e.prodCongr (.refl Circle))

end TauCeti
