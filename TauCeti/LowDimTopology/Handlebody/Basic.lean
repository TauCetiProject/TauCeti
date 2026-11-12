/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
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
* `TauCeti.isClosed_handlebody`: the standard handlebodies are closed.
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

/-- The standard handlebodies are closed. -/
theorem isClosed_handlebody (g : ℕ) : IsClosed (handlebody g) :=
  (isCompact_handlebody g).isClosed

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

/-- A point of the closed disc with one hole is nonzero. -/
private theorem ne_zero_of_mem_planarSurface_one {z : ℂ} (hz : z ∈ planarSurface 1) : z ≠ 0 := by
  rw [planarSurface_one] at hz
  exact norm_pos_iff.1 (lt_of_lt_of_le (by norm_num) hz.1)

/-- The radii `[1 / 2, 2]` of the closed disc with one hole are positive. -/
private theorem pos_of_mem_Icc_inv_two_two {r : ℝ} (hr : r ∈ Icc (2⁻¹ : ℝ) 2) : 0 < r :=
  lt_of_lt_of_le (by norm_num) hr.1

/-- Polar coordinates, restricted from `homeomorphUnitSphereProd ℂ`, identify the closed disc with
one hole with the product of the interval `[1 / 2, 2]` and the circle. -/
private def planarSurfaceOneHomeomorph : planarSurface 1 ≃ₜ Icc (2⁻¹ : ℝ) 2 × Circle :=
  let e : {z : ({0}ᶜ : Set ℂ) | (z : ℂ) ∈ planarSurface 1} ≃ₜ planarSurface 1 :=
    Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange <| by
      intro z hz
      exact ⟨⟨z, ne_zero_of_mem_planarSurface_one hz⟩, rfl⟩
  let r : {r : Ioi (0 : ℝ) | (r : ℝ) ∈ Icc (2⁻¹ : ℝ) 2} ≃ₜ Icc (2⁻¹ : ℝ) 2 :=
    Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange <| by
      intro r hr
      exact ⟨⟨r, pos_of_mem_Icc_inv_two_two hr⟩, rfl⟩
  e.symm.trans <|
    ((homeomorphUnitSphereProd ℂ).subtype
      (q := fun y ↦ y ∈ (univ : Set (sphere (0 : ℂ) 1)) ×ˢ
        {r : Ioi (0 : ℝ) | (r : ℝ) ∈ Icc (2⁻¹ : ℝ) 2})
      (by intro z; simp [planarSurface_one, homeomorphUnitSphereProd_apply_snd_coe])).trans <|
      (Homeomorph.Set.prod _ _).trans <|
        ((Homeomorph.Set.univ (sphere (0 : ℂ) 1)).prodCongr r).trans (Homeomorph.prodComm _ _)

/-- Polar coordinates on the annulus, and the identity on the interval, identify the genus-one
handlebody with the product of a rectangle and the circle. -/
private def handlebodyOneHomeomorphProd :
    handlebody 1 ≃ₜ (Icc (2⁻¹ : ℝ) 2 ×ˢ Icc (-1 : ℝ) 1 : Set (ℝ × ℝ)) × Circle :=
  (Homeomorph.Set.prod (planarSurface 1) (Icc (-1) 1)).trans <|
    (planarSurfaceOneHomeomorph.prodCongr (.refl _)).trans <|
      (Homeomorph.prodAssoc _ _ _).trans <|
        ((Homeomorph.refl _).prodCongr (Homeomorph.prodComm _ _)).trans <|
          (Homeomorph.prodAssoc _ _ _).symm.trans <|
            (Homeomorph.Set.prod _ _).symm.prodCongr (.refl _)

/-- **The genus-one handlebody is a solid torus.** The standard handlebody of genus one is
homeomorphic to the solid torus `D² × S¹`. -/
theorem nonempty_homeomorph_handlebody_one : Nonempty (handlebody 1 ≃ₜ SolidTorus) :=
  (nonempty_homeomorph_Icc_prod_closedBall (F := ℂ) (by norm_num : (2⁻¹ : ℝ) < 2)
    (by norm_num : (-1 : ℝ) < 1) (by simp)).map fun e ↦
    handlebodyOneHomeomorphProd.trans (e.prodCongr (.refl Circle))

end TauCeti
