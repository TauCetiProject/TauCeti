/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.FilledHull
public import TauCeti.Topology.JordanCurve.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Complex.Conformal.Jordan.Schoenflies
import TauCeti.Topology.Homeomorph.SetCongr
import TauCeti.Topology.Homotopy.Cube.BoundaryGluing
import TauCeti.Topology.Homotopy.Cube.Radius

/-!
# Four-sided Jordan domains in the plane

Four injective paths `top : Path a b`, `bot : Path c d`, `left : Path a c`, and
`right : Path b d` in `ℂ` whose opposite edges are disjoint and whose adjacent edges meet only at
their shared corners form a Jordan curve, and the closed domain `filledHull C` they enclose is
homeomorphic to the unit square `I × I` by a homeomorphism restricting to the four given paths
along the four sides (`TauCeti.exists_homeomorph_unitInterval_prod_filledHull`).

## The argument

The square-to-disc homeomorphism `TauCeti.squareHomeomorphClosedBall` identifies `I × I` with
`closedBall (0 : ℂ) 1`, carrying the boundary `TauCeti.squareBoundary` onto the unit circle
`sphere (0 : ℂ) 1` (`TauCeti.norm_squareHomeomorphClosedBall_eq_one_iff`). Gluing the four paths
along the four closed sides of `I × I` (`TauCeti.exists_homeomorph_squareBoundary`) gives a
homeomorphism from `TauCeti.squareBoundary` onto `C`. Transferring to `sphere (0 : ℂ) 1`
supplies the boundary data for the prescribed-boundary Schoenflies theorem
(`Homeomorph.exists_homeomorph_sphere_eq`), whose extension restricts to the required homeomorphism
`I × I ≃ₜ filledHull C`.

## Main results

* `TauCeti.exists_homeomorph_unitInterval_prod_filledHull`: a four-sided Jordan domain in `ℂ` is
  homeomorphic to `I × I` with prescribed boundary paths along the four sides.

## References

* A. Schoenflies, *Beiträge zur Theorie der Punktmengen. III*, Math. Ann. 62 (1906), 286–328.
* E. E. Moise, *Geometric Topology in Dimensions 2 and 3*, Springer GTM 47 (1977), Chapter 10.
-/

public section

noncomputable section

open Function Metric Set Topology unitInterval

namespace TauCeti

/-- **Four-sided Jordan domains are homeomorphic to the unit square.** Given four injective paths
`top : Path a b`, `bot : Path c d`, `left : Path a c`, and `right : Path b d` in `ℂ` whose opposite
edges are disjoint and whose adjacent edges meet only at their shared endpoints, the union of their
ranges is a Jordan curve, and there is a homeomorphism from `I × I` onto its filled hull restricting
to `top`, `bot`, `left`, and `right` along the four sides of the square. -/
theorem exists_homeomorph_unitInterval_prod_filledHull {a b c d : ℂ}
    {top : Path a b} {bot : Path c d} {left : Path a c} {right : Path b d}
    (htop : Injective top) (hbot : Injective bot)
    (hleft : Injective left) (hright : Injective right)
    (htb : Disjoint (range top) (range bot)) (hlr : Disjoint (range left) (range right))
    (htl : range top ∩ range left = {a}) (htr : range top ∩ range right = {b})
    (hbl : range bot ∩ range left = {c}) (hbr : range bot ∩ range right = {d}) :
    IsJordanCurve (range top ∪ range bot ∪ range left ∪ range right) ∧
      ∃ Φ : I × I ≃ₜ filledHull (range top ∪ range bot ∪ range left ∪ range right),
        (∀ s : I, (Φ (s, 0) : ℂ) = top s) ∧
        (∀ s : I, (Φ (s, 1) : ℂ) = bot s) ∧
        (∀ t : I, (Φ (0, t) : ℂ) = left t) ∧
        (∀ t : I, (Φ (1, t) : ℂ) = right t) := by
  obtain ⟨ψ, hψ_top, hψ_bot, hψ_left, hψ_right⟩ := exists_homeomorph_squareBoundary
    htop hbot hleft hright htb hlr htl htr hbl hbr
  -- Restrict `squareHomeomorphClosedBall` to a boundary homeomorphism `∂(I × I) ≃ₜ S¹`.
  have hfin : Module.finrank ℝ ℂ = 2 := by simp [Complex.finrank_real_complex]
  let sq : (I × I) ≃ₜ closedBall (0 : ℂ) 1 := squareHomeomorphClosedBall hfin
  let eQ : squareBoundary ≃ₜ sphere (0 : ℂ) 1 := squareBoundaryHomeomorphSphere hfin
  let φ : sphere (0 : ℂ) 1 ≃ₜ ↥(range top ∪ range bot ∪ range left ∪ range right) :=
    eQ.symm.trans ψ
  have hC : IsJordanCurve (range top ∪ range bot ∪ range left ∪ range right) :=
    (isJordanCurve_sphere 0 one_pos).of_homeomorph φ
  obtain ⟨e, heφ, -, -, heCB⟩ := φ.exists_homeomorph_sphere_eq
  let Φ : I × I ≃ₜ filledHull (range top ∪ range bot ∪ range left ∪ range right) :=
    sq.trans ((e.image (closedBall 0 1)).trans (Homeomorph.setCongr heCB))
  have hΦb (p : I × I) (hp : p ∈ squareBoundary) : (Φ p : ℂ) = ψ ⟨p, hp⟩ := by
    have hcoe : (Φ p : ℂ) = e (sq p) := by
      simp [Φ, Homeomorph.trans_apply, Homeomorph.setCongr_apply]
    have hQ : (sq p : ℂ) = (eQ ⟨p, hp⟩ : ℂ) :=
      (coe_squareBoundaryHomeomorphSphere_apply hfin ⟨p, hp⟩).symm
    rw [hcoe, hQ, heφ (eQ ⟨p, hp⟩)]
    simp [φ]
  refine ⟨hC, Φ, ?_, ?_, ?_, ?_⟩
  · intro s; exact (hΦb (s, 0) (by simp)).trans (hψ_top s (by simp))
  · intro s; exact (hΦb (s, 1) (by simp)).trans (hψ_bot s (by simp))
  · intro t; exact (hΦb (0, t) (by simp)).trans (hψ_left t (by simp))
  · intro t; exact (hΦb (1, t) (by simp)).trans (hψ_right t (by simp))

end TauCeti
