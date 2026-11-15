/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.DirichletDomain.Basic
public import TauCeti.MeasureTheory.Group.DirichletDomain.Thick
import TauCeti.MeasureTheory.Group.Action

/-!
# The thick part of a cofinite Fuchsian group

Let `Γ ≤ PSL(2, ℝ)` be cofinite and `ε > 0`. The `ε`-thick part `thickPart Γ ε` consists of the
points of `ℍ` moved a hyperbolic distance at least `ε` by every nonidentity element of `Γ`. Its
intersection with any Dirichlet domain is bounded, and its image in `Γ \ ℍ` is compact. A
point outside it is moved less than `ε` by some nonidentity element of `Γ`, which is elliptic,
parabolic, or hyperbolic of translation length less than `ε`.

Both statements apply the general packing argument
`TauCeti.isBounded_dirichletDomain_inter_thickPart`: the hyperbolic balls of radius `ε / 2` all
have the same positive area, because `PSL(2, ℝ)` acts transitively on `ℍ` by isometries
preserving the invariant measure, and a cofinite group has a fundamental domain of finite area.

## Main results

* `Subgroup.IsCofinite.isBounded_dirichletDomain_inter_thickPart`: the thick part of a Dirichlet
  domain of a cofinite group is bounded.
* `Subgroup.IsCofinite.isCompact_image_thickPart`: the thick part of `Γ \ ℍ` is compact.

## References

* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §4.1 (Dirichlet regions of cofinite groups).
* Riccardo Benedetti and Carlo Petronio, *Lectures on Hyperbolic Geometry*, Universitext,
  Springer, 1992, Chapter D (the thick part of a finite-volume hyperbolic manifold).
-/

public section

open MeasureTheory Metric MulAction TauCeti UpperHalfPlane

open scoped MatrixGroups

namespace Subgroup

variable {Γ : Subgroup PSL(2, ℝ)}

/-- **The thick part of a Dirichlet domain of a cofinite group is bounded.** For a cofinite
`Γ ≤ PSL(2, ℝ)` and `ε > 0`, the points of a Dirichlet domain moved a hyperbolic distance at least
`ε` by every nonidentity element of `Γ` form a bounded set. -/
theorem IsCofinite.isBounded_dirichletDomain_inter_thickPart (hΓ : Γ.IsCofinite) (p : ℍ)
    {ε : ℝ} (hε : 0 < ε) : Bornology.IsBounded (dirichletDomain Γ p ∩ thickPart Γ ε) := by
  have := hΓ.discreteTopology
  obtain ⟨s, -, -, hs⟩ := exists_isFundamentalDomain Γ
  exact TauCeti.isBounded_dirichletDomain_inter_thickPart hs (hΓ.volume_ne_top hs)
    (measure_ball_pos volume p (half_pos hε)).ne'
    (fun z ↦ (measure_ball_eq_measure_ball (G := PSL(2, ℝ)) volume z p _).ge) p

/-- **The thick part of the quotient of a cofinite group is compact.** For a cofinite
`Γ ≤ PSL(2, ℝ)` and `ε > 0`, the image in `Γ \ ℍ` of the points moved a hyperbolic distance at
least `ε` by every nonidentity element of `Γ` is compact. -/
theorem IsCofinite.isCompact_image_thickPart (hΓ : Γ.IsCofinite) {ε : ℝ} (hε : 0 < ε) :
    IsCompact (Quotient.mk (orbitRel Γ ℍ) '' thickPart Γ ε) := by
  have := hΓ.discreteTopology
  obtain ⟨s, -, -, hs⟩ := exists_isFundamentalDomain Γ
  exact TauCeti.isCompact_image_thickPart hs (hΓ.volume_ne_top hs)
    (measure_ball_pos volume I (half_pos hε)).ne'
    fun z ↦ (measure_ball_eq_measure_ball (G := PSL(2, ℝ)) volume z I _).ge

end Subgroup
