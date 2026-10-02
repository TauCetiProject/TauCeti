/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Toric.Analytic.Fan.Manifold
public import TauCeti.Geometry.Toric.Analytic.Fan.Subfan.Basic

/-!
# The analytic realization of an open subfan is an open complex submanifold

A face-closed set of cones of a regular fan is itself a regular fan, and the map
`TauCeti.Toric.Fan.subfanAnalyticMap` from its analytic realization to the ambient one is an open
embedding. This file proves that it is a local biholomorphism for the complex manifold structures
of the two realizations. Together with `TauCeti.Toric.Fan.isOpenEmbedding_subfanAnalyticMap`, it
identifies the realization of the subfan biholomorphically with an open subset of the ambient
realization, the union of the ambient charts of the cones of the subfan.

The argument is chartwise. On the chart of a cone of the subfan, the subfan map is the inclusion
of the same complex points in the ambient chart of that cone. For one extending basis and one
finite generating family of the dual semigroup, both chart inclusions are biholomorphisms onto
their open images, `TauCeti.Toric.Fan.analyticAffineChartPartialDiffeomorph`, so near a point of
that chart the subfan map is the inverse of the first followed by the second.

## Main declarations

* `TauCeti.Toric.Fan.isLocalDiffeomorph_subfanAnalyticMap`: the map from the analytic realization
  of a subfan to the ambient analytic realization is a local biholomorphism.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.4 and 2.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1 and 3.4.
-/

public section

open Set Topology
open scoped ContDiff Manifold

namespace TauCeti.Toric.Fan

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i) (hΦ : Φ.IsRegular) (S : Set (PointedCone ℝ V)) (hS : S ⊆ Φ.cones)
  (hface : ∀ ⦃σ τ⦄, σ ∈ S → τ.IsFaceOf σ → τ ∈ S)

/-- The map from the analytic realization of a subfan to the ambient analytic realization is a
local biholomorphism, for the complex manifold structures of the two realizations. -/
theorem isLocalDiffeomorph_subfanAnalyticMap (n : ℕ∞ω) :
    letI := (Φ.subfan S hS hface).analyticChartedSpace (hΦ.subfan S hS hface)
    letI := Φ.analyticChartedSpace hΦ
    IsLocalDiffeomorph 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) n
      (Φ.subfanAnalyticMap hΦ S hS hface) := by
  let _ := (Φ.subfan S hS hface).analyticChartedSpace (hΦ.subfan S hS hface)
  let _ := Φ.analyticChartedSpace hΦ
  intro p
  obtain ⟨σ, x, rfl⟩ :=
    (Φ.subfan S hS hface).exists_analyticAffineChartι_apply_eq (hΦ.subfan S hS hface) p
  have hσ := (isRegular_iff.mp (hΦ.subfan S hS hface)) σ.1 σ.2
  obtain ⟨l, B, hB⟩ := hσ.exists_basis_sum
  have : Finite (ToricRay σ.1) := ToricRay.finite_of_fg hσ.fg
  let κ := Finite.equivFin (ToricRay σ.1)
  let g := (analyticChartGenerators (Φ.subfan S hS hface) σ hσ).2
  -- Both chart inclusions of `σ` carry the complex structure of the same extending basis and
  -- generating family on its complex points; the subfan has the lattice of the ambient fan.
  let _ := affinePointTopology g
  let _ := coneChartedSpace Φ.lattice hσ.toIsToricCone hB κ g
  let PΨ := (Φ.subfan S hS hface).analyticAffineChartPartialDiffeomorph (hΦ.subfan S hS hface) σ
    hB κ g n
  let PΦ := Φ.analyticAffineChartPartialDiffeomorph hΦ
    ⟨σ.1, hS (by simpa only [subfan_cones] using σ.2)⟩ hB κ g n
  refine isLocalDiffeomorphAt_of_eqOn (Φ := PΨ.symm.trans PΦ) ?_ fun q hq ↦ ?_
  · simp [PΨ, PΦ]
  · -- A point of the source is the image of a complex point `y` of the chart of `σ`.
    obtain ⟨y, rfl⟩ : ∃ y, PΨ y = q := by
      obtain ⟨y, rfl⟩ : q ∈ range ((Φ.subfan S hS hface).analyticAffineChartι
          (hΦ.subfan S hS hface) σ) := by
        simpa [PΨ] using hq.1
      exact ⟨y, analyticAffineChartPartialDiffeomorph_apply _ _ _ _ _ _ _ y⟩
    have hy : PΨ.symm (PΨ y) = y := PΨ.left_inv (by simp [PΨ])
    have h : Φ.subfanAnalyticMap hΦ S hS hface (PΨ y) = PΦ y := by
      rw [analyticAffineChartPartialDiffeomorph_apply, analyticAffineChartPartialDiffeomorph_apply]
      exact (Φ.subfanAnalyticMap_analyticAffineChartι hΦ S hS hface σ y).trans
        (congrArg _ (Φ.subfanAnalyticChartMap_apply hΦ S hS hface σ y))
    -- The composite `PΦ ∘ PΨ.symm` is, by definition, the composite partial diffeomorphism.
    exact h.trans (congrArg PΦ hy.symm)

end TauCeti.Toric.Fan
