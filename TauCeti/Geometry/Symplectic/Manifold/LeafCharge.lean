/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.PositiveCohomologyAssignment
public import TauCeti.MeasureTheory.Function.Coarea.Eilenberg

/-!
# Almost every leaf of a family of discs meets a set of locally finite area finitely

Taubes reconstructs a pseudoholomorphic curve from a positive cohomology assignment `I` to a
closed set `Z` with locally finite two-dimensional Hausdorff measure in an almost complex
four-manifold `(Y, J)`. Near a point of `Z` he foliates a neighborhood by `J`-holomorphic discs
and reads the curve off the intersections of `Z` with the leaves. The first step is that almost
every leaf meets `Z` in finitely many points. The integer of such a leaf is then the sum of its
local charges at these points, and it bounds their number.

This file proves that step for a family of discs `σ_w : 𝔻 → Y` parametrized by a
finite-dimensional real normed space `P` with an additive Haar measure `ν`; for a foliation of a
four-manifold `P = ℂ` is the transverse coordinate. The family is given by a map
`u : P × ℂ → Y` with `σ_w z = u (w, z)` for `z ∈ 𝔻`. The hypothesis is on the pulled-back set
`S = {(w, z) | ‖z‖ < 1, u (w, z) ∈ Z} ⊆ P × ℂ`: every point of `S` has a neighborhood `U` with
`μH[dim P] (u⁻¹(Z) ∩ U) < ∞`. This holds, for instance, when near each such point `u` is a
diffeomorphism onto an open subset of `Y` in which `Z` has finite `H²` for a Riemannian distance:
the local inverses of `u` are Lipschitz, and Lipschitz maps do not increase `μH[2]` by more than a
constant factor (`LipschitzOnWith.hausdorffMeasure_image_le`).

By Eilenberg's inequality, for almost every `w` the slice of `S` over `w` is discrete
(`TauCeti.ae_isDiscrete_preimage_prodMk`). When `σ_w⁻¹(Z)` is compact it is therefore finite, and
the integer of the leaf is the sum of its local charges over it
(`TauCeti.PositiveCohomologyAssignment.ae_charge_eq_sum_localCharge`). When moreover the leaf is
`J`-holomorphic and constant near none of the points of `σ_w⁻¹(Z)`, the integer is at least the
number of these points (`TauCeti.PositiveCohomologyAssignment.ae_card_le_charge`).

## Main results

* `TauCeti.PositiveCohomologyAssignment.ae_charge_eq_sum_localCharge`: for almost every `w` with
  `σ_w⁻¹(Z)` compact, `σ_w⁻¹(Z)` is finite and the integer of `σ_w` is the sum of its local
  charges over it.
* `TauCeti.PositiveCohomologyAssignment.ae_card_le_charge`: for almost every `w` such that
  `σ_w⁻¹(Z)` is compact and `σ_w` is `J`-holomorphic and constant near no point of `σ_w⁻¹(Z)`,
  the finite set `σ_w⁻¹(Z)` has at most as many points as the integer of `σ_w`.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 6.
* H. Federer, *Geometric Measure Theory*, 2.10.25.
-/

public section

open MeasureTheory Measure Metric Set Module
open Complex.UnitDisc
open scoped Complex.UnitDisc Manifold ContDiff Topology

namespace TauCeti.PositiveCohomologyAssignment

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [MeasurableSpace P] [BorelSpace P] (ν : Measure P) [ν.IsAddHaarMeasure]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y]
  [IsManifold I ∞ Y] {J : SmoothAlmostComplexStructure I Y} {Z : Set Y}
  (A : PositiveCohomologyAssignment J Z) {σ : P → C(𝔻, Y)} {u : P × ℂ → Y}

/-- **Local charges of almost every leaf.** Let `σ_w = u (w, ·)` on `𝔻` be a family of discs
parametrized by a finite-dimensional real normed space `P` with an additive Haar measure `ν`, and
suppose that every point `(w, z)` of `u⁻¹(Z)` with `‖z‖ < 1` has a neighborhood `U` with
`μH[dim P] (u⁻¹(Z) ∩ U) < ∞`. Then for `ν`-almost every `w` with `σ_w⁻¹(Z)` compact, `σ_w⁻¹(Z)`
is a finite set `s` and the integer of `σ_w` is the sum of its local charges over `s`. -/
theorem ae_charge_eq_sum_localCharge (hu : ∀ w (z : 𝔻), u (w, z) = σ w z)
    (hS : ∀ p ∈ u ⁻¹' Z, ‖p.2‖ < 1 → ∃ U ∈ 𝓝 p, μH[finrank ℝ P] (u ⁻¹' Z ∩ U) ≠ ⊤) :
    ∀ᵐ w ∂ν, ∀ h : IsCompact (σ w ⁻¹' Z), ∃ s : Finset 𝔻, (∀ z, σ w z ∈ Z ↔ z ∈ s) ∧
      A.charge (σ w) h = ∑ z ∈ s, A.localCharge (σ w) z := by
  set S := u ⁻¹' Z ∩ {p : P × ℂ | ‖p.2‖ < 1}
  have hS' : ∀ p ∈ S, ∃ U ∈ 𝓝 p, μH[finrank ℝ P] (S ∩ U) ≠ ⊤ := fun p hp ↦
    let ⟨U, hU, hUS⟩ := hS p hp.1 hp.2
    ⟨U, hU, ne_top_of_le_ne_top hUS (measure_mono (inter_subset_inter_left _ inter_subset_left))⟩
  filter_upwards [ae_isDiscrete_preimage_prodMk ν hS'] with w hw h
  -- The image of `σ_w⁻¹(Z)` in `ℂ` is a compact subset of the discrete slice of `S` over `w`.
  have hsub : ((↑) : 𝔻 → ℂ) '' (σ w ⁻¹' Z) ⊆ Prod.mk w ⁻¹' S := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨by simpa [hu] using hz, z.norm_lt_one⟩
  have hfin : (σ w ⁻¹' Z).Finite :=
    (((h.image continuous_coe).finite (hw.mono hsub)).preimage coe_injective.injOn).subset
      (subset_preimage_image _ _)
  have hs (z : 𝔻) : σ w z ∈ Z ↔ z ∈ hfin.toFinset := by simp
  exact ⟨hfin.toFinset, hs, A.charge_eq_sum_localCharge h _ hs⟩

/-- **Counting bound for almost every leaf.** Let `σ_w = u (w, ·)` on `𝔻` be a family of discs
parametrized by a finite-dimensional real normed space `P` with an additive Haar measure `ν`, and
suppose that every point `(w, z)` of `u⁻¹(Z)` with `‖z‖ < 1` has a neighborhood `U` with
`μH[dim P] (u⁻¹(Z) ∩ U) < ∞`. Then for `ν`-almost every `w` such that `σ_w⁻¹(Z)` is compact,
`u (w, ·)` is `J`-holomorphic on the unit disc and `σ_w` is constant near no point of
`σ_w⁻¹(Z)`, the set `σ_w⁻¹(Z)` is finite and has at most as many points as the integer of
`σ_w`. -/
theorem ae_card_le_charge (hu : ∀ w (z : 𝔻), u (w, z) = σ w z)
    (hS : ∀ p ∈ u ⁻¹' Z, ‖p.2‖ < 1 → ∃ U ∈ 𝓝 p, μH[finrank ℝ P] (u ⁻¹' Z ∩ U) ≠ ⊤) :
    ∀ᵐ w ∂ν, ∀ h : IsCompact (σ w ⁻¹' Z),
      IsPseudoholomorphicOn (AlmostComplexStructure.ofComplexModule ℂ).constSmooth J
        (fun z ↦ u (w, z)) (ball 0 1) →
      (∀ z, σ w z ∈ Z → ∀ ε > 0, ∃ z' : 𝔻, dist (z' : ℂ) z < ε ∧ σ w z' ≠ σ w z) →
      ∃ s : Finset 𝔻, (∀ z, σ w z ∈ Z ↔ z ∈ s) ∧ (s.card : ℤ) ≤ A.charge (σ w) h := by
  filter_upwards [A.ae_charge_eq_sum_localCharge ν hu hS] with w hw h hhol hnc
  obtain ⟨s, hs, -⟩ := hw h
  exact ⟨s, hs, A.card_le_charge h _ (hu w) hhol s hs fun z hz ↦ hnc z ((hs z).2 hz)⟩

end TauCeti.PositiveCohomologyAssignment
