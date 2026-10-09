/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Covolume
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Tessellation
import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex.GaussBonnet

/-!
# Fundamental polygons of Fuchsian groups

Let `σ` be a side pairing of a convex hyperbolic polygon `P`, whose vertices may be finite or
ideal, and let `Γ ≤ PSL(2, ℝ)` contain the side-pairing maps. Suppose that the translates
`γ • P`, `γ ∈ Γ`, form a locally finite family and that distinct translates of the interior of
`P` are disjoint. These are the tessellation hypotheses of Poincaré's polygon theorem. Then the
carrier of `P` is a measurable fundamental domain for `Γ`: the translates cover `ℍ`, and two of
them meet only along the boundary of `P`, a finite union of geodesic pieces, which is null.

Consequently `Γ` is a cofinite Fuchsian group, and its covolume is the hyperbolic area of `P`,
given by the Gauss–Bonnet formula `(n - 2) π - ∑ αᵢ` in terms of the number `n` of vertices and
the interior angles `αᵢ`, an ideal vertex contributing angle `0`. This is the area of the quotient
`Γ \ ℍ` read off from a fundamental polygon.

## Main results

* `ConvexPolygon.SidePairing.isFundamentalDomain_carrier`: a side-paired polygon with locally
  finite, interior-disjoint translates is a measurable fundamental domain.
* `ConvexPolygon.SidePairing.isCofinite`: `Γ` is a cofinite Fuchsian group.
* `ConvexPolygon.SidePairing.covolume_eq`: the covolume of `Γ` is `(n - 2) π - ∑ αᵢ`.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, Chapter 9 (locally finite fundamental polygons).
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §§3.1 and 4.1 (fundamental regions, and the area of `Γ \ ℍ` as the area of a
  fundamental region).
-/

public section

open MeasureTheory Set UpperHalfPlane
open scoped MatrixGroups Pointwise Real

namespace TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing

variable {n : ℕ} [NeZero n] {P : ConvexPolygon n} (σ : P.SidePairing) {Γ : Subgroup PSL(2, ℝ)}

/-- **A locally finite side-paired polygon with disjoint translated interiors is a fundamental
domain.** If a subgroup `Γ` of `PSL(2, ℝ)` contains every side-pairing map, its translates of the
polygon are locally finite, and distinct translates of the interior are disjoint, then the polygon
is a measurable fundamental domain for `Γ`. -/
theorem isFundamentalDomain_carrier (hmap : ∀ i, σ.map i ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier)) :
    IsFundamentalDomain Γ P.carrier := by
  refine .of_disjoint_smul_interior P.measurableSet_carrier.nullMeasurableSet
    (.of_forall fun z ↦ ?_) (measure_smul_null P.volume_frontier_carrier) hdisj
  obtain ⟨γ, hγ⟩ := mem_iUnion.1 (σ.iUnion_smul_carrier_eq_univ hmap hlf ▸ mem_univ z)
  exact ⟨γ⁻¹, mem_smul_set_iff_inv_smul_mem.1 hγ⟩

/-- **A group with a fundamental polygon is cofinite.** Under the hypotheses of
`isFundamentalDomain_carrier`, the subgroup `Γ` is discrete and `Γ \ ℍ` has finite area. -/
theorem isCofinite (hmap : ∀ i, σ.map i ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier)) :
    Γ.IsCofinite :=
  have : DiscreteTopology Γ := TauCeti.discreteTopology_of_locallyFinite_smul
    (P.nonempty_interior_carrier.mono interior_subset) hlf
  (σ.isFundamentalDomain_carrier hmap hlf hdisj).isCofinite_of_volume_ne_top
    P.volume_carrier_ne_top

/-- **The covolume of a group with a fundamental polygon.** Under the hypotheses of
`isFundamentalDomain_carrier`, the hyperbolic area of `Γ \ ℍ` is `(n - 2) π` minus the sum of the
interior angles of the polygon, the angle at an ideal vertex being `0`. -/
theorem covolume_eq (hmap : ∀ i, σ.map i ∈ Γ)
    (hlf : LocallyFinite fun γ : Γ ↦ (γ : PSL(2, ℝ)) • P.carrier)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier)) :
    covolume Γ ℍ = ENNReal.ofReal ((n - 2) * π - ∑ i, P.interiorAngle i) := by
  have := (σ.isCofinite hmap hlf hdisj).discreteTopology
  rw [(σ.isFundamentalDomain_carrier hmap hlf hdisj).covolume_eq_volume, P.volume_carrier]

end TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing
