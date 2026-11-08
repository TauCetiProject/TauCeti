/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Rectifiable.Bilipschitz
public import TauCeti.Geometry.MeasureTheory.Rectifiable.TangentCone
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import TauCeti.MeasureTheory.Function.SpecialFunctions.Projection
import TauCeti.Geometry.Euclidean.Volume.Measure
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Measurable approximate tangent projections

The approximate tangent planes of a countably rectifiable set can be chosen measurably.
Planes are encoded by their orthogonal projections, as operators on the ambient space.
For a null-measurable set with locally finite normalized Hausdorff measure, the chosen
operator is almost everywhere the projection onto a plane of the parameter dimension,
and the portion of the set outside each cone about that plane has density zero.
This supplies a measurable plane field for tangential differentiation and integration;
uniqueness of the plane is a separate assertion.

On a bi-Lipschitz patch we transport the measurable projection onto the derivative range
through the inverse coordinates. A countable choice of patches gives a measurable field;
measure differentiation controls the other patches. No measurable structure on the type
of submodules is required, and dimension zero is included.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §11 (approximate tangents).
* P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Theorem 15.19.
-/

public section

open Filter Metric MeasureTheory Set
open scoped ENNReal NNReal Topology

/-- On a bi-Lipschitz patch, the plane with pointwise cone containment can be chosen with
Borel measurable orthogonal projection. The parametrization and its inverse are only
required to be Lipschitz on the Borel parameter domain and its image, respectively. -/
theorem LipschitzOnWith.exists_measurable_tangent_projection
    {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    {f : U → V} {s : Set U} {K L : ℝ≥0} (hf : LipschitzOnWith K f s)
    (hs : MeasurableSet s) (hi : AntilipschitzWith L (s.domRestrict f)) :
    ∃ Q : V → V →L[ℝ] V, Measurable Q ∧
      ∀ᵐ y ∂(μHE[Module.finrank ℝ U] : Measure V), y ∈ f '' s →
        ∃ P : Submodule ℝ V, Module.finrank ℝ P = Module.finrank ℝ U ∧
          Q y = P.starProjection ∧
          ∀ ε > (0 : ℝ), ∃ r > 0, ∀ z ∈ f '' s, dist z y < r →
            infDist (z - y) (P : Set V) ≤ ε * dist z y := by
  obtain ⟨g, hg, hfg⟩ := hf.extend_finite_dimension
  have himage : f '' s = g '' s := image_congr hfg
  have hi' : AntilipschitzWith L (s.domRestrict g) := by
    intro x y
    simpa only [domRestrict_apply, ← hfg x.property, ← hfg y.property] using hi x y
  rw [himage]
  have he : MeasurableEmbedding (s.domRestrict g) :=
    hg.continuous.continuousOn.measurableEmbedding hs (injOn_iff_injective.mpr hi'.injective)
  let A : s → V →L[ℝ] V := fun x ↦ (fderiv ℝ g x).range.starProjection
  obtain ⟨Q, hQm, hQ⟩ := he.exists_measurable_extend (g := A)
    (((measurable_fderiv ℝ g).starProjection_range).comp measurable_subtype_coe)
    (fun _ ↦ ⟨0⟩)
  refine ⟨Q, hQm, ?_⟩
  filter_upwards [hg.ae_exists_fderiv_range_forall_infDist_le hi'] with y hy hyimage
  obtain ⟨x, hx, rfl, hdim, hcone⟩ := hy hyimage
  exact ⟨(fderiv ℝ g x).range, hdim, congrFun hQ ⟨x, hx⟩, hcone⟩

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {k : ℕ} {E : Set V}

/-- A countably rectifiable set admits a countable Borel cover up to a Hausdorff-null set,
with measurable projection fields and pointwise cone containment on each piece. The pieces
may extend beyond the original set. -/
theorem CountablyRectifiable.exists_measurable_cover_tangent_projection
    (hE : CountablyRectifiable k E) :
    ∃ (T : ℕ → Set V) (Q : ℕ → V → V →L[ℝ] V),
      (∀ n, MeasurableSet (T n)) ∧ (∀ n, Measurable (Q n)) ∧
      μHE[k] (E \ ⋃ n, T n) = 0 ∧
      ∀ n, ∀ y ∈ T n, ∃ P : Submodule ℝ V, Module.finrank ℝ P = k ∧
        Q n y = P.starProjection ∧
        ∀ ε > (0 : ℝ), ∃ r > 0, ∀ z ∈ T n, dist z y < r →
          infDist (z - y) (P : Set V) ≤ ε * dist z y := by
  classical
  obtain ⟨A, f, hAm, hbi, hcover⟩ := hE.exists_bilipschitz_cover
  choose K L hLip hAnti using hbi
  have hex (n : ℕ) :=
    (hLip n).lipschitzOnWith.exists_measurable_tangent_projection (hAm n) (hAnti n)
  simp only [finrank_euclideanSpace_fin] at hex
  choose Q hQm hQ using hex
  let S (n : ℕ) := f n '' A n
  have hSm (n : ℕ) : MeasurableSet (S n) :=
    (hAm n).image_of_continuousOn_injOn (hLip n).continuous.continuousOn
      (injOn_iff_injective.mpr (hAnti n).injective)
  have hgood (n : ℕ) := (hQ n).exists_measurable_mem
  choose B hBae hBm hB using hgood
  refine ⟨fun n ↦ S n ∩ B n, Q, fun n ↦ (hSm n).inter (hBm n), hQm, ?_, ?_⟩
  · apply ae_le_set.mp
    refine (ae_le_set.mpr hcover).trans
      (Filter.EventuallySubset.countable_iUnion fun n ↦ ?_)
    filter_upwards [hBae n] with y hy hys
    exact ⟨hys, hy⟩
  · intro n y hy
    obtain ⟨P, hdim, hproj, hcone⟩ := hB n y hy.2 hy.1
    exact ⟨P, hdim, hproj, fun ε hε ↦ by
      obtain ⟨r, hr, hlocal⟩ := hcone ε hε
      exact ⟨r, hr, fun z hz ↦ hlocal z hz.1⟩⟩

/-- **Measurable approximate tangent planes.** A countably rectifiable, null-measurable set
with locally finite normalized Hausdorff measure admits a Borel measurable field of
operators which, almost everywhere on the set, are orthogonal projections onto approximate
tangent `k`-planes. The cone-density characterization and the dimension are supplied together
with the field. No uniqueness is asserted, and values away from the set are unspecified. -/
theorem CountablyRectifiable.exists_measurable_approximate_tangent_projection
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    ∃ Q : V → V →L[ℝ] V, Measurable Q ∧
      ∀ᵐ x ∂μHE[k], x ∈ E → ∃ P : Submodule ℝ V, Module.finrank ℝ P = k ∧
        Q x = P.starProjection ∧
        ∀ ε > (0 : ℝ), Tendsto (fun r ↦
          μHE[k] {z ∈ E ∩ closedBall x r | ε * dist z x < infDist (z - x) (P : Set V)} /
            volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0) := by
  classical
  obtain ⟨T, A, hTm, hAm, hcover, hcone⟩ := hE.exists_measurable_cover_tangent_projection
  let S := ⋃ n, T n
  have hindex (x : S) : ∃ n, (x : V) ∈ T n := mem_iUnion.mp x.property
  let F : S → V →L[ℝ] V := fun x ↦ A (Nat.find (hindex x)) x
  have hFm : Measurable F := Measurable.find
    (fun n ↦ (hAm n).comp measurable_subtype_coe)
    (fun n ↦ (hTm n).preimage measurable_subtype_coe) hindex
  have he := MeasurableEmbedding.subtype_coe (MeasurableSet.iUnion hTm)
  obtain ⟨Q, hQm, hQ⟩ := he.exists_measurable_extend hFm (fun _ ↦ ⟨(0 : V →L[ℝ] V)⟩)
  refine ⟨Q, hQm, ?_⟩
  have hzero (n : ℕ) : ∀ᵐ x ∂μHE[k], x ∉ E \ T n → Tendsto (fun r ↦
      μHE[k] ((E \ T n) ∩ closedBall x r) /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0) := by
    have : IsLocallyFiniteMeasure (μHE[k].restrict (E \ T n)) := by
      rw [Set.sdiff_eq, inter_comm, ← Measure.restrict_restrict (hTm n).compl]
      infer_instance
    exact ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div_of_isLocallyFiniteMeasure k
      (hEm.diff (hTm n).nullMeasurableSet)
  filter_upwards [ae_le_set.mpr hcover, ae_all_iff.mpr hzero] with x hcov hzero hxE
  have hxS : x ∈ S := hcov hxE
  let n := Nat.find (hindex ⟨x, hxS⟩)
  have hxn : x ∈ T n := Nat.find_spec (hindex ⟨x, hxS⟩)
  obtain ⟨P, hdim, hproj, hP⟩ := hcone n x hxn
  refine ⟨P, hdim, (congrFun hQ ⟨x, hxS⟩).trans hproj, fun ε hε ↦ ?_⟩
  obtain ⟨δ, hδ, hlocal⟩ := hP ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hzero n (fun h ↦ h.2 hxn))
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδ)] with r hr
  gcongr
  intro z hz
  refine ⟨⟨hz.1.1, ?_⟩, hz.1.2⟩
  intro hzT
  exact (not_lt_of_ge (hlocal z hzT ((mem_closedBall.mp hz.1.2).trans_lt hr))) hz.2

end TauCeti
