/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue.Open
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Analysis.Fredholm.Basic
import TauCeti.Analysis.Fredholm.SardSmale
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Topology.OpenPartialHomeomorph.Baire

/-!
# Meagreness of critical values on manifolds

The critical values of a smooth map between finite-dimensional real manifolds without boundary
form a meagre set, provided the source is Lindelöf. The dimensions need not be equal. More
locally, it suffices that the map be smooth at the points of a Lindelöf set of critical points.
Consequently an everywhere rank-deficient real analytic map has meagre image.

We use the existing Sard--Smale theorem in finite-dimensional coordinate domains. The
regular-point comparison in arbitrary extended charts identifies the critical points in those
domains. Meagreness is preserved by chart inverses, and a countable neighborhood subcover in the
source gives the global assertion. No decomposition of analytic zero sets is needed.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore
di Pisa (3) 18 (1964), 449–474, §2, Lemma 1 (the real analytic case).
* S. Smale, *An infinite dimensional version of Sard's theorem*, American Journal of
Mathematics 87 (1965), 861–866; the local input is
`TauCeti.isMeagre_image_criticalPoints_of_isFredholm`.
-/

public section

open Function Module Set Filter
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {f : M → N} {s : Set M}

/-- The image of critical points seen by a fixed pair of charts is meagre in the target
manifold. -/
private theorem isMeagre_image_inter_charts
    (hf : ∀ x ∈ s, ContMDiffAt I J ∞ f x) (hs : ∀ x ∈ s, ¬ IsRegularPoint I J f x)
    (x₀ : M) (y₀ : N) :
    IsMeagre (f '' (s ∩ (chartAt H x₀).source ∩ f ⁻¹' (chartAt H' y₀).source)) := by
  let g : E → E' := extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm
  let u := s ∩ (chartAt H x₀).source ∩ f ⁻¹' (chartAt H' y₀).source
  let v := extChartAt I x₀ '' u
  have hgs : ∀ z ∈ v, ContDiffAt ℝ ∞ g z := by
    rintro _ ⟨x, hx, rfl⟩
    exact ((contMDiffAt_iff_of_mem_source hx.1.2 hx.2).1 (hf x hx.1.1)).2.contDiffAt
      (by simp [I.range_eq_univ])
  have hcrit : ∀ z ∈ v, ¬ Surjective (fderiv ℝ g z) := by
    rintro _ ⟨x, hx, rfl⟩
    have h := isRegularPoint_iff_surjective_fderivWithin
      ((hf x hx.1.1).mdifferentiableAt (by simp)) hx.1.2 hx.2
    simpa only [I.range_eq_univ, fderivWithin_univ] using (h.not.mp (hs x hx.1.1))
  have hgv : IsMeagre (g '' v) := by
    have h := isMeagre_image_criticalPoints_of_isFredholm (U := v) hgs
      (fun z _ ↦ (fderiv ℝ g z).isFredholm_of_finiteDimensional)
      (fun _ _ ↦ by exact_mod_cast le_top)
    apply h.mono
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, ⟨hz, hcrit z hz⟩, rfl⟩
  -- The boundaryless extended chart is an open partial homeomorphism.
  let e := (chartAt H' y₀).transHomeomorph J.toHomeomorph
  -- Both chart constructions have forward map J ∘ chartAt H' y₀: transHomeomorph
  -- composes with J.toHomeomorph, whose forward map is J, while extChartAt extends by J.
  have he (y : N) : e y = extChartAt J y₀ y := rfl
  have hmem : g '' v ⊆ e.target := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hxc : x ∈ (extChartAt I x₀).source := by rw [extChartAt_source]; exact hx.1.2
    simpa only [g, comp_apply, (extChartAt I x₀).left_inv hxc, ← he] using e.map_source hx.2
  have h := e.symm.isMeagre_image hgv hmem
  have himage : e.symm '' (g '' v) = f '' u := by
    rw [image_image, image_image]
    apply image_congr
    intro x hx
    have hxc : x ∈ (extChartAt I x₀).source := by rw [extChartAt_source]; exact hx.1.2
    simp only [comp_apply, g, (extChartAt I x₀).left_inv hxc, ← he, e.left_inv hx.2]
  rwa [himage] at h

/-- **Sard's theorem, in Baire category form.** The image of a Lindelöf set of critical points
at which a map is smooth is meagre. Both manifolds are finite-dimensional and without boundary;
their dimensions may differ. Smoothness is required in the ambient manifold at points of `s`,
not merely within `s`. -/
theorem isMeagre_image_of_not_isRegularPoint [LindelofSpace s]
    (hf : ∀ x ∈ s, ContMDiffAt I J ∞ f x) (hs : ∀ x ∈ s, ¬ IsRegularPoint I J f x) :
    IsMeagre (f '' s) := by
  let U := fun x : M ↦ (chartAt H x).source ∩ f ⁻¹' (chartAt H' (f x)).source
  have hU : ∀ x ∈ s, U x ∈ 𝓝 x := fun x hx ↦
    inter_mem (chart_source_mem_nhds H x)
      ((hf x hx).continuousAt.preimage_mem_nhds (chart_source_mem_nhds H' (f x)))
  obtain ⟨t, htc, -, hcover⟩ := (IsLindelof.of_coe (s := s)).elim_nhds_subcover U hU
  refine (isMeagre_biUnion htc fun x _ ↦ isMeagre_image_inter_charts hf hs x (f x)).mono ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.1 (hcover hx)
  exact mem_iUnion₂.2 ⟨z, hz, x, ⟨⟨hx, hxz.1⟩, hxz.2⟩, rfl⟩

/-- The critical values of a smooth map from a Lindelöf finite-dimensional manifold without
boundary form a meagre set. -/
theorem _root_.ContMDiff.isMeagre_image_criticalPoints [LindelofSpace M] {n : ℕ∞ω}
    (hf : ContMDiff I J n f) (hn : ∞ ≤ n) :
    IsMeagre (f '' {x | ¬ IsRegularPoint I J f x}) := by
  have hf_smooth := hf.of_le hn
  have : LindelofSpace {x | ¬ IsRegularPoint I J f x} :=
    isLindelof_iff_lindelofSpace.1
      (isOpen_setOf_isRegularPoint hf_smooth (by simp)).isClosed_compl.isLindelof
  exact isMeagre_image_of_not_isRegularPoint (fun x _ ↦ hf_smooth.contMDiffAt) (fun _ hx ↦ hx)

/-- An everywhere rank-deficient smooth or real analytic map from a Lindelöf manifold without
boundary has meagre image. The rank is the dimension of the range of its native manifold
derivative. For an analytic map, the regularity hypothesis `∞ ≤ ω` is automatic. -/
theorem _root_.ContMDiff.isMeagre_range_of_finrank_mfderiv_lt [LindelofSpace M] {n : ℕ∞ω}
    (hf : ContMDiff I J n f) (hn : ∞ ≤ n)
    (hrank : ∀ x, finrank ℝ (mfderiv I J f x).range < finrank ℝ E') :
    IsMeagre (range f) := by
  have hcrit (x : M) : ¬ IsRegularPoint I J f x := by
    intro hx
    have h := hrank x
    rw [LinearMap.range_eq_top.2 (isRegularPoint_iff.1 hx), finrank_top,
      finrank_tangentSpace] at h
    exact (lt_irrefl _ h)
  have h := hf.isMeagre_image_criticalPoints hn
  have heq : {x | ¬ IsRegularPoint I J f x} = univ := eq_univ_of_forall hcrit
  simpa only [heq, image_univ] using h

end TauCeti
