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
import TauCeti.Geometry.Manifold.Meagre

/-!
# Meagreness of critical values on manifolds

The critical values of a smooth map between finite-dimensional real manifolds without boundary
form a meagre set, provided the source is Lindelöf. The dimensions need not be equal. More
locally, it suffices that the map be smooth at the points of a Lindelöf set of critical points.
Consequently an everywhere rank-deficient real analytic map has meagre image.

We use the existing Sard--Smale theorem in finite-dimensional coordinate domains. The
regular-point comparison in arbitrary extended charts identifies the critical points in those
domains. Meagreness is preserved by chart inverses, and a countable neighborhood subcover in the
source gives the global assertion (`TauCeti.isMeagre_image_of_forall_isMeagre_image_extChartAt`).
No decomposition of analytic zero sets is needed.

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

omit [J.Boundaryless] in
/-- The critical points seen by a fixed pair of charts have meagre coordinate image. -/
private theorem isMeagre_image_extChartAt_inter_charts
    (hf : ∀ x ∈ s, ContMDiffAt I J ∞ f x) (hs : ∀ x ∈ s, ¬ IsRegularPoint I J f x)
    (x₀ : M) (y₀ : N) :
    IsMeagre ((extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm) ''
      (extChartAt I x₀ '' (s ∩ (chartAt H x₀).source ∩ f ⁻¹' (chartAt H' y₀).source))) := by
  let g : E → E' := extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm
  let u := s ∩ (chartAt H x₀).source ∩ f ⁻¹' (chartAt H' y₀).source
  let v := extChartAt I x₀ '' u
  have hgs : ∀ z ∈ v, ContDiffAt ℝ ∞ g z := by
    rintro _ ⟨x, hx, rfl⟩
    exact ((contMDiffAt_iff_of_mem_source hx.1.2 hx.2).1 (hf x hx.1.1)).2.contDiffAt
      (by simp [I.range_eq_univ])
  have hcrit : ∀ z ∈ v, ¬ Surjective (fderiv ℝ g z) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (isRegularPoint_iff_surjective_fderiv_extChartAt
      ((hf x hx.1.1).mdifferentiableAt (by simp)) hx.1.2 hx.2).not.mp (hs x hx.1.1)
  have h := isMeagre_image_criticalPoints_of_isFredholm (U := v) hgs
    (fun z _ ↦ (fderiv ℝ g z).isFredholm_of_finiteDimensional)
    (fun _ _ ↦ by exact_mod_cast le_top)
  apply h.mono
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨z, ⟨hz, hcrit z hz⟩, rfl⟩

/-- **Sard's theorem, in Baire category form.** The image of a Lindelöf set of critical points
at which a map is smooth is meagre. Both manifolds are finite-dimensional and without boundary;
their dimensions may differ. Smoothness is required in the ambient manifold at points of `s`,
not merely within `s`. -/
theorem isMeagre_image_of_not_isRegularPoint [LindelofSpace s]
    (hf : ∀ x ∈ s, ContMDiffAt I J ∞ f x) (hs : ∀ x ∈ s, ¬ IsRegularPoint I J f x) :
    IsMeagre (f '' s) :=
  isMeagre_image_of_forall_isMeagre_image_extChartAt (fun x hx ↦ (hf x hx).continuousAt)
    fun x _ ↦ ⟨univ, univ_mem, by
      simpa only [inter_univ] using isMeagre_image_extChartAt_inter_charts hf hs x (f x)⟩

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
