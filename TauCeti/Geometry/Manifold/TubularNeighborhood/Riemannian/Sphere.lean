/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.Riemannian.Coordinates
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Metric
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ClosedNeighborhood
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Sphere
public import TauCeti.Topology.VectorBundle.DiscSphere
import TauCeti.Geometry.Manifold.SmoothEmbedding.PartialDiffeomorph

/-!
# Smooth boundaries of normal neighbourhoods

For a closed smooth submanifold of a Riemannian manifold, sufficiently small normal
spheres map by the normal exponential to smooth closed embedded hypersurfaces. Their
images are precisely the frontiers of the corresponding open normal neighbourhoods.
The closed normal discs map onto the closures of those neighbourhoods.

The radius is positive and smooth, may vary over a noncompact core, and can be bounded
by any prescribed positive continuous function. The entire closed neighbourhood can
be kept inside any prescribed open neighbourhood of the core. No completeness of
the ambient metric or normal framing is required.

The sphere bundle uses its regular-level atlas from `sphereBundleChartedSpace` and
the metric induced by orthogonal normal representatives. Its smooth embedding is
transported through the normal-exponential coordinates; a topological embedding
alone would not establish smoothness of this boundary. Closed radius selection is
provided by `OpenPartialHomeomorph.exists_contMDiffMap_isClosedEmbedding_norm_le`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
* M. W. Hirsch, *Differential Topology*, Chapter 4, Theorem 6.3.
-/

public noncomputable section

open Bundle Manifold Set Function Topology TopologicalSpace
open scoped ContDiff Manifold Bundle

namespace TauCeti.SmoothEmbedding

variable {E V P H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [I.Boundaryless] [J.Boundaryless] [T2Space N] [SecondCountableTopology N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ V (fun y : N ↦ TangentSpace J y)]

/-- **Smooth sphere tubular neighbourhood theorem.** A closed smooth submanifold has
arbitrarily small closed normal disc neighbourhoods whose bounding normal spheres
are smooth closed embedded hypersurfaces. The normal exponential maps the discs
onto the closure of the open neighbourhood and the spheres onto its frontier.
The radius is measured in the induced normal metric and may vary over a noncompact core. -/
theorem exists_isSmoothEmbedding_normalExp_sphere
    (f : SmoothEmbedding I J ∞ M N) (hclosed : IsClosed (range f))
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E)
    {O : Set N} (hO : IsOpen O) (hfO : range f ⊆ O)
    {ε : M → ℝ} (hε : Continuous ε) (hεpos : ∀ x, 0 < ε x) :
    let hn : (∞ : ℕ∞ω) ≠ 0 := by simp
    haveI : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
    haveI : IsManifold J (∞ + 1) N := by simpa using (inferInstance : IsManifold J ∞ N)
    letI := f.normalSpaceFiberBundle hn hdim
    letI := f.normalSpaceVectorBundle hn hdim
    letI := f.normalSpaceContMDiffVectorBundle (m := ∞) hn (by simp) hdim
    let ν : M → Type _ := fun x ↦ f.NormalSpace x hn
    let g := f.normalContMDiffRiemannianMetric (m := ∞) hn (by simp) hdim
    letI : RiemannianBundle ν := ⟨g.toRiemannianMetric⟩
    letI : ∀ x, NormedAddCommGroup (ν x) := fun x => inferInstance
    letI : ∀ x, InnerProductSpace ℝ (ν x) := fun x => inferInstance
    letI : IsContMDiffRiemannianBundle I ∞ P ν := Bundle.instIsContMDiffRiemannianBundle g
    ∃ r : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, ∃ hr : ∀ x, 0 < r x,
      (∀ x, r x < ε x) ∧
      {p : TotalSpace P ν | ‖p.2‖ ≤ r p.proj} ⊆ f.normalExpDomain hn ∧
      f.normalExp hn '' {p : TotalSpace P ν | ‖p.2‖ ≤ r p.proj} ⊆ O ∧
      IsOpenEmbedding ({p : TotalSpace P ν | ‖p.2‖ < r p.proj}.domRestrict
        (f.normalExp hn)) ∧
      IsClosedEmbedding ({p : TotalSpace P ν | ‖p.2‖ ≤ r p.proj}.domRestrict
        (f.normalExp hn)) ∧
      IsClosedEmbedding ({p : TotalSpace P ν | ‖p.2‖ = r p.proj}.domRestrict
        (f.normalExp hn)) ∧
      closure (f.normalExp hn '' {p : TotalSpace P ν | ‖p.2‖ < r p.proj}) =
        f.normalExp hn '' {p : TotalSpace P ν | ‖p.2‖ ≤ r p.proj} ∧
      frontier (f.normalExp hn '' {p : TotalSpace P ν | ‖p.2‖ < r p.proj}) =
        f.normalExp hn '' {p : TotalSpace P ν | ‖p.2‖ = r p.proj} ∧
      letI := sphereBundleChartedSpace (F := P) (V := ν) r.contMDiff (by simp) hr
      Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin (Module.finrank ℝ (E × P) - 1) → ℝ) J ∞
        ({p : TotalSpace P ν | ‖p.2‖ = r p.proj}.domRestrict (f.normalExp hn)) := by
  let hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have : IsManifold J (∞ + 1) N := by simpa using (inferInstance : IsManifold J ∞ N)
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  let := f.normalSpaceContMDiffVectorBundle (m := ∞) hn (by simp) hdim
  let ν : M → Type _ := fun x ↦ f.NormalSpace x hn
  let g := f.normalContMDiffRiemannianMetric (m := ∞) hn (by simp) hdim
  let : RiemannianBundle ν := ⟨g.toRiemannianMetric⟩
  let : ∀ x, NormedAddCommGroup (ν x) := fun x => inferInstance
  let : ∀ x, InnerProductSpace ℝ (ν x) := fun x => inferInstance
  let : IsContMDiffRiemannianBundle I ∞ P ν := Bundle.instIsContMDiffRiemannianBundle g
  let : IsContinuousRiemannianBundle P ν :=
    Bundle.instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  have h1 : (1 : ℕ∞ω) ≤ ∞ := by simp
  cases isEmpty_or_nonempty M with
  | inl hM =>
    have : IsEmpty (TotalSpace P ν) := ⟨fun p => hM.false p.proj⟩
    let r : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯ := ContMDiffMap.const (I := I) (I' := 𝓘(ℝ)) (n := ∞) 1
    have hr : ∀ x, 0 < r x := fun x => (hM.false x).elim
    refine ⟨r, hr, fun x => (hM.false x).elim, fun p => (IsEmpty.false p).elim,
      ?_, .of_isEmpty _, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Set.eq_empty_of_isEmpty, image_empty, empty_subset]
    · exact ⟨.of_subsingleton _, by simp only [range_eq_empty]; exact isClosed_empty⟩
    · exact ⟨.of_subsingleton _, by simp only [range_eq_empty]; exact isClosed_empty⟩
    · simp only [Set.eq_empty_of_isEmpty, image_empty, closure_empty]
    · simp only [Set.eq_empty_of_isEmpty, image_empty, frontier_empty]
    · let := sphereBundleChartedSpace (F := P) (V := ν) r.contMDiff h1 hr
      exact ⟨TauCeti.isImmersion_iff_forall_isImmersionAt.mpr fun p => isEmptyElim p,
        .of_subsingleton _⟩
  | inr hM =>
    let := hM
    have : T2Space M := f.isEmbedding.t2Space
    have : SecondCountableTopology M := f.isEmbedding.isInducing.secondCountableTopology
    have : LocallyCompactSpace H := I.locallyCompactSpace
    have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
    have : LocallyCompactSpace G := J.locallyCompactSpace
    have : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace G N
    have : MetrizableSpace N := Manifold.metrizableSpace J N
    -- Choose smooth coordinates first, then shrink their domain around the closed core.
    obtain ⟨Φ, hzero, hdomain, htarget, -, hΦ⟩ :=
      f.exists_partialDiffeomorph_normalExp_subset (m := ∞) hn (by simp) (by simp) hdim hO hfO
    have hcore : Φ ∘ zeroSection P ν = f := by
      funext x
      rw [hΦ]
      exact f.normalExp_zeroSection hn x
    obtain ⟨r, hr, hrε, hdisc, hopen, hd, hs⟩ :=
      Φ.toOpenPartialHomeomorph.exists_contMDiffMap_isClosedEmbedding_norm_le
        (I := I) hzero (hcore ▸ hclosed) hε hεpos ⊤
    let D := {p : TotalSpace P ν | ‖p.2‖ ≤ r p.proj}
    let U := {p : TotalSpace P ν | ‖p.2‖ < r p.proj}
    let S := {p : TotalSpace P ν | ‖p.2‖ = r p.proj}
    have hUD : U ⊆ D := fun p (hp : ‖p.2‖ < r p.proj) => le_of_lt hp
    have hSD : S ⊆ D := fun p (hp : ‖p.2‖ = r p.proj) => le_of_eq hp
    -- Closedness of the disc image replaces compactness of the core.
    have hDclosed : IsClosed (Φ '' D) := by
      simpa only [range_domRestrict, PartialDiffeomorph.toFun'_toOpenPartialHomeomorph]
        using hd.isClosed_range
    have hclosure : closure (Φ '' U) = Φ '' D := by
      refine subset_antisymm (closure_minimal (image_mono hUD) hDclosed) ?_
      rintro _ ⟨p, hp, rfl⟩
      have hpcl : p ∈ closure U := by
        rw [closure_setOf_norm_lt_bundle r.contMDiff.continuous hr]
        exact hp
      exact mem_closure_image (Φ.toOpenPartialHomeomorph.continuousAt (hdisc hp)) hpcl
    have hfrontier : frontier (Φ '' U) = Φ '' S := by
      have hdiff : D \ U = S := by
        ext p
        simp only [D, U, S, mem_sdiff, mem_ofPred_eq, not_lt]
        exact le_antisymm_iff.symm
      have hUopen : IsOpen (Φ '' U) := by
        simpa only [range_domRestrict, PartialDiffeomorph.toFun'_toOpenPartialHomeomorph]
          using hopen.isOpen_range
      rw [frontier, hclosure, hUopen.interior_eq,
        ← (Φ.toPartialEquiv.injOn.mono hdisc).image_sdiff_subset hUD, hdiff]
    -- Transport the regular-level sphere atlas through the smooth coordinates.
    let := sphereBundleChartedSpace (F := P) (V := ν) r.contMDiff h1 hr
    have := isManifold_sphereBundle (F := P) (V := ν) r.contMDiff h1 hr
    have hsmooth := Φ.isSmoothEmbedding_comp h1
      (isSmoothEmbedding_coe_sphereBundle (F := P) (V := ν) r.contMDiff h1 hr)
      (fun p => hdisc (hSD p.property))
    simp only [PartialDiffeomorph.toFun'_toOpenPartialHomeomorph, hΦ] at hopen hd hs
    refine ⟨r, hr, hrε, hdisc.trans hdomain, ?_, hopen, hd, hs, ?_, ?_, ?_⟩
    · rw [← hΦ]
      exact (Φ.toPartialEquiv.mapsTo.mono_left hdisc).image_subset.trans htarget
    · simpa only [hΦ] using hclosure
    · simpa only [hΦ] using hfrontier
    · rw [domRestrict_eq, ← hΦ]
      convert hsmooth using 1

end TauCeti.SmoothEmbedding
