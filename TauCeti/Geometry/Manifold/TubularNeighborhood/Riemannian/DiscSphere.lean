/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.Riemannian.Coordinates
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Metric
public import TauCeti.Topology.VectorBundle.DiscSphere

/-!
# Closed normal discs in a Riemannian ambient manifold

For a compact smoothly embedded submanifold, the normal exponential embeds closed normal
discs of sufficiently small positive smooth radius. The open discs map to an open neighbourhood
of the core, and the normal spheres map precisely onto its frontier. The entire closed
neighbourhood can be kept inside any prescribed open neighbourhood of the core.

The radius uses the induced normal metric, measured by orthogonal representatives in the
ambient tangent spaces. The normal bundle carries its intrinsic quotient topology and
complementary-coordinate atlas. No normal framing or completeness of the ambient metric
is required. These are the closed neighbourhoods and boundary spheres used when removing a
tubular neighbourhood in surgery.

## References

* M. W. Hirsch, *Differential Topology*, Chapter 4, Theorem 6.3.
* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
-/

public noncomputable section

open Bundle Manifold Set Function Topology
open scoped ContDiff Manifold

namespace TauCeti.SmoothEmbedding

variable {E V P H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [I.Boundaryless] [J.Boundaryless] [T2Space N] [SecondCountableTopology N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J ∞ V (fun y : N ↦ TangentSpace J y)]

/-- **Closed normal disc and sphere tubular neighbourhood theorem.** For a compact smooth
submanifold in a Riemannian manifold, the normal exponential embeds closed normal discs of
positive smooth radius inside any prescribed open neighbourhood. Their interiors map openly,
and their bounding normal spheres are exactly the frontier of that open image. Norms are
those of the induced normal metric, not of an auxiliary compression metric. -/
theorem exists_isClosedEmbedding_normalExp_disc
    (f : SmoothEmbedding I J ∞ M N)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E)
    {O : Set N} (hO : IsOpen O) (hfO : range f ⊆ O) :
    let hn : (∞ : ℕ∞ω) ≠ 0 := by simp
    letI := f.normalSpaceFiberBundle hn hdim
    let ν : M → Type _ := fun x ↦ f.NormalSpace x hn
    letI : RiemannianBundle ν := ⟨f.normalRiemannianMetric hn⟩
    ∃ r : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, (∀ x, 0 < r x) ∧
      {p : TotalSpace P ν | ‖p.2‖ ≤ r p.proj} ⊆ f.normalExpDomain hn ∧
      f.normalExp hn '' {p : TotalSpace P ν | ‖p.2‖ ≤ r p.proj} ⊆ O ∧
      IsOpenEmbedding (({p : TotalSpace P ν | ‖p.2‖ < r p.proj}).domRestrict
        (f.normalExp hn)) ∧
      IsClosedEmbedding (({p : TotalSpace P ν | ‖p.2‖ ≤ r p.proj}).domRestrict
        (f.normalExp hn)) ∧
      IsClosedEmbedding (({p : TotalSpace P ν | ‖p.2‖ = r p.proj}).domRestrict
        (f.normalExp hn)) ∧
      closure (f.normalExp hn '' {p : TotalSpace P ν | ‖p.2‖ < r p.proj}) =
        f.normalExp hn '' {p : TotalSpace P ν | ‖p.2‖ ≤ r p.proj} ∧
      frontier (f.normalExp hn '' {p : TotalSpace P ν | ‖p.2‖ < r p.proj}) =
        f.normalExp hn '' {p : TotalSpace P ν | ‖p.2‖ = r p.proj} := by
  let hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  let ν : M → Type _ := fun x ↦ f.NormalSpace x hn
  let : RiemannianBundle ν := ⟨f.normalRiemannianMetric hn⟩
  let : ∀ x, NormedAddCommGroup (ν x) := fun x => inferInstance
  let : ∀ x, InnerProductSpace ℝ (ν x) := fun x => inferInstance
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have : IsManifold J (∞ + 1) N := by simpa using (inferInstance : IsManifold J ∞ N)
  let := f.normalSpaceContMDiffVectorBundle (m := ∞) hn (by simp) hdim
  let g := f.normalContMDiffRiemannianMetric (m := ∞) hn (by simp) hdim
  let : IsContinuousRiemannianBundle P ν := by
    have hg : g.toContinuousRiemannianMetric.toRiemannianMetric =
        f.normalRiemannianMetric hn :=
      f.toRiemannianMetric_normalContMDiffRiemannianMetric (m := ∞) hn (by simp) hdim
    have h := Bundle.instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
    rw [hg] at h
    exact h
  have : T2Space M := f.isEmbedding.t2Space
  cases isEmpty_or_nonempty M with
  | inl hM =>
    have : IsEmpty (TotalSpace P ν) := ⟨fun p => hM.false p.proj⟩
    refine ⟨⟨fun _ => 1, contMDiff_const⟩, fun x => (hM.false x).elim,
      (fun p _ => (hM.false p.proj).elim), ?_⟩
    simp only [Set.eq_empty_of_isEmpty, image_empty, empty_subset, frontier_empty,
      closure_empty, true_and]
    refine ⟨.of_isEmpty _, ⟨.of_subsingleton _, ?_⟩, ⟨.of_subsingleton _, ?_⟩, trivial⟩ <;>
      simpa only [range_eq_empty] using (isClosed_empty : IsClosed (∅ : Set N))
  | inr hM =>
    let := hM
    -- Shrink smooth normal-exponential coordinates using the induced fibre metric.
    obtain ⟨Φ, hzero, hdomain, htarget, -, hΦ⟩ :=
      f.exists_partialDiffeomorph_normalExp_subset (m := ∞) hn (by simp) (by simp) hdim hO hfO
    obtain ⟨r, hr, -, hdisc⟩ := Φ.open_source.exists_contMDiffMap_norm_le_subset_bundle
      (I := I) (V := ν) (n := ⊤) hzero (continuous_const (y := (1 : ℝ)))
      (fun _ => zero_lt_one)
    let D := {p : TotalSpace P ν | ‖p.2‖ ≤ r p.proj}
    let U := {p : TotalSpace P ν | ‖p.2‖ < r p.proj}
    let S := {p : TotalSpace P ν | ‖p.2‖ = r p.proj}
    have hD : D ⊆ Φ.source := fun p hp => hdisc p.proj p.2 hp
    have hUD : U ⊆ D := fun p (hp : ‖p.2‖ < r p.proj) => le_of_lt hp
    have hSD : S ⊆ D := fun p (hp : ‖p.2‖ = r p.proj) => le_of_eq hp
    -- Compact closed discs have closed images; the sphere is a closed subset of the discs.
    have hcompact : IsCompact D := TauCeti.isCompact_setOf_norm_le_bundle r.contMDiff.continuous
    have hd : IsClosedEmbedding (D.domRestrict Φ) := by
      let : CompactSpace D := isCompact_iff_compactSpace.mp hcompact
      exact ((Φ.toOpenPartialHomeomorph.continuousOn.mono hD).domRestrict).isClosedEmbedding
        (fun p q hpq => Subtype.ext (Φ.toPartialEquiv.injOn (hD p.property) (hD q.property) hpq))
    have hs : IsClosed S := isClosed_eq (TauCeti.continuous_norm_bundle P ν)
      (r.contMDiff.continuous.comp (FiberBundle.continuous_proj P ν))
    have hsphere : IsClosedEmbedding (S.domRestrict Φ) :=
      hd.comp (IsClosedEmbedding.inclusion hSD (hs.preimage continuous_subtype_val))
    have hu : IsOpen U := isOpen_lt (TauCeti.continuous_norm_bundle P ν)
      (r.contMDiff.continuous.comp (FiberBundle.continuous_proj P ν))
    have hopen : IsOpenEmbedding (U.domRestrict Φ) :=
      Φ.toOpenPartialHomeomorph.isOpenEmbedding_restrict.comp
        (IsOpenEmbedding.inclusion (hUD.trans hD) (hu.preimage continuous_subtype_val))
    refine ⟨r, hr, hD.trans hdomain, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hΦ]
      exact (Φ.toPartialEquiv.mapsTo.mono_left hD).image_subset.trans htarget
    · simpa only [hΦ] using hopen
    · simpa only [hΦ] using hd
    · simpa only [hΦ] using hsphere
    · simpa only [PartialDiffeomorph.toFun'_toOpenPartialHomeomorph, hΦ] using
        Φ.toOpenPartialHomeomorph.closure_image_norm_lt_bundle r.contMDiff.continuous hr hD
    · simpa only [PartialDiffeomorph.toFun'_toOpenPartialHomeomorph, hΦ] using
        Φ.toOpenPartialHomeomorph.frontier_image_norm_lt_bundle r.contMDiff.continuous hr hD

end TauCeti.SmoothEmbedding
