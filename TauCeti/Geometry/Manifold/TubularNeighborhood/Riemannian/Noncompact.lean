/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Geometry.Manifold.TubularNeighborhood.Riemannian.Coordinates
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Metric
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ClosedNeighborhood

/-!
# Closed normal discs over closed submanifolds

For a smooth embedding with closed image into a finite-dimensional Riemannian manifold,
the normal exponential embeds sufficiently small closed normal discs and spheres as closed
subsets of the ambient manifold. The radius is a positive smooth function, measured in the
induced normal metric, and can be chosen below any prescribed positive continuous bound.
The whole disc image can be kept inside any prescribed open neighbourhood of the core.

Neither compactness of the core, completeness of the ambient metric, nor a normal framing
is required. The open discs embed openly; the closed discs remain in the natural domain of
the normal exponential. Closedness follows by shrinking the target of the normal-exponential
coordinates around the closed core before selecting the radius.

Without closedness of the image, the normal exponential is still a partial diffeomorphism whose
source is exactly an open normal disc bundle of positive smooth radius
(`SmoothEmbedding.exists_partialDiffeomorph_normalExp_norm_lt_subset`). Since that source is
described by the normal metric alone, it is preserved by every bundle map acting isometrically on
the fibres, as in equivariant tubular neighbourhoods.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
* M. W. Hirsch, *Differential Topology*, Chapter 4, Theorem 6.3.

The construction uses `SmoothEmbedding.exists_partialDiffeomorph_normalExp_subset`,
`SmoothEmbedding.isContMDiffRiemannianBundle_normalRiemannianMetric`, and closed disc selection
in bundle coordinates. `SmoothEmbedding.exists_partialDiffeomorph_normalExp_norm_le_subset`
provides the coordinates and radius together.
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

/-- **Normal-exponential coordinates on an open disc bundle.** For a smooth embedding into a
Riemannian manifold, there are a positive smooth radius `r` on `M` and a partial diffeomorphism
equal to the normal exponential whose source is exactly the open disc bundle `{ν | ‖ν‖ < r}`, for
the metric induced by orthogonal representatives, and whose target lies in any prescribed open
neighbourhood `O` of `f(M)`. Neither compactness nor closedness of `f(M)` is used. Nonemptiness of
`M` is used only to define the inverse away from the target. -/
theorem exists_partialDiffeomorph_normalExp_norm_lt_subset [Nonempty M]
    (f : SmoothEmbedding I J ∞ M N)
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E)
    {O : Set N} (hO : IsOpen O) (hfO : range f ⊆ O) :
    let hn : (∞ : ℕ∞ω) ≠ 0 := by simp
    letI := f.normalSpaceFiberBundle hn hdim
    let ν : M → Type _ := fun x ↦ f.isImmersion.NormalSpace x hn
    letI : RiemannianBundle ν := ⟨f.normalRiemannianMetric hn⟩
    ∃ (Φ : PartialDiffeomorph (I.prod 𝓘(ℝ, P)) J (TotalSpace P ν) N ∞)
        (r : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯),
      ⇑Φ = f.normalExp hn ∧ (∀ x, 0 < r x) ∧
      Φ.source = {p : TotalSpace P ν | ‖p.snd‖ < r p.proj} ∧ Φ.target ⊆ O := by
  let hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  let := f.normalSpaceFiberBundle hn hdim
  let ν : M → Type _ := fun x ↦ f.isImmersion.NormalSpace x hn
  let : RiemannianBundle ν := ⟨f.normalRiemannianMetric hn⟩
  let : ∀ x, NormedAddCommGroup (ν x) := fun x ↦ inferInstance
  let : ∀ x, InnerProductSpace ℝ (ν x) := fun x ↦ inferInstance
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have : IsManifold J (∞ + 1) N := by simpa using (inferInstance : IsManifold J ∞ N)
  let := f.normalSpaceVectorBundle hn hdim
  have : T2Space M := f.isEmbedding.t2Space
  have : SecondCountableTopology M := f.isEmbedding.isInducing.secondCountableTopology
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  let := f.isContMDiffRiemannianBundle_normalRiemannianMetric (m := ∞) hn (by simp) hdim
  let : IsContinuousRiemannianBundle P ν :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
  -- Normal-exponential coordinates on an open neighbourhood of the zero section.
  obtain ⟨Φ₀, hzero, -, hΦ₀O, -, hΦ₀⟩ :=
    f.exists_partialDiffeomorph_normalExp_subset (m := ∞) hn (by simp) (by simp) hdim hO hfO
  -- A closed disc bundle of positive smooth radius inside their source; restrict to its interior.
  obtain ⟨r, hr, -, hdisc⟩ := Φ₀.open_source.exists_contMDiffMap_norm_le_subset_bundle
    (I := I) (n := ⊤) hzero continuous_const fun _ ↦ zero_lt_one
  let D := {p : TotalSpace P ν | ‖p.snd‖ < r p.proj}
  have hD : IsOpen D := isOpen_lt (TauCeti.continuous_norm_bundle P ν)
    (r.contMDiff.continuous.comp (FiberBundle.continuous_proj P ν))
  have hDsource : D ⊆ Φ₀.source := fun p hp ↦ hdisc p.proj p.snd (le_of_lt hp)
  refine ⟨Φ₀.restrOpen D hD, r, by rw [PartialDiffeomorph.coe_restrOpen, hΦ₀], hr, ?_,
    fun y hy ↦ hΦ₀O ?_⟩
  · rw [PartialDiffeomorph.restrOpen_source, inter_eq_right.2 hDsource]
  · rw [PartialDiffeomorph.restrOpen_target] at hy
    exact hy.1

/-- Choose normal-exponential coordinates and small closed fibre discs simultaneously.
The disc and sphere images are closed in the ambient manifold, and the open discs embed openly.
Nonemptiness is needed only to define the partial inverse away from the coordinate target. -/
theorem exists_partialDiffeomorph_normalExp_norm_le_subset [Nonempty M]
    (f : SmoothEmbedding I J ∞ M N) (hclosed : IsClosed (range f))
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E)
    {O : Set N} (hO : IsOpen O) (hfO : range f ⊆ O)
    {ε : M → ℝ} (hε : Continuous ε) (hεpos : ∀ x, 0 < ε x) :
    let hn : (∞ : ℕ∞ω) ≠ 0 := by simp
    letI := f.normalSpaceFiberBundle hn hdim
    let ν : M → Type _ := fun x => f.isImmersion.NormalSpace x hn
    letI : RiemannianBundle ν := ⟨f.normalRiemannianMetric hn⟩
    ∃ (Φ : PartialDiffeomorph (I.prod 𝓘(ℝ, P)) J (TotalSpace P ν) N ∞)
        (r : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯),
      ⇑Φ = f.normalExp hn ∧ (∀ x, 0 < r x) ∧ (∀ x, r x < ε x) ∧
      {p : TotalSpace P ν | ‖p.snd‖ ≤ r p.proj} ⊆ Φ.source ∧
      Φ.source ⊆ f.normalExpDomain hn ∧ Φ.target ⊆ O ∧
      IsOpenEmbedding ({p : TotalSpace P ν | ‖p.snd‖ < r p.proj}.domRestrict Φ) ∧
      IsClosedEmbedding ({p : TotalSpace P ν | ‖p.snd‖ ≤ r p.proj}.domRestrict Φ) ∧
      IsClosedEmbedding ({p : TotalSpace P ν | ‖p.snd‖ = r p.proj}.domRestrict Φ) := by
  let hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have : IsManifold J (∞ + 1) N := by simpa using (inferInstance : IsManifold J ∞ N)
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  let ν : M → Type _ := fun x => f.isImmersion.NormalSpace x hn
  let : RiemannianBundle ν := ⟨f.normalRiemannianMetric hn⟩
  let : ∀ x, NormedAddCommGroup (ν x) := fun x => inferInstance
  let : ∀ x, InnerProductSpace ℝ (ν x) := fun x => inferInstance
  have : T2Space M := f.isEmbedding.t2Space
  have : SecondCountableTopology M := f.isEmbedding.isInducing.secondCountableTopology
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have : LocallyCompactSpace G := J.locallyCompactSpace
  have : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace G N
  have : MetrizableSpace N := Manifold.metrizableSpace J N
  let := f.isContMDiffRiemannianBundle_normalRiemannianMetric (m := ∞) hn (by simp) hdim
  let : IsContinuousRiemannianBundle P ν :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)
  obtain ⟨Φ, hzero, hsource, htarget, -, hΦ⟩ :=
    f.exists_partialDiffeomorph_normalExp_subset (m := ∞) hn (by simp) (by simp) hdim hO hfO
  have hcore : Φ ∘ zeroSection P ν = f := by
    funext x
    rw [hΦ]
    exact f.normalExp_zeroSection hn x
  obtain ⟨r, hr, hrε, hdisc, hopen, hd, hs⟩ :=
    Φ.toOpenPartialHomeomorph.exists_contMDiffMap_isClosedEmbedding_norm_le
      (I := I) hzero (by convert hclosed using 2; exact hcore) hε hεpos ⊤
  exact ⟨Φ, r, hΦ, hr, hrε, hdisc, hsource, htarget, hopen, hd, hs⟩

/-- **Closed normal disc theorem for a closed smooth submanifold.** The normal exponential
embeds closed discs and spheres of a positive smooth radius as closed subsets of any prescribed
open neighbourhood of the core. The open discs embed openly. The core may be noncompact,
and the ambient Riemannian metric need not be complete. -/
theorem exists_isClosedEmbedding_normalExp_norm_le_subset
    (f : SmoothEmbedding I J ∞ M N) (hclosed : IsClosed (range f))
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E)
    {O : Set N} (hO : IsOpen O) (hfO : range f ⊆ O)
    {ε : M → ℝ} (hε : Continuous ε) (hεpos : ∀ x, 0 < ε x) :
    let hn : (∞ : ℕ∞ω) ≠ 0 := by simp
    letI := f.normalSpaceFiberBundle hn hdim
    let ν : M → Type _ := fun x => f.isImmersion.NormalSpace x hn
    letI : RiemannianBundle ν := ⟨f.normalRiemannianMetric hn⟩
    letI : ∀ x, NormedAddCommGroup (ν x) := fun x => inferInstance
    ∃ r : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, (∀ x, 0 < r x) ∧ (∀ x, r x < ε x) ∧
      {p : TotalSpace P ν | ‖p.snd‖ ≤ r p.proj} ⊆
        f.normalExpDomain hn ∧
      f.normalExp hn '' {p : TotalSpace P ν |
        ‖p.snd‖ ≤ r p.proj} ⊆ O ∧
      IsOpenEmbedding ({p : TotalSpace P ν |
        ‖p.snd‖ < r p.proj}.domRestrict (f.normalExp hn)) ∧
      IsClosedEmbedding ({p : TotalSpace P ν |
        ‖p.snd‖ ≤ r p.proj}.domRestrict (f.normalExp hn)) ∧
      IsClosedEmbedding ({p : TotalSpace P ν |
        ‖p.snd‖ = r p.proj}.domRestrict (f.normalExp hn)) := by
  let hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have : IsManifold J (∞ + 1) N := by simpa using (inferInstance : IsManifold J ∞ N)
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  let ν : M → Type _ := fun x => f.isImmersion.NormalSpace x hn
  let : RiemannianBundle ν := ⟨f.normalRiemannianMetric hn⟩
  let : ∀ x, NormedAddCommGroup (ν x) := fun x => inferInstance
  let : ∀ x, InnerProductSpace ℝ (ν x) := fun x => inferInstance
  cases isEmpty_or_nonempty M with
  | inl hM =>
    have : IsEmpty (TotalSpace P ν) := ⟨fun p => hM.false p.proj⟩
    refine ⟨ContMDiffMap.const (I := I) (I' := 𝓘(ℝ)) (n := ∞) (1 : ℝ),
      fun x => (hM.false x).elim, fun x => (hM.false x).elim,
      fun p => (IsEmpty.false p).elim, ?_, .of_isEmpty _, ?_, ?_⟩
    · rintro _ ⟨p, -, -⟩
      exact (IsEmpty.false p).elim
    all_goals exact ⟨.of_subsingleton _, by
      simp only [range_domRestrict, Set.eq_empty_of_isEmpty, image_empty, isClosed_empty]⟩
  | inr hM =>
    let := hM
    obtain ⟨Φ, r, hΦ, hr, hrε, hdisc, hsource, htarget, hopen, hd, hs⟩ :=
      f.exists_partialDiffeomorph_normalExp_norm_le_subset hclosed hdim hO hfO hε hεpos
    simp only [hΦ] at hopen hd hs
    refine ⟨r, hr, hrε, hdisc.trans hsource, ?_, hopen, hd, hs⟩
    rintro _ ⟨p, hp, rfl⟩
    rw [← hΦ]
    exact htarget (Φ.map_source (hdisc hp))

end TauCeti.SmoothEmbedding
