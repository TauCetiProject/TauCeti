/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.DefiningFunction
public import TauCeti.Geometry.Manifold.TubularNeighborhood.Riemannian.Noncompact

/-!
# Global defining functions for tubular neighbourhoods

A closed boundaryless smooth submanifold of a boundaryless manifold has arbitrarily small
closed normal disc neighbourhoods with a global smooth regular defining function. Their negative
set is the open disc image, their zero set is the sphere image, and their nonpositive set is the
closed disc image. Zero is a regular
value. Thus the exterior is the nonnegative locus of a global regular defining function,
including away from the tubular coordinate neighbourhood.

The chosen radius can vary over a noncompact core and is bounded by any given positive continuous
function. Its closed disc image stays inside any prescribed open neighbourhood of the core.
The open disc, closed disc, and sphere embeddings for this same radius are retained, together
with the germ of the sphere equation in normal-exponential coordinates near the closed discs.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Proposition 5.47
  (regular domains) and Theorem 6.24 (tubular neighbourhoods).
* M. W. Hirsch, *Differential Topology*, Chapter 4, Theorem 6.3.

The construction uses `sphereBundleEquation`,
`PartialDiffeomorph.exists_contMDiffMap_regular_definingFunction_norm_le`, and the disc selection
in `SmoothEmbedding.exists_partialDiffeomorph_normalExp_norm_le_subset`.
-/

public noncomputable section

open Bundle Set Function Manifold Topology TopologicalSpace
open scoped Manifold ContDiff

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

/-- A closed boundaryless smooth submanifold of a boundaryless manifold has arbitrarily small
normal disc neighbourhoods with a global smooth regular defining function. Its negative locus
is the open normal tube, its zero locus is the normal sphere image, and its nonpositive locus
is the closed normal disc image.
The sphere embeds as a closed subset, and the function pulls back to the sphere equation near
every closed disc point. Neither compactness nor completeness of the ambient metric is required. -/
theorem exists_regular_definingFunction_normalExp
    (f : SmoothEmbedding I J ∞ M N) (hclosed : IsClosed (range f))
    (hdim : Module.finrank ℝ P = Module.finrank ℝ V - Module.finrank ℝ E)
    {O : Set N} (hO : IsOpen O) (hfO : range f ⊆ O)
    {ε : M → ℝ} (hε : Continuous ε) (hεpos : ∀ x, 0 < ε x) :
    let hn : (∞ : ℕ∞ω) ≠ 0 := by simp
    letI := f.normalSpaceFiberBundle hn hdim
    let ν : M → Type _ := fun x => f.NormalSpace x hn
    letI : RiemannianBundle ν := ⟨f.normalRiemannianMetric hn⟩
    letI : ∀ x, NormedAddCommGroup (ν x) := fun x => inferInstance
    ∃ (r : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯) (g : C^∞⟮J, N; 𝓘(ℝ), ℝ⟯),
      (∀ x, 0 < r x) ∧ (∀ x, r x < ε x) ∧ IsRegularValue J 𝓘(ℝ) g 0 ∧
      {p : TotalSpace P ν | ‖p.2‖ ≤ r p.proj} ⊆ f.normalExpDomain hn ∧
      f.normalExp hn '' {p : TotalSpace P ν | ‖p.2‖ ≤ r p.proj} ⊆ O ∧
      IsOpenEmbedding ({p : TotalSpace P ν | ‖p.2‖ < r p.proj}.domRestrict
        (f.normalExp hn)) ∧
      IsClosedEmbedding ({p : TotalSpace P ν | ‖p.2‖ ≤ r p.proj}.domRestrict
        (f.normalExp hn)) ∧
      IsClosedEmbedding ({p : TotalSpace P ν | ‖p.2‖ = r p.proj}.domRestrict
        (f.normalExp hn)) ∧
      (∀ p : TotalSpace P ν, ‖p.2‖ ≤ r p.proj →
        (g ∘ f.normalExp hn) =ᶠ[𝓝 p] TauCeti.sphereBundleEquation r) ∧
      {y | g y ≤ 0} = f.normalExp hn '' {p : TotalSpace P ν | ‖p.2‖ ≤ r p.proj} ∧
      {y | g y < 0} = f.normalExp hn '' {p : TotalSpace P ν | ‖p.2‖ < r p.proj} ∧
      {y | g y = 0} = f.normalExp hn '' {p : TotalSpace P ν | ‖p.2‖ = r p.proj} := by
  let hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have : IsManifold J (∞ + 1) N := by simpa using (inferInstance : IsManifold J ∞ N)
  let := f.normalSpaceFiberBundle hn hdim
  let := f.normalSpaceVectorBundle hn hdim
  let := f.normalSpaceContMDiffVectorBundle (m := ∞) hn (by simp) hdim
  let ν : M → Type _ := fun x => f.NormalSpace x hn
  let : RiemannianBundle ν := ⟨f.normalRiemannianMetric hn⟩
  let : ∀ x, NormedAddCommGroup (ν x) := fun x => inferInstance
  let : ∀ x, InnerProductSpace ℝ (ν x) := fun x => inferInstance
  cases isEmpty_or_nonempty M with
  | inl hM =>
    have : IsEmpty (TotalSpace P ν) := ⟨fun p => hM.false p.proj⟩
    refine ⟨ContMDiffMap.const (I := I) 1, ContMDiffMap.const (I := J) 1,
      fun x => (hM.false x).elim, fun x => (hM.false x).elim, ?_,
      fun p => (IsEmpty.false p).elim, ?_⟩
    · apply isRegularValue_of_notMem_range
      simp [ContMDiffMap.const]
    · refine ⟨by simp, .of_isEmpty _, ⟨.of_subsingleton _, ?_⟩, ⟨.of_subsingleton _, ?_⟩,
        (fun p => (IsEmpty.false p).elim), ?_⟩
      · simp only [range_domRestrict, Set.eq_empty_of_isEmpty, image_empty, isClosed_empty]
      · simp only [range_domRestrict, Set.eq_empty_of_isEmpty, image_empty, isClosed_empty]
      · norm_num [ContMDiffMap.const, Set.eq_empty_of_isEmpty]
  | inr hM =>
    let := hM
    have : LocallyCompactSpace G := J.locallyCompactSpace
    have : LocallyCompactSpace N := ChartedSpace.locallyCompactSpace G N
    have : MetrizableSpace N := Manifold.metrizableSpace J N
    let := f.isContMDiffRiemannianBundle_normalRiemannianMetric (m := ∞) hn (by simp) hdim
    obtain ⟨Φ, r, hΦ, hr, hrε, hdisc, hdomain, htarget, hopen, hd, hs⟩ :=
      f.exists_partialDiffeomorph_normalExp_norm_le_subset hclosed hdim hO hfO hε hεpos
    have hclosedDisc : IsClosed (Φ '' {p : TotalSpace P ν | ‖p.2‖ ≤ r p.proj}) := by
      simpa only [range_domRestrict, PartialDiffeomorph.toFun'_toOpenPartialHomeomorph]
        using hd.isClosed_range
    -- Globalize the regular sphere equation without changing any of its sign loci.
    obtain ⟨g, hg, hgerm, hle, hlt, heq⟩ :=
      Φ.exists_contMDiffMap_regular_definingFunction_norm_le r.contMDiff hr hdisc hclosedDisc
    simp only [hΦ] at hle hlt heq
    simp only [hΦ] at hopen hd hs
    refine ⟨r, g, hr, hrε, hg, hdisc.trans hdomain, ?_, hopen, hd, hs, ?_, hle, hlt, heq⟩
    · rintro _ ⟨p, hp, rfl⟩
      rw [← hΦ]
      exact htarget (Φ.toPartialEquiv.map_source (hdisc hp))
    · intro p hp
      rw [← hΦ]
      filter_upwards [(hgerm p hp).comp_tendsto
        (Φ.toOpenPartialHomeomorph.continuousAt (hdisc hp)),
        Φ.open_source.mem_nhds (hdisc hp)] with q hq hsource
      simpa only [comp_apply, PartialDiffeomorph.toFun'_toOpenPartialHomeomorph,
        PartialDiffeomorph.symm_toPartialEquiv, Φ.toPartialEquiv.left_inv hsource] using hq

end TauCeti.SmoothEmbedding
