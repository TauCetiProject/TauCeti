/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Neighborhood
public import TauCeti.Topology.OpenPartialHomeomorph.Basic
public import TauCeti.Topology.VectorBundle.Riemannian.Basic

/-!
# Closed disc neighbourhoods in bundle coordinates

Suppose bundle coordinates identify a neighbourhood of the zero section with an open subset
of a normal space, and the image of the zero section is closed. There is a positive smooth
radius for which the closed fibre discs and spheres embed as closed subsets of the ambient
space. The base need not be compact and the fibres need not have finite rank.

The target is first shrunk around the closed core so that its closure stays in the coordinate
neighbourhood. Smooth radius selection inside that smaller neighbourhood prevents the disc
image from accumulating outside the coordinate target. This supplies the closed neighbourhood
form of tubular coordinates without a proper ambient metric.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
* M. W. Hirsch, *Differential Topology*, Chapter 4, Theorem 6.3.

The radius selection is `IsOpen.exists_contMDiffMap_norm_le_subset_bundle`.
-/

public section

open Bundle Set Topology
open scoped Manifold ContDiff

namespace OpenPartialHomeomorph

variable {B F E H X : Type*} [TopologicalSpace B]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [ChartedSpace H B] [IsManifold I ∞ B] [T2Space B] [SigmaCompactSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [IsContinuousRiemannianBundle F V] [TopologicalSpace X] [NormalSpace X]

/-- Bundle coordinates around a closed core admit positive smooth radii giving closed disc
and sphere embeddings into the ambient space, with an open embedding on the open discs.
The radius can be bounded by any prescribed positive continuous function. -/
theorem exists_contMDiffMap_isClosedEmbedding_norm_le
    (e : OpenPartialHomeomorph (TotalSpace F V) X)
    (hzero : ∀ b, zeroSection F V b ∈ e.source)
    (hcore : IsClosed (range (e ∘ zeroSection F V)))
    {ε : B → ℝ} (hε : Continuous ε) (hεpos : ∀ b, 0 < ε b) (n : ℕ∞) :
    ∃ r : C^n⟮I, B; 𝓘(ℝ), ℝ⟯, (∀ b, 0 < r b) ∧ (∀ b, r b < ε b) ∧
      {p : TotalSpace F V | ‖p.2‖ ≤ r p.proj} ⊆ e.source ∧
      IsOpenEmbedding ({p : TotalSpace F V | ‖p.2‖ < r p.proj}.domRestrict e) ∧
      IsClosedEmbedding ({p : TotalSpace F V | ‖p.2‖ ≤ r p.proj}.domRestrict e) ∧
      IsClosedEmbedding ({p : TotalSpace F V | ‖p.2‖ = r p.proj}.domRestrict e) := by
  have hcoretarget : range (e ∘ zeroSection F V) ⊆ e.target := by
    rintro _ ⟨b, rfl⟩
    exact e.map_source (hzero b)
  obtain ⟨W, hW, hcoreW, hclosureW⟩ :=
    normal_exists_closure_subset hcore e.open_target hcoretarget
  obtain ⟨r, hr, hrε, hdisc⟩ :=
    (e.isOpen_inter_preimage hW).exists_contMDiffMap_norm_le_subset_bundle
      (I := I) (n := n) (fun b => ⟨hzero b, hcoreW (mem_range_self b)⟩) hε hεpos
  let D := {p : TotalSpace F V | ‖p.2‖ ≤ r p.proj}
  let S := {p : TotalSpace F V | ‖p.2‖ = r p.proj}
  let T := {p : TotalSpace F V | ‖p.2‖ < r p.proj}
  have hnorm := TauCeti.continuous_norm_bundle F V
  have hrad : Continuous (fun p : TotalSpace F V => r p.proj) :=
    r.contMDiff.continuous.comp (FiberBundle.continuous_proj _ _)
  have hD : IsClosed D := isClosed_le hnorm hrad
  have hS : IsClosed S := isClosed_eq hnorm hrad
  have hT : IsOpen T := isOpen_lt hnorm hrad
  have hDsource : D ⊆ e.source := fun p hp => (hdisc p.proj p.2 hp).1
  have hTD : T ⊆ D := fun p (hp : ‖p.2‖ < r p.proj) => hp.le
  have hSD : S ⊆ D := fun p (hp : ‖p.2‖ = r p.proj) => hp.le
  have hDW : e '' D ⊆ W := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hdisc p.proj p.2 hp).2
  have hclosed : IsClosed (e '' D) := e.isClosed_image_of_closure_subset_target hD hDsource
    ((closure_mono hDW).trans hclosureW)
  have hd : IsClosedEmbedding (D.domRestrict e) :=
    ⟨e.isEmbedding_restrict.comp (IsEmbedding.inclusion hDsource), by
      simpa only [range_domRestrict] using hclosed⟩
  exact ⟨r, hr, hrε, hDsource,
    e.isOpenEmbedding_restrict.comp (IsOpenEmbedding.inclusion (hTD.trans hDsource)
      (hT.preimage continuous_subtype_val)), hd,
    hd.comp (IsClosedEmbedding.inclusion hSD (hS.preimage continuous_subtype_val))⟩

end OpenPartialHomeomorph
