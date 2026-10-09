/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.SmoothRadius

/-!
# Shrinking tubular neighbourhoods inside the normal bundle

A Euclidean tubular neighbourhood can be chosen so that its closed normal discs lie in
any prescribed open neighbourhood of the zero section in the normal bundle. At the same
time, the ambient closed balls fit inside a prescribed neighbourhood of the embedded image.
The radius is positive and smooth, and normal addition remains an open embedding.

This is the shrinking step for assembling smooth tubular inverses: choose a zero-section
neighbourhood on which normal addition is a local diffeomorphism, then shrink the globally
injective tube into it. The normal bundle retains its topology induced from `M × V`.

Reuse `IsOpen.exists_contMDiffMap_closedBall_subset` for smooth radius selection and
`isEmbedding_totalSpace_normalSubspace` to pass between the normal bundle and the product.

Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
-/

public section

open Set Function Topology Bundle
open scoped Manifold ContDiff

namespace TauCeti

variable {V E F H M : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]

/-- A `C²` Euclidean embedding of a smooth manifold admits a positive smooth tubular radius
whose closed normal discs lie in any prescribed open neighbourhood of the zero section.
Even the ambient closed balls map into the prescribed neighbourhood of the embedded image. -/
theorem exists_isOpenEmbedding_normalTubeOfRadius_contMDiff_subset_zeroSection {f : M → V}
    (hf : ContMDiff I 𝓘(ℝ, V) 2 f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x)) (hind : IsInducing f)
    {U : Set (TotalSpace F (fun x => normalSubspace I f x))} (hU : IsOpen U)
    (hzero : ∀ x, zeroSection F (fun x => normalSubspace I f x) x ∈ U)
    {O : Set V} (hO : IsOpen O) (hfO : range f ⊆ O) :
    ∃ r : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, (∀ x, 0 < r x) ∧
      IsOpenEmbedding ((normalTubeOfRadius I f r).domRestrict
        fun p : M × V => f p.1 + p.2) ∧
      (∀ x v, ‖v‖ ≤ r x → f x + v ∈ O) ∧
      ∀ p : TotalSpace F (fun x => normalSubspace I f x),
        ‖(p.2 : V)‖ ≤ r p.proj → p ∈ U := by
  have : T1Space M := I.t1Space M
  have : T2Space M := hind.isEmbedding.t2Space
  obtain ⟨R, hR, hemb, hambient⟩ :=
    exists_isOpenEmbedding_normalTubeOfRadius_contMDiff_subset hf himm hind hO hfO
  obtain ⟨W, hW, hWU⟩ :=
    (isEmbedding_totalSpace_normalSubspace (F := F) f).isInducing.isOpen_iff.mp hU
  have hWzero : ∀ x, (x, (0 : V)) ∈ W := by
    intro x
    have hx := hzero x
    rw [← hWU] at hx
    exact hx
  obtain ⟨r, hr, hrR, hdisc⟩ := hW.exists_contMDiffMap_closedBall_subset (I := I)
    hWzero R.contMDiff.continuous hR
  refine ⟨r, hr, isOpenEmbedding_normalTubeOfRadius_of_le r.contMDiff.continuous
    (fun x => (hrR x).le) hemb, ?_, ?_⟩
  · intro x v hv
    exact hambient x v (hv.trans (hrR x).le)
  · intro p hp
    rw [← hWU]
    exact hdisc p.proj (p.2 : V) (by simpa using hp)

end TauCeti
