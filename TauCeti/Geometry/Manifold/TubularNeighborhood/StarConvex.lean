/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.Basic
public import TauCeti.Topology.VectorBundle.Radial

/-!
# Shrinking tubular coordinates to a star-convex domain

An open embedding from an open neighbourhood of the zero section of a real vector bundle
can be restricted to its radial core. The resulting domain is open, contains the zero
section, and is fibrewise star-convex, so the restriction supplies `IsTubularNeighborhood`
data and its continuous radial contraction. The core embedding follows from the open
embedding of the coordinates and the vector-bundle zero section.

This is an assembly step for tubular neighbourhoods: after constructing injective coordinates
on some open zero-section neighbourhood, it makes radial deformation available without
requiring that the injectivity neighbourhood was already star-convex. It applies equally to
Euclidean normal addition and to normal-exponential coordinates in an ambient manifold.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
* M. W. Hirsch, *Differential Topology*, Chapter 4, Theorem 6.3.
-/

public section

open Bundle Set Topology

namespace TauCeti

variable {B F N : Type*} {E : B → Type*}
  [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle ℝ F E] [TopologicalSpace N]

/-- Restrict injective open tubular coordinates to the radial core of their domain.
No star-convexity assumption on the original domain is needed, and the core map is
automatically an embedding. -/
theorem isTubularNeighborhood_radialCore {f : B → N} {U : Set (TotalSpace F E)}
    (hU : IsOpen U) (hzero : ∀ x, zeroSection F E x ∈ U)
    {φ : U → N} (hφ : IsOpenEmbedding φ)
    (hφzero : ∀ x, φ ⟨zeroSection F E x, hzero x⟩ = f x) :
    IsTubularNeighborhood f (VectorBundle.radialCore U)
      (φ ∘ Set.inclusion (VectorBundle.radialCore_subset U)) where
  isOpen := VectorBundle.isOpen_radialCore hU
  zero_mem := fun x => (VectorBundle.zeroSection_mem_radialCore x).mpr (hzero x)
  fiberwise_starConvex := VectorBundle.starConvex_radialCore U
  isOpenEmbedding := hφ.comp (.inclusion (VectorBundle.radialCore_subset U)
    ((VectorBundle.isOpen_radialCore hU).preimage continuous_subtype_val))
  isEmbedding_f := by
    have hleft : Function.LeftInverse (π F E) (zeroSection F E) := fun _ => rfl
    have hz : IsEmbedding (zeroSection F E) :=
      hleft.isEmbedding (FiberBundle.continuous_proj F E)
        (Bundle.Trivialization.continuous_zeroSection ℝ)
    simpa only [Function.comp_def, Set.codRestrict, hφzero] using
      hφ.isEmbedding.comp (hz.codRestrict U hzero)
  map_zeroSection := fun x => hφzero x
  continuous_radial :=
    (continuous_subtype_val.comp continuous_fst).smul_totalSpace
      (continuous_subtype_val.comp continuous_snd)

end TauCeti
