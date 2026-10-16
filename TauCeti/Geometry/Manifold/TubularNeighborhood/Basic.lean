/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Basic

/-!
# Tubular-neighborhood data

This file records the topological part of a tubular-neighborhood chart.  Smooth
normal-bundle theorems provide such data for smooth embeddings; the structure
here keeps that existence theorem separate from the interface consumed by disc
and sphere bundle constructions.

The interface follows the tubular-neighborhood theorem of J. M. Lee,
*Introduction to Smooth Manifolds*, 2nd ed., Theorem 6.24, and the corresponding
existence theorem of M. Hirsch, *Differential Topology*, Theorem 6.3.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Theorem 6.24.
* M. Hirsch, *Differential Topology*, Theorem 6.3.
-/

public section

open Set
open Bundle
open Topology

namespace TauCeti

variable {B F N : Type*} {E : B → Type*}
variable [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)]
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)] [TopologicalSpace N]

/-- The data supplied by a tubular-neighborhood theorem.

`U` is an open, fiberwise star-shaped neighborhood of the zero section in a
family of fibers.  A vector-bundle or smooth normal-bundle construction can
instantiate this interface with its additional linear and differentiable
structure.  `toFun` identifies `U` with an open subset of the ambient space
`N`, and agrees with the given core embedding `f` on the zero section.  The
star-shaped condition is stated with real scalars in `[0, 1]`, which is the
form used by the radial deformation of a tubular neighborhood.
-/
structure IsTubularNeighborhood (f : B → N) (U : Set (TotalSpace F E))
    (toFun : U → N) : Prop where
  /-- The tubular domain is open in the total space. -/
  isOpen : IsOpen U
  /-- Every point of the core has its zero vector in the tubular domain. -/
  zero_mem : ∀ x, zeroSection F E x ∈ U
  /-- Each fiber slice of the domain is star-convex at the zero vector. -/
  fiberwise_starConvex : ∀ x, StarConvex ℝ 0
    {v : E x | (⟨x, v⟩ : TotalSpace F E) ∈ U}
  /-- The tubular chart is an open embedding. -/
  isOpenEmbedding : IsOpenEmbedding toFun
  /-- The core map is an embedding. -/
  isEmbedding_f : IsEmbedding f
  /-- The tubular chart restricts to the core map on the zero section. -/
  map_zeroSection : ∀ x, toFun ⟨zeroSection F E x, zero_mem x⟩ = f x
  /-- Radial contraction is continuous on the interval and tubular domain.

  This explicit field records the topological compatibility needed by the
  deformation arguments consuming tubular-neighborhood data. -/
  continuous_radial : Continuous (fun p : Icc (0 : ℝ) 1 × U =>
    (⟨p.2.1.1, (p.1 : ℝ) • p.2.1.2⟩ : TotalSpace F E))

namespace IsTubularNeighborhood

variable {f : B → N} {U : Set (TotalSpace F E)} {toFun : U → N}

/-- The canonical zero-section model on the whole total space.

The continuity hypothesis records the vector-bundle topology needed by the
radial contraction; `hzero` supplies the embedding of the zero section. -/
theorem isTubularNeighborhood_zeroSection
    (hzero : IsEmbedding (zeroSection F E))
    (hradial : Continuous (fun p : Icc (0 : ℝ) 1 × TotalSpace F E =>
      (⟨p.2.proj, (p.1 : ℝ) • p.2.2⟩ : TotalSpace F E))) :
    IsTubularNeighborhood (zeroSection F E) (Set.univ : Set (TotalSpace F E))
      (fun x : (Set.univ : Set (TotalSpace F E)) => x.1) where
  isOpen := isOpen_univ
  zero_mem := fun _ => mem_univ _
  fiberwise_starConvex := by
    intro x
    simpa using (starConvex_univ (𝕜 := ℝ) (0 : E x))
  isOpenEmbedding := isOpen_univ.isOpenEmbedding_subtypeVal
  isEmbedding_f := hzero
  map_zeroSection := by
    intro x
    rfl
  continuous_radial := by
    convert hradial.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)) using 1
    rfl

/-- The radial contraction of a tubular neighborhood, with its image kept in
the tubular domain by `fiberwise_starConvex`. -/
def radialContraction (T : IsTubularNeighborhood f U toFun) : Icc (0 : ℝ) 1 × U → U :=
  fun p => ⟨⟨p.2.1.1, (p.1 : ℝ) • p.2.1.2⟩,
    by
      simpa using (T.fiberwise_starConvex p.2.1.1).smul_mem p.2.property
        p.1.2.1 p.1.2.2⟩

/-- The radial contraction supplied by tubular-neighborhood data is continuous. -/
theorem continuous_radialContraction (T : IsTubularNeighborhood f U toFun) :
    Continuous T.radialContraction :=
  T.continuous_radial.subtype_mk _

/-- At time one, radial contraction is the identity. -/
@[simp] theorem radialContraction_one (T : IsTubularNeighborhood f U toFun) (u : U) :
    T.radialContraction ⟨1, u⟩ = u := by
  rcases u with ⟨⟨x, v⟩, hu⟩
  apply Subtype.ext
  simp [radialContraction]

/-- At time zero, radial contraction lands on the zero section. -/
@[simp] theorem radialContraction_zero (T : IsTubularNeighborhood f U toFun) (u : U) :
    T.radialContraction ⟨0, u⟩ = ⟨zeroSection F E u.1.1, T.zero_mem u.1.1⟩ := by
  rcases u with ⟨⟨x, v⟩, hu⟩
  apply Subtype.ext
  simp [radialContraction, zeroSection]

/-- The underlying total-space point of the radial contraction. -/
@[simp] theorem coe_radialContraction (T : IsTubularNeighborhood f U toFun)
    (p : Icc (0 : ℝ) 1 × U) :
    (T.radialContraction p : TotalSpace F E) =
      ⟨p.2.1.1, (p.1 : ℝ) • p.2.1.2⟩ :=
  by
    simp [radialContraction]

end IsTubularNeighborhood

end TauCeti
