/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.VectorBundle.Basic

/-!
# Tubular-neighborhood data

This file records the topological part of a tubular-neighborhood chart.  A
future smooth normal-bundle theorem can provide such data for a smooth
embedding; the structure here keeps that existence theorem separate from the
interface consumed by disc and sphere bundle constructions.
-/

public section

open Set
open Bundle
open Topology

namespace TauCeti

variable {B F N : Type*} {E : B → Type*}
variable [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)]
  [∀ x, Zero (E x)] [∀ x, SMul ℝ (E x)] [TopologicalSpace N]

/-- The data supplied by a tubular-neighborhood theorem.

`U` is an open, fiberwise star-shaped neighborhood of the zero section in a
family of fibers.  A vector-bundle or smooth normal-bundle construction can
instantiate this interface with its additional linear and differentiable
structure.  `toFun` identifies `U` with an open subset of the ambient space
`N`, and agrees with the given core embedding `f` on the zero section.  The
star-shaped condition is stated with real scalars in `[0, 1]`, which is the
form used by the radial deformation of a tubular neighborhood.
-/
structure TubularNeighborhoodData (f : B → N) (U : Set (TotalSpace F E))
    (toFun : U → N) : Prop where
  /-- The tubular domain is open in the total space. -/
  isOpen : IsOpen U
  /-- Every point of the core has its zero vector in the tubular domain. -/
  zero_mem : ∀ x, zeroSection F E x ∈ U
  /-- The domain is closed under radial contraction in each fiber. -/
  fiberwise_smul_mem : ∀ {x} {v : E x}, (⟨x, v⟩ : TotalSpace F E) ∈ U →
    ∀ {t : ℝ}, t ∈ Icc (0 : ℝ) 1 → (⟨x, t • v⟩ : TotalSpace F E) ∈ U
  /-- The tubular chart is an open embedding. -/
  isOpenEmbedding : IsOpenEmbedding toFun
  /-- The core map is an embedding. -/
  isEmbedding_f : IsEmbedding f
  /-- The tubular chart restricts to the core map on the zero section. -/
  map_zero : ∀ x, toFun ⟨zeroSection F E x, zero_mem x⟩ = f x

namespace TubularNeighborhoodData

variable {f : B → N} {U : Set (TotalSpace F E)} {toFun : U → N}

/-- The zero section gives a canonical tubular data object for its own total
space.  This is a useful nonempty model for consumers of the interface and
fixes all conventions about the subtype domain. -/
theorem zeroSectionData (hzero : IsEmbedding (zeroSection F E)) :
    TubularNeighborhoodData (zeroSection F E) (Set.univ : Set (TotalSpace F E))
      (fun x : (Set.univ : Set (TotalSpace F E)) => x.1) where
  isOpen := isOpen_univ
  zero_mem := fun _ => mem_univ _
  fiberwise_smul_mem := by
    intro x v _ t ht
    exact mem_univ _
  isOpenEmbedding := isOpen_univ.isOpenEmbedding_subtypeVal
  isEmbedding_f := hzero
  map_zero := by
    intro x
    rfl

end TubularNeighborhoodData

end TauCeti
