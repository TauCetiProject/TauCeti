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
  /-- Radial contraction is continuous on the interval and tubular domain.

  This explicit field records the topological compatibility needed by the
  deformation arguments consuming tubular-neighborhood data. -/
  continuous_radial : Continuous (fun p : Icc (0 : ℝ) 1 × U =>
    (⟨p.2.1.1, (p.1 : ℝ) • p.2.1.2⟩ : TotalSpace F E))

namespace TubularNeighborhoodData

variable {f : B → N} {U : Set (TotalSpace F E)} {toFun : U → N}

/-- The radial contraction of a tubular neighborhood, with its image kept in
the tubular domain by `fiberwise_smul_mem`. -/
def radialContraction (T : TubularNeighborhoodData f U toFun) : Icc (0 : ℝ) 1 × U → U :=
  fun p => ⟨⟨p.2.1.1, (p.1 : ℝ) • p.2.1.2⟩,
    T.fiberwise_smul_mem p.2.property p.1.property⟩

/-- The radial contraction supplied by tubular-neighborhood data is continuous. -/
theorem continuous_radialContraction (T : TubularNeighborhoodData f U toFun) :
    Continuous T.radialContraction :=
  T.continuous_radial.subtype_mk _

/-- At time one, radial contraction is the identity. -/
@[simp] theorem radialContraction_one (T : TubularNeighborhoodData f U toFun) (u : U) :
    T.radialContraction ⟨1, u⟩ = u := by
  apply Subtype.ext
  change (⟨u.1.1, (1 : ℝ) • u.1.2⟩ : TotalSpace F E) = u.1
  rw [one_smul]

/-- At time zero, radial contraction lands on the zero section. -/
@[simp] theorem radialContraction_zero (T : TubularNeighborhoodData f U toFun) (u : U) :
    T.radialContraction ⟨0, u⟩ = ⟨zeroSection F E u.1.1, T.zero_mem u.1.1⟩ := by
  apply Subtype.ext
  change (⟨u.1.1, (0 : ℝ) • u.1.2⟩ : TotalSpace F E) = zeroSection F E u.1.1
  rw [zero_smul]
  rfl

end TubularNeighborhoodData

end TauCeti
