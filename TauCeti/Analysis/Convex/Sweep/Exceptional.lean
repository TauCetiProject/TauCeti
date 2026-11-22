/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convex.Sweep.Basic
public import TauCeti.LinearAlgebra.AffineSpace.Generic

/-!
# Affine exceptions from sweeps

The affine span of a negative-ray sweep consists of full lines parallel to the sweeping
vector through the original affine span. Sweeping a set of codimension at least two
therefore yields a proper affine span, including for tangent and zero directions.

An exceptional arrangement of such spans can encode different permitted directions
for different bases. A generic point has its full line in each specified direction
disjoint from the corresponding original affine span.

Adapted from `Mei/Geometry/Convex/Sweep/Exceptional.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`bf3986029ff4d3eb4025d4067489511b0724374e` (Apache 2.0).
-/

public section

namespace TauCeti.ExceptionalArrangement

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V]

/-- The arrangement of swept affine spans of finitely many base-direction pairs.
Empty bases and zero directions are allowed. -/
noncomputable def ofSweeps (pairs : Finset (Set V × V))
    (hdim : ∀ z ∈ pairs, z.1.Nonempty →
      Module.finrank 𝕜 (vectorSpan 𝕜 z.1) + 1 < Module.finrank 𝕜 V) :
    ExceptionalArrangement 𝕜 V := by
  classical
  refine ⟨pairs.image (fun z => affineSpan 𝕜 (Set.sweep 𝕜 z.1 z.2)), ?_⟩
  intro A hA
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hA
  obtain hbase | hbase := z.1.eq_empty_or_nonempty
  · simp [hbase]
  · have h := hdim z hz hbase
    have hpos : 0 < Module.finrank 𝕜 V := by omega
    have := FiniteDimensional.of_finrank_pos hpos
    exact Set.affineSpan_sweep_ne_top z.1 z.2 (hdim z hz)

open Classical in
/-- The exceptions are exactly the swept affine spans of the specified pairs. -/
@[simp]
theorem exceptions_ofSweeps (pairs : Finset (Set V × V))
    (hdim : ∀ z ∈ pairs, z.1.Nonempty →
      Module.finrank 𝕜 (vectorSpan 𝕜 z.1) + 1 < Module.finrank 𝕜 V) :
    (ofSweeps pairs hdim).exceptions =
      pairs.image (fun z => affineSpan 𝕜 (Set.sweep 𝕜 z.1 z.2)) := (rfl)

/-- Genericity for sweep exceptions is equivalent to avoidance of each base's
affine span by the full line in its specified direction. -/
@[simp]
theorem isGeneric_ofSweeps_iff {pairs : Finset (Set V × V)}
    {hdim : ∀ z ∈ pairs, z.1.Nonempty →
      Module.finrank 𝕜 (vectorSpan 𝕜 z.1) + 1 < Module.finrank 𝕜 V} {y : V} :
    (ofSweeps pairs hdim).IsGeneric y ↔
      ∀ z ∈ pairs, ∀ t : 𝕜, y + t • z.2 ∉ affineSpan 𝕜 z.1 := by
  classical
  simp only [isGeneric_iff, exceptions_ofSweeps, Finset.forall_mem_image,
    Set.mem_affineSpan_sweep_iff, not_exists]

end TauCeti.ExceptionalArrangement
