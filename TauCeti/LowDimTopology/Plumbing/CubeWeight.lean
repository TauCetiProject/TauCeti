/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LowDimTopology.Plumbing.Weight

/-!
# Cube weights in a plumbing lattice

This file packages the finite cube weights used in Némethi's lattice homology. A cube is
specified by a base lattice point `x : V → ℤ` and a finite set `S : Finset V` of basis
directions. Its vertices are the points

`x + ∑ v ∈ T, E_v`

for subsets `T ⊆ S`. For a characteristic covector `k`, the cube weight is the maximum of the
already-defined point weights `χ_k` over these vertices.

## Main definitions

* `TauCeti.PlumbingGraph.cubeVertex`: the vertex indexed by a subset of directions.
* `TauCeti.PlumbingGraph.cubeVertices`: the finite set of all vertices of a cube.
* `TauCeti.PlumbingGraph.characteristicCubeWeight`: the maximum `χ_k` over those vertices.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L
("lattice homology"), whose opening item asks for Némethi's lattice (co)homology from lattice
points and weight functions. The cube weight is the standard maximum over vertices used in the
lattice-homology cubical complex; see Némethi, [arXiv:0709.0841](https://arxiv.org/abs/0709.0841).
-/

public section

namespace TauCeti

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V]

/-- The lattice point obtained from a base point `x` by adding the plumbing basis vectors in
`T`. This is the vertex of a lattice cube indexed by the subset `T` of its directions. -/
@[expose]
noncomputable def cubeVertex (x : V → ℤ) (T : Finset V) : V → ℤ :=
  x + ∑ v ∈ T, Pi.single v (1 : ℤ)

/-- The cube vertex, expanded as the defining finite sum of basis vectors. -/
theorem cubeVertex_def (x : V → ℤ) (T : Finset V) :
    cubeVertex x T = x + ∑ v ∈ T, Pi.single v (1 : ℤ) :=
  rfl

/-- The vertex indexed by the empty subset is the base point. -/
@[simp]
theorem cubeVertex_empty (x : V → ℤ) : cubeVertex x ∅ = x := by
  simp [cubeVertex]

/-- Adding a direction not already present adds the corresponding basis vector to the cube
vertex. -/
theorem cubeVertex_insert {T : Finset V} {v : V} (hv : v ∉ T) (x : V → ℤ) :
    cubeVertex x (insert v T) = cubeVertex x T + Pi.single v (1 : ℤ) := by
  ext w
  simp [cubeVertex, hv, add_assoc, add_comm]

/-- The coordinate value of a cube vertex. It is `x v + 1` in directions selected by `T`, and
`x v` otherwise. -/
@[simp]
theorem cubeVertex_apply (x : V → ℤ) (T : Finset V) (v : V) :
    cubeVertex x T v = x v + if v ∈ T then 1 else 0 := by
  classical
  simp [cubeVertex, Finset.sum_apply, Pi.single_apply]

variable [Fintype V]

/-- The finite set of all vertices of the cube with base point `x` and directions `S`. -/
@[expose]
noncomputable def cubeVertices (x : V → ℤ) (S : Finset V) : Finset (V → ℤ) :=
  S.powerset.image fun T => cubeVertex x T

/-- Membership in the vertex set of a plumbing cube. -/
theorem mem_cubeVertices (x : V → ℤ) (S : Finset V) (y : V → ℤ) :
    y ∈ cubeVertices x S ↔ ∃ T : Finset V, T ⊆ S ∧ cubeVertex x T = y := by
  simp [cubeVertices]

/-- The base point is a vertex of every cube. -/
@[simp]
theorem cubeVertex_mem_cubeVertices (x : V → ℤ) (S : Finset V) :
    x ∈ cubeVertices x S := by
  rw [mem_cubeVertices]
  exact ⟨∅, by simp, by simp⟩

/-- The vertex set of a cube is nonempty. -/
theorem cubeVertices_nonempty (x : V → ℤ) (S : Finset V) :
    (cubeVertices x S).Nonempty :=
  ⟨x, cubeVertex_mem_cubeVertices x S⟩

/-- A direction subset determines a vertex of any cube containing those directions. -/
theorem cubeVertex_subset_mem_cubeVertices {T S : Finset V} (hTS : T ⊆ S) (x : V → ℤ) :
    cubeVertex x T ∈ cubeVertices x S := by
  rw [mem_cubeVertices]
  exact ⟨T, hTS, rfl⟩

/-- The vertices of a subcube are vertices of the larger cube. -/
theorem cubeVertices_subset {S T : Finset V} (hST : S ⊆ T) (x : V → ℤ) :
    cubeVertices x S ⊆ cubeVertices x T := by
  intro y hy
  rw [mem_cubeVertices] at hy ⊢
  obtain ⟨U, hUS, rfl⟩ := hy
  exact ⟨U, hUS.trans hST, rfl⟩

/-- The characteristic weight values attained on the vertices of a plumbing cube. -/
noncomputable def characteristicCubeWeightValues
    (P : PlumbingGraph V)
    (k : P.characteristicVectors) (x : V → ℤ) (S : Finset V) : Finset ℤ :=
  (cubeVertices x S).image fun y => P.characteristicWeight k y

/-- The value set for a plumbing cube is nonempty. -/
theorem characteristicCubeWeightValues_nonempty
    (P : PlumbingGraph V)
    (k : P.characteristicVectors) (x : V → ℤ) (S : Finset V) :
    (P.characteristicCubeWeightValues k x S).Nonempty :=
  Finset.image_nonempty.mpr (cubeVertices_nonempty x S)

/-- The characteristic cube weight is the maximum of the point weights over the cube's vertices. -/
noncomputable def characteristicCubeWeight
    (P : PlumbingGraph V)
    (k : P.characteristicVectors) (x : V → ℤ) (S : Finset V) : ℤ :=
  (P.characteristicCubeWeightValues k x S).max'
    (P.characteristicCubeWeightValues_nonempty k x S)

/-- A vertex weight is one of the values used to form the characteristic cube weight. -/
theorem characteristicWeight_mem_characteristicCubeWeightValues
    (P : PlumbingGraph V)
    (k : P.characteristicVectors) {x : V → ℤ} {S : Finset V} {y : V → ℤ}
    (hy : y ∈ cubeVertices x S) :
    P.characteristicWeight k y ∈ P.characteristicCubeWeightValues k x S := by
  exact Finset.mem_image.mpr ⟨y, hy, rfl⟩

/-- The point weight at any vertex is bounded above by the characteristic cube weight. -/
theorem characteristicWeight_le_characteristicCubeWeight
    (P : PlumbingGraph V)
    (k : P.characteristicVectors) {x : V → ℤ} {S : Finset V} {y : V → ℤ}
    (hy : y ∈ cubeVertices x S) :
    P.characteristicWeight k y ≤ P.characteristicCubeWeight k x S := by
  exact Finset.le_max'
    (P.characteristicCubeWeightValues k x S)
    (P.characteristicWeight k y)
    (P.characteristicWeight_mem_characteristicCubeWeightValues k hy)

/-- The point weight at a direction subset is bounded above by the characteristic cube weight. -/
theorem characteristicWeight_cubeVertex_le_characteristicCubeWeight
    (P : PlumbingGraph V)
    (k : P.characteristicVectors) {T S : Finset V} (hTS : T ⊆ S) (x : V → ℤ) :
    P.characteristicWeight k (cubeVertex x T) ≤ P.characteristicCubeWeight k x S :=
  P.characteristicWeight_le_characteristicCubeWeight k
    (cubeVertex_subset_mem_cubeVertices hTS x)

/-- The base point's weight is bounded above by every cube weight based at that point. -/
theorem characteristicWeight_le_characteristicCubeWeight_base
    (P : PlumbingGraph V)
    (k : P.characteristicVectors) (x : V → ℤ) (S : Finset V) :
    P.characteristicWeight k x ≤ P.characteristicCubeWeight k x S := by
  simpa using
    P.characteristicWeight_cubeVertex_le_characteristicCubeWeight k (Finset.empty_subset S) x

/-- Characteristic cube weight is monotone under enlarging the set of cube directions. -/
theorem characteristicCubeWeight_mono
    (P : PlumbingGraph V)
    (k : P.characteristicVectors) {S T : Finset V} (hST : S ⊆ T) (x : V → ℤ) :
    P.characteristicCubeWeight k x S ≤ P.characteristicCubeWeight k x T := by
  let y := (P.characteristicCubeWeightValues k x S).max'
    (P.characteristicCubeWeightValues_nonempty k x S)
  have hy : y ∈ P.characteristicCubeWeightValues k x S :=
    Finset.max'_mem _ _
  obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hy
  change y ≤ P.characteristicCubeWeight k x T
  rw [← hzy]
  exact P.characteristicWeight_le_characteristicCubeWeight k (cubeVertices_subset hST x hz)

/-- The characteristic cube weight of the zero-dimensional cube is the point weight of its base
point. -/
@[simp]
theorem characteristicCubeWeight_empty (P : PlumbingGraph V) (k : P.characteristicVectors)
    (x : V → ℤ) :
    P.characteristicCubeWeight k x ∅ = P.characteristicWeight k x := by
  apply le_antisymm
  · let y := (P.characteristicCubeWeightValues k x ∅).max'
      (P.characteristicCubeWeightValues_nonempty k x ∅)
    have hy : y ∈ P.characteristicCubeWeightValues k x ∅ :=
      Finset.max'_mem _ _
    obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hy
    change y ≤ P.characteristicWeight k x
    rw [← hzy]
    rw [mem_cubeVertices] at hz
    obtain ⟨T, hT, rfl⟩ := hz
    simp at hT
    simp [hT]
  · exact P.characteristicWeight_le_characteristicCubeWeight_base k x ∅

end PlumbingGraph

end TauCeti
