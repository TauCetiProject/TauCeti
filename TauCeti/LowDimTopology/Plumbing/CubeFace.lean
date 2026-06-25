/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LowDimTopology.Plumbing.CubeWeight

/-!
# Faces of plumbing-lattice cubes

This file records the elementary face inclusions for the finite cubes used in Némethi's
lattice homology. If `S` is a set of cube directions and `v ∈ S`, the two codimension-one
faces perpendicular to `v` have directions `S.erase v`: the lower face is based at `x`, and the
upper face is based at `x + E_v`.

Since the characteristic cube weight is the maximum of the point weights over all vertices,
these face inclusions give the inequalities

`w_k(x, S.erase v) ≤ w_k(x, S)`

and

`w_k(x + E_v, S.erase v) ≤ w_k(x, S)`.

Those are the nonnegativity inputs for the `U`-powers in the lattice-homology cubical
differential.

## Main results

* `TauCeti.PlumbingGraph.cubeVertices_erase_subset`: the lower face vertices are cube vertices.
* `TauCeti.PlumbingGraph.cubeVertices_add_single_erase_subset`: the upper face vertices are cube
  vertices.
* `TauCeti.PlumbingGraph.characteristicCubeWeight_erase_le`: the lower face weight is bounded
  by the cube weight.
* `TauCeti.PlumbingGraph.characteristicCubeWeight_add_single_erase_le`: the upper face weight is
  bounded by the cube weight.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L
("lattice homology"), whose cubical differential uses the difference between a cube weight and
its face weights. The convention follows Némethi, [arXiv:0709.0841](https://arxiv.org/abs/0709.0841).
-/

public section

namespace TauCeti

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V]

/-- Adding a basis vector to the base point is the same as adding it after forming any vertex
whose indexing subset does not already contain that direction. -/
theorem cubeVertex_add_single_of_notMem {T : Finset V} {v : V} (hv : v ∉ T) (x : V → ℤ) :
    cubeVertex (x + Pi.single v (1 : ℤ)) T = cubeVertex x T + Pi.single v 1 := by
  ext w
  by_cases hw : w = v
  · subst hw
    simp [hv]
  · simp [hw]

/-- Inserting a direction into the vertex subset agrees with moving to the corresponding upper
base point and using the original subset. -/
theorem cubeVertex_insert_eq_cubeVertex_add_single {T : Finset V} {v : V} (hv : v ∉ T)
    (x : V → ℤ) :
    cubeVertex x (insert v T) = cubeVertex (x + Pi.single v (1 : ℤ)) T := by
  calc
    cubeVertex x (insert v T) = cubeVertex x T + Pi.single v (1 : ℤ) :=
      cubeVertex_insert hv x
    _ = cubeVertex (x + Pi.single v (1 : ℤ)) T :=
      (cubeVertex_add_single_of_notMem hv x).symm

variable [DecidableEq (V → ℤ)]

/-- The vertices of the lower face obtained by removing the direction `v` are vertices of the
original cube. -/
theorem cubeVertices_erase_subset (x : V → ℤ) (S : Finset V) (v : V) :
    cubeVertices x (S.erase v) ⊆ cubeVertices x S :=
  cubeVertices_subset (Finset.erase_subset v S) x

/-- The vertices of the upper face based at `x + E_v` are vertices of the original cube, provided
`v` is one of the original cube directions. -/
theorem cubeVertices_add_single_erase_subset {S : Finset V} {v : V} (hv : v ∈ S)
    (x : V → ℤ) :
    cubeVertices (x + Pi.single v (1 : ℤ)) (S.erase v) ⊆ cubeVertices x S := by
  intro y hy
  rw [mem_cubeVertices] at hy ⊢
  obtain ⟨T, hTS, rfl⟩ := hy
  have hvT : v ∉ T := fun hvT => Finset.notMem_erase v S (hTS hvT)
  refine ⟨insert v T, ?_, ?_⟩
  · intro w hw
    rw [Finset.mem_insert] at hw
    rcases hw with rfl | hw
    · exact hv
    · exact Finset.erase_subset v S (hTS hw)
  · exact cubeVertex_insert_eq_cubeVertex_add_single hvT x

variable [Fintype V]

/-- The characteristic weight of a lower face is bounded above by the characteristic weight of
the whole cube. -/
theorem characteristicCubeWeight_erase_le
    (P : PlumbingGraph V) (k : P.characteristicVectors) (x : V → ℤ)
    (S : Finset V) (v : V) :
    P.characteristicCubeWeight k x (S.erase v) ≤ P.characteristicCubeWeight k x S :=
  P.characteristicCubeWeight_mono k (Finset.erase_subset v S) x

/-- The characteristic weight of an upper face is bounded above by the characteristic weight of
the whole cube. This is the inequality that makes the corresponding `U`-exponent nonnegative in
the lattice-homology cubical differential. -/
theorem characteristicCubeWeight_add_single_erase_le
    (P : PlumbingGraph V) (k : P.characteristicVectors) {S : Finset V} {v : V} (hv : v ∈ S)
    (x : V → ℤ) :
    P.characteristicCubeWeight k (x + Pi.single v (1 : ℤ)) (S.erase v) ≤
      P.characteristicCubeWeight k x S := by
  apply P.characteristicCubeWeight_le k
  intro y hy
  exact P.characteristicWeight_le_characteristicCubeWeight k
    (cubeVertices_add_single_erase_subset hv x hy)

end PlumbingGraph

end TauCeti
