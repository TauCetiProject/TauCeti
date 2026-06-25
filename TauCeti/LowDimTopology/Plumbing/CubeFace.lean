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

`w_k(x + E_v, S.erase v) ≤ w_k(x, S)`.

Together with `characteristicCubeWeight_mono` applied to `S.erase v ⊆ S`, this is the
nonnegativity input for the `U`-powers in the lattice-homology cubical differential.

## Main results

* `TauCeti.PlumbingGraph.cubeVertices_add_single_erase_subset`: the upper face vertices are cube
  vertices.
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

private theorem cubeVertex_add_single_of_notMem {T : Finset V} {v : V} (hv : v ∉ T) (x : V → ℤ) :
    cubeVertex (x + Pi.single v (1 : ℤ)) T = cubeVertex x T + Pi.single v 1 := by
  ext w
  by_cases hw : w = v
  · subst hw
    simp [hv]
  · simp [hw]

private theorem cubeVertex_insert_eq_cubeVertex_add_single {T : Finset V} {v : V} (hv : v ∉ T)
    (x : V → ℤ) :
    cubeVertex x (insert v T) = cubeVertex (x + Pi.single v (1 : ℤ)) T := by
  calc
    cubeVertex x (insert v T) = cubeVertex x T + Pi.single v (1 : ℤ) :=
      cubeVertex_insert hv x
    _ = cubeVertex (x + Pi.single v (1 : ℤ)) T :=
      (cubeVertex_add_single_of_notMem hv x).symm

variable [DecidableEq (V → ℤ)]

/-- The vertices of the upper face based at `x + E_v` are vertices of the original cube, provided
`v` is one of the original cube directions. -/
@[grind =>]
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

/-- The characteristic weight of an upper face is bounded above by the characteristic weight of
the whole cube. This is the inequality that makes the corresponding `U`-exponent nonnegative in
the lattice-homology cubical differential. -/
@[grind =>]
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
