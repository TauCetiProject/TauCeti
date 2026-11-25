/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.CWComplex.Classical.Subcomplex
public import TauCeti.Topology.PathComponent

/-!
# Path components of a CW complex

A closed cell of a relative CW complex is path connected, as the image of a closed ball under its
characteristic map (`Topology.RelCWComplex.isPathConnected_closedCell`). So each closed cell of a
CW complex `C` lies in a single path component of `C`, the path component of its centre, and the
path component `pathComponentIn C x` of a point `x` is the union of the open cells whose centre it
contains. It is therefore a subcomplex of `C` (`Topology.CWComplex.pathComponentInSubcomplex`),
whose cells are those of `C` with centre joined to `x` inside `C`. When `x ∉ C` it is the empty
subcomplex.

The path components partition the cells: every cell lies in the subcomplex of the path component
of its centre and in no other. This is how constructions on a connected CW complex, such as
Brown's semi-free model of the chains on the based path space, are carried to a CW complex that
need not be path connected, one path component at a time.

## Main definitions and results

* `Topology.RelCWComplex.isPathConnected_closedCell`: closed cells are path connected.
* `Topology.CWComplex.pathComponentInSubcomplex C x`: the path component of `x` in `C`, as a
  subcomplex.
* `Topology.CWComplex.coe_pathComponentInSubcomplex`: its underlying set is `pathComponentIn C x`.
* `Topology.CWComplex.mem_pathComponentInSubcomplex_I_iff`: a cell belongs to it exactly when its
  centre is joined to `x` in `C`.
* `Topology.CWComplex.pathComponent_subset_pathComponentInSubcomplex`: it contains the path
  component of `x` in the ambient space whenever `C` does.
* `Topology.CWComplex.sigmaPathComponentCellEquiv`: for a basepoint chosen in each path component,
  the cells of the subcomplexes of the path components are together the cells of the complex.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0 (cell complexes and subcomplexes) and the Appendix (the topology of cell
  complexes).
-/

public section

noncomputable section

open Metric Set

namespace Topology

variable {X : Type*} [TopologicalSpace X]

/-- **A closed cell of a relative CW complex is path connected**: it is the image of the closed
unit ball under the characteristic map, which is continuous there. -/
theorem RelCWComplex.isPathConnected_closedCell {C D : Set X} [RelCWComplex C D] (n : ℕ)
    (j : cell C n) : IsPathConnected (closedCell n j) :=
  (isPathConnected_closedBall zero_le_one).image' (continuousOn n j)

/-- A closed cell lies in the path component of its centre, inside the complex. -/
theorem RelCWComplex.closedCell_subset_pathComponentIn {C D : Set X} [RelCWComplex C D] (n : ℕ)
    (j : cell C n) : closedCell n j ⊆ pathComponentIn C (map n j 0) :=
  (isPathConnected_closedCell n j).subset_pathComponentIn (map_zero_mem_closedCell n j)
    (closedCell_subset_complex n j)

/-- A closed cell whose centre lies in the path component of `x` in the complex lies in that path
component. -/
theorem RelCWComplex.closedCell_subset_pathComponentIn_of_mem {C D : Set X} [RelCWComplex C D]
    {x : X} {n : ℕ} {j : cell C n} (h : map n j 0 ∈ pathComponentIn C x) :
    closedCell n j ⊆ pathComponentIn C x :=
  (closedCell_subset_pathComponentIn n j).trans (pathComponentIn_congr h).subset

namespace CWComplex

variable [T2Space X] (C : Set X) [CWComplex C]

/-- **The path component of a point in a CW complex is a subcomplex**: the path component
`pathComponentIn C x`, made of the cells of `C` whose centre is joined to `x` in `C`. It is the
empty subcomplex when `x ∉ C`. -/
def pathComponentInSubcomplex (x : X) : Subcomplex C :=
  Subcomplex.mk' C (pathComponentIn C x) (fun n ↦ {j | map n j 0 ∈ pathComponentIn C x})
    (fun _ j ↦ RelCWComplex.closedCell_subset_pathComponentIn_of_mem j.property)
    (by
      refine subset_antisymm (iUnion₂_subset fun n j ↦ ?_) fun y hy ↦ ?_
      · exact (openCell_subset_closedCell n _).trans
          (RelCWComplex.closedCell_subset_pathComponentIn_of_mem j.property)
      · have hyC : y ∈ C := pathComponentIn_subset hy
        rw [← iUnion_openCell_eq_complex (C := C)] at hyC
        obtain ⟨n, j, hyj⟩ := mem_iUnion₂.1 hyC
        refine mem_iUnion₂.2 ⟨n, ⟨j, ?_⟩, hyj⟩
        rw [mem_ofPred_eq, ← pathComponentIn_congr hy, pathComponentIn_congr
          (RelCWComplex.closedCell_subset_pathComponentIn n j (openCell_subset_closedCell n j hyj))]
        exact mem_pathComponentIn_self
          (closedCell_subset_complex n j (map_zero_mem_closedCell n j)))

/-- The underlying set of the subcomplex of the path component of `x` is `pathComponentIn C x`. -/
@[simp]
theorem coe_pathComponentInSubcomplex (x : X) :
    (pathComponentInSubcomplex C x : Set X) = pathComponentIn C x :=
  (rfl)

/-- A cell belongs to the subcomplex of the path component of `x` exactly when its centre is joined
to `x` inside `C`. -/
@[simp]
theorem mem_pathComponentInSubcomplex_I_iff {x : X} {n : ℕ} {j : cell C n} :
    j ∈ (pathComponentInSubcomplex C x).I n ↔ map n j 0 ∈ pathComponentIn C x :=
  Iff.rfl

/-- If the path component of `x` in the ambient space lies in `C`, the subcomplex of the path
component of `x` in `C` contains it. -/
theorem pathComponent_subset_pathComponentInSubcomplex {x : X} (h : pathComponent x ⊆ C) :
    pathComponent x ⊆ pathComponentInSubcomplex C x :=
  isPathConnected_pathComponent.subset_pathComponentIn (mem_pathComponent_self x) h

/-- **The path components of a CW complex partition its cells.** For a CW complex `C` that is
all of `X` and a choice `β` of a basepoint in each path component of `X`, the cells of the
subcomplexes of the path components of the basepoints are together the cells of `C`, each once:
a cell lies in the path component of its centre. -/
def sigmaPathComponentCellEquiv (β : TauCeti.PathComponentBasepoints X)
    (hC : ∀ x, x ∈ C) :
    (Σ c : ZerothHomotopy X, Σ n, cell (pathComponentInSubcomplex C (β.point c) : Set X) n) ≃
      Σ n, cell C n where
  toFun x := ⟨x.2.1, x.2.2.val⟩
  invFun x := ⟨ZerothHomotopy.mk (map x.1 x.2 0), x.1, x.2,
    (joinedIn_univ.2 (β.joined_point_mk _)).mono fun y _ ↦ hC y⟩
  left_inv := by
    rintro ⟨c, n, j, hj⟩
    obtain rfl : ZerothHomotopy.mk (map n j 0) = c := by
      rw [← β.mk_point c, ZerothHomotopy.mk_eq_mk_iff]
      exact hj.joined.symm
    rfl
  right_inv _ := rfl

/-- The cell of `C` underlying a cell of the partition `sigmaPathComponentCellEquiv`. -/
@[simp]
theorem sigmaPathComponentCellEquiv_apply (β : TauCeti.PathComponentBasepoints X) (hC : ∀ x, x ∈ C)
    (x : Σ c : ZerothHomotopy X, Σ n, cell (pathComponentInSubcomplex C (β.point c) : Set X) n) :
    sigmaPathComponentCellEquiv C β hC x = ⟨x.2.1, x.2.2.val⟩ :=
  (rfl)

/-- A cell of `C` lies in the subcomplex of the path component of its centre. -/
@[simp]
theorem sigmaPathComponentCellEquiv_symm_apply_fst (β : TauCeti.PathComponentBasepoints X)
    (hC : ∀ x, x ∈ C) (x : Σ n, cell C n) :
    ((sigmaPathComponentCellEquiv C β hC).symm x).1 = ZerothHomotopy.mk (map x.1 x.2 0) :=
  (rfl)

end CWComplex

end Topology
