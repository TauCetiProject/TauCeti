/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Relative.Skeleton
public import TauCeti.AlgebraicTopology.Sphere.CubeQuotient
public import TauCeti.Topology.CWComplex.Abstract.AttachCells
public import TauCeti.Topology.CWComplex.Abstract.CellAttachment
public import TauCeti.Topology.CWComplex.Abstract.ClosedEmbedding
public import TauCeti.Topology.CWComplex.Abstract.Hausdorff
public import TauCeti.Topology.Homotopy.HomotopyGroup.Homeomorph

/-!
# Attaching cells: homotopy groups below their dimension, and killing `π_n`

Let `Y` be obtained from a Hausdorff space `X` by attaching `(n + 1)`-cells along maps of their
boundary spheres `Sⁿ → X`, and let `f : X ⟶ Y` be the inclusion. Then `f` induces a bijection
`π_k(X, x) → π_k(Y, f x)` for `k < n` and a surjection for `k = n`, at every base point `x`
(`HomotopicalAlgebra.AttachCells.bijective_homotopyGroupMap`,
`HomotopicalAlgebra.AttachCells.surjective_homotopyGroupMap`). For the space
`TauCeti.cellAttachment φ` obtained by attaching cells along a family `φ` of maps from spheres,
these are `TauCeti.bijective_homotopyGroupMap_cellAttachmentIncl` and
`TauCeti.surjective_homotopyGroupMap_cellAttachmentIncl`.

This is Hatcher's Corollary 4.12 for the pair `(Y, X)`, all of whose cells outside `X` have
dimension `n + 1`. Attaching the cells is a relative CW complex
(`HomotopicalAlgebra.AttachCells.toRelativeCWComplex`), whose classical skeleton
`skeletonLT Y (n + 1)` is the range of `f`, so the statements for the inclusion of a skeleton
(`TauCeti.surjective_homotopyGroupMap_skeletonLT`, `TauCeti.injective_homotopyGroupMap_skeletonLT`)
apply; `f` is a closed embedding, which identifies `X` with its range.

When `n ≥ 1`, attaching cells kills chosen classes of `π_n(X, x)`. A generalized loop `p`
representing a class gives the attaching map `TauCeti.GenLoop.diskBoundaryMap p`, the
corresponding pointed map `Sⁿ → X`. It becomes null-homotopic in `Y`
(`TauCeti.cellAttachment_attachingMap_nullhomotopic`), so the class of `p` maps to the identity
(`TauCeti.map_cellAttachmentIncl_mk_eq_one`). If the classes of the attaching loops generate
`π_n(X, x)` as a normal subgroup, the surjection on `π_n` then makes `π_n(Y, f x)` trivial
(`TauCeti.subsingleton_homotopyGroup_cellAttachment`).

## Main results

* `HomotopicalAlgebra.AttachCells.surjective_homotopyGroupMap`: attaching `(n + 1)`-cells is
  surjective on `π_k` for `k ≤ n`.
* `HomotopicalAlgebra.AttachCells.bijective_homotopyGroupMap`: attaching `(n + 1)`-cells is
  bijective on `π_k` for `k < n`.
* `TauCeti.subsingleton_homotopyGroup_cellAttachment`: attaching `(n + 1)`-cells along
  generators of `π_n(X, x)` kills `π_n`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Corollary 4.12, and the same section for attaching cells to kill homotopy
  groups.
-/

public section

noncomputable section

universe u v

open CategoryTheory Topology Set TauCeti

namespace HomotopicalAlgebra.AttachCells

variable {X Y : TopCat.{u}} {f : X ⟶ Y} {N : Type v} [T2Space X] [Finite N] {n : ℕ}
  (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell (n + 1)) f)
include c

/-- **Attaching `(n + 1)`-cells is surjective on `π_k` for `k ≤ n`** (Hatcher, Corollary 4.12).
If `Y` is obtained from a Hausdorff space `X` by attaching `(n + 1)`-disks along `f`, then `f`
induces a surjection `π_k(X, x) → π_k(Y, f x)`, where `k = Nat.card N ≤ n`. -/
theorem surjective_homotopyGroupMap (hN : Nat.card N ≤ n) (x : X) :
    Function.Surjective (HomotopyGroup.map (N := N) (x := x) f.hom rfl) := by
  let := c.toRelativeCWComplex.toRelCWComplex
  have := c.toRelativeCWComplex.t2Space
  rw [HomotopyGroup.map_eq_comp_of_isEmbedding
    c.toRelativeCWComplex.isClosedEmbedding.isEmbedding x]
  exact (Equiv.surjective _).comp ((surjective_homotopyGroupMap_skeletonLT hN
    (c.skeletonLT_toRelCWComplex le_rfl) (subset_univ _) _).comp (Equiv.surjective _))

/-- **Attaching `(n + 1)`-cells is bijective on `π_k` for `k < n`** (Hatcher, Corollary 4.12).
If `Y` is obtained from a Hausdorff space `X` by attaching `(n + 1)`-disks along `f`, then `f`
induces a bijection `π_k(X, x) → π_k(Y, f x)`, where `k = Nat.card N < n`. -/
theorem bijective_homotopyGroupMap (hN : Nat.card N < n) (x : X) :
    Function.Bijective (HomotopyGroup.map (N := N) (x := x) f.hom rfl) := by
  refine ⟨?_, c.surjective_homotopyGroupMap hN.le x⟩
  let := c.toRelativeCWComplex.toRelCWComplex
  have := c.toRelativeCWComplex.t2Space
  rw [HomotopyGroup.map_eq_comp_of_isEmbedding
    c.toRelativeCWComplex.isClosedEmbedding.isEmbedding x]
  exact (Equiv.injective _).comp ((injective_homotopyGroupMap_skeletonLT hN
    (c.skeletonLT_toRelCWComplex le_rfl) (subset_univ _) _).comp (Equiv.injective _))

end HomotopicalAlgebra.AttachCells

namespace TauCeti

variable {X : TopCat.{u}} [T2Space X] {ι : Type u} {n : ℕ}
  (φ : ι → (TopCat.diskBoundary (n + 1) ⟶ X)) {N : Type v} [Finite N]

/-- Attaching `(n + 1)`-cells to a Hausdorff space `X` along any family of maps `Sⁿ → X` induces
a surjection `π_k(X, x) → π_k(X ∪ eⁿ⁺¹, x)` for `k = Nat.card N ≤ n`. -/
theorem surjective_homotopyGroupMap_cellAttachmentIncl (hN : Nat.card N ≤ n) (x : X) :
    Function.Surjective (HomotopyGroup.map (N := N) (x := x) (cellAttachmentIncl φ).hom rfl) :=
  (cellAttachmentAttachCells φ).surjective_homotopyGroupMap hN x

/-- Attaching `(n + 1)`-cells to a Hausdorff space `X` along any family of maps `Sⁿ → X` induces
a bijection `π_k(X, x) → π_k(X ∪ eⁿ⁺¹, x)` for `k = Nat.card N < n`. -/
theorem bijective_homotopyGroupMap_cellAttachmentIncl (hN : Nat.card N < n) (x : X) :
    Function.Bijective (HomotopyGroup.map (N := N) (x := x) (cellAttachmentIncl φ).hom rfl) :=
  (cellAttachmentAttachCells φ).bijective_homotopyGroupMap hN x

end TauCeti

/-! ### Killing `πₙ` -/

namespace TauCeti

open scoped Topology.Homotopy

variable {X : TopCat.{u}} {ι : Type u} {n : ℕ} [NeZero n] {x : X}

/-- The attaching map `∂𝔻 (n + 1) ⟶ X` of the `(n + 1)`-cell that kills the class of a generalized
loop `p`: the pointed map `Sⁿ → X` corresponding to `p` (`GenLoop.toSphere`), with its source
written as Mathlib's sphere `TopCat.diskBoundary (n + 1)`. -/
def GenLoop.diskBoundaryMap (p : Ω^ (Fin n) X x) : TopCat.diskBoundary.{u} (n + 1) ⟶ X :=
  TopCat.ofHom ((GenLoop.toSphere p).comp ⟨ULift.down, continuous_uliftDown⟩)

@[simp]
theorem GenLoop.diskBoundaryMap_apply (p : Ω^ (Fin n) X x)
    (s : TopCat.diskBoundary.{u} (n + 1)) :
    GenLoop.diskBoundaryMap p s = GenLoop.toSphere p s.down :=
  (rfl)

/-- **Attaching a cell along a generalized loop kills its class.** After attaching
`(n + 1)`-cells along the generalized loops `p i`, the class of each `p i` maps to the identity
of `πₙ`. -/
theorem map_cellAttachmentIncl_mk_eq_one (p : ι → Ω^ (Fin n) X x) (i : ι) :
    HomotopyGroup.map (cellAttachmentIncl fun j ↦ GenLoop.diskBoundaryMap (p j)).hom rfl
      (⟦p i⟧ : HomotopyGroup (Fin n) X x) = 1 := by
  rw [HomotopyGroup.map_mk]
  refine (HomotopyGroup.mk_eq_one_iff_nullhomotopic_toSphere _).2 ?_
  rw [GenLoop.toSphere_map]
  -- the attaching map is `GenLoop.toSphere (p i)` precomposed with `ULift.down`, so
  -- `GenLoop.toSphere (p i)` is the attaching map precomposed with `ULift.up`
  have h : (GenLoop.toSphere (p i)) =
      (GenLoop.diskBoundaryMap (p i)).hom.comp ⟨ULift.up, continuous_uliftUp⟩ := by
    ext s
    exact (GenLoop.diskBoundaryMap_apply (p i) ⟨s⟩).symm
  rw [h, ← ContinuousMap.comp_assoc]
  exact (cellAttachment_attachingMap_nullhomotopic _ i).comp_left _

/-- **Attaching cells along generators kills `πₙ`** (Hatcher, Section 4.1). If the classes of
the generalized loops `p i` generate `πₙ(X, x)` as a normal subgroup, with `n ≥ 1` and `X`
Hausdorff, then attaching `(n + 1)`-cells along them makes `πₙ` trivial at the image of `x`. For
`n ≥ 2`, where `πₙ` is abelian, this asks that the classes generate `πₙ(X, x)`. -/
theorem subsingleton_homotopyGroup_cellAttachment [T2Space X] (p : ι → Ω^ (Fin n) X x)
    (hp : Subgroup.normalClosure (G := HomotopyGroup (Fin n) X x) (Set.range fun i ↦ ⟦p i⟧) = ⊤) :
    Subsingleton (HomotopyGroup (Fin n) (cellAttachment fun i ↦ GenLoop.diskBoundaryMap (p i))
      (cellAttachmentIncl (fun i ↦ GenLoop.diskBoundaryMap (p i)) x)) := by
  let f := HomotopyGroup.mapHom (N := Fin n) (x := x)
    (cellAttachmentIncl fun i ↦ GenLoop.diskBoundaryMap (p i)).hom rfl
  have hker : ⊤ ≤ f.ker := by
    rw [← hp]
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨i, rfl⟩
    exact map_cellAttachmentIncl_mk_eq_one p i
  refine subsingleton_of_forall_eq 1 fun b ↦ ?_
  obtain ⟨a, rfl⟩ := surjective_homotopyGroupMap_cellAttachmentIncl
    (fun i ↦ GenLoop.diskBoundaryMap (p i)) (N := Fin n) (by simp) x b
  exact f.mem_ker.1 (hker (Subgroup.mem_top a))

end TauCeti
