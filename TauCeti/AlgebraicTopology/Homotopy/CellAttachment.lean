/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Relative.Skeleton
public import TauCeti.Topology.CWComplex.Abstract.AttachCells
public import TauCeti.Topology.CWComplex.Abstract.CellAttachment
public import TauCeti.Topology.CWComplex.Abstract.ClosedEmbedding
public import TauCeti.Topology.CWComplex.Abstract.Hausdorff
public import TauCeti.Topology.Homotopy.HomotopyGroup.Homeomorph

/-!
# Attaching cells does not change homotopy groups below their dimension

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

When `n ≥ 1` and the attaching maps represent generators of `π_n(X, x)`, the surjection on `π_n`
is the step showing that the attached cells kill `π_n`: each attaching map becomes null-homotopic
in `Y` (`TauCeti.cellAttachment_attachingMap_nullhomotopic`).

## Main results

* `HomotopicalAlgebra.AttachCells.surjective_homotopyGroupMap`: attaching `(n + 1)`-cells is
  surjective on `π_k` for `k ≤ n`.
* `HomotopicalAlgebra.AttachCells.bijective_homotopyGroupMap`: attaching `(n + 1)`-cells is
  bijective on `π_k` for `k < n`.

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
