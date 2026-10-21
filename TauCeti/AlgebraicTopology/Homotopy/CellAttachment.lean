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
dimension `n + 1`. More generally, for any relative CW complex `f : X ⟶ Y` in Mathlib's categorical
sense, on a Hausdorff space `X`, the classical skeleton `skeletonLT Y (n + 1)` is the image of the
stage `c.F.obj (n + 1)`, and it is the range of `f` when no cells of dimension at most `n` are
attached. So the statements for the inclusion of a skeleton
(`TauCeti.surjective_homotopyGroupMap_skeletonLT`, `TauCeti.injective_homotopyGroupMap_skeletonLT`)
apply: the stage `c.F.obj (n + 1)` is surjective on `π_k` for `k ≤ n`
(`TopCat.RelativeCWComplex.surjective_homotopyGroupMap_incl_app`), and `f` is bijective on `π_k` for
`k < n` when there are no cells of dimension at most `n`
(`TopCat.RelativeCWComplex.bijective_homotopyGroupMap`). The stages and `f` are closed embeddings,
which identifies them with their ranges. Attaching cells of a single dimension is such a relative
CW complex (`HomotopicalAlgebra.AttachCells.toRelativeCWComplex`).

Conversely, a cell attached along the constant map at `x` closes up to a sphere at `x`, so a map
out of `Y` that is a generalized loop `γ` on such a cell sends the class of that sphere to the
class of `γ` (`TauCeti.mk_mem_range_homotopyGroupMap_of_cellAttachmentCell_comp`). This is how
cells realize classes of a target space in CW approximation.

When `n ≥ 1`, attaching cells kills chosen classes of `π_n(X, x)`. A generalized loop `p`
representing a class gives the attaching map `GenLoop.diskBoundaryMap p`, the
corresponding pointed map `Sⁿ → X`. It becomes null-homotopic in `Y`
(`TauCeti.cellAttachment_attachingMap_nullhomotopic`), so the class of `p` maps to the identity
(`TauCeti.map_cellAttachmentIncl_mk_eq_one`). If the classes of the attaching loops generate
`π_n(X, x)` as a normal subgroup, the surjection on `π_n` then makes `π_n(Y, f x)` trivial
(`TauCeti.subsingleton_homotopyGroup_cellAttachment`).

## Main results

* `TopCat.RelativeCWComplex.surjective_homotopyGroupMap_incl_app`: the stage carrying the cells
  of dimension at most `n` of a relative CW complex is surjective on `π_k` for `k ≤ n`.
* `TopCat.RelativeCWComplex.surjective_homotopyGroupMap`,
  `TopCat.RelativeCWComplex.bijective_homotopyGroupMap`: a relative CW complex without cells of
  dimension at most `n` is surjective on `π_k` for `k ≤ n` and bijective for `k < n`.
* `HomotopicalAlgebra.AttachCells.surjective_homotopyGroupMap`: attaching `(n + 1)`-cells is
  surjective on `π_k` for `k ≤ n`.
* `HomotopicalAlgebra.AttachCells.bijective_homotopyGroupMap`: attaching `(n + 1)`-cells is
  bijective on `π_k` for `k < n`.
* `TauCeti.mk_mem_range_homotopyGroupMap_of_cellAttachmentCell_comp`: a cell attached along a
  constant map realizes the class of the generalized loop it is sent onto.
* `TauCeti.subsingleton_homotopyGroup_cellAttachment`: attaching `(n + 1)`-cells along
  generators of `π_n(X, x)` kills `π_n`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Corollary 4.12, the same section for attaching cells to kill homotopy
  groups, and Proposition 4.13 for attaching spheres to realize them.
-/

public section

noncomputable section

universe u v

open CategoryTheory Topology Set TauCeti

namespace TopCat.RelativeCWComplex

variable {X Y : TopCat.{u}} {f : X ⟶ Y} (c : RelativeCWComplex.{u} f) [T2Space X]
  {N : Type v} [Finite N] {n : ℕ}

/-- **A stage of a relative CW complex is surjective on `π_k` below its dimension** (Hatcher,
Corollary 4.12). If `f : X ⟶ Y` is a relative CW complex on a Hausdorff space `X`, the inclusion
of the stage `c.F.obj (n + 1)`, which carries the cells of dimension at most `n`, induces a
surjection `π_k(c.F.obj (n + 1), y) → π_k(Y, y)`, where `k = Nat.card N ≤ n`. -/
theorem surjective_homotopyGroupMap_incl_app (hN : Nat.card N ≤ n) (y : c.F.obj (n + 1)) :
    Function.Surjective (HomotopyGroup.map (N := N) (x := y) (c.incl.app (n + 1)).hom rfl) := by
  let := c.toRelCWComplex
  have := c.t2Space
  rw [HomotopyGroup.map_eq_comp_of_isEmbedding (c.isClosedEmbedding_incl_app (n + 1)).isEmbedding y]
  exact (Equiv.surjective _).comp ((surjective_homotopyGroupMap_skeletonLT hN
    (c.range_incl_app_eq_toRelCWComplex_skeletonLT (n + 1)).symm (subset_univ _) _).comp
      (Equiv.surjective _))

/-- **A relative CW complex without cells of dimension at most `n` is surjective on `π_k` for
`k ≤ n`** (Hatcher, Corollary 4.12). If `f : X ⟶ Y` is a relative CW complex on a Hausdorff space
`X` all of whose cells have dimension greater than `n`, then `f` induces a surjection
`π_k(X, x) → π_k(Y, f x)`, where `k = Nat.card N ≤ n`. -/
theorem surjective_homotopyGroupMap (hc : ∀ m ≤ n, IsEmpty (c.attachCells m (not_isMax m)).ι)
    (hN : Nat.card N ≤ n) (x : X) :
    Function.Surjective (HomotopyGroup.map (N := N) (x := x) f.hom rfl) := by
  let := c.toRelCWComplex
  have := c.t2Space
  have hA := c.skeletonLT_toRelCWComplex_eq_range fun m hm ↦ hc m (Nat.lt_succ_iff.1 hm)
  rw [HomotopyGroup.map_eq_comp_of_isEmbedding c.isClosedEmbedding.isEmbedding x]
  exact (Equiv.surjective _).comp ((surjective_homotopyGroupMap_skeletonLT hN hA
    (subset_univ _) _).comp (Equiv.surjective _))

/-- **A relative CW complex without cells of dimension at most `n` is bijective on `π_k` for
`k < n`** (Hatcher, Corollary 4.12). If `f : X ⟶ Y` is a relative CW complex on a Hausdorff space
`X` all of whose cells have dimension greater than `n`, then `f` induces a bijection
`π_k(X, x) → π_k(Y, f x)`, where `k = Nat.card N < n`. -/
theorem bijective_homotopyGroupMap (hc : ∀ m ≤ n, IsEmpty (c.attachCells m (not_isMax m)).ι)
    (hN : Nat.card N < n) (x : X) :
    Function.Bijective (HomotopyGroup.map (N := N) (x := x) f.hom rfl) := by
  refine ⟨?_, c.surjective_homotopyGroupMap hc hN.le x⟩
  let := c.toRelCWComplex
  have := c.t2Space
  have hA := c.skeletonLT_toRelCWComplex_eq_range fun m hm ↦ hc m (Nat.lt_succ_iff.1 hm)
  rw [HomotopyGroup.map_eq_comp_of_isEmbedding c.isClosedEmbedding.isEmbedding x]
  exact (Equiv.injective _).comp ((injective_homotopyGroupMap_skeletonLT hN hA
    (subset_univ _) _).comp (Equiv.injective _))

end TopCat.RelativeCWComplex

namespace HomotopicalAlgebra.AttachCells

variable {X Y : TopCat.{u}} {f : X ⟶ Y} {N : Type v} [T2Space X] [Finite N] {n : ℕ}
  (c : AttachCells.{u} (TopCat.RelativeCWComplex.basicCell (n + 1)) f)
include c

/-- **Attaching `(n + 1)`-cells is surjective on `π_k` for `k ≤ n`** (Hatcher, Corollary 4.12).
If `Y` is obtained from a Hausdorff space `X` by attaching `(n + 1)`-disks along `f`, then `f`
induces a surjection `π_k(X, x) → π_k(Y, f x)`, where `k = Nat.card N ≤ n`. -/
theorem surjective_homotopyGroupMap (hN : Nat.card N ≤ n) (x : X) :
    Function.Surjective (HomotopyGroup.map (N := N) (x := x) f.hom rfl) :=
  c.toRelativeCWComplex.surjective_homotopyGroupMap
    (fun _ hm ↦ c.isEmpty_toRelativeCWComplex_attachCells_ι (by omega) _) hN x

/-- **Attaching `(n + 1)`-cells is bijective on `π_k` for `k < n`** (Hatcher, Corollary 4.12).
If `Y` is obtained from a Hausdorff space `X` by attaching `(n + 1)`-disks along `f`, then `f`
induces a bijection `π_k(X, x) → π_k(Y, f x)`, where `k = Nat.card N < n`. -/
theorem bijective_homotopyGroupMap (hN : Nat.card N < n) (x : X) :
    Function.Bijective (HomotopyGroup.map (N := N) (x := x) f.hom rfl) :=
  c.toRelativeCWComplex.bijective_homotopyGroupMap
    (fun _ hm ↦ c.isEmpty_toRelativeCWComplex_attachCells_ι (by omega) _) hN x

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

/-! ### Realizing classes by spheres -/

namespace TauCeti

open scoped Topology.Homotopy unitInterval

variable {X Y : TopCat.{u}} {ι : Type u} {n : ℕ} {x : X} {y : Y}

/-- **A cell attached along a constant map realizes a class** (Hatcher, Proposition 4.13). If the
`(n + 1)`-cell indexed by `i` is attached along the constant map at `x`, it closes up to a sphere
at `x`. If a map `g` out of the cell attachment is a generalized loop `γ` on this cell, read on
the disk through `TauCeti.diskHomeomorphCube`, then the class of `γ` is the image under `g` of the
class of that sphere. -/
theorem mk_mem_range_homotopyGroupMap_of_cellAttachmentCell_comp
    (φ : ι → (TopCat.diskBoundary (n + 1) ⟶ X)) {i : ι}
    (hi : φ i = TopCat.ofHom (ContinuousMap.const _ x)) (g : cellAttachment φ ⟶ Y)
    (hg : g (cellAttachmentIncl φ x) = y) (γ : Ω^ (Fin (n + 1)) Y y)
    (hγ : cellAttachmentCell φ i ≫ g = GenLoop.diskMap γ) :
    (⟦γ⟧ : HomotopyGroup (Fin (n + 1)) Y y) ∈ Set.range (HomotopyGroup.map g.hom hg) := by
  let c := cellAttachmentCell φ i
  -- The characteristic map of the cell, read on the cube, is a generalized loop: the boundary of
  -- the cube goes to the boundary sphere of the disk, attached at `x`.
  let q : Ω^ (Fin (n + 1)) (cellAttachment φ) (cellAttachmentIncl φ x) :=
    ⟨c.hom.comp ((diskHomeomorphCube (n + 1)).symm : C(I^(Fin (n + 1)), TopCat.disk (n + 1))),
      fun t ht ↦ by
        obtain ⟨s, hs⟩ := (diskHomeomorphCube_mem_boundary_iff _).1
          (((diskHomeomorphCube (n + 1)).apply_symm_apply t).symm ▸ ht)
        have h := ConcreteCategory.congr_hom (cellAttachment_boundary φ i) s
        rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hs, hi] at h
        -- `h` evaluates the constant attaching map at `s` and the composite at `t`, both by
        -- definition.
        exact h.symm⟩
  refine ⟨⟦q⟧, ?_⟩
  rw [HomotopyGroup.map_mk]
  congr 1
  ext t
  rw [GenLoop.map_apply]
  refine (ConcreteCategory.congr_hom hγ ((diskHomeomorphCube (n + 1)).symm t)).trans ?_
  simp

end TauCeti

/-! ### Killing `πₙ` -/

namespace TauCeti

open scoped Topology.Homotopy

variable {X : TopCat.{u}} {ι : Type u} {n : ℕ} [NeZero n] {x : X}

/-- **Attaching a cell along a generalized loop kills its class.** If the cell indexed by `i` is
attached along the map `GenLoop.diskBoundaryMap p` of a generalized loop `p`, then the class of `p`
maps to the identity of `πₙ` after attaching the cells. -/
theorem map_cellAttachmentIncl_mk_eq_one (φ : ι → (TopCat.diskBoundary (n + 1) ⟶ X)) {i : ι}
    {p : Ω^ (Fin n) X x} (h : φ i = GenLoop.diskBoundaryMap p) :
    HomotopyGroup.map (cellAttachmentIncl φ).hom rfl (⟦p⟧ : HomotopyGroup (Fin n) X x) = 1 := by
  rw [HomotopyGroup.map_mk_eq_one_iff_nullhomotopic_diskBoundaryMap_comp, ← h, TopCat.hom_comp]
  exact cellAttachment_attachingMap_nullhomotopic φ i

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
    exact map_cellAttachmentIncl_mk_eq_one _ rfl
  refine subsingleton_of_forall_eq 1 fun b ↦ ?_
  obtain ⟨a, rfl⟩ := surjective_homotopyGroupMap_cellAttachmentIncl
    (fun i ↦ GenLoop.diskBoundaryMap (p i)) (N := Fin n) (by simp) x b
  exact f.mem_ker.1 (hker (Subgroup.mem_top a))

end TauCeti
