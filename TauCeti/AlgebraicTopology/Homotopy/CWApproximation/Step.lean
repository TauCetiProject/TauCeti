/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.CellAttachment

/-!
# CW approximation: the inductive step

A CW approximation of a space `X` is built by attaching cells, one dimension at a time, to a space
mapping to `X` (Hatcher, Proposition 4.13). This file carries out one step. Let `f : Z ⟶ X` be a
map, `z` a point of `Z` and `n ≥ 1`. Attach `(n + 1)`-cells to `Z` of two kinds:

* one along the attaching map `GenLoop.diskBoundaryMap p` of every generalized loop `p` of
  dimension `n` at `z` whose class `f` sends to the identity of `πₙ(X, f z)`;
* one along the constant map at `z` for every generalized loop `γ` of dimension `n + 1` of `X` at
  `f z`.

The result is `TauCeti.cwApproximationStep f z n`, a cell attachment by definition, so the
general API of `TauCeti.cellAttachment` applies to it. The map `f` extends to
`TauCeti.cwApproximationStepMap f z n` out of it: over a cell of the first kind through a
null-homotopy of the composite of its attaching map with `f`, and over the cell attached for `γ` by
`γ` itself, read on the disk through `TauCeti.diskHomeomorphCube`. On homotopy groups at the base
point, the first two items below assume that `Z` is Hausdorff, while the third holds for any `Z`:

* attaching `(n + 1)`-cells changes no `πₖ` with `k < n` and is surjective on `πₙ` (Hatcher,
  Corollary 4.12), so the extension is bijective on `πₖ` for `k < n` exactly when `f` is
  (`TauCeti.bijective_homotopyGroupMap_cwApproximationStepMap_iff_of_lt`);
* the cells of the first kind kill the kernel of `f` on `πₙ`, so the extension is injective on
  `πₙ` (`TauCeti.injective_homotopyGroupMap_cwApproximationStepMap`), and bijective exactly when
  `f` is surjective on `πₙ`
  (`TauCeti.bijective_homotopyGroupMap_cwApproximationStepMap_iff_surjective`);
* the cell attached for `γ` is a sphere sent onto `γ`, so the extension is surjective on `πₙ₊₁`
  (`TauCeti.surjective_homotopyGroupMap_cwApproximationStepMap_succ`).

So if `Z` is Hausdorff and `f` is bijective on `πₖ` for `k < n` and surjective on `πₙ`, the
extension is bijective on `πₖ` for `k ≤ n` and surjective on `πₙ₊₁`, which is the inductive step
of Hatcher's construction.
All statements are about the homotopy groups at `z` and at its images.

## Main definitions

* `TauCeti.cwApproximationAttachingMap f z n`: the attaching maps of the cells.
* `TauCeti.cwApproximationStep f z n`: the space obtained by attaching them, with the inclusion
  `TauCeti.cwApproximationStepIncl f z n` of `Z`.
* `TauCeti.cwApproximationStepMap f z n`: the extension of `f`.

## Main results

* `TauCeti.injective_homotopyGroupMap_cwApproximationStepMap`: for Hausdorff `Z`, the extension is
  injective on `πₙ`.
* `TauCeti.surjective_homotopyGroupMap_cwApproximationStepMap_succ`: the extension is surjective on
  `πₙ₊₁`.
* `TauCeti.bijective_homotopyGroupMap_cwApproximationStepMap_iff_of_lt`: for Hausdorff `Z`, below
  `n`, the extension is bijective on `πₖ` exactly when `f` is.
* `TauCeti.bijective_homotopyGroupMap_cwApproximationStepMap_iff_surjective`: for Hausdorff `Z`, the
  extension is bijective on `πₙ` exactly when `f` is surjective on `πₙ`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Proposition 4.13 (CW approximation) and Corollary 4.12.
-/

public section

noncomputable section

universe u v

open CategoryTheory Topology
open scoped Topology.Homotopy unitInterval

namespace TauCeti

variable {Z X : TopCat.{u}} (f : Z ⟶ X) (z : Z) (n : ℕ) [NeZero n]

/-- The attaching maps of the `(n + 1)`-cells of the inductive step of CW approximation for
`f : Z ⟶ X` at `z`. A generalized loop `p` of dimension `n` at `z` whose class `f` sends to the
identity of `πₙ(X, f z)` gives a cell attached along `GenLoop.diskBoundaryMap p`, which kills the
class of `p`. A generalized loop of dimension `n + 1` of `X` at `f z` gives a cell attached along
the constant map at `z`, a sphere on which `f` is extended by that loop. -/
def cwApproximationAttachingMap :
    {p : Ω^ (Fin n) Z z // HomotopyGroup.map f.hom rfl (⟦p⟧ : HomotopyGroup (Fin n) Z z) = 1} ⊕
        Ω^ (Fin (n + 1)) X (f z) → (TopCat.diskBoundary (n + 1) ⟶ Z)
  | .inl p => GenLoop.diskBoundaryMap p.1
  | .inr _ => TopCat.ofHom (ContinuousMap.const _ z)

/-- A cell killing the class of `p` is attached along `GenLoop.diskBoundaryMap p`. -/
@[simp]
lemma cwApproximationAttachingMap_inl
    (p : {p : Ω^ (Fin n) Z z //
      HomotopyGroup.map f.hom rfl (⟦p⟧ : HomotopyGroup (Fin n) Z z) = 1}) :
    cwApproximationAttachingMap f z n (.inl p) = GenLoop.diskBoundaryMap p.1 :=
  (rfl)

/-- The cell attached for a generalized loop of `X` is attached along the constant map at `z`. -/
@[simp]
lemma cwApproximationAttachingMap_inr (γ : Ω^ (Fin (n + 1)) X (f z)) :
    cwApproximationAttachingMap f z n (.inr γ) = TopCat.ofHom (ContinuousMap.const _ z) :=
  (rfl)

/-- The space of the inductive step of CW approximation for `f : Z ⟶ X` at `z`: `Z` with the
`(n + 1)`-cells `TauCeti.cwApproximationAttachingMap f z n` attached. It is reducibly a
`TauCeti.cellAttachment`, so it is Hausdorff when `Z` is and carries the cell-attachment API. -/
abbrev cwApproximationStep : TopCat.{u} :=
  cellAttachment (cwApproximationAttachingMap f z n)

/-- The inclusion of `Z` into `TauCeti.cwApproximationStep f z n`. -/
abbrev cwApproximationStepIncl : Z ⟶ cwApproximationStep f z n :=
  cellAttachmentIncl (cwApproximationAttachingMap f z n)

/-- The attaching map of a cell killing a class, followed by `f`, extends over the disk. -/
private lemma exists_diskBoundaryInclusion_comp_eq_diskBoundaryMap_comp
    (p : {p : Ω^ (Fin n) Z z //
      HomotopyGroup.map f.hom rfl (⟦p⟧ : HomotopyGroup (Fin n) Z z) = 1}) :
    ∃ F : TopCat.disk (n + 1) ⟶ X,
      TopCat.diskBoundaryInclusion (n + 1) ≫ F = GenLoop.diskBoundaryMap p.1 ≫ f :=
  (TopCat.Hom.nullhomotopic_iff_exists_diskBoundaryInclusion_comp_eq _).1
    ((HomotopyGroup.map_mk_eq_one_iff_nullhomotopic_diskBoundaryMap_comp f rfl p.1).1 p.2)

/-- The map of a cell of the inductive step to `X`: a chosen null-homotopy of the attaching map
followed by `f` for a cell killing a class, and the loop `γ` read on the disk for the cell attached
for `γ`. -/
private def cwApproximationCellMap :
    {p : Ω^ (Fin n) Z z // HomotopyGroup.map f.hom rfl (⟦p⟧ : HomotopyGroup (Fin n) Z z) = 1} ⊕
        Ω^ (Fin (n + 1)) X (f z) → (TopCat.disk (n + 1) ⟶ X)
  | .inl p => (exists_diskBoundaryInclusion_comp_eq_diskBoundaryMap_comp f z n p).choose
  | .inr γ => GenLoop.diskMap γ

/-- Each cell map restricts on the boundary sphere to the attaching map followed by `f`. -/
private lemma cwApproximationAttachingMap_comp_eq (i) :
    cwApproximationAttachingMap f z n i ≫ f =
      TopCat.diskBoundaryInclusion (n + 1) ≫ cwApproximationCellMap f z n i :=
  match i with
  | .inl p => (exists_diskBoundaryInclusion_comp_eq_diskBoundaryMap_comp f z n p).choose_spec.symm
  | .inr γ => (GenLoop.diskBoundaryInclusion_comp_diskMap γ).symm

/-- The extension of `f` over `TauCeti.cwApproximationStep f z n`. It agrees with `f` on `Z`
(`TauCeti.cwApproximationStepIncl_comp_cwApproximationStepMap`), and on the cell attached for a
generalized loop `γ` of dimension `n + 1` of `X` it is `γ`, read on the disk through
`TauCeti.diskHomeomorphCube` (`TauCeti.cellAttachmentCell_inr_comp_cwApproximationStepMap`). -/
def cwApproximationStepMap : cwApproximationStep f z n ⟶ X :=
  cellAttachmentLift _ f (cwApproximationCellMap f z n) (cwApproximationAttachingMap_comp_eq f z n)

/-- The extension `TauCeti.cwApproximationStepMap f z n` restricts to `f` on `Z`. -/
@[reassoc (attr := simp)]
theorem cwApproximationStepIncl_comp_cwApproximationStepMap :
    cwApproximationStepIncl f z n ≫ cwApproximationStepMap f z n = f :=
  cellAttachmentIncl_lift _ _ _ _

/-- The extension `TauCeti.cwApproximationStepMap f z n` agrees with `f` on the points of `Z`. -/
@[simp]
theorem cwApproximationStepMap_cwApproximationStepIncl_apply (w : Z) :
    cwApproximationStepMap f z n (cwApproximationStepIncl f z n w) = f w := by
  rw [← ConcreteCategory.comp_apply, cwApproximationStepIncl_comp_cwApproximationStepMap]

/-- On the cell attached for a generalized loop `γ` of dimension `n + 1` of `X`, the extension
`TauCeti.cwApproximationStepMap f z n` is `γ`, read on the disk (`GenLoop.diskMap γ`). -/
@[reassoc]
theorem cellAttachmentCell_inr_comp_cwApproximationStepMap (γ : Ω^ (Fin (n + 1)) X (f z)) :
    cellAttachmentCell (cwApproximationAttachingMap f z n) (.inr γ) ≫
      cwApproximationStepMap f z n = GenLoop.diskMap γ :=
  cellAttachmentCell_lift _ _ _ _ _

/-- On homotopy groups at the base point, the extension `TauCeti.cwApproximationStepMap f z n`
composed with the inclusion of `Z` induces the map induced by `f`. -/
theorem homotopyGroupMap_cwApproximationStepMap_comp_homotopyGroupMap {N : Type v} :
    HomotopyGroup.map (N := N) (cwApproximationStepMap f z n).hom
        (cwApproximationStepMap_cwApproximationStepIncl_apply f z n z) ∘
      HomotopyGroup.map (cwApproximationStepIncl f z n).hom rfl =
    HomotopyGroup.map f.hom rfl := by
  rw [HomotopyGroup.map_comp_map]
  exact funext <| HomotopyGroup.map_congr
    (congrArg TopCat.Hom.hom (cwApproximationStepIncl_comp_cwApproximationStepMap f z n)) _ _

/-- **The extension is surjective on `πₙ₊₁`.** Every class of `πₙ₊₁(X, f z)` is the image under
`TauCeti.cwApproximationStepMap f z n` of the sphere formed by the cell attached for a
representative. -/
theorem surjective_homotopyGroupMap_cwApproximationStepMap_succ :
    Function.Surjective (HomotopyGroup.map (N := Fin (n + 1)) (cwApproximationStepMap f z n).hom
      (cwApproximationStepMap_cwApproximationStepIncl_apply f z n z)) :=
  Quotient.ind fun γ ↦ mk_mem_range_homotopyGroupMap_of_cellAttachmentCell_comp _
    (cwApproximationAttachingMap_inr f z n γ) _ _ γ
    (cellAttachmentCell_inr_comp_cwApproximationStepMap f z n γ)

variable [T2Space Z]

/-- **The extension is injective on `πₙ`.** The cells attached along generalized loops whose
classes `f` kills make the map `πₙ(cwApproximationStep f z n) → πₙ(X, f z)` injective, for a
Hausdorff space `Z`. -/
theorem injective_homotopyGroupMap_cwApproximationStepMap :
    Function.Injective (HomotopyGroup.map (N := Fin n) (cwApproximationStepMap f z n).hom
      (cwApproximationStepMap_cwApproximationStepIncl_apply f z n z)) := by
  let g := HomotopyGroup.mapHom (N := Fin n) (cwApproximationStepMap f z n).hom
    (cwApproximationStepMap_cwApproximationStepIncl_apply f z n z)
  refine (injective_iff_map_eq_one g).2 fun a ha ↦ ?_
  -- Every class comes from `Z`, and a class of `Z` killed by `f` is killed by a cell.
  obtain ⟨b, rfl⟩ := surjective_homotopyGroupMap_cellAttachmentIncl
    (cwApproximationAttachingMap f z n) (N := Fin n) (by simp) z a
  induction b using Quotient.inductionOn with
  | h p =>
    have hp : HomotopyGroup.map f.hom rfl (⟦p⟧ : HomotopyGroup (Fin n) Z z) = 1 :=
      (congrFun (homotopyGroupMap_cwApproximationStepMap_comp_homotopyGroupMap f z n) _).symm.trans
        ha
    exact map_cellAttachmentIncl_mk_eq_one _ (i := .inl ⟨p, hp⟩) rfl

/-- **The extension is bijective below `n` exactly when `f` is.** For `k < n`, the extension
`TauCeti.cwApproximationStepMap f z n` induces a bijection on `πₖ` if and only if `f` does, for a
Hausdorff space `Z`: attaching `(n + 1)`-cells does not change `πₖ`. Here `k = Nat.card N`. -/
theorem bijective_homotopyGroupMap_cwApproximationStepMap_iff_of_lt {N : Type v} [Finite N]
    (hN : Nat.card N < n) :
    Function.Bijective (HomotopyGroup.map (N := N) (cwApproximationStepMap f z n).hom
        (cwApproximationStepMap_cwApproximationStepIncl_apply f z n z)) ↔
      Function.Bijective (HomotopyGroup.map (N := N) (x := z) f.hom rfl) := by
  rw [← Function.Bijective.of_comp_iff _
    (bijective_homotopyGroupMap_cellAttachmentIncl (cwApproximationAttachingMap f z n) hN z),
    homotopyGroupMap_cwApproximationStepMap_comp_homotopyGroupMap]

/-- **The extension is bijective on `πₙ` exactly when `f` is surjective on `πₙ`.** The extension
`TauCeti.cwApproximationStepMap f z n` is always injective on `πₙ`, and it is surjective on `πₙ`
exactly when `f` is, for a Hausdorff space `Z`. -/
theorem bijective_homotopyGroupMap_cwApproximationStepMap_iff_surjective :
    Function.Bijective (HomotopyGroup.map (N := Fin n) (cwApproximationStepMap f z n).hom
        (cwApproximationStepMap_cwApproximationStepIncl_apply f z n z)) ↔
      Function.Surjective (HomotopyGroup.map (N := Fin n) f.hom (rfl : f z = f z)) := by
  rw [← homotopyGroupMap_cwApproximationStepMap_comp_homotopyGroupMap f z n,
    Function.Surjective.of_comp_iff _ (surjective_homotopyGroupMap_cellAttachmentIncl
      (cwApproximationAttachingMap f z n) (N := Fin n) (by simp) z)]
  exact and_iff_right (injective_homotopyGroupMap_cwApproximationStepMap f z n)

end TauCeti
