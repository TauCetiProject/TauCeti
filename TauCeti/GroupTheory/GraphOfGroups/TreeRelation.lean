/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.Presentation
public import TauCeti.Combinatorics.Graph.Serre.SpanningTree
public import TauCeti.Combinatorics.Quiver.PathWeight

/-!
# Omitting the tree relations of a graph of groups

Let `𝔸` be a graph of groups over a connected Serre graph `Γ` and let `T` be a spanning tree of
`Γ`. The group `π₁(𝔸, T)` is the free product of the vertex groups and the free group on the darts
modulo `rev e = e⁻¹`, `e ω_e(c) e⁻¹ = α_e(c)` and `e = 1` for the darts `e` of `T`. Omitting the
last family of relations gives the group `π₁(𝔸, ∅)`, and this adds a free factor whose rank is the
number of geometric edges of `T`: for any orientation `O` of `Γ`,

`π₁(𝔸, ∅) ≃* π₁(𝔸, T) ∗ F(O ∩ T)`.

In particular the relations `e = 1` for `e ∈ T` do not follow from the others: in `π₁(𝔸, ∅)` the
darts of `O ∩ T` freely generate a free factor.

The isomorphism depends on a base vertex `v₀`. Write `g_v ∈ π₁(𝔸, ∅)` for the product of the dart
generators along the tree path from `v₀` to `v`. The inverse isomorphism sends `a ∈ A_v` to
`g_v a g_v⁻¹`, the generator of a dart `e` of `π₁(𝔸, T)` to `g_{src e} e g_{tgt e}⁻¹`, and the free
generator of a dart `e ∈ O ∩ T` to the generator of `e` in `π₁(𝔸, ∅)`. Conversely, write
`t_v ∈ F(O ∩ T)` for the product of the signed coordinates of the darts along the same tree path.
The isomorphism sends `a ∈ A_v` to `t_v⁻¹ a t_v` and the generator of a dart `e` to
`t_{src e}⁻¹ e t_{tgt e}`; for a dart of `T` this is its signed coordinate in `F(O ∩ T)`.

## Main definitions

* `TauCeti.GraphOfGroups.π₁Tree.treeWord`: the signed coordinate of a dart in the free group on
  the positively oriented darts of `T`.
* `TauCeti.GraphOfGroups.π₁Tree.emptyEquivCoprod`: the isomorphism
  `π₁(𝔸, ∅) ≃* π₁(𝔸, T) ∗ F(O ∩ T)`.

## Main results

* `TauCeti.GraphOfGroups.π₁Tree.emptyEquivCoprod_of`,
  `TauCeti.GraphOfGroups.π₁Tree.emptyEquivCoprod_edge`: the isomorphism on the generators.
* `TauCeti.GraphOfGroups.π₁Tree.emptyEquivCoprod_of_base`,
  `TauCeti.GraphOfGroups.π₁Tree.emptyEquivCoprod_edge_of_mem`: the base vertex group goes to
  the first factor, and a positively oriented tree dart to its free generator.
* `TauCeti.GraphOfGroups.π₁Tree.emptyEquivCoprod_symm_inl_of`,
  `TauCeti.GraphOfGroups.π₁Tree.emptyEquivCoprod_symm_inl_edge`,
  `TauCeti.GraphOfGroups.π₁Tree.emptyEquivCoprod_symm_inr_of`: the inverse isomorphism on the
  generators.

## References

* J.-P. Serre, *Trees*, Chapter I, §5.1.
* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2.
-/

public section

universe u v w x

namespace TauCeti.GraphOfGroups.π₁Tree

open SerreGraph Monoid.Coprod

variable {Γ : SerreGraph.{u, v}} (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V)
  (T : Γ.SpanningTree) {O : Set Γ.E} (hO : Γ.IsOrientation O)

/-! ### Coordinates of tree darts -/

variable (O) in
/-- The signed coordinate of a dart in the free group on the positively oriented darts of the
spanning tree `T`: the generator `e` if `e ∈ O ∩ T`, the inverse of the generator `rev e` if
`rev e ∈ O ∩ T`, and `1` for a dart outside `T`. -/
noncomputable def treeWord (e : Γ.E) : FreeGroup ↥(O ∩ T.darts) :=
  FreeGroup.map (Set.inclusion Set.sdiff_compl.subset) (dartWord O T.dartsᶜ e)

@[simp] theorem treeWord_of_mem {e : Γ.E} (he : e ∈ O ∩ T.darts) :
    treeWord T O e = FreeGroup.of ⟨e, he⟩ := by
  simp [treeWord, dartWord_of_mem (show e ∈ O \ T.dartsᶜ from ⟨he.1, not_not_intro he.2⟩)]

@[simp] theorem treeWord_of_rev_mem {e : Γ.E} (he : e ∉ O ∩ T.darts)
    (hr : Γ.rev e ∈ O ∩ T.darts) : treeWord T O e = (FreeGroup.of ⟨Γ.rev e, hr⟩)⁻¹ := by
  simp [treeWord, dartWord_of_rev_mem (show e ∉ O \ T.dartsᶜ by simpa using he)
    (show Γ.rev e ∈ O \ T.dartsᶜ from ⟨hr.1, not_not_intro hr.2⟩)]

/-- A dart outside the spanning tree has trivial coordinate. -/
@[simp] theorem treeWord_of_notMem {e : Γ.E} (he : e ∉ T.darts) : treeWord T O e = 1 := by
  have hr : Γ.rev e ∉ T.darts := fun h => he (Γ.rev_rev e ▸ T.rev_mem _ h)
  simp [treeWord, dartWord_of_notMem (O := O) (T := T.dartsᶜ) (e := e) (by simp [he])
    (by simp [hr])]

include hO in
/-- Reversing a dart inverts its coordinate. -/
@[simp] theorem treeWord_rev (e : Γ.E) : treeWord T O (Γ.rev e) = (treeWord T O e)⁻¹ := by
  simp [treeWord, dartWord_rev hO]

include hO in
/-- On a tree dart, a reversal-compatible dart weight is recovered from the coordinate. -/
private theorem lift_treeWord {H : Type*} [Group H] {wt : Γ.E → H}
    (hwt : ∀ e, wt (Γ.rev e) = (wt e)⁻¹) {e : Γ.E} (he : e ∈ T.darts) :
    FreeGroup.lift (fun x : ↥(O ∩ T.darts) => wt x.1) (treeWord T O e) = wt e := by
  by_cases heO : e ∈ O
  · simp [treeWord_of_mem T ⟨heO, he⟩]
  · -- Otherwise `e` is the reverse of the positively oriented tree dart `rev e`.
    have hr : Γ.rev e ∈ O ∩ T.darts := ⟨(hO.mem_rev_iff Γ e).2 heO, T.rev_mem e he⟩
    rw [← Γ.rev_rev e, treeWord_rev T hO, treeWord_of_mem T hr]
    simp [hwt]

/-! ### The two homomorphisms -/

variable (O)

/-- The homomorphism `π₁(𝔸, T) ∗ F(O ∩ T) →* π₁(𝔸, ∅)`, conjugating along the tree paths from
`v₀`. -/
private noncomputable def coprodToEmpty :
    π₁Tree 𝔸 T.darts ∗ FreeGroup ↥(O ∩ T.darts) →* π₁Tree 𝔸 ∅ :=
  Monoid.Coprod.lift
    (conjLift (fun v => (T.path v₀ v).weight fun {x y : Γ.V} (d : x ⟶ y) => edge ∅ d.1)
      (of ∅) (edge ∅)
      (fun e he => by simp [T.weight_path_tgt edge_rev v₀ he])
      edge_rev edge_mul_of_ω_mul_edge_inv)
    (FreeGroup.lift fun x => edge ∅ x.1)

/-- The homomorphism `π₁(𝔸, ∅) →* π₁(𝔸, T) ∗ F(O ∩ T)`, conjugating along the coordinates of the
tree paths from `v₀`. -/
private noncomputable def emptyToCoprod :
    π₁Tree 𝔸 ∅ →* π₁Tree 𝔸 T.darts ∗ FreeGroup ↥(O ∩ T.darts) :=
  conjLift
    (fun v => (inr ((T.path v₀ v).weight fun {x y : Γ.V} (d : x ⟶ y) => treeWord T O d.1))⁻¹)
    (fun v => inl.comp (of T.darts v)) (fun e => inl (edge T.darts e))
    (fun _ he => (Set.notMem_empty _ he).elim) (fun e => by simp)
    (fun e c => by simp only [MonoidHom.comp_apply, ← map_mul, ← map_inv,
      edge_mul_of_ω_mul_edge_inv])

private theorem emptyToCoprod_of (v : Γ.V) (a : 𝔸.vertexGroup v) :
    emptyToCoprod 𝔸 v₀ T O (of ∅ v a) =
      (inr ((T.path v₀ v).weight fun {x y : Γ.V} (d : x ⟶ y) => treeWord T O d.1))⁻¹ *
        inl (of T.darts v a) *
          inr ((T.path v₀ v).weight fun {x y : Γ.V} (d : x ⟶ y) => treeWord T O d.1) := by
  simp [emptyToCoprod]

private theorem emptyToCoprod_edge (e : Γ.E) :
    emptyToCoprod 𝔸 v₀ T O (edge ∅ e) =
      (inr ((T.path v₀ (Γ.src e)).weight fun {x y : Γ.V} (d : x ⟶ y) => treeWord T O d.1))⁻¹ *
        inl (edge T.darts e) *
          inr ((T.path v₀ (Γ.tgt e)).weight fun {x y : Γ.V} (d : x ⟶ y) => treeWord T O d.1) := by
  simp [emptyToCoprod]

variable {O}

include hO in
/-- The coordinate of a tree path, evaluated at the dart generators, is the product of the dart
generators along the path. -/
private theorem lift_weight_treeWord (v : Γ.V) :
    FreeGroup.lift (fun x : ↥(O ∩ T.darts) => edge (𝔸 := 𝔸) ∅ x.1)
        ((T.path v₀ v).weight fun {x y : Γ.V} (d : x ⟶ y) => treeWord T O d.1) =
      (T.path v₀ v).weight fun {x y : Γ.V} (d : x ⟶ y) => edge ∅ d.1 := by
  rw [Quiver.Path.map_weight]
  exact T.weight_path_congr (fun e he => lift_treeWord T hO edge_rev he) v₀ v

include hO in
/-- On a tree dart, the homomorphism takes values in the free factor. -/
private theorem emptyToCoprod_edge_of_mem {e : Γ.E} (he : e ∈ T.darts) :
    emptyToCoprod 𝔸 v₀ T O (edge ∅ e) = inr (treeWord T O e) := by
  simp [emptyToCoprod_edge, edge_eq_one he, T.weight_path_tgt (treeWord_rev T hO) v₀ he]

include hO in
/-- The homomorphism sends the product of dart generators along a tree path to its coordinate. -/
private theorem emptyToCoprod_weight (v : Γ.V) :
    emptyToCoprod 𝔸 v₀ T O ((T.path v₀ v).weight fun {x y : Γ.V} (d : x ⟶ y) => edge ∅ d.1) =
      inr ((T.path v₀ v).weight fun {x y : Γ.V} (d : x ⟶ y) => treeWord T O d.1) := by
  rw [Quiver.Path.map_weight, Quiver.Path.map_weight]
  exact T.weight_path_congr (fun e he => emptyToCoprod_edge_of_mem 𝔸 v₀ T hO he) v₀ v

include hO in
private theorem coprodToEmpty_comp_emptyToCoprod :
    (coprodToEmpty 𝔸 v₀ T O).comp (emptyToCoprod 𝔸 v₀ T O) = MonoidHom.id _ :=
  hom_ext (fun v => MonoidHom.ext fun a => by
      simp [emptyToCoprod_of, coprodToEmpty, lift_weight_treeWord 𝔸 v₀ T hO, mul_assoc])
    fun e => by
      simp [emptyToCoprod_edge, coprodToEmpty, lift_weight_treeWord 𝔸 v₀ T hO, mul_assoc]

include hO in
private theorem emptyToCoprod_comp_coprodToEmpty :
    (emptyToCoprod 𝔸 v₀ T O).comp (coprodToEmpty 𝔸 v₀ T O) = MonoidHom.id _ :=
  Monoid.Coprod.hom_ext
    (hom_ext (fun v => MonoidHom.ext fun a => by
        simp [emptyToCoprod_of, coprodToEmpty, emptyToCoprod_weight 𝔸 v₀ T hO, mul_assoc])
      fun e => by
        simp [emptyToCoprod_edge, coprodToEmpty, emptyToCoprod_weight 𝔸 v₀ T hO, mul_assoc])
    (FreeGroup.ext_hom _ _ fun x => by
      simp [coprodToEmpty, emptyToCoprod_edge_of_mem 𝔸 v₀ T hO x.2.2])

/-- Omitting the tree relations adds a free factor: for a spanning tree `T`, a base vertex `v₀`
and an orientation `O` of `Γ`, the group `π₁(𝔸, ∅)`, presented without the relations `e = 1` for
the darts `e` of `T`, is the free product of `π₁(𝔸, T)` and the free group on the positively
oriented darts of `T`. The inverse sends `a ∈ A_v` to `g_v a g_v⁻¹`, where `g_v` is the product of
the dart generators along the tree path from `v₀` to `v`. -/
noncomputable def emptyEquivCoprod : π₁Tree 𝔸 ∅ ≃* π₁Tree 𝔸 T.darts ∗ FreeGroup ↥(O ∩ T.darts) :=
  MonoidHom.toMulEquiv (emptyToCoprod 𝔸 v₀ T O) (coprodToEmpty 𝔸 v₀ T O)
    (coprodToEmpty_comp_emptyToCoprod 𝔸 v₀ T hO) (emptyToCoprod_comp_coprodToEmpty 𝔸 v₀ T hO)

/-- `emptyEquivCoprod` sends `a ∈ A_v` to `t_v⁻¹ a t_v`, where `t_v ∈ F(O ∩ T)` is the product of
the coordinates `treeWord` of the darts along the tree path from `v₀` to `v`. -/
theorem emptyEquivCoprod_of (v : Γ.V) (a : 𝔸.vertexGroup v) :
    emptyEquivCoprod 𝔸 v₀ T hO (of ∅ v a) =
      (inr ((T.path v₀ v).weight fun {x y : Γ.V} (d : x ⟶ y) => treeWord T O d.1))⁻¹ *
        inl (of T.darts v a) *
          inr ((T.path v₀ v).weight fun {x y : Γ.V} (d : x ⟶ y) => treeWord T O d.1) :=
  emptyToCoprod_of 𝔸 v₀ T O v a

/-- `emptyEquivCoprod` sends the generator of a dart `e` to `t_{src e}⁻¹ e t_{tgt e}`, where
`t_v ∈ F(O ∩ T)` is the product of the coordinates `treeWord` of the darts along the tree path
from `v₀` to `v`. -/
theorem emptyEquivCoprod_edge (e : Γ.E) :
    emptyEquivCoprod 𝔸 v₀ T hO (edge ∅ e) =
      (inr ((T.path v₀ (Γ.src e)).weight fun {x y : Γ.V} (d : x ⟶ y) => treeWord T O d.1))⁻¹ *
        inl (edge T.darts e) *
          inr ((T.path v₀ (Γ.tgt e)).weight fun {x y : Γ.V} (d : x ⟶ y) => treeWord T O d.1) :=
  emptyToCoprod_edge 𝔸 v₀ T O e

/-- `emptyEquivCoprod` sends the generator of a dart of `T` to its coordinate in the free
factor. -/
theorem emptyEquivCoprod_edge_eq_inr_treeWord {e : Γ.E} (he : e ∈ T.darts) :
    emptyEquivCoprod 𝔸 v₀ T hO (edge ∅ e) = inr (treeWord T O e) :=
  emptyToCoprod_edge_of_mem 𝔸 v₀ T hO he

/-- The inverse of `emptyEquivCoprod` sends `a ∈ A_v` to `g_v a g_v⁻¹`, where `g_v` is the
product of the dart generators along the tree path from `v₀` to `v`. -/
@[simp] theorem emptyEquivCoprod_symm_inl_of (v : Γ.V) (a : 𝔸.vertexGroup v) :
    (emptyEquivCoprod 𝔸 v₀ T hO).symm (inl (of T.darts v a)) =
      (T.path v₀ v).weight (fun {x y : Γ.V} (d : x ⟶ y) => edge ∅ d.1) * of ∅ v a *
        ((T.path v₀ v).weight (fun {x y : Γ.V} (d : x ⟶ y) => edge ∅ d.1))⁻¹ := by
  simp [emptyEquivCoprod, coprodToEmpty]

/-- The inverse of `emptyEquivCoprod` sends the generator of a dart `e` of `π₁(𝔸, T)` to
`g_{src e} e g_{tgt e}⁻¹`, where `g_v` is the product of the dart generators along the tree path
from `v₀` to `v`. -/
@[simp] theorem emptyEquivCoprod_symm_inl_edge (e : Γ.E) :
    (emptyEquivCoprod 𝔸 v₀ T hO).symm (inl (edge T.darts e)) =
      (T.path v₀ (Γ.src e)).weight (fun {x y : Γ.V} (d : x ⟶ y) => edge ∅ d.1) * edge ∅ e *
        ((T.path v₀ (Γ.tgt e)).weight (fun {x y : Γ.V} (d : x ⟶ y) => edge ∅ d.1))⁻¹ := by
  simp [emptyEquivCoprod, coprodToEmpty]

/-- The inverse of `emptyEquivCoprod` sends the free generator of a dart of `O ∩ T` to the
generator of that dart. -/
@[simp] theorem emptyEquivCoprod_symm_inr_of (x : ↥(O ∩ T.darts)) :
    (emptyEquivCoprod 𝔸 v₀ T hO).symm (inr (FreeGroup.of x)) = edge ∅ x.1 := by
  simp [emptyEquivCoprod, coprodToEmpty]

/-- `emptyEquivCoprod` sends the vertex group at the base vertex to the first factor. -/
@[simp] theorem emptyEquivCoprod_of_base (a : 𝔸.vertexGroup v₀) :
    emptyEquivCoprod 𝔸 v₀ T hO (of ∅ v₀ a) = inl (of T.darts v₀ a) := by
  simp [emptyEquivCoprod_of]

/-- `emptyEquivCoprod` sends the generator of a dart of `O ∩ T` to its free generator. -/
@[simp] theorem emptyEquivCoprod_edge_of_mem {e : Γ.E} (he : e ∈ O ∩ T.darts) :
    emptyEquivCoprod 𝔸 v₀ T hO (edge ∅ e) = inr (FreeGroup.of ⟨e, he⟩) := by
  simp [emptyEquivCoprod_edge_eq_inr_treeWord 𝔸 v₀ T hO he.2, he]

end TauCeti.GraphOfGroups.π₁Tree
