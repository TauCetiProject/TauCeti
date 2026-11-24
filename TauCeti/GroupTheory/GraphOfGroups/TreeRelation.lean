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
darts of `O ∩ T` generate a free factor of rank the number of geometric edges of `T`. (That no
dart generator is trivial in `π₁(𝔸, ∅)`, and that the darts of `O` freely generate a subgroup,
holds for every graph of groups: `TauCeti.GraphOfGroups.π₁Tree.edge_empty_ne_one` and
`TauCeti.GraphOfGroups.π₁Tree.freeGroupLift_edge_injective`.)

The isomorphism depends on a base vertex `v₀`. Write `g_v ∈ π₁(𝔸, ∅)` for the product of the dart
generators along the tree path from `v₀` to `v`. The inverse isomorphism sends `a ∈ A_v` to
`g_v a g_v⁻¹`, the generator of a dart `e` of `π₁(𝔸, T)` to `g_{src e} e g_{tgt e}⁻¹`, and the free
generator of a dart `e ∈ O ∩ T` to the generator of `e` in `π₁(𝔸, ∅)`. Conversely, write
`t_v ∈ F(O ∩ T)` for the product of the signed coordinates of the darts along the same tree path.
The isomorphism sends `a ∈ A_v` to `t_v⁻¹ a t_v` and the generator of a dart `e` to
`t_{src e}⁻¹ e t_{tgt e}`; for a dart of `T` this is its signed coordinate in `F(O ∩ T)`.

## Main definitions

* `TauCeti.GraphOfGroups.π₁Tree.treeWord`: the signed coordinate of a dart in the free group on
  the darts of `O ∩ T`.
* `TauCeti.GraphOfGroups.π₁Tree.emptyEquivCoprod`: the isomorphism
  `π₁(𝔸, ∅) ≃* π₁(𝔸, T) ∗ F(O ∩ T)`.

## Main results

* `TauCeti.GraphOfGroups.π₁Tree.emptyEquivCoprod_of`,
  `TauCeti.GraphOfGroups.π₁Tree.emptyEquivCoprod_edge`: the isomorphism on the generators.
* `TauCeti.GraphOfGroups.π₁Tree.emptyEquivCoprod_of_self`,
  `TauCeti.GraphOfGroups.π₁Tree.emptyEquivCoprod_edge_of_mem`: the base vertex group goes to
  the first factor, and a positively oriented tree dart to its free generator.
* `TauCeti.GraphOfGroups.π₁Tree.emptyEquivCoprod_weight`: the isomorphism sends the product of
  the dart generators along a tree path to the product of their coordinates; in particular `g_v`
  goes to `t_v`.
* `TauCeti.GraphOfGroups.π₁Tree.emptyEquivCoprod_symm_inl_of`,
  `TauCeti.GraphOfGroups.π₁Tree.emptyEquivCoprod_symm_inl_edge`,
  `TauCeti.GraphOfGroups.π₁Tree.emptyEquivCoprod_symm_inr`: the inverse isomorphism on the
  generators and on the free factor.

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
  {T : Γ.SpanningTree} {O : Set Γ.E} (hO : Γ.IsOrientation O)

/-! ### Coordinates of tree darts -/

variable (T O) in
/-- The signed coordinate of a dart in the free group on the darts of `O ∩ T`: the generator `e`
if `e ∈ O ∩ T`, otherwise the inverse of the generator `rev e` if `rev e ∈ O ∩ T`, and `1` if
neither holds. For an orientation `O` of `Γ` the three cases are `e ∈ O ∩ T`, `rev e ∈ O ∩ T` and
`e ∉ T`, so a product of these coordinates along a path records the darts of `T` it crosses, with
signs. -/
noncomputable def treeWord (e : Γ.E) : FreeGroup ↥(O ∩ T.darts) :=
  FreeGroup.map (Set.inclusion Set.sdiff_compl.subset) (dartWord O T.dartsᶜ e)

theorem treeWord_def (e : Γ.E) :
    treeWord T O e = FreeGroup.map (Set.inclusion Set.sdiff_compl.subset) (dartWord O T.dartsᶜ e) :=
  (rfl)

@[simp] theorem treeWord_of_mem {e : Γ.E} (he : e ∈ O ∩ T.darts) :
    treeWord T O e = FreeGroup.of ⟨e, he⟩ := by
  simp [treeWord, dartWord_of_mem (Set.sdiff_compl.superset he)]

@[simp] theorem treeWord_of_rev_mem {e : Γ.E} (he : e ∉ O ∩ T.darts)
    (hr : Γ.rev e ∈ O ∩ T.darts) : treeWord T O e = (FreeGroup.of ⟨Γ.rev e, hr⟩)⁻¹ := by
  simp [treeWord, dartWord_of_rev_mem (fun h => he (Set.sdiff_compl.subset h))
    (Set.sdiff_compl.superset hr)]

@[simp] theorem treeWord_of_notMem {e : Γ.E} (he : e ∉ O ∩ T.darts)
    (hr : Γ.rev e ∉ O ∩ T.darts) : treeWord T O e = 1 := by
  simp [treeWord, dartWord_of_notMem (O := O) (T := T.dartsᶜ) (e := e) (by simpa using he)
    (by simpa using hr)]

/-- A dart outside the spanning tree has trivial coordinate. -/
@[simp] theorem treeWord_of_notMem_darts {e : Γ.E} (he : e ∉ T.darts) : treeWord T O e = 1 :=
  treeWord_of_notMem (fun h => he h.2) fun h => he (Γ.rev_rev e ▸ T.rev_mem _ h.2)

/-- Reversing a dart inverts its coordinate, as soon as `O` contains no dart together with its
reverse. -/
@[simp] theorem treeWord_rev (hO : ∀ e ∈ O, Γ.rev e ∉ O) (e : Γ.E) :
    treeWord T O (Γ.rev e) = (treeWord T O e)⁻¹ := by
  simp [treeWord, dartWord_rev hO]

/-- Evaluating the coordinates of the darts along a tree path at a dart weight compatible with
reversal on `T` gives the weight of the path, as soon as `O` contains a dart of every geometric
edge of `T`. -/
theorem freeGroupLift_weight_treeWord {H : Type*} [Group H] {wt : Γ.E → H}
    (hO : ∀ e ∈ T.darts, e ∈ O ∨ Γ.rev e ∈ O) (hwt : ∀ e ∈ T.darts, wt (Γ.rev e) = (wt e)⁻¹)
    (a b : Γ.V) :
    FreeGroup.lift (fun x : ↥(O ∩ T.darts) => wt x.val)
        ((T.path a b).weight fun {x y : Γ.V} (d : x ⟶ y) => treeWord T O d.val) =
      (T.path a b).weight fun {x y : Γ.V} (d : x ⟶ y) => wt d.val := by
  -- `treeWord` is the dart word for `O \ Tᶜ = O ∩ T`, read in `F(O ∩ T)`.
  have h (e : Γ.E) (he : e ∈ T.darts) :
      FreeGroup.lift (fun x : ↥(O ∩ T.darts) => wt x.val) (treeWord T O e) = wt e := by
    rw [treeWord_def]
    refine (FreeGroup.lift_unique ((FreeGroup.lift _).comp (FreeGroup.map _)) fun _ => by
      simp).trans (freeGroupLift_dartWord (hwt e he) ?_)
    rw [Set.sdiff_compl]
    exact (hO e he).imp (⟨·, he⟩) fun hr => .inl ⟨hr, T.rev_mem e he⟩
  rw [Quiver.Path.map_weight]
  exact T.weight_path_congr h a b

/-! ### The two homomorphisms -/

variable (T O)

/-- The homomorphism `π₁(𝔸, T) ∗ F(O ∩ T) →* π₁(𝔸, ∅)`, conjugating along the tree paths from
`v₀`. -/
private noncomputable def coprodToEmpty :
    π₁Tree 𝔸 T.darts ∗ FreeGroup ↥(O ∩ T.darts) →* π₁Tree 𝔸 ∅ :=
  Monoid.Coprod.lift
    (conjLift (fun v => (T.path v₀ v).weight fun {x y : Γ.V} (d : x ⟶ y) => edge ∅ d.val)
      (of ∅) (edge ∅)
      (fun e he => by simp [T.weight_path_tgt v₀ he (edge_rev e)])
      edge_rev edge_mul_of_ω_mul_edge_inv)
    (FreeGroup.lift fun x => edge ∅ x.val)

/-- The homomorphism `π₁(𝔸, ∅) →* π₁(𝔸, T) ∗ F(O ∩ T)`, conjugating along the coordinates of the
tree paths from `v₀`. -/
private noncomputable def emptyToCoprod :
    π₁Tree 𝔸 ∅ →* π₁Tree 𝔸 T.darts ∗ FreeGroup ↥(O ∩ T.darts) :=
  conjLift
    (fun v => (inr ((T.path v₀ v).weight fun {x y : Γ.V} (d : x ⟶ y) => treeWord T O d.val))⁻¹)
    (fun v => inl.comp (of T.darts v)) (fun e => inl (edge T.darts e))
    (fun _ he => (Set.notMem_empty _ he).elim) (fun e => by simp)
    (fun e c => by simp only [MonoidHom.comp_apply, ← map_mul, ← map_inv,
      edge_mul_of_ω_mul_edge_inv])

variable {O}

include hO in
/-- On a tree dart, the homomorphism takes values in the free factor. -/
private theorem emptyToCoprod_edge_of_mem {e : Γ.E} (he : e ∈ T.darts) :
    emptyToCoprod 𝔸 v₀ T O (edge ∅ e) = inr (treeWord T O e) := by
  simp [emptyToCoprod, edge_eq_one he,
    T.weight_path_tgt v₀ he (treeWord_rev (hO.rev_notMem_of_mem _) e)]

include hO in
/-- The homomorphism sends the product of dart generators along a tree path to its coordinate. -/
private theorem emptyToCoprod_weight (a b : Γ.V) :
    emptyToCoprod 𝔸 v₀ T O ((T.path a b).weight fun {x y : Γ.V} (d : x ⟶ y) => edge ∅ d.val) =
      inr ((T.path a b).weight fun {x y : Γ.V} (d : x ⟶ y) => treeWord T O d.val) := by
  rw [Quiver.Path.map_weight, Quiver.Path.map_weight]
  exact T.weight_path_congr (fun e he => emptyToCoprod_edge_of_mem 𝔸 v₀ T hO he) a b

include hO in
private theorem coprodToEmpty_comp_emptyToCoprod :
    (coprodToEmpty 𝔸 v₀ T O).comp (emptyToCoprod 𝔸 v₀ T O) = MonoidHom.id _ := by
  have h := freeGroupLift_weight_treeWord (T := T) (wt := edge (𝔸 := 𝔸) ∅)
    (fun e _ => hO.mem_or_rev_mem e) (fun e _ => edge_rev e) v₀
  refine hom_ext (fun v => MonoidHom.ext fun a => ?_) fun e => ?_ <;>
    simp [emptyToCoprod, coprodToEmpty, h, mul_assoc]

include hO in
private theorem emptyToCoprod_comp_coprodToEmpty :
    (emptyToCoprod 𝔸 v₀ T O).comp (coprodToEmpty 𝔸 v₀ T O) = MonoidHom.id _ :=
  Monoid.Coprod.hom_ext
    (hom_ext (fun v => MonoidHom.ext fun a => by
        simp [coprodToEmpty, emptyToCoprod_weight 𝔸 v₀ T hO]
        simp [emptyToCoprod, mul_assoc])
      fun e => by
        simp [coprodToEmpty, emptyToCoprod_weight 𝔸 v₀ T hO]
        simp [emptyToCoprod, mul_assoc])
    (FreeGroup.ext_hom _ _ fun x => by
      simp [coprodToEmpty, emptyToCoprod_edge_of_mem 𝔸 v₀ T hO x.property.2])

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
@[simp] theorem emptyEquivCoprod_of (v : Γ.V) (a : 𝔸.vertexGroup v) :
    emptyEquivCoprod 𝔸 v₀ T hO (of ∅ v a) =
      (inr ((T.path v₀ v).weight fun {x y : Γ.V} (d : x ⟶ y) => treeWord T O d.val))⁻¹ *
        inl (of T.darts v a) *
          inr ((T.path v₀ v).weight fun {x y : Γ.V} (d : x ⟶ y) => treeWord T O d.val) := by
  simp [emptyEquivCoprod, emptyToCoprod]

/-- `emptyEquivCoprod` sends the generator of a dart `e` to `t_{src e}⁻¹ e t_{tgt e}`, where
`t_v ∈ F(O ∩ T)` is the product of the coordinates `treeWord` of the darts along the tree path
from `v₀` to `v`. -/
theorem emptyEquivCoprod_edge (e : Γ.E) :
    emptyEquivCoprod 𝔸 v₀ T hO (edge ∅ e) =
      (inr ((T.path v₀ (Γ.src e)).weight fun {x y : Γ.V} (d : x ⟶ y) => treeWord T O d.val))⁻¹ *
        inl (edge T.darts e) *
          inr ((T.path v₀ (Γ.tgt e)).weight fun {x y : Γ.V} (d : x ⟶ y) => treeWord T O d.val) := by
  simp [emptyEquivCoprod, emptyToCoprod]

/-- `emptyEquivCoprod` sends the generator of a dart of `T` to its coordinate in the free
factor. -/
theorem emptyEquivCoprod_edge_eq_inr_treeWord {e : Γ.E} (he : e ∈ T.darts) :
    emptyEquivCoprod 𝔸 v₀ T hO (edge ∅ e) = inr (treeWord T O e) :=
  emptyToCoprod_edge_of_mem 𝔸 v₀ T hO he

/-- `emptyEquivCoprod` sends the product of the dart generators along the tree path from `a` to
`b` to the product of the coordinates of its darts in the free factor; for `a = v₀` this sends
`g_b` to `t_b`. -/
@[simp] theorem emptyEquivCoprod_weight (a b : Γ.V) :
    emptyEquivCoprod 𝔸 v₀ T hO ((T.path a b).weight fun {x y : Γ.V} (d : x ⟶ y) => edge ∅ d.val) =
      inr ((T.path a b).weight fun {x y : Γ.V} (d : x ⟶ y) => treeWord T O d.val) :=
  emptyToCoprod_weight 𝔸 v₀ T hO a b

/-- The inverse of `emptyEquivCoprod` sends `a ∈ A_v` to `g_v a g_v⁻¹`, where `g_v` is the
product of the dart generators along the tree path from `v₀` to `v`. -/
@[simp] theorem emptyEquivCoprod_symm_inl_of (v : Γ.V) (a : 𝔸.vertexGroup v) :
    (emptyEquivCoprod 𝔸 v₀ T hO).symm (inl (of T.darts v a)) =
      (T.path v₀ v).weight (fun {x y : Γ.V} (d : x ⟶ y) => edge ∅ d.val) * of ∅ v a *
        ((T.path v₀ v).weight (fun {x y : Γ.V} (d : x ⟶ y) => edge ∅ d.val))⁻¹ := by
  simp [emptyEquivCoprod, coprodToEmpty]

/-- The inverse of `emptyEquivCoprod` sends the generator of a dart `e` of `π₁(𝔸, T)` to
`g_{src e} e g_{tgt e}⁻¹`, where `g_v` is the product of the dart generators along the tree path
from `v₀` to `v`. -/
@[simp] theorem emptyEquivCoprod_symm_inl_edge (e : Γ.E) :
    (emptyEquivCoprod 𝔸 v₀ T hO).symm (inl (edge T.darts e)) =
      (T.path v₀ (Γ.src e)).weight (fun {x y : Γ.V} (d : x ⟶ y) => edge ∅ d.val) * edge ∅ e *
        ((T.path v₀ (Γ.tgt e)).weight (fun {x y : Γ.V} (d : x ⟶ y) => edge ∅ d.val))⁻¹ := by
  simp [emptyEquivCoprod, coprodToEmpty]

/-- The inverse of `emptyEquivCoprod` sends a word `w` of the free factor to `w` evaluated at the
generators of the darts of `O ∩ T`. -/
@[simp] theorem emptyEquivCoprod_symm_inr (w : FreeGroup ↥(O ∩ T.darts)) :
    (emptyEquivCoprod 𝔸 v₀ T hO).symm (inr w) = FreeGroup.lift (fun x => edge ∅ x.val) w := by
  simp [emptyEquivCoprod, coprodToEmpty]

@[simp] theorem emptyEquivCoprod_symm_comp_inr :
    ((emptyEquivCoprod 𝔸 v₀ T hO).symm :
        π₁Tree 𝔸 T.darts ∗ FreeGroup ↥(O ∩ T.darts) →* π₁Tree 𝔸 ∅).comp inr =
      FreeGroup.lift fun x => edge ∅ x.val := by
  ext
  simp

/-- `emptyEquivCoprod` sends the vertex group at the base vertex to the first factor. -/
theorem emptyEquivCoprod_of_self (a : 𝔸.vertexGroup v₀) :
    emptyEquivCoprod 𝔸 v₀ T hO (of ∅ v₀ a) = inl (of T.darts v₀ a) := by
  simp

/-- `emptyEquivCoprod` sends the generator of a dart of `O ∩ T` to its free generator. -/
@[simp] theorem emptyEquivCoprod_edge_of_mem {e : Γ.E} (he : e ∈ O ∩ T.darts) :
    emptyEquivCoprod 𝔸 v₀ T hO (edge ∅ e) = inr (FreeGroup.of ⟨e, he⟩) := by
  simp [emptyEquivCoprod_edge_eq_inr_treeWord 𝔸 v₀ T hO he.2, he]

end TauCeti.GraphOfGroups.π₁Tree
