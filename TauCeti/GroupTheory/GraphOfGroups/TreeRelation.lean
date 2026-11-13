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
generator of a dart `e ∈ O ∩ T` to the generator of `e` in `π₁(𝔸, ∅)`.

## Main definitions

* `TauCeti.GraphOfGroups.π₁Tree.emptyEquivCoprod`: the isomorphism
  `π₁(𝔸, ∅) ≃* π₁(𝔸, T) ∗ F(O ∩ T)`.

## Main results

* `TauCeti.GraphOfGroups.π₁Tree.emptyEquivCoprod_symm_inl_of`,
  `TauCeti.GraphOfGroups.π₁Tree.emptyEquivCoprod_symm_inl_edge`,
  `TauCeti.GraphOfGroups.π₁Tree.emptyEquivCoprod_symm_inr_of`: the inverse isomorphism on the
  generators.
* `TauCeti.GraphOfGroups.π₁Tree.emptyEquivCoprod_of_base`,
  `TauCeti.GraphOfGroups.π₁Tree.emptyEquivCoprod_edge_of_mem`: the base vertex group goes to
  the first factor, and a positively oriented tree dart to its free generator.

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

/-! ### Conjugating the defining families -/

section conjLift

variable {𝔸} {H : Type*} [Group H] {S : Set Γ.E}

/-- Conjugating a family `(φ_v, h_e)` that satisfies the reversal and edge relations by elements
`g_v ∈ H`, as `g_v φ_v g_v⁻¹` and `g_{src e} h_e g_{tgt e}⁻¹`, gives a homomorphism out of
`π₁(𝔸, S)` as soon as the conjugated dart elements are trivial on `S`. -/
private def conjLift (g : Γ.V → H) (φ : ∀ v, 𝔸.vertexGroup v →* H) (h : Γ.E → H)
    (hS : ∀ e ∈ S, g (Γ.src e) * h e * (g (Γ.tgt e))⁻¹ = 1) (hrev : ∀ e, h (Γ.rev e) = (h e)⁻¹)
    (hrel : ∀ e c, h e * φ (Γ.tgt e) (𝔸.ω e c) * (h e)⁻¹ = φ (Γ.src e) (𝔸.α e c)) :
    π₁Tree 𝔸 S →* H :=
  lift (fun v => (MulAut.conj (g v)).toMonoidHom.comp (φ v))
    (fun e => g (Γ.src e) * h e * (g (Γ.tgt e))⁻¹) hS (fun e => by simp [hrev, mul_assoc])
    (fun e c => by simp [← hrel e c, mul_assoc])

variable (g : Γ.V → H) (φ : ∀ v, 𝔸.vertexGroup v →* H) (h : Γ.E → H)
  (hS : ∀ e ∈ S, g (Γ.src e) * h e * (g (Γ.tgt e))⁻¹ = 1) (hrev : ∀ e, h (Γ.rev e) = (h e)⁻¹)
  (hrel : ∀ e c, h e * φ (Γ.tgt e) (𝔸.ω e c) * (h e)⁻¹ = φ (Γ.src e) (𝔸.α e c))

private theorem conjLift_of (v : Γ.V) (a : 𝔸.vertexGroup v) :
    conjLift g φ h hS hrev hrel (of S v a) = g v * φ v a * (g v)⁻¹ := by
  simp [conjLift]

private theorem conjLift_edge (e : Γ.E) :
    conjLift g φ h hS hrev hrel (edge S e) = g (Γ.src e) * h e * (g (Γ.tgt e))⁻¹ := by
  simp [conjLift]

end conjLift

/-! ### Coordinates of tree darts -/

variable (O) in
/-- The signed coordinate of a dart in the free group on the positively oriented darts of the
spanning tree `T`: the generator `e` if `e ∈ O ∩ T`, the inverse of the generator `rev e` if
`rev e ∈ O ∩ T`, and `1` for a dart outside `T`. -/
private noncomputable def treeWord (e : Γ.E) : FreeGroup ↥(O ∩ T.darts) :=
  FreeGroup.map (Set.inclusion Set.sdiff_compl.subset) (dartWord O T.dartsᶜ e)

include hO in
private theorem treeWord_rev (e : Γ.E) : treeWord T O (Γ.rev e) = (treeWord T O e)⁻¹ := by
  simp [treeWord, dartWord_rev hO]

private theorem treeWord_of_mem {e : Γ.E} (he : e ∈ O ∩ T.darts) :
    treeWord T O e = FreeGroup.of ⟨e, he⟩ := by
  simp [treeWord, dartWord_of_mem (show e ∈ O \ T.dartsᶜ from ⟨he.1, not_not_intro he.2⟩)]

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
private noncomputable def ofCoprod : π₁Tree 𝔸 T.darts ∗ FreeGroup ↥(O ∩ T.darts) →* π₁Tree 𝔸 ∅ :=
  Monoid.Coprod.lift
    (conjLift (fun v => (T.path v₀ v).weight fun {x y : Γ.V} (d : x ⟶ y) => edge ∅ d.1)
      (of ∅) (edge ∅)
      (fun e he => by simp [T.weight_path_tgt edge_rev v₀ he])
      edge_rev edge_mul_of_ω_mul_edge_inv)
    (FreeGroup.lift fun x => edge ∅ x.1)

/-- The homomorphism `π₁(𝔸, ∅) →* π₁(𝔸, T) ∗ F(O ∩ T)`, conjugating along the coordinates of the
tree paths from `v₀`. -/
private noncomputable def toCoprod : π₁Tree 𝔸 ∅ →* π₁Tree 𝔸 T.darts ∗ FreeGroup ↥(O ∩ T.darts) :=
  conjLift
    (fun v => (inr ((T.path v₀ v).weight fun {x y : Γ.V} (d : x ⟶ y) => treeWord T O d.1))⁻¹)
    (fun v => inl.comp (of T.darts v)) (fun e => inl (edge T.darts e))
    (fun _ he => (Set.notMem_empty _ he).elim) (fun e => by simp)
    (fun e c => by simp only [MonoidHom.comp_apply, ← map_mul, ← map_inv,
      edge_mul_of_ω_mul_edge_inv])

private theorem toCoprod_of (v : Γ.V) (a : 𝔸.vertexGroup v) :
    toCoprod 𝔸 v₀ T O (of ∅ v a) =
      (inr ((T.path v₀ v).weight fun {x y : Γ.V} (d : x ⟶ y) => treeWord T O d.1))⁻¹ *
        inl (of T.darts v a) *
          inr ((T.path v₀ v).weight fun {x y : Γ.V} (d : x ⟶ y) => treeWord T O d.1) := by
  simp [toCoprod, conjLift_of]

private theorem toCoprod_edge (e : Γ.E) :
    toCoprod 𝔸 v₀ T O (edge ∅ e) =
      (inr ((T.path v₀ (Γ.src e)).weight fun {x y : Γ.V} (d : x ⟶ y) => treeWord T O d.1))⁻¹ *
        inl (edge T.darts e) *
          inr ((T.path v₀ (Γ.tgt e)).weight fun {x y : Γ.V} (d : x ⟶ y) => treeWord T O d.1) := by
  simp [toCoprod, conjLift_edge]

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
private theorem toCoprod_edge_of_mem {e : Γ.E} (he : e ∈ T.darts) :
    toCoprod 𝔸 v₀ T O (edge ∅ e) = inr (treeWord T O e) := by
  simp [toCoprod_edge, edge_eq_one he, T.weight_path_tgt (treeWord_rev T hO) v₀ he]

include hO in
/-- The homomorphism sends the product of dart generators along a tree path to its coordinate. -/
private theorem toCoprod_weight (v : Γ.V) :
    toCoprod 𝔸 v₀ T O ((T.path v₀ v).weight fun {x y : Γ.V} (d : x ⟶ y) => edge ∅ d.1) =
      inr ((T.path v₀ v).weight fun {x y : Γ.V} (d : x ⟶ y) => treeWord T O d.1) := by
  rw [Quiver.Path.map_weight, Quiver.Path.map_weight]
  exact T.weight_path_congr (fun e he => toCoprod_edge_of_mem 𝔸 v₀ T hO he) v₀ v

include hO in
private theorem ofCoprod_comp_toCoprod :
    (ofCoprod 𝔸 v₀ T O).comp (toCoprod 𝔸 v₀ T O) = MonoidHom.id _ :=
  hom_ext (fun v => MonoidHom.ext fun a => by
      simp [toCoprod_of, ofCoprod, conjLift_of, lift_weight_treeWord 𝔸 v₀ T hO, mul_assoc])
    fun e => by
      simp [toCoprod_edge, ofCoprod, conjLift_edge, lift_weight_treeWord 𝔸 v₀ T hO, mul_assoc]

include hO in
private theorem toCoprod_comp_ofCoprod :
    (toCoprod 𝔸 v₀ T O).comp (ofCoprod 𝔸 v₀ T O) = MonoidHom.id _ :=
  Monoid.Coprod.hom_ext
    (hom_ext (fun v => MonoidHom.ext fun a => by
        simp [toCoprod_of, ofCoprod, conjLift_of, toCoprod_weight 𝔸 v₀ T hO, mul_assoc])
      fun e => by
        simp [toCoprod_edge, ofCoprod, conjLift_edge, toCoprod_weight 𝔸 v₀ T hO, mul_assoc])
    (FreeGroup.ext_hom _ _ fun x => by
      simp [ofCoprod, toCoprod_edge_of_mem 𝔸 v₀ T hO x.2.2, treeWord_of_mem T x.2])

/-- Omitting the tree relations adds a free factor: for a spanning tree `T`, a base vertex `v₀`
and an orientation `O` of `Γ`, the group `π₁(𝔸, ∅)`, presented without the relations `e = 1` for
the darts `e` of `T`, is the free product of `π₁(𝔸, T)` and the free group on the positively
oriented darts of `T`. The inverse sends `a ∈ A_v` to `g_v a g_v⁻¹`, where `g_v` is the product of
the dart generators along the tree path from `v₀` to `v`. -/
noncomputable def emptyEquivCoprod : π₁Tree 𝔸 ∅ ≃* π₁Tree 𝔸 T.darts ∗ FreeGroup ↥(O ∩ T.darts) :=
  MonoidHom.toMulEquiv (toCoprod 𝔸 v₀ T O) (ofCoprod 𝔸 v₀ T O)
    (ofCoprod_comp_toCoprod 𝔸 v₀ T hO) (toCoprod_comp_ofCoprod 𝔸 v₀ T hO)

/-- The inverse of `emptyEquivCoprod` sends `a ∈ A_v` to `g_v a g_v⁻¹`, where `g_v` is the
product of the dart generators along the tree path from `v₀` to `v`. -/
@[simp] theorem emptyEquivCoprod_symm_inl_of (v : Γ.V) (a : 𝔸.vertexGroup v) :
    (emptyEquivCoprod 𝔸 v₀ T hO).symm (inl (of T.darts v a)) =
      (T.path v₀ v).weight (fun {x y : Γ.V} (d : x ⟶ y) => edge ∅ d.1) * of ∅ v a *
        ((T.path v₀ v).weight (fun {x y : Γ.V} (d : x ⟶ y) => edge ∅ d.1))⁻¹ := by
  simp [emptyEquivCoprod, ofCoprod, conjLift_of]

/-- The inverse of `emptyEquivCoprod` sends the generator of a dart `e` of `π₁(𝔸, T)` to
`g_{src e} e g_{tgt e}⁻¹`, where `g_v` is the product of the dart generators along the tree path
from `v₀` to `v`. -/
@[simp] theorem emptyEquivCoprod_symm_inl_edge (e : Γ.E) :
    (emptyEquivCoprod 𝔸 v₀ T hO).symm (inl (edge T.darts e)) =
      (T.path v₀ (Γ.src e)).weight (fun {x y : Γ.V} (d : x ⟶ y) => edge ∅ d.1) * edge ∅ e *
        ((T.path v₀ (Γ.tgt e)).weight (fun {x y : Γ.V} (d : x ⟶ y) => edge ∅ d.1))⁻¹ := by
  simp [emptyEquivCoprod, ofCoprod, conjLift_edge]

/-- The inverse of `emptyEquivCoprod` sends the free generator of a dart of `O ∩ T` to the
generator of that dart. -/
@[simp] theorem emptyEquivCoprod_symm_inr_of (x : ↥(O ∩ T.darts)) :
    (emptyEquivCoprod 𝔸 v₀ T hO).symm (inr (FreeGroup.of x)) = edge ∅ x.1 := by
  simp [emptyEquivCoprod, ofCoprod]

/-- `emptyEquivCoprod` sends the vertex group at the base vertex to the first factor. -/
@[simp] theorem emptyEquivCoprod_of_base (a : 𝔸.vertexGroup v₀) :
    emptyEquivCoprod 𝔸 v₀ T hO (of ∅ v₀ a) = inl (of T.darts v₀ a) := by
  simp [emptyEquivCoprod, toCoprod_of]

/-- `emptyEquivCoprod` sends the generator of a dart of `O ∩ T` to its free generator. -/
@[simp] theorem emptyEquivCoprod_edge_of_mem {e : Γ.E} (he : e ∈ O ∩ T.darts) :
    emptyEquivCoprod 𝔸 v₀ T hO (edge ∅ e) = inr (FreeGroup.of ⟨e, he⟩) := by
  simp [emptyEquivCoprod, toCoprod_edge_of_mem 𝔸 v₀ T hO he.2, treeWord_of_mem T he]

end TauCeti.GraphOfGroups.π₁Tree
