/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.SpanningTree
import TauCeti.GroupTheory.GraphOfGroups.BaseVertex

/-!
# Change of maximal tree for the fundamental group of a graph of groups

Let `𝔸` be a graph of groups over a Serre graph `Γ`, let `T` and `T'` be spanning trees of `Γ`
and let `v₀` be a vertex. Both `π₁(𝔸, T)` and `π₁(𝔸, T')` are identified with the group
`π₁(𝔸, v₀)` of closed `𝔸`-paths at `v₀`, so composing the two identifications gives an
isomorphism `π₁(𝔸, T) ≃* π₁(𝔸, T')`.

Explicitly, write `w_v ∈ π₁(𝔸, T')` for the product of the dart generators of `π₁(𝔸, T')` along
the `T`-geodesic `[v₀, v]_T`. The isomorphism sends `g ∈ A_v` to `w_v g w_v⁻¹` and the
generator of a dart `e` to `w_{src e} e w_{tgt e}⁻¹`. In particular it carries the image in
`π₁(𝔸, T)` of any subgroup of a vertex group `A_v` (the vertex group itself, or the image
`α_e(A_e)` or `ω_e(A_e)` of an edge group) to the conjugate by `w_v` of its image in `π₁(𝔸, T')`.
Changing the base vertex `v₀` changes the isomorphism by an inner automorphism.

## Main definitions

* `TauCeti.GraphOfGroups.π₁TreeEquiv`: the isomorphism `π₁(𝔸, T) ≃* π₁(𝔸, T')`.

## Main results

* `TauCeti.GraphOfGroups.π₁TreeEquiv_of`, `TauCeti.GraphOfGroups.π₁TreeEquiv_edge`: the
  isomorphism on the generators.
* `TauCeti.GraphOfGroups.π₁TreeEquiv_toπ₁Tree`: the isomorphism on the element read off an
  `𝔸`-path.
* `TauCeti.GraphOfGroups.map_π₁TreeEquiv_map_of`: it carries the image of a subgroup of a vertex
  group to a conjugate of its image.
* `TauCeti.GraphOfGroups.π₁TreeEquiv_self`, `π₁TreeEquiv_symm`, `π₁TreeEquiv_trans`: the
  isomorphisms form a groupoid.
* `TauCeti.GraphOfGroups.π₁TreeEquiv_eq_trans_conj`: the dependence on the base vertex.

## References

* J.-P. Serre, *Trees*, Chapter I, §5.1, Proposition 20.
* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2, Proposition 2.4(3).
-/

public section

universe u v w x

namespace TauCeti.GraphOfGroups

open SerreGraph

variable {Γ : SerreGraph.{u, v}} (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V)
  (T T' T'' : Γ.SpanningTree)

/-- **Change of maximal tree.** For spanning trees `T` and `T'` of `Γ` and a base vertex `v₀`,
the isomorphism `π₁(𝔸, T) ≃* π₁(𝔸, T')` obtained by identifying both groups with the group
`π₁(𝔸, v₀)` of closed `𝔸`-paths at `v₀`. -/
noncomputable def π₁TreeEquiv : π₁Tree 𝔸 T.darts ≃* π₁Tree 𝔸 T'.darts :=
  (π₁Equiv 𝔸 v₀ T).symm.trans (π₁Equiv 𝔸 v₀ T')

/-- The change of maximal tree is compatible with the identifications with `π₁(𝔸, v₀)`. -/
@[simp] theorem π₁TreeEquiv_π₁Equiv (g : π₁ 𝔸 v₀) :
    π₁TreeEquiv 𝔸 v₀ T T' (π₁Equiv 𝔸 v₀ T g) = π₁Equiv 𝔸 v₀ T' g := by
  simp [π₁TreeEquiv]

/-- The change of maximal tree sends the element of `π₁(𝔸, T)` read off an `𝔸`-path `p` from `a`
to `b` to `w_a p w_b⁻¹`, where `p` is read in `π₁(𝔸, T')` and `w_v` is the product of the dart
generators of `π₁(𝔸, T')` along the `T`-geodesic from `v₀` to `v`. -/
@[simp] theorem π₁TreeEquiv_toπ₁Tree {a b : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) :
    π₁TreeEquiv 𝔸 v₀ T T' (p.toπ₁Tree T.darts) =
      (T.path v₀ a).weight (fun {a b : Γ.V} (e : a ⟶ b) => π₁Tree.edge T'.darts e.1) *
        p.toπ₁Tree T'.darts *
        ((T.path v₀ b).weight (fun {a b : Γ.V} (e : a ⟶ b) => π₁Tree.edge T'.darts e.1))⁻¹ := by
  -- Write the tree path back to `v₀` as the reverse of the tree path from `v₀`, which reads as
  -- the inverse; `reverse_path` is removed from the simp set so that this form is kept.
  rw [π₁TreeEquiv, MulEquiv.trans_apply, π₁Equiv_symm_toπ₁Tree, π₁Equiv_mk, ← T.reverse_path v₀ b]
  simp [Prefunctor.mapPath_reverse, mul_assoc, -SpanningTree.reverse_path]

/-- The change of maximal tree sends `g ∈ A_v` to `w_v g w_v⁻¹`, where `w_v` is the product of
the dart generators of `π₁(𝔸, T')` along the `T`-geodesic from `v₀` to `v`. -/
@[simp] theorem π₁TreeEquiv_of (v : Γ.V) (g : 𝔸.vertexGroup v) :
    π₁TreeEquiv 𝔸 v₀ T T' (π₁Tree.of T.darts v g) =
      (T.path v₀ v).weight (fun {a b : Γ.V} (e : a ⟶ b) => π₁Tree.edge T'.darts e.1) *
        π₁Tree.of T'.darts v g *
        ((T.path v₀ v).weight (fun {a b : Γ.V} (e : a ⟶ b) => π₁Tree.edge T'.darts e.1))⁻¹ := by
  simpa using π₁TreeEquiv_toπ₁Tree 𝔸 v₀ T T' (Path.ofVertex g)

/-- The change of maximal tree sends the generator of a dart `e` to `w_{src e} e w_{tgt e}⁻¹`,
where `w_v` is the product of the dart generators of `π₁(𝔸, T')` along the `T`-geodesic from
`v₀` to `v`. -/
@[simp] theorem π₁TreeEquiv_edge (e : Γ.E) :
    π₁TreeEquiv 𝔸 v₀ T T' (π₁Tree.edge T.darts e) =
      (T.path v₀ (Γ.src e)).weight (fun {a b : Γ.V} (d : a ⟶ b) => π₁Tree.edge T'.darts d.1) *
        π₁Tree.edge T'.darts e * ((T.path v₀ (Γ.tgt e)).weight
          fun {a b : Γ.V} (d : a ⟶ b) => π₁Tree.edge T'.darts d.1)⁻¹ := by
  simpa using π₁TreeEquiv_toπ₁Tree 𝔸 v₀ T T' (Path.ofDart (Γ.dart e))

/-- The change of maximal tree restricted to a vertex group `A_v` is the canonical homomorphism
`π₁Tree.of` of `A_v` into `π₁(𝔸, T')` followed by conjugation by `w_v`. -/
@[simp] theorem π₁TreeEquiv_comp_of (v : Γ.V) :
    (π₁TreeEquiv 𝔸 v₀ T T' : π₁Tree 𝔸 T.darts →* π₁Tree 𝔸 T'.darts).comp (π₁Tree.of T.darts v) =
      (MulAut.conj ((T.path v₀ v).weight
          (fun {a b : Γ.V} (e : a ⟶ b) => π₁Tree.edge (𝔸 := 𝔸) T'.darts e.1)) :
          π₁Tree 𝔸 T'.darts →* π₁Tree 𝔸 T'.darts).comp (π₁Tree.of T'.darts v) := by
  ext g
  simp

/-- **The change of maximal tree carries vertex groups and edge groups to conjugates.** The
image in `π₁(𝔸, T)` of a subgroup `H` of a vertex group `A_v` is carried to the conjugate of its
image in `π₁(𝔸, T')` by `w_v`, the product of the dart generators of `π₁(𝔸, T')` along the
`T`-geodesic from `v₀` to `v`. With `H = ⊤` this is the image of the vertex group, and with `H`
the image of an edge group under `α_e` or `ω_e` it is an edge group image. -/
theorem map_π₁TreeEquiv_map_of (v : Γ.V) (H : Subgroup (𝔸.vertexGroup v)) :
    (H.map (π₁Tree.of T.darts v)).map
        (π₁TreeEquiv 𝔸 v₀ T T' : π₁Tree 𝔸 T.darts →* π₁Tree 𝔸 T'.darts) =
      (H.map (π₁Tree.of T'.darts v)).map
        (MulAut.conj ((T.path v₀ v).weight
          (fun {a b : Γ.V} (e : a ⟶ b) => π₁Tree.edge (𝔸 := 𝔸) T'.darts e.1)) :
          π₁Tree 𝔸 T'.darts →* π₁Tree 𝔸 T'.darts) := by
  simp [Subgroup.map_map]

/-- Changing to the same maximal tree is the identity. -/
@[simp] theorem π₁TreeEquiv_self : π₁TreeEquiv 𝔸 v₀ T T = MulEquiv.refl _ := by
  simp [π₁TreeEquiv]

/-- The inverse of the change from `T` to `T'` is the change from `T'` to `T`. -/
@[simp] theorem π₁TreeEquiv_symm : (π₁TreeEquiv 𝔸 v₀ T T').symm = π₁TreeEquiv 𝔸 v₀ T' T := by
  ext
  simp [π₁TreeEquiv]

/-- Changing from `T` to `T'` and then from `T'` to `T''` is changing from `T` to `T''`. -/
@[simp] theorem π₁TreeEquiv_trans :
    (π₁TreeEquiv 𝔸 v₀ T T').trans (π₁TreeEquiv 𝔸 v₀ T' T'') = π₁TreeEquiv 𝔸 v₀ T T'' := by
  ext
  simp [π₁TreeEquiv]

/-- Changing the base vertex from `v₀` to `v₁` composes the change of maximal tree with the
inner automorphism of `π₁(𝔸, T')` by the inverse of the product of the dart generators of
`π₁(𝔸, T')` along the `T`-geodesic from `v₀` to `v₁`. -/
theorem π₁TreeEquiv_eq_trans_conj (v₁ : Γ.V) :
    π₁TreeEquiv 𝔸 v₁ T T' = (π₁TreeEquiv 𝔸 v₀ T T').trans (MulAut.conj
      ((T.path v₀ v₁).weight fun {a b : Γ.V} (e : a ⟶ b) => π₁Tree.edge T'.darts e.1)⁻¹) := by
  -- Compare the two base vertices through the change of base vertex along the tree path from
  -- `v₀` to `v₁`, which is read as `1` in `π₁(𝔸, T)` and as the conjugator in `π₁(𝔸, T')`.
  ext x
  obtain ⟨y, rfl⟩ := (π₁Equiv 𝔸 v₀ T).surjective x
  have h : π₁Equiv 𝔸 v₀ T y =
      π₁Equiv 𝔸 v₁ T (π₁.mulEquivOfPath ((dartPrefunctor 𝔸).mapPath (T.path v₀ v₁)) y) := by
    simp [π₁Equiv_apply]
  rw [MulEquiv.trans_apply, π₁TreeEquiv_π₁Equiv, h, π₁TreeEquiv_π₁Equiv]
  simp [π₁Equiv_apply]

end TauCeti.GraphOfGroups
