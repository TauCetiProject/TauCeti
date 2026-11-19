/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GTree.Lifting
public import TauCeti.GroupTheory.GraphOfGroups.SpanningTree

/-!
# The quotient graph of groups of a group acting on a tree

Let a group `G` act on a tree `T` without inversions, with quotient graph `B = T / G`, and let `D`
be a lifting of `B` (`GTree.Lifting`): a spanning tree `S` of `B`, a lift `x_v` of every vertex `v`
and a lift `d_y` of every dart `y` of `B` issuing from the lift of its source, and elements
`t_y ∈ G` with `tgt d_y = t_y • x_{tgt y}`, `t_{rev y} = t_y⁻¹` and `t_y = 1` on `S`.

The quotient graph of groups `𝔹 = D.graphOfGroups` over `B` has the stabilizer `G_{x_v}` of the
lifted vertex as vertex group at `v`, and the stabilizer `G_{d_y}` of the lift of the chosen dart
`y` (`SerreGraph.GeomEdge.out`) of a geometric edge as its edge group. For that chosen dart, `α_y`
is the inclusion `G_{d_y} ≤ G_{src d_y}` and `ω_y(c) = t_y⁻¹ c t_y`, which lies in the stabilizer of
`t_y⁻¹ • tgt d_y = x_{tgt y}`, the lift of the target of `y`; for the other dart `rev y` the two
maps are exchanged. For every dart `y` of `B`, whether chosen or not, the image of `α_y` is
`G_{d_y}` and the image of `ω_y` is the stabilizer of the lift of `rev y`, and
`t_y ω_y(c) t_y⁻¹ = α_y(c)` in `G`.

Hence sending each vertex group to `G` by the inclusion and each dart `y` to `t_y` respects the
defining relations of `π₁(𝔹, S)`, and defines a homomorphism `π₁(𝔹, S) →* G`
(`GTree.Lifting.π₁TreeHom`), and with `π₁(𝔹, v) ≃* π₁(𝔹, S)` a homomorphism `π₁(𝔹, v) →* G` at
every vertex `v` (`GTree.Lifting.π₁Hom`). Since the stabilizers of the lifted vertices and the
elements `t_y` generate `G` (`GTree.Lifting.iSup_stabilizer_sup_closure_range_twist_eq_top`),
these homomorphisms are surjective. They are also injective, by the structure theorem of Bass–Serre
theory (`TauCeti.GroupTheory.GTree.StructureTheorem`), which compares `T` with the Bass–Serre tree
of `𝔹`.

## Main definitions

* `TauCeti.GTree.Lifting.graphOfGroups`: the quotient graph of groups of a lifting.
* `TauCeti.GTree.Lifting.π₁TreeHom`: the homomorphism `π₁(𝔹, S) →* G`.
* `TauCeti.GTree.Lifting.π₁Hom`: the homomorphism `π₁(𝔹, v) →* G`.

## Main results

* `TauCeti.GTree.Lifting.coe_α_apply_of_out_eq`, `TauCeti.GTree.Lifting.coe_ω_apply_of_out_eq`
  and their `_rev` versions: the boundary monomorphisms of the chosen dart and of its reverse.
* `TauCeti.GTree.Lifting.twist_mul_coe_ω_mul_inv`: `t_y ω_y(c) t_y⁻¹ = α_y(c)` in `G`.
* `TauCeti.GTree.Lifting.range_val_α`, `TauCeti.GTree.Lifting.range_val_ω`: the images of the
  boundary monomorphisms in `G` are the stabilizers of the lifts of `y` and of `rev y`.
* `TauCeti.GTree.Lifting.π₁TreeHom_surjective`, `TauCeti.GTree.Lifting.π₁Hom_surjective`: the
  homomorphisms to `G` are surjective.

## References

* I. Kapovich, R. Weidmann and A. Myasnikov, *Foldings, graphs of groups and the membership
  problem*, Internat. J. Algebra Comput. 15 (2005), §2, Proposition 2.6 and Remark 2.7.
* J.-P. Serre, *Trees*, Chapter I, §5.4, Theorem 13.
-/

public section

universe u v w

namespace TauCeti

open SerreGraph GraphOfGroups _root_.MulAction

namespace GTree.Lifting

variable {G : Type w} [Group G] {T : GTree.{u, v} G} (D : T.Lifting)

open scoped Classical in
/-- The quotient graph of groups of a lifting `D` of the quotient graph `B = T / G`: the vertex
group at `v` is the stabilizer of the lifted vertex `x_v`, and the edge group of a geometric edge
is the stabilizer of the lift `d_y` of its chosen dart `y`. The boundary monomorphisms of `y` are
the inclusion `α_y : G_{d_y} ≤ G_{src d_y}` and the conjugation `ω_y(c) = t_y⁻¹ c t_y`, and those of
`rev y` are `α_{rev y} = ω_y` and `ω_{rev y} = α_y`. The body is exposed so that elements of the
vertex and edge groups are elements of the stabilizers, with `Subtype.val` into `G`. -/
@[expose] noncomputable def graphOfGroups : GraphOfGroups.{u, v, w, w} T.quotient where
  vertexGroup b := stabilizer G (D.vertex b)
  edgeGroup y := stabilizer G (D.dart (GeomEdge.out T.quotient y))
  ω y := ((MulAut.conj (if GeomEdge.out T.quotient (T.quotient.toGeomEdge y) = y then
      (D.twist y)⁻¹ else 1) : G →* G).comp (Subgroup.subtype _)).codRestrict _ fun c => by
    obtain ⟨c, hc⟩ := c
    rw [mem_stabilizer_iff]
    rcases GeomEdge.out_toGeomEdge_eq_or_eq_rev T.quotient y with h | h
    · -- `c` fixes `d_y`, hence its target `t_y • x_{tgt y}`.
      have hc' := T.stabilizer_dart_le_stabilizer_tgt _ hc
      rw [h, tgt_dart, mem_stabilizer_iff] at hc'
      simp [h, mul_smul, hc']
    · -- `c` fixes the lift of `rev y`, hence its source `x_{tgt y}`.
      have hc' := T.stabilizer_dart_le_stabilizer_src _ hc
      rw [h, src_dart, mem_stabilizer_iff, src_rev] at hc'
      simp [h, T.quotient.rev_ne y, hc']
  ω_injective y c c' h := Subtype.ext <| (MulAut.conj _).injective (congrArg Subtype.val h)

variable {D}

/-! ### The boundary monomorphisms -/

/-- Transport along an equality of vertices does not change an element of a vertex group as an
element of `G`. -/
private theorem coe_cast_vertexGroup {b b' : T.quotient.V} (h : b = b')
    (g : D.graphOfGroups.vertexGroup b) :
    (MulEquiv.cast (M := D.graphOfGroups.vertexGroup) h g).1 = g.1 := by
  subst h
  rfl

/-- Transport along an equality of geometric edges does not change an element of an edge group as
an element of `G`. -/
private theorem coe_cast_edgeGroup {y y' : T.quotient.GeomEdge} (h : y = y')
    (c : D.graphOfGroups.edgeGroup y) :
    (MulEquiv.cast (M := D.graphOfGroups.edgeGroup) h c).1 = c.1 := by
  subst h
  rfl

open scoped Classical in
/-- The boundary monomorphism `ω_y` as a conjugation in `G`, read off the definition. -/
private theorem coe_ω_apply (y : T.quotient.E)
    (c : D.graphOfGroups.edgeGroup (T.quotient.toGeomEdge y)) :
    (D.graphOfGroups.ω y c).1 =
      (if GeomEdge.out T.quotient (T.quotient.toGeomEdge y) = y then (D.twist y)⁻¹ else 1) * c.1 *
        (if GeomEdge.out T.quotient (T.quotient.toGeomEdge y) = y then (D.twist y)⁻¹ else 1)⁻¹ :=
  (rfl)

open scoped Classical in
/-- The boundary monomorphism `α_y = ω_{rev y}` as a conjugation in `G`. -/
private theorem coe_α_apply (y : T.quotient.E)
    (c : D.graphOfGroups.edgeGroup (T.quotient.toGeomEdge y)) :
    (D.graphOfGroups.α y c).1 =
      (if GeomEdge.out T.quotient (T.quotient.toGeomEdge y) = T.quotient.rev y then D.twist y
        else 1) * c.1 *
        (if GeomEdge.out T.quotient (T.quotient.toGeomEdge y) = T.quotient.rev y then D.twist y
          else 1)⁻¹ := by
  rw [GraphOfGroups.α_apply, coe_cast_vertexGroup, coe_ω_apply, coe_cast_edgeGroup]
  -- `α_y` is `ω_{rev y}` on the same geometric edge, conjugated by `t_{rev y}⁻¹ = t_y`.
  have hy : T.quotient.toGeomEdge (T.quotient.rev y) = T.quotient.toGeomEdge y :=
    T.quotient.toGeomEdge_rev y
  simp only [hy, twist_rev, inv_inv]

/-- For the chosen dart `y` of its geometric edge, `α_y` is the inclusion of the stabilizer of the
lift of `y` into the stabilizer of the lift of its source. -/
@[simp] theorem coe_α_apply_of_out_eq {y : T.quotient.E}
    (h : GeomEdge.out T.quotient (T.quotient.toGeomEdge y) = y)
    (c : D.graphOfGroups.edgeGroup (T.quotient.toGeomEdge y)) :
    (D.graphOfGroups.α y c).1 = c.1 := by
  rw [coe_α_apply]
  simp [h, (T.quotient.rev_ne y).symm]

/-- For the chosen dart `y` of its geometric edge, `ω_y` is the conjugation `c ↦ t_y⁻¹ c t_y`. -/
@[simp] theorem coe_ω_apply_of_out_eq {y : T.quotient.E}
    (h : GeomEdge.out T.quotient (T.quotient.toGeomEdge y) = y)
    (c : D.graphOfGroups.edgeGroup (T.quotient.toGeomEdge y)) :
    (D.graphOfGroups.ω y c).1 = (D.twist y)⁻¹ * c.1 * D.twist y := by
  rw [coe_ω_apply]
  simp [h]

/-- When the reverse of `y` is the chosen dart of its geometric edge, `α_y` is the conjugation
`c ↦ t_y c t_y⁻¹`. -/
@[simp] theorem coe_α_apply_of_out_eq_rev {y : T.quotient.E}
    (h : GeomEdge.out T.quotient (T.quotient.toGeomEdge y) = T.quotient.rev y)
    (c : D.graphOfGroups.edgeGroup (T.quotient.toGeomEdge y)) :
    (D.graphOfGroups.α y c).1 = D.twist y * c.1 * (D.twist y)⁻¹ := by
  rw [coe_α_apply]
  simp [h]

/-- When the reverse of `y` is the chosen dart of its geometric edge, `ω_y` is the inclusion of the
stabilizer of the lift of `rev y` into the stabilizer of the lift of the target of `y`. -/
@[simp] theorem coe_ω_apply_of_out_eq_rev {y : T.quotient.E}
    (h : GeomEdge.out T.quotient (T.quotient.toGeomEdge y) = T.quotient.rev y)
    (c : D.graphOfGroups.edgeGroup (T.quotient.toGeomEdge y)) :
    (D.graphOfGroups.ω y c).1 = c.1 := by
  rw [coe_ω_apply]
  simp [h, T.quotient.rev_ne y]

/-- The relation of the dart `y` holds in `G` with `t_y` for `y`: `t_y ω_y(c) t_y⁻¹ = α_y(c)`. -/
theorem twist_mul_coe_ω_mul_inv (y : T.quotient.E)
    (c : D.graphOfGroups.edgeGroup (T.quotient.toGeomEdge y)) :
    D.twist y * (D.graphOfGroups.ω y c).1 * (D.twist y)⁻¹ = (D.graphOfGroups.α y c).1 := by
  rcases GeomEdge.out_toGeomEdge_eq_or_eq_rev T.quotient y with h | h
  · rw [coe_ω_apply_of_out_eq h, coe_α_apply_of_out_eq h]
    simp [mul_assoc]
  · rw [coe_ω_apply_of_out_eq_rev h, coe_α_apply_of_out_eq_rev h]

/-- An element of `G` is the image of an element of the edge group exactly when it lies in the
stabilizer of the lift of the chosen dart. -/
private theorem exists_val_eq_iff {ε : T.quotient.GeomEdge} {g : G} :
    (∃ c : D.graphOfGroups.edgeGroup ε, c.1 = g) ↔
      g ∈ stabilizer G (D.dart (GeomEdge.out T.quotient ε)) :=
  ⟨fun ⟨c, hc⟩ => hc ▸ c.2, fun hg => ⟨⟨g, hg⟩, rfl⟩⟩

/-- An element of `G` is the conjugate by `t` of an element of the edge group exactly when its
conjugate by `t⁻¹` lies in the stabilizer of the lift of the chosen dart. -/
private theorem exists_conj_val_eq_iff {ε : T.quotient.GeomEdge} {t g : G} :
    (∃ c : D.graphOfGroups.edgeGroup ε, t * c.1 * t⁻¹ = g) ↔
      t⁻¹ * g * t ∈ stabilizer G (D.dart (GeomEdge.out T.quotient ε)) := by
  refine ⟨fun ⟨c, hc⟩ => ?_, fun hg => ⟨⟨_, hg⟩, by simp [mul_assoc]⟩⟩
  rw [← hc]
  simpa [mul_assoc] using c.2

/-- An element `g` fixes the lift of `rev y` exactly when its conjugate `t_y g t_y⁻¹` fixes the lift
of `y`. -/
private theorem mem_stabilizer_dart_rev_iff (y : T.quotient.E) {g : G} :
    g ∈ stabilizer G (D.dart (T.quotient.rev y)) ↔
      D.twist y * g * (D.twist y)⁻¹ ∈ stabilizer G (D.dart y) := by
  simp only [dart_rev, mem_stabilizer_iff, ← rev_smul, T.rev_injective.eq_iff, mul_smul]
  -- Both sides say that `g` fixes `t_y⁻¹ • d_y`.
  rw [← smul_left_cancel_iff (D.twist y), smul_inv_smul]

/-- The image of `α_y` in `G` is the stabilizer of the lift of `y`. -/
theorem range_val_α (y : T.quotient.E) :
    Set.range (fun c => (D.graphOfGroups.α y c).1) = stabilizer G (D.dart y) := by
  ext g
  rcases GeomEdge.out_toGeomEdge_eq_or_eq_rev T.quotient y with h | h
  · simp only [Set.mem_range, coe_α_apply_of_out_eq h, exists_val_eq_iff, SetLike.mem_coe]
    rw [h]
  · simp only [Set.mem_range, coe_α_apply_of_out_eq_rev h, exists_conj_val_eq_iff,
      SetLike.mem_coe]
    rw [h, mem_stabilizer_dart_rev_iff]
    simp [mul_assoc]

/-- The boundary monomorphism `α_y` takes values in the stabilizer of the lift of `y`. -/
theorem coe_α_apply_mem_stabilizer (y : T.quotient.E)
    (c : D.graphOfGroups.edgeGroup (T.quotient.toGeomEdge y)) :
    (D.graphOfGroups.α y c).1 ∈ stabilizer G (D.dart y) := by
  rw [← SetLike.mem_coe, ← range_val_α]
  exact ⟨c, rfl⟩

/-- Every element of the stabilizer of the lift of `y` is the image of an element of the edge
group under `α_y`. -/
theorem exists_coe_α_apply_eq_of_mem_stabilizer {y : T.quotient.E} {g : G}
    (hg : g ∈ stabilizer G (D.dart y)) : ∃ c, (D.graphOfGroups.α y c).1 = g := by
  rwa [← SetLike.mem_coe, ← range_val_α] at hg

/-- The image of `ω_y` in `G` is the stabilizer of the lift of `rev y`. -/
theorem range_val_ω (y : T.quotient.E) :
    Set.range (fun c => (D.graphOfGroups.ω y c).1) = stabilizer G (D.dart (T.quotient.rev y)) := by
  ext g
  rcases GeomEdge.out_toGeomEdge_eq_or_eq_rev T.quotient y with h | h
  · simp only [Set.mem_range, coe_ω_apply_of_out_eq h, SetLike.mem_coe]
    -- `ω_y` is the conjugation by `t = t_y⁻¹`.
    simpa only [inv_inv, h, mem_stabilizer_dart_rev_iff] using
      exists_conj_val_eq_iff (ε := T.quotient.toGeomEdge y) (t := (D.twist y)⁻¹) (g := g)
  · simp only [Set.mem_range, coe_ω_apply_of_out_eq_rev h, exists_val_eq_iff, SetLike.mem_coe]
    rw [h]

/-! ### The homomorphism to `G` -/

variable (D)

/-- The homomorphism `π₁(𝔹, S) →* G` from the fundamental group of the quotient graph of groups
relative to the spanning tree `S` of the lifting: it is the inclusion on every vertex group
`G_{x_v}` and sends the dart `y` to `t_y`. -/
noncomputable def π₁TreeHom : π₁Tree D.graphOfGroups D.tree.darts →* G :=
  π₁Tree.lift (fun b => (stabilizer G (D.vertex b)).subtype) D.twist D.twist_eq_one D.twist_rev
    twist_mul_coe_ω_mul_inv

@[simp] theorem π₁TreeHom_of (b : T.quotient.V) (g : D.graphOfGroups.vertexGroup b) :
    D.π₁TreeHom (π₁Tree.of D.tree.darts b g) = g.1 :=
  π₁Tree.lift_of ..

@[simp] theorem π₁TreeHom_comp_of (b : T.quotient.V) :
    D.π₁TreeHom.comp (π₁Tree.of D.tree.darts b) = (stabilizer G (D.vertex b)).subtype :=
  π₁Tree.lift_comp_of ..

@[simp] theorem π₁TreeHom_edge (y : T.quotient.E) :
    D.π₁TreeHom (π₁Tree.edge D.tree.darts y) = D.twist y :=
  π₁Tree.lift_edge ..

/-- The homomorphism `π₁(𝔹, S) →* G` is surjective, since the stabilizers of the lifted vertices
and the elements `t_y` generate `G`. -/
theorem π₁TreeHom_surjective : Function.Surjective D.π₁TreeHom := by
  refine MonoidHom.range_eq_top.1 ((π₁Tree.range_lift ..).trans ?_)
  rw [← D.iSup_stabilizer_sup_closure_range_twist_eq_top]
  congr! with b
  exact Subgroup.range_subtype _

/-- The homomorphism `π₁(𝔹, v) →* G` from the fundamental group of the quotient graph of groups at
a vertex `v`: a closed `𝔹`-path is sent to the product of its letters, read as elements of the
vertex groups and as the elements `t_y` of its darts. -/
noncomputable def π₁Hom (b : T.quotient.V) : π₁ D.graphOfGroups b →* G :=
  D.π₁TreeHom.comp (π₁Equiv D.graphOfGroups b D.tree).toMonoidHom

theorem coe_π₁Hom (b : T.quotient.V) :
    ⇑(D.π₁Hom b) = D.π₁TreeHom ∘ π₁Equiv D.graphOfGroups b D.tree :=
  (rfl)

@[simp] theorem π₁Hom_mk {b : T.quotient.V} (p : D.graphOfGroups.Path ⟨b⟩ ⟨b⟩) :
    D.π₁Hom b (π₁.mk p) = D.π₁TreeHom (p.toπ₁Tree D.tree.darts) := by
  simp [π₁Hom]

/-- On the vertex group at the base vertex, the homomorphism `π₁(𝔹, v) →* G` is the inclusion of
the stabilizer of the lifted vertex. -/
theorem π₁Hom_vertexHom_nil {b : T.quotient.V} (g : D.graphOfGroups.vertexGroup b) :
    D.π₁Hom b (π₁.vertexHom Quiver.Path.nil g) = g.1 := by
  simp

/-- The homomorphism `π₁(𝔹, v) →* G` is surjective. -/
theorem π₁Hom_surjective (b : T.quotient.V) : Function.Surjective (D.π₁Hom b) :=
  D.π₁TreeHom_surjective.comp (π₁Equiv D.graphOfGroups b D.tree).surjective

end GTree.Lifting

end TauCeti
