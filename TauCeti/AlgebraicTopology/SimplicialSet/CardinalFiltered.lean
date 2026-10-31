/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.Order.Bounds.Defs
public import Mathlib.SetTheory.Cardinal.HasCardinalLT
public import TauCeti.AlgebraicTopology.SimplicialSet.Discrete
public import TauCeti.AlgebraicTopology.SimplicialSet.Join
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Preorder

/-!
# Cardinal filtered simplicial sets

Let `κ` be a cardinal. A simplicial set is `κ`-small when it has fewer than `κ` nondegenerate
simplices, and a simplicial set `K` is `κ`-filtered when every map `Y ⟶ K` from a `κ`-small
simplicial set `Y` extends along the inclusion `Y ⟶ Y ⋆ Δ[0]` into the cone on `Y`. Thus every
`κ`-small diagram in `K` has a cocone in `K`. This is the quasicategorical notion of a `κ`-filtered
diagram shape, the analogue for simplicial sets of Mathlib's `CategoryTheory.IsCardinalFiltered`:
`κ`-filtered colimits, `κ`-compact objects and accessible quasicategories are defined through it.

For the empty simplicial set `Y` the condition asks for a vertex of `K`; for `Y` a set of fewer
than `κ` points it asks for a common target of edges out of these vertices
(`SSet.IsCardinalFiltered.exists_edge`). Nondegenerate simplices are counted, not all simplices:
the standard simplex `Δ[n]` has infinitely many simplices but finitely many nondegenerate ones,
so it is `κ`-small for every infinite `κ`.

For the nerve of a preorder `P`, a cocone on a diagram amounts to an upper bound of its vertices,
since simplices of the nerve are determined by their vertices; accordingly the nerve of `P` is
`κ`-filtered exactly when every subset of `P` with fewer than `κ` elements is bounded above
(`SSet.isCardinalFiltered_nerve_iff`).

## Main declarations

* `SSet.IsCardinalFiltered K κ`: the simplicial set `K` is `κ`-filtered.
* `SSet.IsCardinalFiltered.exists_edge`: in a `κ`-filtered simplicial set, every family of fewer
  than `κ` vertices has edges to a common vertex.
* `SSet.isCardinalFiltered_of_isTerminal`: a terminal simplicial set, such as `Δ[0]`, is
  `κ`-filtered.
* `SSet.isCardinalFiltered_nerve_iff`: the nerve of a preorder is `κ`-filtered if and only if its
  subsets with fewer than `κ` elements are bounded above.
* `SSet.not_isCardinalFiltered_nerve_discrete`: the nerve of a discrete category with two distinct
  objects is not `κ`-filtered for `κ > 2`.

## References

* J. Lurie, *Higher Topos Theory*, Definition 5.3.1.7 and Example 5.3.1.8.
-/

public section

open CategoryTheory Limits Opposite Simplicial

universe w u

namespace SSet

/-- A simplicial set `K` is `κ`-filtered if every map `Y ⟶ K` from a simplicial set `Y` with fewer
than `κ` nondegenerate simplices extends to the cone `Y ⋆ Δ[0]`, along the inclusion of `Y`. -/
class IsCardinalFiltered (K : SSet.{u}) (κ : Cardinal.{w}) : Prop where
  exists_join_extension ⦃Y : SSet.{u}⦄ (hY : HasCardinalLT Y.N κ) (f : Y ⟶ K) :
    ∃ F : join Y Δ[0] ⟶ K, join.inl Y Δ[0] ≫ F = f

variable {K L : SSet.{u}} {κ : Cardinal.{w}}

namespace IsCardinalFiltered

/-- A `κ`-filtered simplicial set is `κ'`-filtered for every `κ' ≤ κ`. -/
lemma of_le (K : SSet.{u}) {κ' : Cardinal.{w}} [K.IsCardinalFiltered κ] (h : κ' ≤ κ) :
    K.IsCardinalFiltered κ' where
  exists_join_extension _ hY f := exists_join_extension (hY.of_le h) f

/-- Being `κ`-filtered is invariant under isomorphism. -/
lemma of_iso [K.IsCardinalFiltered κ] (e : K ≅ L) : L.IsCardinalFiltered κ where
  exists_join_extension _ hY f := by
    obtain ⟨F, hF⟩ := exists_join_extension (K := K) hY (f ≫ e.inv)
    exact ⟨F ≫ e.hom, by rw [← Category.assoc, hF, Category.assoc, e.inv_hom_id,
      Category.comp_id]⟩

/-- In a `κ`-filtered simplicial set, every family of fewer than `κ` vertices has edges to a
common vertex: these are the cones on discrete diagrams. -/
theorem exists_edge [K.IsCardinalFiltered κ] {ι : Type u} (hι : HasCardinalLT ι κ)
    (x : ι → K _⦋0⦌) : ∃ z : K _⦋0⦌, ∀ i, Nonempty (K.Edge (x i) z) := by
  -- Extend the map from the discrete simplicial set on `ι` to its cone.
  obtain ⟨F, hF⟩ := exists_join_extension (K := K)
    ((hasCardinalLT_iff_of_equiv (constNEquiv ι) κ).2 hι) ((constHomEquiv ι).symm x)
  refine ⟨F.app _ ((join.inr _ _).app _ (stdSimplex.obj₀Equiv.symm 0)), fun i ↦ ⟨?_⟩⟩
  -- The image of the edge of the cone from `i` to the cone point; the vertices of the discrete
  -- simplicial set on `ι` are the elements of `ι`.
  refine ((join.edgeMk (i : ((Functor.const SimplexCategoryᵒᵖ).obj ι : SSet.{u}) _⦋0⦌)
    (stdSimplex.obj₀Equiv.symm 0)).map F).ofEq ?_ rfl
  rw [← constHomEquiv_symm_app_zero ι x i, ← hF, comp_app, ConcreteCategory.comp_apply]

/-- A `κ`-filtered simplicial set has a vertex if `κ` is nonzero: the empty diagram has a
cocone. -/
theorem nonempty [K.IsCardinalFiltered κ] (hκ : κ ≠ 0) : Nonempty (K _⦋0⦌) := by
  have hι : HasCardinalLT PEmpty.{u + 1} κ := by
    rw [HasCardinalLT, Cardinal.mk_eq_zero, Cardinal.lift_zero]
    exact pos_iff_ne_zero.2 (Cardinal.lift_eq_zero.not.2 hκ)
  exact ⟨(exists_edge hι PEmpty.elim).choose⟩

end IsCardinalFiltered

/-- A terminal simplicial set, such as `Δ[0]`, is `κ`-filtered for every `κ`. -/
lemma isCardinalFiltered_of_isTerminal (hK : IsTerminal K) : K.IsCardinalFiltered κ where
  exists_join_extension _ _ _ := ⟨hK.from _, hK.hom_ext _ _⟩

/-- The standard `0`-simplex is `κ`-filtered for every `κ`. -/
instance isCardinalFiltered_stdSimplex_zero : (Δ[0] : SSet.{u}).IsCardinalFiltered κ :=
  isCardinalFiltered_of_isTerminal SSet.stdSimplex.isTerminalObj₀

/-- The empty simplicial set is not `κ`-filtered for nonzero `κ`. -/
lemma not_isCardinalFiltered_of_isEmpty (hK : IsEmpty (K _⦋0⦌)) (hκ : κ ≠ 0) :
    ¬ K.IsCardinalFiltered κ := fun _ ↦
  hK.false (IsCardinalFiltered.nonempty hκ).some

section Preorder

variable {P : Type u} [Preorder P] {Y : SSet.{u}}

open Classical in
/-- The vertex map of the extension of `f : Y ⟶ nerve P` to the cone `Y ⋆ Δ[0]` which sends the cone
point to `b`. -/
private noncomputable def coneVertex (f : Y ⟶ nerve P) (b : P) (v : (join Y Δ[0]) _⦋0⦌) : P :=
  if hv : v ∈ (joinFiber (join.univ Y Δ[0]).p 0).obj _ then
    nerveEquiv (f.app _ ((join.univ Y Δ[0]).left.app _ ⟨v, hv⟩))
  else b

private lemma coneVertex_of_mem (f : Y ⟶ nerve P) (b : P) {v : (join Y Δ[0]) _⦋0⦌}
    (hv : v ∈ (joinFiber (join.univ Y Δ[0]).p 0).obj _) :
    coneVertex f b v = nerveEquiv (f.app _ ((join.univ Y Δ[0]).left.app _ ⟨v, hv⟩)) := by
  simp only [coneVertex, hv, ↓reduceDIte]

private lemma coneVertex_of_notMem (f : Y ⟶ nerve P) (b : P) {v : (join Y Δ[0]) _⦋0⦌}
    (hv : v ∉ (joinFiber (join.univ Y Δ[0]).p 0).obj _) : coneVertex f b v = b := by
  simp only [coneVertex, hv, ↓reduceDIte]

/-- If `b` bounds the vertices of `f : Y ⟶ nerve P`, sending the cone point to `b` is monotone
along the edges of the cone. -/
private lemma coneVertex_le (f : Y ⟶ nerve P) {b : P}
    (hb : ∀ y : Y _⦋0⦌, nerveEquiv (f.app _ y) ≤ b)
    {v w : (join Y Δ[0]) _⦋0⦌} (e : (join Y Δ[0]).Edge v w) :
    coneVertex f b v ≤ coneVertex f b w := by
  by_cases hw : w ∈ (joinFiber (join.univ Y Δ[0]).p 0).obj _
  · -- The edge lies in `Y`, where it is sent to an edge of `nerve P` by `f`.
    have he := join.edge_mem_joinFiber_zero e hw
    have hv : v ∈ (joinFiber (join.univ Y Δ[0]).p 0).obj _ := by
      rw [← e.src_eq]
      exact (joinFiber (join.univ Y Δ[0]).p 0).map (SimplexCategory.δ 1).op he
    rw [coneVertex_of_mem f b hw, coneVertex_of_mem f b hv]
    exact nerve.le_of_edge f
      ((e.toSubcomplex (joinFiber (join.univ Y Δ[0]).p 0) he).map (join.univ Y Δ[0]).left :
        Y.Edge ((join.univ Y Δ[0]).left.app _ ⟨v, hv⟩) ((join.univ Y Δ[0]).left.app _ ⟨w, hw⟩))
  · rw [coneVertex_of_notMem f b hw]
    by_cases hv : v ∈ (joinFiber (join.univ Y Δ[0]).p 0).obj _
    · exact (coneVertex_of_mem f b hv).trans_le (hb _)
    · exact (coneVertex_of_notMem f b hv).le

/-- The nerve of a preorder `P` is `κ`-filtered if and only if every subset of `P` with fewer than
`κ` elements is bounded above. -/
theorem isCardinalFiltered_nerve_iff :
    (nerve P).IsCardinalFiltered κ ↔ ∀ s : Set P, HasCardinalLT s κ → BddAbove s := by
  refine ⟨fun _ s hs ↦ ?_, fun h ↦ ⟨fun Y hY f ↦ ?_⟩⟩
  · -- The vertices of a cocone on `s` are bounded by its cone point.
    obtain ⟨z, hz⟩ := IsCardinalFiltered.exists_edge (K := nerve P) hs
      fun i ↦ nerveEquiv.symm i.1
    exact ⟨nerveEquiv z, fun a ha ↦ (nerve.homEquiv (hz ⟨a, ha⟩).some).le⟩
  -- The values of `f` on the vertices of `Y` form a set with fewer than `κ` elements, since the
  -- vertices of `Y` are nondegenerate.
  obtain ⟨b, hb⟩ := h (Set.range fun y : Y _⦋0⦌ ↦ nerveEquiv (f.app _ y))
    ((hY.of_injective (fun y ↦ N.mk y (by simp)) fun _ _ hxy ↦
      (S.ext_iff _ _).1 ((N.ext_iff _ _).1 hxy)).of_surjective _
      Set.rangeFactorization_surjective)
  -- Send the cone point to the upper bound `b`.
  refine ⟨nerve.homOfVertex (coneVertex f b) fun _ _ e ↦
    coneVertex_le f (fun y : Y _⦋0⦌ ↦ hb (Set.mem_range_self y)) e,
    nerve.hom_ext_of_preorder fun y ↦ ?_⟩
  rw [comp_app, ConcreteCategory.comp_apply, nerve.nerveEquiv_homOfVertex_app,
    coneVertex_of_mem f b (join.range_inl_le_joinFiber Y Δ[0] _ ⟨y, rfl⟩),
    join.univ_left_app_inl_app]

end Preorder

/-- The nerve of a discrete category with two distinct objects is not `κ`-filtered for `κ > 2`: two
distinct objects have no common target. -/
theorem not_isCardinalFiltered_nerve_discrete {α : Type u} [Nontrivial α]
    (hκ : HasCardinalLT Bool κ) : ¬ (nerve (Discrete α)).IsCardinalFiltered κ := fun _ ↦ by
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  obtain ⟨z, hz⟩ := IsCardinalFiltered.exists_edge (K := nerve (Discrete α))
    ((hasCardinalLT_iff_of_equiv Equiv.ulift κ).2 hκ)
    fun i ↦ nerveEquiv.symm ⟨if i.down then a else b⟩
  have h₁ := Discrete.eq_of_hom (nerve.homEquiv (hz (ULift.up true)).some)
  have h₂ := Discrete.eq_of_hom (nerve.homEquiv (hz (ULift.up false)).some)
  rw [Equiv.apply_symm_apply] at h₁ h₂
  exact hab (by simpa using h₁.trans h₂.symm)

end SSet
