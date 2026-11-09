/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Stallings.Coset.Basic
public import TauCeti.Combinatorics.Graph.Stallings.Morphism

/-!
# Embedding folded labelled graphs in coset graphs

A connected based labelled graph maps to the coset graph of a subgroup precisely when its
accepted subgroup is contained in that subgroup. When the graph is folded and the subgroup
is its own accepted subgroup, this morphism is injective on both vertices and darts.
Thus a connected folded graph can be viewed as a subgraph of its coset graph, the comparison
used to identify folded cores with subgroup graphs.

The vertex reached by a path reading `g` maps to the left coset of `g⁻¹`. This inverse is
required by the inverse-left-action convention for paths in the coset graph.

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*,
  Sections 4–5, especially Theorem 5.1.
-/

public section

namespace TauCeti.StallingsGraph

variable {α : Type*} {S : StallingsGraph α} {H : Subgroup (FreeGroup α)}

/-- The quiver of the target coset graph, for its path endpoint formula. -/
@[instance_reducible] local instance : Quiver H.cosetGraph.graph.V :=
  H.cosetGraph.graph.toQuiver

/-- The image of the endpoint of a based path in a coset graph is the left coset of the
inverse of its reading. -/
theorem Hom.mapV_eq_coset (f : S.Hom H.cosetGraph) {v : S.graph.V}
    (p : S.graph.Path S.base v) :
    f.graphHom.mapV v = (QuotientGroup.mk (S.read p)⁻¹ : FreeGroup α ⧸ H) := by
  have h := H.cosetGraph_path_endpoint (f.graphHom.toPrefunctor.mapPath p)
  rw [f.read_mapPath] at h
  simpa only [SerreGraph.Hom.toPrefunctor_obj, f.map_base, Subgroup.cosetGraph_base,
    Subgroup.cosetStep_mk, mul_one] using h

/-- A connected based labelled graph admits a based morphism to a coset graph exactly when
its accepted subgroup is contained in the defining subgroup. Foldedness of the source is
not required. -/
theorem nonempty_hom_cosetGraph_iff
    (hS : ∀ v : S.graph.V, Nonempty (S.graph.Path S.base v)) :
    Nonempty (S.Hom H.cosetGraph) ↔ S.subgroup S.base ≤ H := by
  classical
  constructor
  · rintro ⟨f⟩
    exact f.subgroup_le.trans_eq H.cosetGraph_subgroup
  · intro hH
    let p (v : S.graph.V) := (hS v).some
    let vmap (v : S.graph.V) : FreeGroup α ⧸ H := QuotientGroup.mk (S.read (p v))⁻¹
    have hv (v : S.graph.V) (q : S.graph.Path S.base v) :
        vmap v = (QuotientGroup.mk (S.read q)⁻¹ : FreeGroup α ⧸ H) := by
      apply QuotientGroup.eq.mpr
      simpa only [inv_inv, read_comp, read_reverse] using
        hH (S.read_mem_subgroup ((p v).comp q.reverse))
    have hstep (e : S.graph.E) :
        vmap (S.graph.tgt e) =
          Subgroup.cosetStep H (vmap (S.graph.src e)) (FreeGroup.mk [S.label e]) := by
      rw [hv _ ((p (S.graph.src e)).cons (S.graph.dart e))]
      simp only [read_cons, SerreGraph.dart_val, mul_inv_rev, vmap,
        Subgroup.cosetStep_mk]
    let f : S.Hom H.cosetGraph := {
      graphHom := {
        mapV := vmap
        mapE := fun e => (vmap (S.graph.src e), S.label e)
        map_src := fun _ => rfl
        map_rev := fun e => Prod.ext (by simpa using hstep e) (S.label_rev e) }
      map_base := by simpa using hv S.base Quiver.Path.nil
      map_label := fun _ => rfl }
    exact ⟨f⟩

/-- For a folded graph, its based map to the coset graph of its accepted subgroup is
injective on both vertices and darts. Distinct parallel darts and loop directions survive.
Connectivity is used only to reach each vertex from the base. -/
theorem Hom.injective_cosetGraph
    (f : S.Hom (S.subgroup S.base).cosetGraph) (hfold : S.IsFolded)
    (hS : ∀ v : S.graph.V, Nonempty (S.graph.Path S.base v)) :
    Function.Injective f.graphHom.mapV ∧ Function.Injective f.graphHom.mapE := by
  have hv : Function.Injective f.graphHom.mapV := by
    intro v w h
    obtain ⟨p⟩ := hS v
    obtain ⟨q⟩ := hS w
    rw [f.mapV_eq_coset p, f.mapV_eq_coset q] at h
    apply (hfold.eq_tgt_iff_read_mul_inv_mem S p q).mpr
    simpa only [inv_inv] using QuotientGroup.eq.mp h
  exact ⟨hv, f.injective_mapE_of_injective_mapV hfold hv⟩

end TauCeti.StallingsGraph
