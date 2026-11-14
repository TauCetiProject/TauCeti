/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.OfGraph.ToGraph

/-!
# The Serre graph of a multigraph is unique up to isomorphism

A multigraph `G` gives the Serre graph `G.toSerreGraph`, which attaches two darts to every edge
after choosing an ordering of its two ends. Since isomorphisms of underlying multigraphs lift to
isomorphisms of Serre graphs (`TauCeti.SerreGraph.Iso.ofToGraphIso`), a Serre graph carries no
information beyond its underlying multigraph, up to isomorphism. So a Serre graph is isomorphic to
`G.toSerreGraph` exactly when its underlying multigraph is isomorphic to `G`, isomorphic
multigraphs have isomorphic Serre graphs, and passing from a Serre graph to its multigraph and
back recovers the Serre graph; the other round trip, `G.toSerreGraph.toGraph ≅ G`, is
`Graph.toSerreGraphToGraphIso`.

For an orientation `O` of a Serre graph `Γ`, the multigraph `Γ.endpointGraph O` of the darts of
`O` is isomorphic to `Γ.toGraph`, so `Γ` is isomorphic to `G.toSerreGraph` exactly when
`Γ.endpointGraph O` is isomorphic to `G`. Informally, this says that the choice of the ordering of
the ends in `G.toSerreGraph` does not matter: a Serre graph obtained from `G` by ordering the ends
of each edge in any way and adding the reverse darts has the orientation formed by the darts
following the chosen orderings, and the multigraph of the darts of that orientation is isomorphic
to `G`.

## Main declarations

* `TauCeti.SerreGraph.toGraphToSerreGraphIso`: the Serre graph of the underlying multigraph of a
  Serre graph is isomorphic to it.
* `Graph.nonempty_iso_toSerreGraph_iff`: the Serre graphs isomorphic to `G.toSerreGraph` are those
  whose underlying multigraph is isomorphic to `G`.
* `Graph.Iso.toSerreGraphIso`: an isomorphism of multigraphs lifts to an isomorphism of their
  Serre graphs, and `Graph.nonempty_toSerreGraph_iso_iff`: two multigraphs have isomorphic Serre
  graphs exactly when they are isomorphic.
* `TauCeti.SerreGraph.IsOrientation.nonempty_iso_toSerreGraph_iff`: a Serre graph with an
  orientation `O` is isomorphic to `G.toSerreGraph` exactly when the multigraph of the darts of `O`
  is isomorphic to `G`.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.1.
* I. Kapovich, R. Weidmann, A. Miasnikov, *Foldings, graphs of groups and the membership
  problem*, Convention 2.1 and Convention 3.2.
* I. Kapovich, A. Myasnikov, *Stallings foldings and subgroups of free groups*, Convention 2.2.
-/

public section

universe u v

namespace TauCeti.SerreGraph

/-- A Serre graph is recovered from its underlying multigraph: the Serre graph of `Γ.toGraph` is
isomorphic to `Γ`, by the identity on vertices and a bijection sending each dart of
`Γ.toGraph.toSerreGraph` into the reversal orbit it lies over. -/
noncomputable def toGraphToSerreGraphIso (Γ : SerreGraph.{u, v}) : Γ.toGraph.toSerreGraph.Iso Γ :=
  Iso.ofToGraphIso Γ.toGraph.toSerreGraphToGraphIso

/-- The isomorphism `Γ.toGraph.toSerreGraph ≅ Γ` is the identity on vertices. -/
@[simp] theorem toGraphToSerreGraphIso_equivV_apply (Γ : SerreGraph.{u, v})
    (a : Γ.toGraph.toSerreGraph.V) : Γ.toGraphToSerreGraphIso.equivV a = a.1 := by
  simp [toGraphToSerreGraphIso]

@[simp] theorem coe_toGraphToSerreGraphIso_equivV_symm_apply (Γ : SerreGraph.{u, v}) (v : Γ.V) :
    (Γ.toGraphToSerreGraphIso.equivV.symm v).1 = v := by
  simp [toGraphToSerreGraphIso]

/-- The isomorphism `Γ.toGraph.toSerreGraph ≅ Γ` sends a dart over an edge of `Γ.toGraph` into
that reversal orbit. -/
@[simp] theorem edge_toGraphToSerreGraphIso_equivE (Γ : SerreGraph.{u, v})
    (d : Γ.toGraph.toSerreGraph.E) : Γ.edge (Γ.toGraphToSerreGraphIso.equivE d) = d.1.1 := by
  simp [toGraphToSerreGraphIso]

@[simp] theorem coe_fst_toGraphToSerreGraphIso_equivE_symm (Γ : SerreGraph.{u, v}) (e : Γ.E) :
    (Γ.toGraphToSerreGraphIso.equivE.symm e).1.1 = Γ.edge e := by
  simpa using (Γ.edge_toGraphToSerreGraphIso_equivE (Γ.toGraphToSerreGraphIso.equivE.symm e)).symm

/-- The isomorphism `Γ.toGraph.toSerreGraph ≅ Γ` induces the isomorphism
`Γ.toGraph.toSerreGraph.toGraph ≅ Γ.toGraph` of the round trip from multigraphs. -/
@[simp] theorem toGraphIso_toGraphToSerreGraphIso (Γ : SerreGraph.{u, v}) :
    Γ.toGraphToSerreGraphIso.toGraphIso = Γ.toGraph.toSerreGraphToGraphIso :=
  Iso.toGraphIso_ofToGraphIso _

end TauCeti.SerreGraph

namespace Graph

open TauCeti

variable {V E V' E' : Type*} {G : Graph V E} {H : Graph V' E'}

/-- The Serre graph of a multigraph `G` is, up to isomorphism, the only Serre graph whose
underlying multigraph is `G`. -/
theorem nonempty_iso_toSerreGraph_iff {Γ : SerreGraph} :
    Nonempty (Γ.Iso G.toSerreGraph) ↔ Nonempty (Γ.toGraph.Iso G) := by
  rw [SerreGraph.nonempty_iso_iff_nonempty_toGraph_iso]
  exact ⟨Nonempty.map (·.trans G.toSerreGraphToGraphIso),
    Nonempty.map (·.trans G.toSerreGraphToGraphIso.symm)⟩

/-- An isomorphism of multigraphs lifts to an isomorphism of their Serre graphs: it is the given
isomorphism on vertices and sends each dart to a dart over the image of its edge. On a loop the
direction of the image dart is chosen. -/
noncomputable def Iso.toSerreGraphIso (φ : G.Iso H) : G.toSerreGraph.Iso H.toSerreGraph :=
  SerreGraph.Iso.ofToGraphIso
    (G.toSerreGraphToGraphIso.trans (φ.trans H.toSerreGraphToGraphIso.symm))

@[simp] theorem Iso.toSerreGraphIso_equivV_apply (φ : G.Iso H) (v : G.toSerreGraph.V) :
    φ.toSerreGraphIso.equivV v = φ.vertexEquiv v := by
  simp [toSerreGraphIso]

@[simp] theorem Iso.toSerreGraphIso_equivV_symm_apply (φ : G.Iso H) (v : H.toSerreGraph.V) :
    φ.toSerreGraphIso.equivV.symm v = φ.vertexEquiv.symm v := by
  rw [Equiv.symm_apply_eq, toSerreGraphIso_equivV_apply, Equiv.apply_symm_apply]

/-- The lift of a multigraph isomorphism sends a dart over an edge to a dart over its image. -/
@[simp] theorem Iso.fst_toSerreGraphIso_equivE (φ : G.Iso H) (d : G.toSerreGraph.E) :
    (φ.toSerreGraphIso.equivE d).1 = φ.edgeEquiv d.1 := by
  rw [← H.toSerreGraphEdgeEquiv_symm_edge (φ.toSerreGraphIso.equivE d), toSerreGraphIso,
    SerreGraph.Iso.edge_ofToGraphIso_equivE]
  simp

@[simp] theorem Iso.fst_toSerreGraphIso_equivE_symm (φ : G.Iso H) (d : H.toSerreGraph.E) :
    (φ.toSerreGraphIso.equivE.symm d).1 = φ.edgeEquiv.symm d.1 := by
  obtain ⟨d, rfl⟩ := φ.toSerreGraphIso.equivE.surjective d
  simp

/-- The lift of a multigraph isomorphism induces that isomorphism, up to the identifications of
the multigraphs underlying the Serre graphs with the original multigraphs. -/
@[simp] theorem Iso.toGraphIso_toSerreGraphIso (φ : G.Iso H) :
    φ.toSerreGraphIso.toGraphIso =
      G.toSerreGraphToGraphIso.trans (φ.trans H.toSerreGraphToGraphIso.symm) :=
  SerreGraph.Iso.toGraphIso_ofToGraphIso _

/-- Two multigraphs have isomorphic Serre graphs exactly when they are isomorphic. -/
theorem nonempty_toSerreGraph_iso_iff :
    Nonempty (G.toSerreGraph.Iso H.toSerreGraph) ↔ Nonempty (G.Iso H) :=
  ⟨Nonempty.map fun ψ ↦ G.toSerreGraphToGraphIso.symm.trans
    (ψ.toGraphIso.trans H.toSerreGraphToGraphIso), Nonempty.map Iso.toSerreGraphIso⟩

end Graph

namespace TauCeti.SerreGraph.IsOrientation

variable {V E : Type*}

/-- A Serre graph `Γ` with an orientation `O` is isomorphic to `G.toSerreGraph` exactly when the
multigraph of the darts of `O` is isomorphic to `G`.

Informally, a Serre graph obtained from `G` by ordering the ends of each edge in some way and
adding the reverse darts has an orientation, formed by the darts following the chosen orderings,
whose dart multigraph is isomorphic to `G`; so all such Serre graphs are isomorphic to
`G.toSerreGraph`. -/
theorem nonempty_iso_toSerreGraph_iff {Γ : SerreGraph} {O : Set Γ.E} (hO : Γ.IsOrientation O)
    {G : Graph V E} : Nonempty (Γ.Iso G.toSerreGraph) ↔ Nonempty ((Γ.endpointGraph O).Iso G) := by
  rw [Graph.nonempty_iso_toSerreGraph_iff]
  exact ⟨Nonempty.map hO.endpointGraphIsoToGraph.trans,
    Nonempty.map hO.endpointGraphIsoToGraph.symm.trans⟩

end TauCeti.SerreGraph.IsOrientation
