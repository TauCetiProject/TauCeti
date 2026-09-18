/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.RibbonGraph.OfPermutationTriple
public import TauCeti.Combinatorics.RibbonGraph.ToPermutationTriple

/-!
# Ribbon graphs and permutation triples classify each other

Numbering the edges of a finite bipartite ribbon graph turns it into a permutation triple
(`TauCeti.BipartiteRibbonGraph.toPermutationTriple`), and every permutation triple has a ribbon
graph (`TauCeti.PermutationTriple.ribbonGraph`). This file proves that the two constructions are
mutually inverse up to the appropriate notion of isomorphism on each side, so that isomorphism
classes of ribbon graphs with `n` edges are the same as isomorphism classes of degree-`n`
permutation triples, automorphisms included.

* `TauCeti.PermutationTriple.toPermutationTriple_ribbonGraph`: triple → graph → triple returns
  the original triple on the nose, for the tautological numbering of the edges by `Fin n`.
* `TauCeti.BipartiteRibbonGraph.isoRibbonGraph`: graph → triple → graph returns a graph
  isomorphic to the original, the isomorphism being the chosen numbering on edges.
* `TauCeti.BipartiteRibbonGraph.nonempty_iso_iff_equivalent`: two numbered graphs are isomorphic
  exactly when their triples are related by relabeling, and
  `TauCeti.PermutationTriple.nonempty_iso_ribbonGraph_iff` is the same statement read on triples.
* `TauCeti.BipartiteRibbonGraph.isoClassEquiv`: the resulting bijection between isomorphism
  classes of ribbon graphs with `n` edges and `TauCeti.PermutationTriple.IsoClass n`.
* `TauCeti.BipartiteRibbonGraph.autEquivAutomorphismGroup`: the automorphism group of a numbered
  graph is the automorphism group of its triple.

Connectedness matches on the two sides
(`TauCeti.BipartiteRibbonGraph.isConnected_toPermutationTriple` and
`TauCeti.PermutationTriple.isConnected_ribbonGraph`), so the bijection restricts to one between
isomorphism classes of dessins d'enfants and of connected triples.

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.3 and §1.5.
* E. Girondo, G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins d'Enfants*,
  London Mathematical Society Student Texts 79, Cambridge University Press 2012, §4.2.
-/

open Equiv

public section

namespace TauCeti

universe u v

/-- Triple → graph → triple is the identity: numbering the edges of the ribbon graph of a triple
by the sheets they are recovers the triple. The edge type of `t.ribbonGraph` is `Fin n` by
construction, so the identity is such a numbering. -/
@[simp]
theorem PermutationTriple.toPermutationTriple_ribbonGraph {n : ℕ} (t : PermutationTriple n) :
    t.ribbonGraph.toPermutationTriple (Equiv.refl (Fin n)) = t := by
  -- Both components are the rotations of `t.ribbonGraph` read through the identity numbering,
  -- which are `t.σ0` and `t.σ1` by the construction of `t.ribbonGraph`; the edge type being
  -- `Fin n` only up to that construction, the pointwise comparison is closed by `rfl`.
  refine PermutationTriple.ext_of_two ((BipartiteRibbonGraph.toPermutationTriple_σ0 _ _).trans ?_)
    ((BipartiteRibbonGraph.toPermutationTriple_σ1 _ _).trans ?_) <;>
  exact Equiv.ext fun _ ↦ rfl

namespace BipartiteRibbonGraph

variable {n : ℕ} {Γ : BipartiteRibbonGraph.{u}} {Δ : BipartiteRibbonGraph.{v}}

/-- Two numbered ribbon graphs with the same permutation triple are isomorphic, by matching the
edges carrying the same number. -/
noncomputable def isoOfToPermutationTripleEq {ν : Γ.E ≃ Fin n} {μ : Δ.E ≃ Fin n}
    (h : Γ.toPermutationTriple ν = Δ.toPermutationTriple μ) : Γ.Iso Δ :=
  Iso.ofEdge (ν.trans μ.symm)
    (fun e ↦ by
      have h0 := congrArg (fun t : PermutationTriple n ↦ t.σ0 (ν e)) h
      simp only [toPermutationTriple_σ0, permCongr_apply, symm_apply_apply] at h0
      simp [h0])
    (fun e ↦ by
      have h1 := congrArg (fun t : PermutationTriple n ↦ t.σ1 (ν e)) h
      simp only [toPermutationTriple_σ1, permCongr_apply, symm_apply_apply] at h1
      simp [h1])

@[simp]
theorem isoOfToPermutationTripleEq_edge {ν : Γ.E ≃ Fin n} {μ : Δ.E ≃ Fin n}
    (h : Γ.toPermutationTriple ν = Δ.toPermutationTriple μ) :
    (isoOfToPermutationTripleEq h).edge = ν.trans μ.symm :=
  Iso.ofEdge_edge _ _ _

variable (Γ) in
/-- Graph → triple → graph is isomorphic to the identity: a ribbon graph is isomorphic to the
ribbon graph of its triple along any numbering `ν` of its edges, by `ν` itself. -/
noncomputable def isoRibbonGraph (ν : Γ.E ≃ Fin n) :
    Γ.Iso (Γ.toPermutationTriple ν).ribbonGraph :=
  isoOfToPermutationTripleEq (μ := Equiv.refl (Fin n))
    (PermutationTriple.toPermutationTriple_ribbonGraph _).symm

@[simp]
theorem isoRibbonGraph_edge (ν : Γ.E ≃ Fin n) : (Γ.isoRibbonGraph ν).edge = ν :=
  isoOfToPermutationTripleEq_edge _

/-- Two numbered ribbon graphs are isomorphic exactly when their permutation triples are related
by a relabeling of the sheets. -/
theorem nonempty_iso_iff_equivalent (ν : Γ.E ≃ Fin n) (μ : Δ.E ≃ Fin n) :
    Nonempty (Γ.Iso Δ) ↔
      PermutationTriple.Equivalent (Γ.toPermutationTriple ν) (Δ.toPermutationTriple μ) := by
  refine ⟨fun ⟨f⟩ ↦ equivalent_toPermutationTriple_of_iso f ν μ, fun h ↦ ?_⟩
  obtain ⟨τ, hτ⟩ := PermutationTriple.equivalent_iff_exists_smul_eq.mp h
  rw [← toPermutationTriple_trans] at hτ
  exact ⟨isoOfToPermutationTripleEq hτ⟩

end BipartiteRibbonGraph

/-- Two permutation triples have isomorphic ribbon graphs exactly when they are related by a
relabeling of the sheets. -/
theorem PermutationTriple.nonempty_iso_ribbonGraph_iff {n : ℕ} {t t' : PermutationTriple n} :
    Nonempty (t.ribbonGraph.Iso t'.ribbonGraph) ↔ t.Equivalent t' := by
  rw [BipartiteRibbonGraph.nonempty_iso_iff_equivalent (Equiv.refl (Fin n)) (Equiv.refl (Fin n)),
    toPermutationTriple_ribbonGraph, toPermutationTriple_ribbonGraph]

namespace BipartiteRibbonGraph

variable {n : ℕ}

/-- Isomorphism of bipartite ribbon graphs with `n` edges, as an equivalence relation. -/
def isoSetoid (n : ℕ) : Setoid {Γ : BipartiteRibbonGraph.{u} // Fintype.card Γ.E = n} where
  r Γ Δ := Nonempty (Γ.1.Iso Δ.1)
  iseqv := ⟨fun Γ ↦ ⟨Iso.refl Γ.1⟩, fun ⟨f⟩ ↦ ⟨f.symm⟩, fun ⟨f⟩ ⟨g⟩ ↦ ⟨f.trans g⟩⟩

theorem isoSetoid_r {Γ Δ : {Γ : BipartiteRibbonGraph.{u} // Fintype.card Γ.E = n}} :
    (isoSetoid n).r Γ Δ ↔ Nonempty (Γ.1.Iso Δ.1) := Iff.rfl

/-- Isomorphism classes of bipartite ribbon graphs with `n` edges are isomorphism classes of
degree-`n` permutation triples: a class of graphs goes to the class of the triple of any numbering
of the edges, and a class of triples goes to the class of the (universe-lifted) ribbon graph of any
representative. -/
noncomputable def isoClassEquiv (n : ℕ) :
    Quotient (isoSetoid.{u} n) ≃ PermutationTriple.IsoClass n where
  toFun := Quotient.lift
    (fun Γ ↦ PermutationTriple.IsoClass.mk
      (Γ.1.toPermutationTriple (Fintype.equivFinOfCardEq Γ.2)))
    fun _ _ h ↦ by
      obtain ⟨f⟩ := isoSetoid_r.mp h
      exact PermutationTriple.IsoClass.mk_eq_mk_iff.mpr
        (equivalent_toPermutationTriple_of_iso f _ _)
  invFun := PermutationTriple.IsoClass.lift
    (fun t ↦ ⟦⟨t.ribbonGraph.ulift, t.ribbonGraph.card_E_ulift.trans t.card_E_ribbonGraph⟩⟧)
    fun _ _ h ↦ Quotient.sound <| isoSetoid_r.mpr <|
      (PermutationTriple.nonempty_iso_ribbonGraph_iff.mpr h).map fun f ↦
        (uliftIso _).trans (f.trans (uliftIso _).symm)
  left_inv := Quotient.ind fun Γ ↦ by
    rw [Quotient.lift_mk, PermutationTriple.IsoClass.lift_mk]
    exact Quotient.sound (isoSetoid_r.mpr ⟨(uliftIso _).trans (Γ.1.isoRibbonGraph _).symm⟩)
  right_inv c := by
    obtain ⟨t, rfl⟩ := PermutationTriple.IsoClass.mk_surjective c
    rw [PermutationTriple.IsoClass.lift_mk, Quotient.lift_mk,
      PermutationTriple.IsoClass.mk_eq_mk_iff]
    simpa using equivalent_toPermutationTriple_of_iso t.ribbonGraph.uliftIso _ (Equiv.refl (Fin n))

/-- The class of a ribbon graph is the class of its triple along any numbering of its edges. -/
theorem isoClassEquiv_mk (Γ : {Γ : BipartiteRibbonGraph.{u} // Fintype.card Γ.E = n})
    (ν : Γ.1.E ≃ Fin n) :
    isoClassEquiv n ⟦Γ⟧ = PermutationTriple.IsoClass.mk (Γ.1.toPermutationTriple ν) :=
  PermutationTriple.IsoClass.mk_eq_mk_iff.mpr (Γ.1.equivalent_toPermutationTriple _ ν)

/-- The class of a triple is the class of its (universe-lifted) ribbon graph. -/
@[simp]
theorem isoClassEquiv_symm_mk (t : PermutationTriple n) :
    (isoClassEquiv.{u} n).symm (PermutationTriple.IsoClass.mk t) =
      ⟦⟨t.ribbonGraph.ulift, t.ribbonGraph.card_E_ulift.trans t.card_E_ribbonGraph⟩⟧ :=
  PermutationTriple.IsoClass.lift_mk _ _ t

/-! ### Automorphisms -/

variable (Γ : BipartiteRibbonGraph.{u})

/-- The edge permutation of an automorphism, read through a numbering of the edges, is an
automorphism of the triple. -/
theorem permCongr_edge_mem_automorphismGroup (ν : Γ.E ≃ Fin n) (f : Γ.Aut) :
    ν.permCongr f.edge ∈ (Γ.toPermutationTriple ν).automorphismGroup := by
  rw [PermutationTriple.mem_automorphismGroup_iff, toPermutationTriple_σ0,
    toPermutationTriple_σ1]
  constructor <;> exact Equiv.ext fun i ↦ by
    simp [Perm.inv_def, permCongr_def, f.map_rotB.eq, f.map_rotW.eq]

/-- The automorphism group of a ribbon graph is the automorphism group of its permutation triple,
along any numbering of the edges: an automorphism is determined by its action on the edges, and
an edge permutation extends to an automorphism exactly when it commutes with both rotations. -/
noncomputable def autEquivAutomorphismGroup (ν : Γ.E ≃ Fin n) :
    Γ.Aut ≃* (Γ.toPermutationTriple ν).automorphismGroup where
  toFun f := ⟨ν.permCongr f.edge, Γ.permCongr_edge_mem_automorphismGroup ν f⟩
  invFun τ := Iso.ofEdge (ν.trans ((τ : Perm (Fin n)).trans ν.symm))
    (fun e ↦ by
      have h := congrArg (· (τ.1 (ν e)))
        (PermutationTriple.mem_automorphismGroup_iff.mp τ.2).1
      simp only [toPermutationTriple_σ0, Perm.mul_apply, Perm.inv_def, symm_apply_apply,
        permCongr_apply, symm_apply_apply] at h
      simp [h])
    (fun e ↦ by
      have h := congrArg (· (τ.1 (ν e)))
        (PermutationTriple.mem_automorphismGroup_iff.mp τ.2).2
      simp only [toPermutationTriple_σ1, Perm.mul_apply, Perm.inv_def, symm_apply_apply,
        permCongr_apply, symm_apply_apply] at h
      simp [h])
  left_inv f := Iso.ext <| (Iso.ofEdge_edge _ _ _).trans (Equiv.ext fun e ↦ by simp)
  right_inv τ := Subtype.ext <|
    (congrArg ν.permCongr (Iso.ofEdge_edge _ _ _)).trans (Equiv.ext fun i ↦ by simp)
  map_mul' f g :=
    Subtype.ext <| (congrArg ν.permCongr (Aut.mul_edge f g)).trans (ν.permCongr_mul _ _)

@[simp]
theorem coe_autEquivAutomorphismGroup_apply (ν : Γ.E ≃ Fin n) (f : Γ.Aut) :
    (Γ.autEquivAutomorphismGroup ν f : Perm (Fin n)) = ν.permCongr f.edge := (rfl)

@[simp]
theorem autEquivAutomorphismGroup_symm_apply_edge (ν : Γ.E ≃ Fin n)
    (τ : (Γ.toPermutationTriple ν).automorphismGroup) :
    ((Γ.autEquivAutomorphismGroup ν).symm τ).edge = ν.symm.permCongr τ :=
  Iso.ofEdge_edge _ _ _

end BipartiteRibbonGraph

end TauCeti
