/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Maps

/-!
# Cores of graphs

A graph `H` is a *core* (`SimpleGraph.IsCore`) when each endomorphism of `H` is bijective. A
finite set `s` of vertices of `G` is a *core retract* of `G` (`SimpleGraph.IsCoreRetract`) when
the induced subgraph `G.induce s` is a core and some homomorphism `G →g G.induce s` fixes each
vertex of `s`.

Two graphs are *homomorphically equivalent* when each maps homomorphically to the other. A core
retract is homomorphically equivalent to its graph, and it represents the homomorphic equivalence
class of the graph up to isomorphism: each graph on a finite type has a core retract, and two
graphs are homomorphically equivalent exactly when their core retracts are isomorphic.

## Main definitions

* `SimpleGraph.IsCore`: each endomorphism of the graph is bijective;
* `SimpleGraph.IsCoreRetract`: a set of vertices whose induced subgraph is a core and onto which
  the graph retracts.

## Main results

* `SimpleGraph.isCore_top`: a complete graph on a finite type is a core;
* `SimpleGraph.Iso.isCore_iff`: a graph isomorphic to a core is a core;
* `SimpleGraph.IsCore.nonempty_iso`: homomorphically equivalent cores are isomorphic when the
  first has finitely many edges;
* `SimpleGraph.exists_isCoreRetract`: each graph on a finite type has a core retract;
* `SimpleGraph.nonempty_hom_and_hom_iff`: two graphs are homomorphically equivalent exactly when
  their core retracts are isomorphic;
* `SimpleGraph.IsCoreRetract.nonempty_iso`: any two core retracts of a graph are isomorphic.

## References

* C. Godsil and G. Royle, *Algebraic Graph Theory*, Graduate Texts in Mathematics 207,
  Springer, 2001, §6.2, pp. 104–105.
-/

public section

open Finset

namespace SimpleGraph

variable {V W : Type*}

/-- A graph is a *core* when each of its endomorphisms is bijective. -/
def IsCore (H : SimpleGraph V) : Prop :=
  ∀ f : H →g H, Function.Bijective f

/-- A set `s` of vertices is a *core retract* of `G` when the induced subgraph `G.induce s` is a
core and `G` retracts onto it: some homomorphism `G →g G.induce s` fixes each vertex of `s`. -/
def IsCoreRetract (G : SimpleGraph V) (s : Finset V) : Prop :=
  (G.induce (s : Set V)).IsCore ∧ ∃ r : G →g G.induce (s : Set V), ∀ x : (s : Set V), r x = x

/-- A graph is a core exactly when each of its endomorphisms is bijective. -/
theorem isCore_iff {H : SimpleGraph V} : H.IsCore ↔ ∀ f : H →g H, Function.Bijective f :=
  Iff.rfl

/-- Each endomorphism of a core is bijective. -/
theorem IsCore.bijective {H : SimpleGraph V} (hH : H.IsCore) (f : H →g H) :
    Function.Bijective f :=
  hH f

/-- A complete graph on a finite type is a core. -/
theorem isCore_top [Finite V] : (⊤ : SimpleGraph V).IsCore := fun f =>
  Finite.injective_iff_bijective.mp (Hom.injective_of_top_hom f)

/-- A graph isomorphic to a core is a core. -/
theorem IsCore.of_iso {H : SimpleGraph V} {K : SimpleGraph W} (hH : H.IsCore) (e : H ≃g K) :
    K.IsCore := by
  intro f
  have hf : ⇑f = e ∘ ((e.symm.toHom.comp f).comp e.toHom) ∘ e.symm := by
    ext x
    simp
  rw [hf]
  exact e.bijective.comp ((hH _).comp e.symm.bijective)

/-- Isomorphic graphs are cores together. -/
theorem Iso.isCore_iff {H : SimpleGraph V} {K : SimpleGraph W} (e : H ≃g K) :
    H.IsCore ↔ K.IsCore :=
  ⟨fun hH => hH.of_iso e, fun hK => hK.of_iso e.symm⟩

/-- **Godsil and Royle, Lemma 6.2.1.** Two cores that map homomorphically to each other are
isomorphic when the first has finitely many edges. -/
theorem IsCore.nonempty_iso {H : SimpleGraph V} {K : SimpleGraph W} [Finite H.edgeSet]
    (hH : H.IsCore) (hK : K.IsCore) (f : H →g K) (g : K →g H) : Nonempty (H ≃g K) := by
  have hgf : Function.Bijective (g ∘ f) := hH (g.comp f)
  have hfg : Function.Bijective (f ∘ g) := hK (f.comp g)
  exact ⟨.ofBijective f ⟨hgf.injective.of_comp, hfg.surjective.of_comp⟩ fun _ _ =>
    ⟨fun h => (Hom.map_adj_iff_of_injective (g.comp f) hgf.injective).mp (g.map_adj h), f.map_adj⟩⟩

/-- A set `s` is a core retract of `G` exactly when `G.induce s` is a core and some homomorphism
`G →g G.induce s` fixes each vertex of `s`. -/
theorem isCoreRetract_iff {G : SimpleGraph V} {s : Finset V} :
    G.IsCoreRetract s ↔ (G.induce (s : Set V)).IsCore ∧
      ∃ r : G →g G.induce (s : Set V), ∀ x : (s : Set V), r x = x :=
  Iff.rfl

/-- A core retract of `G` is a core. -/
theorem IsCoreRetract.isCore {G : SimpleGraph V} {s : Finset V} (hs : G.IsCoreRetract s) :
    (G.induce (s : Set V)).IsCore :=
  hs.1

/-- A graph retracts onto each of its core retracts. -/
theorem IsCoreRetract.exists_retraction {G : SimpleGraph V} {s : Finset V}
    (hs : G.IsCoreRetract s) : ∃ r : G →g G.induce (s : Set V), ∀ x : (s : Set V), r x = x :=
  hs.2

/-- A graph maps homomorphically to each of its core retracts. -/
theorem IsCoreRetract.nonempty_hom {G : SimpleGraph V} {s : Finset V} (hs : G.IsCoreRetract s) :
    Nonempty (G →g G.induce (s : Set V)) :=
  let ⟨r, _⟩ := hs.exists_retraction
  ⟨r⟩

/-- If `G` maps homomorphically to `G.induce s` and to no subgraph induced on fewer vertices, then
`G.induce s` is a core. -/
private theorem isCore_induce_of_forall_card_le {G : SimpleGraph V} {s : Finset V}
    (r : G →g G.induce (s : Set V))
    (hmin : ∀ t : Finset V, Nonempty (G →g G.induce (t : Set V)) → #s ≤ #t) :
    (G.induce (s : Set V)).IsCore := by
  classical
  intro φ
  refine Finite.surjective_iff_bijective.mp fun y => ?_
  by_contra! hy
  -- The vertices of `s` in the image of `φ` form a proper subset `t` of `s`, and `G` maps to
  -- `G.induce t` through `φ ∘ r`.
  let t : Finset V := {x ∈ s | x ∈ Set.range fun a => (φ a : V)}
  have hts : t ⊂ s := by
    refine (ssubset_iff_of_subset (filter_subset _ _)).mpr ⟨y, y.property, ?_⟩
    simp only [mem_filter, Set.mem_range, not_and, not_exists]
    exact fun _ a ha => hy a (Subtype.ext ha)
  let ψ : G →g G.induce (t : Set V) :=
    { toFun := fun x => ⟨φ (r x), mem_filter.mpr ⟨(φ (r x)).property, r x, rfl⟩⟩
      map_rel' := fun h => induce_adj.mpr (induce_adj.mp (φ.map_adj (r.map_adj h))) }
  exact (card_lt_card hts).not_ge (hmin t ⟨ψ⟩)

/-- **Godsil and Royle, Lemma 6.2.2.** Each graph on a finite type has a core retract. -/
theorem exists_isCoreRetract [Finite V] (G : SimpleGraph V) :
    ∃ s : Finset V, G.IsCoreRetract s := by
  have := Fintype.ofFinite V
  -- Choose `s` of least size such that `G` maps to `G.induce s`.
  obtain ⟨s, ⟨r⟩, hmin⟩ := (measure (#· : Finset V → ℕ)).wf.has_min
    {s | Nonempty (G →g G.induce (s : Set V))}
    ⟨univ, ⟨{ toFun := fun x => ⟨x, by simp⟩, map_rel' := fun h => induce_adj.mpr h }⟩⟩
  have hcore := isCore_induce_of_forall_card_le r fun t ht => not_lt.mp (hmin t ht)
  -- The endomorphism `r ∘ ι` of the core, for the inclusion `ι`, is an automorphism `α`, and
  -- `α⁻¹ ∘ r` is a retraction onto `s`: for `x` in `s`, `r x` is `α x` by the definition of `ρ`.
  let ρ := r.comp (Embedding.induce (G := G) (s : Set V)).toHom
  let α : G.induce (s : Set V) ≃g G.induce (s : Set V) :=
    .ofBijective ρ (hcore ρ) fun _ _ => ρ.map_adj_iff_of_injective (hcore ρ).injective
  exact ⟨s, hcore, α.symm.toHom.comp r, fun x => α.symm_apply_apply x⟩

/-- **Godsil and Royle, Lemmas 6.2.2 and 6.2.3.** Two graphs map homomorphically to each other
exactly when their core retracts are isomorphic. -/
theorem nonempty_hom_and_hom_iff {G : SimpleGraph V} {H : SimpleGraph W} {s : Finset V}
    {t : Finset W} (hs : G.IsCoreRetract s) (ht : H.IsCoreRetract t) :
    (Nonempty (G →g H) ∧ Nonempty (H →g G)) ↔
      Nonempty (G.induce (s : Set V) ≃g H.induce (t : Set W)) := by
  obtain ⟨rs⟩ := hs.nonempty_hom
  obtain ⟨rt⟩ := ht.nonempty_hom
  let ιs := (Embedding.induce (G := G) (s : Set V)).toHom
  let ιt := (Embedding.induce (G := H) (t : Set W)).toHom
  constructor
  · rintro ⟨⟨φ⟩, ⟨ψ⟩⟩
    exact hs.isCore.nonempty_iso ht.isCore ((rt.comp φ).comp ιs) ((rs.comp ψ).comp ιt)
  · rintro ⟨e⟩
    exact ⟨⟨(ιt.comp e.toHom).comp rs⟩, ⟨(ιs.comp e.symm.toHom).comp rt⟩⟩

/-- Any two core retracts of a graph are isomorphic. -/
theorem IsCoreRetract.nonempty_iso {G : SimpleGraph V} {s t : Finset V} (hs : G.IsCoreRetract s)
    (ht : G.IsCoreRetract t) : Nonempty (G.induce (s : Set V) ≃g G.induce (t : Set V)) :=
  (nonempty_hom_and_hom_iff hs ht).mp ⟨⟨Hom.id⟩, ⟨Hom.id⟩⟩

end SimpleGraph
