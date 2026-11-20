/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Aut
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# The quotient of a Serre graph by a group action without inversions

Let a group `G` act on a Serre graph `Γ` through a homomorphism `φ : G →* Γ.Aut`. The action is
*without inversions* when no element maps a dart to its reverse. In that case the orbits of
vertices and the orbits of darts form a Serre graph `Γ.quotient φ hφ`, the quotient graph
`G \ Γ`: the source and the reversal of an orbit of darts are computed on representatives, and
the reversal has no fixed orbit exactly because there are no inversions.

The projection `Γ.quotientMap φ hφ` is a morphism of Serre graphs which is surjective on vertices
and on darts, whose fibres are the orbits, and which is invariant under the action. It is
universal with this property: an invariant morphism out of `Γ` factors uniquely through it
(`SerreGraph.quotientLift`, `SerreGraph.quotient_hom_ext`), and invariant functions on vertices
or on darts descend to the quotient (`SerreGraph.quotientLiftV`, `SerreGraph.quotientLiftE`).
Darts lift along the projection with a prescribed source, so the projection is surjective on the
stars of vertices, and the quotient of a connected graph is connected.

The hypothesis on inversions cannot be dropped: a morphism of Serre graphs invariant under an
automorphism forces that automorphism to invert no dart
(`SerreGraph.Aut.smul_ne_rev_of_comp_toHom_eq`).

In Bass–Serre theory, a group acting without inversions on a tree has the quotient graph as the
underlying graph of its quotient graph of groups; for a `G`-tree `T` the construction applies to
the action homomorphism `T.action`, which has no inversions.

## Main declarations

* `TauCeti.SerreGraph.quotient`: the quotient graph of an action without inversions.
* `TauCeti.SerreGraph.quotientMap`: the projection onto the quotient graph.
* `TauCeti.SerreGraph.quotientMap_mapV_eq_iff`, `TauCeti.SerreGraph.quotientMap_mapE_eq_iff`,
  `TauCeti.SerreGraph.quotientMap_mapV_preimage_singleton`,
  `TauCeti.SerreGraph.quotientMap_mapE_preimage_singleton`: the fibres of the projection are the
  orbits.
* `TauCeti.SerreGraph.quotientLiftV`, `TauCeti.SerreGraph.quotientLiftE`: invariant functions on
  vertices and on darts descend to the quotient graph.
* `TauCeti.SerreGraph.quotientLift`: the morphism induced on the quotient by an invariant
  morphism.
* `TauCeti.SerreGraph.exists_quotientMap_mapE_eq_of_src_eq`: lifting of darts with a given source.

## References

* J.-P. Serre, *Trees*, Chapter I, §3.1 (quotient graphs); the quotient graph of groups of an
  action on a tree, which this construction underlies, is Chapter I, §5.4.
* I. Kapovich, R. Weidmann and A. Myasnikov, *Foldings, graphs of groups and the membership
  problem*, Internat. J. Algebra Comput. 15 (2005), §2, Proposition 2.6 (the same application).
-/

public section

universe u v w x

namespace TauCeti
namespace SerreGraph

variable {G : Type*} [Group G] (Γ : SerreGraph.{u, v}) (φ : G →* Γ.Aut)
  (hφ : ∀ (g : G) (e : Γ.E), φ g • e ≠ Γ.rev e)

/-- The quotient graph of a Serre graph by a group acting without inversions. Its vertices are the
orbits of vertices and its darts are the orbits of darts, for the actions of `G` through `φ`; the
source and the reverse of an orbit of darts are the orbits of the source and of the reverse of any
of its members. -/
def quotient : SerreGraph.{u, v} where
  V := @MulAction.orbitRel.Quotient G Γ.V _ (MulAction.compHom Γ.V φ)
  E := @MulAction.orbitRel.Quotient G Γ.E _ (MulAction.compHom Γ.E φ)
  src := Quotient.map Γ.src (by
    rintro _ e ⟨g, rfl⟩
    exact ⟨g, by simp [MulAction.compHom_smul_def]⟩)
  rev := Quotient.map Γ.rev (by
    rintro _ e ⟨g, rfl⟩
    exact ⟨g, by simp [MulAction.compHom_smul_def]⟩)
  rev_rev := by
    rintro ⟨e⟩
    exact congrArg (Quotient.mk _) (Γ.rev_rev e)
  rev_ne := by
    rintro ⟨e⟩ h
    obtain ⟨g, hg⟩ := Quotient.exact h
    exact hφ g e (by simpa [MulAction.compHom_smul_def] using hg)

/-- The projection of a Serre graph onto its quotient by a group acting without inversions,
sending a vertex or a dart to its orbit. -/
def quotientMap : Γ.Hom (Γ.quotient φ hφ) where
  mapV := Quotient.mk _
  mapE := Quotient.mk _
  map_src _ := rfl
  map_rev _ := rfl

variable {Γ φ hφ}

/-- Two vertices have the same image in the quotient graph exactly when they are in the same
orbit. -/
theorem quotientMap_mapV_eq_iff {a b : Γ.V} :
    (Γ.quotientMap φ hφ).mapV a = (Γ.quotientMap φ hφ).mapV b ↔ ∃ g : G, φ g • a = b :=
  eq_comm.trans <| (Quotient.eq (r := @MulAction.orbitRel G Γ.V _ (MulAction.compHom Γ.V φ))).trans
    (by simp [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, MulAction.compHom_smul_def])

/-- Two darts have the same image in the quotient graph exactly when they are in the same
orbit. -/
theorem quotientMap_mapE_eq_iff {e f : Γ.E} :
    (Γ.quotientMap φ hφ).mapE e = (Γ.quotientMap φ hφ).mapE f ↔ ∃ g : G, φ g • e = f :=
  eq_comm.trans <| (Quotient.eq (r := @MulAction.orbitRel G Γ.E _ (MulAction.compHom Γ.E φ))).trans
    (by simp [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, MulAction.compHom_smul_def])

/-- A vertex and its translates have the same image in the quotient graph. -/
@[simp] theorem quotientMap_mapV_smul (g : G) (a : Γ.V) :
    (Γ.quotientMap φ hφ).mapV (φ g • a) = (Γ.quotientMap φ hφ).mapV a :=
  (quotientMap_mapV_eq_iff.mpr ⟨g, rfl⟩).symm

/-- A dart and its translates have the same image in the quotient graph. -/
@[simp] theorem quotientMap_mapE_smul (g : G) (e : Γ.E) :
    (Γ.quotientMap φ hφ).mapE (φ g • e) = (Γ.quotientMap φ hφ).mapE e :=
  (quotientMap_mapE_eq_iff.mpr ⟨g, rfl⟩).symm

/-- The projection onto the quotient graph is invariant under the action. -/
@[simp] theorem quotientMap_comp_toHom (g : G) :
    Hom.comp (Γ.quotientMap φ hφ) (φ g).toHom = Γ.quotientMap φ hφ := by
  ext <;> simp [← Aut.smul_vertex_def, ← Aut.smul_dart_def]

variable (Γ φ hφ) in
/-- Every vertex of the quotient graph is the orbit of a vertex. -/
theorem quotientMap_mapV_surjective : Function.Surjective (Γ.quotientMap φ hφ).mapV :=
  Quotient.mk_surjective

variable (Γ φ hφ) in
/-- Every dart of the quotient graph is the orbit of a dart. -/
theorem quotientMap_mapE_surjective : Function.Surjective (Γ.quotientMap φ hφ).mapE :=
  Quotient.mk_surjective

/-- The fibre of the projection through a vertex is the orbit of that vertex. -/
theorem quotientMap_mapV_preimage_singleton (a : Γ.V) :
    (Γ.quotientMap φ hφ).mapV ⁻¹' {(Γ.quotientMap φ hφ).mapV a} =
      Set.range fun g : G => φ g • a := by
  ext b
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_range]
  exact eq_comm.trans quotientMap_mapV_eq_iff

/-- The fibre of the projection through a dart is the orbit of that dart. -/
theorem quotientMap_mapE_preimage_singleton (e : Γ.E) :
    (Γ.quotientMap φ hφ).mapE ⁻¹' {(Γ.quotientMap φ hφ).mapE e} =
      Set.range fun g : G => φ g • e := by
  ext f
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_range]
  exact eq_comm.trans quotientMap_mapE_eq_iff

/-- The projection is injective on vertices exactly when the group fixes every vertex. -/
theorem quotientMap_mapV_injective_iff :
    Function.Injective (Γ.quotientMap φ hφ).mapV ↔ ∀ (g : G) (a : Γ.V), φ g • a = a :=
  ⟨fun h g a => h (quotientMap_mapV_smul g a), fun h a b hab => by
    obtain ⟨g, rfl⟩ := quotientMap_mapV_eq_iff.mp hab
    exact (h g a).symm⟩

/-- The projection is injective on darts exactly when the group fixes every dart. -/
theorem quotientMap_mapE_injective_iff :
    Function.Injective (Γ.quotientMap φ hφ).mapE ↔ ∀ (g : G) (e : Γ.E), φ g • e = e :=
  ⟨fun h g e => h (quotientMap_mapE_smul g e), fun h e f hef => by
    obtain ⟨g, rfl⟩ := quotientMap_mapE_eq_iff.mp hef
    exact (h g e).symm⟩

/-- A dart of the quotient graph issuing from the orbit of a vertex `a` is the orbit of a dart
issuing from `a`: the projection is surjective on the stars of vertices. -/
theorem exists_quotientMap_mapE_eq_of_src_eq {y : (Γ.quotient φ hφ).E} {a : Γ.V}
    (h : (Γ.quotient φ hφ).src y = (Γ.quotientMap φ hφ).mapV a) :
    ∃ e : Γ.E, Γ.src e = a ∧ (Γ.quotientMap φ hφ).mapE e = y := by
  obtain ⟨e, rfl⟩ := quotientMap_mapE_surjective Γ φ hφ y
  rw [Hom.map_src] at h
  obtain ⟨g, rfl⟩ := quotientMap_mapV_eq_iff.mp h
  exact ⟨φ g • e, Aut.src_smul (φ g) e, quotientMap_mapE_smul g e⟩

/-- A dart of the quotient graph ending at the orbit of a vertex `a` is the orbit of a dart
ending at `a`. -/
theorem exists_quotientMap_mapE_eq_of_tgt_eq {y : (Γ.quotient φ hφ).E} {a : Γ.V}
    (h : (Γ.quotient φ hφ).tgt y = (Γ.quotientMap φ hφ).mapV a) :
    ∃ e : Γ.E, Γ.tgt e = a ∧ (Γ.quotientMap φ hφ).mapE e = y := by
  obtain ⟨e, rfl⟩ := quotientMap_mapE_surjective Γ φ hφ y
  rw [Hom.map_tgt] at h
  obtain ⟨g, rfl⟩ := quotientMap_mapV_eq_iff.mp h
  exact ⟨φ g • e, Aut.tgt_smul (φ g) e, quotientMap_mapE_smul g e⟩

/-- The quotient of a preconnected graph is preconnected. -/
theorem quotient_preconnected (h : Γ.Preconnected) : (Γ.quotient φ hφ).Preconnected :=
  (Γ.quotientMap φ hφ).preconnected_of_surjective (quotientMap_mapV_surjective Γ φ hφ) h

/-- The quotient of a connected graph is connected. -/
theorem quotient_connected (h : Γ.Connected) : (Γ.quotient φ hφ).Connected :=
  (Γ.quotientMap φ hφ).connected_of_surjective (quotientMap_mapV_surjective Γ φ hφ) h

/-! ### Instances on the quotient graph

Finiteness, nonemptiness, emptiness and being a subsingleton pass from the vertices and the darts
of a graph to those of its quotient graph, along the surjective projection. -/

instance [Finite Γ.V] : Finite (Γ.quotient φ hφ).V :=
  Finite.of_surjective _ (quotientMap_mapV_surjective Γ φ hφ)

instance [Finite Γ.E] : Finite (Γ.quotient φ hφ).E :=
  Finite.of_surjective _ (quotientMap_mapE_surjective Γ φ hφ)

instance [Nonempty Γ.V] : Nonempty (Γ.quotient φ hφ).V :=
  .map (Γ.quotientMap φ hφ).mapV inferInstance

instance [Nonempty Γ.E] : Nonempty (Γ.quotient φ hφ).E :=
  .map (Γ.quotientMap φ hφ).mapE inferInstance

instance [IsEmpty Γ.V] : IsEmpty (Γ.quotient φ hφ).V :=
  (quotientMap_mapV_surjective Γ φ hφ).isEmpty

instance [IsEmpty Γ.E] : IsEmpty (Γ.quotient φ hφ).E :=
  (quotientMap_mapE_surjective Γ φ hφ).isEmpty

instance [Subsingleton Γ.V] : Subsingleton (Γ.quotient φ hφ).V :=
  (quotientMap_mapV_surjective Γ φ hφ).subsingleton

instance [Subsingleton Γ.E] : Subsingleton (Γ.quotient φ hφ).E :=
  (quotientMap_mapE_surjective Γ φ hφ).subsingleton

/-! ### The universal property -/

section Lift

variable (hφ) in
/-- A function on vertices which is invariant under the action descends to the vertices of the
quotient graph. -/
def quotientLiftV {β : Sort*} (f : Γ.V → β) (hf : ∀ (g : G) (a : Γ.V), f (φ g • a) = f a) :
    (Γ.quotient φ hφ).V → β :=
  Quotient.lift f (by
    rintro _ a ⟨g, rfl⟩
    simpa [MulAction.compHom_smul_def] using hf g a)

variable (hφ) in
/-- A function on darts which is invariant under the action descends to the darts of the quotient
graph. -/
def quotientLiftE {β : Sort*} (f : Γ.E → β) (hf : ∀ (g : G) (e : Γ.E), f (φ g • e) = f e) :
    (Γ.quotient φ hφ).E → β :=
  Quotient.lift f (by
    rintro _ e ⟨g, rfl⟩
    simpa [MulAction.compHom_smul_def] using hf g e)

@[simp] theorem quotientLiftV_quotientMap {β : Sort*} (f : Γ.V → β)
    (hf : ∀ (g : G) (a : Γ.V), f (φ g • a) = f a) (a : Γ.V) :
    quotientLiftV hφ f hf ((Γ.quotientMap φ hφ).mapV a) = f a := (rfl)

@[simp] theorem quotientLiftE_quotientMap {β : Sort*} (f : Γ.E → β)
    (hf : ∀ (g : G) (e : Γ.E), f (φ g • e) = f e) (e : Γ.E) :
    quotientLiftE hφ f hf ((Γ.quotientMap φ hφ).mapE e) = f e := (rfl)

variable {Δ : SerreGraph.{w, x}}

/-- Two morphisms out of the quotient graph agreeing on the orbits of all vertices and darts are
equal. -/
@[ext (iff := false)] theorem quotient_hom_ext {f₁ f₂ : (Γ.quotient φ hφ).Hom Δ}
    (h : Hom.comp f₁ (Γ.quotientMap φ hφ) = Hom.comp f₂ (Γ.quotientMap φ hφ)) : f₁ = f₂ := by
  refine Hom.ext _ (funext fun a => ?_) (funext fun e => ?_)
  · obtain ⟨a, rfl⟩ := quotientMap_mapV_surjective Γ φ hφ a
    simpa using congrArg (fun k : Γ.Hom Δ => k.mapV a) h
  · obtain ⟨e, rfl⟩ := quotientMap_mapE_surjective Γ φ hφ e
    simpa using congrArg (fun k : Γ.Hom Δ => k.mapE e) h

variable (hφ) in
/-- The universal property of the quotient graph: a morphism invariant under the action induces a
morphism out of the quotient graph. -/
def quotientLift (f : Γ.Hom Δ) (hf : ∀ g : G, Hom.comp f (φ g).toHom = f) :
    (Γ.quotient φ hφ).Hom Δ where
  mapV := quotientLiftV hφ f.mapV fun g a => by
    simpa [Aut.smul_vertex_def] using congrArg (fun k : Γ.Hom Δ => k.mapV a) (hf g)
  mapE := quotientLiftE hφ f.mapE fun g e => by
    simpa [Aut.smul_dart_def] using congrArg (fun k : Γ.Hom Δ => k.mapE e) (hf g)
  map_src y := by
    obtain ⟨e, rfl⟩ := quotientMap_mapE_surjective Γ φ hφ y
    simp
  map_rev y := by
    obtain ⟨e, rfl⟩ := quotientMap_mapE_surjective Γ φ hφ y
    simp [← Hom.map_rev]

variable (f : Γ.Hom Δ) (hf : ∀ g : G, Hom.comp f (φ g).toHom = f)

@[simp] theorem quotientLift_mapV_quotientMap (a : Γ.V) :
    (quotientLift hφ f hf).mapV ((Γ.quotientMap φ hφ).mapV a) = f.mapV a := (rfl)

@[simp] theorem quotientLift_mapE_quotientMap (e : Γ.E) :
    (quotientLift hφ f hf).mapE ((Γ.quotientMap φ hφ).mapE e) = f.mapE e := (rfl)

/-- The morphism induced on the quotient graph composes with the projection to the original
morphism. -/
@[simp] theorem quotientLift_comp_quotientMap :
    Hom.comp (quotientLift hφ f hf) (Γ.quotientMap φ hφ) = f := by
  ext <;> simp

/-- A morphism out of the quotient graph is induced by its composite with the projection. -/
@[simp] theorem quotientLift_comp (k : (Γ.quotient φ hφ).Hom Δ) :
    quotientLift hφ (Hom.comp k (Γ.quotientMap φ hφ))
      (fun g => by rw [← Hom.comp_assoc, quotientMap_comp_toHom]) = k :=
  quotient_hom_ext (quotientLift_comp_quotientMap _ _)

end Lift

/-! ### The trivial action -/

variable (Γ) in
/-- For the trivial action the projection onto the quotient graph is bijective on vertices. -/
theorem quotientMap_one_mapV_bijective
    (h : ∀ (g : G) (e : Γ.E), (1 : G →* Γ.Aut) g • e ≠ Γ.rev e := one_apply_smul_ne_rev Γ G) :
    Function.Bijective (Γ.quotientMap (1 : G →* Γ.Aut) h).mapV :=
  ⟨quotientMap_mapV_injective_iff.mpr fun _ _ => by simp, quotientMap_mapV_surjective _ _ _⟩

variable (Γ) in
/-- For the trivial action the projection onto the quotient graph is bijective on darts. -/
theorem quotientMap_one_mapE_bijective
    (h : ∀ (g : G) (e : Γ.E), (1 : G →* Γ.Aut) g • e ≠ Γ.rev e := one_apply_smul_ne_rev Γ G) :
    Function.Bijective (Γ.quotientMap (1 : G →* Γ.Aut) h).mapE :=
  ⟨quotientMap_mapE_injective_iff.mpr fun _ _ => by simp, quotientMap_mapE_surjective _ _ _⟩

/-- When the group fixes every vertex and every dart, the identity induces a morphism from the
quotient graph back to the graph which is a right inverse of the projection; it is a left inverse
by `SerreGraph.quotientLift_comp_quotientMap`. -/
theorem quotientMap_comp_quotientLift_id
    (hf : ∀ g : G, Hom.comp (Hom.id Γ) (φ g).toHom = Hom.id Γ) :
    Hom.comp (Γ.quotientMap φ hφ) (quotientLift hφ (Hom.id Γ) hf) = Hom.id (Γ.quotient φ hφ) := by
  ext : 1
  rw [← Hom.comp_assoc, quotientLift_comp_quotientMap, Hom.comp_id, Hom.id_comp]

end SerreGraph
end TauCeti
