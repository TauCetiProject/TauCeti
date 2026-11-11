/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Line
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
(`SerreGraph.quotientLift`, `SerreGraph.quotient_hom_ext`). Darts lift along the projection with
a prescribed source, so the projection is surjective on the stars of vertices, and the quotient
of a connected graph is connected.

The hypothesis on inversions cannot be dropped: a morphism of Serre graphs invariant under an
automorphism forces that automorphism to invert no dart
(`SerreGraph.Aut.smul_ne_rev_of_comp_toHom_eq`), so that, for instance, no morphism out of the
segment is invariant under the exchange of its two vertices.

## Main declarations

* `TauCeti.SerreGraph.quotient`: the quotient graph of an action without inversions.
* `TauCeti.SerreGraph.quotientMap`: the projection onto the quotient graph.
* `TauCeti.SerreGraph.quotientMap_mapV_eq_iff`, `TauCeti.SerreGraph.quotientMap_mapE_eq_iff`,
  `TauCeti.SerreGraph.quotientMap_mapV_preimage_singleton`,
  `TauCeti.SerreGraph.quotientMap_mapE_preimage_singleton`: the fibres of the projection are the
  orbits.
* `TauCeti.SerreGraph.quotientLift`: the morphism induced on the quotient by an invariant
  morphism.
* `TauCeti.SerreGraph.exists_quotientMap_mapE_eq_of_src_eq`: lifting of darts with a given source.
* `TauCeti.SerreGraph.lineQuotientDartEquiv`: the quotient of the line by its translations has a
  single vertex and a single pair of mutually reverse darts.

## References

* J.-P. Serre, *Trees*, Chapter I, §3.1 (quotient graphs) and §5.4.
* I. Kapovich, R. Weidmann and A. Myasnikov, *Foldings, graphs of groups and the membership
  problem*, Internat. J. Algebra Comput. 15 (2005), §2, Proposition 2.6.
-/

public section

universe u v w x

namespace TauCeti
namespace SerreGraph

/-- A morphism of Serre graphs invariant under an automorphism forces that automorphism to map no
dart to its reverse: an inversion admits no invariant morphism, hence no quotient graph. -/
theorem Aut.smul_ne_rev_of_comp_toHom_eq {Γ : SerreGraph.{u, v}} {Δ : SerreGraph.{w, x}}
    (f : Γ.Hom Δ) (g : Γ.Aut) (h : Hom.comp f g.toHom = f) (e : Γ.E) : g • e ≠ Γ.rev e := by
  intro he
  have h₁ : f.mapE (g • e) = f.mapE e := by
    simpa using congrArg (fun k : Γ.Hom Δ => k.mapE e) h
  rw [he, f.map_rev] at h₁
  exact Δ.rev_ne _ h₁

/-- No morphism out of the segment is invariant under the exchange of its two vertices, which
inverts the edge: the segment has no quotient graph by this automorphism. -/
theorem segment_comp_segmentSwap_toHom_ne {Δ : SerreGraph.{w, x}} (f : segment.Hom Δ) :
    Hom.comp f segmentSwap.toHom ≠ f := fun h =>
  Aut.smul_ne_rev_of_comp_toHom_eq f segmentSwap h true (segmentSwap_smul true)

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
    exact ⟨g, (Aut.src_smul (φ g) e).symm⟩)
  rev := Quotient.map Γ.rev (by
    rintro _ e ⟨g, rfl⟩
    exact ⟨g, (Aut.rev_smul (φ g) e).symm⟩)
  rev_rev := by
    rintro ⟨e⟩
    exact congrArg (Quotient.mk _) (Γ.rev_rev e)
  rev_ne := by
    rintro ⟨e⟩ h
    obtain ⟨g, hg⟩ := Quotient.exact h
    exact hφ g e hg

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
  eq_comm.trans (Quotient.eq (r := @MulAction.orbitRel G Γ.V _ (MulAction.compHom Γ.V φ)))

/-- Two darts have the same image in the quotient graph exactly when they are in the same
orbit. -/
theorem quotientMap_mapE_eq_iff {e f : Γ.E} :
    (Γ.quotientMap φ hφ).mapE e = (Γ.quotientMap φ hφ).mapE f ↔ ∃ g : G, φ g • e = f :=
  eq_comm.trans (Quotient.eq (r := @MulAction.orbitRel G Γ.E _ (MulAction.compHom Γ.E φ)))

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
  ext <;> simp

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

/-! ### The universal property -/

section Lift

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
  mapV := Quotient.lift f.mapV (by
    rintro _ a ⟨g, rfl⟩
    exact (by simpa using congrArg (fun k : Γ.Hom Δ => k.mapV a) (hf g) :
      f.mapV (φ g • a) = f.mapV a))
  mapE := Quotient.lift f.mapE (by
    rintro _ e ⟨g, rfl⟩
    exact (by simpa using congrArg (fun k : Γ.Hom Δ => k.mapE e) (hf g) :
      f.mapE (φ g • e) = f.mapE e))
  map_src := by
    rintro ⟨e⟩
    exact f.map_src e
  map_rev := by
    rintro ⟨e⟩
    exact f.map_rev e

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
/-- For the trivial action the projection onto the quotient graph is bijective on vertices: the
quotient is the graph itself. -/
theorem quotientMap_one_mapV_bijective (h : ∀ (g : G) (e : Γ.E), (1 : G →* Γ.Aut) g • e ≠ Γ.rev e) :
    Function.Bijective (Γ.quotientMap (1 : G →* Γ.Aut) h).mapV :=
  ⟨quotientMap_mapV_injective_iff.mpr fun _ _ => one_smul _ _, quotientMap_mapV_surjective _ _ _⟩

variable (Γ) in
/-- For the trivial action the projection onto the quotient graph is bijective on darts. -/
theorem quotientMap_one_mapE_bijective (h : ∀ (g : G) (e : Γ.E), (1 : G →* Γ.Aut) g • e ≠ Γ.rev e) :
    Function.Bijective (Γ.quotientMap (1 : G →* Γ.Aut) h).mapE :=
  ⟨quotientMap_mapE_injective_iff.mpr fun _ _ => one_smul _ _, quotientMap_mapE_surjective _ _ _⟩

/-- When the group fixes every vertex and every dart, the identity induces a morphism from the
quotient graph back to the graph which is inverse to the projection. -/
theorem quotientMap_comp_quotientLift_id
    (hf : ∀ g : G, Hom.comp (Hom.id Γ) (φ g).toHom = Hom.id Γ) :
    Hom.comp (Γ.quotientMap φ hφ) (quotientLift hφ (Hom.id Γ) hf) = Hom.id (Γ.quotient φ hφ) := by
  ext : 1
  rw [← Hom.comp_assoc, quotientLift_comp_quotientMap, Hom.comp_id, Hom.id_comp]

/-! ### The quotient of the line by its translations -/

/-- The quotient of the line by its translations has a single vertex. -/
instance : Unique (line.quotient lineShift lineShift_smul_ne_rev).V where
  default := (line.quotientMap lineShift lineShift_smul_ne_rev).mapV (lineVertexEquiv.symm 0)
  uniq a := by
    obtain ⟨a, rfl⟩ := quotientMap_mapV_surjective _ _ _ a
    refine quotientMap_mapV_eq_iff.mpr
      ⟨Multiplicative.ofAdd (-lineVertexEquiv a), lineVertexEquiv.injective ?_⟩
    rw [lineVertexEquiv_lineShift_smul, toAdd_ofAdd, neg_add_cancel, Equiv.apply_symm_apply]

/-- The darts of the quotient of the line by its translations are its two orientations: the
quotient is a loop, a single vertex with one pair of mutually reverse darts. -/
def lineQuotientDartEquiv : (line.quotient lineShift lineShift_smul_ne_rev).E ≃ Bool where
  toFun := Quotient.lift (fun e : ℤ × Bool => e.2) (by
    -- Translation does not change the orientation of a dart.
    rintro _ e ⟨k, rfl⟩
    have h : (lineShift k • e).2 = e.2 := by rw [lineShift_smul_dart]
    exact h)
  invFun d := (line.quotientMap lineShift lineShift_smul_ne_rev).mapE (0, d)
  left_inv y := by
    obtain ⟨e, rfl⟩ := quotientMap_mapE_surjective _ _ _ y
    exact quotientMap_mapE_eq_iff.mpr ⟨Multiplicative.ofAdd e.1,
      (lineShift_smul_dart _ _).trans (Prod.ext (by simp) rfl)⟩
  right_inv _ := rfl

/-- The orbit of a dart of the line under translation is its orientation. -/
@[simp] theorem lineQuotientDartEquiv_quotientMap (e : line.E) :
    lineQuotientDartEquiv ((line.quotientMap lineShift lineShift_smul_ne_rev).mapE e) =
      Prod.snd e := (rfl)

@[simp] theorem lineQuotientDartEquiv_symm_apply (d : Bool) :
    lineQuotientDartEquiv.symm d =
      (line.quotientMap lineShift lineShift_smul_ne_rev).mapE (0, d) := (rfl)

/-- Reversal exchanges the two darts of the quotient of the line by its translations. -/
@[simp] theorem lineQuotientDartEquiv_rev (y : (line.quotient lineShift lineShift_smul_ne_rev).E) :
    lineQuotientDartEquiv ((line.quotient lineShift lineShift_smul_ne_rev).rev y) =
      !lineQuotientDartEquiv y := by
  obtain ⟨e, rfl⟩ := quotientMap_mapE_surjective _ _ _ y
  rw [← Hom.map_rev, lineQuotientDartEquiv_quotientMap, lineQuotientDartEquiv_quotientMap]
  exact congrArg Prod.snd (line_rev e)

end SerreGraph
end TauCeti
