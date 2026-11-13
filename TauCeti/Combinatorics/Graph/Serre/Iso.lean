/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Basic

/-!
# Isomorphisms of Serre graphs

An isomorphism of Serre graphs is a pair of bijections, of the vertices and of the darts,
commuting with the source and reversal maps. Unlike a morphism it can be inverted, so it transports
every notion defined from the incidence structure in both directions: the geometric edges
(`SerreGraph.Iso.geomEdgeEquiv`), the targets of darts, and connectedness
(`SerreGraph.Iso.connected_iff`).

Isomorphisms between two different graphs are what compares, for instance, the link of a vertex of
a polygonal complex with the link of the corresponding vertex of an isomorphic complex.

## Main definitions

* `TauCeti.SerreGraph.Iso`: isomorphisms of Serre graphs, with `SerreGraph.Iso.refl`,
  `SerreGraph.Iso.symm` and `SerreGraph.Iso.trans`, which satisfy the groupoid laws
  (`SerreGraph.Iso.trans_assoc`, `SerreGraph.Iso.refl_trans`, `SerreGraph.Iso.trans_refl`,
  `SerreGraph.Iso.symm_trans_self`, `SerreGraph.Iso.self_trans_symm`).
* `TauCeti.SerreGraph.Iso.toHom`: the underlying morphism, and conversely
  `TauCeti.SerreGraph.Hom.toIso`: a morphism bijective on vertices and darts as an isomorphism.
* `TauCeti.SerreGraph.Iso.geomEdgeEquiv`: the induced bijection of geometric edges, compatible
  with identities, inverses and composites.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.1.
-/

public section

universe u v w x y z u' v'

namespace TauCeti

namespace SerreGraph

/-- An isomorphism of Serre graphs: bijections of the vertices and of the darts preserving sources
and reversal. -/
structure Iso (Γ : SerreGraph.{u, v}) (Δ : SerreGraph.{w, x}) where
  /-- The bijection of vertices. -/
  equivV : Γ.V ≃ Δ.V
  /-- The bijection of darts. -/
  equivE : Γ.E ≃ Δ.E
  /-- Sources are preserved. -/
  map_src : ∀ e, Δ.src (equivE e) = equivV (Γ.src e)
  /-- Reversal is preserved. -/
  map_rev : ∀ e, equivE (Γ.rev e) = Δ.rev (equivE e)

namespace Iso

attribute [simp] map_src map_rev

variable {Γ : SerreGraph.{u, v}} {Δ : SerreGraph.{w, x}} {Θ : SerreGraph.{y, z}}

@[ext] theorem ext {φ ψ : Γ.Iso Δ} (hV : ∀ v, φ.equivV v = ψ.equivV v)
    (hE : ∀ e, φ.equivE e = ψ.equivE e) : φ = ψ := by
  obtain ⟨φV, φE, _, _⟩ := φ
  obtain ⟨ψV, ψE, _, _⟩ := ψ
  obtain rfl : φV = ψV := Equiv.ext hV
  obtain rfl : φE = ψE := Equiv.ext hE
  rfl

/-- The morphism underlying an isomorphism. -/
def toHom (φ : Γ.Iso Δ) : Γ.Hom Δ where
  mapV := φ.equivV
  mapE := φ.equivE
  map_src := φ.map_src
  map_rev := φ.map_rev

@[simp] theorem toHom_mapV (φ : Γ.Iso Δ) : φ.toHom.mapV = φ.equivV := (rfl)

@[simp] theorem toHom_mapE (φ : Γ.Iso Δ) : φ.toHom.mapE = φ.equivE := (rfl)

theorem toHom_mapE_injective (φ : Γ.Iso Δ) : Function.Injective φ.toHom.mapE :=
  φ.equivE.injective

/-- An isomorphism is determined by its underlying morphism. -/
theorem toHom_injective : Function.Injective (toHom : Γ.Iso Δ → Γ.Hom Δ) := fun φ ψ h =>
  ext (fun v => by simpa using congrFun (congrArg Hom.mapV h) v)
    (fun e => by simpa using congrFun (congrArg Hom.mapE h) e)

/-- Targets are preserved. -/
@[simp] theorem map_tgt (φ : Γ.Iso Δ) (e : Γ.E) : Δ.tgt (φ.equivE e) = φ.equivV (Γ.tgt e) :=
  φ.toHom.map_tgt Γ e

/-- The identity isomorphism. -/
@[refl] def refl (Γ : SerreGraph.{u, v}) : Γ.Iso Γ where
  equivV := Equiv.refl _
  equivE := Equiv.refl _
  map_src _ := rfl
  map_rev _ := rfl

@[simp] theorem refl_equivV (Γ : SerreGraph.{u, v}) : (refl Γ).equivV = Equiv.refl _ := (rfl)

@[simp] theorem refl_equivE (Γ : SerreGraph.{u, v}) : (refl Γ).equivE = Equiv.refl _ := (rfl)

@[simp] theorem refl_toHom (Γ : SerreGraph.{u, v}) : (refl Γ).toHom = Hom.id Γ := by
  ext <;> simp

/-- The inverse isomorphism. -/
@[symm] def symm (φ : Γ.Iso Δ) : Δ.Iso Γ where
  equivV := φ.equivV.symm
  equivE := φ.equivE.symm
  map_src e := by rw [Equiv.eq_symm_apply, ← φ.map_src, Equiv.apply_symm_apply]
  map_rev e := by rw [Equiv.symm_apply_eq, φ.map_rev, Equiv.apply_symm_apply]

@[simp] theorem symm_equivV (φ : Γ.Iso Δ) : φ.symm.equivV = φ.equivV.symm := (rfl)

@[simp] theorem symm_equivE (φ : Γ.Iso Δ) : φ.symm.equivE = φ.equivE.symm := (rfl)

@[simp] theorem symm_symm (φ : Γ.Iso Δ) : φ.symm.symm = φ := (rfl)

@[simp] theorem src_equivE_symm (φ : Γ.Iso Δ) (e : Δ.E) :
    Γ.src (φ.equivE.symm e) = φ.equivV.symm (Δ.src e) :=
  φ.symm.map_src e

@[simp] theorem equivE_symm_rev (φ : Γ.Iso Δ) (e : Δ.E) :
    φ.equivE.symm (Δ.rev e) = Γ.rev (φ.equivE.symm e) :=
  φ.symm.map_rev e

@[simp] theorem tgt_equivE_symm (φ : Γ.Iso Δ) (e : Δ.E) :
    Γ.tgt (φ.equivE.symm e) = φ.equivV.symm (Δ.tgt e) :=
  φ.symm.map_tgt e

/-- The composite of two isomorphisms, `φ` followed by `ψ`. -/
@[trans] def trans (φ : Γ.Iso Δ) (ψ : Δ.Iso Θ) : Γ.Iso Θ where
  equivV := φ.equivV.trans ψ.equivV
  equivE := φ.equivE.trans ψ.equivE
  map_src e := by simp
  map_rev e := by simp

@[simp] theorem trans_equivV (φ : Γ.Iso Δ) (ψ : Δ.Iso Θ) :
    (φ.trans ψ).equivV = φ.equivV.trans ψ.equivV := (rfl)

@[simp] theorem trans_equivE (φ : Γ.Iso Δ) (ψ : Δ.Iso Θ) :
    (φ.trans ψ).equivE = φ.equivE.trans ψ.equivE := (rfl)

@[simp] theorem trans_toHom (φ : Γ.Iso Δ) (ψ : Δ.Iso Θ) :
    (φ.trans ψ).toHom = ψ.toHom.comp φ.toHom := by
  ext <;> simp

@[simp] theorem toHom_comp_symm_toHom (φ : Γ.Iso Δ) : φ.toHom.comp φ.symm.toHom = Hom.id Δ := by
  ext <;> simp

@[simp] theorem symm_toHom_comp_toHom (φ : Γ.Iso Δ) : φ.symm.toHom.comp φ.toHom = Hom.id Γ := by
  ext <;> simp

@[simp] theorem refl_symm (Γ : SerreGraph.{u, v}) : (refl Γ).symm = refl Γ := (rfl)

@[simp] theorem symm_trans (φ : Γ.Iso Δ) (ψ : Δ.Iso Θ) :
    (φ.trans ψ).symm = ψ.symm.trans φ.symm := (rfl)

@[simp] theorem refl_trans (φ : Γ.Iso Δ) : (refl Γ).trans φ = φ := by ext <;> simp

@[simp] theorem trans_refl (φ : Γ.Iso Δ) : φ.trans (refl Δ) = φ := by ext <;> simp

@[simp] theorem symm_trans_self (φ : Γ.Iso Δ) : φ.symm.trans φ = refl Δ := by ext <;> simp

@[simp] theorem self_trans_symm (φ : Γ.Iso Δ) : φ.trans φ.symm = refl Γ := by ext <;> simp

theorem trans_assoc {Λ : SerreGraph.{u', v'}} (φ : Γ.Iso Δ) (ψ : Δ.Iso Θ) (χ : Θ.Iso Λ) :
    (φ.trans ψ).trans χ = φ.trans (ψ.trans χ) := (rfl)

/-- The bijection of geometric edges induced by an isomorphism. -/
def geomEdgeEquiv (φ : Γ.Iso Δ) : Γ.GeomEdge ≃ Δ.GeomEdge :=
  GeomEdge.congr Γ φ.equivE φ.map_rev

@[simp] theorem geomEdgeEquiv_toGeomEdge (φ : Γ.Iso Δ) (e : Γ.E) :
    φ.geomEdgeEquiv (Γ.toGeomEdge e) = Δ.toGeomEdge (φ.equivE e) :=
  GeomEdge.congr_toGeomEdge ..

@[simp] theorem geomEdgeEquiv_symm_toGeomEdge (φ : Γ.Iso Δ) (e : Δ.E) :
    φ.geomEdgeEquiv.symm (Δ.toGeomEdge e) = Γ.toGeomEdge (φ.equivE.symm e) :=
  GeomEdge.congr_symm_toGeomEdge ..

@[simp] theorem geomEdgeEquiv_refl (Γ : SerreGraph.{u, v}) :
    (refl Γ).geomEdgeEquiv = Equiv.refl Γ.GeomEdge :=
  Equiv.ext fun x => by obtain ⟨e, rfl⟩ := Γ.toGeomEdge_surjective x; simp

@[simp] theorem geomEdgeEquiv_symm (φ : Γ.Iso Δ) : φ.symm.geomEdgeEquiv = φ.geomEdgeEquiv.symm :=
  Equiv.ext fun x => by obtain ⟨e, rfl⟩ := Δ.toGeomEdge_surjective x; simp

@[simp] theorem geomEdgeEquiv_trans (φ : Γ.Iso Δ) (ψ : Δ.Iso Θ) :
    (φ.trans ψ).geomEdgeEquiv = φ.geomEdgeEquiv.trans ψ.geomEdgeEquiv :=
  Equiv.ext fun x => by obtain ⟨e, rfl⟩ := Γ.toGeomEdge_surjective x; simp

/-- Isomorphic Serre graphs are preconnected together. -/
theorem preconnected_iff (φ : Γ.Iso Δ) : Δ.Preconnected ↔ Γ.Preconnected :=
  ⟨φ.symm.toHom.preconnected_of_surjective φ.equivV.symm.surjective,
    φ.toHom.preconnected_of_surjective φ.equivV.surjective⟩

/-- Isomorphic Serre graphs are connected together. -/
theorem connected_iff (φ : Γ.Iso Δ) : Δ.Connected ↔ Γ.Connected :=
  ⟨φ.symm.toHom.connected_of_surjective φ.equivV.symm.surjective,
    φ.toHom.connected_of_surjective φ.equivV.surjective⟩

end Iso

variable {Γ : SerreGraph.{u, v}} {Δ : SerreGraph.{w, x}}

/-- A morphism of Serre graphs which is bijective on vertices and on darts is an isomorphism. -/
noncomputable def Hom.toIso (f : Γ.Hom Δ) (hV : Function.Bijective f.mapV)
    (hE : Function.Bijective f.mapE) : Γ.Iso Δ where
  equivV := .ofBijective _ hV
  equivE := .ofBijective _ hE
  map_src := f.map_src
  map_rev := f.map_rev

@[simp] theorem Hom.toIso_equivV_apply (f : Γ.Hom Δ) (hV : Function.Bijective f.mapV)
    (hE : Function.Bijective f.mapE) (v : Γ.V) : (f.toIso hV hE).equivV v = f.mapV v := (rfl)

@[simp] theorem Hom.toIso_equivE_apply (f : Γ.Hom Δ) (hV : Function.Bijective f.mapV)
    (hE : Function.Bijective f.mapE) (e : Γ.E) : (f.toIso hV hE).equivE e = f.mapE e := (rfl)

@[simp] theorem Hom.toIso_toHom (f : Γ.Hom Δ) (hV : Function.Bijective f.mapV)
    (hE : Function.Bijective f.mapE) : (f.toIso hV hE).toHom = f := (rfl)

end SerreGraph

end TauCeti
