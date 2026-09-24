/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Cohomology.Basic
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Relabelling graph cohomology

A graph isomorphism transports one-cochains by evaluating at inverse-image darts. This
transport sends vertex coboundaries to vertex coboundaries and therefore induces an
isomorphism on first cohomology. The construction is useful when graph-indexed algebraic
parameters are classified by their cohomology classes.
-/

public section

namespace TauCeti

open SimpleGraph

private theorem mapDart_symm {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (d : G.Dart) : f.mapDart d.symm = (f.mapDart d).symm := by
  apply Dart.ext
  cases d.toProd with
  | mk _ _ => rfl

private theorem mapDart_comp {V W X : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {I : SimpleGraph X} (f : G →g H) (g : H →g I) (d : G.Dart) :
    (g.comp f).mapDart d = g.mapDart (f.mapDart d) := by
  apply Dart.ext
  rfl

private theorem mapDart_refl {V : Type*} {G : SimpleGraph V} (d : G.Dart) :
    (Iso.refl : G ≃g G).toHom.mapDart d = d := by
  apply Dart.ext
  rfl

private theorem mapDart_iso_symm {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (d : G.Dart) :
    e.symm.toHom.mapDart (e.toHom.mapDart d) = d := by
  rw [← mapDart_comp, e.symm_toHom_comp_toHom]
  exact mapDart_refl d

private theorem mapDart_iso_comp {V W X : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {I : SimpleGraph X} (e : G ≃g H) (f : H ≃g I) (d : I.Dart) :
    (f.comp e).symm.toHom.mapDart d =
      e.symm.toHom.mapDart (f.symm.toHom.mapDart d) := by
  have h : (f.comp e).symm.toHom = e.symm.toHom.comp f.symm.toHom := by
    ext v
    simp
  rw [h]
  exact mapDart_comp _ _ d

end TauCeti

namespace SimpleGraph

open TauCeti

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
  (A : Type*) [CommGroup A]

/-- Relabel a graph one-cochain along an isomorphism of graphs. -/
def oneCochainsRelabel (e : G ≃g H) : G.oneCochains A ≃* H.oneCochains A where
  toFun σ := ⟨fun d => (σ : G.Dart → A) (e.symm.toHom.mapDart d), by
    rw [mem_oneCochains_iff]
    intro d
    rw [mapDart_symm]
    exact (mem_oneCochains_iff.mp σ.property) (e.symm.toHom.mapDart d)⟩
  invFun σ := ⟨fun d => (σ : H.Dart → A) (e.toHom.mapDart d), by
    rw [mem_oneCochains_iff]
    intro d
    rw [mapDart_symm]
    exact (mem_oneCochains_iff.mp σ.property) (e.toHom.mapDart d)⟩
  left_inv σ := by
    ext d
    dsimp
    apply congrArg (σ : G.Dart → A)
    exact mapDart_iso_symm e d
  right_inv σ := by
    ext d
    dsimp
    apply congrArg (σ : H.Dart → A)
    exact mapDart_iso_symm e.symm d
  map_mul' σ τ := by
    ext d
    rfl

/-- Relabelling a one-cochain evaluates it on the inverse-image dart. -/
@[simp]
theorem oneCochainsRelabel_apply (e : G ≃g H) (σ : G.oneCochains A) (d : H.Dart) :
    (oneCochainsRelabel A e σ : H.Dart → A) d =
      (σ : G.Dart → A) (e.symm.toHom.mapDart d) := by
  simp [oneCochainsRelabel]

/-- Relabelling by the identity graph isomorphism fixes every one-cochain. -/
@[simp]
theorem oneCochainsRelabel_refl :
    oneCochainsRelabel A (Iso.refl : G ≃g G) = MulEquiv.refl (G.oneCochains A) := by
  ext σ d
  simp only [oneCochainsRelabel_apply, MulEquiv.refl_apply]
  apply congrArg (σ : G.Dart → A)
  exact mapDart_refl d

/-- Successive graph relabellings compose on one-cochains. -/
theorem oneCochainsRelabel_comp {X : Type*} {I : SimpleGraph X}
    (e : G ≃g H) (f : H ≃g I) :
    oneCochainsRelabel A (f.comp e) =
      (oneCochainsRelabel A e).trans (oneCochainsRelabel A f) := by
  ext σ d
  simp only [oneCochainsRelabel_apply, MulEquiv.trans_apply]
  apply congrArg (σ : G.Dart → A)
  exact mapDart_iso_comp e f d

/-- Relabelling carries the coboundary of a vertex function to the coboundary of its
inverse-image relabelling. -/
@[simp]
theorem oneCochainsRelabel_coboundary (e : G ≃g H) (φ : V → A) :
    oneCochainsRelabel A e (G.coboundary A φ) =
      H.coboundary A (φ ∘ e.symm) := by
  ext d
  simp [oneCochainsRelabel_apply, SimpleGraph.Hom.mapDart, Function.comp_def]

/-- A graph isomorphism identifies the first cohomology groups of its two graphs. -/
def firstCohomologyRelabel (e : G ≃g H) : G.FirstCohomology A ≃* H.FirstCohomology A := by
  apply FirstCohomology.congr (oneCochainsRelabel A e)
  apply le_antisymm
  · rintro σ ⟨τ, ⟨φ, rfl⟩, rfl⟩
    exact ⟨φ ∘ e.symm, (oneCochainsRelabel_coboundary A e φ).symm⟩
  · rintro σ ⟨ψ, rfl⟩
    refine ⟨G.coboundary A (ψ ∘ e), ⟨ψ ∘ e, rfl⟩, ?_⟩
    -- `Subgroup.map` coerces the equivalence to its underlying monoid homomorphism.
    change oneCochainsRelabel A e (G.coboundary A (ψ ∘ e)) = H.coboundary A ψ
    rw [oneCochainsRelabel_coboundary]
    congr 1
    funext v
    simp

/-- The relabelling isomorphism takes the class of a cochain to the class of its relabelling. -/
@[simp]
theorem firstCohomologyRelabel_mk (e : G ≃g H) (σ : G.oneCochains A) :
    firstCohomologyRelabel A e (FirstCohomology.mk G A σ) =
      FirstCohomology.mk H A (oneCochainsRelabel A e σ) := by
  exact FirstCohomology.congr_mk _ _ σ

/-- Relabelling by the identity graph isomorphism fixes every cohomology class. -/
@[simp]
theorem firstCohomologyRelabel_refl :
    firstCohomologyRelabel A (Iso.refl : G ≃g G) =
      MulEquiv.refl (G.FirstCohomology A) := by
  ext x
  obtain ⟨σ, rfl⟩ := FirstCohomology.mk_surjective x
  simp

/-- Successive graph relabellings compose on first cohomology. -/
theorem firstCohomologyRelabel_comp {X : Type*} {I : SimpleGraph X}
    (e : G ≃g H) (f : H ≃g I) :
    firstCohomologyRelabel A (f.comp e) =
      (firstCohomologyRelabel A e).trans (firstCohomologyRelabel A f) := by
  ext x
  obtain ⟨σ, rfl⟩ := FirstCohomology.mk_surjective x
  simp only [firstCohomologyRelabel_mk, MulEquiv.trans_apply]
  rw [oneCochainsRelabel_comp]
  rfl

end SimpleGraph
