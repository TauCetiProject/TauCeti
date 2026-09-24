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

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
  (A : Type*) [CommGroup A]

/-- Relabel a graph one-cochain along an isomorphism of graphs. -/
def oneCochainsRelabel (e : G ≃g H) : G.oneCochains A ≃* H.oneCochains A where
  toFun σ := ⟨fun d => (σ : G.Dart → A) (e.symm.toHom.mapDart d), by
    rw [mem_oneCochains_iff]
    intro d
    have hd : e.symm.toHom.mapDart d.symm = (e.symm.toHom.mapDart d).symm := by
      apply Dart.ext
      cases d with
      | mk p hp => cases p; rfl
    rw [hd]
    exact (mem_oneCochains_iff.mp σ.property) (e.symm.toHom.mapDart d)⟩
  invFun σ := ⟨fun d => (σ : H.Dart → A) (e.toHom.mapDart d), by
    rw [mem_oneCochains_iff]
    intro d
    have hd : e.toHom.mapDart d.symm = (e.toHom.mapDart d).symm := by
      apply Dart.ext
      cases d with
      | mk p hp => cases p; rfl
    rw [hd]
    exact (mem_oneCochains_iff.mp σ.property) (e.toHom.mapDart d)⟩
  left_inv σ := by
    ext d
    dsimp
    apply congrArg (σ : G.Dart → A)
    apply Dart.ext
    cases d with
    | mk p hp => cases p with
      | mk i j => simp
  right_inv σ := by
    ext d
    dsimp
    apply congrArg (σ : H.Dart → A)
    apply Dart.ext
    cases d with
    | mk p hp => cases p with
      | mk i j => simp
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
  apply Dart.ext
  cases d with
  | mk p hp => cases p with
    | mk i j => simp [SimpleGraph.Hom.mapDart]

/-- Successive graph relabellings compose on one-cochains. -/
theorem oneCochainsRelabel_comp {X : Type*} {I : SimpleGraph X}
    (e : G ≃g H) (f : H ≃g I) :
    oneCochainsRelabel A (f.comp e) =
      (oneCochainsRelabel A e).trans (oneCochainsRelabel A f) := by
  ext σ d
  simp only [oneCochainsRelabel_apply, MulEquiv.trans_apply]
  apply congrArg (σ : G.Dart → A)
  apply Dart.ext
  cases d with
  | mk p hp => cases p with
    | mk i j => simp [SimpleGraph.Hom.mapDart]

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
