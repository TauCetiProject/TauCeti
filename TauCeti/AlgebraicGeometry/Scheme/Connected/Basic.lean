/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections

/-!
# Connectedness of schemes from their global functions

A nonempty scheme whose ring of global functions is local is connected
(`AlgebraicGeometry.Scheme.connectedSpace_of_isLocalRing_Γ`): a decomposition into two disjoint
nonempty open subsets would split the global functions as a product of two nonzero rings, which
is not local.
-/

public section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme

/-- A nonempty scheme whose ring of global functions is local is connected: a decomposition into
two disjoint nonempty open subsets would split the global functions as a product of two nonzero
rings. -/
theorem connectedSpace_of_isLocalRing_Γ (X : Scheme.{u}) [Nonempty X] [IsLocalRing Γ(X, ⊤)] :
    ConnectedSpace X := by
  refine connectedSpace_iff_clopen.mpr ⟨inferInstance, fun s hs ↦ ?_⟩
  by_contra! hne
  let V : X.Opens := ⟨s, hs.isOpen⟩
  let W : X.Opens := ⟨sᶜ, hs.isClosed.isOpen_compl⟩
  have : Nonempty V := hne.1.to_subtype
  have : Nonempty W := (Set.nonempty_compl.mpr hne.2).to_subtype
  have hVW : V ⊓ W = ⊥ := by ext; simp [V, W]
  have hsup : V ⊔ W = ⊤ := by ext; simp [V, W]
  -- `Γ(X, 𝒪)` is the product of the nonzero rings `Γ(V, 𝒪)` and `Γ(W, 𝒪)`.
  let φ : Γ(X, ⊤) ≃+* Γ(X, V) × Γ(X, W) :=
    (X.presheaf.mapIso (eqToIso hsup).op ≪≫
      (X.sheaf.isProductOfDisjoint V W hVW).conePointUniqueUpToIso
        (CommRingCat.prodFanIsLimit _ _)).commRingCatIsoToRingEquiv
  have hadd : φ.symm (1, 0) + φ.symm (0, 1) = 1 := by
    simp [← map_add, ← Prod.one_eq_mk]
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hadd with h | h
  · exact not_isUnit_zero (Prod.isUnit_iff.mp (by simpa using h.map φ)).2
  · exact not_isUnit_zero (Prod.isUnit_iff.mp (by simpa using h.map φ)).1

end AlgebraicGeometry.Scheme
