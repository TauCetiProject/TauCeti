/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.LocalRing.NonLocalRing

/-!
# Connectedness from a local ring of global functions

A scheme whose ring of global functions is local is connected. A decomposition into two
nonempty clopen subsets would decompose that ring as a product of two nonzero rings.
This criterion applies to non-affine schemes as well, for example punctured local spectra
whose functions extend across the closed point.

The product-of-sections argument follows Mathlib's
`AlgebraicGeometry.irreducibleSpace_of_isIntegral`.
-/

public section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

/-- A scheme with a local ring of global functions is preconnected. -/
theorem preconnectedSpace_of_isLocalRing (X : Scheme.{u}) [IsLocalRing Γ(X, ⊤)] :
    PreconnectedSpace X := by
  rw [preconnectedSpace_iff_clopen]
  intro S hS
  by_contra! h
  let U : X.Opens := ⟨S, hS.isOpen⟩
  let V : X.Opens := ⟨Sᶜ, hS.isClosed.isOpen_compl⟩
  have : Nonempty U := by simpa [U] using h.1
  have : Nonempty V := by
    obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem S).mp h.2
    exact ⟨⟨x, hx⟩⟩
  have hsup : U ⊔ V = ⊤ := by ext; simp [U, V]
  have hinf : U ⊓ V = ⊥ := by ext; simp [U, V]
  let e : Γ(X, U ⊔ V) ≅ CommRingCat.of (Γ(X, U) × Γ(X, V)) :=
    (X.sheaf.isProductOfDisjoint U V hinf).conePointUniqueUpToIso
      (CommRingCat.prodFanIsLimit _ _)
  have : IsLocalRing Γ(X, U ⊔ V) := by rw [hsup]; infer_instance
  have : IsLocalRing (Γ(X, U) × Γ(X, V)) := e.commRingCatIsoToRingEquiv.isLocalRing
  exact IsLocalRing.not_isLocalRing_of_prod_of_nontrivial Γ(X, U) Γ(X, V) this

/-- A scheme with a local ring of global functions is nonempty and connected. -/
theorem connectedSpace_of_isLocalRing (X : Scheme.{u}) [IsLocalRing Γ(X, ⊤)] :
    ConnectedSpace X := by
  have := X.preconnectedSpace_of_isLocalRing
  have : Nonempty X := by
    by_contra h
    have : IsEmpty X := not_nonempty_iff.mp h
    have htop : (⊤ : X.Opens) = ⊥ := by ext x; exact isEmptyElim x
    have : Subsingleton Γ(X, ⊤) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty htop)
    exact zero_ne_one (Subsingleton.elim (0 : Γ(X, ⊤)) 1)
  exact { toPreconnectedSpace := inferInstance, toNonempty := inferInstance }

end AlgebraicGeometry.Scheme
