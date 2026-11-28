/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-!
# Invariant global functions of a monoid scheme action

Let `S` be a scheme and `G` a monoid object of `S`-schemes, for instance a group scheme over `S`,
acting on an `S`-scheme `X` by `γ : G ×_S X ⟶ X`. A global function `r` on `X` is `G`-invariant
when its pullbacks along the action and along the projection `pr₂ : G ×_S X ⟶ X` agree,
`γ^♯ r = pr₂^♯ r`. The invariant functions form the subring
`TauCeti.AlgebraicGeometry.invariantGlobalSections G X` of `Γ(X, 𝒪_X)`.
-/

public noncomputable section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

variable {S : Scheme.{u}} (G X : Over S) [MonObj G] [ModObj G X]

/-- The global functions on `X` invariant under `G`: those with the same pullbacks along the
action and the projection `G ×_S X ⟶ X`. -/
def invariantGlobalSections : Subring Γ(X.left, ⊤) :=
  γ[G,X].left.appTop.hom.eqLocus (snd G X).left.appTop.hom

variable {G X} in
/-- A global function is `G`-invariant exactly when its pullbacks along the action and the
projection agree. -/
@[simp]
lemma mem_invariantGlobalSections_iff {r : Γ(X.left, ⊤)} :
    r ∈ invariantGlobalSections G X ↔ γ[G,X].left.appTop r = (snd G X).left.appTop r :=
  RingHom.mem_eqLocus

end TauCeti.AlgebraicGeometry
