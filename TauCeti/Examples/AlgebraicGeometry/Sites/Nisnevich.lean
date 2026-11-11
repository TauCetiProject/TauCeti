/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.Sites.Nisnevich.Basic

/-!
# Checks for Nisnevich coverings

The identity is a Nisnevich covering, while the spectrum of a quadratic field extension is not a
Nisnevich covering of the spectrum of the base field: its residue field extension is not an
isomorphism.
-/

open CategoryTheory AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

universe u

namespace TauCeti.Examples

-- `{𝟙 X}` is a Nisnevich covering.
example (X : Scheme.{u}) : IsNisnevichCovering (fun _ : PUnit.{1} ↦ 𝟙 X) :=
  isNisnevichCovering_of_isIso _

-- A quadratic field extension is not a Nisnevich covering.
example (k K : Type u) [Field k] [Field K] [Algebra k K] (h : Module.finrank k K = 2) :
    ¬ IsNisnevichCovering
      (fun _ : PUnit.{u + 1} ↦ Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  intro hc
  obtain ⟨-, x, -, hx⟩ := hc.exists_isIso (IsLocalRing.closedPoint k)
  have := x.isPrime
  rw [RingHom.isIso_SpecMap_residueFieldMap_iff _ x _ rfl] at hx
  -- The residue field of the field `k` at its prime is `k`, so `k → K` is onto.
  have hb : Function.Bijective (algebraMap k K) := by
    refine ⟨(algebraMap k K).injective, fun y ↦ ?_⟩
    obtain ⟨w, hw⟩ := hx.2 (algebraMap K x.asIdeal.ResidueField y)
    obtain ⟨r, rfl⟩ :=
      (Ideal.algEquivResidueFieldOfField (x.asIdeal.comap (algebraMap k K))).surjective w
    refine ⟨r, (algebraMap K x.asIdeal.ResidueField).injective ?_⟩
    rw [← hw, Ideal.algEquivResidueFieldOfField_apply, Ideal.ResidueField.map_algebraMap]
  have := (LinearEquiv.ofBijective (Algebra.linearMap k K) hb).finrank_eq
  rw [Module.finrank_self] at this
  omega

end TauCeti.Examples
