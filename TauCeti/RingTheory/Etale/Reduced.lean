/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.FieldTheory.Perfect

/-!
# Finite reduced algebras over perfect fields

A finite reduced commutative algebra over a perfect field is étale. This permits finite
affine quotients to be recognized as finite étale schemes from their coordinate algebras.
-/

public section

namespace TauCeti

/- Mathlib's Artinian decomposition `IsArtinianRing.equivPi` gives finite field-extension
factors, which are separable over the perfect base field. -/
/-- A finite reduced commutative algebra over a perfect field is étale. -/
theorem algebraEtale_of_finite_of_isReduced (k A : Type*) [Field k] [PerfectField k]
    [CommRing A] [Algebra k A] [Module.Finite k A] [IsReduced A] : Algebra.Etale k A := by
  let _ : IsArtinianRing A := IsArtinianRing.of_finite k A
  let _ (m : MaximalSpectrum A) : Field (A ⧸ m.asIdeal) := Ideal.Quotient.field _
  let _ (m : MaximalSpectrum A) : Module.Finite k (A ⧸ m.asIdeal) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ k m.asIdeal).toLinearMap
      (Ideal.Quotient.mkₐ_surjective k m.asIdeal)
  let _ (m : MaximalSpectrum A) : Algebra.FormallyEtale k (A ⧸ m.asIdeal) :=
    Algebra.FormallyEtale.of_isSeparable k _
  let _ : Algebra.FormallyEtale k A :=
    Algebra.FormallyEtale.of_equiv ((IsArtinianRing.equivPi A).restrictScalars k).symm
  exact ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

end TauCeti
