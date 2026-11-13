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
factors, which are separable over the perfect base field; `Algebra.Etale.iff_exists_algEquiv_prod`
recognizes such a product as étale. -/
/-- A finite reduced commutative algebra over a perfect field is étale. -/
theorem algebraEtale_of_finite_of_isReduced (k A : Type*) [Field k] [PerfectField k]
    [CommRing A] [Algebra k A] [Module.Finite k A] [IsReduced A] : Algebra.Etale k A := by
  have : IsArtinianRing A := .of_finite k A
  let _ (m : MaximalSpectrum A) : Field (A ⧸ m.asIdeal) := Ideal.Quotient.field _
  -- Each factor `A ⧸ m` is finite over `k` as a quotient of `A`, and separable as `k` is perfect.
  exact (Algebra.Etale.iff_exists_algEquiv_prod k A).mpr
    ⟨_, inferInstance, _, _, _, (IsArtinianRing.equivPi A).restrictScalars k,
      fun _ ↦ ⟨inferInstance, inferInstance⟩⟩

end TauCeti
