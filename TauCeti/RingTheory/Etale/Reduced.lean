/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.FieldTheory.Perfect

/-!
# Étale algebras over perfect fields

An algebra over a perfect field is étale exactly when it is finite and reduced. This permits
finite affine quotients to be recognized as finite étale schemes from their coordinate algebras.
-/

public section

namespace TauCeti

/- Étale algebras over any field are finite and reduced by Mathlib's unramified theory. For the
converse, Mathlib's Artinian decomposition `IsArtinianRing.equivPi` gives finite field-extension
factors, which are separable over the perfect base field;
`Algebra.Etale.iff_exists_algEquiv_prod` recognizes such a product as étale. -/
/-- An algebra over a perfect field is étale if and only if it is finite and reduced. -/
theorem algebraEtale_iff_finite_and_isReduced {k A : Type*} [Field k] [PerfectField k]
    [CommRing A] [Algebra k A] : Algebra.Etale k A ↔ Module.Finite k A ∧ IsReduced A := by
  refine ⟨fun _ ↦ ⟨Algebra.FormallyUnramified.finite_of_free k A,
    Algebra.FormallyUnramified.isReduced_of_field k A⟩, fun ⟨_, _⟩ ↦ ?_⟩
  have : IsArtinianRing A := .of_finite k A
  let _ (m : MaximalSpectrum A) : Field (A ⧸ m.asIdeal) := Ideal.Quotient.field _
  -- Each factor `A ⧸ m` is finite over `k` as a quotient of `A`, and separable as `k` is perfect.
  exact (Algebra.Etale.iff_exists_algEquiv_prod k A).mpr
    ⟨_, inferInstance, _, _, _, (IsArtinianRing.equivPi A).restrictScalars k,
      fun _ ↦ ⟨inferInstance, inferInstance⟩⟩

end TauCeti
