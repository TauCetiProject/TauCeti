/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Padic
public import TauCeti.NumberTheory.LocalField.Tame.Presentation

/-!
# The marked tame quotient of `ℚ₂`

The residue cardinality is two, so an arithmetic Frobenius conjugates a tame inertia
generator to its square. The chosen generators give the marked Iwasawa presentation,
starting from the intrinsic description of a generator of tame inertia.
-/

public section

namespace TauCeti

/-- The tame quotient of `ℚ₂` has a marked arithmetic Frobenius and tame inertia generator,
with the relation `σ τ σ⁻¹ = τ²` and the marked Iwasawa isomorphism. -/
theorem exists_marked_tameQuotient_padic_two :
    ∃ (σ : Field.absoluteGaloisGroup ℚ_[2]) (τ : inertiaSubgroup ℚ_[2]),
      IsArithFrobeniusLift ℚ_[2] σ ∧
      (Subgroup.zpowers (toTameQuotient ℚ_[2] τ)).topologicalClosure = tameInertia ℚ_[2] ∧
      toTameQuotient ℚ_[2] σ * toTameQuotient ℚ_[2] τ * (toTameQuotient ℚ_[2] σ)⁻¹ =
        toTameQuotient ℚ_[2] τ ^ 2 ∧
      ∃ e : tameQuotient ℚ_[2] ≃ₜ* IwasawaGroup ℚ_[2],
        e (toTameQuotient ℚ_[2] σ) = iwasawaSigma ℚ_[2] ∧
        e (toTameQuotient ℚ_[2] τ) = iwasawaTau ℚ_[2] := by
  obtain ⟨σ, hσ⟩ := exists_isArithFrobeniusLift ℚ_[2]
  obtain ⟨τ, hτI, hτ⟩ := exists_topologicalClosure_zpowers_eq_tameInertia ℚ_[2]
  let t : inertiaSubgroup ℚ_[2] := ⟨τ, hτI⟩
  have ht := (topologicalClosure_zpowers_toTameQuotient_eq_iff (τ := t)).1 hτ
  refine ⟨σ, t, hσ, hτ, ?_, tameQuotientEquiv hσ t ht, ?_, ?_⟩
  · simpa only [Padic.natCard_residueField] using
      hσ.toTameQuotient_mul_toTameQuotient_mul_inv t.2
  · exact tameQuotientEquiv_toTameQuotient_frobenius hσ ht
  · exact tameQuotientEquiv_toTameQuotient_tameGenerator hσ ht

end TauCeti
