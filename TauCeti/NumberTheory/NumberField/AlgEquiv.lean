/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import TauCeti.RingTheory.Unramified.AlgEquiv

/-!
# Transport between isomorphic number-field extensions

This file records how properties of primes of rings of integers transport along an isomorphism
of field extensions.

## Main results

* `AlgEquiv.forall_isUnramifiedAt_iff`: unramifiedness above a base prime is invariant under an
  isomorphism of extensions.
-/

public section

open scoped NumberField

namespace AlgEquiv

variable {K L L' : Type*} [Field K] [Field L] [Algebra K L] [Field L'] [Algebra K L']

/-- **Unramifiedness above `𝔭` does not depend on the model of the extension.** -/
theorem forall_isUnramifiedAt_iff (e : L ≃ₐ[K] L') (𝔭 : Ideal (𝓞 K)) :
    (∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭], Algebra.IsUnramifiedAt (𝓞 K) Q) ↔
      ∀ (Q : Ideal (𝓞 L')) [Q.IsPrime] [Q.LiesOver 𝔭], Algebra.IsUnramifiedAt (𝓞 K) Q := by
  set ψ := NumberField.RingOfIntegers.mapAlgEquiv e
  constructor
  · intro h Q _ _
    exact (ψ.symm.isUnramifiedAt_iff_of_eq_comap (q := Q.comap ψ)
      (Ideal.comap_of_equiv ψ.symm.toRingEquiv).symm).2 (h _)
  · intro h Q _ _
    exact (ψ.isUnramifiedAt_iff_of_eq_comap (q := Q.comap ψ.symm)
      (Ideal.comap_of_equiv ψ.toRingEquiv).symm).2 (h _)

end AlgEquiv
