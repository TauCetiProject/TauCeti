/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Localizing multivariate polynomials away from a product of variables

Localizing `R[X_σ]` away from a product `∏_{i ∈ s} X i` of variables gives the ring of Laurent
polynomials in the variables indexed by `s`. A product of variables is a non-zero-divisor over
every commutative semiring (`MvPolynomial.isRegular_prod_X`), so the polynomial ring embeds into
this localization (`MvPolynomial.algebraMap_injective_of_isLocalizationAway_prod_X`).
-/

public section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R] (S : Type*) [CommSemiring S]
  [Algebra (MvPolynomial σ R) S]

/-- **A polynomial ring embeds into its localization away from a product of variables.** -/
theorem algebraMap_injective_of_isLocalizationAway_prod_X (s : Finset σ)
    [IsLocalization.Away (∏ i ∈ s, X i : MvPolynomial σ R) S] :
    Function.Injective (algebraMap (MvPolynomial σ R) S) :=
  IsLocalization.injectiveₛ (M := Submonoid.powers (∏ i ∈ s, X i : MvPolynomial σ R)) S
    fun _ ⟨k, hk⟩ ↦ hk ▸ (isRegular_prod_X s).pow k

end MvPolynomial
