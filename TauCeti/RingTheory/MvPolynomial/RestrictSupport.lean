/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The monomial basis of polynomials with restricted support

Mathlib's `MvPolynomial.basisRestrictSupport R s` is the basis of `MvPolynomial.restrictSupport R s`
indexed by `s`. This file records its coordinates (the coefficients) and its basis vectors (the
monomials with coefficient `1`).
-/

public section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R] {s : Set (σ →₀ ℕ)}

/-- The coordinates of a polynomial in `basisRestrictSupport` are its coefficients. -/
@[simp]
theorem basisRestrictSupport_repr_apply (p : restrictSupport R s) (c : s) :
    (basisRestrictSupport R s).repr p c = (p : MvPolynomial σ R).coeff c :=
  -- `basisRestrictSupport` is defined through `AddMonoidAlgebra.supportedEquivFinsupp`, which
  -- reads off coefficients.
  rfl

/-- The basis vectors of `basisRestrictSupport` are the monomials with coefficient `1`. -/
@[simp]
theorem basisRestrictSupport_apply_coe (c : s) :
    (basisRestrictSupport R s c : MvPolynomial σ R) = monomial (c : σ →₀ ℕ) 1 := by
  classical
  have hc : monomial (c : σ →₀ ℕ) (1 : R) ∈ restrictSupport R s := by simp
  suffices basisRestrictSupport R s c = ⟨_, hc⟩ from congrArg Subtype.val this
  refine (basisRestrictSupport R s).repr.injective (Finsupp.ext fun d ↦ ?_)
  simp [Finsupp.single_apply, coeff_monomial, Subtype.ext_iff]

end MvPolynomial
