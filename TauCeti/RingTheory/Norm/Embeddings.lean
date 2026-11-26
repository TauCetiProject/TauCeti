/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Norm.Transitivity
import TauCeti.Algebra.GroupWithZero.Basic

/-!
# Weighted products of conjugates of roots of unity

An infinity type is a product of conjugates with possibly different integer exponents. On a root
of unity, if those exponents are all congruent to one integer modulo its order, the product is
the corresponding power of the relative norm. In particular, the infinity type is trivial on
such roots of relative norm one.

For the cyclotomic application, see `New.Data.prod_phi_zeta_pow_pow_liftWeight_zero_eq_one`
in lsernau/grh-lean, `grh/src/New/Derivatives/Field/ChosenPlaces.lean` (`72fead1`).
-/

public section

namespace Algebra

/-- A weighted product of conjugates of an `n`-th root of unity, with all exponents congruent
modulo `n`, is the corresponding power of the relative norm. -/
theorem prod_embeddings_zpow_eq_norm_zpow_of_modEq
    {K L E : Type*} [Field K] [Field L] [Field E] [Algebra K L] [Algebra K E]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsAlgClosed E]
    {x : L} {n : ℕ} (hx : x ^ n = 1) {w : (L →ₐ[K] E) → ℤ} {a : ℤ}
    (hw : ∀ σ, w σ ≡ a [ZMOD (n : ℤ)]) :
    (∏ σ : L →ₐ[K] E, σ x ^ w σ) = algebraMap K E (Algebra.norm K x ^ a) := by
  calc
    _ = ∏ σ : L →ₐ[K] E, σ x ^ a := by
      refine Finset.prod_congr rfl fun σ _ ↦ TauCeti.zpow_eq_zpow_of_modEq ?_ (hw σ)
      rw [← map_pow, hx, map_one]
    _ = algebraMap K E (Algebra.norm K x ^ a) := by
      rw [map_zpow₀, Algebra.norm_eq_prod_embeddings, Finset.prod_zpow]

end Algebra
