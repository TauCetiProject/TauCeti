/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Vanishing coefficients for a family of linear maps into polynomials

Let `V` be a finite-dimensional vector space over a division ring `F`, and let `T ℓ : V → F[X]` be
linear maps for `ℓ < M`. If `∑_{ℓ < M} K ℓ < dim V`, then some nonzero `v ∈ V` makes the first `K ℓ`
coefficients of `T ℓ v` vanish for every `ℓ < M`
(`Polynomial.exists_ne_zero_forall_coeff_eq_zero`): the conditions are fewer than the unknowns, so
the linear map `v ↦ ((T ℓ v).coeff r)_{ℓ < M, r < K ℓ}` has a nonzero kernel.

This is the linear algebra of the interpolation step of Stepanov's method, and of other auxiliary
polynomial constructions that impose vanishing conditions on coefficients.
-/

public section

namespace Polynomial

/-- If the unknowns outnumber the linear conditions, `∑_{ℓ < M} K ℓ < dim V`, then some nonzero
`v` makes the first `K ℓ` coefficients of `T ℓ v` vanish for every `ℓ < M`. -/
theorem exists_ne_zero_forall_coeff_eq_zero {F V : Type*} [DivisionRing F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (T : ℕ → V →ₗ[F] F[X]) {M : ℕ} (K : ℕ → ℕ)
    (hK : ∑ ℓ ∈ Finset.range M, K ℓ < Module.finrank F V) :
    ∃ v : V, v ≠ 0 ∧ ∀ ℓ < M, ∀ r < K ℓ, (T ℓ v).coeff r = 0 := by
  classical
  let Φ : V →ₗ[F] ((Σ ℓ : Fin M, Fin (K ℓ)) → F) :=
    LinearMap.pi fun k => lcoeff F (k.2 : ℕ) ∘ₗ T k.1
  have hdim : Module.finrank F ((Σ ℓ : Fin M, Fin (K ℓ)) → F) < Module.finrank F V := by
    rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_sigma,
      Fin.sum_univ_eq_sum_range (fun ℓ => Fintype.card (Fin (K ℓ))), ← Finset.sum_congr rfl
        fun ℓ _ => (Fintype.card_fin (K ℓ)).symm]
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := Φ) hdim)
  refine ⟨v, hv0, fun ℓ hℓ r hr => ?_⟩
  simpa [Φ] using congrFun (LinearMap.mem_ker.mp hv) ⟨⟨ℓ, hℓ⟩, ⟨r, hr⟩⟩

end Polynomial
