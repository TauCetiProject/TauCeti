/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Pointwise
import TauCeti.Data.Rat.NumDenDvd

/-!
# Coordinatewise embedding of finitely supported natural functions into rationals

Provides the additive homomorphism `TauCeti.ratEmbed : (σ →₀ ℕ) →+ (σ → ℚ)` embedding finitely
supported natural-valued functions into rational-valued functions, together with its compatibility
with `Finsupp.mapDomain` along equivalences (`TauCeti.ratEmbed_mapDomain`) and simultaneous
denominator clearing on finite types (`TauCeti.exists_nat_smul_eq_ratEmbed`).

## Main results

* `TauCeti.ratEmbed`: additive homomorphism embedding `σ →₀ ℕ` into `σ → ℚ`.
* `TauCeti.ratEmbed_injective` and `TauCeti.ratEmbed_mapDomain`: injectivity and equivariance under
  `Finsupp.mapDomain` along an equivalence.
* `TauCeti.exists_nat_smul_eq_ratEmbed`: any nonnegative rational family `x : σ → ℚ` on a finite
  type clears denominators to `TauCeti.ratEmbed d` for some positive natural multiplier `D`.
-/

public section

namespace TauCeti

/-- Embed a finitely supported natural family `σ →₀ ℕ` coordinatewise into `σ → ℚ`. -/
noncomputable def ratEmbed {σ : Type*} : (σ →₀ ℕ) →+ (σ → ℚ) :=
  Finsupp.coeFnAddHom.comp (Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℚ))

@[simp]
theorem ratEmbed_apply {σ : Type*} (d : σ →₀ ℕ) (i : σ) : ratEmbed d i = (d i : ℚ) :=
  (rfl)

/-- `ratEmbed` is injective. -/
theorem ratEmbed_injective {σ : Type*} : Function.Injective (ratEmbed (σ := σ)) :=
  fun _ _ h ↦ Finsupp.ext fun i ↦ Nat.cast_injective (congrFun h i)

/-- Mapping the domain of `d : σ →₀ ℕ` along an equivalence `e : σ ≃ τ` precomposes `ratEmbed d`
with `e.symm`. -/
theorem ratEmbed_mapDomain {σ τ : Type*} (e : σ ≃ τ) (d : σ →₀ ℕ) :
    ratEmbed (d.mapDomain e) = ratEmbed d ∘ e.symm :=
  funext fun i ↦ by
    simp [ratEmbed_apply, ← Finsupp.equivMapDomain_eq_mapDomain, Finsupp.equivMapDomain_apply]

/-- Any nonnegative rational family `x : σ → ℚ` on a finite type clears denominators to
`ratEmbed d` for some positive natural multiplier `D` and `d : σ →₀ ℕ`. -/
theorem exists_nat_smul_eq_ratEmbed {σ : Type*} [Finite σ] {x : σ → ℚ} (hx : ∀ i, 0 ≤ x i) :
    ∃ (D : ℕ) (d : σ →₀ ℕ), 0 < D ∧ (D : ℚ) • x = ratEmbed d := by
  classical
  cases nonempty_fintype σ
  obtain ⟨D, k, hD, hk⟩ := Finset.exists_nat_mul_eq_natCast Finset.univ fun i _ ↦ hx i
  refine ⟨D, Finsupp.equivFunOnFinite.symm k, hD, funext fun i ↦ ?_⟩
  simpa only [Pi.smul_apply, smul_eq_mul, ratEmbed_apply,
    Finsupp.equivFunOnFinite_symm_apply_apply] using hk i (Finset.mem_univ i)

end TauCeti
