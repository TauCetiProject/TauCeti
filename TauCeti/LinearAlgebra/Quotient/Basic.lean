/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Quotient maps and transport

A surjective linear map `f : M → M₂` sending `p` into `q` induces a surjective map
`M ⧸ p → M₂ ⧸ q` (`Submodule.mapQ_surjective`), and `Submodule.factor` commutes with
`Submodule.quotEquivOfEq` (`Submodule.factor_quotEquivOfEq`, `Submodule.factor_comp_quotEquivOfEq`).
-/

public section

namespace Submodule

variable {R M R₂ M₂ : Type*} [Ring R] [AddCommGroup M] [Module R M] [Ring R₂] [AddCommGroup M₂]
  [Module R₂ M₂] {τ₁₂ : R →+* R₂} (p : Submodule R M) (q : Submodule R₂ M₂)

/-- Surjectivity of a linear map implies surjectivity of the map it induces on quotients. -/
theorem mapQ_surjective (f : M →ₛₗ[τ₁₂] M₂) (h : p ≤ comap f q) (hf : Function.Surjective f) :
    Function.Surjective (p.mapQ q f h) := by
  rintro ⟨y⟩
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨Quotient.mk x, rfl⟩

/-- `Submodule.factor` commutes with `Submodule.quotEquivOfEq`. -/
theorem factor_quotEquivOfEq {p₁ p₂ q₁ q₂ : Submodule R M}
    (hp : p₁ = p₂) (hq : q₁ = q₂) (h₁ : p₁ ≤ q₁) (h₂ : p₂ ≤ q₂) (x : M ⧸ p₁) :
    Submodule.factor h₂ (Submodule.quotEquivOfEq p₁ p₂ hp x) =
      Submodule.quotEquivOfEq q₁ q₂ hq (Submodule.factor h₁ x) := by
  obtain ⟨m, rfl⟩ := p₁.mkQ_surjective x
  rw [Submodule.factor_mk, Submodule.mkQ_apply, Submodule.quotEquivOfEq_mk,
    ← Submodule.mkQ_apply, Submodule.factor_mk, Submodule.mkQ_apply, Submodule.mkQ_apply,
    Submodule.quotEquivOfEq_mk]

/-- `Submodule.factor` commutes with `Submodule.quotEquivOfEq` as linear maps. -/
theorem factor_comp_quotEquivOfEq {p₁ p₂ q₁ q₂ : Submodule R M}
    (hp : p₁ = p₂) (hq : q₁ = q₂) (h₁ : p₁ ≤ q₁) (h₂ : p₂ ≤ q₂) :
    Submodule.factor h₂ ∘ₗ (Submodule.quotEquivOfEq p₁ p₂ hp).toLinearMap =
      (Submodule.quotEquivOfEq q₁ q₂ hq).toLinearMap ∘ₗ Submodule.factor h₁ :=
  LinearMap.ext (factor_quotEquivOfEq hp hq h₁ h₂)

end Submodule
