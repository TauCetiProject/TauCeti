/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Ideal.Maps
public import TauCeti.LinearAlgebra.Dual.BaseChange

/-!
# Values of linear functionals after flat base change

For an `R`-module `M` and `m : M`, the values `φ m` of the linear functionals `φ : M → R` form an
ideal of `R`, the range of evaluation at `m` on the dual. When `M` is finitely presented and `A`
is a flat `R`-algebra, linear maps out of `M` commute with base change to `A`
(`Module.FinitePresentation.isBaseChange_map`), so the ideal of `A` formed by the values at
`1 ⊗ m` of the `A`-linear functionals on `A ⊗[R] M` is the extension of that ideal of `R`.

## Main results

* `TauCeti.Module.Dual.range_eval_one_tmul`: for flat `A` and finitely presented `M`, the range of
  evaluation at `1 ⊗ m` on the dual of `A ⊗[R] M` is the extension to `A` of the range of
  evaluation at `m` on the dual of `M`.
-/

public section

open TensorProduct

namespace TauCeti.Module.Dual

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- For a flat `R`-algebra `A` and a finitely presented `R`-module `M`, the values at `1 ⊗ m` of
the `A`-linear functionals on `A ⊗[R] M` form the extension to `A` of the ideal of values at `m`
of the `R`-linear functionals on `M`. The functionals `A ⊗ φ` span the dual of `A ⊗[R] M` over
`A` by `Module.FinitePresentation.isBaseChange_map`. -/
theorem range_eval_one_tmul (A : Type*) [CommRing A] [Algebra R A] [Module.Flat R A]
    [Module.FinitePresentation R M] (m : M) :
    LinearMap.range (Module.Dual.eval A (A ⊗[R] M) (1 ⊗ₜ m)) =
      Ideal.map (algebraMap R A) (LinearMap.range (Module.Dual.eval R M m)) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨ψ, rfl⟩
    rw [Module.Dual.eval_apply]
    let e := AlgebraTensorModule.rid R A A
    suffices H : ∀ g : A ⊗[R] M →ₗ[A] A ⊗[R] R,
        e (g (1 ⊗ₜ m)) ∈ Ideal.map (algebraMap R A) (LinearMap.range (Module.Dual.eval R M m)) by
      simpa using H (e.symm.toLinearMap ∘ₗ ψ)
    intro g
    induction g using (Module.FinitePresentation.isBaseChange_map R M R A).inductionOn with
    | tmul ρ =>
      simp only [LinearMap.baseChangeHom_apply, LinearMap.baseChange_tmul, e,
        AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_one]
      exact Ideal.mem_map_of_mem _ ⟨ρ, Module.Dual.eval_apply ..⟩
    | smul r g hg =>
      rw [LinearMap.smul_apply, map_smul, smul_eq_mul]
      exact Ideal.mul_mem_left _ _ hg
    | add g₁ g₂ h₁ h₂ =>
      rw [LinearMap.add_apply, map_add]
      exact Ideal.add_mem _ h₁ h₂
  · rw [Ideal.map_le_iff_le_comap]
    rintro _ ⟨ρ, rfl⟩
    refine Ideal.mem_comap.2 ⟨ρ.baseChange A, ?_⟩
    rw [Module.Dual.eval_apply, Module.Dual.eval_apply,
      Module.Dual.baseChange_apply_one_tmul]

end TauCeti.Module.Dual
