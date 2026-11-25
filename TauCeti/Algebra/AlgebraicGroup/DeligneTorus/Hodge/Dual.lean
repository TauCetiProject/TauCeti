/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.Hodge
public import TauCeti.Algebra.Coalgebra.Comodule.Evaluation

/-!
# Hodge components of the dual of a representation of the Deligne torus

For a finite-dimensional real representation `V` of the Deligne torus `S`, the linear dual
`Module.Dual ℝ V` is a representation through the dual coaction (`TauCeti.Comodule.dual`). Under
the canonical pairing of `ℂ ⊗[ℝ] Module.Dual ℝ V` with `ℂ ⊗[ℝ] V`
(`TauCeti.Module.Dual.baseChangeEvaluation`), Hodge types negate: `(V^∨)^{p,q}` pairs trivially
with `V^{p',q'}` unless `(p', q') = (-p, -q)`, and it consists exactly of the vectors with this
property.

The orthogonality is a computation with the universal point of `𝔾ₘ × 𝔾ₘ`: acting by the same
point on both arguments preserves the pairing
(`TauCeti.Comodule.baseChangeEvaluation_dual_endOfPoint_invariant`), and the point acts on the
two arguments by `X^{(-p,-q)}` and `X^{(-p',-q')}`. The converse uses the Hodge decompositions of
`ℂ ⊗[ℝ] Module.Dual ℝ V` and `ℂ ⊗[ℝ] V` and the nondegeneracy of the pairing.

## Main results

* `TauCeti.DeligneTorus.baseChangeEvaluation_eq_zero_of_mem_hodgeComponent`: a vector of
  `(V^∨)^{p,q}` pairs trivially with `V^{p',q'}` unless `(p', q') = (-p, -q)`.
* `TauCeti.DeligneTorus.mem_hodgeComponent_dual_iff`: `(V^∨)^{p,q}` consists of the vectors
  pairing trivially with every `V^{p',q'}` for `(p', q') ≠ (-p, -q)`.

## References

* J. S. Milne, *Introduction to Shimura varieties*, §2, *Hodge structures as representations of
  `S`*, pp. 26–27.
-/

public section

open WithConv TauCeti.Algebra
open scoped TensorProduct

namespace TauCeti.DeligneTorus

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [Comodule ℝ S V] [Module.Finite ℝ V]

attribute [local instance] Comodule.dual

/-- **Hodge types negate in the dual.** A vector of `(V^∨)^{p,q}` pairs trivially with every
vector of `V^{p',q'}` unless `(p', q') = (-p, -q)`. -/
theorem baseChangeEvaluation_eq_zero_of_mem_hodgeComponent {p q p' q' : ℤ}
    {ξ : ℂ ⊗[ℝ] Module.Dual ℝ V} {v : ℂ ⊗[ℝ] V}
    (hξ : ξ ∈ hodgeComponent (Module.Dual ℝ V) p q) (hv : v ∈ hodgeComponent V p' q')
    (hpq : (p', q') ≠ (-p, -q)) :
    TauCeti.Module.Dual.baseChangeEvaluation (R := ℝ) (M := V) (A := ℂ) ξ v = 0 := by
  have h := TauCeti.Comodule.baseChangeEvaluation_dual_endOfPoint_invariant (R := ℝ) (H := S)
    (M := V) splittingPoint
    (LinearMap.rTensor (Module.Dual ℝ V)
      (IsScalarTower.toAlgHom ℝ ℂ (MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)))).toLinearMap ξ)
    (LinearMap.rTensor V
      (IsScalarTower.toAlgHom ℝ ℂ (MonoidAlgebra ℂ (Multiplicative (ℤ × ℤ)))).toLinearMap v)
  rw [mem_hodgeComponent_iff] at hξ hv
  rw [hξ, hv] at h
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, AlgHom.baseChangeEvaluation_rTensor,
    IsScalarTower.coe_toAlgHom', MonoidAlgebra.coe_algebraMap, Function.comp_apply,
    Algebra.algebraMap_self, RingHom.id_apply, MonoidAlgebra.single_mul_single, mul_one,
    one_mul] at h
  have hne : Multiplicative.ofAdd (-p', -q') * Multiplicative.ofAdd (-p, -q) ≠ 1 := by
    simp [← ofAdd_add, Prod.ext_iff, -not_and] at hpq ⊢
    omega
  by_contra h₀
  exact hne ((MonoidAlgebra.single_left_inj h₀).mp h)

/-- **The Hodge components of the dual.** `(V^∨)^{p,q}` consists of the vectors of
`ℂ ⊗[ℝ] Module.Dual ℝ V` pairing trivially with `V^{p',q'}` for every `(p', q') ≠ (-p, -q)`. -/
theorem mem_hodgeComponent_dual_iff {p q : ℤ} {ξ : ℂ ⊗[ℝ] Module.Dual ℝ V} :
    ξ ∈ hodgeComponent (Module.Dual ℝ V) p q ↔
      ∀ p' q' : ℤ, (p', q') ≠ (-p, -q) → ∀ v ∈ hodgeComponent V p' q',
        TauCeti.Module.Dual.baseChangeEvaluation (R := ℝ) (M := V) (A := ℂ) ξ v = 0 := by
  refine ⟨fun hξ p' q' hne v hv ↦ baseChangeEvaluation_eq_zero_of_mem_hodgeComponent hξ hv hne,
    fun h ↦ ?_⟩
  let D : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℝ] Module.Dual ℝ V) := fun ab ↦
    hodgeComponent (Module.Dual ℝ V) ab.1 ab.2
  have hξ : ξ ∈ D (p, q) ⊔ ⨆ (ab : ℤ × ℤ) (_ : ab ≠ (p, q)), D ab := by
    rw [← iSup_split_single D (p, q),
      (isInternal_hodgeComponent (Module.Dual ℝ V)).submodule_iSup_eq_top]
    exact Submodule.mem_top
  obtain ⟨ξ₀, hξ₀, ξ₁, hξ₁, rfl⟩ := Submodule.mem_sup.mp hξ
  -- the components of `ξ` other than `(p, q)` pair trivially with `V^{-p,-q}`
  have hle : ⨆ (ab : ℤ × ℤ) (_ : ab ≠ (p, q)), D ab ≤
      (hodgeComponent V (-p) (-q)).dualAnnihilator.comap
        (TauCeti.Module.Dual.baseChangeEvaluation (R := ℝ) (M := V) (A := ℂ)) :=
    iSup₂_le fun ab hab ξ' hξ' ↦ (Submodule.mem_dualAnnihilator _).mpr fun v hv ↦
      baseChangeEvaluation_eq_zero_of_mem_hodgeComponent hξ' hv fun h0 ↦ hab <| by
        simp only [Prod.ext_iff] at h0 ⊢
        omega
  have h₁ := (Submodule.mem_dualAnnihilator _).mp (hle hξ₁)
  -- hence `ξ₁` pairs trivially with everything
  have hker : (⊤ : Submodule ℂ (ℂ ⊗[ℝ] V)) ≤
      LinearMap.ker (TauCeti.Module.Dual.baseChangeEvaluation (R := ℝ) (M := V) (A := ℂ) ξ₁) := by
    rw [← (isInternal_hodgeComponent V).submodule_iSup_eq_top]
    refine iSup_le fun ab v hv ↦ LinearMap.mem_ker.mpr ?_
    by_cases hab : ab = (-p, -q)
    · subst hab
      exact h₁ v hv
    · have h₀ := baseChangeEvaluation_eq_zero_of_mem_hodgeComponent hξ₀ hv hab
      have := h ab.1 ab.2 hab v hv
      rwa [map_add, LinearMap.add_apply, h₀, zero_add] at this
  have hz : ξ₁ = 0 := (TauCeti.Module.Dual.baseChangeEvaluationEquiv (R := ℝ) (M := V)
    (A := ℂ)).injective <| by
      rw [map_zero, TauCeti.Module.Dual.baseChangeEvaluationEquiv_apply]
      exact LinearMap.ext fun v ↦ hker Submodule.mem_top
  rwa [hz, add_zero]

end TauCeti.DeligneTorus
