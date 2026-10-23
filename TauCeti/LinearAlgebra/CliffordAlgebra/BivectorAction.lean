/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Trace
public import TauCeti.LinearAlgebra.CliffordAlgebra.Bivector

/-!
# Two-forms acting on a Hermitian Clifford module

Let `Q` be a real quadratic form on `M` and `W` a complex inner product space carrying a real
algebra map `ρ : CliffordAlgebra Q → End_ℂ W`. Two-forms `α ∈ ⋀² M` act on `W` through the
bivector map `c₂ = CliffordAlgebra.bivectorExterior Q`. This file records two basic facts about
this action.

## Main results

* `CliffordAlgebra.trace_map_bivectorExterior`: two-forms act trace freely, `tr c₂(α) = 0`.
* `CliffordAlgebra.adjoint_map_bivectorExterior`: on a finite-dimensional module whose generators
  act skew-adjointly, `c(v)* = -c(v)`, two-forms act skew-adjointly, `c₂(α)* = -c₂(α)`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

namespace CliffordAlgebra

variable {M : Type*} [AddCommGroup M] [Module ℝ M] {Q : QuadraticForm ℝ M}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)

/-- Two-forms act trace-freely on every Clifford module: `tr c₂(α) = 0`. -/
theorem trace_map_bivectorExterior (x : ⋀[ℝ]^2 M) :
    LinearMap.trace ℂ W (ρ (bivectorExterior Q x)) = 0 := by
  refine bivectorExterior_range_le_of_bivector_mem Q
    (LinearMap.ker ((LinearMap.trace ℂ W).restrictScalars ℝ ∘ₗ ρ.toLinearMap)) (fun a b ↦ ?_)
    ⟨x, rfl⟩
  simp [bivector_def, LinearMap.trace_mul_comm ℂ (ρ (ι Q a))]

variable [FiniteDimensional ℂ W] {ρ}

/-- If the generators act skew-adjointly, `c(v)* = -c(v)`, then so do two-forms:
`c₂(α)* = -c₂(α)`. -/
theorem adjoint_map_bivectorExterior (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (x : ⋀[ℝ]^2 M) :
    LinearMap.adjoint (ρ (bivectorExterior Q x)) = -ρ (bivectorExterior Q x) := by
  -- The elements acting skew-adjointly form a real subspace containing every bivector.
  let P : Submodule ℝ (CliffordAlgebra Q) :=
    { carrier := {a | LinearMap.adjoint (ρ a) = -ρ a}
      add_mem' := fun {a b} ha hb ↦ by
        simp only [Set.mem_ofPred_eq, map_add] at ha hb ⊢
        rw [ha, hb, neg_add]
      zero_mem' := by simp
      smul_mem' := fun r a ha ↦ by
        simp only [Set.mem_ofPred_eq, map_smul] at ha ⊢
        rw [← Complex.coe_smul, map_smulₛₗ, ha, Complex.conj_ofReal, smul_neg, Complex.coe_smul] }
  refine bivectorExterior_range_le_of_bivector_mem Q P (fun a b ↦ ?_) ⟨x, rfl⟩
  simp only [P, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq]
  rw [bivector_def, map_smul, map_sub, map_mul, map_mul, ← Complex.coe_smul, map_smulₛₗ, map_sub,
    Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearMap.adjoint_comp,
    LinearMap.adjoint_comp, hρ, hρ]
  simp only [LinearMap.neg_comp, LinearMap.comp_neg, neg_neg, Complex.conj_ofReal]
  module

end CliffordAlgebra
