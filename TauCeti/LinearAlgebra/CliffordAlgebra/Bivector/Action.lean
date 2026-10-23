/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Trace
public import TauCeti.LinearAlgebra.CliffordAlgebra.Bivector.Basic

/-!
# Two-forms acting on a Clifford module

Let `Q` be a real quadratic form on `M` and `W` a complex vector space carrying a real algebra map
`ρ : CliffordAlgebra Q → End_ℂ W`. Two-forms `α ∈ ⋀² M` act on `W` through the bivector map
`c₂ = CliffordAlgebra.bivectorExterior Q`. This file records two basic facts about this action.

## Main results

* `CliffordAlgebra.trace_map_bivectorExterior`: two-forms act trace freely, `tr c₂(α) = 0`.
* `CliffordAlgebra.adjoint_map_bivectorExterior`: on a finite-dimensional complex inner product
  space whose generators act skew-adjointly, `c(v)* = -c(v)`, two-forms act skew-adjointly,
  `c₂(α)* = -c₂(α)`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

namespace CliffordAlgebra

variable {M : Type*} [AddCommGroup M] [Module ℝ M] {Q : QuadraticForm ℝ M}

section Trace

variable {W : Type*} [AddCommGroup W] [Module ℂ W] (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)

/-- Two-forms act trace-freely on every Clifford module: `tr c₂(α) = 0`. -/
theorem trace_map_bivectorExterior (x : ⋀[ℝ]^2 M) :
    LinearMap.trace ℂ W (ρ (bivectorExterior Q x)) = 0 := by
  refine bivectorExterior_range_le_of_bivector_mem Q
    (LinearMap.ker ((LinearMap.trace ℂ W).restrictScalars ℝ ∘ₗ ρ.toLinearMap)) (fun a b ↦ ?_)
    ⟨x, rfl⟩
  simp [bivector_def, LinearMap.trace_mul_comm ℂ (ρ (ι Q a))]

end Trace

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}

/-- If the generators act skew-adjointly, `c(v)* = -c(v)`, then so do two-forms:
`c₂(α)* = -c₂(α)`. -/
theorem adjoint_map_bivectorExterior (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
    (x : ⋀[ℝ]^2 M) :
    LinearMap.adjoint (ρ (bivectorExterior Q x)) = -ρ (bivectorExterior Q x) := by
  -- The elements acting skew-adjointly form a real subspace containing every bivector.
  let P : Submodule ℝ (CliffordAlgebra Q) :=
    { carrier := {a | LinearMap.adjoint (ρ a) = -ρ a}
      add_mem' := fun {a b} (ha : _ = _) (hb : _ = _) ↦ (by simp [ha, hb, add_comm] : _ = _)
      zero_mem' := (by simp : _ = _)
      smul_mem' := fun r a (ha : _ = _) ↦
        (by rw [map_smul, ← Complex.coe_smul, map_smulₛₗ, ha]; simp : _ = _) }
  refine bivectorExterior_range_le_of_bivector_mem Q P
    (fun a b ↦ (?_ : LinearMap.adjoint (ρ (bivector Q a b)) = -ρ (bivector Q a b))) ⟨x, rfl⟩
  rw [bivector_def, map_smul, ← Complex.coe_smul, map_smulₛₗ, Complex.conj_ofReal]
  simp [Module.End.mul_eq_comp, LinearMap.adjoint_comp, hρ]
  module

end CliffordAlgebra
