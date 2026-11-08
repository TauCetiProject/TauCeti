/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.HahnBanach
public import Mathlib.Analysis.LocallyConvex.PointwiseConvergence
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Continuous functionals for the topology of pointwise convergence

Every linear functional on `E →SLₚₜ[σ] F` which is continuous for the topology of pointwise
convergence (the strong operator topology) is a finite sum `T ↦ ∑ x ∈ s, g x (T x)` of continuous
functionals of values (`PointwiseConvergenceCLM.exists_finset_sum_eq`). On a Hilbert space,
writing each `g x` as an inner product gives the usual finite sums of matrix coefficients.

## References

Kadison–Ringrose, *Fundamentals of the Theory of Operator Algebras I*, Theorem 5.1.2.
-/

public section

namespace PointwiseConvergenceCLM

variable {𝕜₁ 𝕜 E F : Type*} [NormedField 𝕜₁] [RCLike 𝕜] {σ : 𝕜₁ →+* 𝕜} [AddCommGroup E]
    [TopologicalSpace E] [Module 𝕜₁ E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Continuous functionals in the strong operator topology.** A linear functional on operators
which is continuous for the topology of pointwise convergence is a finite sum of functionals
`T ↦ g x (T x)`, each a continuous functional on `F` applied to the value at a vector `x`. -/
theorem exists_finset_sum_eq (φ : StrongDual 𝕜 (E →SLₚₜ[σ] F)) :
    ∃ (s : Finset E) (g : E → StrongDual 𝕜 F), ∀ T : E →SLₚₜ[σ] F,
      φ T = ∑ x ∈ s, g x (T x) := by
  classical
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous PointwiseConvergenceCLM.withSeminorms
    ((normSeminorm 𝕜 𝕜).comp (φ : (E →SLₚₜ[σ] F) →ₗ[𝕜] 𝕜)) (continuous_norm.comp φ.continuous)
  -- `Φ T` records the values of `T` on `s`; the sup norm of `Φ T` controls `φ T`.
  let Φ : (E →SLₚₜ[σ] F) →ₗ[𝕜] (s → F) :=
    { toFun T x := T x, map_add' _ _ := rfl, map_smul' _ _ := rfl }
  have hbound (T : E →SLₚₜ[σ] F) : ‖φ T‖ ≤ C * ‖Φ T‖ := by
    refine (hC T).trans ?_
    rw [smul_apply, NNReal.smul_def, smul_eq_mul]
    gcongr
    exact Seminorm.finset_sup_apply_le (norm_nonneg _) fun x hx ↦ norm_le_pi_norm (Φ T) ⟨x, hx⟩
  -- Hence `φ` factors through `Φ`, and the factor extends to `s → F` by Hahn–Banach.
  let f : Module.Dual 𝕜 (LinearMap.range Φ) := (φ : (E →SLₚₜ[σ] F) →ₗ[𝕜] 𝕜).compLeftInverse Φ
  have hf (T : E →SLₚₜ[σ] F) : f ⟨Φ T, LinearMap.mem_range_self Φ T⟩ = φ T :=
    LinearMap.compLeftInverse_apply_of_bdd _ _ ⟨C, hbound⟩ T (Φ T) rfl
  obtain ⟨G, hG, -⟩ := Module.Dual.exists_continuous_extension_of_le_seminorm
    (LinearMap.range Φ) f (p := C • normSeminorm 𝕜 (s → F))
    (continuous_norm.const_smul (C : ℝ)) (by
      rintro ⟨-, T, rfl⟩
      simpa [hf, NNReal.smul_def] using hbound T)
  refine ⟨s, fun x ↦ if hx : x ∈ s then G ∘L ContinuousLinearMap.single 𝕜 (fun _ : s ↦ F) ⟨x, hx⟩
    else 0, fun T ↦ ?_⟩
  rw [← hf, ← hG, ← Finset.sum_coe_sort s]
  simp only [Finset.coe_mem, dite_true]
  -- The coordinates of `Φ T` are the values `T x`, by definition of `Φ`.
  exact (ContinuousLinearMap.sum_comp_single 𝕜 (fun _ ↦ F) G (Φ T)).symm

end PointwiseConvergenceCLM
