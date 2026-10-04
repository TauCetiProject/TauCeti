/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The orthogonal projection onto the range of an operator

If `B : F →L[𝕜] V` is an operator between inner product spaces whose Gram operator `B† B` is
invertible, the orthogonal projection of `V` onto the range of `B` is `B (B† B)⁻¹ B†`. When `F` is
finite-dimensional, `B† B` is invertible exactly when `B` is injective.

Over `ℝ` this explicit formula shows that the projection depends smoothly on the operator: for a
`C^n` family of injective operators `A u : E →L[ℝ] V` out of a finite-dimensional real normed
space `E`, the orthogonal projections of `V` onto the ranges of `A u` form a `C^n` family. Applied
to the derivative of an immersion into a Euclidean space, this says that the tangent spaces, and
hence the normal spaces, of an immersed submanifold vary smoothly.

## Main results

* `ContinuousLinearMap.isUnit_adjoint_comp_self`: the Gram operator of an injective operator out
  of a finite-dimensional space is invertible.
* `ContinuousLinearMap.starProjection_range_eq`: the formula `B (B† B)⁻¹ B†` for the orthogonal
  projection onto the range of `B`.
* `ContDiffAt.starProjection_range`: the orthogonal projection onto the range of a `C^n` family of
  injective operators is `C^n`.
-/

public section

open Function Filter Topology

namespace ContinuousLinearMap

variable {𝕜 F V : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [CompleteSpace F] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]

/-- The Gram operator `B† B` of an injective operator out of a finite-dimensional space is
invertible. -/
theorem isUnit_adjoint_comp_self [FiniteDimensional 𝕜 F] {B : F →L[𝕜] V} (hB : Injective B) :
    IsUnit (adjoint B ∘L B) := by
  have hinj : Injective (adjoint B ∘L B) := by
    rw [coe_comp]
    exact (adjoint_comp_self_injective_iff B).mpr hB
  exact isUnit_iff_bijective.mpr ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- The orthogonal projection onto the range of `B` is `B (B† B)⁻¹ B†`, when the Gram operator
`B† B` is invertible. -/
theorem starProjection_range_eq {B : F →L[𝕜] V} [B.range.HasOrthogonalProjection]
    (hB : IsUnit (adjoint B ∘L B)) :
    B.range.starProjection = B ∘L Ring.inverse (adjoint B ∘L B) ∘L adjoint B := by
  have hG : (adjoint B ∘L B) ∘L Ring.inverse (adjoint B ∘L B) = 1 :=
    Ring.mul_inverse_cancel _ hB
  ext v
  rw [comp_apply, comp_apply]
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (LinearMap.mem_range_self (B : F →ₗ[𝕜] V) _) ?_
  rintro _ ⟨x, rfl⟩
  have h := congrArg (fun T : F →L[𝕜] F => T (adjoint B v)) hG
  simp only [comp_apply, one_apply_eq_self] at h
  rw [coe_coe, inner_sub_left, ← adjoint_inner_left, ← adjoint_inner_left, h, sub_self]

end ContinuousLinearMap

variable {X E V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The orthogonal projection onto the range of a `C^n` family of operators out of a
finite-dimensional space is `C^n` at every point where the operator is injective. -/
theorem ContDiffAt.starProjection_range {A : X → E →L[ℝ] V} {u₀ : X} {n : WithTop ℕ∞}
    (hA : ContDiffAt ℝ n A u₀) (hinj : Injective (A u₀)) :
    ContDiffAt ℝ n (fun u => (A u).range.starProjection) u₀ := by
  -- Precompose with a linear isomorphism from a Euclidean space, so that adjoints exist.
  let F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let j : F ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq (by simp [F])
  let B : X → F →L[ℝ] V := fun u => (A u).comp (j : F →L[ℝ] E)
  have hrange : ∀ u, (B u).range = (A u).range := fun u =>
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr j.surjective)
  have hB : ContDiffAt ℝ n B u₀ := hA.clm_comp contDiffAt_const
  have hadj : ContDiff ℝ n fun T : F →L[ℝ] V => ContinuousLinearMap.adjoint T :=
    IsBoundedLinearMap.contDiff
      { map_add := fun T S => map_add _ T S
        map_smul := fun c T => by simp
        bound := ⟨1, one_pos, fun T => by simp⟩ }
  have hB' : ContDiffAt ℝ n (fun u => ContinuousLinearMap.adjoint (B u)) u₀ :=
    hadj.contDiffAt.comp u₀ hB
  have hG : IsUnit (ContinuousLinearMap.adjoint (B u₀) ∘L B u₀) :=
    ContinuousLinearMap.isUnit_adjoint_comp_self (hinj.comp j.injective)
  have hinv : ContDiffAt ℝ n
      (fun u => Ring.inverse (ContinuousLinearMap.adjoint (B u) ∘L B u)) u₀ := by
    have := contDiffAt_ringInverse ℝ (n := n) hG.unit
    rw [hG.unit_spec] at this
    exact this.comp u₀ (hB'.clm_comp hB)
  -- Near `u₀` the operators stay injective, so the projection is given by the Gram formula.
  have hev : ∀ᶠ u in 𝓝 u₀, Injective (B u) :=
    hB.continuousAt.preimage_mem_nhds
      (ContinuousLinearMap.isOpen_injective.mem_nhds (hinj.comp j.injective))
  refine (hB.clm_comp (hinv.clm_comp hB')).congr_of_eventuallyEq ?_
  filter_upwards [hev] with u hu
  simp only [← hrange u]
  exact ContinuousLinearMap.starProjection_range_eq
    (ContinuousLinearMap.isUnit_adjoint_comp_self hu)
