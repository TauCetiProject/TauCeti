/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import TauCeti.Analysis.Normed.Module.Dual.Adjoint
import TauCeti.Analysis.Normed.Module.Annihilator

/-!
# Reflexivity and the continuous dual

A normed space is reflexive when its canonical map into the continuous bidual is
surjective. This file proves that finite-dimensional spaces are reflexive, that reflexivity
passes to the continuous dual, that the converse holds for Banach spaces, and that bounded
linear equivalences preserve reflexivity. Reflexivity is expressed directly as surjectivity of
`NormedSpace.inclusionInDoubleDual`.

The forward implication needs no completeness. Reflexivity itself implies completeness
over real or complex scalars. Completeness is essential in the reverse implication:
a proper dense subspace of a Hilbert space can have a reflexive continuous dual.

The converse uses `ContinuousLinearMap.surjective_of_norm_le_norm_comp`, the
surjectivity criterion for an operator whose adjoint is bounded below. The bidual
isometry is Mathlib's `NormedSpace.inclusionInDoubleDualLi`. Through it, every bounded bilinear
form on `E* × E` over a reflexive space `E` is `(f, x) ↦ f (T x)` for an operator `T` of no larger
norm (`TauCeti.exists_apply_eq_and_norm_le_of_surjective_inclusionInDoubleDual`).

Finally, `LinearIsometry.surjective_of_surjective_inclusionInDoubleDual` is the standard
surjectivity criterion for representing the dual of a reflexive space: a linear isometry from a
Banach space into the continuous dual of a reflexive space is onto when its functionals separate
points.

## References

* R. E. Megginson, *An Introduction to Banach Space Theory*, §2.6.
-/

public section

open Function NormedSpace

namespace TauCeti

section Dual

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The continuous dual of a reflexive seminormed space is reflexive.
No completeness assumption on the original space is needed. -/
theorem surjective_inclusionInDoubleDual_strongDual
    (hE : Surjective (inclusionInDoubleDual 𝕜 E)) :
    Surjective (inclusionInDoubleDual 𝕜 (StrongDual 𝕜 E)) := by
  intro Φ
  refine ⟨Φ.comp (inclusionInDoubleDual 𝕜 E), ?_⟩
  ext y
  obtain ⟨x, rfl⟩ := hE y
  rfl

end Dual

section FiniteDimensional

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- A finite-dimensional normed space is reflexive: every functional on the continuous dual is a
functional on the algebraic dual, which is evaluation at a point (`Module.bijective_dual_eval`). -/
theorem surjective_inclusionInDoubleDual_of_finiteDimensional :
    Surjective (inclusionInDoubleDual 𝕜 E) := by
  intro χ
  let e : Module.Dual 𝕜 E ≃ₗ[𝕜] StrongDual 𝕜 E := LinearMap.toContinuousLinearMap
  obtain ⟨x, hx⟩ := (Module.bijective_dual_eval 𝕜 E).2 (χ.toLinearMap ∘ₗ e.toLinearMap)
  refine ⟨x, ContinuousLinearMap.ext fun f ↦ ?_⟩
  have := LinearMap.congr_fun hx (e.symm f)
  rwa [LinearMap.comp_apply, LinearEquiv.coe_coe, e.apply_symm_apply] at this

variable (𝕜 E) in
/-- Evaluation identifies a finite-dimensional normed space with its continuous double dual, as a
topological linear isomorphism (`TauCeti.inclusionInDoubleDualEquiv_apply`). -/
noncomputable def inclusionInDoubleDualEquiv : E ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E) :=
  let c : Module.Dual 𝕜 E ≃ₗ[𝕜] StrongDual 𝕜 E := LinearMap.toContinuousLinearMap
  LinearEquiv.toContinuousLinearEquiv (𝕜 := 𝕜) (E := E) (F := StrongDual 𝕜 (StrongDual 𝕜 E))
    ((Module.evalEquiv 𝕜 E).trans
      ((c.arrowCongr (LinearEquiv.refl 𝕜 𝕜)).trans LinearMap.toContinuousLinearMap))

/-- The finite-dimensional double-dual equivalence is `NormedSpace.inclusionInDoubleDual`. -/
@[simp]
theorem inclusionInDoubleDualEquiv_apply (x : E) :
    inclusionInDoubleDualEquiv 𝕜 E x = inclusionInDoubleDual 𝕜 E x := by
  ext f
  simp [inclusionInDoubleDualEquiv, dual_def]

/-- The finite-dimensional double-dual equivalence extends `NormedSpace.inclusionInDoubleDual`. -/
@[simp]
theorem toContinuousLinearMap_inclusionInDoubleDualEquiv :
    (inclusionInDoubleDualEquiv 𝕜 E).toContinuousLinearMap = inclusionInDoubleDual 𝕜 E :=
  ContinuousLinearMap.ext inclusionInDoubleDualEquiv_apply

/-- The inverse of the finite-dimensional double-dual equivalence sends a functional `Φ` on the
dual to the point at which every functional `f` takes the value `Φ f`. -/
@[simp]
theorem apply_inclusionInDoubleDualEquiv_symm (Φ : StrongDual 𝕜 (StrongDual 𝕜 E))
    (f : StrongDual 𝕜 E) : f ((inclusionInDoubleDualEquiv 𝕜 E).symm Φ) = Φ f := by
  conv_rhs => rw [← (inclusionInDoubleDualEquiv 𝕜 E).apply_symm_apply Φ]
  rw [inclusionInDoubleDualEquiv_apply, dual_def]

end FiniteDimensional

section Complete

variable {𝕜 E : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A reflexive seminormed space over real or complex scalars is complete. -/
theorem completeSpace_of_surjective_inclusionInDoubleDual
    (hE : Surjective (inclusionInDoubleDual 𝕜 E)) : CompleteSpace E :=
  ((inclusionInDoubleDualLi 𝕜 (E := E)).isometry.isUniformInducing.completeSpace_congr hE).2
    inferInstance

end Complete

section Bilinear

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- On a reflexive space `E`, every bounded bilinear form `B` on `E* × E` has the form
`(f, x) ↦ f (T x)` for an operator `T` on `E` with `‖T‖ ≤ ‖B‖`: `T x` is the vector whose
evaluation map is `B (·) x`. -/
theorem exists_apply_eq_and_norm_le_of_surjective_inclusionInDoubleDual
    (hE : Surjective (inclusionInDoubleDual 𝕜 E)) (B : StrongDual 𝕜 E →L[𝕜] E →L[𝕜] 𝕜) :
    ∃ T : E →L[𝕜] E, (∀ f x, f (T x) = B f x) ∧ ‖T‖ ≤ ‖B‖ := by
  obtain ⟨e, he⟩ : ∃ e : E ≃ₗᵢ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E),
      ∀ y, e y = inclusionInDoubleDual 𝕜 E y :=
    ⟨.ofSurjective (inclusionInDoubleDualLi 𝕜) hE, fun y ↦ by simp [inclusionInDoubleDualLi]⟩
  obtain ⟨T, hT⟩ : ∃ T : E →L[𝕜] E, ∀ x, e (T x) = B.flip x :=
    ⟨e.symm.toLinearIsometry.toContinuousLinearMap ∘L B.flip, fun x ↦ e.apply_symm_apply _⟩
  have hTx (f : StrongDual 𝕜 E) (x : E) : f (T x) = B f x := by
    simpa [he, dual_def] using congr($(hT x) f)
  refine ⟨T, hTx, T.opNorm_le_bound (norm_nonneg B) fun x ↦ ?_⟩
  rw [← e.norm_map]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun f ↦ ?_
  rw [he, dual_def, hTx]
  exact (B.le_opNorm₂ f x).trans_eq (mul_right_comm _ _ _)

end Bilinear

section Banach

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- A Banach space is reflexive if its continuous dual is reflexive. -/
theorem surjective_inclusionInDoubleDual_of_strongDual
    (hE : Surjective (inclusionInDoubleDual 𝕜 (StrongDual 𝕜 E))) :
    Surjective (inclusionInDoubleDual 𝕜 E) := by
  refine ContinuousLinearMap.surjective_of_norm_le_norm_comp
    (𝕜 := 𝕜) (F := StrongDual 𝕜 (StrongDual 𝕜 E))
    (inclusionInDoubleDual 𝕜 E) (K := 1) ?_
  intro Φ
  obtain ⟨f, rfl⟩ := hE Φ
  have hcomp : (inclusionInDoubleDual 𝕜 (StrongDual 𝕜 E) f).comp
      (inclusionInDoubleDual 𝕜 E) = f := by
    ext x
    rfl
  rw [hcomp]
  simp only [NNReal.coe_one, one_mul]
  exact le_of_eq ((inclusionInDoubleDualLi 𝕜 (E := StrongDual 𝕜 E)).norm_map f)

/-- A Banach space is reflexive exactly when its continuous dual is reflexive. -/
@[simp]
theorem surjective_inclusionInDoubleDual_strongDual_iff :
    Surjective (inclusionInDoubleDual 𝕜 (StrongDual 𝕜 E)) ↔
      Surjective (inclusionInDoubleDual 𝕜 E) :=
  ⟨surjective_inclusionInDoubleDual_of_strongDual,
    surjective_inclusionInDoubleDual_strongDual⟩

end Banach

end TauCeti

namespace ContinuousLinearEquiv

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Reflexivity is invariant under bounded linear equivalence, without completeness
assumptions on either space. -/
theorem surjective_inclusionInDoubleDual_iff (e : E ≃L[𝕜] F) :
    Surjective (inclusionInDoubleDual 𝕜 E) ↔
      Surjective (inclusionInDoubleDual 𝕜 F) := by
  let d := e.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜)
  let dd := d.arrowCongr (ContinuousLinearEquiv.refl 𝕜 𝕜)
  have h : dd ∘ inclusionInDoubleDual 𝕜 E = inclusionInDoubleDual 𝕜 F ∘ e := by
    ext x f
    simp [dd, d]
  rw [← Surjective.of_comp_iff' dd.bijective (inclusionInDoubleDual 𝕜 E), h,
    Surjective.of_comp_iff _ e.surjective]

end ContinuousLinearEquiv

namespace LinearIsometry

variable {𝕜 X Y : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- A linear isometry `T` from a Banach space into the continuous dual of a reflexive space `Y` is
onto when the functionals `T x` separate the points of `Y`: a functional on `Y⋆` annihilating the
closed range of `T` is evaluation at some `y ∈ Y`, which must vanish. -/
theorem surjective_of_surjective_inclusionInDoubleDual (T : X →ₗᵢ[𝕜] StrongDual 𝕜 Y)
    (hY : Surjective (inclusionInDoubleDual 𝕜 Y)) (h : ∀ y, (∀ x, T x y = 0) → y = 0) :
    Surjective T := by
  let S := T.toLinearMap.range
  have hS : IsClosed (S : Set (StrongDual 𝕜 Y)) := T.isometry.isClosedEmbedding.isClosed_range
  intro Λ
  suffices Λ ∈ S.topologicalClosure by
    rw [hS.submodule_topologicalClosure_eq] at this
    exact this
  apply (S.mem_topologicalClosure_iff_forall_dual_eq_zero Λ).2
  intro Ψ hΨ
  obtain ⟨y, rfl⟩ := hY Ψ
  have hy : y = 0 := h y fun x ↦ by
    rw [← dual_def]
    exact hΨ (T x) (LinearMap.mem_range_self T.toLinearMap x)
  simp [hy]

end LinearIsometry
