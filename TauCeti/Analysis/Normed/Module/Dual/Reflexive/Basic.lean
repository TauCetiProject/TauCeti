/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import TauCeti.Analysis.Normed.Module.Dual.Adjoint

/-!
# Reflexivity and the continuous dual

A normed space is reflexive when its canonical map into the continuous bidual is
surjective. This file proves that reflexivity passes to the continuous dual, that
the converse holds for Banach spaces, and that bounded linear equivalences preserve
reflexivity. Reflexivity is expressed directly as surjectivity of
`NormedSpace.inclusionInDoubleDual`.

The forward implication needs no completeness. Reflexivity itself implies completeness
over real or complex scalars. Completeness is essential in the reverse implication:
a proper dense subspace of a Hilbert space can have a reflexive continuous dual.

The converse uses `ContinuousLinearMap.surjective_of_norm_le_norm_comp`, the
surjectivity criterion for an operator whose adjoint is bounded below. The bidual
isometry is Mathlib's `NormedSpace.inclusionInDoubleDualLi`.

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

section Complete

variable {𝕜 E : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A reflexive seminormed space over real or complex scalars is complete. -/
theorem completeSpace_of_surjective_inclusionInDoubleDual
    (hE : Surjective (inclusionInDoubleDual 𝕜 E)) : CompleteSpace E :=
  ((inclusionInDoubleDualLi 𝕜 (E := E)).isometry.isUniformInducing.completeSpace_congr hE).2
    inferInstance

end Complete

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
