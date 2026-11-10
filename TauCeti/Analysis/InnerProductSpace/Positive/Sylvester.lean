/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Sylvester
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Algebra.Algebra.StrictPositivity
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Topology.Algebra.Module.Equiv.Submodule

/-!
# Positive Sylvester equations and the derivative of squaring

For a strictly positive operator `A` and a nonnegative operator `B` on finite-dimensional
inner product spaces, the equation `A X + X B = C` has a unique solution. We package its
Sylvester operator as `ContinuousLinearMap.positiveSylvesterEquiv`, whose inverse solves
the equation, using the existing operator `A.sylvester (-B)`. No eigenbasis choices enter
this equivalence.

When `B = A`, the solution commutes with taking adjoints, and hence restricts to an
isomorphism on self-adjoint operators. This is the linear equation obtained by
differentiating `S² = H`: the derivative of squaring at `S` sends `K` to `S K + K S`.
Its invertibility at positive `S` is the linear input to the inverse-function argument
for smooth dependence of positive square roots. This file proves that input, not
smoothness of the square-root map itself.

## References

* R. Bhatia, *Positive Definite Matrices*, Princeton University Press (2007).
-/

public section

noncomputable section

open InnerProductSpace Module
open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  {A : E →L[𝕜] E} {B : F →L[𝕜] F}

/-- A strictly positive operator and the negative of a nonnegative operator have disjoint
real point spectra. The two operators may act on different spaces. -/
theorem disjoint_restrictedPointSpectrum_neg_of_isStrictlyPositive [CompleteSpace E]
    (hA : IsStrictlyPositive A) (hB : 0 ≤ B) :
    Disjoint (End.restrictedPointSpectrum (A : E →ₗ[𝕜] E) ⊤)
      (End.restrictedPointSpectrum ((-B) : F →ₗ[𝕜] F) ⊤) := by
  have hAp := (nonneg_iff_isPositive.mp hA.nonneg).toLinearMap
  have hBp := (nonneg_iff_isPositive.mp hB).toLinearMap
  have hleft : End.PointSpectrumIn (A : E →ₗ[𝕜] E) ⊤ (Set.Ici 0) :=
    End.pointSpectrumIn_Ici_of_le_re_inner_apply_self fun x _ ↦ by
      simpa using hAp.re_inner_nonneg_left x
  have hright : End.PointSpectrumIn ((-B) : F →ₗ[𝕜] F) ⊤ (Set.Iic 0) :=
    End.pointSpectrumIn_Iic_of_re_inner_apply_self_le fun x _ ↦ by
      simpa using neg_nonpos.mpr (hBp.re_inner_nonneg_left x)
  refine Set.disjoint_left.2 fun μ hμA hμB ↦ ?_
  have hμ : μ = 0 := le_antisymm
    ((End.pointSpectrumIn_iff_restrictedPointSpectrum_subset.mp hright) hμB)
    ((End.pointSpectrumIn_iff_restrictedPointSpectrum_subset.mp hleft) hμA)
  obtain ⟨x, -, hx, hAx⟩ := End.mem_restrictedPointSpectrum_iff.1 hμA
  have hinj := (isUnit_iff_bijective.mp hA.isUnit).injective
  apply hx
  apply hinj
  simpa [hμ] using hAx

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

/-- The positive Sylvester operator `X ↦ A X + X B` as a continuous linear equivalence.
Only `A` needs to be strictly positive; `B` may have a kernel. -/
def positiveSylvesterEquiv (hA : IsStrictlyPositive A) (hB : 0 ≤ B) :
    (F →L[𝕜] E) ≃L[𝕜] (F →L[𝕜] E) :=
  letI := FiniteDimensional.complete 𝕜 E
  let h := sylvester_bijective (A := A) (B := -B)
    (by
      intro x y
      simp only [coe_coe, neg_apply, inner_neg_left, inner_neg_right]
      exact congrArg Neg.neg ((nonneg_iff_isPositive.mp hB).isSymmetric x y))
    (disjoint_restrictedPointSpectrum_neg_of_isStrictlyPositive hA hB)
  .ofBijective (A.sylvester (-B)) (LinearMap.ker_eq_bot.mpr h.injective)
    (LinearMap.range_eq_top.mpr h.surjective)

/-- The positive Sylvester equivalence sends `X` to `A X + X B`. -/
@[simp]
theorem positiveSylvesterEquiv_apply (hA : IsStrictlyPositive A) (hB : 0 ≤ B)
    (X : F →L[𝕜] E) :
    positiveSylvesterEquiv hA hB X = A ∘L X + X ∘L B := by
  simp [positiveSylvesterEquiv, sylvester_apply]

/-- Applying the inverse solves the positive Sylvester equation. -/
@[simp]
theorem comp_positiveSylvesterEquiv_symm_add (hA : IsStrictlyPositive A) (hB : 0 ≤ B)
    (C : F →L[𝕜] E) :
    A ∘L (positiveSylvesterEquiv hA hB).symm C +
      (positiveSylvesterEquiv hA hB).symm C ∘L B = C := by
  simpa only [positiveSylvesterEquiv_apply] using
    (positiveSylvesterEquiv hA hB).apply_symm_apply C

/-- The inverse equivalence recovers `X` from `A X + X B`. -/
@[simp]
theorem positiveSylvesterEquiv_symm_comp_add_comp (hA : IsStrictlyPositive A) (hB : 0 ≤ B)
    (X : F →L[𝕜] E) :
    (positiveSylvesterEquiv hA hB).symm (A ∘L X + X ∘L B) = X := by
  rw [← positiveSylvesterEquiv_apply hA hB, ContinuousLinearEquiv.symm_apply_apply]

/-- A solution of the positive Sylvester equation is the value of the inverse equivalence. -/
theorem comp_add_comp_eq_iff_eq_positiveSylvesterEquiv_symm (hA : IsStrictlyPositive A) (hB : 0 ≤ B)
    {X C : F →L[𝕜] E} :
    A ∘L X + X ∘L B = C ↔ X = (positiveSylvesterEquiv hA hB).symm C := by
  rw [← positiveSylvesterEquiv_apply hA hB, ContinuousLinearEquiv.eq_symm_apply]

section Adjoint

variable [CompleteSpace E]

/-- For the equation `A X + X A = C`, solving commutes with taking adjoints. -/
@[simp]
theorem adjoint_positiveSylvesterEquiv_symm (hA : IsStrictlyPositive A) (C : E →L[𝕜] E) :
    adjoint ((positiveSylvesterEquiv hA hA.nonneg).symm C) =
      (positiveSylvesterEquiv hA hA.nonneg).symm (adjoint C) := by
  apply (comp_add_comp_eq_iff_eq_positiveSylvesterEquiv_symm hA hA.nonneg).1
  have h := congrArg adjoint (comp_positiveSylvesterEquiv_symm_add hA hA.nonneg C)
  simpa only [map_add, adjoint_comp,
    ((nonneg_iff_isPositive.mp hA.nonneg).isSelfAdjoint).adjoint_eq, add_comm] using h

/-- The solution of `A X + X A = C` is self-adjoint exactly when `C` is self-adjoint. -/
@[simp]
theorem isSelfAdjoint_positiveSylvesterEquiv_symm_iff (hA : IsStrictlyPositive A)
    (C : E →L[𝕜] E) :
    IsSelfAdjoint ((positiveSylvesterEquiv hA hA.nonneg).symm C) ↔ IsSelfAdjoint C := by
  simp only [isSelfAdjoint_iff, star_eq_adjoint, adjoint_positiveSylvesterEquiv_symm,
    (positiveSylvesterEquiv hA hA.nonneg).symm.injective.eq_iff]

section RealScalars

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [StarModule ℝ (E →L[𝕜] E)]

/-- The positive Sylvester equivalence restricted to the real subspace of self-adjoint
operators. Its inverse solves the equation within that subspace. -/
def positiveSylvesterSelfAdjointEquiv (hA : IsStrictlyPositive A) :
    (selfAdjoint.submodule ℝ (E →L[𝕜] E)) ≃L[ℝ]
      (selfAdjoint.submodule ℝ (E →L[𝕜] E)) :=
  ((positiveSylvesterEquiv hA hA.nonneg).restrictScalars ℝ).ofSubmodules _ _ (by
    ext C
    -- Mathlib has no membership lemma for selfAdjoint.submodule, so expose its predicate here.
    change (∃ X, IsSelfAdjoint X ∧
      (positiveSylvesterEquiv hA hA.nonneg) X = C) ↔ IsSelfAdjoint C
    constructor
    · rintro ⟨X, hX, rfl⟩
      exact (isSelfAdjoint_positiveSylvesterEquiv_symm_iff hA _).mp (by
        simpa only [ContinuousLinearEquiv.symm_apply_apply] using hX)
    · intro hC
      exact ⟨(positiveSylvesterEquiv hA hA.nonneg).symm C,
        (isSelfAdjoint_positiveSylvesterEquiv_symm_iff hA C).mpr hC,
        (positiveSylvesterEquiv hA hA.nonneg).apply_symm_apply C⟩)

/-- The self-adjoint restriction has the same formula `X ↦ A X + X A`. -/
@[simp]
theorem coe_positiveSylvesterSelfAdjointEquiv_apply (hA : IsStrictlyPositive A)
    (X : selfAdjoint.submodule ℝ (E →L[𝕜] E)) :
    (positiveSylvesterSelfAdjointEquiv hA X : E →L[𝕜] E) = A ∘L X + (X : E →L[𝕜] E) ∘L A := by
  simp [positiveSylvesterSelfAdjointEquiv]

/-- The inverse self-adjoint restriction is the unrestricted solution operator. -/
@[simp]
theorem coe_positiveSylvesterSelfAdjointEquiv_symm_apply (hA : IsStrictlyPositive A)
    (C : selfAdjoint.submodule ℝ (E →L[𝕜] E)) :
    ((positiveSylvesterSelfAdjointEquiv hA).symm C : E →L[𝕜] E) =
      (positiveSylvesterEquiv hA hA.nonneg).symm C := by
  simp [positiveSylvesterSelfAdjointEquiv]

end RealScalars

omit [CompleteSpace E] in
/-- Squaring has the positive Sylvester equivalence as its strict derivative at a strictly
positive operator. In particular this derivative is invertible, including in dimension zero. -/
theorem hasStrictFDerivAt_mul_self_positiveSylvesterEquiv (hA : IsStrictlyPositive A) :
    HasStrictFDerivAt (fun S : E →L[𝕜] E ↦ S * S)
      (positiveSylvesterEquiv hA hA.nonneg : (E →L[𝕜] E) →L[𝕜] (E →L[𝕜] E)) A := by
  refine ((hasStrictFDerivAt_id (𝕜 := 𝕜) A).mul'
    (hasStrictFDerivAt_id (𝕜 := 𝕜) A)).congr_fderiv ?_
  ext X
  simp only [ContinuousLinearEquiv.coe_coe, positiveSylvesterEquiv_apply]
  -- Both sides now evaluate the product rule as A (X x) + X (A x).
  rfl

end Adjoint

end ContinuousLinearMap
