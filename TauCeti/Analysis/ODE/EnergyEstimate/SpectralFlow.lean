/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Symmetric.Signature
public import TauCeti.Analysis.Matrix.HermitianSignature.RegularCrossings
public import TauCeti.Analysis.ODE.EnergyEstimate.Index

/-!
# The index of the trajectory operator is the spectral flow

Let `A : ℝ → End(E)` be a differentiable family of symmetric operators on a finite-dimensional
real inner product space `E`, with invertible limits `A±` at `±∞`, so that the trajectory operator `D_A u = u' + A u : W^{1,2}(ℝ, E) → L²(ℝ, E)` is Fredholm. A
*crossing* of `A` is a time `t` at which `A t` is not invertible, and its *crossing form* is the
quadratic form `v ↦ ⟪A' t v, v⟫` on the kernel of `A t`. The crossing is *regular* when its crossing
form is nondegenerate.

This file proves the formula of Robbin and Salamon for the index of `D_A` in this setting: if all
crossings of `A` are regular, then there are finitely many of them, and the index of `D_A` is the
sum over the crossings of the signatures of the crossing forms,

`index D_A = ∑ₜ (sigPos Γₜ - sigNeg Γₜ)`.

The right side is the spectral flow of `A`, the net number of eigenvalues of `A t` that cross zero
from negative to positive as `t` increases, so the index of `u ↦ u' + A u` is the spectral flow
of `A`. For instance, for `A s = tanh s` on `ℝ` the only crossing is at `0`, where the crossing form
`v ↦ v²` is positive definite, so the index is `1`: the kernel is spanned by `1 / cosh`.

The proof combines two computations. The index of `D_A` is the number of negative eigenvalues of
`A⁻` minus that of `A⁺`
(`TauCeti.WeakDerivStep.index_trajectoryOperator_eq_finrank_pointSpectralSubspace_sub_finrank`).
On the other hand, along the path of symmetric bilinear forms `⟪A t ·, ·⟫`, the negative index
drops between two invertible times by the sum of the signatures of the crossing forms in between
(`ContinuousLinearMap.sigNeg_sub_sigNeg_eq_finsum_sigPos_sub_sigNeg_crossingForm`). The negative
index of `⟪B ·, ·⟫` is the number of negative eigenvalues of `B`
(`LinearMap.IsSymmetric.sigNeg_toBilinForm_innerSL_comp`), and it is locally constant at
an invertible symmetric operator, so it agrees with that of `A±` at all large enough `±t`, where
`A t` is invertible (`TauCeti.exists_le_forall_ker_eq_bot_and_sigNeg_eq_of_tendsto`).

## Main results

* `TauCeti.finite_setOf_ker_ne_bot_of_tendsto`: a family of symmetric operators with invertible
  limits and only regular crossings has finitely many crossings.
* `TauCeti.WeakDerivStep.index_trajectoryOperator_eq_finsum_sigPos_sub_sigNeg_crossingForm`: the
  index of `u ↦ u' + A u` is the sum of the signatures of the crossing forms of `A`.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33, Section 4 (the index of `d/ds + A(s)` as the spectral flow, computed as
  a sum of crossing signatures).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic Geometry and Topology*, IAS/Park City
  Math. Ser. **7** (1999), Section 2.3 (the spectral flow and the index of the linearized
  gradient-flow operator).
-/

public section

open MeasureTheory TopologicalSpace Filter Set ContinuousLinearMap
open scoped ENNReal Topology InnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {A : ℝ → E →L[ℝ] E}

omit [FiniteDimensional ℝ E] in
/-- The path of bilinear forms `⟪A t ·, ·⟫` of a differentiable family `A` has derivative
`⟪A' t ·, ·⟫`. -/
private theorem hasDerivAt_innerSL_comp (hA : Differentiable ℝ A) (t : ℝ) :
    HasDerivAt (fun t ↦ (innerSL ℝ).comp (A t)) ((innerSL ℝ).comp (deriv A t)) t := by
  simpa using (hasDerivAt_const t (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)).clm_comp (hA t).hasDerivAt

omit [FiniteDimensional ℝ E] in
/-- The path of bilinear forms `⟪A t ·, ·⟫` of a differentiable family `A` is continuous. -/
private theorem continuous_innerSL_comp (hA : Differentiable ℝ A) :
    Continuous fun t ↦ (innerSL ℝ).comp (A t) :=
  continuous_const.clm_comp hA.continuous

/-- Regularity of the crossings of `A`, stated with the kernels of `A t`, in the form used for the
path of bilinear forms `⟪A t ·, ·⟫`: the crossing form is nondegenerate wherever `⟪A t ·, ·⟫` is
degenerate. -/
private theorem nondegenerate_crossingForm_of_not_nondegenerate
    (hreg : ∀ t, LinearMap.ker (A t : E →ₗ[ℝ] E) ≠ ⊥ →
      (crossingForm ((innerSL ℝ).comp (A t)) ((innerSL ℝ).comp (deriv A t))).Nondegenerate)
    (t : ℝ) (ht : ¬((innerSL ℝ).comp (A t)).toBilinForm.Nondegenerate) :
    (crossingForm ((innerSL ℝ).comp (A t)) ((innerSL ℝ).comp (deriv A t))).Nondegenerate :=
  hreg t (mt nondegenerate_toBilinForm_innerSL_comp_iff.2 ht)

/-- **Regular crossings are finitely many.** Let `A` be a differentiable family of symmetric
operators on a finite-dimensional real inner product space with invertible limits at `±∞`. If at
every crossing `t`, where `A t` is not injective, the crossing form `v ↦ ⟪A' t v, v⟫` on the
kernel of `A t` is nondegenerate, then there are finitely many crossings. -/
theorem finite_setOf_ker_ne_bot_of_tendsto (hA : Differentiable ℝ A)
    (hsym : ∀ s, (A s : E →ₗ[ℝ] E).IsSymmetric) {Aminus Aplus : E →L[ℝ] E}
    (hminus : LinearMap.ker (Aminus : E →ₗ[ℝ] E) = ⊥)
    (hplus : LinearMap.ker (Aplus : E →ₗ[ℝ] E) = ⊥)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (hreg : ∀ t, LinearMap.ker (A t : E →ₗ[ℝ] E) ≠ ⊥ →
      (crossingForm ((innerSL ℝ).comp (A t)) ((innerSL ℝ).comp (deriv A t))).Nondegenerate) :
    {t | LinearMap.ker (A t : E →ₗ[ℝ] E) ≠ ⊥}.Finite := by
  obtain ⟨a, b, -, hout, -, -⟩ :=
    exists_le_forall_ker_eq_bot_and_sigNeg_eq_of_tendsto hsym hminus hplus hbot htop
  have hfin := finite_setOf_not_nondegenerate_toBilinForm
    (continuous_innerSL_comp hA).continuousOn (a := a) (b := b)
    (fun t _ ↦ (hsym t).isSymm_toBilinForm_innerSL_comp)
    (nondegenerate_toBilinForm_innerSL_comp_iff.2 (hout a (by simp)))
    (nondegenerate_toBilinForm_innerSL_comp_iff.2 (hout b (by simp)))
    (fun t _ _ ↦ hasDerivAt_innerSL_comp hA t)
    (fun t _ ↦ nondegenerate_crossingForm_of_not_nondegenerate hreg t)
  refine hfin.subset fun t ht ↦ ⟨?_, mt nondegenerate_toBilinForm_innerSL_comp_iff.1 ht⟩
  by_contra hab
  exact ht (hout t fun h ↦ hab (Ioo_subset_Icc_self h))

namespace WeakDerivStep

/-- **The index of the trajectory operator is the spectral flow.** Let `A` be a differentiable
family of symmetric operators on a finite-dimensional real inner product space with invertible
limits `A±` at `±∞`. Suppose that every crossing `t` of `A`,
where `A t` is not injective, is regular: the crossing form `Γₜ : v ↦ ⟪A' t v, v⟫` on the kernel of
`A t` is nondegenerate. Then the index of the trajectory operator `u ↦ u' + A u` from
`W^{1,2}(ℝ, E)` to `L²(ℝ, E)` is the sum over the (finitely many) crossings of the signatures
`sigPos Γₜ - sigNeg Γₜ`. Times at which `A t` is invertible contribute zero to the sum. -/
theorem index_trajectoryOperator_eq_finsum_sigPos_sub_sigNeg_crossingForm
    (hA : Differentiable ℝ A) (hsym : ∀ s, (A s : E →ₗ[ℝ] E).IsSymmetric)
    {Aminus Aplus : E →L[ℝ] E} {α : ℝ} (hα : 0 < α)
    (hminus : ∀ v, α * ‖v‖ ≤ ‖Aminus v‖) (hplus : ∀ v, α * ‖v‖ ≤ ‖Aplus v‖)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A)
    (hreg : ∀ t, LinearMap.ker (A t : E →ₗ[ℝ] E) ≠ ⊥ →
      (crossingForm ((innerSL ℝ).comp (A t)) ((innerSL ℝ).comp (deriv A t))).Nondegenerate) :
    (trajectoryOperator (p := 2) AL).index =
      ∑ᶠ t, ((sigPos (crossingForm ((innerSL ℝ).comp (A t)) ((innerSL ℝ).comp (deriv A t))) : ℤ) -
        sigNeg (crossingForm ((innerSL ℝ).comp (A t)) ((innerSL ℝ).comp (deriv A t)))) := by
  obtain ⟨a, b, hab, hout, ha, hb⟩ := exists_le_forall_ker_eq_bot_and_sigNeg_eq_of_tendsto hsym
    (ker_eq_bot_of_mul_norm_le hα hminus) (ker_eq_bot_of_mul_norm_le hα hplus) hbot htop
  have hnd {s : ℝ} (hs : s ∉ Ioo a b) : ((innerSL ℝ).comp (A s)).toBilinForm.Nondegenerate :=
    nondegenerate_toBilinForm_innerSL_comp_iff.2 (hout s hs)
  have hcross := sigNeg_sub_sigNeg_eq_finsum_sigPos_sub_sigNeg_crossingForm hab
    (continuous_innerSL_comp hA).continuousOn (fun t _ ↦ (hsym t).isSymm_toBilinForm_innerSL_comp)
    (hnd (by simp)) (hnd (by simp)) (fun t _ _ ↦ hasDerivAt_innerSL_comp hA t)
    (fun t _ ↦ nondegenerate_crossingForm_of_not_nondegenerate hreg t)
  rw [index_trajectoryOperator_eq_finrank_pointSpectralSubspace_sub_finrank hA.continuous
      (isClosed_setOf_isSymmetric.mem_of_tendsto hbot (.of_forall hsym))
      (isClosed_setOf_isSymmetric.mem_of_tendsto htop (.of_forall hsym)) hα hminus hplus hbot htop
      AL hAL, ← ha, ← hb, hcross]
  -- Only crossings contribute, and all crossings lie in `(a, b)`.
  refine (finsum_mem_inter_support_eq' _ (Ioo a b) univ fun t ht ↦
    iff_of_true ?_ (mem_univ t)).trans (finsum_mem_univ _)
  by_contra hab
  exact ht (sigPos_sub_sigNeg_crossingForm_eq_zero (hnd hab) _)

end WeakDerivStep

end TauCeti
