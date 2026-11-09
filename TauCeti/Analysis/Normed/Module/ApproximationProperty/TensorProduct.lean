/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.ApproximationProperty.Basic
public import TauCeti.Analysis.Normed.Operator.Nuclear
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import TauCeti.Analysis.Normed.Module.TensorProduct.Associator
import TauCeti.Analysis.Normed.Module.TensorProduct.IntegralBilinearForm
import TauCeti.Analysis.Normed.Module.TensorProduct.Series

/-!
# The approximation property and completed tensor products

Let `E` and `F` be normed spaces over `ℝ` or `ℂ`. The elementary functionals
`x ⊗ₜ y ↦ f x * g y`, for `f ∈ E*` and `g ∈ F*`, are bounded for the injective norm, so they
factor through the contraction `E ⊗̂π F → E ⊗̂ε F`. This file proves that they separate the
points of the completed projective tensor product `E ⊗̂π F` as soon as one of the two factors
has the approximation property. Consequently:

* the contraction `E ⊗̂π F → E ⊗̂ε F` is injective when `E` or `F` has the approximation
  property;
* for a Banach space `F`, the canonical operator `E* ⊗̂π F → (E →L[𝕜] F)`, whose range is the
  space of nuclear operators, is injective when `E*` or `F` has the approximation property. This
  uses `injective_toContinuousLinearMap_iff` from `TauCeti.Analysis.Normed.Operator.Nuclear`: the
  operator is injective exactly when the contraction `E* ⊗̂π F → E* ⊗̂ε F` is.

Under these hypotheses a nuclear operator therefore has a unique representing tensor.

The proof follows Grothendieck. Write `u = ∑ n, x n ⊗ₜ y n` with `∑ n, ‖x n‖` finite and
`y n → 0`, and let `B` be a bounded bilinear form on `E × F`. If `F` has the approximation
property, there is a finite-rank operator `R` on `F` within `δ` of the identity on the compact set
`{y n} ∪ {0}`. The form `(x, y) ↦ B x (R y)` is a finite sum of elementary forms, so it vanishes on
`u` when all elementary functionals do, while it differs from `B` on `u` by at most
`‖B‖ * δ * ∑ n, ‖x n‖`.

## Main results

All declarations are in the namespace `TauCeti.CompletedProjectiveTensor`.

* `eq_zero_of_hasApproximationProperty_right` and `eq_zero_of_hasApproximationProperty_left`: if
  `F`, or `E`, has the approximation property, an element of `E ⊗̂π F` on which every elementary
  functional vanishes is zero.
* `injective_toCompletedInjectiveTensor_of_hasApproximationProperty_right` and its `_left`
  counterpart: the contraction `E ⊗̂π F → E ⊗̂ε F` is injective.
* `injective_toContinuousLinearMap_of_hasApproximationProperty` and
  `injective_toContinuousLinearMap_of_hasApproximationProperty_strongDual`: the canonical operator
  is injective when `F`, or `E*`, has the approximation property.

## References

* A. Grothendieck, *Produits tensoriels topologiques et espaces nucléaires*, Mem. Amer. Math.
  Soc. **16** (1955).
* R. A. Ryan, *Introduction to Tensor Products of Banach Spaces*, Springer, 2002, Chapter 4.
-/

public section

open Filter Set
open scoped TensorProduct Topology

namespace TauCeti.CompletedProjectiveTensor

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If every elementary functional vanishes on `u`, then so does the functional induced by
`(x, y) ↦ B x (R y)` for a finite-rank operator `R`, which is a finite sum of elementary
functionals. -/
private theorem liftIsometry_bilinearComp_eq_zero {u : CompletedProjectiveTensor 𝕜 E F}
    (hu : ∀ (f : StrongDual 𝕜 E) (g : StrongDual 𝕜 F),
      liftIsometry 𝕜 E F 𝕜 (f.smulRight g) u = 0)
    (B : E →L[𝕜] F →L[𝕜] 𝕜) {R : F →L[𝕜] F} (hR : R.toLinearMap.HasFiniteRange) :
    liftIsometry 𝕜 E F 𝕜 (B.bilinearComp (ContinuousLinearMap.id 𝕜 E) R) u = 0 := by
  obtain ⟨⟨w⟩, rfl⟩ := (InjectiveTensor.mem_range_toOperator_iff R).2 hR
  simp only [LinearIsometry.coe_toLinearMap, InjectiveTensor.toOperator_mk]
  clear hR
  induction w with
  | tmul g z =>
    have : B.bilinearComp (ContinuousLinearMap.id 𝕜 E) (TensorProduct.toOperator (g ⊗ₜ z)) =
        (B.flip z).smulRight g := by
      ext x y
      simp [mul_comm]
    rw [this]
    exact hu _ _
  | add w w' hw hw' =>
    have : B.bilinearComp (ContinuousLinearMap.id 𝕜 E) (TensorProduct.toOperator (w + w')) =
        B.bilinearComp (ContinuousLinearMap.id 𝕜 E) (TensorProduct.toOperator w) +
          B.bilinearComp (ContinuousLinearMap.id 𝕜 E) (TensorProduct.toOperator w') := by
      ext x y
      simp
    rw [this, map_add]
    simp [hw, hw']

/-- **Elementary functionals separate points under the approximation property.** If `F` has the
approximation property, an element of `E ⊗̂π F` on which every functional
`x ⊗ₜ y ↦ f x * g y` vanishes is zero. -/
theorem eq_zero_of_hasApproximationProperty_right (hF : HasApproximationProperty 𝕜 F)
    {u : CompletedProjectiveTensor 𝕜 E F}
    (hu : ∀ (f : StrongDual 𝕜 E) (g : StrongDual 𝕜 F),
      liftIsometry 𝕜 E F 𝕜 (f.smulRight g) u = 0) :
    u = 0 := by
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := 𝕜) fun Λ ↦ ?_
  obtain ⟨B, rfl⟩ := (liftIsometry 𝕜 E F 𝕜).surjective Λ
  obtain ⟨x, y, hxy, hx, hy⟩ := exists_hasSum_tmul_tendsto_zero u
  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε ↦ ?_)
  set S := ∑' n, ‖x n‖ with hS_def
  have hS : 0 ≤ S := tsum_nonneg fun n ↦ norm_nonneg _
  set δ := ε / ((‖B‖ + 1) * (S + 1)) with hδ_def
  have hδ : 0 < δ := by positivity
  -- A finite-rank operator `R` within `δ` of the identity on the compact set `{y n} ∪ {0}`.
  obtain ⟨R, hR, hRy⟩ := hasApproximationProperty_iff.1 hF _ hy.isCompact_insert_range δ hδ
  -- The form `(x, y) ↦ B x y - B x (R y)` takes the same value as `B` on `u`, and is small on
  -- each term of the series.
  have hsum : HasSum (fun n ↦ B (x n) (y n - R (y n))) (liftIsometry 𝕜 E F 𝕜 B u) := by
    have h := hxy.map (liftIsometry 𝕜 E F 𝕜 (B - B.bilinearComp (ContinuousLinearMap.id 𝕜 E) R))
      (ContinuousLinearMap.continuous _)
    rw [LinearIsometryEquiv.map_sub, sub_apply,
      liftIsometry_bilinearComp_eq_zero hu B hR, sub_zero] at h
    simpa [Function.comp_def] using h
  have hbound (n : ℕ) : ‖B (x n) (y n - R (y n))‖ ≤ ‖B‖ * δ * ‖x n‖ := by
    have hn : ‖y n - R (y n)‖ ≤ δ := by
      rw [norm_sub_rev]
      exact (hRy _ (mem_insert_of_mem _ (mem_range_self n))).le
    calc ‖B (x n) (y n - R (y n))‖ ≤ ‖B‖ * ‖x n‖ * ‖y n - R (y n)‖ := B.le_opNorm₂ _ _
      _ ≤ ‖B‖ * ‖x n‖ * δ := by gcongr
      _ = ‖B‖ * δ * ‖x n‖ := by ring
  calc ‖liftIsometry 𝕜 E F 𝕜 B u‖ ≤ ‖B‖ * δ * S :=
        hsum.norm_le_of_bounded (hx.hasSum.mul_left (‖B‖ * δ)) hbound
    _ = δ * (‖B‖ * S) := by ring
    _ ≤ δ * ((‖B‖ + 1) * (S + 1)) := by gcongr <;> linarith
    _ = 0 + ε := by rw [hδ_def, div_mul_cancel₀ _ (by positivity), zero_add]

/-- If `E` has the approximation property, an element of `E ⊗̂π F` on which every functional
`x ⊗ₜ y ↦ f x * g y` vanishes is zero. -/
theorem eq_zero_of_hasApproximationProperty_left (hE : HasApproximationProperty 𝕜 E)
    {u : CompletedProjectiveTensor 𝕜 E F}
    (hu : ∀ (f : StrongDual 𝕜 E) (g : StrongDual 𝕜 F),
      liftIsometry 𝕜 E F 𝕜 (f.smulRight g) u = 0) :
    u = 0 := by
  have hcomm (f : StrongDual 𝕜 E) (g : StrongDual 𝕜 F) :
      liftIsometry 𝕜 F E 𝕜 (g.smulRight f) (comm 𝕜 E F u) =
        liftIsometry 𝕜 E F 𝕜 (f.smulRight g) u := by
    have h : liftIsometry 𝕜 F E 𝕜 (g.smulRight f) ∘L
        (comm 𝕜 E F).toContinuousLinearEquiv.toContinuousLinearMap =
          liftIsometry 𝕜 E F 𝕜 (f.smulRight g) :=
      continuousLinearMap_ext fun x y ↦ by simp [comm_coe, mul_comm]
    exact congr($h u)
  have h := eq_zero_of_hasApproximationProperty_right hE (u := comm 𝕜 E F u)
    fun g f ↦ (hcomm f g).trans (hu f g)
  rwa [LinearIsometryEquiv.map_eq_zero_iff] at h

/-- If `F` has the approximation property, the contraction `E ⊗̂π F → E ⊗̂ε F` is injective. -/
theorem injective_toCompletedInjectiveTensor_of_hasApproximationProperty_right
    (hF : HasApproximationProperty 𝕜 F) :
    Function.Injective (toCompletedInjectiveTensor 𝕜 E F) :=
  (injective_iff_map_eq_zero _).2 fun _ hu ↦
    eq_zero_of_hasApproximationProperty_right hF
      (liftIsometry_smulRight_eq_zero_of_toCompletedInjectiveTensor_eq_zero hu)

/-- If `E` has the approximation property, the contraction `E ⊗̂π F → E ⊗̂ε F` is injective. -/
theorem injective_toCompletedInjectiveTensor_of_hasApproximationProperty_left
    (hE : HasApproximationProperty 𝕜 E) :
    Function.Injective (toCompletedInjectiveTensor 𝕜 E F) :=
  (injective_iff_map_eq_zero _).2 fun _ hu ↦
    eq_zero_of_hasApproximationProperty_left hE
      (liftIsometry_smulRight_eq_zero_of_toCompletedInjectiveTensor_eq_zero hu)

section Operator

variable [CompleteSpace F]

/-- If the Banach space `F` has the approximation property, the canonical operator
`E* ⊗̂π F → (E →L[𝕜] F)` is injective: every nuclear operator `E → F` has a unique representing
tensor. -/
theorem injective_toContinuousLinearMap_of_hasApproximationProperty
    (hF : HasApproximationProperty 𝕜 F) :
    Function.Injective (toContinuousLinearMap 𝕜 E F) :=
  injective_toContinuousLinearMap_iff.2
    (injective_toCompletedInjectiveTensor_of_hasApproximationProperty_right hF)

/-- If the dual `E*` has the approximation property, the canonical operator
`E* ⊗̂π F → (E →L[𝕜] F)` is injective: every nuclear operator `E → F` has a unique representing
tensor. -/
theorem injective_toContinuousLinearMap_of_hasApproximationProperty_strongDual
    (hE : HasApproximationProperty 𝕜 (StrongDual 𝕜 E)) :
    Function.Injective (toContinuousLinearMap 𝕜 E F) :=
  injective_toContinuousLinearMap_iff.2
    (injective_toCompletedInjectiveTensor_of_hasApproximationProperty_left hE)

end Operator

end TauCeti.CompletedProjectiveTensor
