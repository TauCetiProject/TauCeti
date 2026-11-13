/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.CauchyProblem
import TauCeti.Analysis.Normed.Operator.Banach

/-!
# Parabolic Cauchy problems on the real line

On the line, the coefficient fields of the parabolic operator
`P u = ∂ₜu - A·D_x²u - B·D_xu - C·u` on `ℝ × [a, b]` are determined by scalar fields. A Hessian
`H : ℝ →L[ℝ] ℝ →L[ℝ] ℝ` is `H 1 1` times the product `(h, k) ↦ h k`, a gradient `D` is `D 1`
times the identity, and a value `y` is `y` times `1`. Hence `P` is the one-dimensional operator
`∂ₜ - a ∂ₓ² - b ∂ₓ - c` with the scalar coefficients `a = A(·)(h, k ↦ h k)`, `b = B(·)(id)` and
`c = C(·)(1)`. The coordinate `ℝ¹ = EuclideanSpace ℝ (Fin 1) ≃ ℝ` identifies it with the
Euclidean operator with these coefficients, which transfers the well-posedness of the Cauchy
problem with variable Hölder coefficients from `ℝ¹` to the line:

* if `lam ≤ a` with `0 < lam`, the initial-data map `u ↦ (P u, u(·, 0))` on `ℝ × [0, T]` is an
  isomorphism of Banach spaces from `C_b^{2+α,1+α/2}` onto `C_b^{α,α/2} × C_b^{2,α}`
  (`ParabolicC2HolderSpace.isInvertible_parabolicOperatorL_prod_spatialTraceL_real`);
* by time reversal, so is the terminal-data map `u ↦ (P_back u, u(·, t₁))` of the backward
  operator `P_back u = ∂ₜu + A·D_x²u + B·D_xu + C·u` on every slab `ℝ × [t₀, t₁]`
  (`ParabolicC2HolderSpace.isInvertible_backwardParabolicOperatorL_prod_spatialTraceL_real`).

As for the Euclidean theorems, `0 < α < 1`, and no sign condition on the lower-order coefficients
is needed. One-dimensional problems, such as the weighted pricing equation in log-spot
coordinates, are naturally stated with these coefficient fields on `ℝ` rather than on `ℝ¹`.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
-/

public section
noncomputable section

namespace TauCeti.ParabolicC2HolderSpace

open Set Function ParabolicSpaceTime
open scoped NNReal

variable {α : ℝ≥0}

/-- A local shortcut for the norm on Hessians on the line. Without it, instance search for the
operator norm on `(ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ`, the coefficient space of the second-order term,
fails, for the reason explained in `TauCeti.Analysis.PDE.Parabolic.Holder.Operator`. -/
local instance : NormedAddCommGroup (ℝ →L[ℝ] ℝ →L[ℝ] ℝ) := inferInstance
/-- A local shortcut for scalar operations on Hessians on the line, needed for the same reason. -/
local instance : NormedSpace ℝ (ℝ →L[ℝ] ℝ →L[ℝ] ℝ) := inferInstance

/-! ### Scalar coefficients on `ℝ¹` -/

section Transport

variable {a b : ℝ} {hab : a < b}

/-- The coordinate `x ↦ x 0` of `ℝ¹ = EuclideanSpace ℝ (Fin 1)`. -/
private def coord : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
  PiLp.equivOfUnique 2 ℝ fun _ : Fin 1 ↦ ℝ

private theorem coord_single (i : Fin 1) : coord (EuclideanSpace.single i 1) = 1 := by
  simp [coord, Subsingleton.elim i default]

private theorem lipschitzWith_slabSpaceMap_coord :
    LipschitzWith (max ‖(coord : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ)‖₊ 1)
      (slabSpaceMap (a := a) (b := b) (coord : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ)) :=
  lipschitzWith_slabSpaceMap (coord : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).lipschitzWith

/-- The scalar field `p ↦ A (x₀ p, t) w` on the slab over `ℝ¹`, for a coefficient field `A` on the
slab over the line and a fixed argument `w`. -/
private def evalCoord {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : HolderSpace α (slab (E := ℝ) a b) (G →L[ℝ] ℝ)) (w : G) :
    HolderSpace α (slab (E := EuclideanSpace ℝ (Fin 1)) a b) ℝ :=
  (ContinuousLinearMap.id ℝ (G →L[ℝ] ℝ)).compHolder₂
    (HolderSpace.compLipschitzL _ lipschitzWith_slabSpaceMap_coord A) (HolderSpace.const w)

private theorem evalCoord_apply {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : HolderSpace α (slab (E := ℝ) a b) (G →L[ℝ] ℝ)) (w : G)
    (p : slab (E := EuclideanSpace ℝ (Fin 1)) a b) :
    evalCoord A w p = A (slabSpaceMap coord p) w := by
  simp [evalCoord]

/-- **The operator on the line is the Euclidean operator on `ℝ¹`.** With the scalar coefficients
`a = A(·)(h, k ↦ h k)`, `b = B(·)(id)` and `c = C(·)(1)` read through the coordinate `x₀` of `ℝ¹`,
`P_{a,b,c} (u ∘ (x₀ × id)) = (P_{A,B,C} u) ∘ (x₀ × id)`. -/
private theorem euclideanParabolicOperatorL_compSpatialL_coord (hα : α ≤ 1)
    (A : HolderSpace α (slab (E := ℝ) a b) ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
    (B : HolderSpace α (slab (E := ℝ) a b) ((ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
    (C : HolderSpace α (slab (E := ℝ) a b) (ℝ →L[ℝ] ℝ)) (u : ParabolicC2HolderSpace α ℝ ℝ hab) :
    euclideanParabolicOperatorL hα (fun _ _ ↦ evalCoord A (ContinuousLinearMap.mul ℝ ℝ))
        (fun _ ↦ evalCoord B (ContinuousLinearMap.id ℝ ℝ)) (evalCoord C 1)
        (compSpatialL α ℝ hab (coord : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ) u) =
      HolderSpace.compLipschitzL _ lipschitzWith_slabSpaceMap_coord
        (parabolicOperatorL hα A B C u) := by
  ext p
  -- On the line, a Hessian `H` is `H 1 1 • (h, k ↦ h k)`, a gradient `D` is `D 1 • id` and a
  -- value `y` is `y • 1`, so each coefficient field acts through its value at that argument.
  have hA (q) : A q (spatialSecondFDerivL u q) =
      spatialSecondFDerivL u q 1 1 * A q (ContinuousLinearMap.mul ℝ ℝ) := by
    rw [← smul_eq_mul, ← map_smul]
    congr 1
    ext
    simp
  have hB (q) : B q (spatialFDerivL u q) =
      spatialFDerivL u q 1 * B q (ContinuousLinearMap.id ℝ ℝ) := by
    rw [← smul_eq_mul, ← map_smul]
    congr 1
    ext
    simp
  have hC (q) : C q (u q) = u q * C q 1 := by
    rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  simp only [euclideanParabolicOperatorL_apply, parabolicOperatorL_apply,
    HolderSpace.compLipschitzL_apply, evalCoord_apply, timeDerivL_compSpatialL,
    spatialSecondFDerivL_compSpatialL, spatialFDerivL_compSpatialL, compSpatialL_apply,
    ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, coord_single, Finset.univ_unique, Finset.sum_singleton, hA, hB,
    hC]
  ring

end Transport

/-! ### The Cauchy problem on the line -/

/-- **The Cauchy problem on the line is well posed.** For `0 < α < 1`, a horizon `T > 0` and
coefficient fields `A`, `B`, `C` in `C_b^{α,α/2}(ℝ × [0, T])` whose second-order part is uniformly
parabolic, `lam ≤ A p (h, k ↦ h k)` with `0 < lam`, the initial-data map
`u ↦ (∂ₜu - A·D_x²u - B·D_xu - C·u, u(·, 0))` is an isomorphism of Banach spaces from
`C_b^{2+α,1+α/2}` onto `C_b^{α,α/2} × C_b^{2,α}`. -/
theorem isInvertible_parabolicOperatorL_prod_spatialTraceL_real (hα₀ : 0 < α) (hα₁ : α < 1)
    {T : ℝ≥0} (hT : (0 : ℝ) < T)
    {A : HolderSpace α (slab (E := ℝ) 0 T) ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ)}
    (B : HolderSpace α (slab (E := ℝ) 0 T) ((ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
    (C : HolderSpace α (slab (E := ℝ) 0 T) (ℝ →L[ℝ] ℝ)) {lam : ℝ} (hlam : 0 < lam)
    (hA : ∀ p, lam ≤ A p (ContinuousLinearMap.mul ℝ ℝ)) :
    ((parabolicOperatorL hα₁.le A B C).prod
      (spatialTraceL (F := ℝ) (hab := hT) ⟨0, left_mem_Icc.2 hT.le⟩)).IsInvertible := by
  rw [ContinuousLinearMap.isInvertible_iff_bijective]
  -- The Euclidean problem with the scalar coefficients is well posed.
  have hE := bijective_euclideanParabolicOperatorL_prod_spatialTraceL hα₀ hα₁ hT
    (a := fun _ _ ↦ evalCoord A (ContinuousLinearMap.mul ℝ ℝ))
    (fun _ ↦ evalCoord B (ContinuousLinearMap.id ℝ ℝ)) (evalCoord C 1) hlam fun p ξ ↦ by
      have h := hA (slabSpaceMap coord p)
      rw [← evalCoord_apply] at h
      simp only [Matrix.toQuadraticForm'_apply, dotProduct, Matrix.mulVec, Matrix.of_apply,
        Finset.univ_unique, Finset.sum_singleton, EuclideanSpace.real_norm_sq_eq]
      nlinarith [sq_nonneg (ξ default)]
  -- The data are transported by `Ψ (f, g) = (f ∘ (x₀ × id), g ∘ x₀)`, a bijection.
  set Ψ : HolderSpace α (slab (E := ℝ) 0 T) ℝ × CkHolderSpace 2 α ℝ ℝ →
      HolderSpace α (slab (E := EuclideanSpace ℝ (Fin 1)) 0 T) ℝ ×
        CkHolderSpace 2 α (EuclideanSpace ℝ (Fin 1)) ℝ :=
    Prod.map (HolderSpace.compLipschitzL _ lipschitzWith_slabSpaceMap_coord)
      (CkHolderSpace.compLinearCLE coord) with hΨ
  have hΨb : Bijective Ψ := by
    -- The first component is inverted by the change of variables along `x₀⁻¹`.
    refine Bijective.prodMap (bijective_iff_has_inverse.2
      ⟨HolderSpace.compLipschitzL _
        (lipschitzWith_slabSpaceMap (coord.symm : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)).lipschitzWith),
        fun f ↦ ?_, fun f ↦ ?_⟩) (CkHolderSpace.compLinearCLE coord).bijective <;>
      ext p <;> simp
  have hcomp : ⇑((euclideanParabolicOperatorL hα₁.le
        (fun _ _ ↦ evalCoord A (ContinuousLinearMap.mul ℝ ℝ))
        (fun _ ↦ evalCoord B (ContinuousLinearMap.id ℝ ℝ)) (evalCoord C 1)).prod
        (spatialTraceL (F := ℝ) (hab := hT) ⟨0, left_mem_Icc.2 hT.le⟩)) ∘
        compSpatialCLE α ℝ hT coord =
      Ψ ∘ (parabolicOperatorL hα₁.le A B C).prod
        (spatialTraceL (F := ℝ) (hab := hT) ⟨0, left_mem_Icc.2 hT.le⟩) := by
    funext u
    simp only [comp_apply, ContinuousLinearMap.prod_apply, spatialTraceL_apply, hΨ,
      Prod.map_apply, compSpatialCLE_apply, euclideanParabolicOperatorL_compSpatialL_coord,
      spatialTrace_compSpatialL, CkHolderSpace.compLinearCLE_apply]
  rw [← Bijective.of_comp_iff' hΨb, ← hcomp]
  exact hE.comp (compSpatialCLE α ℝ hT coord).bijective

/-- **The terminal-value problem on the line is well posed.** For `0 < α < 1`, a slab
`ℝ × [t₀, t₁]` and coefficient fields `A`, `B`, `C` in `C_b^{α,α/2}` with
`lam ≤ A p (h, k ↦ h k)` and `0 < lam`, the terminal-data map
`u ↦ (∂ₜu + A·D_x²u + B·D_xu + C·u, u(·, t₁))` is an isomorphism of Banach spaces from
`C_b^{2+α,1+α/2}` onto `C_b^{α,α/2} × C_b^{2,α}`. -/
theorem isInvertible_backwardParabolicOperatorL_prod_spatialTraceL_real (hα₀ : 0 < α)
    (hα₁ : α < 1) {t₀ t₁ : ℝ} (ht : t₀ < t₁)
    {A : HolderSpace α (slab (E := ℝ) t₀ t₁) ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ)}
    (B : HolderSpace α (slab (E := ℝ) t₀ t₁) ((ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
    (C : HolderSpace α (slab (E := ℝ) t₀ t₁) (ℝ →L[ℝ] ℝ)) {lam : ℝ} (hlam : 0 < lam)
    (hA : ∀ p, lam ≤ A p (ContinuousLinearMap.mul ℝ ℝ)) :
    ((backwardParabolicOperatorL (ht := ht) hα₁.le A B C).prod
      (spatialTraceL (F := ℝ) ⟨t₁, right_mem_Icc.2 ht.le⟩)).IsInvertible := by
  -- Reversing time about `t₁` turns the problem into a forward one on `ℝ × [0, t₁ - t₀]`.
  obtain ⟨T, h₁⟩ : ∃ T : ℝ≥0, (T : ℝ) = t₁ - t₀ :=
    ⟨(t₁ - t₀).toNNReal, Real.coe_toNNReal _ (sub_nonneg.2 ht.le)⟩
  have h₀ : (0 : ℝ) = t₁ - t₁ := (sub_self _).symm
  rw [ContinuousLinearMap.isInvertible_iff_bijective,
    bijective_backwardParabolicOperatorL_prod_spatialTraceL_iff (hab := ht) (T := t₁) (ha := h₀)
      (hb := h₁)]
  have hT : (0 : ℝ) < T := h₁ ▸ sub_pos.2 ht
  exact (isInvertible_parabolicOperatorL_prod_spatialTraceL_real hα₀ hα₁ hT _ _ hlam
    fun p ↦ by simpa only [HolderSpace.compLipschitzL_apply] using hA _).bijective

end TauCeti.ParabolicC2HolderSpace
