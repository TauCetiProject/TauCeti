/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Solvability
import TauCeti.Analysis.Matrix.QuadraticBounds
import TauCeti.Analysis.Normed.Operator.Banach
import TauCeti.Analysis.Normed.Operator.Prod
import TauCeti.Analysis.PDE.Parabolic.Holder.CompSpatial

/-!
# Parabolic Cauchy problems on the real line

On the line, the coefficient fields of the parabolic operator
`P u = ∂ₜu - A·D_x²u - B·D_xu - C·u` on `ℝ × [a, b]` are determined by scalar fields. A Hessian
`H : ℝ →L[ℝ] ℝ →L[ℝ] ℝ` is `H 1 1` times the product `(h, k) ↦ h k`, a gradient `D` is `D 1`
times the identity, and a value `y` is `y` times `1`. Hence `P` is the one-dimensional operator
`∂ₜ - a ∂ₓ² - b ∂ₓ - c` with the scalar coefficients `a = A(·)(h, k ↦ h k)`, `b = B(·)(id)` and
`c = C(·)(1)`. The isometric coordinate `ℝ¹ = EuclideanSpace ℝ (Fin 1) ≃ₗᵢ[ℝ] ℝ` identifies it
with the Euclidean operator with these coefficients, which transfers the well-posedness and
uniform estimates of the Cauchy and terminal-value problems from `ℝ¹` to the line:

* if `lam ≤ a` with `0 < lam`, the initial-data map `u ↦ (P u, u(·, 0))` on `ℝ × [0, T]` is an
  isomorphism of Banach spaces from `C_b^{2+α,1+α/2}` onto `C_b^{α,α/2} × C_b^{2,α}`
  (`ParabolicC2HolderSpace.isInvertible_parabolicOperatorL_prod_spatialTraceL_real`);
* by time reversal, so is the terminal-data map `u ↦ (P_back u, u(·, t₁))` of the backward
  operator `P_back u = ∂ₜu + A·D_x²u + B·D_xu + C·u` on every slab `ℝ × [t₀, t₁]`
  (`ParabolicC2HolderSpace.isInvertible_backwardParabolicOperatorL_prod_spatialTraceL_real`),
  packaged as the Banach isomorphism `ParabolicC2HolderSpace.realTerminalDataCLE` with uniform
  Schauder estimate `ParabolicC2HolderSpace.exists_norm_realTerminalDataCLE_symm_le` and Lipschitz
  dependence on `(A, B, C)` `ParabolicC2HolderSpace.exists_norm_realTerminalDataCLE_symm_sub_le`.

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

/-- The isometric coordinate `x ↦ x 0` of `ℝ¹ = EuclideanSpace ℝ (Fin 1)`. -/
private def coord : EuclideanSpace ℝ (Fin 1) ≃ₗᵢ[ℝ] ℝ :=
  { (PiLp.equivOfUnique 2 ℝ fun _ : Fin 1 ↦ ℝ).toLinearEquiv with
    norm_map' x := by
      simp [EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs] }

private theorem coord_single (i : Fin 1) : coord (EuclideanSpace.single i 1) = 1 := by
  simp [coord, Subsingleton.elim i default]

/-- The scalar field `p ↦ A (x₀ p, t) w` on the slab over `ℝ¹`, for a coefficient field `A` on the
slab over the line and a fixed argument `w`. -/
private def evalCoord {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : HolderSpace α (slab (E := ℝ) a b) (G →L[ℝ] ℝ)) (w : G) :
    HolderSpace α (slab (E := EuclideanSpace ℝ (Fin 1)) a b) ℝ :=
  HolderSpace.compLeftL (ContinuousLinearMap.apply ℝ ℝ w)
    (HolderSpace.compIsometryEquivLIE α _
      (slabSpaceIsometryEquiv (a := a) (b := b) coord.toIsometryEquiv) A)

private theorem evalCoord_apply {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : HolderSpace α (slab (E := ℝ) a b) (G →L[ℝ] ℝ)) (w : G)
    (p : slab (E := EuclideanSpace ℝ (Fin 1)) a b) :
    evalCoord A w p = A (slabSpaceMap coord p) w := by
  simp [evalCoord]

private theorem evalCoord_sub {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A A' : HolderSpace α (slab (E := ℝ) a b) (G →L[ℝ] ℝ)) (w : G) :
    evalCoord (A - A') w = evalCoord A w - evalCoord A' w := by
  simp [evalCoord, map_sub]

private theorem norm_evalCoord_le {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : HolderSpace α (slab (E := ℝ) a b) (G →L[ℝ] ℝ)) {w : G} (hw : ‖w‖ ≤ 1) :
    ‖evalCoord A w‖ ≤ ‖A‖ := by
  have h : ‖ContinuousLinearMap.apply ℝ ℝ w‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f ↦
      (f.le_opNorm w).trans (by nlinarith [norm_nonneg f])
  have hL := (HolderSpace.compLeftL (α := α)
    (X := slab (E := EuclideanSpace ℝ (Fin 1)) a b)
    (ContinuousLinearMap.apply ℝ ℝ w)).le_of_opNorm_le
    ((HolderSpace.norm_compLeftL_le _).trans h)
    (HolderSpace.compIsometryEquivLIE α _
      (slabSpaceIsometryEquiv (a := a) (b := b) coord.toIsometryEquiv) A)
  simpa [evalCoord] using hL

private theorem norm_mulCLM_le_one : ‖ContinuousLinearMap.mul ℝ ℝ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y ↦ by
      simp [mul_comm]

private theorem evalCoord_ellipticity
    {A : HolderSpace α (slab (E := ℝ) a b) ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ)}
    {lam : ℝ} (hA : ∀ p, lam ≤ A p (ContinuousLinearMap.mul ℝ ℝ))
    (p : slab (E := EuclideanSpace ℝ (Fin 1)) a b) (ξ : EuclideanSpace ℝ (Fin 1)) :
    lam * ‖ξ‖ ^ 2 ≤
      (Matrix.of fun _ _ : Fin 1 ↦
        evalCoord A (ContinuousLinearMap.mul ℝ ℝ) p).toQuadraticForm' ξ := by
  simpa only [Matrix.of_apply, evalCoord_apply] using
    Matrix.mul_norm_sq_le_toQuadraticForm'_of_unique (hA (slabSpaceMap coord p)) ξ

/-- **The spatial part on the line is the Euclidean spatial operator on `ℝ¹`.** -/
private theorem spatialOperatorL_compSpatialLIE_coord (hα : α ≤ 1)
    (A : HolderSpace α (slab (E := ℝ) a b) ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
    (B : HolderSpace α (slab (E := ℝ) a b) ((ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
    (C : HolderSpace α (slab (E := ℝ) a b) (ℝ →L[ℝ] ℝ)) (u : ParabolicC2HolderSpace α ℝ ℝ hab) :
    spatialOperatorL hα
        (euclideanSecondOrderCoeff (fun _ _ ↦ evalCoord A (ContinuousLinearMap.mul ℝ ℝ)))
        (euclideanFirstOrderCoeff (fun _ ↦ evalCoord B (ContinuousLinearMap.id ℝ ℝ)))
        (euclideanZerothOrderCoeff (evalCoord C 1)) (compSpatialLIE α ℝ hab coord u) =
      HolderSpace.compIsometryEquivLIE α ℝ
        (slabSpaceIsometryEquiv (a := a) (b := b) coord.toIsometryEquiv)
        (spatialOperatorL hα A B C u) := by
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
  simp only [spatialOperatorL_apply, euclideanSecondOrderCoeff_apply,
    euclideanFirstOrderCoeff_apply, euclideanZerothOrderCoeff_apply, evalCoord_apply,
    compSpatialLIE_apply, spatialSecondFDerivL_compSpatialL, spatialFDerivL_compSpatialL,
    compSpatialL_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.comp_apply, coord_single, Finset.univ_unique, Finset.sum_singleton,
    HolderSpace.compIsometryEquivLIE_apply, slabSpaceIsometryEquiv_apply,
    LinearIsometryEquiv.coe_toIsometryEquiv, hA, hB, hC]
  ring

/-- **The forward operator on the line is the Euclidean operator on `ℝ¹`.** -/
private theorem euclideanParabolicOperatorL_compSpatialLIE_coord (hα : α ≤ 1)
    (A : HolderSpace α (slab (E := ℝ) a b) ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
    (B : HolderSpace α (slab (E := ℝ) a b) ((ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
    (C : HolderSpace α (slab (E := ℝ) a b) (ℝ →L[ℝ] ℝ)) (u : ParabolicC2HolderSpace α ℝ ℝ hab) :
    euclideanParabolicOperatorL hα (fun _ _ ↦ evalCoord A (ContinuousLinearMap.mul ℝ ℝ))
        (fun _ ↦ evalCoord B (ContinuousLinearMap.id ℝ ℝ)) (evalCoord C 1)
        (compSpatialLIE α ℝ hab coord u) =
      HolderSpace.compIsometryEquivLIE α ℝ
        (slabSpaceIsometryEquiv (a := a) (b := b) coord.toIsometryEquiv)
        (parabolicOperatorL hα A B C u) := by
  ext p
  have hs := congrArg (fun f ↦ f p) (spatialOperatorL_compSpatialLIE_coord hα A B C u)
  simp only [euclideanParabolicOperatorL_def, parabolicOperatorL_def,
    _root_.sub_apply, HolderSpace.sub_apply,
    HolderSpace.compIsometryEquivLIE_apply, slabSpaceIsometryEquiv_apply,
    LinearIsometryEquiv.coe_toIsometryEquiv] at hs ⊢
  rw [hs]
  simp [compSpatialLIE_apply]

/-- **The backward operator on the line is the Euclidean backward operator on `ℝ¹`.** -/
private theorem euclideanBackwardParabolicOperatorL_compSpatialLIE_coord (hα : α ≤ 1)
    (A : HolderSpace α (slab (E := ℝ) a b) ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
    (B : HolderSpace α (slab (E := ℝ) a b) ((ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
    (C : HolderSpace α (slab (E := ℝ) a b) (ℝ →L[ℝ] ℝ)) (u : ParabolicC2HolderSpace α ℝ ℝ hab) :
    euclideanBackwardParabolicOperatorL hα (fun _ _ ↦ evalCoord A (ContinuousLinearMap.mul ℝ ℝ))
        (fun _ ↦ evalCoord B (ContinuousLinearMap.id ℝ ℝ)) (evalCoord C 1)
        (compSpatialLIE α ℝ hab coord u) =
      HolderSpace.compIsometryEquivLIE α ℝ
        (slabSpaceIsometryEquiv (a := a) (b := b) coord.toIsometryEquiv)
        (backwardParabolicOperatorL hα A B C u) := by
  ext p
  have hs := congrArg (fun f ↦ f p) (spatialOperatorL_compSpatialLIE_coord hα A B C u)
  simp only [euclideanBackwardParabolicOperatorL_def, backwardParabolicOperatorL_def,
    _root_.add_apply, HolderSpace.add_apply,
    HolderSpace.compIsometryEquivLIE_apply, slabSpaceIsometryEquiv_apply,
    LinearIsometryEquiv.coe_toIsometryEquiv] at hs ⊢
  rw [hs]
  simp [compSpatialLIE_apply]

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
    (fun _ ↦ evalCoord B (ContinuousLinearMap.id ℝ ℝ)) (evalCoord C 1) hlam
    (evalCoord_ellipticity hA)
  -- The data are transported isometrically by `Ψ (f, g) = (f ∘ (x₀ × id), g ∘ x₀)`.
  let Ψ := (HolderSpace.compIsometryEquivLIE α ℝ
    (slabSpaceIsometryEquiv (a := 0) (b := T) coord.toIsometryEquiv)).prodCongr
    (CkHolderSpace.compLinearLIE (k := 2) (α := α) (F := ℝ) coord)
  have hcomp : ⇑((euclideanParabolicOperatorL hα₁.le
        (fun _ _ ↦ evalCoord A (ContinuousLinearMap.mul ℝ ℝ))
        (fun _ ↦ evalCoord B (ContinuousLinearMap.id ℝ ℝ)) (evalCoord C 1)).prod
        (spatialTraceL (F := ℝ) (hab := hT) ⟨0, left_mem_Icc.2 hT.le⟩)) ∘
        compSpatialLIE α ℝ hT coord =
      Ψ ∘ (parabolicOperatorL hα₁.le A B C).prod
        (spatialTraceL (F := ℝ) (hab := hT) ⟨0, left_mem_Icc.2 hT.le⟩) := by
    funext u
    simp only [comp_apply, ContinuousLinearMap.prod_apply, spatialTraceL_apply, Ψ,
      LinearIsometryEquiv.prodCongr_apply]
    refine Prod.ext (euclideanParabolicOperatorL_compSpatialLIE_coord hα₁.le A B C u) ?_
    simp [compSpatialLIE_apply, spatialTrace_compSpatialL, CkHolderSpace.compLinearLIE_apply]
  rw [← Bijective.of_comp_iff' Ψ.bijective, ← hcomp]
  exact hE.comp (compSpatialLIE α ℝ hT coord).bijective

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
      (hb := h₁), initialDataL_def]
  have hT : (0 : ℝ) < T := h₁ ▸ sub_pos.2 ht
  exact (isInvertible_parabolicOperatorL_prod_spatialTraceL_real hα₀ hα₁ hT _ _ hlam
    fun p ↦ by simpa only [HolderSpace.compLipschitzL_apply] using hA _).bijective

/-! ### The terminal-data isomorphism and uniform estimates on the line -/

/-- **The terminal-data isomorphism on the line.** For `0 < α < 1`, `t₀ < t₁`, and coefficient
fields `A`, `B`, `C` in `C_b^{α,α/2}(ℝ × [t₀, t₁])` with `A` uniformly elliptic,
`lam ≤ A p (h, k ↦ h k)` (`0 < lam`), the map `u ↦ (∂ₜu + A·D_x²u + B·D_xu + C·u, u(·, t₁))` as
an isomorphism of Banach spaces from `C_b^{2+α,1+α/2}(ℝ × [t₀, t₁])` onto
`C_b^{α,α/2}(ℝ × [t₀, t₁]) × C_b^{2,α}(ℝ)`. -/
def realTerminalDataCLE {t₀ t₁ : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) (ht : t₀ < t₁)
    (A : HolderSpace α (slab (E := ℝ) t₀ t₁) ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
    (B : HolderSpace α (slab (E := ℝ) t₀ t₁) ((ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
    (C : HolderSpace α (slab (E := ℝ) t₀ t₁) (ℝ →L[ℝ] ℝ))
    (hA : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ A p (ContinuousLinearMap.mul ℝ ℝ)) :
    ParabolicC2HolderSpace α ℝ ℝ ht ≃L[ℝ]
      HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ :=
  have hbij := hA.elim fun _ h ↦
    (isInvertible_backwardParabolicOperatorL_prod_spatialTraceL_real
      hα₀ hα₁ ht B C h.1 h.2).bijective
  ContinuousLinearEquiv.ofBijective _ (LinearMap.ker_eq_bot.2 hbij.1)
    (LinearMap.range_eq_top.2 hbij.2)

section RealTerminalDataCLE

variable {t₀ t₁ : ℝ} {hα₀ : 0 < α} {hα₁ : α < 1} {ht : t₀ < t₁}
  {A : HolderSpace α (slab (E := ℝ) t₀ t₁) ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ)}
  {B : HolderSpace α (slab (E := ℝ) t₀ t₁) ((ℝ →L[ℝ] ℝ) →L[ℝ] ℝ)}
  {C : HolderSpace α (slab (E := ℝ) t₀ t₁) (ℝ →L[ℝ] ℝ)}
  {hA : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ A p (ContinuousLinearMap.mul ℝ ℝ)}

/-- The terminal-data isomorphism on the line sends `u` to its backward forcing `P_back u` and
its terminal trace `u(·, t₁)`. -/
@[simp]
theorem realTerminalDataCLE_apply (u : ParabolicC2HolderSpace α ℝ ℝ ht) :
    realTerminalDataCLE hα₀ hα₁ ht A B C hA u =
      (backwardParabolicOperatorL hα₁.le A B C u, u.spatialTrace ⟨t₁, right_mem_Icc.2 ht.le⟩) := by
  simp [realTerminalDataCLE, spatialTraceL_apply]

/-- The solution of the terminal-value problem on the line with forcing `f` and terminal datum `g`
has backward forcing `f`. -/
@[simp]
theorem backwardParabolicOperatorL_realTerminalDataCLE_symm_apply
    (d : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ) :
    backwardParabolicOperatorL hα₁.le A B C
      ((realTerminalDataCLE hα₀ hα₁ ht A B C hA).symm d) = d.1 := by
  have h := (realTerminalDataCLE hα₀ hα₁ ht A B C hA).apply_symm_apply d
  rw [realTerminalDataCLE_apply] at h
  exact congrArg Prod.fst h

/-- The solution of the terminal-value problem on the line with forcing `f` and terminal datum `g`
has terminal trace `g`. -/
@[simp]
theorem spatialTrace_realTerminalDataCLE_symm_apply
    (d : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ) :
    ((realTerminalDataCLE hα₀ hα₁ ht A B C hA).symm d).spatialTrace
      ⟨t₁, right_mem_Icc.2 ht.le⟩ = d.2 := by
  have h := (realTerminalDataCLE hα₀ hα₁ ht A B C hA).apply_symm_apply d
  rw [realTerminalDataCLE_apply] at h
  exact congrArg Prod.snd h

/-- The solution of the terminal-value problem on the line with terminal datum `g` takes the value
`g x` at `(x, t₁)`. -/
@[simp]
theorem realTerminalDataCLE_symm_apply_slabMk_right
    (d : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ) (x : ℝ) :
    (realTerminalDataCLE hα₀ hα₁ ht A B C hA).symm d
      (slabMk x ⟨t₁, right_mem_Icc.2 ht.le⟩) = d.2 x := by
  rw [← spatialTrace_apply, spatialTrace_realTerminalDataCLE_symm_apply]

end RealTerminalDataCLE

/-- Conjugacy between the line solution operator and the `ℝ¹` Euclidean solution operator. -/
private theorem realTerminalDataCLE_symm_eq {t₀ t₁ : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) (ht : t₀ < t₁)
    (A : HolderSpace α (slab (E := ℝ) t₀ t₁) ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
    (B : HolderSpace α (slab (E := ℝ) t₀ t₁) ((ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
    (C : HolderSpace α (slab (E := ℝ) t₀ t₁) (ℝ →L[ℝ] ℝ))
    (hA : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ A p (ContinuousLinearMap.mul ℝ ℝ)) :
    let eData := (HolderSpace.compIsometryEquivLIE α ℝ
      (slabSpaceIsometryEquiv (a := t₀) (b := t₁) coord.toIsometryEquiv)).prodCongr
      (CkHolderSpace.compLinearLIE (k := 2) (α := α) (F := ℝ) coord)
    (realTerminalDataCLE hα₀ hα₁ ht A B C hA).symm.toContinuousLinearMap =
      ((compSpatialLIE α ℝ ht coord).symm : _ →L[ℝ] _) ∘L
        (euclideanTerminalDataCLE hα₀ hα₁ ht
          (fun _ _ ↦ evalCoord A (ContinuousLinearMap.mul ℝ ℝ))
          (fun _ ↦ evalCoord B (ContinuousLinearMap.id ℝ ℝ)) (evalCoord C 1)
          (hA.imp fun _ ⟨hlam, h⟩ ↦ ⟨hlam, evalCoord_ellipticity h⟩)).symm.toContinuousLinearMap ∘L
        (eData : _ →L[ℝ] _) := by
  intro eData
  refine ContinuousLinearMap.ext fun d ↦ ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_coe]
  apply (compSpatialLIE α ℝ ht coord).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply (euclideanTerminalDataCLE hα₀ hα₁ ht
    (fun _ _ ↦ evalCoord A (ContinuousLinearMap.mul ℝ ℝ))
    (fun _ ↦ evalCoord B (ContinuousLinearMap.id ℝ ℝ)) (evalCoord C 1)
    (hA.imp fun _ ⟨hlam, h⟩ ↦ ⟨hlam, evalCoord_ellipticity h⟩)).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, euclideanTerminalDataCLE_apply]
  refine Prod.ext ?_ ?_
  · rw [euclideanBackwardParabolicOperatorL_compSpatialLIE_coord,
      backwardParabolicOperatorL_realTerminalDataCLE_symm_apply]
    simp [eData]
  · rw [compSpatialLIE_apply, spatialTrace_compSpatialL,
      spatialTrace_realTerminalDataCLE_symm_apply]
    ext x
    simp [eData]

/-- **Uniform Schauder estimate for the terminal-value problem on the line.** For `0 < α < 1`,
an ellipticity constant `lam > 0`, a bound `K` on the Hölder norms of the coefficients and a bound
`T₀` on the slab duration, the solution operators of the terminal-value problems on `ℝ × [t₀, t₁]`,
`t₁ - t₀ ≤ T₀`, are bounded uniformly in operator norm. -/
theorem exists_norm_realTerminalDataCLE_symm_le (hα₀ : 0 < α) (hα₁ : α < 1) {lam : ℝ}
    (hlam : 0 < lam) (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {t₀ t₁ : ℝ} (ht : t₀ < t₁), t₁ - t₀ ≤ T₀ →
      ∀ (A : HolderSpace α (slab (E := ℝ) t₀ t₁) ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
        (B : HolderSpace α (slab (E := ℝ) t₀ t₁) ((ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
        (C₀ : HolderSpace α (slab (E := ℝ) t₀ t₁) (ℝ →L[ℝ] ℝ))
        (hA : ∀ p, lam ≤ A p (ContinuousLinearMap.mul ℝ ℝ)),
        ‖A‖ ≤ K → ‖B‖ ≤ K → ‖C₀‖ ≤ K →
        ‖(realTerminalDataCLE hα₀ hα₁ ht A B C₀ ⟨lam, hlam, hA⟩).symm.toContinuousLinearMap‖ ≤
          C := by
  obtain ⟨C, hC, hest⟩ :=
    exists_norm_euclideanTerminalDataCLE_symm_le (ι := Fin 1) hα₀ hα₁ hlam K T₀
  refine ⟨C, hC, fun {t₀ t₁} ht hTT₀ A B C₀ hA hAk hBk hCk ↦ ?_⟩
  rw [realTerminalDataCLE_symm_eq,
    ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]
  exact hest ht hTT₀ _ _ _ (evalCoord_ellipticity hA)
    (fun _ _ ↦ (norm_evalCoord_le A norm_mulCLM_le_one).trans hAk)
    (fun _ ↦ (norm_evalCoord_le B ContinuousLinearMap.norm_id_le).trans hBk)
    ((norm_evalCoord_le C₀ norm_one.le).trans hCk)

/-- **Lipschitz dependence of the line terminal-value solution operator on `(A, B, C)`.** Under
the bounds of `exists_norm_realTerminalDataCLE_symm_le`, the solution operators for `(A, B, C)` and
`(A', B', C')` differ in operator norm by at most `C (‖A - A'‖ + ‖B - B'‖ + ‖C - C'‖)`. -/
theorem exists_norm_realTerminalDataCLE_symm_sub_le (hα₀ : 0 < α) (hα₁ : α < 1) {lam : ℝ}
    (hlam : 0 < lam) (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {t₀ t₁ : ℝ} (ht : t₀ < t₁), t₁ - t₀ ≤ T₀ →
      ∀ (A A' : HolderSpace α (slab (E := ℝ) t₀ t₁) ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
        (B B' : HolderSpace α (slab (E := ℝ) t₀ t₁) ((ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
        (C₀ C₀' : HolderSpace α (slab (E := ℝ) t₀ t₁) (ℝ →L[ℝ] ℝ))
        (hA : ∀ p, lam ≤ A p (ContinuousLinearMap.mul ℝ ℝ))
        (hA' : ∀ p, lam ≤ A' p (ContinuousLinearMap.mul ℝ ℝ)),
        ‖A‖ ≤ K → ‖B‖ ≤ K → ‖C₀‖ ≤ K → ‖A'‖ ≤ K → ‖B'‖ ≤ K → ‖C₀'‖ ≤ K →
        ‖(realTerminalDataCLE hα₀ hα₁ ht A B C₀ ⟨lam, hlam, hA⟩).symm.toContinuousLinearMap -
          (realTerminalDataCLE hα₀ hα₁ ht A' B' C₀'
            ⟨lam, hlam, hA'⟩).symm.toContinuousLinearMap‖ ≤
          C * (‖A - A'‖ + ‖B - B'‖ + ‖C₀ - C₀'‖) := by
  obtain ⟨C, hC, hest⟩ :=
    exists_norm_euclideanTerminalDataCLE_symm_sub_le (ι := Fin 1) hα₀ hα₁ hlam K T₀
  refine ⟨C, hC, fun {t₀ t₁} ht hTT₀ A A' B B' C₀ C₀' hA hA' hAk hBk hCk hAk' hBk' hCk' ↦ ?_⟩
  rw [realTerminalDataCLE_symm_eq, realTerminalDataCLE_symm_eq,
    ← ContinuousLinearMap.comp_sub, ← ContinuousLinearMap.sub_comp,
    ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]
  have hmid := hest ht hTT₀ _ _ _ _ _ _
    (evalCoord_ellipticity hA) (evalCoord_ellipticity hA')
    (fun _ _ ↦ (norm_evalCoord_le A norm_mulCLM_le_one).trans hAk)
    (fun _ ↦ (norm_evalCoord_le B ContinuousLinearMap.norm_id_le).trans hBk)
    ((norm_evalCoord_le C₀ norm_one.le).trans hCk)
    (fun _ _ ↦ (norm_evalCoord_le A' norm_mulCLM_le_one).trans hAk')
    (fun _ ↦ (norm_evalCoord_le B' ContinuousLinearMap.norm_id_le).trans hBk')
    ((norm_evalCoord_le C₀' norm_one.le).trans hCk')
  simp only [Finset.univ_unique, Finset.sum_singleton, ← evalCoord_sub] at hmid
  have hδ : ‖evalCoord (A - A') (ContinuousLinearMap.mul ℝ ℝ)‖ +
        ‖evalCoord (B - B') (ContinuousLinearMap.id ℝ ℝ)‖ + ‖evalCoord (C₀ - C₀') 1‖ ≤
      ‖A - A'‖ + ‖B - B'‖ + ‖C₀ - C₀'‖ :=
    add_le_add (add_le_add (norm_evalCoord_le (A - A') norm_mulCLM_le_one)
      (norm_evalCoord_le (B - B') ContinuousLinearMap.norm_id_le))
      (norm_evalCoord_le (C₀ - C₀') norm_one.le)
  calc _ ≤ C * (‖evalCoord (A - A') (ContinuousLinearMap.mul ℝ ℝ)‖ +
          ‖evalCoord (B - B') (ContinuousLinearMap.id ℝ ℝ)‖ + ‖evalCoord (C₀ - C₀') 1‖) := by
        convert hmid using 1
    _ ≤ C * (‖A - A'‖ + ‖B - B'‖ + ‖C₀ - C₀'‖) := mul_le_mul_of_nonneg_left hδ hC

end TauCeti.ParabolicC2HolderSpace
