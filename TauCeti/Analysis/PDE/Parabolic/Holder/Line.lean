/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Solvability
import TauCeti.Analysis.Matrix.QuadraticBounds
import TauCeti.Analysis.Normed.Lp.PiLp
import TauCeti.Analysis.Normed.Operator.Banach
import TauCeti.Analysis.Normed.Operator.LinearIsometryEquiv.Prod
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
private abbrev coord : EuclideanSpace ℝ (Fin 1) ≃ₗᵢ[ℝ] ℝ :=
  PiLp.equivOfUniqueLIE 2 ℝ fun _ : Fin 1 ↦ ℝ

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

private theorem evalCoord_ellipticity
    {A : HolderSpace α (slab (E := ℝ) a b) ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ)}
    {lam : ℝ} (hA : ∀ p, lam ≤ A p (ContinuousLinearMap.mul ℝ ℝ))
    (p : slab (E := EuclideanSpace ℝ (Fin 1)) a b) (ξ : EuclideanSpace ℝ (Fin 1)) :
    lam * ‖ξ‖ ^ 2 ≤
      (Matrix.of fun _ _ : Fin 1 ↦
        evalCoord A (ContinuousLinearMap.mul ℝ ℝ) p).toQuadraticForm' ξ := by
  simpa only [Matrix.of_apply, evalCoord_apply] using
    (Matrix.of fun _ _ : Fin 1 ↦
      evalCoord A (ContinuousLinearMap.mul ℝ ℝ) p).mul_norm_sq_le_toQuadraticForm'_of_unique
      (by simpa only [Matrix.of_apply, evalCoord_apply] using hA (slabSpaceMap coord p)) ξ

private theorem spatialFDerivL_compSpatialLIE_coord_single
    (u : ParabolicC2HolderSpace α ℝ ℝ hab) (p : slab (E := EuclideanSpace ℝ (Fin 1)) a b)
    (i : Fin 1) :
    spatialFDerivL (compSpatialLIE α ℝ hab coord u) p (EuclideanSpace.single i 1) =
      spatialFDerivL u (slabSpaceMap coord p) 1 := by
  simp [compSpatialLIE_apply, spatialFDerivL_compSpatialL]

private theorem spatialSecondFDerivL_compSpatialLIE_coord_single
    (u : ParabolicC2HolderSpace α ℝ ℝ hab) (p : slab (E := EuclideanSpace ℝ (Fin 1)) a b)
    (i j : Fin 1) :
    spatialSecondFDerivL (compSpatialLIE α ℝ hab coord u) p
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      spatialSecondFDerivL u (slabSpaceMap coord p) 1 1 := by
  simp [compSpatialLIE_apply, spatialSecondFDerivL_compSpatialL]

private theorem timeDerivL_compSpatialLIE_coord (u : ParabolicC2HolderSpace α ℝ ℝ hab) :
    timeDerivL (compSpatialLIE α ℝ hab coord u) =
      HolderSpace.compIsometryEquivLIE α ℝ
        (slabSpaceIsometryEquiv (a := a) (b := b) coord.toIsometryEquiv) (timeDerivL u) := by
  ext p
  simp [compSpatialLIE_apply, timeDerivL_compSpatialL]

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
  rw [spatialOperatorL_apply, HolderSpace.compIsometryEquivLIE_apply, spatialOperatorL_apply,
    slabSpaceIsometryEquiv_apply]
  simp only [euclideanSecondOrderCoeff_apply, euclideanFirstOrderCoeff_apply,
    euclideanZerothOrderCoeff_apply, evalCoord_apply, Finset.univ_unique, Finset.sum_singleton,
    spatialSecondFDerivL_compSpatialLIE_coord_single,
    spatialFDerivL_compSpatialLIE_coord_single]
  simp only [compSpatialLIE_apply, compSpatialL_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.coe_toIsometryEquiv, hA, hB, hC]
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
  simp only [euclideanParabolicOperatorL_def, parabolicOperatorL_def, _root_.sub_apply, map_sub,
    timeDerivL_compSpatialLIE_coord, spatialOperatorL_compSpatialLIE_coord]

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
  simp only [euclideanBackwardParabolicOperatorL_def, backwardParabolicOperatorL_def,
    _root_.add_apply, map_add, timeDerivL_compSpatialLIE_coord,
    spatialOperatorL_compSpatialLIE_coord]

/-- The isometric equivalence transporting forcing and spatial trace data between `ℝ × [a, b]` and
`ℝ¹ × [a, b]`. -/
private def dataEquiv (a b : ℝ) :
    HolderSpace α (slab (E := ℝ) a b) ℝ × CkHolderSpace 2 α ℝ ℝ ≃ₗᵢ[ℝ]
      HolderSpace α (slab (E := EuclideanSpace ℝ (Fin 1)) a b) ℝ ×
        CkHolderSpace 2 α (EuclideanSpace ℝ (Fin 1)) ℝ :=
  (HolderSpace.compIsometryEquivLIE α ℝ
    (slabSpaceIsometryEquiv (a := a) (b := b) coord.toIsometryEquiv)).prodCongr
    (CkHolderSpace.compLinearLIE (k := 2) (α := α) (F := ℝ) coord)

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
  -- The data are transported isometrically by `dataEquiv (α := α) 0 T`.
  have hcomp : ⇑((euclideanParabolicOperatorL hα₁.le
        (fun _ _ ↦ evalCoord A (ContinuousLinearMap.mul ℝ ℝ))
        (fun _ ↦ evalCoord B (ContinuousLinearMap.id ℝ ℝ)) (evalCoord C 1)).prod
        (spatialTraceL (F := ℝ) (hab := hT) ⟨0, left_mem_Icc.2 hT.le⟩)) ∘
        compSpatialLIE α ℝ hT coord =
      dataEquiv (α := α) 0 T ∘ (parabolicOperatorL hα₁.le A B C).prod
        (spatialTraceL (F := ℝ) (hab := hT) ⟨0, left_mem_Icc.2 hT.le⟩) := by
    funext u
    simp only [comp_apply, ContinuousLinearMap.prod_apply, spatialTraceL_apply, dataEquiv,
      LinearIsometryEquiv.prodCongr_apply]
    refine Prod.ext (euclideanParabolicOperatorL_compSpatialLIE_coord hα₁.le A B C u) ?_
    simp [compSpatialLIE_apply, spatialTrace_compSpatialL]
  rw [← Bijective.of_comp_iff' (dataEquiv (α := α) 0 T).bijective, ← hcomp]
  exact hE.comp (compSpatialLIE α ℝ hT coord).bijective

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
  let eSol := compSpatialLIE α ℝ ht coord
  let eEuclidean := euclideanTerminalDataCLE hα₀ hα₁ ht
    (fun _ _ ↦ evalCoord A (ContinuousLinearMap.mul ℝ ℝ))
    (fun _ ↦ evalCoord B (ContinuousLinearMap.id ℝ ℝ)) (evalCoord C 1)
    (hA.imp fun _ ⟨hlam, h⟩ ↦ ⟨hlam, evalCoord_ellipticity h⟩)
  eSol.toContinuousLinearEquiv.trans
    (eEuclidean.trans (dataEquiv (α := α) t₀ t₁).symm.toContinuousLinearEquiv)

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
  apply Prod.ext
  · ext p
    simp [realTerminalDataCLE, dataEquiv, -compSpatialLIE_apply,
      euclideanBackwardParabolicOperatorL_compSpatialLIE_coord]
  · ext x
    simp [realTerminalDataCLE, dataEquiv, compSpatialLIE_apply, spatialTrace_compSpatialL]

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
  have heq : (backwardParabolicOperatorL (ht := ht) hα₁.le A B C).prod
        (spatialTraceL (F := ℝ) ⟨t₁, right_mem_Icc.2 ht.le⟩) =
      (realTerminalDataCLE hα₀ hα₁ ht A B C ⟨lam, hlam, hA⟩).toContinuousLinearMap :=
    ContinuousLinearMap.ext fun u ↦ by simp [spatialTraceL_apply]
  exact heq ▸ ContinuousLinearMap.isInvertible_equiv

/-- Conjugacy between the line solution operator and the `ℝ¹` Euclidean solution operator. -/
private theorem realTerminalDataCLE_symm_eq {t₀ t₁ : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1) (ht : t₀ < t₁)
    (A : HolderSpace α (slab (E := ℝ) t₀ t₁) ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
    (B : HolderSpace α (slab (E := ℝ) t₀ t₁) ((ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
    (C : HolderSpace α (slab (E := ℝ) t₀ t₁) (ℝ →L[ℝ] ℝ))
    (hA : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ A p (ContinuousLinearMap.mul ℝ ℝ)) :
    (realTerminalDataCLE hα₀ hα₁ ht A B C hA).symm.toContinuousLinearMap =
      ((compSpatialLIE α ℝ ht coord).symm : _ →L[ℝ] _) ∘L
        (euclideanTerminalDataCLE hα₀ hα₁ ht
          (fun _ _ ↦ evalCoord A (ContinuousLinearMap.mul ℝ ℝ))
          (fun _ ↦ evalCoord B (ContinuousLinearMap.id ℝ ℝ)) (evalCoord C 1)
          (hA.imp fun _ ⟨hlam, h⟩ ↦ ⟨hlam, evalCoord_ellipticity h⟩)).symm.toContinuousLinearMap ∘L
        (dataEquiv (α := α) t₀ t₁ : _ →L[ℝ] _) :=
  ContinuousLinearMap.ext fun d ↦ by simp [realTerminalDataCLE]

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
    (fun _ _ ↦ (norm_evalCoord_le A (ContinuousLinearMap.opNorm_mul_le ℝ ℝ)).trans hAk)
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
    (fun _ _ ↦ (norm_evalCoord_le A (ContinuousLinearMap.opNorm_mul_le ℝ ℝ)).trans hAk)
    (fun _ ↦ (norm_evalCoord_le B ContinuousLinearMap.norm_id_le).trans hBk)
    ((norm_evalCoord_le C₀ norm_one.le).trans hCk)
    (fun _ _ ↦ (norm_evalCoord_le A' (ContinuousLinearMap.opNorm_mul_le ℝ ℝ)).trans hAk')
    (fun _ ↦ (norm_evalCoord_le B' ContinuousLinearMap.norm_id_le).trans hBk')
    ((norm_evalCoord_le C₀' norm_one.le).trans hCk')
  simp only [Finset.univ_unique, Finset.sum_singleton, ← evalCoord_sub] at hmid
  have hδ : ‖evalCoord (A - A') (ContinuousLinearMap.mul ℝ ℝ)‖ +
        ‖evalCoord (B - B') (ContinuousLinearMap.id ℝ ℝ)‖ + ‖evalCoord (C₀ - C₀') 1‖ ≤
      ‖A - A'‖ + ‖B - B'‖ + ‖C₀ - C₀'‖ :=
    add_le_add (add_le_add (norm_evalCoord_le (A - A') (ContinuousLinearMap.opNorm_mul_le ℝ ℝ))
      (norm_evalCoord_le (B - B') ContinuousLinearMap.norm_id_le))
      (norm_evalCoord_le (C₀ - C₀') norm_one.le)
  calc _ ≤ C * (‖evalCoord (A - A') (ContinuousLinearMap.mul ℝ ℝ)‖ +
          ‖evalCoord (B - B') (ContinuousLinearMap.id ℝ ℝ)‖ + ‖evalCoord (C₀ - C₀') 1‖) := by
        convert hmid using 1
    _ ≤ C * (‖A - A'‖ + ‖B - B'‖ + ‖C₀ - C₀'‖) := mul_le_mul_of_nonneg_left hδ hC

end TauCeti.ParabolicC2HolderSpace
