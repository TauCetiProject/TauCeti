/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.CauchyProblem
import TauCeti.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.Matrix.QuadraticBounds
import TauCeti.Analysis.Normed.Operator.Bilinear
import TauCeti.Analysis.PDE.Parabolic.Holder.Solvability

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
  (`ParabolicC2HolderSpace.realInitialDataCLE`,
  `ParabolicC2HolderSpace.isInvertible_parabolicOperatorL_prod_spatialTraceL_real`);
* by time reversal, so is the terminal-data map `u ↦ (P_back u, u(·, t₁))` of the backward
  operator `P_back u = ∂ₜu + A·D_x²u + B·D_xu + C·u` on every slab `ℝ × [t₀, t₁]`
  (`ParabolicC2HolderSpace.realTerminalDataCLE`,
  `ParabolicC2HolderSpace.isInvertible_backwardParabolicOperatorL_prod_spatialTraceL_real`).

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

/-- The coordinate `x ↦ x 0` of `ℝ¹ = EuclideanSpace ℝ (Fin 1)`, as a linear isometry. -/
private abbrev coordLIE : EuclideanSpace ℝ (Fin 1) ≃ₗᵢ[ℝ] ℝ :=
  (OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm

private theorem coordLIE_single (i : Fin 1) : coordLIE (EuclideanSpace.single i 1) = 1 := by
  rw [Subsingleton.elim i default]
  exact (OrthonormalBasis.singleton_repr_symm (ι := Fin 1) (𝕜 := ℝ)
    (EuclideanSpace.single default 1)).trans (by simp)

/-- The scalar field `p ↦ A (x₀ p, t) w` on the slab over `ℝ¹`, for a coefficient field `A` on the
slab over the line and a fixed argument `w`. -/
private def evalCoord {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : HolderSpace α (slab (E := ℝ) a b) (G →L[ℝ] ℝ)) (w : G) :
    HolderSpace α (slab (E := EuclideanSpace ℝ (Fin 1)) a b) ℝ :=
  HolderSpace.compLeftL (ContinuousLinearMap.apply ℝ ℝ w)
    (HolderSpace.slabSpaceIsometryEquivLIE coordLIE.toIsometryEquiv A)

private theorem evalCoord_apply {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : HolderSpace α (slab (E := ℝ) a b) (G →L[ℝ] ℝ)) (w : G)
    (p : slab (E := EuclideanSpace ℝ (Fin 1)) a b) :
    evalCoord A w p = A (slabSpaceMap coordLIE p) w := by simp [evalCoord]

private abbrev evalA (A : HolderSpace α (slab (E := ℝ) a b) ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ)) :
    Fin 1 → Fin 1 → HolderSpace α (slab (E := EuclideanSpace ℝ (Fin 1)) a b) ℝ :=
  fun _ _ ↦ evalCoord A (ContinuousLinearMap.mul ℝ ℝ)
private abbrev evalB (B : HolderSpace α (slab (E := ℝ) a b) ((ℝ →L[ℝ] ℝ) →L[ℝ] ℝ)) :
    Fin 1 → HolderSpace α (slab (E := EuclideanSpace ℝ (Fin 1)) a b) ℝ :=
  fun _ ↦ evalCoord B (ContinuousLinearMap.id ℝ ℝ)
private theorem ellipticity_evalCoord
    {A : HolderSpace α (slab (E := ℝ) a b) ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ)} {lam : ℝ}
    (hA : ∀ p, lam ≤ A p (ContinuousLinearMap.mul ℝ ℝ))
    (q : slab (E := EuclideanSpace ℝ (Fin 1)) a b) (ξ : EuclideanSpace ℝ (Fin 1)) :
    lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ evalA A i j q).toQuadraticForm' ξ := by
  rw [Matrix.toQuadraticForm'_eq_mul_norm_sq]
  exact mul_le_mul_of_nonneg_right (by simpa [evalA, evalCoord_apply] using hA _) (sq_nonneg _)

/-- **The forward operator on the line is the Euclidean operator on `ℝ¹`.** -/
private theorem euclideanParabolicOperatorL_compSpatialL_coord (hα : α ≤ 1)
    (A : HolderSpace α (slab (E := ℝ) a b) ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
    (B : HolderSpace α (slab (E := ℝ) a b) ((ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
    (C : HolderSpace α (slab (E := ℝ) a b) (ℝ →L[ℝ] ℝ)) (u : ParabolicC2HolderSpace α ℝ ℝ hab) :
    euclideanParabolicOperatorL hα (evalA A) (evalB B) (evalCoord C 1)
        (compSpatialL α ℝ hab (coordLIE.toContinuousLinearEquiv : _ →L[ℝ] ℝ) u) =
      HolderSpace.slabSpaceIsometryEquivLIE coordLIE.toIsometryEquiv
        (parabolicOperatorL hα A B C u) := by
  ext p
  simp only [euclideanParabolicOperatorL_apply, parabolicOperatorL_apply,
    HolderSpace.slabSpaceIsometryEquivLIE_apply, evalA, evalB, evalCoord_apply,
    timeDerivL_compSpatialL, spatialSecondFDerivL_compSpatialL, spatialFDerivL_compSpatialL,
    compSpatialL_apply, ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.coe_toIsometryEquiv, coordLIE_single, Finset.univ_unique,
    Finset.sum_singleton]
  set q := slabSpaceMap (coordLIE : _ → ℝ) p
  have hA := congrArg (A q) (spatialSecondFDerivL u q).eq_apply_one_one_smul_mul
  have hB := congrArg (B q) (spatialFDerivL u q).eq_apply_one_smul_id
  have hC := (C q).map_smul (u q) (1 : ℝ)
  simp only [map_smul, smul_eq_mul, mul_one] at hA hB hC
  rw [hA, hB, hC]
  ring

/-- Data transport `(f, g) ↦ (f ∘ (x₀ × id), g ∘ x₀)` from `ℝ` to `ℝ¹`. -/
private def dataCoordBridgeCLE (a b : ℝ) :
    (HolderSpace α (slab (E := ℝ) a b) ℝ × CkHolderSpace 2 α ℝ ℝ) ≃L[ℝ]
      (HolderSpace α (slab (E := EuclideanSpace ℝ (Fin 1)) a b) ℝ ×
        CkHolderSpace 2 α (EuclideanSpace ℝ (Fin 1)) ℝ) :=
  (HolderSpace.slabSpaceIsometryEquivLIE
      coordLIE.toIsometryEquiv).toContinuousLinearEquiv.prodCongr
    (CkHolderSpace.compLinearCLE coordLIE.toContinuousLinearEquiv)

end Transport

/-! ### Initial-data and terminal-data isomorphisms on the line -/

section InitialData

variable {T : ℝ≥0}

/-- **The initial-data isomorphism on the line.** For `0 < α < 1`, `0 < T`, and coefficient
fields `A`, `B`, `C` in `C_b^{α,α/2}(ℝ × [0, T])` with `0 < lam ≤ A p (h, k ↦ h k)`, the map
`u ↦ (∂ₜu - A·D_x²u - B·D_xu - C·u, u(·, 0))` as a Banach-space isomorphism onto
`C_b^{α,α/2}(ℝ × [0, T]) × C_b^{2,α}(ℝ)`. -/
def realInitialDataCLE (hα₀ : 0 < α) (hα₁ : α < 1) (hT : (0 : ℝ) < T)
    (A : HolderSpace α (slab (E := ℝ) 0 T) ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
    (B : HolderSpace α (slab (E := ℝ) 0 T) ((ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
    (C : HolderSpace α (slab (E := ℝ) 0 T) (ℝ →L[ℝ] ℝ))
    (hA : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ A p (ContinuousLinearMap.mul ℝ ℝ)) :
    ParabolicC2HolderSpace α ℝ ℝ hT ≃L[ℝ]
      HolderSpace α (slab (E := ℝ) 0 T) ℝ × CkHolderSpace 2 α ℝ ℝ :=
  (compSpatialCLE α ℝ hT coordLIE.toContinuousLinearEquiv).trans <|
    (euclideanInitialDataCLE hα₀ hα₁ hT (evalA A) (evalB B) (evalCoord C 1)
      (hA.elim fun lam h ↦ ⟨lam, h.1, ellipticity_evalCoord h.2⟩)).trans
      (dataCoordBridgeCLE 0 T).symm

section InitialDataEval

variable {hα₀ : 0 < α} {hα₁ : α < 1} {hT : (0 : ℝ) < T}
  {A : HolderSpace α (slab (E := ℝ) 0 T) ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ)}
  {B : HolderSpace α (slab (E := ℝ) 0 T) ((ℝ →L[ℝ] ℝ) →L[ℝ] ℝ)}
  {C : HolderSpace α (slab (E := ℝ) 0 T) (ℝ →L[ℝ] ℝ)}
  {hA : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ A p (ContinuousLinearMap.mul ℝ ℝ)}

/-- The initial-data isomorphism on the line sends `u` to `(P u, u(·, 0))`. -/
@[simp] theorem realInitialDataCLE_apply (u : ParabolicC2HolderSpace α ℝ ℝ hT) :
    realInitialDataCLE hα₀ hα₁ hT A B C hA u =
      (parabolicOperatorL hα₁.le A B C u,
        u.spatialTrace ⟨0, left_mem_Icc.2 hT.le⟩) := by
  apply (dataCoordBridgeCLE 0 T).injective
  rw [realInitialDataCLE, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  simp [dataCoordBridgeCLE, euclideanParabolicOperatorL_compSpatialL_coord]

/-- The inverse of `realInitialDataCLE` satisfies the forward PDE with forcing `d.1`. -/
@[simp] theorem parabolicOperatorL_realInitialDataCLE_symm_apply
    (d : HolderSpace α (slab (E := ℝ) 0 T) ℝ × CkHolderSpace 2 α ℝ ℝ) :
    parabolicOperatorL hα₁.le A B C
      ((realInitialDataCLE hα₀ hα₁ hT A B C hA).symm d) = d.1 :=
  congrArg Prod.fst <| (realInitialDataCLE_apply _).symm.trans
    ((realInitialDataCLE hα₀ hα₁ hT A B C hA).apply_symm_apply d)

/-- The inverse of `realInitialDataCLE` has initial trace `d.2`. -/
@[simp] theorem spatialTrace_realInitialDataCLE_symm_apply
    (d : HolderSpace α (slab (E := ℝ) 0 T) ℝ × CkHolderSpace 2 α ℝ ℝ) :
    ((realInitialDataCLE hα₀ hα₁ hT A B C hA).symm d).spatialTrace
      ⟨0, left_mem_Icc.2 hT.le⟩ = d.2 :=
  congrArg Prod.snd <| (realInitialDataCLE_apply _).symm.trans
    ((realInitialDataCLE hα₀ hα₁ hT A B C hA).apply_symm_apply d)

end InitialDataEval

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
      (spatialTraceL (F := ℝ) (hab := hT) ⟨0, left_mem_Icc.2 hT.le⟩)).IsInvertible :=
  ⟨realInitialDataCLE hα₀ hα₁ hT A B C ⟨lam, hlam, hA⟩,
    ContinuousLinearMap.ext fun u ↦ by simp [spatialTraceL_apply]⟩

end InitialData

section TerminalData

variable {t₀ t₁ : ℝ}

private def slabDuration (ht : t₀ < t₁) : ℝ≥0 := ⟨t₁ - t₀, sub_nonneg.2 ht.le⟩
private theorem coe_slabDuration (ht : t₀ < t₁) : (slabDuration ht : ℝ) = t₁ - t₀ := rfl
private theorem slabDuration_pos (ht : t₀ < t₁) : (0 : ℝ) < slabDuration ht := sub_pos.2 ht

private abbrev revHolderLIE {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (ht : t₀ < t₁) :
    HolderSpace α (slab (E := ℝ) t₀ t₁) Y ≃ₗᵢ[ℝ]
      HolderSpace α (slab (E := ℝ) 0 (slabDuration ht)) Y :=
  HolderSpace.slabTimeReverseLIE t₁ (sub_self t₁).symm (coe_slabDuration ht)

private abbrev revC2LIE (ht : t₀ < t₁) :
    ParabolicC2HolderSpace α ℝ ℝ ht ≃ₗᵢ[ℝ] ParabolicC2HolderSpace α ℝ ℝ (slabDuration_pos ht) :=
  timeReverseLIE (hab := ht) (a' := 0) (b' := (slabDuration ht : ℝ)) t₁ (sub_self t₁).symm
    (coe_slabDuration ht)

private def terminalDataBridgeCLE (ht : t₀ < t₁) :
    (HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ) ≃L[ℝ]
      (HolderSpace α (slab (E := ℝ) 0 (slabDuration ht)) ℝ × CkHolderSpace 2 α ℝ ℝ) :=
  ((revHolderLIE (α := α) ht).toContinuousLinearEquiv.trans
    (ContinuousLinearEquiv.neg ℝ)).prodCongr (ContinuousLinearEquiv.refl ℝ _)

private theorem ellipticity_revHolder (ht : t₀ < t₁)
    {A : HolderSpace α (slab (E := ℝ) t₀ t₁) ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ)} {lam : ℝ}
    (hA : ∀ p, lam ≤ A p (ContinuousLinearMap.mul ℝ ℝ))
    (p : slab (E := ℝ) 0 (slabDuration ht)) :
    lam ≤ revHolderLIE ht A p (ContinuousLinearMap.mul ℝ ℝ) := by
  rw [revHolderLIE, HolderSpace.slabTimeReverseLIE_apply]
  exact hA _

/-- **The terminal-data isomorphism on the line.** For `0 < α < 1`, `t₀ < t₁`, and coefficient
fields `A`, `B`, `C` in `C_b^{α,α/2}(ℝ × [t₀, t₁])` with `0 < lam ≤ A p (h, k ↦ h k)`, the map
`u ↦ (∂ₜu + A·D_x²u + B·D_xu + C·u, u(·, t₁))` as a Banach-space isomorphism onto
`C_b^{α,α/2}(ℝ × [t₀, t₁]) × C_b^{2,α}(ℝ)`. -/
def realTerminalDataCLE (hα₀ : 0 < α) (hα₁ : α < 1) (ht : t₀ < t₁)
    (A : HolderSpace α (slab (E := ℝ) t₀ t₁) ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
    (B : HolderSpace α (slab (E := ℝ) t₀ t₁) ((ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
    (C : HolderSpace α (slab (E := ℝ) t₀ t₁) (ℝ →L[ℝ] ℝ))
    (hA : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ A p (ContinuousLinearMap.mul ℝ ℝ)) :
    ParabolicC2HolderSpace α ℝ ℝ ht ≃L[ℝ]
      HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ :=
  (revC2LIE ht).toContinuousLinearEquiv.trans <|
    (realInitialDataCLE hα₀ hα₁ (slabDuration_pos ht)
      (revHolderLIE ht A) (revHolderLIE ht B) (revHolderLIE ht C)
      (hA.elim fun lam h ↦ ⟨lam, h.1, ellipticity_revHolder ht h.2⟩)).trans
      (terminalDataBridgeCLE ht).symm

section TerminalDataEval

variable {hα₀ : 0 < α} {hα₁ : α < 1} {ht : t₀ < t₁}
  {A : HolderSpace α (slab (E := ℝ) t₀ t₁) ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ)}
  {B : HolderSpace α (slab (E := ℝ) t₀ t₁) ((ℝ →L[ℝ] ℝ) →L[ℝ] ℝ)}
  {C : HolderSpace α (slab (E := ℝ) t₀ t₁) (ℝ →L[ℝ] ℝ)}
  {hA : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ A p (ContinuousLinearMap.mul ℝ ℝ)}

/-- The terminal-data isomorphism on the line sends `u` to `(P_back u, u(·, t₁))`. -/
@[simp] theorem realTerminalDataCLE_apply (u : ParabolicC2HolderSpace α ℝ ℝ ht) :
    realTerminalDataCLE hα₀ hα₁ ht A B C hA u =
      (backwardParabolicOperatorL hα₁.le A B C u,
        u.spatialTrace ⟨t₁, right_mem_Icc.2 ht.le⟩) := by
  apply (terminalDataBridgeCLE ht).injective
  simp only [realTerminalDataCLE, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply, realInitialDataCLE_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, spatialTrace_timeReverseLIE_left,
    terminalDataBridgeCLE, ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.neg_apply,
    ContinuousLinearEquiv.refl_apply]
  congr 1
  simpa only [revHolderLIE, HolderSpace.slabTimeReverseLIE_eq_compLipschitzL] using
    parabolicOperatorL_timeReverseLIE (T := t₁) (ha := (sub_self t₁).symm)
      (hb := coe_slabDuration ht) hα₁.le u

/-- The inverse of `realTerminalDataCLE` satisfies the backward PDE with forcing `d.1`. -/
@[simp] theorem backwardParabolicOperatorL_realTerminalDataCLE_symm_apply
    (d : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ) :
    backwardParabolicOperatorL hα₁.le A B C
      ((realTerminalDataCLE hα₀ hα₁ ht A B C hA).symm d) = d.1 :=
  congrArg Prod.fst <| (realTerminalDataCLE_apply _).symm.trans
    ((realTerminalDataCLE hα₀ hα₁ ht A B C hA).apply_symm_apply d)

/-- The inverse of `realTerminalDataCLE` has terminal trace `d.2`. -/
@[simp] theorem spatialTrace_realTerminalDataCLE_symm_apply
    (d : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ) :
    ((realTerminalDataCLE hα₀ hα₁ ht A B C hA).symm d).spatialTrace
      ⟨t₁, right_mem_Icc.2 ht.le⟩ = d.2 :=
  congrArg Prod.snd <| (realTerminalDataCLE_apply _).symm.trans
    ((realTerminalDataCLE hα₀ hα₁ ht A B C hA).apply_symm_apply d)

/-- The inverse of `realTerminalDataCLE` takes value `d.2 x` at `(x, t₁)`. -/
@[simp] theorem realTerminalDataCLE_symm_apply_slabMk_right
    (d : HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ) (x : ℝ) :
    (realTerminalDataCLE hα₀ hα₁ ht A B C hA).symm d
      (slabMk x ⟨t₁, right_mem_Icc.2 ht.le⟩) = d.2 x := by
  rw [← spatialTrace_apply, spatialTrace_realTerminalDataCLE_symm_apply]

end TerminalDataEval

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
      (spatialTraceL (F := ℝ) ⟨t₁, right_mem_Icc.2 ht.le⟩)).IsInvertible :=
  ⟨realTerminalDataCLE hα₀ hα₁ ht A B C ⟨lam, hlam, hA⟩,
    ContinuousLinearMap.ext fun u ↦ by simp [spatialTraceL_apply]⟩

end TerminalData

end TauCeti.ParabolicC2HolderSpace
