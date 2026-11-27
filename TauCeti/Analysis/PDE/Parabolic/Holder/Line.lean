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
import TauCeti.Analysis.Normed.Operator.LinearIsometryEquiv.Prod
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
  `ParabolicC2HolderSpace.isInvertible_backwardParabolicOperatorL_prod_spatialTraceL_real`);
* for `0 < lam ≤ a`, `‖A‖, ‖B‖, ‖C‖ ≤ K`, and horizon/duration at most `T₀`, both solution
  operators are uniformly bounded in operator norm and Lipschitz in `(A, B, C)`
  (`ParabolicC2HolderSpace.exists_norm_realInitialDataCLE_symm_le`,
  `ParabolicC2HolderSpace.exists_norm_realInitialDataCLE_symm_sub_le`,
  `ParabolicC2HolderSpace.exists_norm_realTerminalDataCLE_symm_le`,
  `ParabolicC2HolderSpace.exists_norm_realTerminalDataCLE_symm_sub_le`).

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

private theorem evalCoord_sub {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A A' : HolderSpace α (slab (E := ℝ) a b) (G →L[ℝ] ℝ)) (w : G) :
    evalCoord A w - evalCoord A' w = evalCoord (A - A') w := by
  ext p
  simp [evalCoord_apply]

private theorem norm_evalCoord_le {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : HolderSpace α (slab (E := ℝ) a b) (G →L[ℝ] ℝ)) {w : G} (hw : ‖w‖ ≤ 1) :
    ‖evalCoord A w‖ ≤ ‖A‖ := by
  have h1 : ‖HolderSpace.compLeftL (ContinuousLinearMap.apply ℝ ℝ w)
      (HolderSpace.slabSpaceIsometryEquivLIE coordLIE.toIsometryEquiv A)‖ ≤
      ‖ContinuousLinearMap.apply ℝ ℝ w‖ *
        ‖HolderSpace.slabSpaceIsometryEquivLIE coordLIE.toIsometryEquiv A‖ :=
    (HolderSpace.compLeftL (ContinuousLinearMap.apply ℝ ℝ w)).le_of_opNorm_le
      (HolderSpace.norm_compLeftL_le _) _
  have h2 : ‖ContinuousLinearMap.apply ℝ ℝ w‖ ≤ 1 :=
    (ContinuousLinearMap.opNorm_apply_apply_le (𝕜 := ℝ) (G := ℝ) w).trans hw
  have h3 : ‖HolderSpace.slabSpaceIsometryEquivLIE coordLIE.toIsometryEquiv A‖ = ‖A‖ :=
    (HolderSpace.slabSpaceIsometryEquivLIE coordLIE.toIsometryEquiv).norm_map A
  calc ‖evalCoord A w‖
      ≤ ‖ContinuousLinearMap.apply ℝ ℝ w‖ *
          ‖HolderSpace.slabSpaceIsometryEquivLIE coordLIE.toIsometryEquiv A‖ := h1
    _ ≤ 1 * ‖A‖ := by
        rw [h3]
        exact mul_le_mul_of_nonneg_right h2 (norm_nonneg A)
    _ = ‖A‖ := one_mul _

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

private def dataCoordBridgeLIE (a b : ℝ) :
    (HolderSpace α (slab (E := ℝ) a b) ℝ × CkHolderSpace 2 α ℝ ℝ) ≃ₗᵢ[ℝ]
      (HolderSpace α (slab (E := EuclideanSpace ℝ (Fin 1)) a b) ℝ ×
        CkHolderSpace 2 α (EuclideanSpace ℝ (Fin 1)) ℝ) :=
  (HolderSpace.slabSpaceIsometryEquivLIE coordLIE.toIsometryEquiv).prodCongr
    (CkHolderSpace.compLinearLIE coordLIE)

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

private theorem realInitialDataCLE_symm_eq {T : ℝ≥0} (hα₀ : 0 < α) (hα₁ : α < 1)
    (hT : (0 : ℝ) < T)
    (A : HolderSpace α (slab (E := ℝ) 0 T) ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
    (B : HolderSpace α (slab (E := ℝ) 0 T) ((ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
    (C : HolderSpace α (slab (E := ℝ) 0 T) (ℝ →L[ℝ] ℝ))
    (hA : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ A p (ContinuousLinearMap.mul ℝ ℝ)) :
    (realInitialDataCLE hα₀ hα₁ hT A B C hA).symm.toContinuousLinearMap =
      ((compSpatialLIE α ℝ hT coordLIE).symm : _ →L[ℝ] _) ∘L
        (euclideanInitialDataCLE hα₀ hα₁ hT (evalA A) (evalB B) (evalCoord C 1)
          (hA.elim fun lam h ↦ ⟨lam, h.1, ellipticity_evalCoord h.2⟩)).symm.toContinuousLinearMap ∘L
        (dataCoordBridgeLIE (α := α) 0 T : _ →L[ℝ] _) :=
  ContinuousLinearMap.ext fun d ↦ by
    simp only [realInitialDataCLE, dataCoordBridgeCLE, dataCoordBridgeLIE,
      ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_trans_apply, ContinuousLinearEquiv.symm_symm,
      ContinuousLinearEquiv.prodCongr_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      LinearIsometryEquiv.prodCongr_apply, compSpatialCLE_symm_apply, compSpatialLIE_symm,
      compSpatialLIE_apply, CkHolderSpace.compLinearCLE_apply, CkHolderSpace.compLinearLIE_apply]
    rw [← LinearIsometryEquiv.toContinuousLinearEquiv_symm,
      ← coordLIE.symm.toContinuousLinearMap_toLinearIsometry,
      ← coordLIE.toContinuousLinearMap_toLinearIsometry]

/-- **Uniform Schauder estimate for the initial-value problem on the line.** For `0 < α < 1`, an
ellipticity constant `lam > 0`, a bound `K` on the Hölder norms of the coefficients and a bound `T₀`
on the horizon, the solution operators of the initial-value problems on `ℝ × [0, T]`, `T ≤ T₀`, are
bounded uniformly in operator norm. -/
theorem exists_norm_realInitialDataCLE_symm_le (hα₀ : 0 < α) (hα₁ : α < 1) {lam : ℝ}
    (hlam : 0 < lam) (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (A : HolderSpace α (slab (E := ℝ) 0 T) ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
        (B : HolderSpace α (slab (E := ℝ) 0 T) ((ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
        (C₀ : HolderSpace α (slab (E := ℝ) 0 T) (ℝ →L[ℝ] ℝ))
        (hA : ∀ p, lam ≤ A p (ContinuousLinearMap.mul ℝ ℝ)),
        ‖A‖ ≤ K → ‖B‖ ≤ K → ‖C₀‖ ≤ K →
        ‖(realInitialDataCLE hα₀ hα₁ hT A B C₀ ⟨lam, hlam, hA⟩).symm.toContinuousLinearMap‖ ≤
          C := by
  obtain ⟨C, hC, hest⟩ :=
    exists_norm_euclideanInitialDataCLE_symm_le (ι := Fin 1) hα₀ hα₁ hlam K T₀
  refine ⟨C, hC, fun T hT hTT₀ A B C₀ hA hAk hBk hCk ↦ ?_⟩
  rw [realInitialDataCLE_symm_eq,
    ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]
  exact hest T hT hTT₀ _ _ _ (ellipticity_evalCoord hA)
    (fun _ _ ↦ (norm_evalCoord_le A (ContinuousLinearMap.opNorm_mul_le ℝ ℝ)).trans hAk)
    (fun _ ↦ (norm_evalCoord_le B ContinuousLinearMap.norm_id_le).trans hBk)
    ((norm_evalCoord_le C₀ norm_one.le).trans hCk)

/-- **Lipschitz dependence of the line initial-value solution operator on `(A, B, C)`.** Under the
bounds of `exists_norm_realInitialDataCLE_symm_le`, the solution operators for `(A, B, C)` and
`(A', B', C')` differ in operator norm by at most `C (‖A - A'‖ + ‖B - B'‖ + ‖C - C'‖)`. -/
theorem exists_norm_realInitialDataCLE_symm_sub_le (hα₀ : 0 < α) (hα₁ : α < 1) {lam : ℝ}
    (hlam : 0 < lam) (K T₀ : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ≥0) (hT : (0 : ℝ) < T), T ≤ T₀ →
      ∀ (A A' : HolderSpace α (slab (E := ℝ) 0 T) ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
        (B B' : HolderSpace α (slab (E := ℝ) 0 T) ((ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
        (C₀ C₀' : HolderSpace α (slab (E := ℝ) 0 T) (ℝ →L[ℝ] ℝ))
        (hA : ∀ p, lam ≤ A p (ContinuousLinearMap.mul ℝ ℝ))
        (hA' : ∀ p, lam ≤ A' p (ContinuousLinearMap.mul ℝ ℝ)),
        ‖A‖ ≤ K → ‖B‖ ≤ K → ‖C₀‖ ≤ K → ‖A'‖ ≤ K → ‖B'‖ ≤ K → ‖C₀'‖ ≤ K →
        ‖(realInitialDataCLE hα₀ hα₁ hT A B C₀ ⟨lam, hlam, hA⟩).symm.toContinuousLinearMap -
          (realInitialDataCLE hα₀ hα₁ hT A' B' C₀'
            ⟨lam, hlam, hA'⟩).symm.toContinuousLinearMap‖ ≤
          C * (‖A - A'‖ + ‖B - B'‖ + ‖C₀ - C₀'‖) := by
  obtain ⟨C, hC, hest⟩ :=
    exists_norm_euclideanInitialDataCLE_symm_sub_le (ι := Fin 1) hα₀ hα₁ hlam K T₀
  refine ⟨C, hC, fun T hT hTT₀ A A' B B' C₀ C₀' hA hA' hAk hBk hCk hAk' hBk' hCk' ↦ ?_⟩
  have hmid := hest T hT hTT₀ _ _ _ _ _ _
    (ellipticity_evalCoord hA) (ellipticity_evalCoord hA')
    (fun _ _ ↦ (norm_evalCoord_le A (ContinuousLinearMap.opNorm_mul_le ℝ ℝ)).trans hAk)
    (fun _ ↦ (norm_evalCoord_le B ContinuousLinearMap.norm_id_le).trans hBk)
    ((norm_evalCoord_le C₀ norm_one.le).trans hCk)
    (fun _ _ ↦ (norm_evalCoord_le A' (ContinuousLinearMap.opNorm_mul_le ℝ ℝ)).trans hAk')
    (fun _ ↦ (norm_evalCoord_le B' ContinuousLinearMap.norm_id_le).trans hBk')
    ((norm_evalCoord_le C₀' norm_one.le).trans hCk')
  simp only [Finset.univ_unique, Finset.sum_singleton, evalCoord_sub] at hmid
  have heq (X : HolderSpace α (slab (E := ℝ) 0 T) ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
      (Y : HolderSpace α (slab (E := ℝ) 0 T) ((ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
      (Z : HolderSpace α (slab (E := ℝ) 0 T) (ℝ →L[ℝ] ℝ))
      (hX : ∀ p, lam ≤ X p (ContinuousLinearMap.mul ℝ ℝ)) :
      (euclideanInitialDataCLE hα₀ hα₁ hT (evalA X) (evalB Y) (evalCoord Z 1)
        ((⟨lam, hlam, hX⟩ : ∃ l, 0 < l ∧ ∀ p, l ≤ X p (ContinuousLinearMap.mul ℝ ℝ)).elim
          fun l h ↦ ⟨l, h.1, ellipticity_evalCoord h.2⟩)).symm.toContinuousLinearMap =
      (euclideanInitialDataCLE hα₀ hα₁ hT (evalA X) (evalB Y) (evalCoord Z 1)
        ⟨lam, hlam, ellipticity_evalCoord hX⟩).symm.toContinuousLinearMap := rfl
  rw [realInitialDataCLE_symm_eq, realInitialDataCLE_symm_eq, heq A B C₀ hA, heq A' B' C₀' hA',
    ← ContinuousLinearMap.comp_sub, ← ContinuousLinearMap.sub_comp,
    ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]
  have hδ : ‖evalCoord (A - A') (ContinuousLinearMap.mul ℝ ℝ)‖ +
        ‖evalCoord (B - B') (ContinuousLinearMap.id ℝ ℝ)‖ + ‖evalCoord (C₀ - C₀') 1‖ ≤
      ‖A - A'‖ + ‖B - B'‖ + ‖C₀ - C₀'‖ :=
    add_le_add (add_le_add (norm_evalCoord_le (A - A') (ContinuousLinearMap.opNorm_mul_le ℝ ℝ))
      (norm_evalCoord_le (B - B') ContinuousLinearMap.norm_id_le))
      (norm_evalCoord_le (C₀ - C₀') norm_one.le)
  -- Bridge the product-space topology/norm instance diamond on
  -- `HolderSpace α (slab 0 T) ℝ × CkHolderSpace 2 α (EuclideanSpace ℝ (Fin 1)) ℝ` between
  -- `Solvability` (`instTopologicalSpaceProd`) and `opNorm_comp_linearIsometryEquiv`
  -- (uniform product topology), as in `exists_norm_euclideanTerminalDataCLE_symm_sub_le`.
  convert hmid.trans (mul_le_mul_of_nonneg_left hδ hC) using 1

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

private def terminalDataBridgeLIE (ht : t₀ < t₁) :
    (HolderSpace α (slab (E := ℝ) t₀ t₁) ℝ × CkHolderSpace 2 α ℝ ℝ) ≃ₗᵢ[ℝ]
      (HolderSpace α (slab (E := ℝ) 0 (slabDuration ht)) ℝ × CkHolderSpace 2 α ℝ ℝ) :=
  ((revHolderLIE (α := α) ht).trans (LinearIsometryEquiv.neg ℝ)).prodCongr
    (LinearIsometryEquiv.refl ℝ _)

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

/-- The underlying continuous linear map of `realTerminalDataCLE` is the product of the backward
parabolic operator on the line and the terminal spatial trace. -/
theorem realTerminalDataCLE_toContinuousLinearMap :
    (realTerminalDataCLE hα₀ hα₁ ht A B C hA).toContinuousLinearMap =
      (backwardParabolicOperatorL (ht := ht) hα₁.le A B C).prod
        (spatialTraceL (F := ℝ) ⟨t₁, right_mem_Icc.2 ht.le⟩) :=
  ContinuousLinearMap.ext fun u ↦ by simp [spatialTraceL_apply]

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
    realTerminalDataCLE_toContinuousLinearMap⟩

private theorem realTerminalDataCLE_symm_eq (hα₀ : 0 < α) (hα₁ : α < 1) (ht : t₀ < t₁)
    (A : HolderSpace α (slab (E := ℝ) t₀ t₁) ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
    (B : HolderSpace α (slab (E := ℝ) t₀ t₁) ((ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
    (C : HolderSpace α (slab (E := ℝ) t₀ t₁) (ℝ →L[ℝ] ℝ))
    (hA : ∃ lam : ℝ, 0 < lam ∧ ∀ p, lam ≤ A p (ContinuousLinearMap.mul ℝ ℝ)) :
    (realTerminalDataCLE hα₀ hα₁ ht A B C hA).symm.toContinuousLinearMap =
      ((revC2LIE (α := α) ht).symm :
          ParabolicC2HolderSpace α ℝ ℝ (slabDuration_pos ht) →L[ℝ] _) ∘L
        (realInitialDataCLE hα₀ hα₁ (slabDuration_pos ht)
          (revHolderLIE ht A) (revHolderLIE ht B) (revHolderLIE ht C)
          (hA.elim fun lam h ↦
            ⟨lam, h.1, ellipticity_revHolder ht h.2⟩)).symm.toContinuousLinearMap ∘L
        (terminalDataBridgeLIE (α := α) ht : _ →L[ℝ] _) :=
  ContinuousLinearMap.ext fun d ↦ by
    simp [realTerminalDataCLE, terminalDataBridgeCLE, terminalDataBridgeLIE]

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
  obtain ⟨C, hC, hest⟩ := exists_norm_realInitialDataCLE_symm_le (α := α) hα₀ hα₁ hlam K T₀
  refine ⟨C, hC, fun {t₀ t₁} ht hTT₀ A B C₀ hA hAk hBk hCk ↦ ?_⟩
  rw [realTerminalDataCLE_symm_eq,
    ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]
  exact hest (slabDuration ht) (slabDuration_pos ht) (by exact_mod_cast hTT₀)
    _ _ _ (ellipticity_revHolder ht hA)
    (((revHolderLIE ht).norm_map A).le.trans hAk)
    (((revHolderLIE ht).norm_map B).le.trans hBk)
    (((revHolderLIE ht).norm_map C₀).le.trans hCk)

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
    exists_norm_realInitialDataCLE_symm_sub_le (α := α) hα₀ hα₁ hlam K T₀
  refine ⟨C, hC, fun {t₀ t₁} ht hTT₀ A A' B B' C₀ C₀' hA hA' hAk hBk hCk hAk' hBk' hCk' ↦ ?_⟩
  have hmid := hest (slabDuration ht) (slabDuration_pos ht) (by exact_mod_cast hTT₀)
    _ _ _ _ _ _ (ellipticity_revHolder ht hA) (ellipticity_revHolder ht hA')
    (((revHolderLIE ht).norm_map A).le.trans hAk)
    (((revHolderLIE ht).norm_map B).le.trans hBk)
    (((revHolderLIE ht).norm_map C₀).le.trans hCk)
    (((revHolderLIE ht).norm_map A').le.trans hAk')
    (((revHolderLIE ht).norm_map B').le.trans hBk')
    (((revHolderLIE ht).norm_map C₀').le.trans hCk')
  simp only [← map_sub, (revHolderLIE ht).norm_map] at hmid
  have heq (X : HolderSpace α (slab (E := ℝ) t₀ t₁) ((ℝ →L[ℝ] ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
      (Y : HolderSpace α (slab (E := ℝ) t₀ t₁) ((ℝ →L[ℝ] ℝ) →L[ℝ] ℝ))
      (Z : HolderSpace α (slab (E := ℝ) t₀ t₁) (ℝ →L[ℝ] ℝ))
      (hX : ∀ p, lam ≤ X p (ContinuousLinearMap.mul ℝ ℝ)) :
      (realInitialDataCLE hα₀ hα₁ (slabDuration_pos ht)
        (revHolderLIE ht X) (revHolderLIE ht Y) (revHolderLIE ht Z)
        ((⟨lam, hlam, hX⟩ : ∃ l, 0 < l ∧ ∀ p, l ≤ X p (ContinuousLinearMap.mul ℝ ℝ)).elim
          fun l h ↦ ⟨l, h.1, ellipticity_revHolder ht h.2⟩)).symm.toContinuousLinearMap =
      (realInitialDataCLE hα₀ hα₁ (slabDuration_pos ht)
        (revHolderLIE ht X) (revHolderLIE ht Y) (revHolderLIE ht Z)
        ⟨lam, hlam, ellipticity_revHolder ht hX⟩).symm.toContinuousLinearMap := rfl
  rw [realTerminalDataCLE_symm_eq, realTerminalDataCLE_symm_eq, heq A B C₀ hA, heq A' B' C₀' hA',
    ← ContinuousLinearMap.comp_sub, ← ContinuousLinearMap.sub_comp,
    ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]
  exact hmid

end TerminalData

end TauCeti.ParabolicC2HolderSpace
