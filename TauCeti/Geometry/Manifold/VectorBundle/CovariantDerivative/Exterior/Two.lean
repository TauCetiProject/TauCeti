/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Form
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Derivative.Torsion
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Derivative.Connection
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Geometry.Manifold.ContMDiff.ContinuousAlternatingMap
import TauCeti.LinearAlgebra.BilinearMap.Multilinear
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Exterior covariant differentiation of two-forms

Exterior covariant differentiation sends a bundle-valued two-form to a bundle-valued
three-form. Its intrinsic formula uses covariant derivatives of evaluations and Lie
brackets. Alternating the induced tensor derivative gives this operator after adding
the torsion correction of the auxiliary tangent connection. The correction makes the
answer independent of that auxiliary connection.

For the induced endomorphism connection, the curvature two-form is covariantly closed.
All forms and connections use the native alternating-map and Hom bundles.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I,
  Chapter III (exterior covariant differentiation and the second Bianchi identity).
* The construction uses `CovariantDerivative.hom`, `CovariantDerivative.curvatureForm`
  and `CovariantDerivative.derivCurvatureTensor_cyclic_eq_neg_torsion`.
-/

public noncomputable section

open Bundle FiberBundle TauCeti
open scoped ContDiff Manifold

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  (cov : CovariantDerivative I F V)
  (covT : CovariantDerivative I E (TangentSpace I : M → Type _))

private def twoFormTensor (α : SmoothBundleForm I F V 2) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] V x :=
  LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ
      (α.val x).toAlternatingMap.toMultilinearMap.toBilinMap)

omit [T2Space M] [ContMDiffVectorBundle ∞ F V I] in
private theorem twoFormTensor_apply (α : SmoothBundleForm I F V 2) (x : M)
    (u v : TangentSpace I x) : twoFormTensor α x u v = α.eval₂ x u v := by
  simp [twoFormTensor, SmoothBundleForm.eval₂_apply]

private theorem contMDiff_twoFormTensor (α : SmoothBundleForm I F V 2) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] F) x (twoFormTensor α x)) := by
  apply (TauCeti.Manifold.contMDiff_hom_iff _).2
  intro X hX
  apply (TauCeti.Manifold.contMDiff_hom_iff _).2
  intro Y hY
  simpa only [twoFormTensor_apply] using α.contMDiff_eval₂ hX hY

private theorem hom_twoFormTensor_apply (α : SmoothBundleForm I F V 2)
    {X Y : Π x : M, TangentSpace I x}
    {x : M} (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (u : TangentSpace I x) :
    (covT.hom (covT.hom cov)) (twoFormTensor α) x u (X x) (Y x) =
      cov (fun y ↦ α.eval₂ y (X y) (Y y)) x u -
        α.eval₂ x (covT X x u) (Y x) - α.eval₂ x (X x) (covT Y x u) := by
  have hα := contMDiff_twoFormTensor α
  rw [hom_apply _ _ (hα.mdifferentiableAt (by simp)) hX,
    sub_apply,
    hom_apply _ _ ((hα.mdifferentiableAt (by simp)).clm_bundle_apply hX) hY]
  simp only [twoFormTensor_apply]
  abel

private theorem hom_twoFormTensor_swap (α : SmoothBundleForm I F V 2) (x : M)
    (d u v : TangentSpace I x) :
    (covT.hom (covT.hom cov)) (twoFormTensor α) x d u v =
      -(covT.hom (covT.hom cov)) (twoFormTensor α) x d v u := by
  obtain ⟨X, hX, rfl⟩ := exists_contMDiff_section_eq I E ∞ u
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E ∞ v
  have heq : (fun y ↦ α.eval₂ y (X y) (Y y)) =
      -(fun y ↦ α.eval₂ y (Y y) (X y)) := by
    funext y
    exact α.eval₂_swap y _ _
  rw [hom_twoFormTensor_apply cov covT α
      (hX.mdifferentiableAt (by simp)) (hY.mdifferentiableAt (by simp)),
    hom_twoFormTensor_apply cov covT α
      (hY.mdifferentiableAt (by simp)) (hX.mdifferentiableAt (by simp)), heq,
    cov.isCovariantDerivativeOnUniv.neg
      ((α.contMDiff_eval₂ hY hX).mdifferentiableAt (by simp))]
  simp only [neg_apply]
  rw [α.eval₂_swap x (covT X x d) (Y x), α.eval₂_swap x (X x) (covT Y x d)]
  abel

private def exteriorTwoValue (α : SmoothBundleForm I F V 2) (x : M)
    (u v w : TangentSpace I x) : V x :=
  let D := (covT.hom (covT.hom cov)) (twoFormTensor α) x
  let A := twoFormTensor α x
  D u v w + D v w u + D w u v +
    A (covT.torsion x u v) w + A (covT.torsion x v w) u + A (covT.torsion x w u) v

private theorem exteriorTwoValue_self (α : SmoothBundleForm I F V 2) (x : M)
    (u v : TangentSpace I x) : exteriorTwoValue cov covT α x u u v = 0 := by
  have hD := hom_twoFormTensor_swap cov covT α x v u u
  have hD₀ : (covT.hom (covT.hom cov)) (twoFormTensor α) x v u u = 0 := by
    have hz := eq_neg_iff_add_eq_zero.mp hD
    rw [← two_smul ℝ] at hz
    exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
  simp only [exteriorTwoValue, hom_twoFormTensor_swap cov covT α x u u v,
    hD₀, covT.torsion_self, map_zero, zero_apply,
    covT.torsion_antisymm (x := x) v u, map_neg, neg_apply]
  abel

omit [T2Space M] [ContMDiffVectorBundle ∞ F V I] in
private theorem exteriorTwoValue_cyclic (α : SmoothBundleForm I F V 2) (x : M)
    (u v w : TangentSpace I x) :
    exteriorTwoValue cov covT α x u v w = exteriorTwoValue cov covT α x v w u := by
  dsimp only [exteriorTwoValue]
  abel

private theorem exteriorTwoValue_self_last (α : SmoothBundleForm I F V 2) (x : M)
    (u v : TangentSpace I x) : exteriorTwoValue cov covT α x u v v = 0 := by
  rw [exteriorTwoValue_cyclic, exteriorTwoValue_self]

private theorem exteriorTwoValue_self_outer (α : SmoothBundleForm I F V 2) (x : M)
    (u v : TangentSpace I x) : exteriorTwoValue cov covT α x u v u = 0 := by
  rw [exteriorTwoValue_cyclic, exteriorTwoValue_self_last]

private def exteriorTwoAlternating (α : SmoothBundleForm I F V 2) (x : M) :
    TangentSpace I x [⋀^Fin 3]→L[ℝ] V x := by
  -- Cache the iterated Hom norms before checking the multilinearity laws.
  let _ : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
  let _ : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
  let _ : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
  let _ : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance
  -- Use mk' to avoid a free decidable-equality instance in the tuple calculations.
  exact AlternatingMap.toContinuousAlternatingMap
    ({ toMultilinearMap := MultilinearMap.mk'
        (fun v : Fin 3 → TangentSpace I x ↦ exteriorTwoValue cov covT α x (v 0) (v 1) (v 2))
        (by
          intro v i a b
          rcases i with ⟨i, hi⟩
          interval_cases i <;> simp [exteriorTwoValue, add_apply, map_add] <;> abel)
        (by
          intro v i c a
          rcases i with ⟨i, hi⟩
          interval_cases i <;> simp [exteriorTwoValue, smul_apply, map_smul, smul_add])
       map_eq_zero_of_eq' v i j hij hne := by
        dsimp only [MultilinearMap.mk']
        rcases i with ⟨i, hi⟩
        rcases j with ⟨j, hj⟩
        interval_cases i <;> interval_cases j <;> norm_num at hij hne
        · rw [hij]; exact exteriorTwoValue_self cov covT α x _ _
        · rw [hij]; exact exteriorTwoValue_self_outer cov covT α x _ _
        · rw [hij]; exact exteriorTwoValue_self cov covT α x _ _
        · rw [hij]; exact exteriorTwoValue_self_last cov covT α x _ _
        · rw [hij]; exact exteriorTwoValue_self_outer cov covT α x _ _
        · rw [hij]; exact exteriorTwoValue_self_last cov covT α x _ _
      } : TangentSpace I x [⋀^Fin 3]→ₗ[ℝ] V x)

private theorem exteriorTwoValue_apply (α : SmoothBundleForm I F V 2)
    {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    exteriorTwoValue cov covT α x (X x) (Y x) (Z x) =
      cov (fun y ↦ α.eval₂ y (Y y) (Z y)) x (X x) +
      cov (fun y ↦ α.eval₂ y (Z y) (X y)) x (Y x) +
      cov (fun y ↦ α.eval₂ y (X y) (Y y)) x (Z x) -
      α.eval₂ x (VectorField.mlieBracket I X Y x) (Z x) -
      α.eval₂ x (VectorField.mlieBracket I Y Z x) (X x) -
      α.eval₂ x (VectorField.mlieBracket I Z X x) (Y x) := by
  rw [exteriorTwoValue,
    hom_twoFormTensor_apply cov covT α hY hZ,
    hom_twoFormTensor_apply cov covT α hZ hX,
    hom_twoFormTensor_apply cov covT α hX hY,
    covT.torsion_apply hX hY, covT.torsion_apply hY hZ, covT.torsion_apply hZ hX]
  simp only [← twoFormTensor_apply, map_sub, sub_apply]
  have hswap (u v : TangentSpace I x) :
      twoFormTensor α x u v = -twoFormTensor α x v u := by
    simp only [twoFormTensor_apply]
    exact α.eval₂_swap x u v
  rw [hswap (Y x) (covT Z x (X x)), hswap (Z x) (covT X x (Y x)),
    hswap (X x) (covT Y x (Z x))]
  abel

private theorem exteriorTwoAlternating_apply (α : SmoothBundleForm I F V 2) (x : M)
    (v : Fin 3 → TangentSpace I x) :
    exteriorTwoAlternating cov covT α x v =
      exteriorTwoValue cov covT α x (v 0) (v 1) (v 2) := by
  simp [exteriorTwoAlternating]

private theorem contMDiffOn_exteriorTwoValue [ContMDiffCovariantDerivative cov ∞]
    (α : SmoothBundleForm I F V 2) {u : Set M} (hu : IsOpen u)
    (X : Fin 3 → Π y : M, TangentSpace I y) (hX : ∀ i, CMDiff[u] ∞ (T% (X i))) :
    CMDiff[u] ∞ (T% (fun y ↦ exteriorTwoValue cov covT α y (X 0 y) (X 1 y) (X 2 y))) := by
  have : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I (∞ + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  have hA := (contMDiff_twoFormTensor α).contMDiffOn (s := u)
  have hEval (i j : Fin 3) : CMDiff[u] ∞
      (T% (fun y ↦ α.eval₂ y (X i y) (X j y))) := by
    simpa only [twoFormTensor_apply] using (hA.clm_bundle_apply (hX i)).clm_bundle_apply (hX j)
  have hCov := cov.contMDiffCovariantDerivativeOn_of_isOpen (n := ⊤) hu
  have hD (i j k : Fin 3) : CMDiff[u] ∞
      (T% (fun y ↦ cov (fun z ↦ α.eval₂ z (X i z) (X j z)) y (X k y))) :=
    (hCov.contMDiff (by simpa using hEval i j)).clm_bundle_apply (hX k)
  have hBracket (i j : Fin 3) : CMDiff[u] ∞
      (T% (VectorField.mlieBracket I (X i) (X j))) := by
    intro y hy
    exact (((hX i y hy).contMDiffAt (hu.mem_nhds hy)).mlieBracket_vectorField
      ((hX j y hy).contMDiffAt (hu.mem_nhds hy)) (m := ⊤) (by simp)).contMDiffWithinAt
  have hB (i j k : Fin 3) : CMDiff[u] ∞
      (T% (fun y ↦ α.eval₂ y (VectorField.mlieBracket I (X i) (X j) y) (X k y))) := by
    simpa only [twoFormTensor_apply] using
      (hA.clm_bundle_apply (hBracket i j)).clm_bundle_apply (hX k)
  apply ((((((hD 1 2 0).add_section (hD 2 0 1)).add_section (hD 0 1 2)).sub_section
    (hB 0 1 2)).sub_section (hB 1 2 0)).sub_section (hB 2 0 1)).congr
  intro y hy
  exact congrArg (TotalSpace.mk' F y) (exteriorTwoValue_apply cov covT α
    (((hX 0 y hy).contMDiffAt (hu.mem_nhds hy)).mdifferentiableAt (by simp))
    (((hX 1 y hy).contMDiffAt (hu.mem_nhds hy)).mdifferentiableAt (by simp))
    (((hX 2 y hy).contMDiffAt (hu.mem_nhds hy)).mdifferentiableAt (by simp)))

private theorem contMDiff_exteriorTwoAlternating [ContMDiffCovariantDerivative cov ∞]
    (α : SmoothBundleForm I F V 2) :
    ContMDiff I (I.prod 𝓘(ℝ, E [⋀^Fin 3]→L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E [⋀^Fin 3]→L[ℝ] F) x
        (exteriorTwoAlternating cov covT α x)) := by
  intro x
  rw [contMDiffAt_continuousAlternatingMap_bundle]
  refine ⟨contMDiffAt_id, TauCeti.contMDiffAt_continuousAlternatingMap_apply.2 fun v ↦ ?_⟩
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  let eV := trivializationAt F V x
  let X (i : Fin 3) (y : M) := e.symmL ℝ y (v i)
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
  have hXV (i : Fin 3) : CMDiff[e.baseSet] ∞ (T% (X i)) := by
    intro y hy
    exact ((e.contMDiffAt_symmL hy).clm_bundle_apply
      (by rw [contMDiffAt_section_iff]; exact contMDiffAt_const)).contMDiffWithinAt
  have hS := contMDiffOn_exteriorTwoValue cov covT α e.open_baseSet X hXV
  have hc := (contMDiffAt_totalSpace_iff.1 (hS.contMDiffAt (e.open_baseSet.mem_nhds hx))).2
  refine hc.congr_of_eventuallyEq ?_
  have hxV : x ∈ eV.baseSet := mem_baseSet_trivializationAt F V x
  filter_upwards [e.open_baseSet.mem_nhds hx, eV.open_baseSet.mem_nhds hxV] with y hy hyV
  simp only [ContinuousAlternatingMap.inCoordinates,
    ContinuousLinearMap.compContinuousAlternatingMap_coe,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, exteriorTwoAlternating_apply,
    Function.comp_apply]
  exact eV.continuousLinearMapAt_apply_of_mem ℝ hyV _

private theorem exteriorTwoValue_add (α β : SmoothBundleForm I F V 2) (x : M)
    (u v w : TangentSpace I x) :
    exteriorTwoValue cov covT (α + β) x u v w =
      exteriorTwoValue cov covT α x u v w + exteriorTwoValue cov covT β x u v w := by
  have hsum : twoFormTensor (α + β) = twoFormTensor α + twoFormTensor β := by
    ext y a b
    simp [twoFormTensor_apply]
  have hα := (contMDiff_twoFormTensor α).mdifferentiableAt (by simp) (x := x)
  have hβ := (contMDiff_twoFormTensor β).mdifferentiableAt (by simp) (x := x)
  simp only [exteriorTwoValue, hsum,
    (covT.hom (covT.hom cov)).isCovariantDerivativeOnUniv.add hα hβ,
    Pi.add_apply, add_apply]
  abel

private theorem exteriorTwoValue_smul (c : ℝ) (α : SmoothBundleForm I F V 2) (x : M)
    (u v w : TangentSpace I x) :
    exteriorTwoValue cov covT (c • α) x u v w = c • exteriorTwoValue cov covT α x u v w := by
  have hsmul : twoFormTensor (c • α) = c • twoFormTensor α := by
    ext y a b
    simp [twoFormTensor_apply]
  have hα := (contMDiff_twoFormTensor α).mdifferentiableAt (by simp) (x := x)
  simp only [exteriorTwoValue, hsmul,
    (covT.hom (covT.hom cov)).isCovariantDerivativeOnUniv.smul_const c hα,
    Pi.smul_apply, smul_apply, smul_add]

variable [ContMDiffCovariantDerivative cov ∞]

/-- Exterior covariant differentiation of bundle-valued two-forms. The tangent connection
is auxiliary: `exteriorCovariantDerivativeTwo_eq` proves independence of this choice,
including for tangent connections with torsion. The output is a smooth three-form. -/
def exteriorCovariantDerivativeTwo :
    SmoothBundleForm I F V 2 →ₗ[ℝ] SmoothBundleForm I F V 3 where
  toFun α := ⟨exteriorTwoAlternating cov covT α, mem_smoothBundleForms.mpr
    ((isSmoothBundleForm_def ∞ _).mpr (contMDiff_exteriorTwoAlternating cov covT α))⟩
  map_add' α β := by
    apply SmoothBundleForm.ext
    intro x v
    simpa only [Submodule.coe_add, exteriorTwoAlternating_apply, Pi.add_apply,
      ContinuousAlternatingMap.add_apply] using
      exteriorTwoValue_add cov covT α β x (v 0) (v 1) (v 2)
  map_smul' c α := by
    apply SmoothBundleForm.ext
    intro x v
    simpa only [Submodule.coe_smul, exteriorTwoAlternating_apply, Pi.smul_apply,
      ContinuousAlternatingMap.smul_apply, RingHom.id_apply] using
      exteriorTwoValue_smul cov covT c α x (v 0) (v 1) (v 2)

/-- The intrinsic formula for exterior covariant differentiation on three vector fields
that are differentiable at the tested point. No auxiliary tangent connection occurs
on the right, and the Lie-bracket terms allow noncoordinate fields. -/
theorem exteriorCovariantDerivativeTwo_apply (α : SmoothBundleForm I F V 2)
    {X Y Z : Π y : M, TangentSpace I y} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    (cov.exteriorCovariantDerivativeTwo covT α).val x ![X x, Y x, Z x] =
      cov (fun y ↦ α.eval₂ y (Y y) (Z y)) x (X x) +
      cov (fun y ↦ α.eval₂ y (Z y) (X y)) x (Y x) +
      cov (fun y ↦ α.eval₂ y (X y) (Y y)) x (Z x) -
      α.eval₂ x (VectorField.mlieBracket I X Y x) (Z x) -
      α.eval₂ x (VectorField.mlieBracket I Y Z x) (X x) -
      α.eval₂ x (VectorField.mlieBracket I Z X x) (Y x) := by
  simpa [exteriorCovariantDerivativeTwo, exteriorTwoAlternating_apply] using
    exteriorTwoValue_apply cov covT α hX hY hZ

/-- Exterior covariant differentiation of two-forms does not depend on the auxiliary
connection on the tangent bundle. Neither tangent connection needs to be smooth or torsion-free. -/
theorem exteriorCovariantDerivativeTwo_eq
    (covT' : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    cov.exteriorCovariantDerivativeTwo covT = cov.exteriorCovariantDerivativeTwo covT' := by
  apply LinearMap.ext
  intro α
  apply SmoothBundleForm.ext
  intro x v
  obtain ⟨X, hX, hXv⟩ := exists_contMDiff_section_eq I E ∞ (v 0)
  obtain ⟨Y, hY, hYv⟩ := exists_contMDiff_section_eq I E ∞ (v 1)
  obtain ⟨Z, hZ, hZv⟩ := exists_contMDiff_section_eq I E ∞ (v 2)
  have hv : v = ![X x, Y x, Z x] := by
    ext i
    rcases i with ⟨i, hi⟩
    interval_cases i <;> simp [hXv, hYv, hZv]
  rw [hv, exteriorCovariantDerivativeTwo_apply cov covT α
    (hX.mdifferentiableAt (by simp)) (hY.mdifferentiableAt (by simp))
      (hZ.mdifferentiableAt (by simp)),
    exteriorCovariantDerivativeTwo_apply cov covT' α
      (hX.mdifferentiableAt (by simp)) (hY.mdifferentiableAt (by simp))
      (hZ.mdifferentiableAt (by simp))]

/-- **The second Bianchi identity as covariant closedness of the curvature form.**
The coefficient connection is the actual induced endomorphism connection; no metric,
torsion assumption or choice of frame is involved. -/
@[simp]
theorem exteriorCovariantDerivativeTwo_curvatureForm [FiniteDimensional ℝ F] :
    (cov.hom cov).exteriorCovariantDerivativeTwo covT cov.curvatureForm = 0 := by
  have hΩ : twoFormTensor cov.curvatureForm = cov.curvatureTensorCLM := by
    ext x u v s
    simp [twoFormTensor_apply, curvatureTensorCLM_apply]
  apply SmoothBundleForm.ext
  intro x v
  ext s
  simp only [exteriorCovariantDerivativeTwo, LinearMap.coe_mk, AddHom.coe_mk,
    exteriorTwoAlternating_apply, exteriorTwoValue, hΩ,
    ← cov.derivCurvatureTensorCLM_eq_hom covT x, derivCurvatureTensorCLM_apply,
    curvatureTensorCLM_apply, Pi.zero_apply,
    Submodule.coe_zero, ContinuousAlternatingMap.coe_zero, zero_apply, add_apply]
  have h := congrArg (fun A ↦ A s)
    (cov.derivCurvatureTensor_cyclic_eq_neg_torsion covT x (v 0) (v 1) (v 2))
  simp only [LinearMap.add_apply, LinearMap.neg_apply] at h
  rw [h]
  abel

end CovariantDerivative
