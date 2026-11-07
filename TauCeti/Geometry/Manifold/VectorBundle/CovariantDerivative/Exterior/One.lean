/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.ContMDiff.ContinuousAlternatingMap
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Exterior covariant differentiation of bundle-valued one-forms

For a connection on a vector bundle, the exterior covariant derivative of a one-form is
`d∇ α(X,Y) = ∇_X(α(Y)) - ∇_Y(α(X)) - α([X,Y])`.
The result is a smooth two-form on the existing alternating-map bundle. No connection on
the tangent bundle is chosen in this construction. The tensoriality criterion constructs
the pointwise alternating map from the vector-field formula.

The tangent-valued identity one-form differentiates to torsion. Applying the operator to
the covariant derivative of a section gives the curvature acting on that section. These
are the degree-one first structure equation and the degree-zero curvature identity.

The conventions follow Kobayashi–Nomizu, *Foundations of Differential Geometry*,
Volume I, Chapter III. The formal construction uses Mathlib's `TensorialAt.mkHom₂`
and the native `SmoothBundleForm.degreeOneEquiv` identification.
-/

public section

open Bundle FiberBundle TauCeti VectorField
open scoped ContDiff Manifold Topology

noncomputable section

namespace CovariantDerivative

section Bundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  (cov : CovariantDerivative I F V)

private def exteriorOneAux
    (A : ContMDiffSection I (E →L[ℝ] F) ∞ (fun x ↦ TangentSpace I x →L[ℝ] V x))
    (X Y : Π x : M, TangentSpace I x) (x : M) : V x :=
  cov (fun y ↦ A y (Y y)) x (X x) - cov (fun y ↦ A y (X y)) x (Y x) -
    A x (mlieBracket I X Y x)

omit [FiniteDimensional ℝ E] in
private theorem exteriorOneAux_swap
    (A : ContMDiffSection I (E →L[ℝ] F) ∞ (fun x ↦ TangentSpace I x →L[ℝ] V x))
    (X Y : Π x : M, TangentSpace I x) (x : M) :
    exteriorOneAux cov A X Y x = -exteriorOneAux cov A Y X x := by
  simp only [exteriorOneAux, mlieBracket_swap_apply (V := Y) (W := X), map_neg]
  abel

private theorem tensorialAt_exteriorOneAux_left
    (A : ContMDiffSection I (E →L[ℝ] F) ∞ (fun x ↦ TangentSpace I x →L[ℝ] V x))
    (Y : Π x : M, TangentSpace I x) (x : M) :
    TensorialAt I E (fun X ↦ exteriorOneAux cov A X Y x) x where
  add {X X'} hX hX' := by
    have hsum : (fun y ↦ A y ((X + X') y)) =
        (fun y ↦ A y (X y)) + fun y ↦ A y (X' y) := by ext y; simp
    have hA := A.contMDiff.mdifferentiableAt (x := x) (by simp)
    simp only [exteriorOneAux]
    rw [hsum,
      cov.isCovariantDerivativeOnUniv.add (hA.clm_bundle_apply hX)
        (hA.clm_bundle_apply hX')]
    simp only [mlieBracket_add_left hX hX', Pi.add_apply, map_add, add_apply]
    abel
  smul {f X} hf hX := by
    have hsmul : (fun y ↦ A y ((f • X) y)) = f • fun y ↦ A y (X y) := by
      ext y; simp
    have hA := A.contMDiff.mdifferentiableAt (x := x) (by simp)
    simp only [exteriorOneAux]
    rw [hsmul,
      cov.isCovariantDerivativeOnUniv.leibniz (hA.clm_bundle_apply hX) hf]
    simp only [mlieBracket_smul_left hf hX, Pi.smul_apply', map_smul, map_add,
      add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
    module

private theorem tensorialAt_exteriorOneAux_right
    (A : ContMDiffSection I (E →L[ℝ] F) ∞ (fun x ↦ TangentSpace I x →L[ℝ] V x))
    (X : Π x : M, TangentSpace I x) (x : M) :
    TensorialAt I E (fun Y ↦ exteriorOneAux cov A X Y x) x where
  add hY hY' := by
    rw [exteriorOneAux_swap, (tensorialAt_exteriorOneAux_left cov A X x).add hY hY',
      neg_add, ← exteriorOneAux_swap, ← exteriorOneAux_swap]
  smul hf hY := by
    rw [exteriorOneAux_swap, (tensorialAt_exteriorOneAux_left cov A X x).smul hf hY,
      ← smul_neg, ← exteriorOneAux_swap]

private def exteriorOneBilin
    (A : ContMDiffSection I (E →L[ℝ] F) ∞ (fun x ↦ TangentSpace I x →L[ℝ] V x)) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] V x :=
  TensorialAt.mkHom₂ (fun X Y ↦ exteriorOneAux cov A X Y x) x
    (fun Y _ ↦ tensorialAt_exteriorOneAux_left cov A Y x)
    (fun X _ ↦ tensorialAt_exteriorOneAux_right cov A X x)

private theorem exteriorOneBilin_apply
    (A : ContMDiffSection I (E →L[ℝ] F) ∞ (fun x ↦ TangentSpace I x →L[ℝ] V x))
    {X Y : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    exteriorOneBilin cov A x (X x) (Y x) = exteriorOneAux cov A X Y x :=
  TensorialAt.mkHom₂_apply _ _ hX hY

private def exteriorOneValue
    (A : ContMDiffSection I (E →L[ℝ] F) ∞ (fun x ↦ TangentSpace I x →L[ℝ] V x)) (x : M) :
    TangentSpace I x [⋀^Fin 2]→L[ℝ] V x :=
  AlternatingMap.toContinuousAlternatingMap
    (LinearMap.IsAlt.toAlternatingMap
      -- Keep the bilinear-map type explicit when elaborating the alternating constructor.
      (show (ContinuousLinearMap.toLinearMap₁₂ (exteriorOneBilin cov A x)).IsAlt from fun u ↦ by
        simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply]
        have h := exteriorOneBilin_apply cov A (mdifferentiableAt_extend I E u)
          (mdifferentiableAt_extend I E u)
        simpa [exteriorOneAux] using h))

private theorem exteriorOneValue_apply
    (A : ContMDiffSection I (E →L[ℝ] F) ∞ (fun x ↦ TangentSpace I x →L[ℝ] V x))
    {X Y : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    exteriorOneValue cov A x ![X x, Y x] = exteriorOneAux cov A X Y x := by
  simpa [exteriorOneValue] using exteriorOneBilin_apply cov A hX hY

private theorem exteriorOneValue_apply_eq_extend
    (A : ContMDiffSection I (E →L[ℝ] F) ∞ (fun x ↦ TangentSpace I x →L[ℝ] V x))
    (x : M) (v : Fin 2 → TangentSpace I x) :
    exteriorOneValue cov A x v =
      exteriorOneAux cov A (extend E (v 0)) (extend E (v 1)) x := by
  simpa [exteriorOneValue, exteriorOneBilin] using
    TensorialAt.mkHom₂_apply_eq_extend
      (fun Y _ ↦ tensorialAt_exteriorOneAux_left cov A Y x)
      (fun X _ ↦ tensorialAt_exteriorOneAux_right cov A X x) (v 0) (v 1)

private theorem exteriorOneValue_add
    (A B : ContMDiffSection I (E →L[ℝ] F) ∞ (fun x ↦ TangentSpace I x →L[ℝ] V x))
    (x : M) : exteriorOneValue cov (A + B) x =
      exteriorOneValue cov A x + exteriorOneValue cov B x := by
  ext v
  simp only [ContinuousAlternatingMap.add_apply, exteriorOneValue_apply_eq_extend]
  have hA := A.contMDiff.mdifferentiableAt (x := x) (by simp)
  have hB := B.contMDiff.mdifferentiableAt (x := x) (by simp)
  have hs (u : TangentSpace I x) :
      (fun y ↦ (A + B) y (extend E u y)) =
        (fun y ↦ A y (extend E u y)) + fun y ↦ B y (extend E u y) := by ext y; simp
  simp only [exteriorOneAux]
  rw [hs, hs, cov.isCovariantDerivativeOnUniv.add
    (hA.clm_bundle_apply (mdifferentiableAt_extend I E _))
    (hB.clm_bundle_apply (mdifferentiableAt_extend I E _)),
    cov.isCovariantDerivativeOnUniv.add
    (hA.clm_bundle_apply (mdifferentiableAt_extend I E _))
    (hB.clm_bundle_apply (mdifferentiableAt_extend I E _))]
  simp only [ContMDiffSection.coe_add, Pi.add_apply, add_apply]
  abel

private theorem exteriorOneValue_smul (c : ℝ)
    (A : ContMDiffSection I (E →L[ℝ] F) ∞ (fun x ↦ TangentSpace I x →L[ℝ] V x))
    (x : M) : exteriorOneValue cov (c • A) x = c • exteriorOneValue cov A x := by
  ext v
  simp only [ContinuousAlternatingMap.smul_apply, exteriorOneValue_apply_eq_extend]
  have hA := A.contMDiff.mdifferentiableAt (x := x) (by simp)
  have hs (u : TangentSpace I x) :
      (fun y ↦ (c • A) y (extend E u y)) = c • fun y ↦ A y (extend E u y) := by
    ext y; simp
  simp only [exteriorOneAux]
  rw [hs, hs, cov.isCovariantDerivativeOnUniv.smul_const c
    (hA.clm_bundle_apply (mdifferentiableAt_extend I E _)),
    cov.isCovariantDerivativeOnUniv.smul_const c
    (hA.clm_bundle_apply (mdifferentiableAt_extend I E _))]
  simp only [ContMDiffSection.coe_smul, Pi.smul_apply, smul_apply]
  module

variable [ContMDiffCovariantDerivative cov ∞]

/-- The covariant derivative of a smooth section, viewed as a smooth bundle-valued one-form.
This is exterior covariant differentiation in degree zero. -/
def covariantOneForm : ContMDiffSection I F ∞ V →ₗ[ℝ] SmoothBundleForm I F V 1 where
  toFun σ := SmoothBundleForm.degreeOneEquiv.symm ⟨cov σ, by
    exact contMDiffOn_univ.mp
      (ContMDiffCovariantDerivative.contMDiff.contMDiff (by simpa using σ.contMDiff.contMDiffOn))⟩
  map_add' σ τ := by
    apply SmoothBundleForm.ext
    intro x v
    simp only [SmoothBundleForm.degreeOneEquiv_symm_apply_apply, ContMDiffSection.coeFn_mk,
      ContMDiffSection.coe_add, Submodule.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply]
    rw [cov.isCovariantDerivativeOnUniv.add
      (σ.contMDiff.mdifferentiableAt (by simp)) (τ.contMDiff.mdifferentiableAt (by simp))]
    rfl
  map_smul' c σ := by
    apply SmoothBundleForm.ext
    intro x v
    simp only [SmoothBundleForm.degreeOneEquiv_symm_apply_apply, ContMDiffSection.coeFn_mk,
      ContMDiffSection.coe_smul, Submodule.coe_smul, Pi.smul_apply,
      ContinuousAlternatingMap.smul_apply, RingHom.id_apply]
    rw [cov.isCovariantDerivativeOnUniv.smul_const c (σ.contMDiff.mdifferentiableAt (by simp))]
    rfl

omit [FiniteDimensional ℝ E] in
/-- Evaluation of the covariant derivative as a one-form. -/
@[simp]
theorem covariantOneForm_apply (σ : ContMDiffSection I F ∞ V) (x : M)
    (v : Fin 1 → TangentSpace I x) :
    (cov.covariantOneForm σ).val x v = cov σ x (v 0) := by
  simp only [covariantOneForm, LinearMap.coe_mk, AddHom.coe_mk,
    SmoothBundleForm.degreeOneEquiv_symm_apply_apply]
  rfl

variable [T2Space M] [ContMDiffVectorBundle ∞ F V I]

private theorem contMDiff_exteriorOneBilin
    (A : ContMDiffSection I (E →L[ℝ] F) ∞ (fun x ↦ TangentSpace I x →L[ℝ] V x)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] F) x (exteriorOneBilin cov A x)) := by
  apply (TauCeti.Manifold.contMDiff_hom_iff _).2
  intro X hX
  apply (TauCeti.Manifold.contMDiff_hom_iff _).2
  intro Y hY
  have hXY := cov.contMDiff_apply hX (A.contMDiff.clm_bundle_apply hY)
  have hYX := cov.contMDiff_apply hY (A.contMDiff.clm_bundle_apply hX)
  have hbr := A.contMDiff.clm_bundle_apply (contMDiff_mlieBracket hX hY)
  refine ((hXY.sub_section hYX).sub_section hbr).congr fun x ↦ ?_
  exact congrArg (TotalSpace.mk' F x)
    (exteriorOneBilin_apply cov A (hX.mdifferentiableAt (by simp))
      (hY.mdifferentiableAt (by simp)))

private theorem contMDiff_exteriorOneValue
    (A : ContMDiffSection I (E →L[ℝ] F) ∞ (fun x ↦ TangentSpace I x →L[ℝ] V x)) :
    ContMDiff I (I.prod 𝓘(ℝ, E [⋀^Fin 2]→L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E [⋀^Fin 2]→L[ℝ] F) x (exteriorOneValue cov A x)) := by
  intro x
  rw [contMDiffAt_continuousAlternatingMap_bundle]
  refine ⟨contMDiffAt_id, TauCeti.contMDiffAt_continuousAlternatingMap_apply.2 fun v ↦ ?_⟩
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  have he : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
  have hs (i : Fin 2) : CMDiffAt ∞ (T% (fun y ↦ e.symm y (v i))) x := by
    rw [contMDiffAt_section]
    refine (contMDiffAt_const (c := v i)).congr_of_eventuallyEq ?_
    filter_upwards [e.open_baseSet.mem_nhds he] with y hy
    exact congr(Prod.snd $(e.apply_mk_symm hy (v i)))
  have h := ((contMDiff_exteriorOneBilin cov A x).clm_bundle_apply (hs 0)).clm_bundle_apply
    (hs 1)
  have hc := (contMDiffAt_totalSpace.1 h).2
  refine hc.congr_of_eventuallyEq ?_
  let e' := trivializationAt F V x
  have he' : x ∈ e'.baseSet := mem_baseSet_trivializationAt F V x
  filter_upwards [e.open_baseSet.mem_nhds he, e'.open_baseSet.mem_nhds he'] with y hy hy'
  simp only [ContinuousAlternatingMap.inCoordinates,
    ContinuousLinearMap.compContinuousAlternatingMap_coe,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    exteriorOneValue, AlternatingMap.coe_toContinuousAlternatingMap,
    LinearMap.IsAlt.toAlternatingMap_apply,
    ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply, Function.comp_apply]
  rw [Trivialization.symmL_apply _ hy, Trivialization.symmL_apply _ hy]
  exact e'.continuousLinearMapAt_apply_of_mem ℝ hy' _

/-- The exterior covariant derivative of smooth bundle-valued one-forms, as a real
linear map to smooth bundle-valued two-forms. Its normalization has no factor of two. -/
def exteriorCovDerivOne : SmoothBundleForm I F V 1 →ₗ[ℝ] SmoothBundleForm I F V 2 where
  toFun α := ⟨exteriorOneValue cov (SmoothBundleForm.degreeOneEquiv α),
    mem_smoothBundleForms.mpr ((isSmoothBundleForm_def ∞ _).mpr
      (contMDiff_exteriorOneValue cov _))⟩
  map_add' α β := by
    apply Subtype.ext
    funext x
    simpa only [map_add, Submodule.coe_add, Pi.add_apply] using exteriorOneValue_add cov
      (SmoothBundleForm.degreeOneEquiv α) (SmoothBundleForm.degreeOneEquiv β) x
  map_smul' c α := by
    apply Subtype.ext
    funext x
    simpa only [map_smul, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply] using
      exteriorOneValue_smul cov c (SmoothBundleForm.degreeOneEquiv α) x

/-- The vector-field formula for exterior covariant differentiation. The direction fields
need only be differentiable at the point of evaluation. -/
theorem exteriorCovDerivOne_apply (α : SmoothBundleForm I F V 1)
    {X Y : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    (cov.exteriorCovDerivOne α).eval₂ x (X x) (Y x) =
      cov (fun y ↦ α.val y ![Y y]) x (X x) -
        cov (fun y ↦ α.val y ![X y]) x (Y x) - α.val x ![mlieBracket I X Y x] := by
  rw [SmoothBundleForm.eval₂_apply]
  simpa only [exteriorCovDerivOne, exteriorOneAux,
    SmoothBundleForm.degreeOneEquiv_apply_apply, Matrix.vec_single_eq_const,
    LinearMap.coe_mk, AddHom.coe_mk] using
    exteriorOneValue_apply cov (SmoothBundleForm.degreeOneEquiv α) hX hY

/-- Exterior covariant differentiation squared on a smooth section is curvature acting
on that section. Both sides use the existing connection and curvature conventions. -/
theorem exteriorCovDerivOne_covariantOneForm [FiniteDimensional ℝ F]
    (σ : ContMDiffSection I F ∞ V) (x : M) (u v : TangentSpace I x) :
    (cov.exteriorCovDerivOne (cov.covariantOneForm σ)).eval₂ x u v =
      cov.curvatureTensor x u v (σ x) := by
  obtain ⟨X, hX, rfl⟩ := exists_contMDiff_section_eq I E ∞ u
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E ∞ v
  rw [exteriorCovDerivOne_apply cov _ (hX.mdifferentiableAt (by simp))
    (hY.mdifferentiableAt (by simp)), cov.curvatureTensor_apply x hX hY σ.contMDiff]
  simp only [covariantOneForm_apply, Matrix.cons_val_zero, curvatureOperator_apply]

end Bundle

section Tangent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative cov ∞]

/-- Cartan's first structure equation without a choice of frame: the exterior covariant
derivative of the tangent identity one-form is the native torsion tensor. -/
@[simp]
theorem exteriorCovDerivOne_tangentIdentity_apply (x : M) (u v : TangentSpace I x) :
    (cov.exteriorCovDerivOne SmoothBundleForm.tangentIdentity).val x ![u, v] =
      cov.torsion x u v := by
  rw [← SmoothBundleForm.eval₂_apply]
  obtain ⟨X, hX, rfl⟩ := exists_contMDiff_section_eq I E ∞ u
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E ∞ v
  rw [exteriorCovDerivOne_apply cov _ (hX.mdifferentiableAt (by simp))
    (hY.mdifferentiableAt (by simp)), cov.torsion_apply
    (hX.mdifferentiableAt (by simp)) (hY.mdifferentiableAt (by simp))]
  simp

/-- The tangent identity one-form is exterior-covariantly closed exactly when the
connection is torsion free. -/
@[simp]
theorem exteriorCovDerivOne_tangentIdentity_eq_zero_iff :
    cov.exteriorCovDerivOne SmoothBundleForm.tangentIdentity = 0 ↔ cov.torsion = 0 := by
  constructor
  · intro h
    ext x u v
    rw [← exteriorCovDerivOne_tangentIdentity_apply, h]
    simp
  · intro h
    apply SmoothBundleForm.ext_eval₂
    intro x u v
    rw [SmoothBundleForm.eval₂_apply, exteriorCovDerivOne_tangentIdentity_apply, h]
    simp

end Tangent

end CovariantDerivative
