/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.Frame.Basic

import TauCeti.Analysis.CStarAlgebra.Module.Adjointable.Order

/-!
# Polar decomposition for modules with a finite Parseval frame

For a right `A`-linear equivalence `T : E ≃ₗ[Aᵐᵒᵖ] F` out of a right Hilbert `A`-module `E`
equipped with a finite Parseval frame `x : ι → E` into a complete right Hilbert `A`-module `F`:

* By `hx.completeSpace`, `E` is complete, and `T` is adjointable with explicit adjoint
  `frameAdjoint Aᵐᵒᵖ x T`.
* Using continuity of `T⁻¹` (`LinearEquiv.continuous_symm`) and Paschke's inequality, `T* ∘ T`
  has a strictly positive scalar lower bound in `TauCeti.AdjointableMap Aᵐᵒᵖ E E`, so the
  operator modulus `|T| = √(T* ∘ T)` (`TauCeti.AdjointableMap.abs`) is invertible as a module
  endomorphism (`CStarModule.IsParsevalFrame.polarModulus`).
* The quotient `U = T ∘ |T|⁻¹` is a unitary isomorphism `E ≃ₗᵢ[Aᵐᵒᵖ] F`
  (`CStarModule.IsParsevalFrame.polarUnitary`), giving the canonical polar decomposition
  `T = U ∘ |T|` (`CStarModule.IsParsevalFrame.polarUnitary_polarModulus_apply`), shown to be unique
  and
  independent of `x` (`CStarModule.IsParsevalFrame.eq_polarModulus_of_inner_eq`,
  `CStarModule.IsParsevalFrame.eq_polarModulus_toLinearMap`,
  `CStarModule.IsParsevalFrame.polarModulus_eq`, `CStarModule.IsParsevalFrame.polarUnitary_eq`).

## Main declarations

* `TauCeti.CStarModule.polarMatrix`
* `CStarModule.IsParsevalFrame.polarModulus`, `CStarModule.IsParsevalFrame.polarUnitary`,
  `CStarModule.IsParsevalFrame.polarUnitary_polarModulus_apply`
* `CStarModule.IsParsevalFrame.eq_polarModulus_of_inner_eq`,
  `CStarModule.IsParsevalFrame.eq_polarModulus_toLinearMap`,
  `CStarModule.IsParsevalFrame.polarModulus_eq`, `CStarModule.IsParsevalFrame.polarUnitary_eq`

## References

* M. Frank and D. R. Larson, *Frames in Hilbert C⋆-modules and C⋆-algebras*, J. Operator Theory 48
  (2002), 273–314.
* E. C. Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 3.
* I. Raeburn and D. P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*, Chapter 2.
-/

public section

open MulOpposite Matrix CStarModule TauCeti
open CStarMatrix (mulVecCLM mulVecLinearMap)
open scoped WithCStarModule

namespace TauCeti.CStarModule

section Polar

/-- Matrix `CStarMatrix.gram A (fun i ↦ T (x i)) + (1 - CStarMatrix.gram A x)` in
`CStarMatrix ι ι A` for a family `x : ι → E` and a function `T : E → F`. When `x` is a Parseval
frame and `T` is right `A`-linear, this represents `T* T ⊕ 1` on `C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)` with
the identity on the complementary summand `ker (CStarMatrix.gram A x)`. -/
def polarMatrix (A : Type*) {ι E F : Type*} [DecidableEq ι] [AddGroupWithOne A] [Inner Aᵐᵒᵖ E]
    [Inner Aᵐᵒᵖ F] (x : ι → E) (T : E → F) : CStarMatrix ι ι A :=
  CStarMatrix.gram A (fun i ↦ T (x i)) + (1 - CStarMatrix.gram A x)

section PolarBasic

variable {A ι E F : Type*} [DecidableEq ι] [AddGroupWithOne A] [Inner Aᵐᵒᵖ E] [Inner Aᵐᵒᵖ F]

theorem polarMatrix_def (x : ι → E) (T : E → F) :
    polarMatrix A x T = CStarMatrix.gram A (fun i ↦ T (x i)) + (1 - CStarMatrix.gram A x) := (rfl)

@[simp] theorem polarMatrix_apply (x : ι → E) (T : E → F) (i j : ι) : polarMatrix A x T i j =
    unop (inner Aᵐᵒᵖ (T (x i)) (T (x j))) + (1 - CStarMatrix.gram A x) i j := by
  simp [polarMatrix_def]

end PolarBasic

/-- Over a unital C⋆-algebra, for a Parseval frame `x` and an arbitrary function `T : E → F`,
`polarMatrix A x T` is positive (`0 ≤ polarMatrix A x T`). -/
theorem _root_.CStarModule.IsParsevalFrame.polarMatrix_nonneg {A ι E F : Type*} [Fintype ι]
    [DecidableEq ι] [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [AddCommGroup E] [Module ℂ E] [SMul Aᵐᵒᵖ E] [Norm E] [CStarModule Aᵐᵒᵖ E]
    [AddCommGroup F] [Module ℂ F] [SMul Aᵐᵒᵖ F] [Norm F] [CStarModule Aᵐᵒᵖ F]
    {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E → F) : 0 ≤ polarMatrix A x T :=
  add_nonneg (CStarMatrix.gram_nonneg _) (CStarMatrix.isStarProjection_gram hx).one_sub.nonneg

section PolarAlg

variable {A ι E F 𝓕 : Type*} [Fintype ι] [DecidableEq ι] [Ring A] [StarRing A]
  [Module ℂ A] [PartialOrder A] [Norm Aᵐᵒᵖ] [AddCommGroup E] [Module ℂ E]
  [Module Aᵐᵒᵖ E] [Norm E] [CStarModule Aᵐᵒᵖ E] [AddCommGroup F] [Module ℂ F] [Module Aᵐᵒᵖ F]
  [Norm F] [CStarModule Aᵐᵒᵖ F] [FunLike 𝓕 E F] [LinearMapClass 𝓕 Aᵐᵒᵖ E F]

/-- When `T` is right `A`-linear, multiplying `polarMatrix A x T` on the right by the Gram
projection `CStarMatrix.gram A x` isolates the Gram matrix of `T ∘ x`:
`polarMatrix A x T * CStarMatrix.gram A x = CStarMatrix.gram A (fun i ↦ T (x i))`. -/
theorem _root_.CStarModule.IsParsevalFrame.polarMatrix_mul_gram {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : 𝓕) :
    polarMatrix A x T * CStarMatrix.gram A x = CStarMatrix.gram A (fun i ↦ T (x i)) := by
  rw [polarMatrix_def, add_mul, (CStarMatrix.isStarProjection_gram hx).one_sub_mul_self, add_zero]
  ext i j
  conv_rhs => rw [CStarMatrix.gram_apply, ← hx.sum_inner_smul (x j), map_sum, inner_sum_right']
  simp [CStarMatrix.mul_apply, map_smul, Finset.unop_sum]

/-- When `T` is right `A`-linear, `polarMatrix A x T` commutes with the Gram projection
`CStarMatrix.gram A x`, so functional-calculus operations on `polarMatrix A x T` preserve the
Gram range. -/
theorem _root_.CStarModule.IsParsevalFrame.commute_polarMatrix_gram {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : 𝓕) : Commute (polarMatrix A x T) (CStarMatrix.gram A x) :=
  IsSelfAdjoint.commute_of_mul_eq_isSelfAdjoint _ _ _
    ((TauCeti.CStarMatrix.isSelfAdjoint_gram _).add
      (CStarMatrix.isStarProjection_gram hx).one_sub.isSelfAdjoint)
    (CStarMatrix.isStarProjection_gram hx).isSelfAdjoint (TauCeti.CStarMatrix.isSelfAdjoint_gram _)
    (hx.polarMatrix_mul_gram T)

end PolarAlg

section NormedHelpers

variable {A ι E F : Type*} [Fintype ι] [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [Module Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [Module Aᵐᵒᵖ F] [CStarModule Aᵐᵒᵖ F]
  [CompleteSpace E] [CompleteSpace F]

private noncomputable def equivAdjointableMap {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (T : E ≃ₗ[Aᵐᵒᵖ] F) : AdjointableMap Aᵐᵒᵖ E F :=
  AdjointableMap.ofAdjointPair T (frameAdjoint Aᵐᵒᵖ x T)
    (hx.isAdjointPair_frameAdjoint T).inner_eq_cstarModule

private noncomputable def equivSymmCLM {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (T : E ≃ₗ[Aᵐᵒᵖ] F) : F →L[ℂ] E :=
  have : IsScalarTower ℂ Aᵐᵒᵖ E := CStarModule.isScalarTower Aᵐᵒᵖ E
  have : IsScalarTower ℂ Aᵐᵒᵖ F := CStarModule.isScalarTower Aᵐᵒᵖ F
  let T_op := equivAdjointableMap hx T
  have hcont : Continuous (T.restrictScalars ℂ) := by
    convert T_op.continuous
    ext z
    simp [T_op, equivAdjointableMap]
  ⟨(T.restrictScalars ℂ).symm, (T.restrictScalars ℂ).continuous_symm hcont⟩

private theorem inner_le_norm_sq_smul_equivSymmCLM {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) :
    inner Aᵐᵒᵖ z z ≤ ‖equivSymmCLM hx T‖ ^ 2 • inner Aᵐᵒᵖ (T z) (T z) := by
  have h := ContinuousLinearMap.inner_map_map_le_norm_sq_smul (equivSymmCLM hx T)
    (fun a y ↦ (T.symm.map_smul a y : _)) (T z)
  simpa [equivSymmCLM] using h

private theorem isStrictlyPositive_adjoint_comp_self {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (T : E ≃ₗ[Aᵐᵒᵖ] F) :
    IsStrictlyPositive ((equivAdjointableMap hx T).adjoint.comp (equivAdjointableMap hx T)) := by
  let T_op := equivAdjointableMap hx T
  let T_inv := equivSymmCLM hx T
  have hpos : (0 : ℝ) < 1 + ‖T_inv‖ ^ 2 := by positivity
  refine (isStrictlyPositive_algebraMap (inv_pos.mpr hpos)).of_le ?_
  rw [AdjointableMap.le_iff_forall_inner_le]
  intro z
  rw [AdjointableMap.algebraMap_apply, AdjointableMap.comp_apply, T_op.adjoint_inner_right]
  have hpas := inner_le_norm_sq_smul_equivSymmCLM hx T z
  rw [← Complex.coe_smul, inner_smul_right_complex, Complex.coe_smul]
  calc (1 + ‖T_inv‖ ^ 2)⁻¹ • inner Aᵐᵒᵖ z z
      ≤ (1 + ‖T_inv‖ ^ 2)⁻¹ • ((1 + ‖T_inv‖ ^ 2) • inner Aᵐᵒᵖ (T z) (T z)) := by
        refine smul_le_smul_of_nonneg_left (hpas.trans ?_) (by positivity)
        exact smul_le_smul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) inner_self_nonneg
    _ = inner Aᵐᵒᵖ (T_op z) (T_op z) := by
        rw [smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
        simp [T_op, equivAdjointableMap]

private theorem isUnit_abs_equivAdjointableMap {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (T : E ≃ₗ[Aᵐᵒᵖ] F) : IsUnit (equivAdjointableMap hx T).abs := by
  have hu_sqrt : IsUnit (CFC.sqrt ((equivAdjointableMap hx T).adjoint.comp
      (equivAdjointableMap hx T))) :=
    (isStrictlyPositive_adjoint_comp_self hx T).isUnit_cfcSqrt _
  have hu_sq : IsUnit ((equivAdjointableMap hx T).abs * (equivAdjointableMap hx T).abs) := by
    rw [AdjointableMap.abs_mul_abs,
      ← CFC.sqrt_mul_sqrt_self _ (AdjointableMap.adjoint_comp_self_nonneg _)]
    exact hu_sqrt.mul hu_sqrt
  exact ((Commute.refl _).isUnit_mul_iff.mp hu_sq).1

private noncomputable def adjointableEndToLinearMap
    (S : AdjointableMap Aᵐᵒᵖ E E) : E →ₗ[Aᵐᵒᵖ] E where
  toFun := S
  map_add' := map_add S
  map_smul' := S.map_smul_coeff

private noncomputable def polarModulusAux {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (T : E ≃ₗ[Aᵐᵒᵖ] F) : E ≃ₗ[Aᵐᵒᵖ] E :=
  let hunit := isUnit_abs_equivAdjointableMap hx T
  LinearEquiv.ofLinearMap
    (adjointableEndToLinearMap (equivAdjointableMap hx T).abs)
    (adjointableEndToLinearMap (hunit.unit⁻¹ : (AdjointableMap Aᵐᵒᵖ E E)ˣ))
    (LinearMap.ext fun z ↦ by
      have hmul : (equivAdjointableMap hx T).abs *
          ((hunit.unit⁻¹ : (AdjointableMap Aᵐᵒᵖ E E)ˣ) : AdjointableMap Aᵐᵒᵖ E E) = 1 := by
        calc (equivAdjointableMap hx T).abs *
              ((hunit.unit⁻¹ : (AdjointableMap Aᵐᵒᵖ E E)ˣ) : AdjointableMap Aᵐᵒᵖ E E)
            = (hunit.unit : AdjointableMap Aᵐᵒᵖ E E) * ↑hunit.unit⁻¹ := by
              rw [hunit.unit_spec]
          _ = 1 := Units.mul_inv _
      have hz := congrArg (fun S : AdjointableMap Aᵐᵒᵖ E E ↦ S z) hmul
      rw [AdjointableMap.mul_def, AdjointableMap.comp_apply, AdjointableMap.one_def,
        AdjointableMap.id_apply] at hz
      exact hz)
    (LinearMap.ext fun z ↦ by
      have hmul : ((hunit.unit⁻¹ : (AdjointableMap Aᵐᵒᵖ E E)ˣ) : AdjointableMap Aᵐᵒᵖ E E) *
          (equivAdjointableMap hx T).abs = 1 := by
        calc ((hunit.unit⁻¹ : (AdjointableMap Aᵐᵒᵖ E E)ˣ) : AdjointableMap Aᵐᵒᵖ E E) *
              (equivAdjointableMap hx T).abs
            = ↑hunit.unit⁻¹ * (hunit.unit : AdjointableMap Aᵐᵒᵖ E E) := by
              rw [hunit.unit_spec]
          _ = 1 := Units.inv_mul _
      have hz := congrArg (fun S : AdjointableMap Aᵐᵒᵖ E E ↦ S z) hmul
      rw [AdjointableMap.mul_def, AdjointableMap.comp_apply, AdjointableMap.one_def,
        AdjointableMap.id_apply] at hz
      exact hz)

private theorem polarModulusAux_apply {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) :
    polarModulusAux hx T z = (equivAdjointableMap hx T).abs z := (rfl)

private theorem polarModulusAux_isAdjointPair {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (T : E ≃ₗ[Aᵐᵒᵖ] F) :
    LinearMap.IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip
      (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip (polarModulusAux hx T) (polarModulusAux hx T) := by
  rw [isAdjointPair_inner_iff]; intro y z
  rw [polarModulusAux_apply, polarModulusAux_apply]
  have hM := (equivAdjointableMap hx T).abs.adjoint_inner_right y z
  rw [AdjointableMap.isSelfAdjoint_iff_adjoint_eq.mp (AdjointableMap.isSelfAdjoint_abs _)] at hM
  exact hM.symm

private theorem polarModulusAux_inner_right_nonneg {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) : 0 ≤ inner Aᵐᵒᵖ z (polarModulusAux hx T z) := by
  rw [polarModulusAux_apply]
  exact AdjointableMap.nonneg_iff_forall_inner_nonneg.mp (AdjointableMap.abs_nonneg _) z

private theorem polarModulusAux_inner_inner {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (T : E ≃ₗ[Aᵐᵒᵖ] F) (y z : E) :
    inner Aᵐᵒᵖ (polarModulusAux hx T y) (polarModulusAux hx T z) = inner Aᵐᵒᵖ (T y) (T z) := by
  rw [polarModulusAux_apply, polarModulusAux_apply]
  simpa [equivAdjointableMap] using AdjointableMap.inner_abs_abs (equivAdjointableMap hx T) y z

private theorem polarModulusAux_polarModulusAux_apply {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) :
    polarModulusAux hx T (polarModulusAux hx T z) = frameAdjoint Aᵐᵒᵖ x T (T z) := by
  rw [polarModulusAux_apply, polarModulusAux_apply, ← AdjointableMap.comp_apply,
    ← AdjointableMap.mul_def, AdjointableMap.abs_mul_abs, AdjointableMap.comp_apply]
  simp [equivAdjointableMap]

private theorem polarModulusAux_eq_of_inner_eq {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (T : E ≃ₗ[Aᵐᵒᵖ] F) (P : E → E)
    (hP_sa : ∀ y z : E, inner Aᵐᵒᵖ (P y) z = inner Aᵐᵒᵖ y (P z))
    (hP_nonneg : ∀ z : E, 0 ≤ inner Aᵐᵒᵖ z (P z))
    (hP_inner : ∀ y z : E, inner Aᵐᵒᵖ (P y) (P z) = inner Aᵐᵒᵖ (T y) (T z)) (z : E) :
    P z = polarModulusAux hx T z := by
  let P_op : AdjointableMap Aᵐᵒᵖ E E := AdjointableMap.ofAdjointPair P P hP_sa
  let T_op := equivAdjointableMap hx T
  have hP_pos : 0 ≤ P_op := AdjointableMap.nonneg_iff_forall_inner_nonneg.mpr fun w ↦ by
    simpa [P_op] using hP_nonneg w
  have hP_sq : P_op.adjoint.comp P_op = T_op.adjoint.comp T_op := by
    refine AdjointableMap.ext fun v ↦ ext_inner_left (A := Aᵐᵒᵖ) fun u ↦ ?_
    have h1 : inner Aᵐᵒᵖ (P_op u) (P_op v) = inner Aᵐᵒᵖ (T_op u) (T_op v) := by
      simpa [P_op, T_op, equivAdjointableMap] using hP_inner u v
    rw [AdjointableMap.comp_apply, P_op.adjoint_inner_right, h1, ← T_op.adjoint_inner_right,
      ← AdjointableMap.comp_apply]
  have hPM : P_op = T_op.abs := calc
    P_op = P_op.abs := (AdjointableMap.abs_of_nonneg hP_pos).symm
    _ = CFC.sqrt (P_op.abs * P_op.abs) := (CFC.sqrt_mul_self _ (AdjointableMap.abs_nonneg _)).symm
    _ = CFC.sqrt (T_op.abs * T_op.abs) := by
        rw [AdjointableMap.abs_mul_abs, hP_sq, ← AdjointableMap.abs_mul_abs]
    _ = T_op.abs := CFC.sqrt_mul_self _ (AdjointableMap.abs_nonneg _)
  rw [polarModulusAux_apply]
  simpa [P_op, T_op] using congrArg (fun (f : AdjointableMap Aᵐᵒᵖ E E) ↦ f z) hPM

end NormedHelpers

variable {A ι E F : Type*} [Fintype ι] [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [Module Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]
  [SeminormedAddCommGroup F] [NormedSpace ℂ F] [Module Aᵐᵒᵖ F] [CStarModule Aᵐᵒᵖ F]
  [CompleteSpace F]

/-- Positive self-adjoint modulus `|T| : E ≃ₗ[Aᵐᵒᵖ] E` of `T : E ≃ₗ[Aᵐᵒᵖ] F` into a complete right
Hilbert `A`-module `F`. -/
noncomputable def _root_.CStarModule.IsParsevalFrame.polarModulus {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) : E ≃ₗ[Aᵐᵒᵖ] E :=
  let : NormedAddCommGroup E := normedAddCommGroupOfCStarModule Aᵐᵒᵖ E
  let : NormedAddCommGroup F := normedAddCommGroupOfCStarModule Aᵐᵒᵖ F
  let : CompleteSpace E := hx.completeSpace
  polarModulusAux hx T

/-- `hx.polarModulus T` is self-adjoint as a module operator on `E`. -/
theorem _root_.CStarModule.IsParsevalFrame.isAdjointPair_polarModulus {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) :
    LinearMap.IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip
      (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip (hx.polarModulus T) (hx.polarModulus T) :=
  let : NormedAddCommGroup E := normedAddCommGroupOfCStarModule Aᵐᵒᵖ E
  let : NormedAddCommGroup F := normedAddCommGroupOfCStarModule Aᵐᵒᵖ F
  let : CompleteSpace E := hx.completeSpace
  polarModulusAux_isAdjointPair hx T

/-- `hx.polarModulus T` is positive: `0 ≤ ⟨z, |T| z⟩_A` for all `z : E`. -/
theorem _root_.CStarModule.IsParsevalFrame.inner_polarModulus_right_nonneg {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) :
    0 ≤ inner Aᵐᵒᵖ z (hx.polarModulus T z) :=
  let : NormedAddCommGroup E := normedAddCommGroupOfCStarModule Aᵐᵒᵖ E
  let : NormedAddCommGroup F := normedAddCommGroupOfCStarModule Aᵐᵒᵖ F
  let : CompleteSpace E := hx.completeSpace
  polarModulusAux_inner_right_nonneg hx T z

/-- `hx.polarModulus T` has the same Gram inner products as `T`:
`⟨|T| y, |T| z⟩_A = ⟨T y, T z⟩_A`. -/
@[simp]
theorem _root_.CStarModule.IsParsevalFrame.inner_polarModulus_polarModulus {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (y z : E) :
    inner Aᵐᵒᵖ (hx.polarModulus T y) (hx.polarModulus T z) = inner Aᵐᵒᵖ (T y) (T z) :=
  let : NormedAddCommGroup E := normedAddCommGroupOfCStarModule Aᵐᵒᵖ E
  let : NormedAddCommGroup F := normedAddCommGroupOfCStarModule Aᵐᵒᵖ F
  let : CompleteSpace E := hx.completeSpace
  polarModulusAux_inner_inner hx T y z

/-- The square of `hx.polarModulus T` equals `T* ∘ T`:
`|T| (|T| z) = frameAdjoint Aᵐᵒᵖ x T (T z)`. -/
theorem _root_.CStarModule.IsParsevalFrame.polarModulus_polarModulus_apply {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) :
    hx.polarModulus T (hx.polarModulus T z) = frameAdjoint Aᵐᵒᵖ x T (T z) :=
  let : NormedAddCommGroup E := normedAddCommGroupOfCStarModule Aᵐᵒᵖ E
  let : NormedAddCommGroup F := normedAddCommGroupOfCStarModule Aᵐᵒᵖ F
  let : CompleteSpace E := hx.completeSpace
  polarModulusAux_polarModulusAux_apply hx T z

/-- Uniqueness of the positive self-adjoint modulus: any map `P : E → E` that is symmetric for
`⟪·, ·⟫_{Aᵐᵒᵖ}`, positive (`0 ≤ ⟪z, P z⟫_{Aᵐᵒᵖ}`), and satisfies `⟪P y, P z⟫ = ⟪T y, T z⟫`
agrees pointwise with `hx.polarModulus T`. -/
theorem _root_.CStarModule.IsParsevalFrame.eq_polarModulus_of_inner_eq {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (P : E → E)
    (hP_sa : ∀ y z : E, inner Aᵐᵒᵖ (P y) z = inner Aᵐᵒᵖ y (P z))
    (hP_nonneg : ∀ z : E, 0 ≤ inner Aᵐᵒᵖ z (P z))
    (hP_inner : ∀ y z : E, inner Aᵐᵒᵖ (P y) (P z) = inner Aᵐᵒᵖ (T y) (T z)) (z : E) :
    P z = hx.polarModulus T z :=
  let : NormedAddCommGroup E := normedAddCommGroupOfCStarModule Aᵐᵒᵖ E
  let : NormedAddCommGroup F := normedAddCommGroupOfCStarModule Aᵐᵒᵖ F
  let : CompleteSpace E := hx.completeSpace
  polarModulusAux_eq_of_inner_eq hx T P hP_sa hP_nonneg hP_inner z

/-- A positive self-adjoint `Aᵐᵒᵖ`-linear endomorphism `P : E →ₗ[Aᵐᵒᵖ] E` satisfying
`P ∘ₗ P = (frameAdjoint Aᵐᵒᵖ x T).comp T.toLinearMap` equals `(hx.polarModulus T).toLinearMap`. -/
theorem _root_.CStarModule.IsParsevalFrame.eq_polarModulus_toLinearMap {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (P : E →ₗ[Aᵐᵒᵖ] E)
    (hP_sa : LinearMap.IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip
      (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip P P)
    (hP_nonneg : ∀ z : E, 0 ≤ inner Aᵐᵒᵖ z (P z))
    (hP_sq : P.comp P = (frameAdjoint Aᵐᵒᵖ x T).comp T.toLinearMap) :
    P = (hx.polarModulus T).toLinearMap := by
  refine LinearMap.ext fun z ↦ hx.eq_polarModulus_of_inner_eq T P
    (isAdjointPair_inner_iff.mp hP_sa) hP_nonneg (fun u v ↦ ?_) z
  rw [(isAdjointPair_inner_iff.mp hP_sa) u (P v), ← LinearMap.comp_apply, hP_sq,
    LinearMap.comp_apply, LinearEquiv.coe_coe,
    ← (hx.isAdjointPair_frameAdjoint T).inner_eq_cstarModule]

/-- `hx.polarModulus T` is independent of the choice of finite Parseval frame `x` (even across
different finite index types). -/
theorem _root_.CStarModule.IsParsevalFrame.polarModulus_eq {κ : Type*} [Fintype κ]
    {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F)
    {y : κ → E} (hy : IsParsevalFrame Aᵐᵒᵖ y) :
    hx.polarModulus T = hy.polarModulus T :=
  LinearEquiv.ext fun z ↦ (hx.eq_polarModulus_of_inner_eq T (hy.polarModulus T)
    (hy.isAdjointPair_polarModulus T).inner_eq_cstarModule
    (hy.inner_polarModulus_right_nonneg T) (hy.inner_polarModulus_polarModulus T) z).symm

/-- When `x : ι → E` is a Parseval frame and `T : E ≃ₗ[Aᵐᵒᵖ] F` is a right `A`-linear
equivalence into a complete right Hilbert `A`-module `F`, `polarMatrix A x T` is strictly positive
in `CStarMatrix ι ι A`. -/
theorem _root_.CStarModule.IsParsevalFrame.isStrictlyPositive_polarMatrix [DecidableEq ι]
    {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) :
    IsStrictlyPositive (polarMatrix A x T) := by
  have : CompleteSpace E := hx.completeSpace
  let : NormedAddCommGroup E := normedAddCommGroupOfCStarModule Aᵐᵒᵖ E
  let : NormedAddCommGroup F := normedAddCommGroupOfCStarModule Aᵐᵒᵖ F
  set p := CStarMatrix.gram A x with hp_def
  let e := fun j : ι ↦ (WithCStarModule.equiv Aᵐᵒᵖ (ι → A)).symm (Pi.single j (1 : A))
  let y : ι → C⋆ᵐᵒᵈ(Aᵐᵒᵖ, F × C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :=
    fun i ↦ (WithCStarModule.equiv Aᵐᵒᵖ _).symm (T (x i), mulVecCLM (1 - p) (e i))
  have hgram : polarMatrix A x T = CStarMatrix.gram A y := by
    ext i j
    rw [polarMatrix_apply, ← hp_def, CStarMatrix.gram_apply, WithCStarModule.prod_inner, unop_add,
      WithCStarModule.equiv_symm_fst, WithCStarModule.equiv_symm_fst,
      WithCStarModule.equiv_symm_snd, WithCStarModule.equiv_symm_snd,
      ← CStarMatrix.gram_apply (A := A) (x := fun k ↦ mulVecCLM (1 - p) (e k)),
      (CStarMatrix.isStarProjection_gram hx).one_sub.gram_mulVecCLM_single_one]
  rw [hgram]
  let T_inv := equivSymmCLM hx T
  have hC : (0 : ℝ) < 2 * (1 + ‖T_inv‖ ^ 2) := by positivity
  refine (isStrictlyPositive_algebraMap (inv_pos.mpr hC)).of_le <|
    (CStarMatrix.algebraMap_le_gram_iff y).mpr fun w ↦ ?_
  rw [inv_smul_le_iff_of_pos hC]
  let z : E := ∑ i, op (w i) • x i
  have hw_fst : (∑ i, op (w i) • y i).fst = T z := by
    have hπ : ∀ u : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, F × C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)), u.fst =
        LinearMap.fst Aᵐᵒᵖ _ _ ((WithCStarModule.linearEquiv Aᵐᵒᵖ Aᵐᵒᵖ _).toLinearMap u) :=
      fun _ ↦ rfl
    rw [hπ, map_sum, map_sum]
    simp [y, z]
  have hw_snd : (∑ i, op (w i) • y i).snd = mulVecCLM (1 - p) w := by
    have hπ : ∀ u : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, F × C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)), u.snd =
        LinearMap.snd Aᵐᵒᵖ _ _ ((WithCStarModule.linearEquiv Aᵐᵒᵖ Aᵐᵒᵖ _).toLinearMap u) :=
      fun _ ↦ rfl
    rw [hπ, map_sum, map_sum]
    calc ∑ i, LinearMap.snd Aᵐᵒᵖ _ _
          ((WithCStarModule.linearEquiv Aᵐᵒᵖ Aᵐᵒᵖ _) (op (w i) • y i))
        = ∑ i, op (w i) • mulVecLinearMap (1 - p) (e i) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          simp [y, ← CStarMatrix.coe_mulVecLinearMap]
      _ = mulVecLinearMap (1 - p) (∑ i, op (w i) • e i) := by
          simp_rw [map_sum, map_smul]
      _ = mulVecCLM (1 - p) w := by
          rw [WithCStarModule.sum_op_smul_single_one, CStarMatrix.coe_mulVecLinearMap]
  rw [WithCStarModule.prod_inner, hw_fst, hw_snd, unop_add]
  have hp_gram : unop (inner Aᵐᵒᵖ (mulVecCLM p w) (mulVecCLM p w)) = unop (inner Aᵐᵒᵖ z z) := by
    have hp_star := (CStarMatrix.isAdjointPair_mulVecCLM_star p).inner_eq_cstarModule w
      (mulVecCLM p w)
    rw [(CStarMatrix.isStarProjection_gram hx).isSelfAdjoint.star_eq,
      CStarMatrix.mulVecCLM_mulVecCLM, (CStarMatrix.isStarProjection_gram hx).isIdempotentElem.eq]
      at hp_star
    rw [congrArg unop hp_star]
    simpa [WithCStarModule.pi_inner, Finset.unop_sum, CStarMatrix.mulVecCLM_apply_apply,
      Finset.mul_sum, mul_assoc, z] using
      CStarMatrix.sum_star_mul_gram_mul x (WithCStarModule.equiv Aᵐᵒᵖ (ι → A) w)
        (WithCStarModule.equiv Aᵐᵒᵖ (ι → A) w)
  have hT_le : unop (inner Aᵐᵒᵖ z z) ≤ ‖T_inv‖ ^ 2 • unop (inner Aᵐᵒᵖ (T z) (T z)) := by
    simpa only [unop_smul] using unop_le_unop.mpr (inner_le_norm_sq_smul_equivSymmCLM hx T z)
  have hw_split : unop (inner Aᵐᵒᵖ w w) ≤
      (2 : ℝ) • (‖T_inv‖ ^ 2 • unop (inner Aᵐᵒᵖ (T z) (T z)) +
        unop (inner Aᵐᵒᵖ (mulVecCLM (1 - p) w) (mulVecCLM (1 - p) w))) := by
    have hadd := unop_inner_add_add_self_le (A := A) (mulVecCLM p w) (mulVecCLM (1 - p) w)
    have hsum : mulVecCLM p w + mulVecCLM (1 - p) w = w := by
      rw [← CStarMatrix.coe_mulVecLinearMap, ← CStarMatrix.coe_mulVecLinearMap,
        ← LinearMap.add_apply, ← map_add, add_sub_cancel, CStarMatrix.mulVecLinearMap_one,
        LinearMap.id_apply]
    rw [hsum, hp_gram] at hadd
    exact hadd.trans ((nsmul_le_nsmul_right
      (add_le_add hT_le (le_refl _)) 2).trans_eq (by simp only [two_smul]))
  set u := unop (inner Aᵐᵒᵖ (T z) (T z))
  set v := unop (inner Aᵐᵒᵖ (mulVecCLM (1 - p) w) (mulVecCLM (1 - p) w))
  have hu : 0 ≤ u := unop_nonneg.mpr CStarModule.inner_self_nonneg
  have hv : 0 ≤ v :=
    unop_nonneg.mpr (CStarModule.inner_self_nonneg (A := Aᵐᵒᵖ) (E := C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)))
  have hCu : ‖T_inv‖ ^ 2 • u + v ≤ (1 + ‖T_inv‖ ^ 2) • (u + v) :=
    (add_le_add (le_add_of_nonneg_left hu)
      (le_add_of_nonneg_right (smul_nonneg (sq_nonneg _) hv))).trans_eq
      (by rw [add_add_add_comm, add_smul, one_smul, smul_add])
  exact hw_split.trans
    ((smul_le_smul_of_nonneg_left hCu zero_le_two).trans_eq (mul_smul _ _ _).symm)

theorem _root_.CStarModule.IsParsevalFrame.isUnit_sqrt_polarMatrix [DecidableEq ι] {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) : IsUnit (CFC.sqrt (polarMatrix A x T)) :=
  have : ContinuousFunctionalCalculus ℝ (CStarMatrix ι ι A) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  (hx.isStrictlyPositive_polarMatrix T).isUnit_cfcSqrt _

private noncomputable def matOp {x : ι → E} (M : CStarMatrix ι ι A) :
    E →ₗ[Aᵐᵒᵖ] E where
  toFun z := ∑ i, (∑ j, inner Aᵐᵒᵖ (x j) z * op (M i j)) • x i
  map_add' y z := by
    simp_rw [_root_.CStarModule.inner_add_right, add_mul, Finset.sum_add_distrib, add_smul,
      Finset.sum_add_distrib]
  map_smul' a z := by
    simp only [RingHom.id_apply, inner_op_smul_right, mul_assoc, ← Finset.mul_sum, mul_smul,
      ← Finset.smul_sum]

omit [StarOrderedRing A] in
private theorem inner_matOp_eq_sum_star {x : ι → E} (M : CStarMatrix ι ι A)
    (y z : E) :
    unop (inner Aᵐᵒᵖ y (matOp (x := x) M z)) =
      ∑ i, ∑ j, star (unop (inner Aᵐᵒᵖ (x i) y)) * M i j * unop (inner Aᵐᵒᵖ (x j) z) := by
  simp only [matOp, LinearMap.coe_mk, AddHom.coe_mk, TauCeti.CStarModule.inner_sum_right',
    Finset.unop_sum, inner_op_smul_right, unop_mul, unop_op, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by
    rw [← _root_.CStarModule.star_inner (x i) y, unop_star, mul_assoc]

omit [StarOrderedRing A] in
private theorem matOp_comp_matOp {x : ι → E} (M N : CStarMatrix ι ι A) :
    (matOp (x := x) M).comp (matOp (x := x) N) =
      matOp (x := x) (M * CStarMatrix.gram A x * N) := by
  ext z
  simp only [LinearMap.comp_apply, matOp, LinearMap.coe_mk, AddHom.coe_mk,
    TauCeti.CStarModule.inner_sum_right', inner_op_smul_right, Finset.sum_mul, Finset.op_sum,
    op_mul, CStarMatrix.mul_apply, mul_assoc]
  refine Finset.sum_congr rfl fun i _ ↦ congrArg (· • x i) ?_
  rw [Finset.sum_comm]
  conv_lhs => enter [2, k]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, CStarMatrix.gram_apply, op_unop]

omit [StarOrderedRing A] in
private theorem matOp_gram_apply {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (z : E) : matOp (x := x) (CStarMatrix.gram A x) z = z := by
  have hinner (i : ι) : ∑ j, inner Aᵐᵒᵖ (x j) z * op (CStarMatrix.gram A x i j) =
      inner Aᵐᵒᵖ (x i) z := by
    have hz := congrArg (inner Aᵐᵒᵖ (x i)) (hx.sum_inner_smul z)
    rw [TauCeti.CStarModule.inner_sum_right'] at hz
    simpa [CStarMatrix.gram_apply, mul_comm] using hz
  simp only [matOp, LinearMap.coe_mk, AddHom.coe_mk, hinner]
  exact hx.sum_inner_smul z

/-- Explicit frame-matrix formula for `hx.polarModulus T`. -/
theorem _root_.CStarModule.IsParsevalFrame.polarModulus_apply [DecidableEq ι] {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) :
    hx.polarModulus T z =
      ∑ i, (∑ j, inner Aᵐᵒᵖ (x j) z * op (CFC.sqrt (polarMatrix A x T) i j)) • x i := by
  set S := CFC.sqrt (polarMatrix A x T)
  have hS_sa : IsSelfAdjoint S := (CFC.sqrt_nonneg _).isSelfAdjoint
  have hP_sa : LinearMap.IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip
      (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip (matOp (x := x) S) (matOp (x := x) S) := by
    rw [isAdjointPair_inner_iff]; intro u v
    apply unop_injective
    have h1 : unop (inner Aᵐᵒᵖ (matOp (x := x) S u) v) =
        star (unop (inner Aᵐᵒᵖ v (matOp (x := x) S u))) := by simp [← unop_star]
    rw [h1, inner_matOp_eq_sum_star, inner_matOp_eq_sum_star, star_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [star_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hSji : star (S j i) = S i j := by
      simpa [CStarMatrix.star_apply] using congrFun (congrFun hS_sa.star_eq i) j
    simp [star_mul, hSji, mul_assoc]
  have hP_nonneg : ∀ w : E, 0 ≤ inner Aᵐᵒᵖ w (matOp (x := x) S w) := by
    intro w
    rw [← unop_nonneg, inner_matOp_eq_sum_star]
    set R := CFC.sqrt S
    have hRR : S = star R * R := by
      rw [(CFC.sqrt_nonneg S).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self S (CFC.sqrt_nonneg _)]
    have hsum : ∑ i, ∑ j, star (unop (inner Aᵐᵒᵖ (x i) w)) * S i j *
          unop (inner Aᵐᵒᵖ (x j) w) =
        ∑ k, star (∑ i, R k i * unop (inner Aᵐᵒᵖ (x i) w)) *
          (∑ j, R k j * unop (inner Aᵐᵒᵖ (x j) w)) := by
      simp_rw [hRR, CStarMatrix.mul_apply, CStarMatrix.star_apply, Finset.mul_sum, Finset.sum_mul,
        star_sum, star_mul, mul_assoc]
      conv_lhs => enter [2, i]; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      simp_rw [Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm
    rw [hsum]
    exact Finset.sum_nonneg fun _ _ ↦ star_mul_self_nonneg _
  have hP_sq : (matOp (x := x) S).comp (matOp (x := x) S) =
      (frameAdjoint Aᵐᵒᵖ x T).comp T.toLinearMap := by
    have hSpS : S * CStarMatrix.gram A x * S = CStarMatrix.gram A (fun i ↦ T (x i)) := by
      have hcomm : Commute S (CStarMatrix.gram A x) :=
        (hx.commute_polarMatrix_gram T).cfcₙ_nnreal NNReal.sqrt
      rw [mul_assoc, ← hcomm.eq, ← mul_assoc, CFC.sqrt_mul_sqrt_self _ (hx.polarMatrix_nonneg T),
        hx.polarMatrix_mul_gram T]
    rw [matOp_comp_matOp, hSpS]
    ext w
    refine ext_inner_left (A := Aᵐᵒᵖ) fun y ↦ ?_
    apply unop_injective
    rw [inner_matOp_eq_sum_star, LinearMap.comp_apply, LinearEquiv.coe_coe,
      ← (hx.isAdjointPair_frameAdjoint T).inner_eq_cstarModule,
      CStarMatrix.sum_star_mul_gram_mul]
    have hT (u : E) : ∑ i, op (unop (inner Aᵐᵒᵖ (x i) u)) • T (x i) = T u := by
      conv_rhs => rw [← hx.sum_inner_smul u, map_sum]
      simp
    rw [hT y, hT w]
  exact (LinearMap.congr_fun (hx.eq_polarModulus_toLinearMap T (matOp (x := x) S)
    hP_sa hP_nonneg hP_sq) z).symm

theorem _root_.CStarModule.IsParsevalFrame.polarModulus_symm_apply [DecidableEq ι] {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) :
    (hx.polarModulus T).symm z =
      ∑ i, (∑ j, inner Aᵐᵒᵖ (x j) z *
        op (Ring.inverse (CFC.sqrt (polarMatrix A x T)) i j)) • x i := by
  set S := CFC.sqrt (polarMatrix A x T)
  refine (hx.polarModulus T).symm_apply_eq.mpr ?_
  change z = (hx.polarModulus T) (matOp (x := x) (Ring.inverse S) z)
  have hL : (hx.polarModulus T) (matOp (x := x) (Ring.inverse S) z) =
      (matOp (x := x) S) (matOp (x := x) (Ring.inverse S) z) :=
    hx.polarModulus_apply T _
  rw [hL, ← LinearMap.comp_apply, matOp_comp_matOp]
  have hcomm : Commute S (CStarMatrix.gram A x) :=
    (hx.commute_polarMatrix_gram T).cfcₙ_nnreal NNReal.sqrt
  rw [hcomm.eq, mul_assoc,
    Ring.mul_inverse_cancel S (hx.isUnit_sqrt_polarMatrix T), mul_one]
  exact (matOp_gram_apply hx z).symm

/-- Polar unitary `U = T ∘ |T|⁻¹ : E ≃ₗᵢ[Aᵐᵒᵖ] F` of a right `A`-linear equivalence
`T : E ≃ₗ[Aᵐᵒᵖ] F` into a complete right Hilbert `A`-module `F`. -/
noncomputable def _root_.CStarModule.IsParsevalFrame.polarUnitary {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) : E ≃ₗᵢ[Aᵐᵒᵖ] F :=
  ((hx.polarModulus T).symm.trans T).isometryOfInnerCStarModule fun z ↦ by
    simp only [LinearEquiv.trans_apply]
    rw [← hx.inner_polarModulus_polarModulus T, LinearEquiv.apply_symm_apply]

theorem _root_.CStarModule.IsParsevalFrame.polarUnitary_apply {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) :
    hx.polarUnitary T z = T ((hx.polarModulus T).symm z) := by
  simp [_root_.CStarModule.IsParsevalFrame.polarUnitary]

theorem _root_.CStarModule.IsParsevalFrame.polarUnitary_symm_apply {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (w : F) :
    (hx.polarUnitary T).symm w = hx.polarModulus T (T.symm w) := by
  simp [_root_.CStarModule.IsParsevalFrame.polarUnitary]

/-- The polar decomposition factorization `T = U ∘ |T|`: applying `hx.polarUnitary T` after
`hx.polarModulus T` recovers `T`. -/
@[simp] theorem _root_.CStarModule.IsParsevalFrame.polarUnitary_polarModulus_apply {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) :
    hx.polarUnitary T (hx.polarModulus T z) = T z := by
  simp [_root_.CStarModule.IsParsevalFrame.polarUnitary]

@[simp] theorem _root_.CStarModule.IsParsevalFrame.polarUnitary_symm_map {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) :
    (hx.polarUnitary T).symm (T z) = hx.polarModulus T z := by
  rw [hx.polarUnitary_symm_apply, T.symm_apply_apply]

/-- `hx.polarUnitary T` is independent of the choice of finite Parseval frame `x` (even across
different finite index types). -/
theorem _root_.CStarModule.IsParsevalFrame.polarUnitary_eq {κ : Type*} [Fintype κ]
    {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F)
    {y : κ → E} (hy : IsParsevalFrame Aᵐᵒᵖ y) :
    hx.polarUnitary T = hy.polarUnitary T := by
  ext z
  rw [hx.polarUnitary_apply, hy.polarUnitary_apply, hx.polarModulus_eq T hy]

end Polar

end TauCeti.CStarModule
