/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.Adjointable.Order
public import TauCeti.Analysis.CStarAlgebra.Module.Frame.Operators

/-!
# Polar decomposition for invertible adjointable maps and finite Parseval frames

Over a (possibly non-unital) C⋆-algebra `A`, any adjointable operator `T : AdjointableMap A E F`
on a complete Hilbert C⋆-module `E` that admits a bounded complex-linear two-sided inverse
`T_inv : F →L[ℂ] E` has a strictly positive square `T* ∘ T`
(`TauCeti.AdjointableMap.isStrictlyPositive_adjoint_comp_self_of_leftInverse`), hence an invertible
modulus `|T|` (`TauCeti.AdjointableMap.isUnit_abs_of_leftInverse`), and a unitary polar factor
`U = T ∘ |T|⁻¹ : CStarModuleUnitary A E F` (`TauCeti.AdjointableMap.polarUnitary`) satisfying
`U (|T| x) = T x` (`TauCeti.AdjointableMap.polarUnitary_apply_abs`).

Over a unital C⋆-algebra `A`, for a right `A`-linear equivalence `T : E ≃ₗ[Aᵐᵒᵖ] F` out of a right
Hilbert `A`-module `E` equipped with a finite Parseval frame `x : ι → E` into a complete right
Hilbert `A`-module `F`:

* By `hx.completeSpace`, `E` is complete, and `T` is adjointable with explicit adjoint
  `frameAdjoint Aᵐᵒᵖ x T`.
* Specializing the general adjointable polar construction gives an invertible positive modulus
  `|T| : E ≃ₗ[Aᵐᵒᵖ] E` (`CStarModule.IsParsevalFrame.polarModulus`) and a unitary isomorphism
  `U : E ≃ₗᵢ[Aᵐᵒᵖ] F` (`CStarModule.IsParsevalFrame.polarUnitary`) satisfying `T = U ∘ |T|`
  (`CStarModule.IsParsevalFrame.polarUnitary_polarModulus_apply`), unique and independent of `x`
  (`CStarModule.IsParsevalFrame.eq_polarModulus_of_inner_eq`,
  `CStarModule.IsParsevalFrame.eq_polarModulus_toLinearMap`,
  `CStarModule.IsParsevalFrame.polarModulus_eq`, `CStarModule.IsParsevalFrame.polarUnitary_eq`).
* In frame coordinates, `|T|` and `|T|⁻¹` are represented by `CFC.sqrt (polarMatrix A x T)` and
  its matrix inverse (`CStarModule.IsParsevalFrame.polarModulus_apply`,
  `CStarModule.IsParsevalFrame.polarModulus_symm_apply`).

## Main declarations

* `TauCeti.AdjointableMap.isStrictlyPositive_adjoint_comp_self_of_leftInverse`,
  `TauCeti.AdjointableMap.isUnit_abs_of_leftInverse`, `TauCeti.AdjointableMap.polarUnitary`,
  `TauCeti.AdjointableMap.polarUnitary_apply_abs`, `TauCeti.AdjointableMap.eq_abs_of_inner_eq`
* `TauCeti.CStarModule.polarMatrix`
* `CStarModule.IsParsevalFrame.polarModulus`, `CStarModule.IsParsevalFrame.polarUnitary`,
  `CStarModule.IsParsevalFrame.polarUnitary_polarModulus_apply`
* `CStarModule.IsParsevalFrame.eq_polarModulus_of_inner_eq`,
  `CStarModule.IsParsevalFrame.eq_polarModulus_toLinearMap`,
  `CStarModule.IsParsevalFrame.polarModulus_eq`, `CStarModule.IsParsevalFrame.polarUnitary_eq`
* `CStarModule.IsParsevalFrame.isStrictlyPositive_polarMatrix`,
  `CStarModule.IsParsevalFrame.isUnit_sqrt_polarMatrix`,
  `CStarModule.IsParsevalFrame.polarModulus_apply`,
  `CStarModule.IsParsevalFrame.polarModulus_symm_apply`

## References

* M. Frank and D. R. Larson, *Frames in Hilbert C⋆-modules and C⋆-algebras*, J. Operator Theory 48
  (2002), 273–314.
* E. C. Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapters 3 and 4.
* I. Raeburn and D. P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*, Chapter 2.
-/

public section

open MulOpposite Matrix CStarModule TauCeti
open CStarMatrix (mulVecCLM mulVecLinearMap)
open scoped WithCStarModule

/-! ### Polar decomposition of invertible adjointable maps -/

namespace TauCeti.AdjointableMap

section Polar

variable {A E F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]

/-- Over any (possibly non-unital) C⋆-algebra `A`, if `T : AdjointableMap A E F` has a bounded
complex-linear two-sided inverse `T_inv : F →L[ℂ] E`, then `T* ∘ T` is strictly positive in
`AdjointableMap A E E`. -/
theorem isStrictlyPositive_adjoint_comp_self_of_leftInverse (T : AdjointableMap A E F)
    {T_inv : F →L[ℂ] E} (hleft : Function.LeftInverse T_inv T)
    (hright : Function.RightInverse T_inv T) :
    IsStrictlyPositive (T.adjoint.comp T) := by
  have hpos : (0 : ℝ) < 1 + ‖T_inv‖ ^ 2 := by positivity
  refine (isStrictlyPositive_algebraMap (inv_pos.mpr hpos)).of_le ?_
  rw [AdjointableMap.le_iff_forall_inner_le]
  intro z
  rw [AdjointableMap.algebraMap_apply, AdjointableMap.comp_apply, T.adjoint_inner_right]
  have hTinv_smul (a : A) (y : F) : T_inv (a • y) = a • T_inv y := by
    calc T_inv (a • y) = T_inv (a • T (T_inv y)) := by rw [hright y]
      _ = T_inv (T (a • T_inv y)) := by rw [T.map_smul_coeff]
      _ = a • T_inv y := hleft _
  have hpas : inner A z z ≤ ‖T_inv‖ ^ 2 • inner A (T z) (T z) := by
    simpa [hleft z] using ContinuousLinearMap.inner_map_map_le_norm_sq_smul T_inv hTinv_smul (T z)
  rw [← Complex.coe_smul, inner_smul_right_complex, Complex.coe_smul]
  calc (1 + ‖T_inv‖ ^ 2)⁻¹ • inner A z z
      ≤ (1 + ‖T_inv‖ ^ 2)⁻¹ • ((1 + ‖T_inv‖ ^ 2) • inner A (T z) (T z)) := by
        refine smul_le_smul_of_nonneg_left (hpas.trans ?_) (by positivity)
        exact smul_le_smul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) inner_self_nonneg
    _ = inner A (T z) (T z) := by rw [smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]

/-- If `T : AdjointableMap A E F` has a bounded complex-linear two-sided inverse `T_inv`, then its
modulus `T.abs = √(T* ∘ T)` is a unit in `AdjointableMap A E E`. -/
theorem isUnit_abs_of_leftInverse (T : AdjointableMap A E F) {T_inv : F →L[ℂ] E}
    (hleft : Function.LeftInverse T_inv T) (hright : Function.RightInverse T_inv T) :
    IsUnit T.abs := by
  have hu_sq : IsUnit (T.abs * T.abs) := by
    rw [AdjointableMap.abs_mul_abs]
    exact (IsStrictlyPositive.iff_of_unital.mp
      (isStrictlyPositive_adjoint_comp_self_of_leftInverse T hleft hright)).2
  exact ((Commute.refl _).isUnit_mul_iff.mp hu_sq).1

private noncomputable def invAbs (T : AdjointableMap A E F) {T_inv : F →L[ℂ] E}
    (hleft : Function.LeftInverse T_inv T) (hright : Function.RightInverse T_inv T) :
    AdjointableMap A E E :=
  ((T.isUnit_abs_of_leftInverse hleft hright).unit⁻¹ : (AdjointableMap A E E)ˣ)

/-- Unitary polar factor `U = T ∘ |T|⁻¹ : CStarModuleUnitary A E F` of an adjointable operator
`T : AdjointableMap A E F` with a bounded complex-linear two-sided inverse `T_inv`. -/
noncomputable def polarUnitary (T : AdjointableMap A E F) {T_inv : F →L[ℂ] E}
    (hleft : Function.LeftInverse T_inv T) (hright : Function.RightInverse T_inv T) :
    CStarModuleUnitary A E F :=
  CStarModuleUnitary.ofSurjective (fun x ↦ T (T.invAbs hleft hright x))
    (fun y ↦ ⟨T.abs (T_inv y), by
      have hinv_mul : T.invAbs hleft hright * T.abs = 1 :=
        (T.isUnit_abs_of_leftInverse hleft hright).val_inv_mul
      dsimp only
      rw [← AdjointableMap.comp_apply (T.invAbs hleft hright) T.abs,
        ← AdjointableMap.mul_def, hinv_mul, AdjointableMap.one_def, AdjointableMap.id_apply,
        hright y]⟩)
    (fun x y ↦ by
      have hmul : T.abs * T.invAbs hleft hright = 1 :=
        (T.isUnit_abs_of_leftInverse hleft hright).mul_val_inv
      rw [← T.inner_abs_abs, ← AdjointableMap.comp_apply T.abs (T.invAbs hleft hright),
        ← AdjointableMap.comp_apply T.abs (T.invAbs hleft hright), ← AdjointableMap.mul_def, hmul,
        AdjointableMap.one_def]
      simp_rw [AdjointableMap.id_apply])

/-- The polar factorization `U (|T| x) = T x` for `polarUnitary`. -/
@[simp]
theorem polarUnitary_apply_abs (T : AdjointableMap A E F) {T_inv : F →L[ℂ] E}
    (hleft : Function.LeftInverse T_inv T) (hright : Function.RightInverse T_inv T) (x : E) :
    T.polarUnitary hleft hright (T.abs x) = T x := by
  have hinv_mul : T.invAbs hleft hright * T.abs = 1 :=
    (T.isUnit_abs_of_leftInverse hleft hright).val_inv_mul
  calc T.polarUnitary hleft hright (T.abs x)
      = T (T.invAbs hleft hright (T.abs x)) := by
          rw [polarUnitary]
          exact CStarModuleUnitary.ofSurjective_apply _ _ _ (T.abs x)
    _ = T x := by
          rw [← AdjointableMap.comp_apply (T.invAbs hleft hright) T.abs,
            ← AdjointableMap.mul_def, hinv_mul, AdjointableMap.one_def, AdjointableMap.id_apply]

/-- Applying the inverse polar unitary to `T x` recovers `|T| x`. -/
@[simp]
theorem polarUnitary_symm_map (T : AdjointableMap A E F) {T_inv : F →L[ℂ] E}
    (hleft : Function.LeftInverse T_inv T) (hright : Function.RightInverse T_inv T) (x : E) :
    (T.polarUnitary hleft hright).symm (T x) = T.abs x :=
  (T.polarUnitary hleft hright).symm_apply_eq.mpr (T.polarUnitary_apply_abs hleft hright x).symm

/-- Applying the inverse polar unitary to `y : F` gives `|T| (T_inv y)`. -/
theorem polarUnitary_symm_apply (T : AdjointableMap A E F) {T_inv : F →L[ℂ] E}
    (hleft : Function.LeftInverse T_inv T) (hright : Function.RightInverse T_inv T) (y : F) :
    (T.polarUnitary hleft hright).symm y = T.abs (T_inv y) := by
  conv_lhs => rw [← hright y]
  exact T.polarUnitary_symm_map hleft hright (T_inv y)

/-- Uniqueness of the positive self-adjoint modulus `T.abs`: any map `P : E → E` that is
symmetric for `⟪·, ·⟫_A`, positive (`0 ≤ ⟪z, P z⟫_A`), and satisfies `⟪P y, P z⟫_A = ⟪T y, T z⟫_A`
agrees pointwise with `T.abs`. -/
theorem eq_abs_of_inner_eq (T : AdjointableMap A E F) (P : E → E)
    (hP_sa : ∀ y z : E, inner A (P y) z = inner A y (P z))
    (hP_nonneg : ∀ z : E, 0 ≤ inner A z (P z))
    (hP_inner : ∀ y z : E, inner A (P y) (P z) = inner A (T y) (T z)) (z : E) :
    P z = T.abs z := by
  let P_op : AdjointableMap A E E := AdjointableMap.ofAdjointPair P P hP_sa
  have hP_pos : 0 ≤ P_op := AdjointableMap.nonneg_iff_forall_inner_nonneg.mpr fun w ↦ by
    simpa [P_op] using hP_nonneg w
  have hP_sq : P_op.adjoint.comp P_op = T.adjoint.comp T := by
    refine AdjointableMap.ext fun v ↦ CStarModule.ext_inner_left (A := A) fun u ↦ ?_
    have h1 : inner A (P_op u) (P_op v) = inner A (T u) (T v) := by
      simpa [P_op] using hP_inner u v
    rw [AdjointableMap.comp_apply, P_op.adjoint_inner_right, h1, ← T.adjoint_inner_right,
      ← AdjointableMap.comp_apply]
  have hPM : P_op = T.abs := calc
    P_op = P_op.abs := (AdjointableMap.abs_of_nonneg hP_pos).symm
    _ = CFC.sqrt (P_op.abs * P_op.abs) := (CFC.sqrt_mul_self _ (AdjointableMap.abs_nonneg _)).symm
    _ = CFC.sqrt (T.abs * T.abs) := by
        rw [AdjointableMap.abs_mul_abs, hP_sq, ← AdjointableMap.abs_mul_abs]
    _ = T.abs := CFC.sqrt_mul_self _ (AdjointableMap.abs_nonneg _)
  simpa [P_op] using congrArg (fun (f : AdjointableMap A E E) ↦ f z) hPM

end Polar

end TauCeti.AdjointableMap

/-! ### Polar decomposition for right Hilbert modules with a finite Parseval frame -/

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

private theorem equivSymmCLM_leftInverse {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (T : E ≃ₗ[Aᵐᵒᵖ] F) : Function.LeftInverse (equivSymmCLM hx T) (equivAdjointableMap hx T) :=
  fun z ↦ by simp [equivSymmCLM, equivAdjointableMap]

private theorem equivSymmCLM_rightInverse {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (T : E ≃ₗ[Aᵐᵒᵖ] F) : Function.RightInverse (equivSymmCLM hx T) (equivAdjointableMap hx T) :=
  fun w ↦ by simp [equivSymmCLM, equivAdjointableMap]

private theorem inner_le_norm_sq_smul_equivSymmCLM {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) :
    inner Aᵐᵒᵖ z z ≤ ‖equivSymmCLM hx T‖ ^ 2 • inner Aᵐᵒᵖ (T z) (T z) := by
  have h := ContinuousLinearMap.inner_map_map_le_norm_sq_smul (equivSymmCLM hx T)
    (fun a y ↦ (T.symm.map_smul a y : _)) (T z)
  simpa [equivSymmCLM] using h

private noncomputable def polarModulusAux {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (T : E ≃ₗ[Aᵐᵒᵖ] F) : E ≃ₗ[Aᵐᵒᵖ] E :=
  let hunit := (equivAdjointableMap hx T).isUnit_abs_of_leftInverse
    (equivSymmCLM_leftInverse hx T) (equivSymmCLM_rightInverse hx T)
  LinearEquiv.ofBijective (equivAdjointableMap hx T).abs.toCoeffLinearMap
    ((Module.End.isUnit_iff _).mp (by simpa using hunit.map AdjointableMap.toCoeffLinearMapRingHom))

private theorem polarModulusAux_apply {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x)
    (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) :
    polarModulusAux hx T z = (equivAdjointableMap hx T).abs z := by
  simp [polarModulusAux]

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
  isAdjointPair_inner_iff.mpr fun y z ↦ by
    change inner Aᵐᵒᵖ (polarModulusAux hx T y) z = inner Aᵐᵒᵖ y (polarModulusAux hx T z)
    rw [polarModulusAux_apply, polarModulusAux_apply]
    have hM := (equivAdjointableMap hx T).abs.adjoint_inner_right y z
    rw [AdjointableMap.isSelfAdjoint_iff_adjoint_eq.mp (AdjointableMap.isSelfAdjoint_abs _)] at hM
    exact hM.symm

/-- `hx.polarModulus T` is positive: `0 ≤ ⟨z, |T| z⟩_A` for all `z : E`. -/
theorem _root_.CStarModule.IsParsevalFrame.inner_polarModulus_right_nonneg {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) :
    0 ≤ inner Aᵐᵒᵖ z (hx.polarModulus T z) :=
  let : NormedAddCommGroup E := normedAddCommGroupOfCStarModule Aᵐᵒᵖ E
  let : NormedAddCommGroup F := normedAddCommGroupOfCStarModule Aᵐᵒᵖ F
  let : CompleteSpace E := hx.completeSpace
  by
    change 0 ≤ inner Aᵐᵒᵖ z (polarModulusAux hx T z)
    rw [polarModulusAux_apply]
    exact AdjointableMap.nonneg_iff_forall_inner_nonneg.mp (AdjointableMap.abs_nonneg _) z

/-- `hx.polarModulus T` has the same Gram inner products as `T`:
`⟨|T| y, |T| z⟩_A = ⟨T y, T z⟩_A`. -/
@[simp]
theorem _root_.CStarModule.IsParsevalFrame.inner_polarModulus_polarModulus {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (y z : E) :
    inner Aᵐᵒᵖ (hx.polarModulus T y) (hx.polarModulus T z) = inner Aᵐᵒᵖ (T y) (T z) :=
  let : NormedAddCommGroup E := normedAddCommGroupOfCStarModule Aᵐᵒᵖ E
  let : NormedAddCommGroup F := normedAddCommGroupOfCStarModule Aᵐᵒᵖ F
  let : CompleteSpace E := hx.completeSpace
  by
    change inner Aᵐᵒᵖ (polarModulusAux hx T y) (polarModulusAux hx T z) = inner Aᵐᵒᵖ (T y) (T z)
    rw [polarModulusAux_apply, polarModulusAux_apply]
    simpa [equivAdjointableMap] using AdjointableMap.inner_abs_abs (equivAdjointableMap hx T) y z

/-- The square of `hx.polarModulus T` equals `T* ∘ T`:
`|T| (|T| z) = frameAdjoint Aᵐᵒᵖ x T (T z)`. -/
theorem _root_.CStarModule.IsParsevalFrame.polarModulus_polarModulus_apply {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) :
    hx.polarModulus T (hx.polarModulus T z) = frameAdjoint Aᵐᵒᵖ x T (T z) :=
  let : NormedAddCommGroup E := normedAddCommGroupOfCStarModule Aᵐᵒᵖ E
  let : NormedAddCommGroup F := normedAddCommGroupOfCStarModule Aᵐᵒᵖ F
  let : CompleteSpace E := hx.completeSpace
  by
    change polarModulusAux hx T (polarModulusAux hx T z) = frameAdjoint Aᵐᵒᵖ x T (T z)
    rw [polarModulusAux_apply, polarModulusAux_apply, ← AdjointableMap.comp_apply,
      ← AdjointableMap.mul_def, AdjointableMap.abs_mul_abs, AdjointableMap.comp_apply]
    simp [equivAdjointableMap]

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
  ((equivAdjointableMap hx T).eq_abs_of_inner_eq P hP_sa hP_nonneg
    (fun u v ↦ by simpa [equivAdjointableMap] using hP_inner u v) z).trans
    (polarModulusAux_apply hx T z).symm

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
  have hp : IsStarProjection p := CStarMatrix.isStarProjection_gram hx
  let e := fun j : ι ↦ (WithCStarModule.equiv Aᵐᵒᵖ (ι → A)).symm (Pi.single j (1 : A))
  let y : ι → C⋆ᵐᵒᵈ(Aᵐᵒᵖ, F × C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)) :=
    fun i ↦ (WithCStarModule.equiv Aᵐᵒᵖ _).symm (T (x i), mulVecCLM (1 - p) (e i))
  have hgram : polarMatrix A x T = CStarMatrix.gram A y := by
    ext i j
    rw [polarMatrix_apply, ← hp_def, CStarMatrix.gram_apply, WithCStarModule.prod_inner, unop_add,
      WithCStarModule.equiv_symm_fst, WithCStarModule.equiv_symm_fst,
      WithCStarModule.equiv_symm_snd, WithCStarModule.equiv_symm_snd,
      ← CStarMatrix.gram_apply (A := A) (x := fun k ↦ mulVecCLM (1 - p) (e k)),
      hp.one_sub.gram_mulVecCLM_single_one]
  rw [hgram]
  let T_inv := equivSymmCLM hx T
  have hC : (0 : ℝ) < 1 + ‖T_inv‖ ^ 2 := by positivity
  refine (isStrictlyPositive_algebraMap (inv_pos.mpr hC)).of_le <|
    (CStarMatrix.algebraMap_le_gram_iff y).mpr fun w ↦ ?_
  rw [inv_smul_le_iff_of_pos hC]
  let z : E := opSynthesisLinearMap A x w
  let π₂ := _root_.WithCStarModule.sndLinearMap Aᵐᵒᵖ Aᵐᵒᵖ F C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A)
  have hw_fst : (∑ i, op (w i) • y i).fst = T z := by
    rw [← _root_.WithCStarModule.fstLinearMap_apply Aᵐᵒᵖ Aᵐᵒᵖ, map_sum]
    simp [y, z]
  have hw_snd : (∑ i, op (w i) • y i).snd = mulVecCLM (1 - p) w := by
    rw [← _root_.WithCStarModule.sndLinearMap_apply Aᵐᵒᵖ Aᵐᵒᵖ, map_sum]
    calc ∑ i, π₂ (op (w i) • y i)
        = ∑ i, op (w i) • mulVecLinearMap (1 - p) (e i) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          simp [π₂, y, ← CStarMatrix.coe_mulVecLinearMap]
      _ = mulVecLinearMap (1 - p) (∑ i, op (w i) • e i) := by simp_rw [map_sum, map_smul]
      _ = mulVecCLM (1 - p) w := by
          rw [WithCStarModule.sum_op_smul_single_one, CStarMatrix.coe_mulVecLinearMap]
  rw [WithCStarModule.prod_inner, hw_fst, hw_snd, unop_add]
  let P : AdjointableMap Aᵐᵒᵖ C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A) :=
    AdjointableMap.ofAdjointPair (mulVecCLM p) (mulVecCLM p) fun u v ↦ by
      have h := (CStarMatrix.isAdjointPair_mulVecCLM_conjTranspose p).inner_eq_cstarModule u v
      rwa [← CStarMatrix.star_eq_conjTranspose, hp.isSelfAdjoint.star_eq] at h
  have hP : IsStarProjection P :=
    { isIdempotentElem := AdjointableMap.ext fun v ↦ by
        simp [mul_apply_eq_comp, P, hp.isIdempotentElem.eq]
      isSelfAdjoint := by
        rw [IsSelfAdjoint, AdjointableMap.star_eq_adjoint]
        exact AdjointableMap.ext fun v ↦ by simp [P] }
  have hp_gram : inner Aᵐᵒᵖ (P w) (P w) = inner Aᵐᵒᵖ z z := by
    calc inner Aᵐᵒᵖ (P w) (P w)
        = inner Aᵐᵒᵖ (mulVecCLM p w) (mulVecCLM p w) := by simp [P]
      _ = inner Aᵐᵒᵖ (opAnalysisLinearMap A x z) (opAnalysisLinearMap A x z) := by
          rw [← CStarMatrix.coe_mulVecLinearMap, ← opAnalysisLinearMap_opSynthesisLinearMap]
      _ = inner Aᵐᵒᵖ z z := inner_opAnalysisLinearMap hx z z
  have h1P : (1 - P) w = mulVecCLM (1 - p) w := by
    rw [sub_apply, one_apply_eq_self, map_sub, CStarMatrix.mulVecCLM_one,
      sub_apply, ContinuousLinearMap.id_apply, AdjointableMap.ofAdjointPair_apply]
  have hw_orth : unop (inner Aᵐᵒᵖ w w) =
      unop (inner Aᵐᵒᵖ z z) + unop (inner Aᵐᵒᵖ (mulVecCLM (1 - p) w) (mulVecCLM (1 - p) w)) := by
    have h := congrArg unop (AdjointableMap.inner_eq_add_inner_one_sub_of_isStarProjection hP w w)
    rwa [hp_gram, h1P, unop_add] at h
  have hT_le : unop (inner Aᵐᵒᵖ z z) ≤ ‖T_inv‖ ^ 2 • unop (inner Aᵐᵒᵖ (T z) (T z)) := by
    simpa only [unop_smul] using unop_le_unop.mpr (inner_le_norm_sq_smul_equivSymmCLM hx T z)
  rw [hw_orth]
  exact (add_le_add hT_le le_rfl).trans
    (smul_add_le_one_add_smul (unop_nonneg.mpr (CStarModule.inner_self_nonneg (A := Aᵐᵒᵖ)))
      (unop_nonneg.mpr (CStarModule.inner_self_nonneg (A := Aᵐᵒᵖ) (E := C⋆ᵐᵒᵈ(Aᵐᵒᵖ, ι → A))))
      (sq_nonneg _))

/-- `CFC.sqrt (polarMatrix A x T)` is a unit in `CStarMatrix ι ι A`, justifying taking its
matrix inverse in the frame-coordinate formula `polarModulus_symm_apply`. -/
theorem _root_.CStarModule.IsParsevalFrame.isUnit_sqrt_polarMatrix [DecidableEq ι] {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) : IsUnit (CFC.sqrt (polarMatrix A x T)) :=
  have : ContinuousFunctionalCalculus ℝ (CStarMatrix ι ι A) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  (hx.isStrictlyPositive_polarMatrix T).isUnit_cfcSqrt _

section MatOp

variable {A ι E : Type*} [Fintype ι] [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [Module Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]

private noncomputable def matOp {x : ι → E} (M : CStarMatrix ι ι A) : E →ₗ[Aᵐᵒᵖ] E :=
  (opSynthesisLinearMap A x).comp ((mulVecLinearMap M).comp (opAnalysisLinearMap A x))

private theorem matOp_apply {x : ι → E} (M : CStarMatrix ι ι A) (z : E) :
    matOp (x := x) M z = ∑ i, (∑ j, inner Aᵐᵒᵖ (x j) z * op (M i j)) • x i := by
  simp only [matOp, LinearMap.comp_apply, opSynthesisLinearMap_apply,
    CStarMatrix.mulVecLinearMap_apply_apply, opAnalysisLinearMap_apply_apply, Finset.op_sum,
    op_mul, op_unop]

private theorem matOp_comp_matOp {x : ι → E} (M N : CStarMatrix ι ι A) :
    (matOp (x := x) M).comp (matOp (x := x) N) =
      matOp (x := x) (M * CStarMatrix.gram A x * N) := by
  ext z
  simp only [matOp, LinearMap.comp_apply, opAnalysisLinearMap_opSynthesisLinearMap,
    CStarMatrix.mulVecLinearMap_mulVecLinearMap, mul_assoc]

private theorem matOp_gram_apply {x : ι → E} (hx : IsParsevalFrame Aᵐᵒᵖ x) (z : E) :
    matOp (x := x) (CStarMatrix.gram A x) z = z := by
  dsimp only [matOp]
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ← opAnalysisLinearMap_opSynthesisLinearMap,
    opSynthesisLinearMap_opAnalysisLinearMap hx, opSynthesisLinearMap_opAnalysisLinearMap hx]

private theorem isAdjointPair_matOp {x : ι → E} (M : CStarMatrix ι ι A) :
    LinearMap.IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip
      (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip
      (matOp (x := x) M) (matOp (x := x) M.conjTranspose) :=
  ((isAdjointPair_opAnalysisLinearMap_opSynthesisLinearMap A x).comp
    (CStarMatrix.isAdjointPair_mulVecLinearMap_conjTranspose M)).comp
    (isAdjointPair_opSynthesisLinearMap_opAnalysisLinearMap A x)

private theorem inner_matOp_right_nonneg {x : ι → E} {M : CStarMatrix ι ι A} (hM : 0 ≤ M)
    (w : E) : 0 ≤ inner Aᵐᵒᵖ w (matOp (x := x) M w) := by
  rw [← unop_nonneg]
  have h1 : unop (inner Aᵐᵒᵖ w (matOp (x := x) M w)) =
      unop (inner Aᵐᵒᵖ (opAnalysisLinearMap A x w)
        (mulVecLinearMap M (opAnalysisLinearMap A x w))) :=
    congrArg unop
      ((isAdjointPair_opAnalysisLinearMap_opSynthesisLinearMap A x).inner_eq_cstarModule
        w (mulVecLinearMap M (opAnalysisLinearMap A x w))).symm
  rw [h1]
  simpa [WithCStarModule.pi_inner, Finset.unop_sum, Finset.mul_sum, mul_assoc] using
    CStarMatrix.nonneg_iff_forall_sum_nonneg.mp hM (opAnalysisLinearMap A x w)

end MatOp

/-- Explicit frame-matrix formula for `hx.polarModulus T`. -/
theorem _root_.CStarModule.IsParsevalFrame.polarModulus_apply [DecidableEq ι] {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) :
    hx.polarModulus T z =
      ∑ i, (∑ j, inner Aᵐᵒᵖ (x j) z * op (CFC.sqrt (polarMatrix A x T) i j)) • x i := by
  let : NormedAddCommGroup E := normedAddCommGroupOfCStarModule Aᵐᵒᵖ E
  set S := CFC.sqrt (polarMatrix A x T)
  have hS_sa : IsSelfAdjoint S := (CFC.sqrt_nonneg _).isSelfAdjoint
  have hP_sa : LinearMap.IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip
      (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip (matOp (x := x) S) (matOp (x := x) S) := by
    have h := isAdjointPair_matOp (x := x) S
    rwa [← CStarMatrix.star_eq_conjTranspose, hS_sa.star_eq] at h
  have hP_nonneg : ∀ w : E, 0 ≤ inner Aᵐᵒᵖ w (matOp (x := x) S w) :=
    inner_matOp_right_nonneg (CFC.sqrt_nonneg _)
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
    have h1 : unop (inner Aᵐᵒᵖ y (matOp (x := x) (CStarMatrix.gram A (fun i ↦ T (x i))) w)) =
        unop (inner Aᵐᵒᵖ (opAnalysisLinearMap A x y)
          (mulVecLinearMap (CStarMatrix.gram A (fun i ↦ T (x i)))
            (opAnalysisLinearMap A x w))) :=
      congrArg unop
        ((isAdjointPair_opAnalysisLinearMap_opSynthesisLinearMap A x).inner_eq_cstarModule
          y (mulVecLinearMap (CStarMatrix.gram A (fun i ↦ T (x i)))
            (opAnalysisLinearMap A x w))).symm
    have hsum : unop (inner Aᵐᵒᵖ (opAnalysisLinearMap A x y)
        (mulVecLinearMap (CStarMatrix.gram A (fun i ↦ T (x i))) (opAnalysisLinearMap A x w))) =
        unop (inner Aᵐᵒᵖ (∑ i, op (opAnalysisLinearMap A x y i) • T (x i))
          (∑ j, op (opAnalysisLinearMap A x w j) • T (x j))) := by
      rw [← CStarMatrix.sum_star_mul_gram_mul (fun i ↦ T (x i))
        (fun i ↦ opAnalysisLinearMap A x y i) (fun j ↦ opAnalysisLinearMap A x w j)]
      simp [WithCStarModule.pi_inner, Finset.unop_sum, mul_assoc]
    rw [h1, hsum]
    have hT (u : E) : ∑ i, op (opAnalysisLinearMap A x u i) • T (x i) = T u := by
      conv_rhs => rw [← hx.sum_inner_smul u, map_sum]
      simp
    rw [hT y, hT w, LinearMap.comp_apply, LinearEquiv.coe_coe,
      ← (hx.isAdjointPair_frameAdjoint T).inner_eq_cstarModule]
  rw [← matOp_apply (x := x) S z]
  exact (LinearMap.congr_fun (hx.eq_polarModulus_toLinearMap T (matOp (x := x) S)
    hP_sa hP_nonneg hP_sq) z).symm

/-- Explicit frame-matrix formula for the inverse modulus `(hx.polarModulus T).symm`, obtained by
applying `Ring.inverse (CFC.sqrt (polarMatrix A x T))` in frame coordinates and synthesizing. -/
theorem _root_.CStarModule.IsParsevalFrame.polarModulus_symm_apply [DecidableEq ι] {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) :
    (hx.polarModulus T).symm z =
      ∑ i, (∑ j, inner Aᵐᵒᵖ (x j) z *
        op (Ring.inverse (CFC.sqrt (polarMatrix A x T)) i j)) • x i := by
  let : NormedAddCommGroup E := normedAddCommGroupOfCStarModule Aᵐᵒᵖ E
  set S := CFC.sqrt (polarMatrix A x T)
  refine (hx.polarModulus T).symm_apply_eq.mpr ?_
  rw [← matOp_apply (x := x) (Ring.inverse S) z]
  have hL : (hx.polarModulus T) (matOp (x := x) (Ring.inverse S) z) =
      (matOp (x := x) S) (matOp (x := x) (Ring.inverse S) z) := by
    rw [hx.polarModulus_apply T, ← matOp_apply]
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
  let : NormedAddCommGroup E := normedAddCommGroupOfCStarModule Aᵐᵒᵖ E
  let : NormedAddCommGroup F := normedAddCommGroupOfCStarModule Aᵐᵒᵖ F
  let : CompleteSpace E := hx.completeSpace
  CStarModuleUnitary.equivLinearIsometryEquiv
    ((equivAdjointableMap hx T).polarUnitary
      (equivSymmCLM_leftInverse hx T) (equivSymmCLM_rightInverse hx T))

/-- The polar decomposition factorization `T = U ∘ |T|`: applying `hx.polarUnitary T` after
`hx.polarModulus T` recovers `T`. -/
@[simp] theorem _root_.CStarModule.IsParsevalFrame.polarUnitary_polarModulus_apply {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) :
    hx.polarUnitary T (hx.polarModulus T z) = T z := by
  let : NormedAddCommGroup E := normedAddCommGroupOfCStarModule Aᵐᵒᵖ E
  let : NormedAddCommGroup F := normedAddCommGroupOfCStarModule Aᵐᵒᵖ F
  let : CompleteSpace E := hx.completeSpace
  dsimp only [CStarModule.IsParsevalFrame.polarUnitary,
    CStarModule.IsParsevalFrame.polarModulus]
  rw [CStarModuleUnitary.equivLinearIsometryEquiv_apply, polarModulusAux_apply,
    AdjointableMap.polarUnitary_apply_abs]
  simp [equivAdjointableMap]

theorem _root_.CStarModule.IsParsevalFrame.polarUnitary_apply {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (z : E) :
    hx.polarUnitary T z = T ((hx.polarModulus T).symm z) := by
  calc hx.polarUnitary T z
      = hx.polarUnitary T (hx.polarModulus T ((hx.polarModulus T).symm z)) := by
          rw [LinearEquiv.apply_symm_apply]
    _ = T ((hx.polarModulus T).symm z) := hx.polarUnitary_polarModulus_apply T _

theorem _root_.CStarModule.IsParsevalFrame.polarUnitary_symm_apply {x : ι → E}
    (hx : IsParsevalFrame Aᵐᵒᵖ x) (T : E ≃ₗ[Aᵐᵒᵖ] F) (w : F) :
    (hx.polarUnitary T).symm w = hx.polarModulus T (T.symm w) :=
  (hx.polarUnitary T).symm_apply_eq.mpr <| by
    rw [hx.polarUnitary_polarModulus_apply, T.apply_symm_apply]

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
