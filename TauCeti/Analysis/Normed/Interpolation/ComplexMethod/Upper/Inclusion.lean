/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Basic
public import TauCeti.Analysis.Normed.Interpolation.ComplexMethod.Upper.Map
import TauCeti.Analysis.Complex.HasPrimitives
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive

/-!
# The lower complex method embeds in the upper complex method

For a compatible couple `(X₀, X₁)` of complex Banach spaces and `0 < θ < 1`, every element of
Calderón's (lower) complex interpolation space `[X₀, X₁]_θ` lies in his upper space `[X₀, X₁]^θ`,
and `‖u‖^θ ≤ ‖u‖_θ`. If `F` is an admissible function with `F θ = u`, its primitive
`G z = ∫₀^z F` along the wedge from `0` (`Complex.wedgeIntegral 0 z F`) is an upper strip function
with `deriv G θ = u`: on the line `re z = j` its increments are `G (j + t i) - G (j + s i) =
∫ₛᵗ i F (j + r i) dr`, which lie in `X_j` with difference quotients bounded by the sup norm of the
boundary trace of `F` there.

This inclusion is one half of the comparison of the two complex methods in Bergh–Löfström, §4.3.
The reverse inclusion, which holds with equal norms when one of `X₀`, `X₁` is reflexive, is not
treated here.

## Main declarations

* `TauCeti.CompatibleCouple.IsStripFunction.isUpperStripFunction_wedgeIntegral`: the wedge
  primitive of an admissible function is an upper strip function, with boundary difference
  quotients `CompatibleCouple.stripTracesToUpper`.
* `TauCeti.CompatibleCouple.stripTracesToUpper`: the continuous linear map from the boundary
  traces of admissible functions to the boundary difference quotients of their primitives, of norm
  at most one, intertwining evaluation at `z` with differentiation at `z` in the open strip
  (`CompatibleCouple.upperStripDerivEval_stripTracesToUpper`).
* `TauCeti.CompatibleCouple.ComplexMethodSpace.toUpper`: the inclusion
  `[X₀, X₁]_θ →L[ℂ] [X₀, X₁]^θ`, of norm at most one
  (`ComplexMethodSpace.norm_toUpper_le`), lying over the identity of the sum space
  (`ComplexMethodSpace.toSum_toUpper`) and hence injective for `0 < θ < 1`
  (`ComplexMethodSpace.toUpper_injective`). It commutes with the inclusions of the intersection
  (`ComplexMethodSpace.toUpper_ofInter`) and with the maps induced by endpoint operators
  (`ComplexMethodSpace.toUpper_map`).

## References

* A.-P. Calderón, *Intermediate spaces and interpolation, the complex method*, Studia Math. 24
  (1964), 113–190.
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Springer, 1976, §4.3.
* M. Cwikel, *Lecture notes on duality and interpolation spaces*, arXiv:0803.3558 (2008), §2.4.
-/

public noncomputable section

open Asymptotics Complex Complex.HadamardThreeLines Filter MeasureTheory Set
open TauCeti.Complex.HadamardThreeLines
open scoped BoundedContinuousFunction NNReal ZeroAtInfty

namespace TauCeti.CompatibleCouple

variable {X₀ X₁ V : Type*}
  [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [NormedAddCommGroup X₁] [NormedSpace ℂ X₁]
  [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [ContinuousAdd V] [T1Space V]
  (C : CompatibleCouple ℂ X₀ X₁ V)

/-! ### The wedge primitive of an admissible function -/

section Primitive

/-- The vertical primitive `t ↦ ∫ r in 0..t, I • f r` of a boundary trace is `‖f‖`-Lipschitz. -/
private theorem lipschitzWith_integral_I_smul {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (f : C₀(ℝ, X)) : LipschitzWith ‖f‖₊ fun t => ∫ r in 0..t, I • f r :=
  intervalIntegral.lipschitzWith_primitive ((map_continuous f).const_smul I).locallyIntegrable
    (ae_of_all _ fun r => by simpa [norm_smul] using ZeroAtInftyContinuousMap.norm_coe_le_norm f r)
    0

/-- The boundary difference quotients of the vertical primitives of the boundary traces `g`. -/
private def primitiveTrace (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)) :
    (offDiag (univ : Set ℝ) →ᵇ X₀) × (offDiag (univ : Set ℝ) →ᵇ X₁) :=
  ((lipschitzWith_integral_I_smul g.1).offDiagSlope,
    (lipschitzWith_integral_I_smul g.2).offDiagSlope)

private theorem integral_I_smul_add {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (f₁ f₂ : C₀(ℝ, X)) (t : ℝ) :
    ∫ r in 0..t, I • (f₁ + f₂) r = (∫ r in 0..t, I • f₁ r) + ∫ r in 0..t, I • f₂ r := by
  simp only [add_apply, smul_add]
  exact intervalIntegral.integral_add (((map_continuous f₁).const_smul I).intervalIntegrable _ _)
    (((map_continuous f₂).const_smul I).intervalIntegrable _ _)

private theorem primitiveTrace_add (g h : C₀(ℝ, X₀) × C₀(ℝ, X₁)) :
    primitiveTrace (g + h) = primitiveTrace g + primitiveTrace h := by
  refine Prod.ext (BoundedContinuousFunction.ext fun p => ?_)
    (BoundedContinuousFunction.ext fun p => ?_) <;>
  simp only [primitiveTrace, LipschitzWith.offDiagSlope_apply, Prod.fst_add, Prod.snd_add,
    integral_I_smul_add] <;>
  simp only [FunLike.coe_add, Pi.add_apply, LipschitzWith.offDiagSlope_apply, add_sub_add_comm,
    smul_add]

private theorem primitiveTrace_smul (c : ℂ) (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)) :
    primitiveTrace (c • g) = c • primitiveTrace g := by
  refine Prod.ext (BoundedContinuousFunction.ext fun p => ?_)
    (BoundedContinuousFunction.ext fun p => ?_) <;>
  simp [primitiveTrace, smul_comm I c, intervalIntegral.integral_smul, ← smul_sub,
    smul_comm _ c]

private theorem norm_primitiveTrace_le (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)) :
    ‖primitiveTrace g‖ ≤ ‖g‖ :=
  norm_prod_le_iff.2
    ⟨(LipschitzWith.norm_offDiagSlope_le _).trans (by simpa using norm_fst_le g),
      (LipschitzWith.norm_offDiagSlope_le _).trans (by simpa using norm_snd_le g)⟩

variable [CompleteSpace X₀] [CompleteSpace X₁]

variable {C} {F : ℂ → C.SumSpace} {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)}

private theorem wedgeIntegral_mul_I (hF : C.IsStripFunction F g) (t : ℝ) :
    wedgeIntegral 0 (t * I) F = C.fstToSum (∫ r in 0..t, I • g.1 r) := by
  -- the wedge from `0` to `t * I` is the vertical segment along `re z = 0`
  rw [intervalIntegral.integral_smul, map_smul, ← ContinuousLinearMap.intervalIntegral_comp_comm _
    ((map_continuous g.1).intervalIntegrable _ _)]
  simp [wedgeIntegral, hF.apply_mul_I]

private theorem wedgeIntegral_one_add_mul_I (hF : C.IsStripFunction F g) (t : ℝ) :
    wedgeIntegral 0 (1 + t * I) F = wedgeIntegral 0 1 F + C.sndToSum (∫ r in 0..t, I • g.2 r) := by
  -- the wedge from `0` to `1 + t * I` runs along `[0, 1]`, then vertically along `re z = 1`
  rw [intervalIntegral.integral_smul, map_smul, ← ContinuousLinearMap.intervalIntegral_comp_comm _
    ((map_continuous g.2).intervalIntegrable _ _)]
  simp [wedgeIntegral, hF.apply_one_add_mul_I]

omit [CompleteSpace X₀] [CompleteSpace X₁] in
/-- The wedge primitive of an admissible function grows at most linearly on the closed strip. -/
private theorem norm_wedgeIntegral_le (hF : C.IsStripFunction F g) {z : ℂ}
    (hz : z ∈ verticalClosedStrip 0 1) : ‖wedgeIntegral 0 z F‖ ≤ 2 * ‖g‖ * ‖z‖ := by
  simpa using TauCeti.norm_wedgeIntegral_le_of_norm_le_const (z := 0) (w := z) fun u hu =>
    hF.norm_le (uIcc_subset_Icc (by simp) hz hu.1)

private theorem isUpperStripFunction_wedgeIntegral_primitiveTrace (hF : C.IsStripFunction F g) :
    C.IsUpperStripFunction (fun z => wedgeIntegral 0 z F) (primitiveTrace g) :=
  IsUpperStripFunction.of_lipschitz
    (hF.diffContOnCl.diffContOnCl_wedgeIntegral_verticalStrip zero_lt_one (by simp))
    ⟨1, 1, IsBigO.of_bound (2 * ‖g‖) <| eventually_inf_principal.2 <| .of_forall fun w hw => by
      rw [one_mul, Real.rpow_one, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact (norm_wedgeIntegral_le hF (verticalStrip_subset_verticalClosedStrip 0 1 hw)).trans
        (mul_le_mul_of_nonneg_left ((le_add_of_nonneg_right zero_le_one).trans
          (Real.add_one_le_exp _)) (by positivity))⟩
    (lipschitzWith_integral_I_smul g.1) (lipschitzWith_integral_I_smul g.2)
    (fun t s => by simp only [wedgeIntegral_mul_I hF, map_sub])
    (fun t s => by simp only [wedgeIntegral_one_add_mul_I hF, map_sub, add_sub_add_left_eq_sub])

end Primitive

variable [CompleteSpace X₀] [CompleteSpace X₁]

/-! ### From admissible traces to upper traces -/

private theorem primitiveTrace_mem (g : C.stripTraces) :
    primitiveTrace (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)) ∈ C.upperStripTraces :=
  mem_upperStripTraces_iff.2
    ⟨_, isUpperStripFunction_wedgeIntegral_primitiveTrace (C.isStripFunction_stripFunction g)⟩

/-- The boundary difference quotients of the wedge primitive `z ↦ ∫₀^z F` of the admissible
function `F` with boundary traces `g` (`IsStripFunction.isUpperStripFunction_wedgeIntegral`). It is
a continuous linear map of norm at most one (`CompatibleCouple.norm_stripTracesToUpper_le`), and it
turns evaluation at a point of the open strip into differentiation there
(`CompatibleCouple.upperStripDerivEval_stripTracesToUpper`). -/
def stripTracesToUpper : C.stripTraces →L[ℂ] C.upperStripTraces :=
  LinearMap.mkContinuous
    { toFun g := ⟨primitiveTrace g, C.primitiveTrace_mem g⟩
      map_add' g h := Subtype.ext <| by
        simpa using primitiveTrace_add (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)) h
      map_smul' c g := Subtype.ext <| by
        simpa using primitiveTrace_smul c (g : C₀(ℝ, X₀) × C₀(ℝ, X₁)) }
    1 fun g => by simpa using norm_primitiveTrace_le (g : C₀(ℝ, X₀) × C₀(ℝ, X₁))

private theorem coe_stripTracesToUpper (g : C.stripTraces) :
    (C.stripTracesToUpper g :
      (offDiag (univ : Set ℝ) →ᵇ X₀) × (offDiag (univ : Set ℝ) →ᵇ X₁)) = primitiveTrace g :=
  (rfl)

/-- The `X₀`-component of `stripTracesToUpper g` is the difference quotient of the vertical
primitive `t ↦ ∫ r in 0..t, I • g₀ r`. -/
@[simp]
theorem stripTracesToUpper_apply_fst (g : C.stripTraces) (p : offDiag (univ : Set ℝ)) :
    (C.stripTracesToUpper g).val.1 p =
      (p.val.1 - p.val.2)⁻¹ •
        ((∫ r in 0..p.val.1, I • g.val.1 r) - ∫ r in 0..p.val.2, I • g.val.1 r) := by
  rw [coe_stripTracesToUpper, primitiveTrace, LipschitzWith.offDiagSlope_apply]

/-- The `X₁`-component of `stripTracesToUpper g` is the difference quotient of the vertical
primitive `t ↦ ∫ r in 0..t, I • g₁ r`. -/
@[simp]
theorem stripTracesToUpper_apply_snd (g : C.stripTraces) (p : offDiag (univ : Set ℝ)) :
    (C.stripTracesToUpper g).val.2 p =
      (p.val.1 - p.val.2)⁻¹ •
        ((∫ r in 0..p.val.1, I • g.val.2 r) - ∫ r in 0..p.val.2, I • g.val.2 r) := by
  rw [coe_stripTracesToUpper, primitiveTrace, LipschitzWith.offDiagSlope_apply]

/-- **The primitive of an admissible function.** For an admissible function `F` with boundary
traces `g`, the wedge primitive `z ↦ ∫₀^z F` is an upper strip function, with boundary difference
quotients `stripTracesToUpper g`. -/
theorem IsStripFunction.isUpperStripFunction_wedgeIntegral {F : ℂ → C.SumSpace}
    {g : C₀(ℝ, X₀) × C₀(ℝ, X₁)} (hF : C.IsStripFunction F g) :
    C.IsUpperStripFunction (fun z => wedgeIntegral 0 z F)
      (C.stripTracesToUpper ⟨g, mem_stripTraces_iff.2 ⟨F, hF⟩⟩) := by
  rw [coe_stripTracesToUpper]
  exact isUpperStripFunction_wedgeIntegral_primitiveTrace hF

theorem norm_stripTracesToUpper_le (g : C.stripTraces) : ‖C.stripTracesToUpper g‖ ≤ ‖g‖ := by
  rw [← Submodule.norm_coe, coe_stripTracesToUpper]
  exact norm_primitiveTrace_le _

theorem opNorm_stripTracesToUpper_le : ‖C.stripTracesToUpper‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun g => by
    simpa using C.norm_stripTracesToUpper_le g

/-- At a point `z` of the open strip, the derivative of the primitive of an admissible function is
its value: `upperStripDerivEval z ∘ stripTracesToUpper = stripEval z`. -/
theorem upperStripDerivEval_stripTracesToUpper {z : ℂ} (hz : z ∈ verticalStrip 0 1)
    (g : C.stripTraces) : C.upperStripDerivEval z (C.stripTracesToUpper g) = C.stripEval z g := by
  have hF := C.isStripFunction_stripFunction g
  rw [upperStripDerivEval_eq_deriv hz (g := C.stripTracesToUpper g)
    hF.isUpperStripFunction_wedgeIntegral, stripEval_apply]
  exact (hF.diffContOnCl.hasDerivAt_wedgeIntegral_verticalStrip (by simp) hz).deriv

/-! ### The inclusion `[X₀, X₁]_θ → [X₀, X₁]^θ` -/

namespace ComplexMethodSpace

variable {C} {θ : ℝ}

/-- The inclusion of Calderón's lower complex interpolation space `[X₀, X₁]_θ` into his upper
space `[X₀, X₁]^θ`, sending the value `F θ` of an admissible function to the class of its wedge
primitive. For `0 < θ < 1` it lies over the identity of the sum space
(`ComplexMethodSpace.toSum_toUpper`); for other `θ` the upper space is zero. -/
def toUpper : C.ComplexMethodSpace θ →L[ℂ] C.UpperComplexMethodSpace θ :=
  lift ((UpperComplexMethodSpace.mk θ).comp C.stripTracesToUpper) fun g hg => by
    by_cases hθ : θ ∈ Ioo 0 1
    · rw [ContinuousLinearMap.comp_apply, ← map_zero (UpperComplexMethodSpace.mk (C := C) θ),
        UpperComplexMethodSpace.mk_eq_mk_iff, map_zero,
        C.upperStripDerivEval_stripTracesToUpper (by simpa using hθ), hg]
    · exact UpperComplexMethodSpace.eq_zero_of_notMem hθ _

@[simp]
theorem toUpper_mk (g : C.stripTraces) :
    toUpper (mk θ g) = UpperComplexMethodSpace.mk θ (C.stripTracesToUpper g) := by
  rw [toUpper, lift_mk, ContinuousLinearMap.comp_apply]

/-- For `0 < θ < 1`, the inclusion `[X₀, X₁]_θ → [X₀, X₁]^θ` lies over the identity of the sum
space. -/
@[simp]
theorem toSum_toUpper (hθ : θ ∈ Ioo 0 1) (u : C.ComplexMethodSpace θ) :
    UpperComplexMethodSpace.toSum (toUpper u) = toSum u := by
  obtain ⟨g, rfl⟩ := mk_surjective u
  rw [toUpper_mk, UpperComplexMethodSpace.toSum_mk,
    C.upperStripDerivEval_stripTracesToUpper (by simpa using hθ), toSum_mk]

theorem toUpper_injective (hθ : θ ∈ Ioo 0 1) :
    Function.Injective (toUpper : C.ComplexMethodSpace θ → C.UpperComplexMethodSpace θ) :=
  fun u v huv => toSum_injective <| by
    rw [← toSum_toUpper hθ u, ← toSum_toUpper hθ v, huv]

theorem opNorm_toUpper_le :
    ‖(toUpper : C.ComplexMethodSpace θ →L[ℂ] C.UpperComplexMethodSpace θ)‖ ≤ 1 := by
  rw [toUpper, norm_lift]
  exact (UpperComplexMethodSpace.norm_mk_comp_le _).trans C.opNorm_stripTracesToUpper_le

/-- **The upper norm is at most the lower norm:** `‖u‖^θ ≤ ‖u‖_θ` for `u ∈ [X₀, X₁]_θ`. -/
theorem norm_toUpper_le (u : C.ComplexMethodSpace θ) : ‖toUpper u‖ ≤ ‖u‖ := by
  simpa using (toUpper (C := C) (θ := θ)).le_of_opNorm_le opNorm_toUpper_le u

/-- The inclusion `[X₀, X₁]_θ → [X₀, X₁]^θ` commutes with the inclusions of the intersection. -/
@[simp]
theorem toUpper_ofInter (x : C.inter) :
    toUpper (ofInter θ x) = UpperComplexMethodSpace.ofInter θ x := by
  by_cases hθ : θ ∈ Ioo 0 1
  · ext
    rw [toSum_toUpper hθ, toSum_ofInter (Ioo_subset_Icc_self hθ),
      UpperComplexMethodSpace.toSum_ofInter hθ]
  · exact UpperComplexMethodSpace.eq_zero_of_notMem hθ _ |>.trans
      (UpperComplexMethodSpace.eq_zero_of_notMem hθ _).symm

section Map

variable {Y₀ Y₁ W : Type*}
  [NormedAddCommGroup Y₀] [NormedSpace ℂ Y₀] [CompleteSpace Y₀]
  [NormedAddCommGroup Y₁] [NormedSpace ℂ Y₁] [CompleteSpace Y₁]
  [AddCommGroup W] [Module ℂ W] [TopologicalSpace W] [ContinuousAdd W] [T1Space W]
  {D : CompatibleCouple ℂ Y₀ Y₁ W}
  (T₀ : X₀ →L[ℂ] Y₀) (T₁ : X₁ →L[ℂ] Y₁)
  (h : ∀ x : C.inter, D.fstToSum (T₀ (C.interFst x)) = D.sndToSum (T₁ (C.interSnd x)))

/-- The inclusion `[X₀, X₁]_θ → [X₀, X₁]^θ` is natural: it commutes with the maps induced on both
methods by endpoint operators `T₀`, `T₁` that agree on the intersection. -/
theorem toUpper_map (u : C.ComplexMethodSpace θ) :
    toUpper (map θ T₀ T₁ h u) = UpperComplexMethodSpace.map θ T₀ T₁ h (toUpper u) := by
  by_cases hθ : θ ∈ Ioo 0 1
  · ext
    rw [toSum_toUpper hθ, toSum_map, UpperComplexMethodSpace.toSum_map, toSum_toUpper hθ]
  · exact UpperComplexMethodSpace.eq_zero_of_notMem hθ _ |>.trans
      (UpperComplexMethodSpace.eq_zero_of_notMem hθ _).symm

end Map

end ComplexMethodSpace

end TauCeti.CompatibleCouple
