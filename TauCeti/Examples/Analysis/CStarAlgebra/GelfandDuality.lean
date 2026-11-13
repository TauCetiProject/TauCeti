/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import TauCeti.Analysis.CStarAlgebra.GelfandDuality

import Mathlib.Topology.Order.Compact

/-!
# Nonunital Gelfand duality on the half-open unit interval `(0, 1]`

For `A = C₀(Set.Ioc (0 : ℝ) 1, ℂ)` viewed as a nonunital commutative C⋆-algebra:

* the half-open interval `Set.Ioc (0 : ℝ) 1` identifies homeomorphically with the punctured closed
  unit interval `({0}ᶜ : Set (Set.Icc (0 : ℝ) 1))`, so its one-point compactification is
  `Set.Icc (0 : ℝ) 1` with `∞` sent to `0`;
* the minimal unitization `C₀(Set.Ioc (0 : ℝ) 1, ℂ)⁺¹` is `⋆`-isomorphic to
  `C(Set.Icc (0 : ℝ) 1, ℂ)`, intertwining the augmentation `Unitization.fstStarAlgHom` with point
  evaluation at `0`;
* consequently `characterSpace ℂ C₀(Set.Ioc (0 : ℝ) 1, ℂ)⁺¹` identifies with `Set.Icc (0 : ℝ) 1`
  sending `Unitization.fstCharacter` to `0`, while `characterSpace ℂ C₀(Set.Ioc (0 : ℝ) 1, ℂ)`
  identifies with `Set.Ioc (0 : ℝ) 1` via `WeakDual.CharacterSpace.homeoEvalZeroAtInfty`.

We also exhibit the necessity of the vanishing condition at `Unitization.fstCharacter`: the
constant function `1` and the oscillatory bounded continuous function `t ↦ sin (1 / t)` on
`(0, 1]` both lie in `BoundedContinuousFunction (Set.Ioc (0 : ℝ) 1) ℂ`, yet neither tends to `0`
along `Filter.cocompact (Set.Ioc (0 : ℝ) 1)`.
-/

public section

noncomputable section

open Filter Topology WeakDual
open scoped BoundedContinuousFunction CStarAlgebra OnePoint ZeroAtInfty

namespace TauCeti.GelfandDualityExample

/-- The half-open interval `(0, 1]` is homeomorphic to the punctured closed interval
`[0, 1] \ {0}`. -/
def iocZeroOneHomeomorphComplZero :
    Set.Ioc (0 : ℝ) 1 ≃ₜ ({(0 : Set.Icc (0 : ℝ) 1)}ᶜ : Set (Set.Icc (0 : ℝ) 1)) where
  toFun x := ⟨⟨x.1, Set.Ioc_subset_Icc_self x.2⟩, Subtype.coe_ne_coe.mp x.2.1.ne'⟩
  invFun y := ⟨y.1.1, lt_of_le_of_ne y.1.2.1 (Subtype.coe_ne_coe.mpr y.2).symm, y.1.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _
  continuous_invFun := Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _

/-- The one-point compactification of `(0, 1]` is homeomorphic to `[0, 1]`, sending `∞` to `0`. -/
def onePointIocZeroOneHomeomorph :
    OnePoint (Set.Ioc (0 : ℝ) 1) ≃ₜ Set.Icc (0 : ℝ) 1 :=
  iocZeroOneHomeomorphComplZero.onePointCongr.trans
    (OnePoint.complSingletonHomeomorph (0 : Set.Icc (0 : ℝ) 1))

/-- `onePointIocZeroOneHomeomorph` sends `∞` to `0 ∈ [0, 1]`. -/
@[simp]
theorem onePointIocZeroOneHomeomorph_infty :
    onePointIocZeroOneHomeomorph ∞ = (0 : Set.Icc (0 : ℝ) 1) := by
  simp [onePointIocZeroOneHomeomorph]

/-- `onePointIocZeroOneHomeomorph` embeds `x ∈ (0, 1]` as `x ∈ [0, 1]`. -/
@[simp]
theorem coe_onePointIocZeroOneHomeomorph_coe (x : Set.Ioc (0 : ℝ) 1) :
    (onePointIocZeroOneHomeomorph x : ℝ) = x.1 := by
  simp [onePointIocZeroOneHomeomorph]
  rfl

/-- The minimal unitization `C₀((0, 1], ℂ)⁺¹` is `⋆`-isomorphic to `C([0, 1], ℂ)`. -/
def unitizationZeroAtInftyIocZeroOneStarAlgEquiv :
    C₀(Set.Ioc (0 : ℝ) 1, ℂ)⁺¹ ≃⋆ₐ[ℂ] C(Set.Icc (0 : ℝ) 1, ℂ) :=
  (ZeroAtInftyContinuousMap.unitizationStarAlgEquiv (Set.Ioc (0 : ℝ) 1) ℂ ℂ).trans
    (onePointIocZeroOneHomeomorph.symm.compStarAlgEquiv' ℂ ℂ)

/-- Under `unitizationZeroAtInftyIocZeroOneStarAlgEquiv`, evaluation at `0 ∈ [0, 1]` coincides with
the scalar augmentation `Unitization.fstStarAlgHom`. -/
@[simp]
theorem evalZero_comp_unitizationZeroAtInftyIocZeroOneStarAlgEquiv :
    (ContinuousMap.evalStarAlgHom ℂ ℂ (0 : Set.Icc (0 : ℝ) 1)).comp
        unitizationZeroAtInftyIocZeroOneStarAlgEquiv.toStarAlgHom =
      Unitization.fstStarAlgHom ℂ C₀(Set.Ioc (0 : ℝ) 1, ℂ) := by
  ext u
  have hsymm : onePointIocZeroOneHomeomorph.symm (0 : Set.Icc (0 : ℝ) 1) = ∞ :=
    (Homeomorph.symm_apply_eq _).2 onePointIocZeroOneHomeomorph_infty.symm
  simp [unitizationZeroAtInftyIocZeroOneStarAlgEquiv, hsymm]

/-- The character space of `C₀((0, 1], ℂ)⁺¹` identifies homeomorphically with `[0, 1]`. -/
def characterSpaceUnitizationIocZeroOneHomeomorph :
    Set.Icc (0 : ℝ) 1 ≃ₜ characterSpace ℂ C₀(Set.Ioc (0 : ℝ) 1, ℂ)⁺¹ :=
  (CharacterSpace.homeoEval (Set.Icc (0 : ℝ) 1) ℂ).trans
    (CharacterSpace.compHomeomorph unitizationZeroAtInftyIocZeroOneStarAlgEquiv)

/-- Under `characterSpaceUnitizationIocZeroOneHomeomorph`, `0 ∈ [0, 1]` corresponds to the
augmentation character `Unitization.fstCharacter ℂ C₀((0, 1], ℂ)`. -/
@[simp]
theorem characterSpaceUnitizationIocZeroOneHomeomorph_zero :
    characterSpaceUnitizationIocZeroOneHomeomorph (0 : Set.Icc (0 : ℝ) 1) =
      Unitization.fstCharacter ℂ C₀(Set.Ioc (0 : ℝ) 1, ℂ) := by
  ext u
  have hsymm : onePointIocZeroOneHomeomorph.symm (0 : Set.Icc (0 : ℝ) 1) = ∞ :=
    (Homeomorph.symm_apply_eq _).2 onePointIocZeroOneHomeomorph_infty.symm
  simp [characterSpaceUnitizationIocZeroOneHomeomorph,
    unitizationZeroAtInftyIocZeroOneStarAlgEquiv, hsymm]

/-- A map into `(0, 1]` tends to the cocompact filter if and only if its real values tend to `0`. -/
theorem tendsto_cocompact_iocZeroOne_iff {α : Type*} {l : Filter α}
    {u : α → Set.Ioc (0 : ℝ) 1} :
    Tendsto u l (cocompact (Set.Ioc (0 : ℝ) 1)) ↔ Tendsto (fun i ↦ (u i : ℝ)) l (𝓝 0) := by
  rw [← coclosedCompact_eq_cocompact, ← OnePoint.comap_coe_nhds_infty, tendsto_comap_iff,
    onePointIocZeroOneHomeomorph.isEmbedding.tendsto_nhds_iff,
    onePointIocZeroOneHomeomorph_infty,
    Topology.IsEmbedding.subtypeVal.tendsto_nhds_iff]
  simp [Function.comp_def]

/-- Sequence `n ↦ (π / 2 + n * (2π))⁻¹` in `(0, 1]` converging to the puncture `0` (cocompactly),
along which `sin (1 / t)` is identically `1`. -/
private def peakSeq (n : ℕ) : Set.Ioc (0 : ℝ) 1 :=
  ⟨(Real.pi / 2 + n * (2 * Real.pi))⁻¹, by
    have hge : 1 ≤ Real.pi / 2 + n * (2 * Real.pi) :=
      le_add_of_le_of_nonneg Real.one_le_pi_div_two (by positivity)
    exact ⟨inv_pos.mpr (zero_lt_one.trans_le hge), inv_le_one_of_one_le₀ hge⟩⟩

private theorem tendsto_peakSeq_cocompact :
    Tendsto peakSeq atTop (cocompact (Set.Ioc (0 : ℝ) 1)) := by
  rw [tendsto_cocompact_iocZeroOne_iff]
  refine tendsto_inv_atTop_zero.comp ?_
  exact tendsto_atTop_add_const_left atTop (Real.pi / 2)
    (tendsto_natCast_atTop_atTop.atTop_mul_const Real.two_pi_pos)

/-- The oscillatory function `t ↦ sin (1 / t)` as a bounded continuous complex-valued function on
`(0, 1]`. -/
def sinInvBCF : Set.Ioc (0 : ℝ) 1 →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun t ↦ (Real.sin (1 / t.1) : ℂ),
      Complex.continuous_ofReal.comp <|
        Real.continuous_sin.comp (continuous_const.div continuous_subtype_val fun t ↦ t.2.1.ne')⟩
    2 fun s t ↦ by
      calc dist (Real.sin (1 / s.1) : ℂ) (Real.sin (1 / t.1) : ℂ)
          _ ≤ ‖(Real.sin (1 / s.1) : ℂ)‖ + ‖(Real.sin (1 / t.1) : ℂ)‖ := dist_le_norm_add_norm _ _
          _ = |Real.sin (1 / s.1)| + |Real.sin (1 / t.1)| := by
            rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
          _ ≤ 1 + 1 := add_le_add (Real.abs_sin_le_one _) (Real.abs_sin_le_one _)
          _ = 2 := one_add_one_eq_two

/-- The constant bounded continuous function `1` on `(0, 1]` does not vanish at infinity. -/
theorem not_tendsto_one_cocompact :
    ¬ Tendsto (1 : Set.Ioc (0 : ℝ) 1 →ᵇ ℂ) (cocompact (Set.Ioc (0 : ℝ) 1)) (𝓝 0) := fun h ↦
  one_ne_zero <| tendsto_nhds_unique (tendsto_const_nhds (x := (1 : ℂ)))
    (h.comp tendsto_peakSeq_cocompact)

/-- The bounded continuous function `t ↦ sin (1 / t)` on `(0, 1]` does not vanish at infinity. -/
theorem not_tendsto_sinInvBCF_cocompact :
    ¬ Tendsto sinInvBCF (cocompact (Set.Ioc (0 : ℝ) 1)) (𝓝 0) := by
  intro h
  have hcomp : Tendsto (sinInvBCF ∘ peakSeq) atTop (𝓝 (1 : ℂ)) := by
    have heq : sinInvBCF ∘ peakSeq = fun _ : ℕ ↦ (1 : ℂ) := by
      ext n
      simp [Function.comp_apply, sinInvBCF, peakSeq, one_div, Complex.sin_add_nat_mul_two_pi,
        Complex.sin_pi_div_two]
    rw [heq]
    exact tendsto_const_nhds
  exact one_ne_zero (tendsto_nhds_unique hcomp (h.comp tendsto_peakSeq_cocompact))

end TauCeti.GelfandDualityExample
