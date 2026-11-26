/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.HaarMeasureWithValues.Convolution
public import TauCeti.RingTheory.Idempotents.Corner.Basic

/-!
# Normalized compact open Hecke idempotents

For a compact open subgroup of unit volume, `TauCeti.HeckeAlgebra.normalizedIndicator` is its
indicator divided by its volume. Left and right multiplication by this idempotent characterize
left and right subgroup invariance, respectively. For nested subgroups the larger subgroup's
idempotent absorbs the smaller one on either side.

The statements use `LocallyConstant.compactOpenIndicator` and
`TauCeti.HaarMeasureWithValues.convolution` on `TauCeti.HeckeAlgebra`.
`Subsemigroup.mem_corner_iff` identifies the corner, whose unit is given by `Corner.val_one`.

## References

* C. J. Bushnell and G. Henniart, *The Local Langlands Conjecture for GL(2)*, §4.1,
  Proposition (1)–(3).
-/

public section

open Set TopologicalSpace LocallyConstant
open scoped Pointwise

namespace TauCeti.HeckeAlgebra

variable {A G : Type*} [CommSemiring A] [Group G] [TopologicalSpace G]

section Indicator

variable [SeparatelyContinuousMul G]

/-- The indicator of a compact open subgroup divided by its unit volume. -/
noncomputable def normalizedIndicator (μ : HaarMeasureWithValues A G)
    (U : OpenSubgroup G) (hU : IsCompact (U : Set G))
    (h : IsUnit (μ (U.toCompactOpens hU))) : HeckeAlgebra μ :=
  ofCompactlySupported ⟨(LocallyConstant.const G (↑h.unit⁻¹ : A)).indicator U.isClopen,
    indicator_mem_compactlySupported _ _ hU⟩

/-- The normalized indicator takes the inverse volume on the subgroup and zero elsewhere. -/
@[simp]
theorem normalizedIndicator_apply {μ : HaarMeasureWithValues A G}
    {U : OpenSubgroup G} {hU : IsCompact (U : Set G)}
    (h : IsUnit (μ (U.toCompactOpens hU))) (x : G) :
    (normalizedIndicator μ U hU h).toCompactlySupported.val x =
      (U : Set G).indicator (fun _ ↦ (↑h.unit⁻¹ : A)) x :=
  (rfl)

end Indicator

variable [IsTopologicalGroup G] [T2Space G] {μ : HaarMeasureWithValues A G}
  {U : OpenSubgroup G} {hU : IsCompact (U : Set G)} (h : IsUnit (μ (U.toCompactOpens hU)))

/-- Left multiplication by the normalized indicator fixes precisely the left invariant
functions (Bushnell and Henniart, §4.1). -/
theorem normalizedIndicator_mul_eq_iff (f : HeckeAlgebra μ) :
    normalizedIndicator μ U hU h * f = f ↔
      ∀ g ∈ U, ∀ x, f.toCompactlySupported.val (g * x) = f.toCompactlySupported.val x := by
  classical
  constructor
  · intro hf g hg x
    have hTranslate :
        compactlySupportedRep A G G A g⁻¹ (normalizedIndicator μ U hU h).toCompactlySupported =
          (normalizedIndicator μ U hU h).toCompactlySupported := by
      ext y
      rw [compactlySupportedRep_apply_coe, inv_inv, smul_eq_mul, normalizedIndicator_apply,
        normalizedIndicator_apply]
      exact if_congr ((U : Subgroup G).mul_mem_cancel_left hg) rfl rfl
    have hFixed : compactlySupportedRep A G G A g⁻¹ f.toCompactlySupported =
        f.toCompactlySupported := by
      have hMul := congrArg HeckeAlgebra.toCompactlySupported hf
      rw [toCompactlySupported_mul] at hMul
      nth_rw 1 [← hMul]
      rw [← μ.convolution_compactlySupportedRep_left, hTranslate, hMul]
    simpa only [compactlySupportedRep_apply_coe, inv_inv, smul_eq_mul] using
      congrArg (fun F : compactlySupported A G A ↦ F.val x) hFixed
  · intro hf
    ext x
    rw [toCompactlySupported_mul, HaarMeasureWithValues.convolution_apply]
    have hSlice :
        compactlySupported.sliceRight A A x
            (HaarMeasureWithValues.convolutionKernel
              (normalizedIndicator μ U hU h).toCompactlySupported f.toCompactlySupported) =
          ⟨compactOpenIndicator (U.toCompactOpens hU)
            ((↑h.unit⁻¹ : A) * f.toCompactlySupported.val x),
            compactOpenIndicator_mem_compactlySupported _ _⟩ := by
      ext y
      rw [compactlySupported.sliceRight_apply, HaarMeasureWithValues.convolutionKernel_apply,
        normalizedIndicator_apply]
      by_cases hy : y ∈ (U : Set G)
      · rw [Set.indicator_of_mem hy, hf y⁻¹ (U.inv_mem hy) x,
          compactOpenIndicator_of_mem (OpenSubgroup.mem_toCompactOpens.2 hy)]
      · rw [Set.indicator_of_notMem hy, zero_mul,
          compactOpenIndicator_of_notMem (mt OpenSubgroup.mem_toCompactOpens.1 hy)]
    rw [hSlice, HaarMeasureWithValues.integral_compactOpenIndicator, smul_eq_mul]
    exact (congrArg (· * _) h.unit_spec.symm).trans (Units.mul_inv_cancel_left h.unit _)

/-- Right multiplication by the normalized indicator fixes precisely the right invariant
functions (Bushnell and Henniart, §4.1). -/
theorem mul_normalizedIndicator_eq_iff (f : HeckeAlgebra μ) :
    f * normalizedIndicator μ U hU h = f ↔
      ∀ g ∈ U, ∀ x, f.toCompactlySupported.val (x * g) = f.toCompactlySupported.val x := by
  classical
  constructor
  · intro hf g hg x
    have hTranslate :
        compactlySupportedRep A Gᵐᵒᵖ G A (MulOpposite.op g⁻¹)
            (normalizedIndicator μ U hU h).toCompactlySupported =
          (normalizedIndicator μ U hU h).toCompactlySupported := by
      ext y
      rw [compactlySupportedRep_apply_coe, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_inv,
        MulOpposite.unop_op, inv_inv, normalizedIndicator_apply, normalizedIndicator_apply]
      exact if_congr ((U : Subgroup G).mul_mem_cancel_right hg) rfl rfl
    have hFixed : compactlySupportedRep A Gᵐᵒᵖ G A (MulOpposite.op g⁻¹)
        f.toCompactlySupported = f.toCompactlySupported := by
      have hMul := congrArg HeckeAlgebra.toCompactlySupported hf
      rw [toCompactlySupported_mul] at hMul
      nth_rw 1 [← hMul]
      rw [← μ.convolution_compactlySupportedRep_right, hTranslate, hMul]
    simpa only [compactlySupportedRep_apply_coe, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_inv, MulOpposite.unop_op, inv_inv] using
      congrArg (fun F : compactlySupported A G A ↦ F.val x) hFixed
  · intro hf
    ext x
    rw [toCompactlySupported_mul, HaarMeasureWithValues.convolution_apply]
    have hSlice :
        compactlySupported.sliceRight A A x
            (HaarMeasureWithValues.convolutionKernel
              f.toCompactlySupported (normalizedIndicator μ U hU h).toCompactlySupported) =
          ⟨compactOpenIndicator (x • U.toCompactOpens hU)
            ((↑h.unit⁻¹ : A) * f.toCompactlySupported.val x),
            compactOpenIndicator_mem_compactlySupported _ _⟩ := by
      ext y
      rw [compactlySupported.sliceRight_apply, HaarMeasureWithValues.convolutionKernel_apply,
        normalizedIndicator_apply]
      -- The integrand is supported on the left coset `xU`.
      have hy : y ∈ x • U.toCompactOpens hU ↔ x⁻¹ * y ∈ (U : Subgroup G) := by
        rw [CompactOpens.mem_smul_iff_inv_smul_mem, smul_eq_mul]
        exact OpenSubgroup.mem_toCompactOpens
      have hInv : y⁻¹ * x ∈ (U : Subgroup G) ↔ x⁻¹ * y ∈ (U : Subgroup G) := by
        rw [← (U : Subgroup G).inv_mem_iff (x := y⁻¹ * x), mul_inv_rev, inv_inv]
      by_cases hy' : x⁻¹ * y ∈ (U : Subgroup G)
      · have hValue : f.toCompactlySupported.val y = f.toCompactlySupported.val x := by
          simpa only [mul_inv_cancel_left] using hf (x⁻¹ * y) hy' x
        rw [Set.indicator_of_mem (s := (U : Set G)) (hInv.mpr hy'),
          compactOpenIndicator_of_mem (hy.mpr hy'),
          hValue, mul_comm]
      · rw [Set.indicator_of_notMem (s := (U : Set G)) (mt hInv.mp hy'), mul_zero,
          compactOpenIndicator_of_notMem (mt hy.mp hy')]
    rw [hSlice, HaarMeasureWithValues.integral_compactOpenIndicator, μ.apply_smul, smul_eq_mul]
    exact (congrArg (· * _) h.unit_spec.symm).trans (Units.mul_inv_cancel_left h.unit _)

/-- The larger subgroup's normalized indicator absorbs the smaller one's on the left. -/
@[simp]
theorem normalizedIndicator_mul_normalizedIndicator_of_ge {W : OpenSubgroup G}
    {hW : IsCompact (W : Set G)} (h' : IsUnit (μ (W.toCompactOpens hW))) (hWU : W ≤ U) :
    normalizedIndicator μ U hU h * normalizedIndicator μ W hW h' =
      normalizedIndicator μ U hU h := by
  classical
  apply (mul_normalizedIndicator_eq_iff h' _).2
  intro g hg x
  rw [normalizedIndicator_apply, normalizedIndicator_apply]
  exact if_congr ((U : Subgroup G).mul_mem_cancel_right (hWU hg)) rfl rfl

/-- The larger subgroup's normalized indicator absorbs the smaller one's on the right. -/
@[simp]
theorem normalizedIndicator_mul_normalizedIndicator_of_le {W : OpenSubgroup G}
    {hW : IsCompact (W : Set G)} (h' : IsUnit (μ (W.toCompactOpens hW))) (hWU : W ≤ U) :
    normalizedIndicator μ W hW h' * normalizedIndicator μ U hU h =
      normalizedIndicator μ U hU h := by
  classical
  apply (normalizedIndicator_mul_eq_iff h' _).2
  intro g hg x
  rw [normalizedIndicator_apply, normalizedIndicator_apply]
  exact if_congr ((U : Subgroup G).mul_mem_cancel_left (hWU hg)) rfl rfl

/-- The normalized indicator of a compact open subgroup of unit volume is idempotent
(Bushnell and Henniart, §4.1). -/
theorem isIdempotentElem_normalizedIndicator :
    IsIdempotentElem (normalizedIndicator μ U hU h) :=
  normalizedIndicator_mul_normalizedIndicator_of_le h h le_rfl

/-- The corner cut out by the normalized indicator consists of the bi-invariant functions. -/
theorem mem_corner_normalizedIndicator_iff (f : HeckeAlgebra μ) :
    f ∈ Subsemigroup.corner (normalizedIndicator μ U hU h) ↔
      (∀ g ∈ U, ∀ x, f.toCompactlySupported.val (g * x) = f.toCompactlySupported.val x) ∧
      (∀ g ∈ U, ∀ x, f.toCompactlySupported.val (x * g) = f.toCompactlySupported.val x) := by
  rw [Subsemigroup.mem_corner_iff (isIdempotentElem_normalizedIndicator h),
    normalizedIndicator_mul_eq_iff, mul_normalizedIndicator_eq_iff]

end TauCeti.HeckeAlgebra
