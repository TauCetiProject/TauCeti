/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Completion.Basic
public import Mathlib.Topology.Algebra.Valued.ValuedField

import Mathlib.RingTheory.Valuation.Integral

/-!
# Valued fields as Tate rings

The valuation subring of a valued field is open and bounded, at arbitrary rank.
Consequently a nonzero topologically nilpotent element makes the field a Tate ring,
and its valuation subring is a ring of integral elements. These results apply to
completed valued residue fields without choosing a real-valued norm.
-/

public section

open Filter Pointwise Topology

namespace TauCeti.Huber

variable (K : Type*) [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  [hv : Valued K Γ₀]

/-- The valuation subring of a valued field is bounded, without a rank restriction. -/
theorem isBounded_valuationSubring : IsBounded (hv.v.valuationSubring : Set K) := by
  apply isBounded_iff.mpr
  intro U hU
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hU
  refine ⟨{x : K | hv.v.restrict x < γ.val},
    (Valued.hasBasis_nhds_zero K Γ₀).mem_of_mem (i := γ) trivial, ?_⟩
  rintro _ ⟨x, hx, y, hy, rfl⟩
  apply hγ
  have hy' : hv.v.restrict y ≤ 1 :=
    (hv.v.restrict_le_one_iff).mpr ((hv.v.mem_valuationSubring_iff y).mp hy)
  simpa only [Set.mem_ofPred_eq, map_mul] using
    (mul_le_of_le_one_right (zero_le : 0 ≤ hv.v.restrict x) hy').trans_lt hx

/-- A valued field with a nonzero topologically nilpotent element is a Tate ring. -/
theorem IsTateRing.of_valued {ϖ : K} (hϖ : IsTopologicallyNilpotent ϖ) (hϖ0 : ϖ ≠ 0) :
    IsTateRing K :=
  IsTateRing.of_isOpen_isBounded hv.v.valuationSubring.toSubring
    (Valued.isOpen_valuationSubring K) (isBounded_valuationSubring K)
    (isPseudoUniformizer_iff.mpr ⟨isUnit_iff_ne_zero.mpr hϖ0, hϖ⟩)

/-- The valuation subring is a ring of integral elements of a nonarchimedean valued field.
In particular the nonarchimedean hypothesis is supplied by any Tate-ring structure. -/
theorem isRingOfIntegralElements_valuationSubring [NonarchimedeanRing K] :
    IsRingOfIntegralElements hv.v.valuationSubring.toSubring where
  isOpen := Valued.isOpen_valuationSubring K
  isIntegrallyClosedIn := Subring.isIntegrallyClosedIn_iff.mpr fun _ hx ↦
    (Valuation.valuationSubring.integers hv.v).isIntegral_iff_v_le_one.mp hx
  le_powerBoundedSubring := fun _ hx ↦
    mem_powerBoundedSubring.mpr ((isBounded_valuationSubring K).isPowerBounded_of_mem hx)

/-- Completing the valuation subring gives the valuation subring of the completed field. -/
theorem completionPlus_valuationSubring :
    completionPlus hv.v.valuationSubring.toSubring =
      (Valued.v : Valuation (UniformSpace.Completion K) Γ₀).valuationSubring.toSubring := by
  rw [completionPlus_def]
  apply SetLike.coe_injective
  simp only [Subring.topologicalClosure_coe, Subring.coe_map]
  have hpre : (UniformSpace.Completion.coeRingHom : K →+* UniformSpace.Completion K) ⁻¹'
      ((Valued.v : Valuation (UniformSpace.Completion K) Γ₀).valuationSubring.toSubring :
        Set (UniformSpace.Completion K)) = (hv.v.valuationSubring.toSubring : Set K) := by
    ext x
    simp only [Set.mem_preimage, SetLike.mem_coe, ValuationSubring.mem_toSubring,
      Valuation.mem_valuationSubring_iff, UniformSpace.Completion.coe_coeRingHom,
      Valued.valuedCompletion_apply]
  refine le_antisymm (closure_minimal ?_ (Valued.isClosed_valuationSubring _)) ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact (Set.mem_preimage.mp (hpre.symm ▸ hx))
  · rw [← hpre]
    exact UniformSpace.Completion.denseRange_coe.subset_closure_image_preimage_of_isOpen
      (Valued.isOpen_valuationSubring _)

end TauCeti.Huber
