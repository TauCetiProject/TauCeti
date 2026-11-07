/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.LeftRegular.Basic
public import TauCeti.RepresentationTheory.Continuous.AlmostInvariant
public import TauCeti.GroupTheory.Amenable.Foelner
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Følner vectors in the discrete regular representation

The normalized indicator of a finite nonempty set is a unit vector in the counting-measure
regular representation. Its squared displacement is the relative size of the translation
boundary. Consequently Følner sets give almost invariant vectors. In contrast, on an infinite
group the regular representation has no nonzero invariant vectors: an invariant function is
constant, and a nonzero constant is not square summable.

These are the regular-representation obstruction to property (T) for infinite amenable groups.
The argument follows Bekka–de la Harpe–Valette, *Kazhdan's Property (T)*, Appendix G.5.
-/

public section

open MeasureTheory Finset
open scoped ENNReal Pointwise symmDiff

namespace MeasureTheory.Measure

variable {G 𝕜 : Type*} [Group G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G] [RCLike 𝕜] [DecidableEq G]

/-- The displacement of a finite-set indicator is the square root of the cardinality of its
translation boundary. -/
theorem _root_.Finset.norm_count_leftRegular_sub_indicatorConstLp (F : Finset G) (g : G) :
    ‖(count : Measure G).leftRegular 𝕜 𝕜 2 g
        (indicatorConstLp 2 F.measurableSet (by simp) (1 : 𝕜)) -
      indicatorConstLp 2 F.measurableSet (by simp) (1 : 𝕜)‖ =
        Real.sqrt (#((g • F) ∆ F) : ℝ) := by
  classical
  have hpre : (fun x : G ↦ g⁻¹ * x) ⁻¹' (F : Set G) = (g • F : Finset G) := by
    ext x
    simp only [Set.mem_preimage, Finset.mem_coe]
    rw [← Finset.mul_mem_smul_finset_iff g, mul_inv_cancel_left]
  rw [leftRegular_apply, Lp.indicatorConstLp_compMeasurePreserving, ← dist_eq_norm_sub,
    dist_indicatorConstLp_eq_norm, norm_indicatorConstLp (by simp) (by simp)]
  simp only [hpre, ← Finset.coe_symmDiff, measureReal_def, count_apply_finset,
    ENNReal.toReal_natCast, norm_one, one_mul, ENNReal.toReal_ofNat]
  exact (Real.sqrt_eq_rpow _).symm

omit [DecidableEq G] in
/-- Følner sets produce almost invariant unit vectors in the counting-measure regular
representation. No countability of the group is required. -/
theorem hasAlmostInvariantVectors_count_leftRegular (hG : TauCeti.HasFoelnerSets G) :
    ((count : Measure G).leftRegular 𝕜 𝕜 2).HasAlmostInvariantVectors := by
  classical
  rw [ContRepresentation.hasAlmostInvariantVectors_def]
  intro K ε hε
  obtain ⟨F, hF, hboundary⟩ := TauCeti.hasFoelnerSets_iff.mp hG K (ε ^ 2) (sq_pos_of_pos hε)
  let ξ : Lp 𝕜 2 (count : Measure G) :=
    indicatorConstLp 2 F.measurableSet (by simp) (1 : 𝕜)
  have hnorm : ‖ξ‖ = Real.sqrt (#F : ℝ) := by
    rw [norm_indicatorConstLp (by simp) (by simp)]
    simp [measureReal_def, Real.sqrt_eq_rpow]
  have hcard : (0 : ℝ) < #F := Nat.cast_pos.mpr hF.card_pos
  have hξ : ξ ≠ 0 := norm_ne_zero_iff.mp (by rw [hnorm]; positivity)
  refine ⟨(‖ξ‖⁻¹ : 𝕜) • ξ, norm_smul_inv_norm hξ, fun g hg ↦ ?_⟩
  rw [map_smul, ← smul_sub, norm_smul, norm_inv, RCLike.norm_coe_norm, hnorm]
  have hdisp : ‖(count : Measure G).leftRegular 𝕜 𝕜 2 g ξ - ξ‖ =
      Real.sqrt (#((g • F) ∆ F) : ℝ) := F.norm_count_leftRegular_sub_indicatorConstLp g
  rw [hdisp]
  have hroot : Real.sqrt (#((g • F) ∆ F) : ℝ) < ε * Real.sqrt (#F : ℝ) := by
    apply (sq_lt_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt hcard.le]
    exact hboundary g hg
  exact (inv_mul_lt_iff₀ (Real.sqrt_pos.mpr hcard)).mpr (by simpa [mul_comm] using hroot)

section Invariants

variable {R E : Type*} [NormedRing R] [NormedAddCommGroup E]
  [Module R E] [IsBoundedSMul R E]

omit [MeasurableSingletonClass G] [DecidableEq G] in
/-- For counting measure on an infinite group, the vector-valued regular representation on
`Lᵖ`, `1 ≤ p < ∞`, has only the zero invariant vector. -/
@[simp]
theorem invariants_count_leftRegular [Infinite G] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp' : p ≠ ∞) :
    ((count : Measure G).leftRegular R E p).invariants = ⊥ := by
  have hp : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  apply le_antisymm _ bot_le
  intro f hf
  have hconst (x : G) : f x = f 1 := by
    have hg := ae_count_iff.mp (coeFn_leftRegular (𝕜 := R) count p x f) x
    rw [hf x] at hg
    simpa using hg
  have hc : MemLp (fun _ : G ↦ f 1) p count :=
    (memLp_congr_ae (.of_forall hconst)).mp (Lp.memLp f)
  have hz : f 1 = 0 := by
    simpa [memLp_const_iff hp hp', count_apply_infinite Set.infinite_univ] using hc
  exact Lp.ext (.of_forall fun x ↦ by simp [hconst x, hz])

end Invariants

end MeasureTheory.Measure
