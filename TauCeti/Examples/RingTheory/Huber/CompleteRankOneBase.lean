/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import TauCeti.RingTheory.Huber.CompleteRankOneBase.Basic

import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.RingTheory.Localization.FractionRing
import TauCeti.NumberTheory.Padics.Complex.Basic
import TauCeti.NumberTheory.Padics.Complex.MaximalIdeal
import TauCeti.RingTheory.Huber.CompleteRankOneBase.FractionRing
import TauCeti.RingTheory.Huber.Padic.Basic
import TauCeti.RingTheory.Valuation.AdicSeparated
import TauCeti.Topology.Algebra.Valued.NormedValued

/-!
# Examples of complete rank-one valuation bases

* `ℤ_[p]` with pseudouniformiser `p` satisfies `TauCeti.Huber.IsCompleteRankOneBase`, its fraction
  field `ℚ_[p]` is the localisation `ℤ_[p][1/p]`, and its valued fraction field is complete of rank
  one with integer ring topologically isomorphic to `ℤ_[p]`.
* `𝓞_ℂ_[p]` with pseudouniformiser `p` also satisfies `TauCeti.Huber.IsCompleteRankOneBase`, even
  though its maximal ideal is not finitely generated (`¬ IsNoetherianRing 𝓞_ℂ_[p]`).
* Neither `0` nor a unit can serve as pseudouniformiser, even over a field: the class records that
  `ϖ` is a genuine pseudouniformiser rather than only that the topology is adic.
-/

public section

namespace TauCeti.HuberExamples

open IsLocalRing TauCeti.Huber Topology
open scoped NNReal

/-- The `p`-adic integers form a complete rank-one valuation base with pseudouniformiser `p`. -/
theorem isCompleteRankOneBase_padicInt (p : ℕ) [Fact p.Prime] :
    IsCompleteRankOneBase ℤ_[p] (p : ℤ_[p]) where
  ringKrullDim_eq_one := IsDiscreteValuationRing.ringKrullDim_eq_one ℤ_[p]
  ne_zero := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  not_isUnit := (mem_maximalIdeal _).mp
    (_root_.PadicInt.maximalIdeal_eq_span_p (p := p) ▸ Ideal.mem_span_singleton_self _)
  isAdic := _root_.PadicInt.maximalIdeal_eq_span_p (p := p) ▸ _root_.PadicInt.isAdic_maximalIdeal
  isAdicComplete := _root_.PadicInt.maximalIdeal_eq_span_p (p := p) ▸ inferInstance

/-- The non-noetherian valuation ring `𝓞_ℂ_[p]` of `ℂ_p` forms a complete rank-one valuation base
with pseudouniformiser `p`. -/
theorem isCompleteRankOneBase_padicComplexInt (p : ℕ) [Fact p.Prime] :
    IsCompleteRankOneBase 𝓞_ℂ_[p] (p : 𝓞_ℂ_[p]) := by
  have hv := PadicComplexInt.integers_normedFieldValuation p
  have hp0 : (p : 𝓞_ℂ_[p]) ≠ 0 := fun h ↦
    (Fact.out : p.Prime).ne_zero (by simpa using congrArg Subtype.val h)
  have hp1 : ‖algebraMap 𝓞_ℂ_[p] ℂ_[p] (p : 𝓞_ℂ_[p])‖ < 1 := by
    simpa using PadicComplex.norm_p_lt_one p
  have hp_pos : 0 < ‖algebraMap 𝓞_ℂ_[p] ℂ_[p] (p : 𝓞_ℂ_[p])‖ :=
    norm_pos_iff.mpr ((map_ne_zero_iff _ hv.hom_inj).mpr hp0)
  have hnu : ¬ IsUnit (p : 𝓞_ℂ_[p]) := fun hu ↦
    hp1.ne (by simpa [NormedField.valuation_apply, ← NNReal.coe_eq_one] using hv.one_of_isUnit hu)
  refine {
    ringKrullDim_eq_one := ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.mpr
      ⟨fun hf ↦ let ⟨b, hb⟩ := hf.mul_inv_cancel hp0; hnu (IsUnit.of_mul_eq_one b hb),
        fun x hx y hy ↦ by
        refine hv.mem_radical_span_singleton_of_norm_lt_one ?_ hx
        have hy_ne : algebraMap 𝓞_ℂ_[p] ℂ_[p] y ≠ 0 → NormedField.valuation (y : ℂ_[p]) ≠ 1 :=
          fun hy0 h1 ↦ (mem_maximalIdeal _).mp hy (hv.isUnit_of_one (IsUnit.mk0 _ hy0) h1)
        by_cases hy0 : (y : ℂ_[p]) = 0
        · simp [Algebra.algebraMap_ofSubsemiring_apply, hy0]
        · have hlt := lt_of_le_of_ne (hv.map_le_one y) (hy_ne hy0)
          simpa [NormedField.valuation_apply, ← NNReal.coe_lt_one] using hlt⟩
    ne_zero := hp0
    not_isUnit := hnu
    isAdic := by
      rw [isAdic_iff]
      refine ⟨fun n ↦ ?_, fun s hs ↦ ?_⟩
      · have heq : ((Ideal.span {(p : 𝓞_ℂ_[p])} ^ n : Ideal 𝓞_ℂ_[p]) : Set 𝓞_ℂ_[p]) =
            Subtype.val ⁻¹'
              Metric.closedBall (0 : ℂ_[p]) (‖algebraMap 𝓞_ℂ_[p] ℂ_[p] (p : 𝓞_ℂ_[p])‖ ^ n) := by
          ext x
          simp [SetLike.mem_coe, hv.mem_span_singleton_pow_iff_norm_le, Metric.mem_closedBall,
            dist_zero_right]
        rw [heq]
        exact (IsUltrametricDist.isOpen_closedBall _ (pow_pos hp_pos n).ne').preimage
          continuous_subtypeVal
      · rw [nhds_subtype_eq_comap] at hs
        obtain ⟨U, hU, hUs⟩ := hs
        obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
        obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hp1
        refine ⟨n, fun x hx ↦ hUs (hball ?_)⟩
        rw [SetLike.mem_coe, hv.mem_span_singleton_pow_iff_norm_le] at hx
        simpa [Metric.mem_ball, dist_zero_right] using hx.trans_lt hn
    isAdicComplete := hv.isAdicComplete_span_singleton hp1 }

-- The element `0` is not a pseudouniformiser.
example (O : Type*) [CommRing O] [TopologicalSpace O] : ¬ IsCompleteRankOneBase O 0 :=
  fun h ↦ h.ne_zero rfl

-- A unit is not a pseudouniformiser, even over a field.
example (k : Type*) [Field k] [TopologicalSpace k] : ¬ IsCompleteRankOneBase k 1 :=
  fun h ↦ h.not_isUnit isUnit_one

-- Over a separated valuation ring, a nonzero element divides a power of the pseudouniformiser.
example {O : Type*} [CommRing O] [IsDomain O] [ValuationRing O] [TopologicalSpace O] (ϖ : O)
    [IsCompleteRankOneBase O ϖ] {a : O} (ha : a ≠ 0) : ∃ n : ℕ, a ∣ ϖ ^ n :=
  TauCeti.PreValuationRing.exists_dvd_pow_of_isHausdorff ha

-- Consequently `ℚ_[p]` is the localisation of `ℤ_[p]` away from `p`, and the canonical valuation
-- on `ℚ_[p]` has rank one and complete valued field `WithVal` whose integer ring recovers `ℤ_[p]`.
example (p : ℕ) [Fact p.Prime] :
    IsLocalization.Away (p : ℤ_[p]) ℚ_[p] ∧
      Nonempty (ValuationRing.valuation ℤ_[p] ℚ_[p]).RankOne ∧
      CompleteSpace (WithVal (ValuationRing.valuation ℤ_[p] ℚ_[p])) := by
  have := isCompleteRankOneBase_padicInt p
  exact ⟨IsCompleteRankOneBase.isLocalization_away (p : ℤ_[p]) ℚ_[p],
    IsCompleteRankOneBase.nonempty_rankOne_valuation (p : ℤ_[p]) ℚ_[p],
    IsCompleteRankOneBase.completeSpace_withVal (p : ℤ_[p]) ℚ_[p]⟩

-- `𝓞_ℂ_[p]` satisfies `IsCompleteRankOneBase` with pseudouniformiser `p` yet is not noetherian.
example (p : ℕ) [Fact p.Prime] :
    IsCompleteRankOneBase 𝓞_ℂ_[p] (p : 𝓞_ℂ_[p]) ∧ ¬ IsNoetherianRing 𝓞_ℂ_[p] :=
  ⟨isCompleteRankOneBase_padicComplexInt p,
    fun hnoeth ↦ TauCeti.PadicComplexInt.not_fg_maximalIdeal p (hnoeth.noetherian _)⟩

end TauCeti.HuberExamples
