/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import TauCeti.NumberTheory.Padics.Measure.ExtendCoefficients.Pseudomeasure
public import TauCeti.NumberTheory.Padics.WeightSpace.Measure

/-!
# Pseudomeasures on weight discs

A pseudomeasure on the p-adic units can be evaluated at every nontrivial weight by clearing a
Dirac difference. On a disc with nontrivial finite character, a torsion element gives a constant
nonzero clearing factor. On the trivial finite-character disc the principal generator gives the
disc coordinate as clearing factor, so the only possible pole is simple and at the origin.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, Remark 3.47.
-/

public noncomputable section

open AbstractMeasure ContinuousMonoidHom TauCeti.Iwasawa
open scoped AbstractMeasure

namespace TauCeti.WeightSpace

variable {p : ℕ} [Fact p.Prime] {O K : Type*}
  [CommRing O] [TopologicalSpace O] [IsTopologicalRing O] [T0Space O]

local notation "M" => D(ℤ_[p]ˣ, O)
local notation "δ" => (diracHom (G := ℤ_[p]ˣ) (R := O))
local notation "P" => pseudomeasures δ (FractionRing M)

variable [Monoid K] [TopologicalSpace K] in
private theorem weightTest_ne_one (κ : {κ : WeightSpace p K // κ ≠ 1}) :
    κ.val.weightTest ≠ 1 := by
  have hone : (1 : WeightSpace p K).weightTest = 1 := by
    ext u
    simp
  exact fun h ↦ κ.property (weightTest_injective (h.trans hone.symm))

section Evaluation

variable [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
  (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ 1)

/-- The function of a pseudomeasure on nontrivial weights, obtained from scalar-valued character
evaluation after extending coefficients along `j`. -/
def pseudoMeasureFun : P →+ ({κ : WeightSpace p K // κ ≠ 1} → K) :=
  AddMonoidHom.pi fun κ ↦ κ.val.weightTest.extendedPseudoCharacterEval j hj (FractionRing M)
    (weightTest_ne_one κ)

/-- Multiplying the value of a pseudomeasure by a Dirac difference evaluated at the weight gives
the integral of its cleared numerator. -/
theorem pseudoMeasureFun_spec (z : P) (κ : {κ : WeightSpace p K // κ ≠ 1}) (g : ℤ_[p]ˣ) :
    ((κ.val g : K) - 1) * pseudoMeasureFun j hj z κ =
      κ.val.weightTest.extendedCharacterRingHom j hj (numerator δ (FractionRing M) g z) := by
  simpa only [pseudoMeasureFun, AddMonoidHom.pi_apply, weightTest_apply] using
    κ.val.weightTest.extendedPseudoCharacterEval_spec j hj (FractionRing M)
      (weightTest_ne_one κ) g z

/-- Any group element whose weight value differs from one computes the same pseudomeasure value. -/
theorem pseudoMeasureFun_eq_div (z : P) (κ : {κ : WeightSpace p K // κ ≠ 1}) {g : ℤ_[p]ˣ}
    (hg : (κ.val g : K) ≠ 1) :
    pseudoMeasureFun j hj z κ =
      κ.val.weightTest.extendedCharacterRingHom j hj (numerator δ (FractionRing M) g z) /
        ((κ.val g : K) - 1) := by
  simpa only [pseudoMeasureFun, AddMonoidHom.pi_apply, weightTest_apply] using
    κ.val.weightTest.extendedPseudoCharacterEval_eq_div j hj (FractionRing M)
      (weightTest_ne_one κ) (g := g) (by simpa only [weightTest_apply] using hg) z

/-- Evaluation of an integral measure as a pseudomeasure agrees with its weight integral. -/
@[simp]
theorem pseudoMeasureFun_integral (μ : M) (κ : {κ : WeightSpace p K // κ ≠ 1}) :
    pseudoMeasureFun j hj (integral δ (FractionRing M) μ) κ =
      κ.val.weightTest.extendedCharacterRingHom j hj μ := by
  simp [pseudoMeasureFun]

/-- Measure convolution acts on pseudomeasure functions by pointwise multiplication by the
measure integral. -/
theorem pseudoMeasureFun_smul (μ : M) (z : P) (κ : {κ : WeightSpace p K // κ ≠ 1}) :
    pseudoMeasureFun j hj (μ • z) κ =
      κ.val.weightTest.extendedCharacterRingHom j hj μ * pseudoMeasureFun j hj z κ := by
  simp [pseudoMeasureFun, extendedPseudoCharacterEval_smul]

/-- Multiplication by the principal disc coordinate clears the denominator at the principal
generator, including at weights with zero coordinate and nontrivial finite character. -/
theorem coord_mul_pseudoMeasureFun (z : P) (κ : {κ : WeightSpace p K // κ ≠ 1}) :
    κ.val.coord * pseudoMeasureFun j hj z κ =
      κ.val.weightTest.extendedCharacterRingHom j hj
        (numerator δ (FractionRing M) (padicUnitsGenerator p) z) := by
  rw [coord_def, pseudoMeasureFun_spec]

end Evaluation

section Analytic

variable [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  [Algebra ℤ_[p] K] [IsBoundedSMul ℤ_[p] K]
  (j : O →+* K) (hj : ∀ a, ‖j a‖ ≤ 1)

/-- The pseudomeasure function on a disc with nontrivial finite character admits an analytic
representative on the entire disc. -/
theorem exists_analyticOnNhd_pseudoMeasureFun (z : P)
    {η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Kˣ} (hη : η ≠ 1) :
    ∃ f : K → K, AnalyticOnNhd K f (Metric.ball 0 1) ∧
      ∀ (t : K) (ht : ‖t‖ < 1)
        (hκ : ofCoord η t (tendsto_pow_atTop_nhds_zero_of_norm_lt_one ht) ≠ 1),
        f t = pseudoMeasureFun j hj z ⟨_, hκ⟩ := by
  obtain ⟨d, hd⟩ : ∃ d, (η d : K) ≠ 1 := by
    obtain ⟨d, hd⟩ := DFunLike.ne_iff.mp hη
    exact ⟨d, fun h ↦ hd (Units.ext (by simpa using h))⟩
  let g := padicUnitsSection p d
  obtain ⟨F, hF, heval⟩ :=
    (extendCoefficients j hj (numerator δ (FractionRing M) g z)).exists_analyticOnNhd_weightDisc η
  refine ⟨fun t ↦ F t / ((η d : K) - 1), fun t ht ↦ (hF t ht).div analyticAt_const
    (sub_ne_zero.mpr hd), fun t ht hκ ↦ ?_⟩
  have hval : (ofCoord η t (tendsto_pow_atTop_nhds_zero_of_norm_lt_one ht) g : K) = η d := by
    rw [← finiteChar_apply, finiteChar_ofCoord]
  rw [pseudoMeasureFun_eq_div j hj z ⟨_, hκ⟩ (g := g) (hval.trans_ne hd)]
  simp only [heval t ht, hval, extendedCharacterRingHom_apply, characterIntegralAlgHom_apply]

/-- On the trivial finite-character disc, multiplying the pseudomeasure function by the disc
coordinate extends analytically through the trivial weight. -/
theorem exists_analyticOnNhd_mul_pseudoMeasureFun (z : P) :
    ∃ f : K → K, AnalyticOnNhd K f (Metric.ball 0 1) ∧
      ∀ (t : K) (ht : ‖t‖ < 1)
        (hκ : ofCoord (p := p) 1 t (tendsto_pow_atTop_nhds_zero_of_norm_lt_one ht) ≠ 1),
        f t = t * pseudoMeasureFun j hj z ⟨_, hκ⟩ := by
  obtain ⟨F, hF, heval⟩ := (extendCoefficients j hj
    (numerator δ (FractionRing M) (padicUnitsGenerator p) z)).exists_analyticOnNhd_weightDisc 1
  refine ⟨F, hF, fun t ht hκ ↦ ?_⟩
  let κ : {κ : WeightSpace p K // κ ≠ 1} := ⟨_, hκ⟩
  have hcoord : κ.val.coord = t := coord_ofCoord ..
  have hcleared := coord_mul_pseudoMeasureFun j hj z κ
  rw [hcoord] at hcleared
  simpa only [extendedCharacterRingHom_apply, characterIntegralAlgHom_apply, κ, heval t ht]
    using hcleared.symm

/-- Each disc admits a meromorphic representative of the pseudomeasure function. It is analytic
away from the origin, is analytic even at the origin on a nontrivial finite-character disc, and
has order at least `-1` at the origin. -/
theorem exists_meromorphicOn_pseudoMeasureFun (z : P)
    (η : (ZMod (p ^ padicUnitsDepth p))ˣ →* Kˣ) :
    ∃ f : K → K, MeromorphicOn f (Metric.ball 0 1) ∧
      AnalyticOnNhd K f (Metric.ball 0 1 \ {0}) ∧
      (η ≠ 1 → AnalyticAt K f 0) ∧
      (-1 : WithTop ℤ) ≤ meromorphicOrderAt f 0 ∧
      ∀ (t : K) (ht : ‖t‖ < 1)
        (hκ : ofCoord η t (tendsto_pow_atTop_nhds_zero_of_norm_lt_one ht) ≠ 1),
        f t = pseudoMeasureFun j hj z ⟨_, hκ⟩ := by
  have h0 : (0 : K) ∈ Metric.ball (0 : K) 1 := Metric.mem_ball_self zero_lt_one
  have hneg : (-1 : WithTop ℤ) ≤ 0 := WithTop.coe_le_coe.mpr (by decide : (-1 : ℤ) ≤ 0)
  by_cases hη : η = 1
  · subst η
    obtain ⟨F, hF, heval⟩ := exists_analyticOnNhd_mul_pseudoMeasureFun j hj z
    refine ⟨F / _root_.id, fun t ht ↦ (hF t ht).meromorphicAt.div analyticAt_id.meromorphicAt,
      fun t ht ↦ (hF t ht.1).div analyticAt_id ht.2, by simp, ?_, fun t ht hκ ↦ ?_⟩
    · rw [meromorphicOrderAt_div (hF 0 h0).meromorphicAt analyticAt_id.meromorphicAt,
        meromorphicOrderAt_id, sub_eq_add_neg]
      simpa using add_le_add_left (hF 0 h0).meromorphicOrderAt_nonneg (-1)
    · have ht₀ : t ≠ 0 := by
        intro ht₀
        apply hκ
        apply ext_finiteChar_coord _ (by simp [ht₀])
        ext d
        simp [finiteChar_apply]
      simp only [Pi.div_apply, id_eq, heval t ht hκ]
      exact mul_div_cancel_left₀ _ ht₀
  · obtain ⟨F, hF, heval⟩ := exists_analyticOnNhd_pseudoMeasureFun j hj z hη
    exact ⟨F, fun t ht ↦ (hF t ht).meromorphicAt, fun t ht ↦ hF t ht.1,
      fun _ ↦ hF 0 h0, hneg.trans
        (hF 0 h0).meromorphicOrderAt_nonneg, heval⟩

end Analytic

-- At a dyadic sign weight with zero principal coordinate, the scalar difference at `-1`
-- still evaluates the pseudomeasure.
example (κ : {κ : WeightSpace 2 ℚ_[2] // κ ≠ 1}) (hκ : (κ.val (-1) : ℚ_[2]) = -1)
    (hcoord : κ.val.coord = 0) (z : unitsPseudomeasures 2) :
    let j := PadicInt.Coe.ringHom (p := 2)
    let hj := PadicInt.norm_coe_ringHom_le_one (p := 2)
    let clear := numerator (diracHom (G := ℤ_[2]ˣ) (R := ℤ_[2]))
      (FractionRing D(ℤ_[2]ˣ, ℤ_[2]))
    pseudoMeasureFun j hj z κ =
        κ.val.weightTest.extendedCharacterRingHom j hj (clear (-1) z) / (-2) ∧
      κ.val.weightTest.extendedCharacterRingHom j hj (clear (padicUnitsGenerator 2) z) = 0 := by
  have hne : (κ.val (-1) : ℚ_[2]) ≠ 1 := by rw [hκ]; norm_num
  dsimp only
  constructor
  · rw [pseudoMeasureFun_eq_div _ _ z κ hne, hκ]
    norm_num
  · simpa only [hcoord, zero_mul] using
      (coord_mul_pseudoMeasureFun PadicInt.Coe.ringHom PadicInt.norm_coe_ringHom_le_one z κ).symm

end TauCeti.WeightSpace
