/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Lp
public import TauCeti.Analysis.Sobolev.W1p.Morrey

/-!
# Morrey's embedding into the Hölder Banach space

This file packages the continuous representative supplied by Morrey's inequality as a bounded
linear map from `W^{1,p}(ℝⁿ)` to the global Hölder space of exponent `1 - n / p` when
`n < p < ∞`.  The supremum part of the Hölder norm is controlled by averaging on unit balls:
a Hölder representative differs from its unit-ball average by at most its Hölder constant, while
Hölder's inequality controls the average by its `Lᵖ` norm.

## Main declarations

* `TauCeti.W1p.morreyEmbedding`: Morrey's embedding as a continuous linear map into
  `TauCeti.HolderSpace`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 7.17.
* L. C. Evans, *Partial Differential Equations*, §5.6.2, Theorem 4.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Set Module TopologicalSpace
open scoped Distributions ENNReal NNReal Gradient BoundedContinuousFunction

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]

private theorem W1p.morreyRepresentative_add (hp : (finrank ℝ E : ℝ≥0) < p)
    (u v : W1p mu ⊤ (p : ℝ≥0∞)) :
    W1p.morreyRepresentative (u + v) hp =
      W1p.morreyRepresentative u hp + W1p.morreyRepresentative v hp := by
  apply (Continuous.ae_eq_iff_eq mu (W1p.continuous_morreyRepresentative (u + v) hp)
    ((W1p.continuous_morreyRepresentative u hp).add
      (W1p.continuous_morreyRepresentative v hp))).1
  refine (W1p.value_ae_eq_morreyRepresentative (u + v) hp).symm.trans ?_
  have hadd := Lp.coeFn_add (W1p.value u) (W1p.value v)
  have hadd' : ((W1p.value u + W1p.value v :
      Lp ℝ (p : ℝ≥0∞) (mu.restrict (⊤ : Opens E))) : E → ℝ) =ᵐ[mu]
        W1p.value u + W1p.value v := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using hadd
  have hvalue : W1p.value (u + v) = W1p.value u + W1p.value v :=
    by simpa only [W1p.valueL_apply] using W1p.valueL.map_add u v
  rw [hvalue]
  exact hadd'.trans
      ((W1p.value_ae_eq_morreyRepresentative u hp).add
        (W1p.value_ae_eq_morreyRepresentative v hp))

private theorem W1p.morreyRepresentative_smul (hp : (finrank ℝ E : ℝ≥0) < p) (c : ℝ)
    (u : W1p mu ⊤ (p : ℝ≥0∞)) :
    W1p.morreyRepresentative (c • u) hp = c • W1p.morreyRepresentative u hp := by
  apply (Continuous.ae_eq_iff_eq mu (W1p.continuous_morreyRepresentative (c • u) hp)
    ((W1p.continuous_morreyRepresentative u hp).const_smul c)).1
  refine (W1p.value_ae_eq_morreyRepresentative (c • u) hp).symm.trans ?_
  have hsmul := Lp.coeFn_smul c (W1p.value u)
  have hsmul' : ((c • W1p.value u :
      Lp ℝ (p : ℝ≥0∞) (mu.restrict (⊤ : Opens E))) : E → ℝ) =ᵐ[mu]
        c • W1p.value u := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using hsmul
  have hvalue : W1p.value (c • u) = c • W1p.value u := by
    simpa only [W1p.valueL_apply] using W1p.valueL.map_smul c u
  rw [hvalue]
  exact hsmul'.trans
      ((W1p.value_ae_eq_morreyRepresentative u hp).const_smul c)

private def W1p.morreyHolderSpace (hp : (finrank ℝ E : ℝ≥0) < p)
    (u : W1p mu ⊤ (p : ℝ≥0∞)) : HolderSpace (1 - finrank ℝ E / p) E ℝ := by
  have hα : 0 < 1 - finrank ℝ E / p :=
    tsub_pos_of_lt ((div_lt_one (zero_le.trans_lt hp)).2 hp)
  have hmem : MemLp (W1p.morreyRepresentative u hp) (p : ℝ≥0∞) mu := by
    have hvalue : MemLp (W1p.value u) (p : ℝ≥0∞) mu := by
      simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.memLp (W1p.value u)
    exact MemLp.ae_eq (W1p.value_ae_eq_morreyRepresentative u hp) hvalue
  exact (W1p.holderWith_morreyRepresentative u hp).toHolderSpace hα Fact.out
    ENNReal.coe_ne_top hmem

private theorem W1p.morreyHolderSpace_apply (hp : (finrank ℝ E : ℝ≥0) < p)
    (u : W1p mu ⊤ (p : ℝ≥0∞)) (x : E) :
    W1p.morreyHolderSpace hp u x = W1p.morreyRepresentative u hp x := by
  rw [W1p.morreyHolderSpace]
  exact HolderWith.toHolderSpace_apply _ _ _ _ _ _

private def W1p.morreyEmbeddingLinearMap (hp : (finrank ℝ E : ℝ≥0) < p) :
    W1p mu ⊤ (p : ℝ≥0∞) →ₗ[ℝ] HolderSpace (1 - finrank ℝ E / p) E ℝ where
  toFun := W1p.morreyHolderSpace hp
  map_add' u v := by
    apply HolderSpace.toBoundedContinuousFunction_injective
    apply BoundedContinuousFunction.ext
    intro x
    rw [HolderSpace.toBoundedContinuousFunction_add]
    simp only [HolderSpace.toBoundedContinuousFunction_apply, W1p.morreyHolderSpace_apply,
      W1p.morreyRepresentative_add, Pi.add_apply, BoundedContinuousFunction.add_apply]
  map_smul' c u := by
    apply HolderSpace.toBoundedContinuousFunction_injective
    apply BoundedContinuousFunction.ext
    intro x
    rw [HolderSpace.toBoundedContinuousFunction_smul]
    simp only [HolderSpace.toBoundedContinuousFunction_apply, W1p.morreyHolderSpace_apply,
      W1p.morreyRepresentative_smul, Pi.smul_apply, smul_eq_mul,
      BoundedContinuousFunction.smul_apply, RingHom.id_apply]

private theorem W1p.norm_morreyHolderSpace_le_aux
    (hp : (finrank ℝ E : ℝ≥0) < p) (u : W1p mu ⊤ (p : ℝ≥0∞)) :
    ‖W1p.morreyHolderSpace hp u‖ ≤
      ((Real.toNNReal (2 ^ (finrank ℝ E + 1) /
            (finrank ℝ E * mu.real (ball 0 1)) *
            (finrank ℝ E * mu.real (ball 0 1) * (p - 1) / (p - finrank ℝ E)) ^
              (1 - 1 / (p : ℝ)) * 2 ^ (1 - finrank ℝ E / (p : ℝ))) *
                ‖W1p.gradient u‖₊) +
        mu (ball (0 : E) 1) ^ (-(((p : ℝ≥0∞).toReal)⁻¹)) *
          eLpNorm (W1p.morreyRepresentative u hp) (p : ℝ≥0∞) mu).toReal +
      (Real.toNNReal (2 ^ (finrank ℝ E + 1) /
        (finrank ℝ E * mu.real (ball 0 1)) *
        (finrank ℝ E * mu.real (ball 0 1) * (p - 1) / (p - finrank ℝ E)) ^
          (1 - 1 / (p : ℝ)) * 2 ^ (1 - finrank ℝ E / (p : ℝ))) *
            ‖W1p.gradient u‖₊) := by
  rw [W1p.morreyHolderSpace]
  exact HolderWith.norm_toHolderSpace_le _ _ _ _ _

private theorem W1p.exists_bound_morreyEmbeddingLinearMap
    (hp : (finrank ℝ E : ℝ≥0) < p) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : W1p mu ⊤ (p : ℝ≥0∞),
      ‖W1p.morreyEmbeddingLinearMap hp u‖ ≤ B * ‖u‖ := by
  let A : ℝ≥0 := Real.toNNReal (2 ^ (finrank ℝ E + 1) /
    (finrank ℝ E * mu.real (ball 0 1)) *
    (finrank ℝ E * mu.real (ball 0 1) * (p - 1) / (p - finrank ℝ E)) ^
      (1 - 1 / (p : ℝ)) * 2 ^ (1 - finrank ℝ E / (p : ℝ)))
  let V : ℝ≥0∞ := mu (ball (0 : E) 1) ^ (-(((p : ℝ≥0∞).toReal)⁻¹))
  refine ⟨(V.toReal + 2 * A : ℝ), by positivity, fun u => ?_⟩
  have hrep : eLpNorm (W1p.morreyRepresentative u hp) (p : ℝ≥0∞) mu =
      ‖W1p.value u‖ₑ := by
    calc
      _ = eLpNorm (W1p.value u) (p : ℝ≥0∞) mu :=
        eLpNorm_congr_ae (W1p.value_ae_eq_morreyRepresentative u hp).symm
      _ = _ := by
        rw [Lp.enorm_def]
        simp only [Opens.coe_top, Measure.restrict_univ]
  have hV : V ≠ ∞ := by
    exact ENNReal.rpow_ne_top_of_ne_zero (measure_ball_pos mu 0 one_pos).ne'
      measure_ball_lt_top.ne
  have hC : (A * ‖W1p.gradient u‖₊ : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  have hvalue : ‖W1p.value u‖ₑ ≠ ∞ := enorm_ne_top
  have hbase := W1p.norm_morreyHolderSpace_le_aux hp u
  have hbase' : ‖W1p.morreyEmbeddingLinearMap hp u‖ ≤
      ((A * ‖W1p.gradient u‖₊ : ℝ≥0) +
        V * eLpNorm (W1p.morreyRepresentative u hp) (p : ℝ≥0∞) mu).toReal +
          (A * ‖W1p.gradient u‖₊ : ℝ≥0) := by
    convert hbase using 1
    · rfl
    · rfl
  rw [hrep, ENNReal.coe_mul, ENNReal.toReal_add hC (ENNReal.mul_ne_top hV hvalue),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, toReal_enorm,
    NNReal.coe_mul, coe_nnnorm] at hbase'
  simp only [ENNReal.coe_toReal, coe_nnnorm] at hbase'
  calc
    ‖W1p.morreyEmbeddingLinearMap hp u‖ ≤
        (A : ℝ) * ‖W1p.gradient u‖ + V.toReal * ‖W1p.value u‖ +
      (A : ℝ) * ‖W1p.gradient u‖ := by
        simpa only [mul_assoc] using hbase'
    _ ≤ (A : ℝ) * ‖u‖ + V.toReal * ‖u‖ + (A : ℝ) * ‖u‖ := by
      gcongr
      · exact W1p.norm_gradient_le u
      · exact W1p.norm_value_le u
      · exact W1p.norm_gradient_le u
    _ = (V.toReal + 2 * A : ℝ) * ‖u‖ := by ring

/-- **Morrey's embedding into the Hölder Banach space.**  If `p` exceeds the dimension of `E`,
this continuous linear map sends a whole-space `W^{1,p}` function to its unique continuous
representative in the global Hölder space of exponent `1 - n / p`. -/
def W1p.morreyEmbedding (hp : (finrank ℝ E : ℝ≥0) < p) :
    W1p mu ⊤ (p : ℝ≥0∞) →L[ℝ] HolderSpace (1 - finrank ℝ E / p) E ℝ := by
  let h := W1p.exists_bound_morreyEmbeddingLinearMap (mu := mu) hp
  exact (W1p.morreyEmbeddingLinearMap hp).mkContinuous h.choose h.choose_spec.2

private theorem W1p.morreyEmbedding_apply (hp : (finrank ℝ E : ℝ≥0) < p)
    (u : W1p mu ⊤ (p : ℝ≥0∞)) :
    W1p.morreyEmbedding hp u = W1p.morreyHolderSpace hp u := by
  rw [W1p.morreyEmbedding]
  rfl

/-- Evaluating the Morrey embedding gives the canonical continuous representative. -/
theorem W1p.morreyEmbedding_apply_apply (hp : (finrank ℝ E : ℝ≥0) < p)
    (u : W1p mu ⊤ (p : ℝ≥0∞)) (x : E) :
    W1p.morreyEmbedding hp u x = W1p.morreyRepresentative u hp x := by
  rw [W1p.morreyEmbedding_apply, W1p.morreyHolderSpace_apply]

/-- The Hölder function produced by Morrey's embedding represents the original Sobolev value. -/
theorem W1p.value_ae_eq_morreyEmbedding (hp : (finrank ℝ E : ℝ≥0) < p)
    (u : W1p mu ⊤ (p : ℝ≥0∞)) :
    W1p.value u =ᵐ[mu] W1p.morreyEmbedding hp u := by
  filter_upwards [W1p.value_ae_eq_morreyRepresentative u hp] with x hx
  simpa only [W1p.morreyEmbedding_apply_apply] using hx

/-- Morrey's continuous linear map is an embedding: the continuous representative determines its
Sobolev class. -/
theorem W1p.morreyEmbedding_injective (hp : (finrank ℝ E : ℝ≥0) < p) :
    Function.Injective (W1p.morreyEmbedding (mu := mu) hp) := by
  intro u v huv
  apply W1p.ext_value
  apply Lp.ext
  have hae : W1p.value u =ᵐ[mu] W1p.value v := by
    filter_upwards [W1p.value_ae_eq_morreyEmbedding hp u,
      W1p.value_ae_eq_morreyEmbedding hp v] with x hu hv
    rw [hu, hv]
    exact congrArg (fun g : HolderSpace (1 - finrank ℝ E / p) E ℝ => g x) huv
  simpa only [Opens.coe_top, Measure.restrict_univ] using hae

end TauCeti
