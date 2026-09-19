/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Normed
public import TauCeti.Analysis.Sobolev.W1p.Morrey

import TauCeti.MeasureTheory.Function.Lp.BallAverage

/-!
# Morrey's embedding into the Hölder Banach space

This file packages the continuous representative supplied by Morrey's inequality as a bounded
linear map from `W^{1,p}(ℝⁿ)` to the global Hölder space of exponent `1 - n / p` when
`n < p < ∞`.  The supremum part of the Hölder norm is controlled by averaging on unit balls:
a Hölder representative differs from its unit-ball average by at most its Hölder constant, while
Hölder's inequality controls the average by its `Lᵖ` norm.

## Main declarations

* `HolderWith.enorm_le_add_eLpNorm`: a global Hölder function in `Lᵖ` has a pointwise bound.
* `TauCeti.W1p.morreyRepresentative`: the unique continuous representative of a whole-space
  Sobolev function in the supercritical range.
* `TauCeti.W1p.morreyEmbedding`: Morrey's embedding as a continuous linear map into
  `TauCeti.HolderSpace`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 7.17.
* L. C. Evans, *Partial Differential Equations*, §5.6.2, Theorem 4.
-/

public section

noncomputable section

namespace HolderWith

open MeasureTheory Metric Set
open scoped ENNReal NNReal BoundedContinuousFunction
open TauCeti

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
  [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {mu : Measure E} [mu.IsAddHaarMeasure] {g : E → F} {C α : ℝ≥0} {p : ℝ≥0∞}

/-- A globally Hölder function with finite `Lᵖ` norm is pointwise bounded.  At unit scale the
bound is the sum of its Hölder constant and the `Lᵖ` norm multiplied by the inverse `p`-th power
of the volume of the unit ball. -/
theorem enorm_le_add_eLpNorm (hg : HolderWith C α g) (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hgLp : MemLp g p mu) (x : E) :
    ‖g x‖ₑ ≤ C + mu (ball (0 : E) 1) ^ (-(p.toReal)⁻¹) * eLpNorm g p mu := by
  have hdev : ‖ballAverage mu 1 g x - g x‖ₑ ≤ C := by
    rw [ballAverage_sub_self hp hgLp one_pos]
    rw [setAverage_eq, enorm_smul]
    refine (mul_le_mul le_rfl (enorm_integral_le_lintegral_enorm _) bot_le bot_le).trans ?_
    calc
      _ ≤ ‖(mu.real (ball (0 : E) 1))⁻¹‖ₑ *
          ∫⁻ e in ball (0 : E) 1, (C : ℝ≥0∞) ∂mu := by
        refine mul_le_mul le_rfl (lintegral_mono_ae ?_) bot_le bot_le
        filter_upwards [ae_restrict_mem measurableSet_ball] with e he
        rw [← edist_eq_enorm_sub]
        refine (hg (x + e) x).trans ?_
        have he' : edist (x + e) x ≤ 1 := by
          simpa only [edist_dist, ENNReal.ofReal_le_one, dist_eq_norm, add_sub_cancel_left,
            norm_neg] using (mem_ball_zero_iff.1 he).le
        exact (mul_le_mul le_rfl (ENNReal.rpow_le_one he' (by positivity)) bot_le bot_le).trans
          (mul_one _).le
      _ = ‖(mu.real (ball (0 : E) 1))⁻¹‖ₑ * mu (ball (0 : E) 1) * C := by
        rw [setLIntegral_const]
        ac_rfl
      _ = C := by
        have hinv : ‖(mu.real (ball (0 : E) 1))⁻¹‖ₑ =
            (mu (ball (0 : E) 1))⁻¹ := by
          rw [Real.enorm_eq_ofReal (by positivity), measureReal_def, ← ENNReal.toReal_inv,
            ENNReal.ofReal_toReal
              (ENNReal.inv_ne_top.2 (measure_ball_pos mu 0 one_pos).ne')]
        rw [hinv]
        simp only [ENNReal.inv_mul_cancel (measure_ball_pos mu 0 one_pos).ne'
          measure_ball_lt_top.ne, one_mul]
  calc
    ‖g x‖ₑ = edist (g x) 0 := by rw [edist_zero_right]
    _ ≤ edist (g x) (ballAverage mu 1 g x) + ‖ballAverage mu 1 g x‖ₑ := by
      simpa only [edist_zero_right] using edist_triangle (g x) (ballAverage mu 1 g x) 0
    _ ≤ C + mu (ball (0 : E) 1) ^ (-(p.toReal)⁻¹) * eLpNorm g p mu :=
      add_le_add (by rw [edist_comm]; simpa only [edist_eq_enorm_sub] using hdev)
        (enorm_ballAverage_le hp hp' hgLp.aestronglyMeasurable one_pos x)

/-- A global Hölder function in `Lᵖ`, bundled as an element of the Hölder Banach space. -/
def toHolderSpace (hg : HolderWith C α g) (hα : 0 < α) (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hgLp : MemLp g p mu) : TauCeti.HolderSpace α E F := by
  let R : ℝ≥0∞ := C + mu (ball (0 : E) 1) ^ (-(p.toReal)⁻¹) * eLpNorm g p mu
  have hR : R ≠ ∞ := by
    rw [← lt_top_iff_ne_top]
    change (C : ℝ≥0∞) +
        mu (ball (0 : E) 1) ^ (-(p.toReal)⁻¹) * eLpNorm g p mu < ∞
    rw [ENNReal.add_lt_top]
    exact ⟨ENNReal.coe_lt_top, ENNReal.mul_lt_top
        (lt_top_iff_ne_top.2 (ENNReal.rpow_ne_top_of_ne_zero
          (measure_ball_pos mu 0 one_pos).ne' measure_ball_lt_top.ne)) hgLp.eLpNorm_lt_top⟩
  have hpoint (x : E) : ‖g x‖ ≤ R.toReal := by
    simpa only [toReal_enorm] using (ENNReal.toReal_le_toReal enorm_ne_top hR).2
      (hg.enorm_le_add_eLpNorm hp hp' hgLp x)
  let G : E →ᵇ F := BoundedContinuousFunction.mkOfBound ⟨g, hg.continuous hα⟩
    (2 * R.toReal) (BoundedContinuousFunction.dist_le_two_norm' hpoint)
  exact TauCeti.HolderSpace.ofBoundedContinuousFunction G (by
    change MemHolder α g
    exact hg.memHolder)

/-- The Hölder-space bundling does not change the underlying function. -/
@[simp]
theorem toHolderSpace_apply (hg : HolderWith C α g) (hα : 0 < α) (hp : 1 ≤ p)
    (hp' : p ≠ ∞) (hgLp : MemLp g p mu) (x : E) :
    hg.toHolderSpace hα hp hp' hgLp x = g x := by
  rw [← TauCeti.HolderSpace.toBoundedContinuousFunction_apply]
  rw [toHolderSpace, TauCeti.HolderSpace.toBoundedContinuousFunction_ofBoundedContinuousFunction]
  rfl

/-- The Hölder-space norm is controlled by the pointwise bound and the given Hölder
constant. -/
theorem norm_toHolderSpace_le (hg : HolderWith C α g) (hα : 0 < α) (hp : 1 ≤ p)
    (hp' : p ≠ ∞) (hgLp : MemLp g p mu) :
    ‖hg.toHolderSpace hα hp hp' hgLp‖ ≤
      (C + mu (ball (0 : E) 1) ^ (-(p.toReal)⁻¹) * eLpNorm g p mu).toReal + C := by
  rw [TauCeti.HolderSpace.norm_def]
  apply add_le_add
  · rw [BoundedContinuousFunction.norm_le (by positivity)]
    intro x
    rw [TauCeti.HolderSpace.toBoundedContinuousFunction_apply, toHolderSpace_apply]
    have hx := (ENNReal.toReal_le_toReal enorm_ne_top (by
      rw [← lt_top_iff_ne_top, ENNReal.add_lt_top]
      exact ⟨ENNReal.coe_lt_top, ENNReal.mul_lt_top
          (lt_top_iff_ne_top.2 (ENNReal.rpow_ne_top_of_ne_zero
            (measure_ball_pos mu 0 one_pos).ne' measure_ball_lt_top.ne))
          hgLp.eLpNorm_lt_top⟩)).2 (hg.enorm_le_add_eLpNorm hp hp' hgLp x)
    simpa only [toReal_enorm] using hx
  · have hb : HolderWith C α (fun x => hg.toHolderSpace hα hp hp' hgLp x) := by
      intro x y
      simpa only [toHolderSpace_apply] using hg x y
    have heq : ((hg.toHolderSpace hα hp hp' hgLp).toBoundedContinuousFunction : E → F) =
        fun x => hg.toHolderSpace hα hp hp' hgLp x := by
      funext x
      rw [TauCeti.HolderSpace.toBoundedContinuousFunction_apply]
    rw [heq]
    exact_mod_cast hb.nnholderNorm_le

end HolderWith

namespace TauCeti

open MeasureTheory Metric Set Module TopologicalSpace
open scoped Distributions ENNReal NNReal Gradient BoundedContinuousFunction

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]

/-- The canonical continuous representative of a whole-space Sobolev function in Morrey's
supercritical range.  It is canonical because two continuous representatives that agree almost
everywhere for Haar measure agree everywhere. -/
def W1p.morreyRepresentative (u : W1p mu ⊤ (p : ℝ≥0∞)) (hp : (finrank ℝ E : ℝ≥0) < p) :
    E → ℝ :=
  Classical.choose (W1p.exists_holderWith_ae_eq_value hp u)

/-- Morrey's estimate for the canonical representative. -/
theorem W1p.morreyRepresentative_holderWith (u : W1p mu ⊤ (p : ℝ≥0∞))
    (hp : (finrank ℝ E : ℝ≥0) < p) :
    HolderWith (Real.toNNReal (2 ^ (finrank ℝ E + 1) / (finrank ℝ E * mu.real (ball 0 1)) *
        (finrank ℝ E * mu.real (ball 0 1) * (p - 1) / (p - finrank ℝ E)) ^
          (1 - 1 / (p : ℝ)) * 2 ^ (1 - finrank ℝ E / (p : ℝ))) *
          ‖W1p.gradient u‖₊)
      (1 - finrank ℝ E / p) (W1p.morreyRepresentative u hp) :=
  (Classical.choose_spec (W1p.exists_holderWith_ae_eq_value hp u)).1

/-- The canonical Morrey representative agrees almost everywhere with the Sobolev value. -/
theorem W1p.value_ae_eq_morreyRepresentative (u : W1p mu ⊤ (p : ℝ≥0∞))
    (hp : (finrank ℝ E : ℝ≥0) < p) :
    W1p.value u =ᵐ[mu] W1p.morreyRepresentative u hp :=
  (Classical.choose_spec (W1p.exists_holderWith_ae_eq_value hp u)).2

/-- The canonical Morrey representative is continuous. -/
theorem W1p.continuous_morreyRepresentative (u : W1p mu ⊤ (p : ℝ≥0∞))
    (hp : (finrank ℝ E : ℝ≥0) < p) : Continuous (W1p.morreyRepresentative u hp) :=
  (W1p.morreyRepresentative_holderWith u hp).continuous
    (tsub_pos_of_lt ((div_lt_one (zero_le.trans_lt hp)).2 hp))

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
  exact (W1p.morreyRepresentative_holderWith u hp).toHolderSpace hα Fact.out
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
  change ‖W1p.morreyEmbeddingLinearMap hp u‖ ≤
    ((A * ‖W1p.gradient u‖₊ : ℝ≥0) +
      V * eLpNorm (W1p.morreyRepresentative u hp) (p : ℝ≥0∞) mu).toReal +
        (A * ‖W1p.gradient u‖₊ : ℝ≥0) at hbase
  rw [hrep, ENNReal.coe_mul, ENNReal.toReal_add hC (ENNReal.mul_ne_top hV hvalue),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, toReal_enorm,
    NNReal.coe_mul, coe_nnnorm] at hbase
  calc
    ‖W1p.morreyEmbeddingLinearMap hp u‖ ≤
        (A : ℝ) * ‖W1p.gradient u‖ + V.toReal * ‖W1p.value u‖ +
          (A : ℝ) * ‖W1p.gradient u‖ := by simpa [mul_assoc] using hbase
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
