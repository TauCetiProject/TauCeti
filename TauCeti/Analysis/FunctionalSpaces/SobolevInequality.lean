/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.Analysis.Sobolev.SmoothCutoff

/-!
# Sobolev inequalities for smooth functions

This file contains two inequalities bounding a smooth function by an integral of its derivatives.

## The Gagliardo–Nirenberg–Sobolev inequality for integrable functions

Mathlib's Gagliardo–Nirenberg–Sobolev inequality `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_one`
bounds `‖u‖_p`, for `p = n / (n - 1)`, by `C ‖Du‖₁` for a compactly supported `C¹` function `u`
on a space of dimension `n ≥ 2`, where `C = MeasureTheory.eLpNormLESNormFDerivOneConst μ p`.
This file removes the compact support hypothesis: the same inequality, with the same constant,
holds for every integrable `C¹` function, with `‖Du‖₁` finite or infinite.

The constant is positive (`TauCeti.eLpNormLESNormFDerivOneConst_pos`), as one sees by applying
the inequality to a bump function; this is what makes the inequality meaningful when `‖Du‖₁` is
infinite. When `‖Du‖₁` is finite, the compactly supported functions `χ(x / R) u(x)`, for a bump
function `χ` equal to one near zero, converge to `u` in `L¹` and their derivatives converge to
`Du` in `L¹` (`TauCeti.tendsto_eLpNorm_iteratedFDeriv_cutoff_sub`). Mathlib's inequality holds
for each of them, and Fatou's lemma along an almost everywhere convergent subsequence passes it
to `u`.

## The critical case: a bound in the supremum norm

On a real inner product space `E` of dimension `n`, every compactly supported `Cⁿ` function `u`
satisfies

`‖u x‖ ≤ ∫ ‖Dⁿu y‖ dy` for every `x`

(`HasCompactSupport.eNorm_le_lintegral_iteratedFDeriv`), with constant `1` and the Lebesgue
measure `volume` of `E`. This is the endpoint `p = 1`, `k = n` of the Sobolev embeddings
`W^{k,p} ⊆ C⁰`, which hold for `kp > n` and fail for `kp = n` when `p > 1`. In coordinates of an
orthonormal basis `e₁, …, eₙ` it is the fundamental theorem of calculus applied once in each
coordinate: `|u x| ≤ ∫ |∂ᵢu|` along the line through `x` in the direction `eᵢ`, since `u` vanishes
at infinity on that line. Iterating over the `n` coordinates bounds `|u x|` by the integral of
`|∂ₙ ⋯ ∂₁u|` over all of `E`, and `|∂ₙ ⋯ ∂₁u y| ≤ ‖Dⁿu y‖` since the `eᵢ` are unit vectors.

## Main results

* `TauCeti.eLpNormLESNormFDerivOneConst_pos`: the constant of the Gagliardo–Nirenberg–Sobolev
  inequality is positive.
* `TauCeti.eLpNorm_le_eLpNorm_fderiv_one_of_integrable`: the Gagliardo–Nirenberg–Sobolev
  inequality for integrable `C¹` functions.
* `HasCompactSupport.eNorm_le_lintegral_iteratedFDeriv`: the bound `‖u x‖ ≤ ∫ ‖Dⁿu‖` for
  compactly supported `Cⁿ` functions on a space of dimension `n`.
* `HasCompactSupport.eNorm_le_lmarginal_iteratedFDeriv`: its iterated form over a finite set of
  coordinates, along vectors of norm at most one.

## References

* L. C. Evans, *Partial Differential Equations*, §5.6.1, Theorem 1.
* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 4.12, Part I, Case A, for
  `p = 1` and `m = n`.
-/

public section

namespace TauCeti

open MeasureTheory Module Filter
open scoped ENNReal NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The constant `MeasureTheory.eLpNormLESNormFDerivOneConst μ p` of the Gagliardo–Nirenberg–
Sobolev inequality `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_one` is positive. -/
theorem eLpNormLESNormFDerivOneConst_pos {p : ℝ≥0}
    (hp : NNReal.HolderConjugate (finrank ℝ E) p) : 0 < eLpNormLESNormFDerivOneConst μ p := by
  let χ : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  refine pos_iff_ne_zero.2 fun h => ?_
  have hle := eLpNorm_le_eLpNorm_fderiv_one μ (χ.contDiff (n := 1)) χ.hasCompactSupport hp
  rw [h, ENNReal.coe_zero, zero_mul, nonpos_iff_eq_zero,
    eLpNorm_eq_zero_iff (by exact_mod_cast hp.symm.pos.ne')] at hle
  -- The bump vanishes almost everywhere, but its support is the open ball `ball 0 2`.
  refine (Metric.measure_ball_pos μ (0 : E) two_pos).ne' ?_
  rw [← χ.support_eq]
  exact ae_iff.1 hle

/-- **The Gagliardo–Nirenberg–Sobolev inequality for integrable functions.** Let `E` have
dimension `n ≥ 2` and let `p = n / (n - 1)`. Every integrable `C¹` function `u` satisfies
`‖u‖_p ≤ C ‖Du‖₁`, with `‖Du‖₁` finite or infinite, where `C` is the constant
`MeasureTheory.eLpNormLESNormFDerivOneConst μ p` of the compactly supported case
`MeasureTheory.eLpNorm_le_eLpNorm_fderiv_one`. -/
theorem eLpNorm_le_eLpNorm_fderiv_one_of_integrable {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {u : E → F} (hu : ContDiff ℝ 1 u) (hi : Integrable u μ) {p : ℝ≥0}
    (hp : NNReal.HolderConjugate (finrank ℝ E) p) :
    eLpNorm u p μ ≤ eLpNormLESNormFDerivOneConst μ p * eLpNorm (fderiv ℝ u) 1 μ := by
  set C := eLpNormLESNormFDerivOneConst μ p
  rcases eq_or_ne (eLpNorm (fderiv ℝ u) 1 μ) ∞ with htop | htop
  · rw [htop, ENNReal.mul_top (by exact_mod_cast (eLpNormLESNormFDerivOneConst_pos μ hp).ne')]
    exact le_top
  obtain ⟨g, ε, hg, hgc, hval, hε, hderiv⟩ :=
    exists_contDiff_hasCompactSupport_tendsto_eLpNorm_fderiv hu hi htop
  have hbound : Tendsto (fun n => (C : ℝ≥0∞) * (eLpNorm (fderiv ℝ u) 1 μ + ε n)) atTop
      (𝓝 (C * eLpNorm (fderiv ℝ u) 1 μ)) := by
    simpa using ENNReal.Tendsto.const_mul (tendsto_const_nhds.add hε)
      (Or.inr ENNReal.coe_ne_top)
  -- Fatou's lemma along an almost everywhere convergent subsequence.
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero hval).exists_seq_tendsto_ae
  refine (Lp.eLpNorm_lim_le_liminf_eLpNorm (fun n => (hg (ns n)).continuous.aestronglyMeasurable)
    u hi.aestronglyMeasurable hae).trans ?_
  refine (liminf_le_liminf (.of_forall fun n => ?_)).trans_eq
    (hbound.comp hns.tendsto_atTop).liminf_eq
  exact (eLpNorm_le_eLpNorm_fderiv_one μ (hg (ns n)) (hgc (ns n)) hp).trans
    (mul_le_mul_right (hderiv (ns n)) _)

end TauCeti

section Critical

open MeasureTheory Module Finset
open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The iterated form of the one-dimensional bound `‖u x‖ ≤ ∫ ‖u'‖`. Write the points of `E` as
`L y` for coordinates `y : ι → ℝ` along vectors `L (Pi.single i 1)` of norm at most one. Then for
every finite set `s` of coordinates, the value of a compactly supported `C^#s` function `u` at
`L y` is bounded by the integral of `‖D^#s u‖` over the coordinates in `s`. -/
theorem HasCompactSupport.eNorm_le_lmarginal_iteratedFDeriv {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Finite ι] [DecidableEq ι] (L : (ι → ℝ) ≃L[ℝ] E)
    (hL : ∀ i, ‖L (Pi.single i 1)‖ ≤ 1) (s : Finset ι) {u : E → F}
    (hu : ContDiff ℝ #s u) (h'u : HasCompactSupport u) (y : ι → ℝ) :
    ‖u (L y)‖ₑ ≤
      (∫⋯∫⁻_s, fun z ↦ ‖iteratedFDeriv ℝ #s u (L z)‖ₑ ∂fun _ ↦ (volume : Measure ℝ)) y := by
  have := Fintype.ofFinite ι
  induction s using Finset.induction_on generalizing u y with
  | empty => rw [lmarginal_empty, eNorm_le_iff_norm_le, card_empty, norm_iteratedFDeriv_zero]
  | insert i s hi ih =>
    rw [card_insert_of_notMem hi] at hu ⊢
    have hmeas : Measurable fun z ↦ ‖iteratedFDeriv ℝ (#s + 1) u (L z)‖ₑ :=
      ((hu.continuous_iteratedFDeriv le_rfl).comp L.continuous).eNorm.measurable
    rw [lmarginal_insert _ hmeas hi]
    -- The derivative of `u` along the `i`-th coordinate direction.
    set v := L (Pi.single i 1)
    have hv : ContDiff ℝ #s (fun w ↦ fderiv ℝ u w v) :=
      (hu.fderiv_right le_rfl).clm_apply contDiff_const
    -- The fundamental theorem of calculus on the line through `L y` in the direction `v`.
    have hline : ContDiff ℝ 1 (fun t ↦ u (L (Function.update y i t))) :=
      (hu.of_le (by simp)).comp (L.contDiff.comp (contDiff_update 1 y i))
    have hderiv (t : ℝ) : deriv (fun t ↦ u (L (Function.update y i t))) t =
        fderiv ℝ u (L (Function.update y i t)) v := by
      have hL : HasDerivAt (fun t ↦ L (Function.update y i t)) v t :=
        L.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_update y i t)
      exact (((hu.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt t hL).deriv
    have hftc := HasCompactSupport.eNorm_le_lintegral_Ici_deriv hline
      (h'u.comp_isClosedEmbedding (L.toHomeomorph.isClosedEmbedding.comp
        (isClosedEmbedding_update y i))) (y i)
    simp only [Function.update_eq_self, hderiv] at hftc
    refine hftc.trans ((setLIntegral_le_lintegral _ _).trans (lintegral_mono fun t ↦ ?_))
    refine (ih hv (h'u.fderiv_apply ℝ v) _).trans (lmarginal_mono (fun z ↦ ?_) _)
    -- A derivative in the direction of a vector of norm at most one costs one order.
    rw [eNorm_le_iff_norm_le, ← norm_iteratedFDeriv_fderiv]
    exact (norm_iteratedFDeriv_clm_apply_const (hu.fderiv_right le_rfl).contDiffAt le_rfl).trans
      (mul_le_of_le_one_left (norm_nonneg _) (hL i))

/-- **The Sobolev inequality in the critical case `W^{n,1} ⊆ L^∞`.** On a real inner product space
of dimension `n` with its Lebesgue measure, a compactly supported `Cⁿ` function `u` satisfies
`‖u x‖ ≤ ∫ ‖Dⁿu y‖ dy` at every point `x`. -/
theorem HasCompactSupport.eNorm_le_lintegral_iteratedFDeriv {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {u : E → F}
    (hu : ContDiff ℝ (finrank ℝ E) u) (h'u : HasCompactSupport u) (x : E) :
    ‖u x‖ₑ ≤ ∫⁻ y, ‖iteratedFDeriv ℝ (finrank ℝ E) u y‖ₑ := by
  classical
  -- Coordinates along the standard orthonormal basis `b` of `E`.
  let b := stdOrthonormalBasis ℝ E
  let L : (Fin (finrank ℝ E) → ℝ) ≃L[ℝ] E :=
    (PiLp.continuousLinearEquiv 2 ℝ fun _ ↦ ℝ).symm.trans b.repr.symm.toContinuousLinearEquiv
  have hL (i : Fin (finrank ℝ E)) : ‖L (Pi.single i 1)‖ ≤ 1 := by
    simp [L, b.repr_symm_single]
  have hmp : MeasurePreserving L :=
    b.measurePreserving_repr_symm.comp (PiLp.volume_preserving_toLp _)
  obtain ⟨y, rfl⟩ := L.surjective x
  have h := h'u.eNorm_le_lmarginal_iteratedFDeriv L hL univ (by simpa using hu) y
  rw [lmarginal_univ, card_univ, Fintype.card_fin, ← volume_pi] at h
  exact h.trans_eq (hmp.lintegral_comp_emb L.toHomeomorph.measurableEmbedding
    fun w ↦ ‖iteratedFDeriv ℝ (finrank ℝ E) u w‖ₑ)

end Critical
