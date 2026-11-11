/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Trace.Reflection.Coefficients
public import TauCeti.Analysis.Calculus.ContDiff.GlueHalfLine
public import TauCeti.MeasureTheory.Function.Lp.Dilation
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Matching the normal derivatives of a higher-order reflection

`higherReflection k f` extends the values of `f` on the nonnegative normal line by the weighted
reflections at `-t / (j + 1)`, `j : Fin k`. For a `Cⁿ` input and `n < k`, the result is `Cⁿ`
across zero, and all its normal derivatives through order `n` agree there with those of `f`.
The construction works for functions with values in an arbitrary real normed space, and may be
applied to each normal slice of a function on a half-space. Polynomial normal slices of degree
less than `k` are reproduced exactly. In particular the second-order reflection extends the
normal coordinate to itself, rather than to its absolute value.

This is the classical normal-jet matching part of higher-order Sobolev extension. The construction
is bounded from `Lᵖ` of the original half-line to `Lᵖ` of the full line, including both endpoints.
Bounds for weak derivatives on half-discs and the weak gluing theorem are separate analytic
requirements.

## References

* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Chapter 5, extension theorems.
-/

public section

noncomputable section

open Set Filter Polynomial MeasureTheory
open scoped ENNReal
open scoped Topology

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Extension from the nonnegative normal line by higher-order reflection. -/
def higherReflection (k : ℕ) (f : ℝ → F) (t : ℝ) : F :=
  if 0 ≤ t then f t else higherReflectionLower k f t

/-- The extension agrees with the input on the original half-line. -/
@[simp]
theorem higherReflection_of_nonneg (k : ℕ) (f : ℝ → F) {t : ℝ} (ht : 0 ≤ t) :
    higherReflection k f t = f t := ite_eq_left ht

/-- On the negative half-line the extension uses the reflected dilations. -/
@[simp]
theorem higherReflection_of_neg (k : ℕ) (f : ℝ → F) {t : ℝ} (ht : t < 0) :
    higherReflection k f t = higherReflectionLower k f t := ite_eq_right ht.not_ge

/-- The extension depends only on the values on the original closed half-line. -/
theorem higherReflection_congr {k : ℕ} {f g : ℝ → F} (hfg : EqOn f g (Ici 0)) :
    higherReflection k f = higherReflection k g := by
  funext t
  unfold higherReflection
  split_ifs with ht
  · exact hfg ht
  · simp only [higherReflectionLower_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [hfg (mul_nonneg_of_nonpos_of_nonpos (higherReflectionNode_neg j).le (le_of_not_ge ht))]

/-- Higher-order reflection is linear in the input. -/
theorem higherReflection_add (k : ℕ) (f g : ℝ → F) :
    higherReflection k (f + g) = higherReflection k f + higherReflection k g := by
  funext t
  simp only [higherReflection, higherReflectionLower_add, Pi.add_apply]
  split_ifs <;> rfl

/-- Higher-order reflection commutes with scalar multiplication. -/
theorem higherReflection_smul (k : ℕ) (c : ℝ) (f : ℝ → F) :
    higherReflection k (c • f) = c • higherReflection k f := by
  funext t
  simp only [higherReflection, higherReflectionLower_smul, Pi.smul_apply]
  split_ifs <;> rfl

/-- At first order higher-order reflection is the usual even extension. -/
@[simp]
theorem higherReflection_one (f : ℝ → F) (t : ℝ) :
    higherReflection 1 f t = f |t| := by
  by_cases ht : 0 ≤ t
  · simp [ht, abs_of_nonneg ht]
  · simp [higherReflection, ht, abs_of_neg (lt_of_not_ge ht)]

/-- The reflected normal slice is `Cⁿ` across zero when `n < k`. -/
theorem _root_.ContDiff.higherReflection {k n : ℕ} (hn : n < k) {f : ℝ → F}
    (hf : ContDiff ℝ n f) : ContDiff ℝ n (higherReflection k f) := by
  apply hf.if_nonneg hf.higherReflectionLower
  intro i hi
  exact (iteratedDeriv_higherReflectionLower_zero (by omega)
    (hf.of_le (by exact_mod_cast hi))).symm

/-- The extension preserves every normal derivative through order `n` at zero. -/
theorem iteratedDeriv_higherReflection_zero {k n i : ℕ} (hn : n < k) (hi : i ≤ n)
    {f : ℝ → F} (hf : ContDiff ℝ n f) :
    iteratedDeriv i (higherReflection k f) 0 = iteratedDeriv i f 0 := by
  have heq : EqOn (higherReflection k f) f (Ici 0) := fun _ ht ↦
    higherReflection_of_nonneg k f ht
  rw [← iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0)
    ((hf.higherReflection hn).of_le (by exact_mod_cast hi)).contDiffAt (by simp),
    ← iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0)
      (hf.of_le (by exact_mod_cast hi)).contDiffAt (by simp)]
  exact iteratedDerivWithin_congr heq (by simp)

/-- Every polynomial normal slice of degree less than `k` is reproduced by the extension. -/
theorem higherReflection_eval_eq {k : ℕ} (P : ℝ[X]) (hP : P.degree < k) :
    higherReflection k (fun t ↦ P.eval t) = fun t ↦ P.eval t := by
  funext t
  by_cases ht : 0 ≤ t
  · exact higherReflection_of_nonneg k _ ht
  · rw [higherReflection, ite_eq_right ht]
    have hdeg : (P.comp (C t * X)).degree ≤ P.degree := by
      rw [degree_comp (by simp [degree_C_mul_X (ne_of_lt (lt_of_not_ge ht))])]
      simp [degree_C_mul_X (ne_of_lt (lt_of_not_ge ht))]
    have h := sum_higherReflectionCoeff_mul_eval (P.comp (C t * X)) (hdeg.trans_lt hP)
    simpa only [higherReflectionLower_apply, eval_comp, eval_mul, eval_C, eval_X,
      mul_one, smul_eq_mul, mul_comm] using h

/-- The dilation factor for the `Lᵖ` bound of the reflection operator on normal slices. -/
def higherReflectionBound (k : ℕ) (p : ℝ≥0∞) : ℝ≥0∞ :=
  1 + ∑ j : Fin k, ‖higherReflectionCoeff k j‖ₑ *
    ENNReal.ofReal |(higherReflectionNode j)⁻¹| ^ (1 / p).toReal

/-- The reflection bound as a finite sum of the Jacobian factors. -/
theorem higherReflectionBound_eq (k : ℕ) (p : ℝ≥0∞) :
    higherReflectionBound k p = 1 + ∑ j : Fin k, ‖higherReflectionCoeff k j‖ₑ *
      ENNReal.ofReal |(higherReflectionNode j)⁻¹| ^ (1 / p).toReal := by
  rw [higherReflectionBound]

/-- At `p = ∞` the Jacobian factors disappear. -/
@[simp]
theorem higherReflectionBound_top (k : ℕ) :
    higherReflectionBound k ∞ = 1 + ∑ j : Fin k, ‖higherReflectionCoeff k j‖ₑ := by
  simp [higherReflectionBound]

/-- The reflection bound is finite, including at the endpoint `p = ∞`. -/
@[simp]
theorem higherReflectionBound_ne_top (k : ℕ) (p : ℝ≥0∞) :
    higherReflectionBound k p ≠ ⊤ := by
  unfold higherReflectionBound
  apply ENNReal.add_ne_top.mpr
  refine ⟨by simp, ENNReal.sum_ne_top.mpr fun j _ ↦ ?_⟩
  exact ENNReal.mul_ne_top (by simp) (ENNReal.rpow_ne_top_of_nonneg (by positivity)
    ENNReal.ofReal_ne_top)

omit [NormedSpace ℝ F] in
/-- The normal dilation changes the `Lᵖ` seminorm by its one-dimensional Jacobian. -/
private lemma eLpNorm_comp_higherReflectionNode {k : ℕ} (j : Fin k) (f : ℝ → F) (p : ℝ≥0∞) :
    eLpNorm (fun t ↦ f (higherReflectionNode j * t)) p volume =
      ENNReal.ofReal |(higherReflectionNode j)⁻¹| ^ (1 / p).toReal * eLpNorm f p volume := by
  have hn : higherReflectionNode j ≠ 0 := (higherReflectionNode_neg j).ne
  let e : ℝ ≃L[ℝ] ℝ :=
    (LinearEquiv.smulOfUnit (M := ℝ)
      (Units.mk0 (higherReflectionNode j) hn)).toContinuousLinearEquiv
  have he_apply (t : ℝ) : e t = higherReflectionNode j * t := rfl
  -- The scalar-unit equivalence has scalar multiplication as its underlying linear map.
  have he : (e : ℝ →ₗ[ℝ] ℝ) = higherReflectionNode j • LinearMap.id := rfl
  have he_det : LinearMap.det (e : ℝ →ₗ[ℝ] ℝ) = higherReflectionNode j := by
    rw [he, LinearMap.det_smul, LinearMap.det_id]
    simp only [Module.finrank_self, pow_one, mul_one]
  simpa only [Function.comp_def, he_apply, he_det] using
    Measure.eLpNorm_comp_continuousLinearEquiv volume f e p

/-- The lower-branch `Lᵖ` estimate before cutting off the negative half-line. -/
private lemma eLpNorm_higherReflectionLower_le (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p) (f : ℝ → F) :
    eLpNorm (higherReflectionLower k f) p volume ≤
      (∑ j : Fin k, ‖higherReflectionCoeff k j‖ₑ *
        ENNReal.ofReal |(higherReflectionNode j)⁻¹| ^ (1 / p).toReal) * eLpNorm f p volume := by
  have hfun : higherReflectionLower k f = ∑ j : Fin k,
      fun t ↦ higherReflectionCoeff k j • f (higherReflectionNode j * t) := by
    ext t
    simp only [higherReflectionLower_apply, Finset.sum_apply]
  rw [hfun]
  calc
    _ ≤ ∑ j : Fin k, eLpNorm (fun t ↦ higherReflectionCoeff k j •
      f (higherReflectionNode j * t)) p volume := eLpNorm_sum_le hp
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      -- Pi scalar multiplication evaluates pointwise; expose that function to use the norm API.
      change eLpNorm (higherReflectionCoeff k j • fun t ↦ f (higherReflectionNode j * t))
        p volume = _
      rw [eLpNorm_const_smul, eLpNorm_comp_higherReflectionNode, mul_assoc]

/-- Split the extension of a zero-extended input into the original input and its lower part. -/
private lemma higherReflection_indicator_eq_add (k : ℕ) (f : ℝ → F) :
    higherReflection k ((Ici (0 : ℝ)).indicator f) =
      (Ici (0 : ℝ)).indicator f + (Iio (0 : ℝ)).indicator
        (higherReflectionLower k ((Ici (0 : ℝ)).indicator f)) := by
  let g := (Ici (0 : ℝ)).indicator f
  -- The local name g abbreviates the indicator input on both sides.
  change higherReflection k g = g + (Iio (0 : ℝ)).indicator (higherReflectionLower k g)
  ext t
  by_cases ht : 0 ≤ t
  · rw [higherReflection_of_nonneg k g ht, Pi.add_apply,
      indicator_of_notMem (not_lt.mpr ht), add_zero]
  · rw [higherReflection_of_neg k g (lt_of_not_ge ht), Pi.add_apply,
      indicator_of_mem (lt_of_not_ge ht)]
    have hgt : g t = 0 := indicator_of_notMem ht f
    rw [hgt, zero_add]

/-- Higher-order reflection is bounded from `Lᵖ` of the original half-line to `Lᵖ` of the full
normal line. The estimate includes `p = 1` and `p = ∞` and arbitrary real normed codomains. -/
theorem eLpNorm_higherReflection_le (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p) (f : ℝ → F) :
    eLpNorm (higherReflection k f) p volume ≤
      higherReflectionBound k p * eLpNorm f p (volume.restrict (Ici 0)) := by
  let g := (Ici (0 : ℝ)).indicator f
  have hg : EqOn f g (Ici 0) := fun _ ht ↦ (indicator_of_mem ht f).symm
  rw [higherReflection_congr (k := k) hg]
  rw [higherReflection_indicator_eq_add]
  -- Replace the indicator expression by its local name g under the pointwise sum.
  change eLpNorm (g + (Iio (0 : ℝ)).indicator (higherReflectionLower k g)) p volume ≤ _
  have h₁ := eLpNorm_add_le (μ := (volume : Measure ℝ)) (p := p)
    (f := g) (g := (Iio (0 : ℝ)).indicator (higherReflectionLower k g)) hp
  have h₂ := eLpNorm_indicator_le (μ := (volume : Measure ℝ)) (p := p)
    (higherReflectionLower k g) (s := Iio 0) measurableSet_Iio.nullMeasurableSet
  have h₃ := eLpNorm_higherReflectionLower_le k hp g
  calc
    _ ≤ eLpNorm g p volume + eLpNorm ((Iio (0 : ℝ)).indicator
      (higherReflectionLower k g)) p volume := h₁
    _ ≤ eLpNorm g p volume + eLpNorm (higherReflectionLower k g) p volume :=
      add_le_add le_rfl h₂
    _ ≤ higherReflectionBound k p * eLpNorm g p volume := by
      rw [higherReflectionBound, add_mul, one_mul]
      exact add_le_add le_rfl h₃
    _ = _ := by rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ici.nullMeasurableSet]

/-- Reflection preserves strong measurability from the original half-line. -/
theorem _root_.MeasureTheory.AEStronglyMeasurable.higherReflection {k : ℕ} {f : ℝ → F}
    (hf : AEStronglyMeasurable f (volume.restrict (Ici 0))) :
    AEStronglyMeasurable (higherReflection k f) volume := by
  let g := (Ici (0 : ℝ)).indicator f
  have hg : AEStronglyMeasurable g volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Ici).mpr hf
  have heq : EqOn f g (Ici 0) := fun _ ht ↦ (indicator_of_mem ht f).symm
  rw [higherReflection_congr (k := k) heq, higherReflection_indicator_eq_add]
  apply hg.add
  apply AEStronglyMeasurable.indicator _ measurableSet_Iio
  have hsum : higherReflectionLower k g = ∑ j : Fin k,
      fun t ↦ higherReflectionCoeff k j • g (higherReflectionNode j * t) := by
    ext t
    simp only [higherReflectionLower_apply, Finset.sum_apply]
  rw [hsum]
  apply Finset.aestronglyMeasurable_sum
  intro j _
  exact (hg.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_smul volume
    (higherReflectionNode_neg j).ne)).const_smul _

/-- Higher-order reflection sends `Lᵖ` functions on the original half-line to `Lᵖ` functions on
the full normal line, for every exponent, including those below one. -/
theorem _root_.MeasureTheory.MemLp.higherReflection {k : ℕ} {p : ℝ≥0∞} {f : ℝ → F}
    (hf : MemLp f p (volume.restrict (Ici 0))) : MemLp (higherReflection k f) p volume := by
  let g := (Ici (0 : ℝ)).indicator f
  have hg : MemLp g p volume :=
    (memLp_indicator_iff_restrict measurableSet_Ici.nullMeasurableSet).2 hf
  have heq : EqOn f g (Ici 0) := fun _ ht ↦ (indicator_of_mem ht f).symm
  rw [higherReflection_congr (k := k) heq, higherReflection_indicator_eq_add]
  apply hg.add
  apply MemLp.indicator measurableSet_Iio.nullMeasurableSet
  have hlower : MemLp (fun t ↦ ∑ j : Fin k,
      higherReflectionCoeff k j • g (higherReflectionNode j * t)) p volume := by
    apply memLp_finsetSum
    intro j _
    have hj : MemLp (fun t ↦ g (higherReflectionNode j * t)) p volume := by
      rw [MemLp, eLpNorm_comp_higherReflectionNode]
      exact ENNReal.mul_lt_top
        (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top).lt_top
        hg.eLpNorm_lt_top
    exact hj.const_smul _
  have hsum : (fun t ↦ ∑ j : Fin k,
      higherReflectionCoeff k j • g (higherReflectionNode j * t)) =
      higherReflectionLower k g := by
    funext t
    exact (higherReflectionLower_apply k g t).symm
  rw [hsum] at hlower
  exact hlower

end TauCeti
