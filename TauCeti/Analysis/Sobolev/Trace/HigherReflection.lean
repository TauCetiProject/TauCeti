/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Trace.ReflectionCoefficients
public import TauCeti.MeasureTheory.Function.Lp.Dilation
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Topology.Piecewise

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
theorem higherReflection_one (f : ℝ → F) (t : ℝ) :
    higherReflection 1 f t = f |t| := by
  by_cases ht : 0 ≤ t
  · simp [ht, abs_of_nonneg ht]
  · simp [higherReflection, ht, abs_of_neg (lt_of_not_ge ht)]

/-- Equal values and derivatives at zero allow gluing the one-sided derivatives. -/
private lemma hasDerivAt_if_nonneg {f g f' g' : ℝ → F}
    (hf : ∀ t, HasDerivAt f (f' t) t) (hg : ∀ t, HasDerivAt g (g' t) t)
    (h₀ : f 0 = g 0) (h₁ : f' 0 = g' 0) (t : ℝ) :
    HasDerivAt (fun t ↦ if 0 ≤ t then f t else g t)
      (if 0 ≤ t then f' t else g' t) t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · simp only [ite_eq_right ht.not_ge]
    exact (hg t).congr_of_eventuallyEq (by
      filter_upwards [eventually_lt_nhds ht] with x hx
      exact ite_eq_right hx.not_ge)
  · simp only [le_refl, ite_true]
    have hpos : HasDerivWithinAt (fun t ↦ if 0 ≤ t then f t else g t) (f' 0) (Ici 0) 0 :=
      (hf 0).hasDerivWithinAt.congr (fun _ hx ↦ ite_eq_left hx) (ite_eq_left le_rfl)
    have hneg : HasDerivWithinAt (fun t ↦ if 0 ≤ t then f t else g t) (f' 0) (Iic 0) 0 := by
      rw [h₁]
      apply (hg 0).hasDerivWithinAt.congr
      · intro x hx
        by_cases hx' : 0 ≤ x
        · have : x = 0 := le_antisymm hx hx'
          subst x
          simpa using h₀
        · exact ite_eq_right hx'
      · simpa using h₀
    simpa only [Ici_union_Iic, hasDerivWithinAt_univ] using hpos.union hneg
  · simp only [ite_eq_left ht.le]
    exact (hf t).congr_of_eventuallyEq (by
      filter_upwards [eventually_gt_nhds ht] with x hx
      exact ite_eq_left hx.le)

/-- Gluing `Cⁿ` functions with matching jets through order `n`. -/
private lemma contDiff_if_nonneg {n : ℕ} {f g : ℝ → F}
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g)
    (h : ∀ i ≤ n, iteratedDeriv i f 0 = iteratedDeriv i g 0) :
    ContDiff ℝ n (fun t ↦ if 0 ≤ t then f t else g t) := by
  induction n generalizing f g with
  | zero =>
    apply contDiff_zero.mpr
    apply hf.continuous.if _ hg.continuous
    intro t ht
    have ht : t = 0 := by simpa only [show {x : ℝ | 0 ≤ x} = Ici 0 from rfl,
      frontier_Ici, mem_singleton_iff] using ht
    subst t
    exact h 0 le_rfl
  | succ n ih =>
    have hderiv := hasDerivAt_if_nonneg
      (fun t ↦ (hf.differentiable (by simp) t).hasDerivAt)
      (fun t ↦ (hg.differentiable (by simp) t).hasDerivAt)
      (h 0 (by omega)) (by simpa only [iteratedDeriv_one] using h 1 (by omega))
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by simp,
      contDiff_succ_iff_deriv]
    refine ⟨fun t ↦ (hderiv t).differentiableAt, by simp, ?_⟩
    have heq : deriv (fun t ↦ if 0 ≤ t then f t else g t) =
        fun t ↦ if 0 ≤ t then deriv f t else deriv g t := funext fun t ↦ (hderiv t).deriv
    rw [heq]
    apply ih hf.deriv' hg.deriv'
    intro i hi
    simpa only [← iteratedDeriv_succ'] using h (i + 1) (by omega)

/-- The reflected normal slice is `Cⁿ` across zero when `n < k`. -/
theorem _root_.ContDiff.higherReflection {k n : ℕ} (hn : n < k) {f : ℝ → F}
    (hf : ContDiff ℝ n f) : ContDiff ℝ n (higherReflection k f) := by
  apply contDiff_if_nonneg hf hf.higherReflectionLower
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
  change eLpNorm (fun t : ℝ ↦ f (higherReflectionNode j • t)) p volume = _
  rw [← Function.comp_def, ← (measurableEmbedding_const_smul₀ hn).eLpNorm_map_measure,
    Measure.map_addHaar_smul volume hn,
    eLpNorm_smul_measure_of_ne_zero (by positivity), smul_eq_mul]
  simp [Module.finrank_self, abs_inv]

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
      change eLpNorm (higherReflectionCoeff k j • fun t ↦ f (higherReflectionNode j * t))
        p volume = _
      rw [eLpNorm_const_smul, eLpNorm_comp_higherReflectionNode, mul_assoc]

/-- Split the extension of a zero-extended input into the original input and its lower part. -/
private lemma higherReflection_indicator_eq_add (k : ℕ) (f : ℝ → F) :
    higherReflection k ((Ici (0 : ℝ)).indicator f) =
      (Ici (0 : ℝ)).indicator f + (Iio (0 : ℝ)).indicator
        (higherReflectionLower k ((Ici (0 : ℝ)).indicator f)) := by
  let g := (Ici (0 : ℝ)).indicator f
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
theorem aestronglyMeasurable_higherReflection {k : ℕ} {f : ℝ → F}
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
the full normal line. -/
theorem _root_.MeasureTheory.MemLp.higherReflection {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {f : ℝ → F}
    (hf : MemLp f p (volume.restrict (Ici 0))) : MemLp (higherReflection k f) p volume := by
  exact (eLpNorm_higherReflection_le k hp f).trans_lt (ENNReal.mul_lt_top
    (higherReflectionBound_ne_top k p).lt_top hf.eLpNorm_lt_top)

end TauCeti
