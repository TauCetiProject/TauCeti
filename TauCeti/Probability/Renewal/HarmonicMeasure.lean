/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.IntegralConvolution
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.MeasureTheory.Group.ChoquetDeny
public import TauCeti.Probability.Renewal.Lattice.Basic

/-!
# Harmonic measures of a nonlattice law are multiples of Lebesgue measure

Let `F` be a probability law on `ℝ≥0` and write `F` also for its image on `ℝ`. A measure `η` on
`ℝ` is `F`-harmonic if `F ∗ η = η`. This file proves the rigidity theorem of renewal theory: if
`F` is nonlattice and `η` is uniformly locally bounded, that is `η [a, a + 1] ≤ C` for every
`a : ℝ`, then `η` is a multiple of Lebesgue measure, namely `η = η (0, 1] • volume`
(`MeasureTheory.Measure.eq_smul_volume_of_map_coe_conv_eq_self`).

Limits of translates of the renewal measure are harmonic and uniformly locally bounded, so this
theorem identifies them with multiples of Lebesgue measure. It is the step of Feller's proof of
Blackwell's renewal theorem for nonlattice laws that uses the nonlattice hypothesis.

The proof has two steps.

* For a bounded uniformly continuous function `h : ℝ → ℝ` with `h x = ∫ t, h (x - t) ∂F`, the
  Choquet–Deny lemma `TauCeti.periodic_of_forall_eq_integral_sub` makes every point of the
  support of `F` a period of `h`. Since `F` is nonlattice, these periods generate a dense
  subgroup of `ℝ` (`MeasureTheory.Measure.dense_addSubgroupClosure_support_map_coe_iff`), so by
  continuity `h` is constant (`MeasureTheory.Measure.apply_eq_of_forall_eq_integral_sub`).
* For a compactly supported continuous `f`, the function `x ↦ ∫ y, f (y - x) ∂η` is bounded,
  uniformly continuous and harmonic, because `η` is uniformly locally bounded and `F ∗ η = η`.
  Hence it is constant, so `η` and its translates integrate every such `f` alike. By uniqueness
  in the Riesz–Markov–Kakutani theorem `η` is translation invariant, and by uniqueness of Haar
  measure it is a multiple of Lebesgue measure.

No mean or moment assumption is made on `F`, and `η` may have atoms a priori.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  2nd edition, Wiley, 1971, §XI.2.
* G. Choquet and J. Deny, *Sur l'équation de convolution μ = μ ⋆ σ*, C. R. Acad. Sci. Paris
  250 (1960), 799–801.
-/

public section

open Set Filter Metric
open scoped NNReal ENNReal CompactlySupported

namespace MeasureTheory.Measure

/-- A measure on `ℝ` whose unit windows `[a, a + 1]` have mass at most `C` gives every window
`[a, a + n]` of natural length `n` mass at most `(n + 1) * C`. -/
theorem measure_Icc_add_natCast_le {η : Measure ℝ} {C : ℝ≥0∞}
    (hC : ∀ a : ℝ, η (Icc a (a + 1)) ≤ C) (a : ℝ) (n : ℕ) :
    η (Icc a (a + n)) ≤ (n + 1) * C := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, add_zero, zero_add, one_mul]
    exact (measure_mono (Icc_subset_Icc_right (by linarith))).trans (hC a)
  | succ n ih =>
    calc η (Icc a (a + (n + 1 : ℕ)))
        ≤ η (Icc a (a + n) ∪ Icc (a + n) (a + n + 1)) := by
          refine measure_mono fun x hx ↦ ?_
          push_cast at hx
          rcases le_total x (a + n) with h | h
          · exact Or.inl ⟨hx.1, h⟩
          · exact Or.inr ⟨h, by linarith [hx.2]⟩
      _ ≤ (n + 1) * C + C := (measure_union_le _ _).trans (add_le_add ih (hC _))
      _ = ((n + 1 : ℕ) + 1) * C := by push_cast; ring

/-- A measure on `ℝ` with uniformly bounded mass on unit windows is locally finite. -/
theorem isLocallyFiniteMeasure_of_measure_Icc_add_one_le {η : Measure ℝ} {C : ℝ≥0}
    (hC : ∀ a : ℝ, η (Icc a (a + 1)) ≤ C) : IsLocallyFiniteMeasure η :=
  ⟨fun x ↦ ⟨Icc (x - 2⁻¹) (x - 2⁻¹ + 1), Icc_mem_nhds (by linarith) (by linarith),
    (hC _).trans_lt ENNReal.coe_lt_top⟩⟩

/-- **Harmonic functions of a nonlattice law are constant.** If `μ` is a nonlattice probability
law on `ℝ≥0`, a bounded, uniformly continuous function `h : ℝ → ℝ` with
`h x = ∫ t, h (x - t) ∂μ` for every `x`, the law `μ` being taken on `ℝ`, is constant. -/
theorem apply_eq_of_forall_eq_integral_sub (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (hμ : ¬ μ.IsLattice) {h : ℝ → ℝ} {C : ℝ} (hC : ∀ x, |h x| ≤ C) (hu : UniformContinuous h)
    (hh : ∀ x, h x = ∫ t, h (x - t) ∂μ.map ((↑) : ℝ≥0 → ℝ)) (x y : ℝ) : h x = h y := by
  -- The periods of the continuous function `h` form a closed subgroup of `ℝ`.
  let P : AddSubgroup ℝ :=
    { carrier := {c | Function.Periodic h c}
      zero_mem' := fun x ↦ by simp
      add_mem' := fun ha hb ↦ ha.add_period hb
      neg_mem' := fun ha ↦ ha.neg }
  have hP : IsClosed (P : Set ℝ) := by
    have : (P : Set ℝ) = ⋂ z, {c | h (z + c) = h z} := by ext; simp [P, Function.Periodic]
    rw [this]
    exact isClosed_iInter fun z ↦ isClosed_eq
      (hu.continuous.comp (continuous_const.add continuous_id)) continuous_const
  -- It contains the support of `μ`, hence the dense subgroup that the support generates.
  have hle : AddSubgroup.closure (μ.map ((↑) : ℝ≥0 → ℝ)).support ≤ P :=
    (AddSubgroup.closure_le _).2 fun s hs ↦ TauCeti.periodic_of_forall_eq_integral_sub hC hu hh hs
  have hdense := (dense_addSubgroupClosure_support_map_coe_iff (μ := μ)).2 hμ
  have hyx : y - x ∈ (P : Set ℝ) := by
    rw [← hP.closure_eq]
    exact closure_mono hle (hdense.closure_eq ▸ mem_univ _)
  simpa using (hyx x).symm

/-- A bounded function vanishing off a window `[a, a + n]` has integral at most
`A * ((n + 1) * C)` in absolute value against a measure whose unit windows have mass at most
`C`. -/
theorem abs_integral_le_of_measure_Icc_add_one_le {η : Measure ℝ} {C : ℝ≥0}
    (hC : ∀ a : ℝ, η (Icc a (a + 1)) ≤ C) {φ : ℝ → ℝ} {A : ℝ} (hφA : ∀ y, |φ y| ≤ A)
    (a : ℝ) (n : ℕ) (hφ : ∀ y, y ∉ Icc a (a + n) → φ y = 0) :
    |∫ y, φ y ∂η| ≤ A * ((n + 1) * C) := by
  have hmass := measure_Icc_add_natCast_le (fun a ↦ hC a) a n
  have hfin : η (Icc a (a + n)) < ∞ := hmass.trans_lt (by finiteness)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hφ, ← Real.norm_eq_abs]
  refine (norm_setIntegral_le_of_norm_le_const hfin fun y _ ↦ hφA y).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ ((abs_nonneg _).trans (hφA 0))
  have hreal : ((n + 1 : ℝ≥0∞) * C).toReal = (n + 1) * C := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp
  rw [measureReal_def, ← hreal]
  exact ENNReal.toReal_mono (by finiteness) hmass

variable {μ : Measure ℝ≥0} [IsProbabilityMeasure μ] {η : Measure ℝ} {C : ℝ≥0}

/-- A compactly supported function on `ℝ` vanishes outside `[-R, R]` for some natural `R`, so
each translate `y ↦ f (y - c)` vanishes outside `[c - R, c + R]`. -/
private lemma exists_natCast_apply_sub_eq_zero (f : C_c(ℝ, ℝ)) :
    ∃ R : ℕ, ∀ y c : ℝ, y < c - R ∨ c + R < y → f (y - c) = 0 := by
  obtain ⟨r, hr⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
  refine ⟨⌈r⌉₊, fun y c h ↦ image_eq_zero_of_notMem_tsupport fun hy ↦ ?_⟩
  have := mem_closedBall_zero_iff.1 (hr hy)
  rw [Real.norm_eq_abs, abs_le] at this
  rcases h with h | h <;> linarith [Nat.le_ceil r]

/-- The integrals of the translates `y ↦ f (y - x)` of a compactly supported continuous function
against a uniformly locally bounded measure are uniformly bounded. -/
private lemma exists_abs_integral_apply_sub_le (hC : ∀ a : ℝ, η (Icc a (a + 1)) ≤ C)
    (f : C_c(ℝ, ℝ)) : ∃ B, ∀ x, |∫ y, f (y - x) ∂η| ≤ B := by
  obtain ⟨R, hR⟩ := exists_natCast_apply_sub_eq_zero f
  obtain ⟨A, hA⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  refine ⟨A * ((2 * R + 1) * C), fun x ↦ ?_⟩
  -- The translate vanishes off the window `[x - R, x + R]` of length `2 * R`.
  have := abs_integral_le_of_measure_Icc_add_one_le hC (φ := fun y ↦ f (y - x))
    (fun y ↦ by simpa using hA (y - x)) (x - R) (2 * R) fun y hy ↦ hR y x (by
      simp only [mem_Icc, not_and_or, not_le] at hy
      push_cast at hy
      rcases hy with hy | hy
      exacts [Or.inl hy, Or.inr (by linarith)])
  simpa using this

/-- The integrals of the translates `y ↦ f (y - x)` of a compactly supported continuous function
against a uniformly locally bounded measure depend uniformly continuously on `x`. -/
private lemma uniformContinuous_integral_apply_sub (hC : ∀ a : ℝ, η (Icc a (a + 1)) ≤ C)
    (f : C_c(ℝ, ℝ)) : UniformContinuous fun x ↦ ∫ y, f (y - x) ∂η := by
  have := isLocallyFiniteMeasure_of_measure_Icc_add_one_le hC
  obtain ⟨R, hR⟩ := exists_natCast_apply_sub_eq_zero f
  have hfi (x : ℝ) : Integrable (fun y ↦ f (y - x)) η :=
    (f.continuous.comp (continuous_id.sub continuous_const)).integrable_of_hasCompactSupport
      (f.hasCompactSupport.comp_homeomorph (Homeomorph.subRight x))
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  -- `K` exceeds the mass bound `(2 * R + 3) * C` of the windows of length `2 * R + 2`.
  set K : ℝ := (2 * R + 3) * C + 1
  have hK : 0 < K := by positivity
  obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuous_iff.1
    (f.hasCompactSupport.uniformContinuous_of_continuous f.continuous) (ε / (2 * K))
    (by positivity)
  refine ⟨min δ 1, by positivity, fun {x x'} hxx' ↦ ?_⟩
  have hxx'1 : |x - x'| < 1 := by
    simpa [Real.dist_eq] using hxx'.trans_le (min_le_right _ _)
  rw [abs_lt] at hxx'1
  rw [Real.dist_eq, ← integral_sub (hfi x) (hfi x')]
  -- The difference of the two translates is small and vanishes off `[x - R - 1, x + R + 1]`.
  have := abs_integral_le_of_measure_Icc_add_one_le hC
    (φ := fun y ↦ f (y - x) - f (y - x')) (A := ε / (2 * K))
    (fun y ↦ by
      have := hfδ (a := y - x) (b := y - x') (by
        rw [dist_sub_left]
        exact hxx'.trans_le (min_le_left _ _))
      rw [Real.dist_eq] at this
      exact this.le)
    (x - R - 1) (2 * R + 2)
    fun y hy ↦ by
      simp only [mem_Icc, not_and_or, not_le] at hy
      push_cast at hy
      have h₁ : y < x - R ∨ x + R < y := by
        rcases hy with hy | hy
        exacts [Or.inl (by linarith), Or.inr (by linarith)]
      have h₂ : y < x' - R ∨ x' + R < y := by
        rcases hy with hy | hy
        exacts [Or.inl (by linarith), Or.inr (by linarith)]
      rw [hR y x h₁, hR y x' h₂, sub_zero]
  refine this.trans_lt ?_
  have hCK : ((2 * R + 2 : ℕ) + 1) * (C : ℝ) < K := by push_cast; linarith
  calc ε / (2 * K) * ((((2 * R + 2 : ℕ) : ℝ) + 1) * C) ≤ ε / (2 * K) * K := by
        gcongr
    _ < ε := by field_simp; linarith

/-- If `μ ∗ η = η`, the integrals of the translates `y ↦ f (y - x)` of a compactly supported
continuous function against `η` form a `μ`-harmonic function of `x`. -/
private lemma integral_apply_sub_eq_integral_integral (hC : ∀ a : ℝ, η (Icc a (a + 1)) ≤ C)
    (hη : μ.map ((↑) : ℝ≥0 → ℝ) ∗ η = η) (f : C_c(ℝ, ℝ)) (x : ℝ) :
    ∫ y, f (y - x) ∂η = ∫ t, (∫ y, f (y - (x - t)) ∂η) ∂μ.map ((↑) : ℝ≥0 → ℝ) := by
  have := isLocallyFiniteMeasure_of_measure_Icc_add_one_le hC
  have hfi : Integrable (fun y ↦ f (y - x)) η :=
    (f.continuous.comp (continuous_id.sub continuous_const)).integrable_of_hasCompactSupport
      (f.hasCompactSupport.comp_homeomorph (Homeomorph.subRight x))
  calc ∫ y, f (y - x) ∂η = ∫ y, f (y - x) ∂(μ.map ((↑) : ℝ≥0 → ℝ) ∗ η) := by rw [hη]
    _ = ∫ t, ∫ y, f (t + y - x) ∂η ∂μ.map ((↑) : ℝ≥0 → ℝ) :=
      integral_conv (by rw [hη]; exact hfi)
    _ = _ := by congr with t; congr with y; congr 1; ring

/-- **Rigidity of harmonic measures.** Let `μ` be a nonlattice probability law on `ℝ≥0`. A measure
`η` on `ℝ` with `μ ∗ η = η`, the law `μ` being taken on `ℝ`, and with uniformly bounded mass on
the unit windows `[a, a + 1]`, is the multiple `η (0, 1] • volume` of Lebesgue measure. -/
theorem eq_smul_volume_of_map_coe_conv_eq_self (hμ : ¬ μ.IsLattice)
    (hC : ∀ a : ℝ, η (Icc a (a + 1)) ≤ C) (hη : μ.map ((↑) : ℝ≥0 → ℝ) ∗ η = η) :
    η = η (Ioc 0 1) • volume := by
  have := isLocallyFiniteMeasure_of_measure_Icc_add_one_le hC
  -- Every compactly supported continuous function has the same integral against all
  -- translates of `η`.
  have htrans (a : ℝ) (f : C_c(ℝ, ℝ)) : ∫ y, f (y + a) ∂η = ∫ y, f y ∂η := by
    obtain ⟨B, hB⟩ := exists_abs_integral_apply_sub_le hC f
    simpa using μ.apply_eq_of_forall_eq_integral_sub hμ hB
      (uniformContinuous_integral_apply_sub hC f) (integral_apply_sub_eq_integral_integral hC hη f)
      (-a) 0
  have hinv : IsAddLeftInvariant η := by
    refine ⟨fun a ↦ ?_⟩
    have : (η.map (a + ·)).Regular := by
      simpa using Regular.map (μ := η) (Homeomorph.addLeft a)
    refine ext_of_integral_eq_on_compactlySupported fun f ↦ ?_
    rw [integral_map (f := fun y ↦ f y) (by fun_prop) f.continuous.aestronglyMeasurable]
    simpa [add_comm] using htrans a f
  have heq := isAddLeftInvariant_eq_smul η volume
  have hc : η (Ioc 0 1) = addHaarScalarFactor η volume := by
    conv_lhs => rw [heq]
    simp
  rw [hc]
  exact heq

end MeasureTheory.Measure
