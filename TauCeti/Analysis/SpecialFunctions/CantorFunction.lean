/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import TauCeti.Analysis.Real.OfDigits
public import TauCeti.MeasureTheory.Measure.Lebesgue.CantorSet

/-!
# The Cantor–Lebesgue function

The Cantor–Lebesgue function (the "devil's staircase") `C : ℝ → ℝ` is the standard example of a
continuous monotone function of bounded variation whose derivative vanishes almost everywhere
but which is not constant. It is built from the ternary Cantor set by the dyadic-value
construction: the point `0.(2s₀)(2s₁)(2s₂)…` (in base `3`) of the Cantor set, for a Boolean
sequence `s`, is sent to the dyadic number `0.s₀s₁s₂…` (in base `2`), and the value at an
arbitrary `x` is the supremum of these values over the points of the Cantor set lying to the
left of `x`. In particular `C` is `0` on `(-∞, 0]` and `1` on `[1, ∞)`.

We prove that `C` is monotone and continuous, takes the values `C 0 = 0` and `C 1 = 1`, maps
the Cantor set onto `[0, 1]`, is locally constant off the Cantor set and hence has derivative
`0` almost everywhere, has total variation `1`, and is not absolutely continuous on `[0, 1]`.
Its Lebesgue–Stieltjes measure `dC` is an atomless probability measure concentrated on the
Lebesgue-null Cantor set, hence mutually singular with Lebesgue measure.

## Main definitions

* `TauCeti.cantorFunction`: the Cantor–Lebesgue function.
* `TauCeti.cantorStieltjesFunction`: `cantorFunction` as a Stieltjes function, whose measure
  is the Cantor measure `dC`.

## Main results

* `TauCeti.cantorFunction_cantorSetEquivNatToBool_symm`: the dyadic-value description of
  `cantorFunction` on the Cantor set.
* `TauCeti.continuous_cantorFunction`, `TauCeti.monotone_cantorFunction`.
* `TauCeti.image_cantorFunction_cantorSet`: `cantorFunction` maps the Cantor set onto `[0, 1]`.
* `TauCeti.ae_hasDerivAt_cantorFunction`: the derivative of `cantorFunction` is `0` almost
  everywhere.
* `TauCeti.eVariationOn_cantorFunction`: the total variation of `cantorFunction` is `1`.
* `TauCeti.not_absolutelyContinuousOnInterval_cantorFunction`.
* `TauCeti.mutuallySingular_cantorStieltjesFunction_measure_volume`: `dC ⟂ volume`.

## References

* O. Dovgoshey, O. Martio, V. Ryazanov, M. Vuorinen, *The Cantor function*,
  Expo. Math. 24 (2006), 1–37.
-/

public section

open Real Set MeasureTheory Filter Topology
open scoped ENNReal

namespace TauCeti

/-- The point `0.(2s₀)(2s₁)(2s₂)…` (in base `3`) of the Cantor set coded by `s`. -/
private noncomputable def ternary (s : ℕ → Bool) : ℝ := (cantorSetEquivNatToBool.symm s : ℝ)

/-- The dyadic number `0.s₀s₁s₂…` (in base `2`) coded by `s`. -/
private noncomputable def dyadic (s : ℕ → Bool) : ℝ := ofDigits fun i ↦ cond (s i) (1 : Fin 2) 0

/-- The *Cantor–Lebesgue function*. The value at `x` is the supremum of the dyadic numbers
`0.s₀s₁s₂…` (in base `2`) over the Boolean sequences `s` whose Cantor point
`0.(2s₀)(2s₁)(2s₂)…` (in base `3`) is at most `x`; the supremum of the empty set is `0`, so the
function vanishes on `(-∞, 0)`. -/
noncomputable def cantorFunction (x : ℝ) : ℝ :=
  sSup (dyadic '' {s | ternary s ≤ x})

/-- The defining formula of the Cantor function, stated without its private helpers. -/
theorem cantorFunction_eq_sSup (x : ℝ) :
    cantorFunction x = sSup ((fun s ↦ ofDigits fun i ↦ cond (s i) (1 : Fin 2) 0) ''
      {s | (cantorSetEquivNatToBool.symm s : ℝ) ≤ x}) := (rfl)

/-- Mathlib's `cantorSetEquivNatToBool.symm` is defined by this formula. -/
private lemma ternary_eq (s : ℕ → Bool) :
    ternary s = ofDigits fun i ↦ cond (s i) (2 : Fin 3) 0 := (rfl)

private lemma range_ternary : range ternary = cantorSet := by
  ext x
  refine ⟨?_, fun hx ↦ ⟨cantorSetEquivNatToBool ⟨x, hx⟩, ?_⟩⟩
  · rintro ⟨s, rfl⟩
    exact (cantorSetEquivNatToBool.symm s).2
  · simp [ternary]

private lemma bddAbove_image_dyadic (S : Set (ℕ → Bool)) : BddAbove (dyadic '' S) :=
  ⟨1, forall_mem_image.2 fun _ _ ↦ ofDigits_le_one _⟩

/-- Comparing Cantor points compares their dyadic values. Ternary codes with digits `0` and `2`
are ordered strictly lexicographically, and binary codes weakly so. -/
private lemma dyadic_le_dyadic_of_ternary_le {s t : ℕ → Bool} (h : ternary s ≤ ternary t) :
    dyadic s ≤ dyadic t := by
  by_cases hst : s = t
  · rw [hst]
  obtain ⟨n, hn, hmin⟩ : ∃ n, s n ≠ t n ∧ ∀ i < n, s i = t i :=
    ⟨Nat.find (Function.ne_iff.mp hst), Nat.find_spec (Function.ne_iff.mp hst),
      fun i hi ↦ not_not.mp (Nat.find_min (Function.ne_iff.mp hst) hi)⟩
  cases hs : s n <;> cases ht : t n <;> simp only [hs, ht, ne_eq, not_true_eq_false] at hn
  · exact ofDigits_le_ofDigits_of_lt (n := n) (fun i hi ↦ by simp [hmin i hi]) (by simp [hs, ht])
  · refine absurd h (not_le.mpr ?_)
    rw [ternary_eq, ternary_eq]
    exact ofDigits_lt_ofDigits_of_add_one_lt (n := n) (fun i hi ↦ by simp [hmin i hi])
      (by simp [hs, ht])

/-- On the Cantor point coded by `s`, the Cantor function takes the dyadic value coded by `s`. -/
private lemma cantorFunction_ternary (s : ℕ → Bool) : cantorFunction (ternary s) = dyadic s :=
  le_antisymm
    (csSup_le ⟨_, mem_image_of_mem _ (le_refl (ternary s))⟩
      (forall_mem_image.2 fun _ ht ↦ dyadic_le_dyadic_of_ternary_le ht))
    (le_csSup (bddAbove_image_dyadic _) (mem_image_of_mem _ (le_refl (ternary s))))

/-- The *dyadic-value description* of the Cantor function: it sends the point
`0.(2s₀)(2s₁)(2s₂)…` (in base `3`) of the Cantor set to `0.s₀s₁s₂…` (in base `2`). -/
theorem cantorFunction_cantorSetEquivNatToBool_symm (s : ℕ → Bool) :
    cantorFunction (cantorSetEquivNatToBool.symm s) =
      ofDigits fun i ↦ cond (s i) (1 : Fin 2) 0 :=
  cantorFunction_ternary s

/-- On the Cantor set, the Cantor function reads the code `cantorSetEquivNatToBool` of a point
(its ternary digits halved) in base `2`. -/
theorem cantorFunction_of_mem_cantorSet {x : ℝ} (hx : x ∈ cantorSet) :
    cantorFunction x = ofDigits fun i ↦ cond (cantorSetEquivNatToBool ⟨x, hx⟩ i) (1 : Fin 2) 0 := by
  rw [← cantorFunction_cantorSetEquivNatToBool_symm, Equiv.symm_apply_apply]

/-- The Cantor function is nonnegative. -/
theorem cantorFunction_nonneg (x : ℝ) : 0 ≤ cantorFunction x :=
  Real.sSup_nonneg (forall_mem_image.2 fun _ _ ↦ ofDigits_nonneg _)

/-- The Cantor function is at most `1`. -/
theorem cantorFunction_le_one (x : ℝ) : cantorFunction x ≤ 1 :=
  Real.sSup_le (forall_mem_image.2 fun _ _ ↦ ofDigits_le_one _) zero_le_one

/-- The Cantor function is monotone. -/
theorem monotone_cantorFunction : Monotone cantorFunction := fun _ y hxy ↦
  Real.sSup_le (forall_mem_image.2 fun _ hs ↦
    le_csSup (bddAbove_image_dyadic _) (mem_image_of_mem _ (le_trans hs hxy)))
    (cantorFunction_nonneg y)

/-- The Cantor function vanishes at `0`. -/
theorem cantorFunction_zero : cantorFunction 0 = 0 := by
  have h := cantorFunction_ternary fun _ ↦ false
  -- The constant digits `cond false 2 0` and `cond false 1 0` are `0` by definition.
  rwa [ternary_eq, show (fun _ ↦ cond false (2 : Fin 3) 0) = fun _ ↦ 0 from rfl,
    ofDigits_const_zero, dyadic, show (fun _ ↦ cond false (1 : Fin 2) 0) = fun _ ↦ 0 from rfl,
    ofDigits_const_zero] at h

/-- The Cantor function equals `1` at `1`. -/
theorem cantorFunction_one : cantorFunction 1 = 1 := by
  have h := cantorFunction_ternary fun _ ↦ true
  -- `ofDigits_const_last_eq_one` is stated for the constant digit `Fin.last`.
  rwa [ternary_eq, show (fun _ ↦ cond true (2 : Fin 3) 0) = fun _ ↦ Fin.last 2 from rfl,
    ofDigits_const_last_eq_one, dyadic,
    show (fun _ ↦ cond true (1 : Fin 2) 0) = fun _ ↦ Fin.last 1 from rfl,
    ofDigits_const_last_eq_one] at h

/-- The Cantor function vanishes on `(-∞, 0]`. -/
@[simp]
theorem cantorFunction_of_nonpos {x : ℝ} (hx : x ≤ 0) : cantorFunction x = 0 :=
  le_antisymm (cantorFunction_zero ▸ monotone_cantorFunction hx) (cantorFunction_nonneg x)

/-- The Cantor function equals `1` on `[1, ∞)`. -/
@[simp]
theorem cantorFunction_of_one_le {x : ℝ} (hx : 1 ≤ x) : cantorFunction x = 1 :=
  le_antisymm (cantorFunction_le_one x) (cantorFunction_one ▸ monotone_cantorFunction hx)

private lemma range_cantorFunction_subset : range cantorFunction ⊆ Icc 0 1 :=
  range_subset_iff.2 fun x ↦ mem_Icc.2 ⟨cantorFunction_nonneg x, cantorFunction_le_one x⟩

/-- The Cantor function maps the Cantor set onto `[0, 1]`. -/
theorem image_cantorFunction_cantorSet : cantorFunction '' cantorSet = Icc 0 1 := by
  refine ((image_subset_range _ _).trans range_cantorFunction_subset).antisymm fun y hy ↦ ?_
  obtain ⟨a, -, rfl⟩ := ofDigits_SurjOn (b := 2) one_lt_two hy
  refine ⟨ternary fun i ↦ decide (a i = 1), range_ternary ▸ mem_range_self _, ?_⟩
  rw [cantorFunction_ternary, dyadic]
  congr 1
  funext i
  generalize a i = d
  fin_cases d <;> rfl

/-- The range of the Cantor function is `[0, 1]`. -/
theorem range_cantorFunction : range cantorFunction = Icc 0 1 :=
  range_cantorFunction_subset.antisymm
    (image_cantorFunction_cantorSet ▸ image_subset_range _ _)

/-- The Cantor function is continuous, being monotone with an interval as its range. -/
@[fun_prop]
theorem continuous_cantorFunction : Continuous cantorFunction := by
  let g : ℝ → Icc (0 : ℝ) 1 := fun x ↦ ⟨cantorFunction x, cantorFunction_nonneg x,
    cantorFunction_le_one x⟩
  have hg : Monotone g := fun _ _ hxy ↦ monotone_cantorFunction hxy
  have hsurj : Function.Surjective g := fun y ↦ by
    obtain ⟨x, hx⟩ : (y : ℝ) ∈ range cantorFunction := by
      rw [range_cantorFunction]
      exact y.2
    exact ⟨x, Subtype.ext hx⟩
  exact continuous_subtype_val.comp (hg.continuous_of_surjective hsurj)

/-- The Cantor function is measurable. -/
@[fun_prop]
theorem measurable_cantorFunction : Measurable cantorFunction :=
  continuous_cantorFunction.measurable

/-- The Cantor function is locally constant off the Cantor set. -/
theorem cantorFunction_eventuallyEq_of_notMem {x : ℝ} (hx : x ∉ cantorSet) :
    cantorFunction =ᶠ[𝓝 x] fun _ ↦ cantorFunction x := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isClosed_cantorSet.isOpen_compl x hx
  filter_upwards [Metric.ball_mem_nhds x hε] with y hy
  have hset : {s | ternary s ≤ y} = {s | ternary s ≤ x} := by
    ext s
    have hs : ternary s ∉ Metric.ball x ε := fun h ↦ hball h (range_ternary ▸ mem_range_self s)
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hy hs
    simp only [mem_ofPred_eq]
    constructor <;> intro h <;> by_contra h' <;> exact hs ⟨by linarith, by linarith⟩
  simp only [cantorFunction, hset]

/-- Off the Cantor set, the Cantor function has derivative `0`. -/
theorem hasDerivAt_cantorFunction_of_notMem {x : ℝ} (hx : x ∉ cantorSet) :
    HasDerivAt cantorFunction 0 x :=
  (hasDerivAt_const x _).congr_of_eventuallyEq (cantorFunction_eventuallyEq_of_notMem hx)

/-- The Cantor function has derivative `0` at almost every point. -/
theorem ae_hasDerivAt_cantorFunction : ∀ᵐ x, HasDerivAt cantorFunction 0 x :=
  (measure_eq_zero_iff_ae_notMem.mp volume_cantorSet).mono
    fun _ ↦ hasDerivAt_cantorFunction_of_notMem

/-- The Cantor function has variation `1` on `[0, 1]`. -/
theorem eVariationOn_cantorFunction_Icc : eVariationOn cantorFunction (Icc 0 1) = 1 := by
  simpa using (monotone_cantorFunction.monotoneOn univ).eVariationOn_eq (mem_univ 0) (mem_univ 1)

/-- The Cantor function has total variation `1` on the real line. -/
theorem eVariationOn_cantorFunction : eVariationOn cantorFunction univ = 1 := by
  refine le_antisymm ?_ (eVariationOn_cantorFunction_Icc ▸ eVariationOn.mono _ (subset_univ _))
  rw [eVariationOn.eq_biSup_inter_Icc]
  refine iSup₂_le fun p _ ↦ ?_
  rw [(monotone_cantorFunction.monotoneOn univ).eVariationOn_eq (mem_univ _) (mem_univ _)]
  refine ENNReal.ofReal_le_one.mpr ?_
  linarith [cantorFunction_le_one p.2, cantorFunction_nonneg p.1]

/-- The Cantor function is not absolutely continuous on `[0, 1]`: its derivative vanishes almost
everywhere, so it would be constant by the fundamental theorem of calculus. -/
theorem not_absolutelyContinuousOnInterval_cantorFunction :
    ¬ AbsolutelyContinuousOnInterval cantorFunction 0 1 := fun h ↦ by
  have hftc := h.integral_deriv_eq_sub
  rw [intervalIntegral.integral_zero_ae (ae_hasDerivAt_cantorFunction.mono
    fun _ hx _ ↦ hx.deriv), cantorFunction_one, cantorFunction_zero] at hftc
  norm_num at hftc

/-- The Cantor function as a Stieltjes function; it is continuous, so no right-limit
modification as in `Monotone.stieltjesFunction` is needed. Its measure `dC` is the Cantor
measure. -/
noncomputable def cantorStieltjesFunction : StieltjesFunction ℝ where
  toFun := cantorFunction
  mono' := monotone_cantorFunction
  right_continuous' _ := continuous_cantorFunction.continuousWithinAt

/-- The underlying function of `cantorStieltjesFunction` is the Cantor function. -/
@[simp]
theorem coe_cantorStieltjesFunction : ⇑cantorStieltjesFunction = cantorFunction := (rfl)

/-- The Cantor measure is a probability measure. -/
instance : IsProbabilityMeasure cantorStieltjesFunction.measure :=
  cantorStieltjesFunction.isProbabilityMeasure
    (tendsto_const_nhds.congr' ((eventually_le_atBot 0).mono fun _ hx ↦
      (cantorFunction_of_nonpos hx).symm))
    (tendsto_const_nhds.congr' ((eventually_ge_atTop 1).mono fun _ hx ↦
      (cantorFunction_of_one_le hx).symm))

/-- The Cantor measure has no atoms, since the Cantor function is continuous. -/
instance : NullSingletonClass cantorStieltjesFunction.measure where
  measure_singleton x := by
    rw [StieltjesFunction.measure_singleton, coe_cantorStieltjesFunction,
      continuous_cantorFunction.continuousWithinAt.leftLim_eq, sub_self, ENNReal.ofReal_zero]

/-- The Cantor measure is concentrated on the Cantor set. -/
theorem cantorStieltjesFunction_measure_compl_cantorSet :
    cantorStieltjesFunction.measure cantorSetᶜ = 0 := by
  refine measure_null_of_locally_null _ fun x hx ↦ ?_
  obtain ⟨ε, hε, hconst⟩ := Metric.eventually_nhds_iff.mp
    (cantorFunction_eventuallyEq_of_notMem hx)
  have hmem : ∀ y, |y - x| ≤ ε / 2 → cantorFunction y = cantorFunction x := fun y hy ↦
    hconst (by rw [Real.dist_eq]; linarith)
  refine ⟨Ioc (x - ε / 2) (x + ε / 2), mem_nhdsWithin_of_mem_nhds
    (Ioc_mem_nhds (by linarith) (by linarith)), ?_⟩
  rw [StieltjesFunction.measure_Ioc, coe_cantorStieltjesFunction,
    hmem (x + ε / 2) (abs_le.mpr ⟨by linarith, by linarith⟩),
    hmem (x - ε / 2) (abs_le.mpr ⟨by linarith, by linarith⟩),
    sub_self, ENNReal.ofReal_zero]

/-- The Cantor measure and Lebesgue measure are mutually singular: the former is concentrated
on the Cantor set, which is Lebesgue-null. -/
theorem mutuallySingular_cantorStieltjesFunction_measure_volume :
    cantorStieltjesFunction.measure ⟂ₘ volume :=
  ⟨cantorSetᶜ, isClosed_cantorSet.isOpen_compl.measurableSet,
    cantorStieltjesFunction_measure_compl_cantorSet, by rw [compl_compl, volume_cantorSet]⟩

end TauCeti
