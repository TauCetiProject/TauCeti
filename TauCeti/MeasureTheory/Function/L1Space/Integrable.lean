/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.NormNum
import TauCeti.Analysis.Normed.Module.Basic
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Integrability criteria

Taking the absolute value of an almost everywhere measurable real coefficient does not change
integrability of its scalar product with a real normed-space-valued function, even when that
function is not measurable by itself. The equivalence permits signed Jacobians in oriented
change of variables for arbitrary rough-form coefficients.

An integrable function weights singletons summably by the norms of its values
(`MeasureTheory.summable_measureReal_mul_norm_of_integrable`), and a measure carrying an
integrable function whose norm is almost everywhere at least one is finite
(`MeasureTheory.Integrable.isFiniteMeasure_of_one_le_norm`).

For absolute moments, a real function in `Lᵖ` of positive real order has an integrable `p`-th
power (`MeasureTheory.MemLp.integrable_rpow`), and when the function is almost everywhere
nonnegative both its extended `p`-th moment and the `p`-th power of its `eLpNorm` agree with
`ENNReal.ofReal` of its Bochner `p`-th moment
(`MeasureTheory.MemLp.lintegral_ofReal_rpow_eq_ofReal_integral`,
`MeasureTheory.MemLp.eLpNorm_rpow_eq_ofReal_integral`), converting `eLpNorm` bounds between almost
everywhere nonnegative functions into Bochner `p`-th moment inequalities
(`MeasureTheory.integral_rpow_le_mul_integral_rpow_of_eLpNorm_le`). Membership of the identity in
`Lᵖ` gives integrability of its norm power even on a seminormed group, and on the real line
positive-order `Lᵖ` membership is equivalent to integrability of the corresponding absolute power.
By Hölder's inequality, a finite product of functions, the `i`th in `L^(p i)`, is integrable when
`∑ i, (p i)⁻¹ = 1` (`TauCeti.integrable_fun_prod_of_memLp`); in particular a product of `k`
functions in `Lᵏ` is integrable when `k ≠ 0`
(`TauCeti.integrable_fun_prod_of_memLp_card_of_nonempty`), and on a finite measure space for
every `k` (`TauCeti.integrable_fun_prod_of_memLp_card`). Against a finite measure, every power of
an almost everywhere strongly measurable, almost everywhere bounded function into a normed ring is
integrable (`TauCeti.integrable_pow_of_ae_norm_le`); in particular, a finite measure on `ℝ`
concentrated on `[-R, R]` has finite moments of every order (`TauCeti.integrable_pow_of_ae_abs_le`).

The pointwise supremum of finitely many integrable lattice-valued functions is integrable
(`MeasureTheory.integrable_finset_sup'`). A function nonzero at an atom of infinite mass is not
integrable (`MeasureTheory.not_integrable_of_measure_singleton_eq_top`). A multiplier bounded on
a set containing the support of an integrable function keeps it integrable
(`MeasureTheory.Integrable.smul_of_support_subset`), and so does an operator-valued function
bounded on a set outside which the integrable function vanishes
(`MeasureTheory.Integrable.apply_of_norm_le`). An `Lᵖ` function with `1 ≤ p` vanishing outside
a set of finite measure is integrable (`MeasureTheory.MemLp.integrable_of_ae_notMem_eq_zero`), and
so is a function vanishing outside a measurable set and dominated on it by a function integrable
there (`MeasureTheory.integrable_of_forall_notMem_eq_zero_of_norm_le`).
Scalar multiplication by a finite product of multiplicative indicators, each constant on a
null-measurable set and equal to `1` off it, preserves integrability
(`MeasureTheory.Integrable.prod_mulIndicator_const_smul`). A function integrable for the measure
`μ` weighted by `‖h‖ₑ` has an integrable scalar product with `h`
(`MeasureTheory.integrable_smul_of_integrable_withDensity_enorm`).

The reciprocal of a density over a finite base measure is integrable under the weighted measure,
even when that measure is infinite (`AEMeasurable.integrable_inv_toReal_withDensity`).
-/

public section

open scoped ENNReal

namespace MeasureTheory

/-- Scalar multiplication by a finite product of multiplicative indicators preserves
integrability, when each factor is a constant on a null-measurable set and `1` off it.
Neither a finite measure nor disjoint sets are required. -/
theorem Integrable.prod_mulIndicator_const_smul {X κ 𝕜 E : Type*} [MeasurableSpace X]
    [NormedCommRing 𝕜] [NormedAddCommGroup E] [MulActionWithZero 𝕜 E] [IsBoundedSMul 𝕜 E]
    {μ : Measure X} {f : X → E} (hf : Integrable f μ)
    (s : Finset κ) {B : κ → Set X} (hB : ∀ k ∈ s, NullMeasurableSet (B k) μ) (z : κ → 𝕜) :
    Integrable (fun x ↦ (∏ k ∈ s, (B k).mulIndicator (fun _ ↦ z k) x) • f x) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hf
  | @insert k s hk ih =>
    have hi := ih (fun j hj ↦ hB j (Finset.mem_insert_of_mem hj))
    have hp := Integrable.piecewise (hB k (Finset.mem_insert_self k s))
      (hi.smul (z k)).integrableOn hi.integrableOn
    refine hp.congr (.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ B k <;> simp [hx, Finset.prod_insert hk, mul_smul]

/-- Multiplication by an almost everywhere measurable real coefficient preserves integrability
exactly when its absolute value does, without assuming measurability of the vector-valued `f`. -/
theorem integrable_smul_iff_abs_smul {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure X} {d : X → ℝ} {f : X → F} (hd : AEStronglyMeasurable d μ) :
    Integrable (fun x ↦ d x • f x) μ ↔ Integrable (fun x ↦ |d x| • f x) μ := by
  -- Multiplying by the measurable sign `u` of `d` exchanges `d • f` and `|d| • f`.
  let u : X → ℝ := fun x ↦ if 0 ≤ d x then 1 else -1
  have hu : AEStronglyMeasurable u μ :=
    ((Measurable.ite measurableSet_Ici measurable_const measurable_const).comp_aemeasurable
      hd.aemeasurable).aestronglyMeasurable
  have hb : ∀ᵐ x ∂μ, ‖u x‖ ≤ 1 := .of_forall fun x ↦ by unfold u; split_ifs <;> norm_num
  constructor <;> refine fun h ↦ (h.bdd_smul 1 hu hb).congr (.of_forall fun x ↦ ?_) <;>
    by_cases hx : 0 ≤ d x <;> simp [u, hx, smul_smul, abs_of_nonneg, abs_of_neg, lt_of_not_ge]

/-- Integrability with respect to a measure on a type with measurable singletons implies
summability of the singleton masses weighted by the norms of the function values. -/
theorem summable_measureReal_mul_norm_of_integrable {X E : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [NormedAddCommGroup E]
    {ν : Measure X} {f : X → E} (hf : Integrable f ν) :
    Summable (fun x : X ↦ ν.real {x} * ‖f x‖) := by
  refine summable_of_sum_le (c := ∫ x, ‖f x‖ ∂ν) (fun x ↦ by positivity) fun S ↦ ?_
  calc ∑ x ∈ S, ν.real {x} * ‖f x‖
      = ∑ x ∈ S, ∫ y in {x}, ‖f y‖ ∂ν := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        rw [integral_singleton, smul_eq_mul]
    _ = ∫ y in ⋃ x ∈ S, {x}, ‖f y‖ ∂ν := by
        rw [integral_biUnion_finset S (fun x _ ↦ measurableSet_singleton x)
          (fun x _ y _ hxy ↦ by simpa using hxy)
          (fun x _ ↦ hf.norm.integrableOn)]
    _ ≤ ∫ y, ‖f y‖ ∂ν :=
        setIntegral_le_integral hf.norm (Filter.Eventually.of_forall fun y ↦ norm_nonneg _)

/-- An integrable function whose norm is almost everywhere at least one can only be carried by a
finite measure. -/
theorem Integrable.isFiniteMeasure_of_one_le_norm {X F : Type*} [MeasurableSpace X]
    [SeminormedAddGroup F] {f : X → F} {μ : Measure X} (hf : Integrable f μ)
    (h_one : ∀ᵐ x ∂μ, 1 ≤ ‖f x‖) : IsFiniteMeasure μ :=
  (hasFiniteIntegral_const_iff_isFiniteMeasure (one_ne_zero (α := ℝ))).1 <|
    hf.hasFiniteIntegral.mono_eNorm <| h_one.mono fun _ hx ↦ by
      rwa [eNorm_le_iff_norm_le, norm_one]

/-- The pointwise supremum over a nonempty finset of integrable functions with values in a normed
lattice is integrable. -/
theorem integrable_finset_sup' {X β κ : Type*} [MeasurableSpace X] [NormedAddCommGroup β]
    [Lattice β] [HasSolidNorm β] [IsOrderedAddMonoid β] {μ : Measure X} {s : Finset κ}
    (hs : s.Nonempty) {f : κ → X → β} (hf : ∀ i ∈ s, Integrable (f i) μ) :
    Integrable (fun x ↦ s.sup' hs fun i ↦ f i x) μ := by
  simpa only [← Finset.sup'_apply] using
    Finset.sup'_induction (p := fun h ↦ Integrable h μ) hs f (fun _ h₁ _ h₂ ↦ h₁.sup h₂) hf

/-- A function that is nonzero at an atom of infinite mass is not integrable. -/
theorem not_integrable_of_measure_singleton_eq_top {α E : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [NormedAddCommGroup E] {ν : Measure α} {f : α → E} {x : α}
    (hx : ν {x} = ⊤) (hf : f x ≠ 0) : ¬ Integrable f ν := fun hint ↦ by
  have h := (integrableOn_singleton_iff (μ := ν)).1 hint.integrableOn
  simp [hx, hf] at h

/-- For a positive real order `p`, if `g` lies in `Lᵖ` then `g ^ p` is integrable. -/
theorem MemLp.integrable_rpow {X : Type*} [MeasurableSpace X] {μ : Measure X} {g : X → ℝ}
    {p : ℝ} (hp : 0 < p) (hg : MemLp g (ENNReal.ofReal p) μ) :
    Integrable (fun y => g y ^ p) μ := by
  have hn := hg.integrable_norm_rpow (ENNReal.ofReal_pos.2 hp).ne' ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_ofReal hp.le] at hn
  exact hn.mono' (hg.aestronglyMeasurable.aemeasurable.pow_const p).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      simpa only [Real.norm_eq_abs, abs_abs] using Real.abs_rpow_le_abs_rpow (g y) p)

/-- For a positive real order `p` and an almost everywhere nonnegative `g` in `Lᵖ`, the lower
integral of `ENNReal.ofReal (g y) ^ p` equals `ENNReal.ofReal` of the Bochner `p`-th moment. -/
theorem MemLp.lintegral_ofReal_rpow_eq_ofReal_integral {X : Type*} {_ : MeasurableSpace X}
    {μ : Measure X} {g : X → ℝ} {p : ℝ} (hg : MemLp g (ENNReal.ofReal p) μ) (hp : 0 < p)
    (hnn : 0 ≤ᵐ[μ] g) :
    ∫⁻ y, ENNReal.ofReal (g y) ^ p ∂μ = ENNReal.ofReal (∫ y, g y ^ p ∂μ) := by
  let _ : MeasurableSpace X := ‹_›
  rw [ofReal_integral_eq_lintegral_ofReal (hg.integrable_rpow hp)
    (hnn.mono fun _ h => Real.rpow_nonneg h _)]
  refine lintegral_congr_ae ?_
  filter_upwards [hnn] with y hy
  rw [Pi.zero_apply] at hy
  exact ENNReal.ofReal_rpow_of_nonneg hy hp.le

/-- For a positive real order `p` and an almost everywhere nonnegative `g` in `Lᵖ`, the `p`-th
power of its `eLpNorm` equals `ENNReal.ofReal` of its Bochner `p`-th moment. -/
theorem MemLp.eLpNorm_rpow_eq_ofReal_integral {X : Type*} {_ : MeasurableSpace X}
    {μ : Measure X} {g : X → ℝ} {p : ℝ} (hg : MemLp g (ENNReal.ofReal p) μ) (hp : 0 < p)
    (hnn : 0 ≤ᵐ[μ] g) :
    eLpNorm g (ENNReal.ofReal p) μ ^ p = ENNReal.ofReal (∫ y, g y ^ p ∂μ) := by
  rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.2 hp).ne' ENNReal.ofReal_ne_top
      hg.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp.le, ← lintegral_rpow_eNorm_eq_rpow_eLpNorm' hp,
    ← hg.lintegral_ofReal_rpow_eq_ofReal_integral hp hnn]
  refine lintegral_congr_ae ?_
  filter_upwards [hnn] with y hy
  rw [Pi.zero_apply] at hy
  rw [Real.eNorm_eq_ofReal hy]

/-- For a positive real order `p`, an `eLpNorm` bound between almost everywhere nonnegative
real-valued functions with `v ∈ Lᵖ` yields the corresponding Bochner `p`-th moment inequality; no
separate `MemLp` or measurability hypothesis on `u` is needed. -/
theorem integral_rpow_le_mul_integral_rpow_of_eLpNorm_le {X Y : Type*}
    {_ : MeasurableSpace X} {_ : MeasurableSpace Y} {μ : Measure X} {ν : Measure Y}
    {u : X → ℝ} {v : Y → ℝ} {p c : ℝ} (hp : 0 < p) (hc : 0 ≤ c)
    (hu_nn : 0 ≤ᵐ[μ] u) (hv_nn : 0 ≤ᵐ[ν] v) (hv : MemLp v (ENNReal.ofReal p) ν)
    (hle : eLpNorm u (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal c * eLpNorm v (ENNReal.ofReal p) ν) :
    ∫ x, u x ^ p ∂μ ≤ c ^ p * ∫ y, v y ^ p ∂ν := by
  have hu : MemLp u (ENNReal.ofReal p) μ :=
    hle.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hv.eLpNorm_lt_top)
  have hpow := ENNReal.rpow_le_rpow hle hp.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, ENNReal.ofReal_rpow_of_nonneg hc hp.le,
    hu.eLpNorm_rpow_eq_ofReal_integral hp hu_nn, hv.eLpNorm_rpow_eq_ofReal_integral hp hv_nn,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hc p)] at hpow
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (Real.rpow_nonneg hc p)
      (integral_nonneg_of_ae (hv_nn.mono fun _ h ↦ Real.rpow_nonneg h _)))).1 hpow

/-- An integrable function times a multiplier bounded on a set containing its support is
integrable. -/
theorem Integrable.smul_of_support_subset {α 𝕜 E : Type*} [NormedRing 𝕜]
    [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [MeasurableSpace α]
    {μ : Measure α} {f : α → E} {g : α → 𝕜} {s : Set α} {K : ℝ} (hf : Integrable f μ)
    (hsupp : Function.support f ⊆ s) (hg : AEStronglyMeasurable g μ) (hK : ∀ x ∈ s, ‖g x‖ ≤ K) :
    Integrable (fun x ↦ g x • f x) μ :=
  (hf.norm.const_mul K).mono' (hg.smul hf.1)
    (ae_of_all _ (TauCeti.norm_smul_le_mul_norm_of_support_subset hsupp hK))

/-- The reciprocal of a density is integrable under the changed measure when the
original measure is finite, even if the changed measure is infinite. Zero and infinite
density values give reciprocal zero by totalization. No lower bound is required. -/
theorem _root_.AEMeasurable.integrable_inv_toReal_withDensity {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {w : Ω → ℝ≥0∞} (hw : AEMeasurable w μ) :
    Integrable (fun x ↦ ((w x).toReal)⁻¹) (μ.withDensity w) := by
  have hle := Measure.le_iff.mp (withDensity_inv_same_le hw) Set.univ MeasurableSet.univ
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hle
  have hi : AEMeasurable (fun x ↦ (w x)⁻¹) (μ.withDensity w) :=
    hw.fun_inv.mono_ac (withDensity_absolutelyContinuous μ w)
  simpa only [ENNReal.toReal_inv] using
    integrable_toReal_of_lintegral_ne_top hi (hle.trans_lt (measure_lt_top μ _)).ne

/-- An integrable function vanishing almost everywhere outside a set stays integrable when an
operator-valued function bounded on that set is applied to it. -/
theorem Integrable.apply_of_norm_le {α 𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [MeasurableSpace α] {μ : Measure α} {f : α → E} {A : α → E →L[𝕜] F} {t : Set α} {M : ℝ}
    (hf : Integrable f μ) (hA : AEStronglyMeasurable A μ) (hM : ∀ y ∈ t, ‖A y‖ ≤ M)
    (hft : ∀ᵐ y ∂μ, y ∉ t → f y = 0) : Integrable (fun y ↦ A y (f y)) μ := by
  refine (hf.norm.const_mul M).mono'
    ((isBoundedBilinearMap_apply.continuous).comp_aestronglyMeasurable
      (hA.prodMk hf.aestronglyMeasurable)) ?_
  filter_upwards [hft] with y hy
  by_cases hyt : y ∈ t
  · exact ((A y).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hM y hyt) (norm_nonneg _))
  · simp [hy hyt]

/-- An `Lᵖ` function, `1 ≤ p`, vanishing almost everywhere outside a set of finite measure is
integrable. -/
theorem MemLp.integrable_of_ae_notMem_eq_zero {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {f : α → E} {p : ENNReal} (hf : MemLp f p μ) (hp : 1 ≤ p) {s : Set α}
    (hs : μ s ≠ ⊤) (hfs : ∀ᵐ x ∂μ, x ∉ s → f x = 0) : Integrable f μ := by
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hs
  exact IntegrableOn.integrable_of_ae_notMem_eq_zero ((hf.restrict s).integrable hp) hfs

/-- A function vanishing outside a measurable set `s`, a.e. strongly measurable on `s` and dominated
on `s` by a function integrable there, is integrable. -/
theorem integrable_of_forall_notMem_eq_zero_of_norm_le {α E : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup E] {s : Set α} {f : α → E} {g : α → ℝ}
    (hs : MeasurableSet s) (hf : AEStronglyMeasurable f (μ.restrict s)) (hg : IntegrableOn g s μ)
    (hf0 : ∀ x ∉ s, f x = 0) (hfg : ∀ x ∈ s, ‖f x‖ ≤ g x) : Integrable f μ :=
  IntegrableOn.integrable_of_forall_notMem_eq_zero
    (hg.mono' hf (ae_restrict_of_forall_mem hs hfg)) hf0

/-- If `f` is integrable for the measure `μ` weighted by `‖h‖ₑ`, then `f • h` is integrable for
`μ`. -/
theorem integrable_smul_of_integrable_withDensity_enorm {α 𝕜 E : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedField 𝕜] [NormedSpace ℝ 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f : α → 𝕜} {h : α → E} (hf : Integrable f (μ.withDensity fun x ↦ ‖h x‖ₑ))
    (hfm : AEStronglyMeasurable f μ) (hh : AEStronglyMeasurable h μ) :
    Integrable (fun x ↦ f x • h x) μ := by
  simp_rw [eNorm_eq_nnNorm] at hf
  rw [integrable_withDensity_iff_integrable_smul₀ hh.nnNorm.aemeasurable] at hf
  refine hf.mono (hfm.smul hh) (.of_forall fun x ↦ ?_)
  rw [norm_smul, NNReal.smul_def, norm_smul, coe_nnNorm, Real.norm_of_nonneg (norm_nonneg _),
    mul_comm]

end MeasureTheory

open MeasureTheory

namespace TauCeti

/-- On a finite measure, `Lᵖ` membership of the identity gives integrability of its norm
power, including for seminormed groups and order zero. -/
theorem integrable_norm_rpow_of_memLp_id_ofReal {E : Type*} [SeminormedAddCommGroup E]
    [MeasurableSpace E] {p : ℝ} (hp : 0 ≤ p) {ν : Measure E} [IsFiniteMeasure ν]
    (hν : MemLp id (ENNReal.ofReal p) ν) : Integrable (fun x : E ↦ ‖x‖ ^ p) ν := by
  -- Apply the normed-target moment lemma to the real-valued norm.
  simpa only [ENNReal.toReal_ofReal hp, id_eq, norm_norm] using
    (hν.of_le_eNorm hν.aestronglyMeasurable.norm (by simp)).integrable_norm_rpow'

/-- For a positive real order, `Lᵖ` membership of the identity on the real line is
equivalent to integrability of the absolute power. -/
theorem memLp_id_ofReal_iff_integrable_abs_rpow {q : ℝ} (hq : 0 < q) (μ : Measure ℝ) :
    MemLp id (ENNReal.ofReal q) μ ↔ Integrable (fun x : ℝ ↦ |x| ^ q) μ := by
  simpa only [id_eq, Real.norm_eq_abs, ENNReal.toReal_ofReal hq.le] using
    (integrable_norm_rpow_iff (f := id) (μ := μ) aestronglyMeasurable_id
      (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top).symm

/-- **Hölder's inequality** for finite products, as an integrability criterion: a finite product
of functions, the `i`th in `L^(p i)`, is integrable when the reciprocal exponents sum to `1`.
This is Mathlib's `MeasureTheory.MemLp.fun_prod`, which gives membership in `Lʳ` with
`r = (∑ i ∈ s, (p i)⁻¹)⁻¹`, specialized to the output exponent `r = 1`. -/
theorem integrable_fun_prod_of_memLp {X ι 𝕜 : Type*} [MeasurableSpace X] [NormedCommRing 𝕜]
    {μ : Measure X} {f : ι → X → 𝕜} {p : ι → ENNReal} {s : Finset ι}
    (hf : ∀ i ∈ s, MemLp (f i) (p i) μ) (hp : ∑ i ∈ s, (p i)⁻¹ = 1) :
    Integrable (fun x ↦ ∏ i ∈ s, f i x) μ := by
  have h := MemLp.fun_prod hf
  rw [hp, inv_one] at h
  exact memLp_one_iff_integrable.1 h

/-- A product of functions indexed by a nonempty finset `s` is integrable when every factor lies
in `L^(s.card)`, for any measure. -/
theorem integrable_fun_prod_of_memLp_card_of_nonempty {X ι 𝕜 : Type*} [MeasurableSpace X]
    [NormedCommRing 𝕜] {μ : Measure X} {f : ι → X → 𝕜} {s : Finset ι} (hs : s.Nonempty)
    (hf : ∀ i ∈ s, MemLp (f i) s.card μ) :
    Integrable (fun x ↦ ∏ i ∈ s, f i x) μ :=
  memLp_one_iff_integrable.1 <| memLp_fun_prod_of_memLp_mul_card hs fun i hi ↦ by
    simpa only [one_mul] using hf i hi

/-- On a finite measure space, a product of functions indexed by a finset `s` is integrable when
every factor lies in `L^(s.card)`. The finite measure is needed only for the empty product; see
`TauCeti.integrable_fun_prod_of_memLp_card_of_nonempty` for nonempty `s` and any measure. -/
theorem integrable_fun_prod_of_memLp_card {X ι 𝕜 : Type*} [MeasurableSpace X]
    [NormedCommRing 𝕜] {μ : Measure X} [IsFiniteMeasure μ] {f : ι → X → 𝕜} {s : Finset ι}
    (hf : ∀ i ∈ s, MemLp (f i) s.card μ) :
    Integrable (fun x ↦ ∏ i ∈ s, f i x) μ := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  exact integrable_fun_prod_of_memLp_card_of_nonempty hs hf

/-- Against a finite measure, every power of an almost everywhere strongly measurable function
into a normed ring that is almost everywhere bounded in norm by `R` is integrable. For `g = id`,
when the identity is almost everywhere strongly measurable (as on `ℝ` with its Borel σ-algebra),
this says that a finite measure concentrated on a ball has finite moments of every order. -/
theorem integrable_pow_of_ae_norm_le {Ω A : Type*} [MeasurableSpace Ω] [NormedRing A]
    {μ : Measure Ω} [IsFiniteMeasure μ] {g : Ω → A} (hg : AEStronglyMeasurable g μ) {R : ℝ}
    (h : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ R) (n : ℕ) :
    Integrable (fun ω => g ω ^ n) μ := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simpa only [pow_zero] using integrable_const (1 : A)
  refine .of_bound (hg.pow n) (R ^ n) ?_
  filter_upwards [h] with ω hω
  exact (norm_pow_le' (g ω) hn).trans (pow_le_pow_left₀ (norm_nonneg _) hω n)

/-- A finite measure on `ℝ` concentrated on `[-R, R]` has finite moments of every order: every
monomial `x ↦ xⁿ` is integrable. -/
theorem integrable_pow_of_ae_abs_le {μ : Measure ℝ} [IsFiniteMeasure μ] {R : ℝ}
    (hae : ∀ᵐ x ∂μ, |x| ≤ R) (n : ℕ) : Integrable (fun x : ℝ => x ^ n) μ :=
  integrable_pow_of_ae_norm_le (g := fun x : ℝ => x) aestronglyMeasurable_id
    (hae.mono fun x hx => (Real.norm_eq_abs x).trans_le hx) n

end TauCeti
