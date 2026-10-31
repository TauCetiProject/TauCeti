/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Analysis.Normed.Operator.Extend
public import TauCeti.Analysis.Normed.Order.PositiveLinearMap
public import TauCeti.MeasureTheory.Function.Lp.LeftTranslation
public import TauCeti.MeasureTheory.Function.Lp.SimpleFunc
public import TauCeti.MeasureTheory.Integral.AddContent
public import TauCeti.MeasureTheory.Measure.AddContent

/-!
# Positive functionals on `L∞` and finitely additive set functions

Let `μ` be a measure on a measurable space `α`. Evaluating a linear functional `M` on `L∞(μ)` at
indicator classes gives a real finitely additive set function on the measurable sets,

```text
ν(A) = M [1_A],
```

which vanishes on `μ`-null sets (`LinearMap.toAddContentLpTop`). It is nonnegative when `M` is
positive, and its total mass is `M 1`.

Conversely, every real content `ν` on the measurable sets which is nonnegative and vanishes on
`μ`-null sets arises in this way from exactly one positive functional
(`PositiveLinearMap.ofAddContentLpTop`). A simple function `g` is integrated by the finite sum
`∑ c, c * ν {x | g x = c}`. Since `ν` annihilates null sets, this depends only on the class of `g`
in `L∞`, and it is bounded by `ν univ` times the essential supremum of `g`. Simple functions are
dense in `L∞`, so the integral extends uniquely by continuity, and it is positive because it has
norm at most its value `ν univ` at the constant one. Neither side involves countable additivity,
and `μ` need not be σ-finite. Only the values of `ν` on measurable sets enter; the content of a
functional is `0` on the other sets.

For a left-invariant measure on a group, a positive functional is invariant under left translation
exactly when its content is invariant under left translation of measurable sets. Hence `L∞(μ)`
carries a left-invariant normalized positive functional exactly when the measurable sets carry a
left-invariant finitely additive probability vanishing on `μ`-null sets
(`MeasureTheory.exists_positiveLinearMap_lpTop_iff_exists_addContent`).

The finite sums are `MeasureTheory.AddContent.integralSimple`, the density of simple functions is
`MeasureTheory.SimpleFunc.denseRange_toLpTop`, and the extension is `LinearMap.extendOfNorm`, as in
the correspondence for bounded functions on a discrete space, `PositiveLinearMap.addContentEquiv`.

## Main definitions

* `LinearMap.toAddContentLpTop`: the content `s ↦ M [1_s]` of a linear functional on `L∞`.
* `PositiveLinearMap.ofAddContentLpTop`: the positive functional on `L∞` integrating against a
  nonnegative content which vanishes on null sets.

## Main results

* `PositiveLinearMap.ofAddContentLpTop_toLpTop`: the functional associated to `ν` integrates simple
  functions against `ν`.
* `PositiveLinearMap.toAddContentLpTop_ofAddContentLpTop_apply`,
  `PositiveLinearMap.ofAddContentLpTop_toAddContentLpTop`: the two constructions are inverse, on
  measurable sets.
* `PositiveLinearMap.toAddContentLpTop_injective`: a positive functional on `L∞` is determined by
  its values at indicator classes.
* `PositiveLinearMap.forall_apply_leftTranslation_iff`: a positive functional is invariant under
  left translation exactly when its content is.
* `MeasureTheory.exists_positiveLinearMap_lpTop_iff_exists_addContent`: invariant normalized
  positive functionals on `L∞` exist exactly when invariant finitely additive probabilities
  vanishing on null sets do.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G, in particular
  Theorem G.3.1.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped ENNReal Pointwise

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}

namespace LinearMap

open scoped Classical in
/-- The real content `s ↦ M [1_s]` on the measurable sets of a linear functional `M` on `L∞(μ)`,
where `[1_s]` is the indicator class of `s`. It is `0` on sets which are not measurable. -/
def toAddContentLpTop (M : Lp ℝ ∞ μ →ₗ[ℝ] ℝ) : AddContent ℝ {s : Set α | MeasurableSet s} :=
  isSetRing_measurableSet.addContent_of_union
    (fun s => if hs : MeasurableSet s then M (indicatorConstLpTop μ hs 1) else 0)
    (by simp [indicatorConstLpTop_eq_zero μ MeasurableSet.empty measure_empty]) (by
      intro s t hs ht hst
      have hs' : MeasurableSet s := hs
      have ht' : MeasurableSet t := ht
      simp only [hs', ht', hs'.union ht', dite_true, indicatorConstLpTop_union μ hs' ht' hst,
        map_add])

open scoped Classical in
private theorem toAddContentLpTop_eq (M : Lp ℝ ∞ μ →ₗ[ℝ] ℝ) (s : Set α) :
    M.toAddContentLpTop s = if hs : MeasurableSet s then M (indicatorConstLpTop μ hs 1) else 0 :=
  (rfl)

/-- The content of `M` at a measurable set `s` is the value of `M` at the indicator class of
`s`. -/
@[simp]
theorem toAddContentLpTop_apply (M : Lp ℝ ∞ μ →ₗ[ℝ] ℝ) (hs : MeasurableSet s) :
    M.toAddContentLpTop s = M (indicatorConstLpTop μ hs 1) := by
  simp [toAddContentLpTop_eq, hs]

/-- The content of `M` is `0` on sets which are not measurable. -/
theorem toAddContentLpTop_of_not_measurableSet (M : Lp ℝ ∞ μ →ₗ[ℝ] ℝ)
    (hs : ¬MeasurableSet s) : M.toAddContentLpTop s = 0 := by
  simp [toAddContentLpTop_eq, hs]

/-- The total mass of the content of `M` is the value of `M` at the constant one. -/
theorem toAddContentLpTop_univ (M : Lp ℝ ∞ μ →ₗ[ℝ] ℝ) :
    M.toAddContentLpTop univ = M TauCeti.linftyOne := by
  simp

/-- The content of a functional on `L∞(μ)` vanishes on `μ`-null sets. -/
theorem toAddContentLpTop_eq_zero (M : Lp ℝ ∞ μ →ₗ[ℝ] ℝ) (hμs : μ s = 0) :
    M.toAddContentLpTop s = 0 := by
  by_cases hs : MeasurableSet s
  · simp [hs, indicatorConstLpTop_eq_zero μ hs hμs]
  · exact M.toAddContentLpTop_of_not_measurableSet hs

end LinearMap

namespace PositiveLinearMap

/-- The content of a positive functional on `L∞` is nonnegative. -/
theorem toAddContentLpTop_nonneg (M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ) (s : Set α) :
    0 ≤ M.toLinearMap.toAddContentLpTop s := by
  by_cases hs : MeasurableSet s
  · simpa [hs] using M.map_nonneg (indicatorConstLpTop_nonneg μ hs zero_le_one)
  · rw [LinearMap.toAddContentLpTop_of_not_measurableSet _ hs]

section ofAddContent

/-! ### Integration against a content vanishing on null sets

A real content `ν` on the measurable sets is integrated first on simple functions, by
`∑ c, c * ν {x | g x = c}` (`MeasureTheory.AddContent.integralSimple`), and then on all of `L∞` by
continuity. -/

variable (ν : AddContent ℝ {s : Set α | MeasurableSet s})

variable (μ) in
/-- The integral against `ν` on `L∞(μ)`, extending `ν.integralSimple` by continuity. It is
meaningful when `ν` is nonnegative and vanishes on `μ`-null sets. -/
private def integral : Lp ℝ ∞ μ →L[ℝ] ℝ :=
  (ν.integralSimple fun _ hs => hs).extendOfNorm (SimpleFunc.toLpTop μ ℝ)

variable {ν} (hν : ∀ s, MeasurableSet s → 0 ≤ ν s)
  (hnull : ∀ s, MeasurableSet s → μ s = 0 → ν s = 0)
include hν hnull

private theorem norm_integralSimple_le (g : SimpleFunc α ℝ) :
    ‖ν.integralSimple (fun _ hs => hs) g‖ ≤ ν univ * ‖SimpleFunc.toLpTop μ ℝ g‖ := by
  set c := ‖SimpleFunc.toLpTop μ ℝ g‖
  -- Clamping `g` to `[-c, c]` changes it only on a null set.
  have hgg' : g =ᵐ[μ] g.map fun y => max (-c) (min c y) :=
    Lp.ae_eq_max_min_norm_top (SimpleFunc.coeFn_toLpTop (𝕜 := ℝ) g)
  rw [AddContent.integralSimple_congr_ae _ hnull hgg', Real.norm_eq_abs, mul_comm]
  refine AddContent.abs_integralSimple_le _ hν fun x => abs_le.2
    ⟨le_max_left _ _, max_le ?_ (min_le_left _ _)⟩
  linarith [norm_nonneg (SimpleFunc.toLpTop μ ℝ g)]

private theorem integral_toLpTop (g : SimpleFunc α ℝ) :
    integral μ ν (SimpleFunc.toLpTop μ ℝ g) = ν.integralSimple (fun _ hs => hs) g :=
  LinearMap.extendOfNorm_eq SimpleFunc.denseRange_toLpTop ⟨_, norm_integralSimple_le hν hnull⟩ g

private theorem norm_integral_apply_le (f : Lp ℝ ∞ μ) : ‖integral μ ν f‖ ≤ ν univ * ‖f‖ :=
  LinearMap.norm_extendOfNorm_apply_le SimpleFunc.denseRange_toLpTop _
    (norm_integralSimple_le hν hnull) f

private theorem integral_indicatorConstLpTop (hs : MeasurableSet s) :
    integral μ ν (indicatorConstLpTop μ hs 1) = ν s := by
  rw [← SimpleFunc.toLpTop_piecewise_const (𝕜 := ℝ), integral_toLpTop hν hnull,
    AddContent.integralSimple_piecewise, one_mul]

/-- The integral against a nonnegative content vanishing on null sets is positive. -/
private theorem integral_nonneg {f : Lp ℝ ∞ μ} (hf : 0 ≤ f) : 0 ≤ integral μ ν f := by
  have h₁ : integral μ ν TauCeti.linftyOne = ν univ := by
    simpa using integral_indicatorConstLpTop hν hnull MeasurableSet.univ
  refine (integral μ ν).toLinearMap.apply_nonneg_of_norm_smul_sub_le (u := TauCeti.linftyOne)
    (fun g => by simpa [h₁, ← Real.norm_eq_abs] using norm_integral_apply_le hν hnull g) ?_
  refine Lp.norm_le_of_ae_bound_top (norm_nonneg f) ?_
  filter_upwards [Lp.coeFn_sub (‖f‖ • TauCeti.linftyOne) f,
    Lp.coeFn_smul ‖f‖ (TauCeti.linftyOne (μ := μ)), TauCeti.coeFn_linftyOne,
    (Lp.coeFn_nonneg f).2 hf, Lp.ae_norm_le_norm_top f] with x hsub hsmul h1 h0 hle
  rw [Pi.zero_apply] at h0
  rw [Real.norm_eq_abs, abs_of_nonneg h0] at hle
  rw [hsub, Pi.sub_apply, hsmul, Pi.smul_apply, h1, smul_eq_mul, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (by linarith)]
  linarith

omit hν hnull in
/-- A positive functional on `L∞` is the integral against its content. -/
private theorem integral_toAddContentLpTop (M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ) (f : Lp ℝ ∞ μ) :
    integral μ M.toLinearMap.toAddContentLpTop f = M f := by
  let mL : Lp ℝ ∞ μ →L[ℝ] ℝ :=
    { toLinearMap := M.toLinearMap
      cont := PositiveLinearMap.continuous_of_forall_le_norm_smul M Lp.le_norm_smul_linftyOne }
  -- On simple functions, `M` is the integral against its content.
  have hM := AddContent.eq_integralSimple M.toLinearMap.toAddContentLpTop (fun _ hs => hs)
    (L := M.toLinearMap ∘ₗ SimpleFunc.toLpTop μ ℝ) fun s hs c => by
      rw [LinearMap.comp_apply, SimpleFunc.toLpTop_piecewise_const]
      simpa [hs] using congrArg M (indicatorConstLpTop_smul μ hs c (1 : ℝ))
  have h := LinearMap.extendOfNorm_unique SimpleFunc.denseRange_toLpTop _
    (norm_integralSimple_le (fun s _ => M.toAddContentLpTop_nonneg s)
      (fun _ _ h => M.toLinearMap.toAddContentLpTop_eq_zero h)) mL hM
  exact congrArg (· f) h

omit hν hnull in
variable (ν) in
/-- The positive functional on `L∞(μ)` integrating against a real content `ν` on the measurable
sets which is nonnegative and vanishes on `μ`-null sets. -/
def ofAddContentLpTop (hν : ∀ s, MeasurableSet s → 0 ≤ ν s)
    (hnull : ∀ s, MeasurableSet s → μ s = 0 → ν s = 0) : Lp ℝ ∞ μ →ₚ[ℝ] ℝ :=
  mk₀ (integral μ ν).toLinearMap fun _ hf => integral_nonneg hν hnull hf

/-- The functional associated to a content `ν` takes the value `ν s` at the indicator class of a
measurable set `s`. -/
@[simp]
theorem ofAddContentLpTop_apply_indicatorConstLpTop (hs : MeasurableSet s) :
    ofAddContentLpTop ν hν hnull (indicatorConstLpTop μ hs 1) = ν s :=
  integral_indicatorConstLpTop hν hnull hs

/-- The functional associated to a content takes its total mass at the constant one. -/
@[simp]
theorem ofAddContentLpTop_linftyOne :
    ofAddContentLpTop ν hν hnull TauCeti.linftyOne = ν univ := by
  simpa using ofAddContentLpTop_apply_indicatorConstLpTop hν hnull MeasurableSet.univ

/-- The functional associated to a content `ν` integrates the class of a simple function against
`ν`. -/
@[simp]
theorem ofAddContentLpTop_toLpTop (g : SimpleFunc α ℝ) :
    ofAddContentLpTop ν hν hnull (SimpleFunc.toLpTop μ ℝ g) = ν.integralSimple (fun _ hs => hs) g :=
  integral_toLpTop hν hnull g

/-- The content of the functional associated to `ν` agrees with `ν` on measurable sets. -/
theorem toAddContentLpTop_ofAddContentLpTop_apply (hs : MeasurableSet s) :
    (ofAddContentLpTop ν hν hnull).toLinearMap.toAddContentLpTop s = ν s := by
  simp [hs]

end ofAddContent

/-- A positive functional on `L∞` is the integral against its content. -/
@[simp]
theorem ofAddContentLpTop_toAddContentLpTop (M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ) :
    ofAddContentLpTop M.toLinearMap.toAddContentLpTop (fun s _ => M.toAddContentLpTop_nonneg s)
      (fun _ _ h => M.toLinearMap.toAddContentLpTop_eq_zero h) = M := by
  ext f
  exact integral_toAddContentLpTop M f

/-- A positive functional on `L∞` is determined by its content. -/
theorem toAddContentLpTop_injective :
    Function.Injective fun M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ => M.toLinearMap.toAddContentLpTop := by
  intro M M' h
  rw [← ofAddContentLpTop_toAddContentLpTop M, ← ofAddContentLpTop_toAddContentLpTop M']
  simp_rw [h]

/-- Two positive functionals on `L∞` agreeing at the indicator classes of all measurable sets are
equal. -/
theorem ext_indicatorConstLpTop {M M' : Lp ℝ ∞ μ →ₚ[ℝ] ℝ}
    (h : ∀ s (hs : MeasurableSet s), M (indicatorConstLpTop μ hs 1) =
      M' (indicatorConstLpTop μ hs 1)) : M = M' := by
  refine toAddContentLpTop_injective (AddContent.ext fun s => ?_)
  by_cases hs : MeasurableSet s
  · simpa [hs] using h s hs
  · simp [LinearMap.toAddContentLpTop_of_not_measurableSet _ hs]

section LeftTranslation

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] {μ : Measure G}
  [μ.IsMulLeftInvariant]

/-- A positive functional on `L∞` of a left-invariant measure is invariant under left translation
exactly when its content is invariant under left translation of measurable sets. -/
theorem forall_apply_leftTranslation_iff (M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ) :
    (∀ g φ, M (Lp.leftTranslation μ ∞ ℝ g φ) = M φ) ↔
      ∀ (g : G) (s : Set G), MeasurableSet s →
        M.toLinearMap.toAddContentLpTop (g • s) = M.toLinearMap.toAddContentLpTop s := by
  refine ⟨fun h g s hs => ?_, fun h g => ?_⟩
  · have := h g (indicatorConstLpTop μ hs 1)
    rw [Lp.leftTranslation_indicatorConstLpTop] at this
    simpa [hs, hs.const_smul g] using this
  -- `M ∘ L_g` is a positive functional with the same content as `M`.
  let Mg : Lp ℝ ∞ μ →ₚ[ℝ] ℝ := mk₀ (M.toLinearMap ∘ₗ (Lp.leftTranslation μ ∞ ℝ g).toLinearMap)
    fun φ hφ => M.map_nonneg (by simpa using Lp.leftTranslation_mono g hφ)
  have hMg : Mg = M := ext_indicatorConstLpTop fun s hs => by
    have : M (indicatorConstLpTop μ (hs.const_smul g) 1) = M (indicatorConstLpTop μ hs 1) := by
      simpa [hs, hs.const_smul g] using h g s hs
    -- `Mg φ` is by definition `M (L_g φ)`; `PositiveLinearMap.mk₀` has no evaluation lemma.
    calc Mg (indicatorConstLpTop μ hs 1)
        = M (Lp.leftTranslation μ ∞ ℝ g (indicatorConstLpTop μ hs 1)) := rfl
      _ = M (indicatorConstLpTop μ hs 1) := by
        rw [Lp.leftTranslation_indicatorConstLpTop, this]
  exact fun φ => congrArg (· φ) hMg

end LeftTranslation

end PositiveLinearMap

namespace MeasureTheory

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] {μ : Measure G}
  [μ.IsMulLeftInvariant]

/-- **Invariant means on `L∞` and invariant finitely additive probabilities.** For a
left-invariant measure `μ` on a group, `L∞(μ)` carries a positive linear functional taking the
value one at one and invariant under left translation exactly when the measurable sets carry a
finitely additive probability which vanishes on `μ`-null sets and is invariant under left
translation. -/
theorem exists_positiveLinearMap_lpTop_iff_exists_addContent :
    (∃ M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ, M TauCeti.linftyOne = 1 ∧
      ∀ g φ, M (Lp.leftTranslation μ ∞ ℝ g φ) = M φ) ↔
    ∃ ν : AddContent ℝ≥0∞ {s : Set G | MeasurableSet s}, ν univ = 1 ∧
      (∀ s, MeasurableSet s → μ s = 0 → ν s = 0) ∧
      ∀ (g : G) (s : Set G), MeasurableSet s → ν (g • s) = ν s := by
  constructor
  · rintro ⟨M, h1, hM⟩
    refine ⟨M.toLinearMap.toAddContentLpTop.ofReal fun s _ => M.toAddContentLpTop_nonneg s,
      by simp [h1], fun s _ hμs => ?_, fun g s hs => ?_⟩
    · simp [LinearMap.toAddContentLpTop_eq_zero _ hμs]
    · rw [AddContent.ofReal_apply, AddContent.ofReal_apply,
        (PositiveLinearMap.forall_apply_leftTranslation_iff M).1 hM g s hs]
  · rintro ⟨ν, h1, hnull, hν⟩
    -- `ν` is finite on measurable sets, so it is the extension of a real content.
    have hfin : ∀ s ∈ {s : Set G | MeasurableSet s}, ν s ≠ ∞ := fun s hs =>
      ne_top_of_le_ne_top (h1 ▸ ENNReal.one_ne_top) (addContent_mono
        isSetRing_measurableSet.isSetSemiring hs MeasurableSet.univ (subset_univ s))
    set ν' := ν.toReal hfin
    have hν' : ∀ s, MeasurableSet s → 0 ≤ ν' s := fun s _ => AddContent.toReal_nonneg _ _ s
    have hnull' : ∀ s, MeasurableSet s → μ s = 0 → ν' s = 0 := fun s hs hμs => by
      simp [ν', hnull s hs hμs]
    refine ⟨PositiveLinearMap.ofAddContentLpTop ν' hν' hnull', by simp [ν', h1], ?_⟩
    refine (PositiveLinearMap.forall_apply_leftTranslation_iff _).2 fun g s hs => ?_
    simp [hs, hs.const_smul g, ν', hν g s hs]

end MeasureTheory
