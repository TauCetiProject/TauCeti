/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.MeasureTheory.Integral.FinMeasAdditive
public import TauCeti.Analysis.Normed.Order.PositiveLinearMap
public import TauCeti.MeasureTheory.Measure.AddContent

/-!
# Functionals on bounded functions and contents on all subsets

On a discrete space, applying a linear functional to characteristic functions gives a real-valued
content on all subsets. It is nonnegative when the functional is positive, and its total mass is
the functional's value at one.

Conversely, every nonnegative real content `ν` on all subsets of a discrete space `X` arises in
this way from exactly one positive linear functional on `X →ᵇ ℝ`. A finite-valued function `f` is
integrated by the finite sum `∑ c, c * ν {x | f x = c}`. These sums are bounded by `ν univ` times
the supremum norm, and finite-valued functions are uniformly dense among bounded functions, so the
integral extends uniquely by continuity. The extension is positive because it has norm at most its
value `ν univ` at the constant one. This is the correspondence between means and finitely additive
probabilities; neither side involves countable additivity.

We use Mathlib's bounded continuous characteristic functions, with a small API for clopen sets
that also applies without discreteness. The finite sums are Mathlib's
`MeasureTheory.SimpleFunc.setToSimpleFunc`, and the extension is `LinearMap.extendOfNorm`.

## Main definitions

* `LinearMap.toAddContent`: the real content `s ↦ m (indicator s)` of a linear functional `m`.
* `PositiveLinearMap.addContentEquiv`: positive linear functionals on bounded functions on a
  discrete space correspond to nonnegative real contents on all subsets.

## Main results

* `BoundedContinuousFunction.exists_finite_range_dist_lt`: on a discrete space, finite-valued
  functions are uniformly dense among bounded real functions.
* `PositiveLinearMap.addContentEquiv_symm_apply_indicator`: the functional associated to a content
  `ν` takes the value `ν s` at the characteristic function of `s`.

## References

* A. Garrido, *An introduction to amenable groups*, Theorem 1.15.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped BoundedContinuousFunction

namespace BoundedContinuousFunction

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

@[simp]
theorem indicator_empty : indicator (∅ : Set X) isClopen_empty = 0 := by
  ext x
  simp

@[simp]
theorem indicator_univ : indicator (univ : Set X) isClopen_univ = 1 := by
  ext x
  simp

/-- Characteristic functions add on disjoint clopen sets. -/
theorem indicator_union {s t : Set X} (hs : IsClopen s) (ht : IsClopen t)
    (hst : Disjoint s t) : indicator (s ∪ t) (hs.union ht) = indicator s hs + indicator t ht := by
  ext x
  simp only [indicator_apply, Set.indicator_union_of_disjoint hst, add_apply]

/-- A characteristic function is pointwise nonnegative. -/
theorem indicator_nonneg (s : Set X) (hs : IsClopen s) : 0 ≤ indicator s hs := by
  intro x
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) x

/-- Pullback of a characteristic function is the characteristic function of the preimage. -/
@[simp]
theorem indicator_compContinuous (s : Set X) (hs : IsClopen s) (f : C(Y, X)) :
    (indicator s hs).compContinuous f = indicator (f ⁻¹' s) (hs.preimage f.continuous) := by
  ext x
  by_cases hx : f x ∈ s <;> simp [hx]

/-- On a discrete space, every bounded real function is a uniform limit of finite-valued
bounded functions: `δ * ⌊f / δ⌋` is within `δ` of `f`. -/
theorem exists_finite_range_dist_lt [DiscreteTopology X] (f : X →ᵇ ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : X →ᵇ ℝ, (range g).Finite ∧ dist f g < ε := by
  set δ := ε / 2 with hδ_def
  have hδ : 0 < δ := half_pos hε
  have hrange : (range fun x => δ * ⌊f x / δ⌋).Finite := by
    refine ((Set.finite_Icc ⌊-‖f‖ / δ⌋ ⌊‖f‖ / δ⌋).image fun n : ℤ => δ * n).subset
      (range_subset_iff.2 fun x => mem_image_of_mem _ ?_)
    have hx := abs_le.1 (Real.norm_eq_abs (f x) ▸ f.norm_coe_le_norm x)
    exact ⟨Int.floor_mono (div_le_div_of_nonneg_right hx.1 hδ.le),
      Int.floor_mono (div_le_div_of_nonneg_right hx.2 hδ.le)⟩
  refine ⟨mkOfDiscrete _ _ fun x y =>
      Metric.dist_le_diam_of_mem hrange.isBounded (mem_range_self x) (mem_range_self y),
    hrange, lt_of_le_of_lt ((f.dist_le hδ.le).2 fun x => ?_) (by linarith)⟩
  have h : f x - δ * ⌊f x / δ⌋ = δ * Int.fract (f x / δ) := by
    rw [Int.fract, mul_sub, mul_div_cancel₀ _ hδ.ne']
  rw [mkOfDiscrete_apply, Real.dist_eq, h, abs_of_nonneg (mul_nonneg hδ.le (Int.fract_nonneg _))]
  exact mul_le_of_le_one_right hδ.le (Int.fract_lt_one _).le

end BoundedContinuousFunction

namespace LinearMap

variable {X : Type*} [TopologicalSpace X] [DiscreteTopology X]

/-- The real content obtained by evaluating a linear functional on characteristic functions. -/
def toAddContent (m : (X →ᵇ ℝ) →ₗ[ℝ] ℝ) : AddContent ℝ (univ : Set (Set X)) :=
  isSetRing_univ.addContent_of_union
    (fun s => m (BoundedContinuousFunction.indicator s (isClopen_discrete s)))
    (by simp) (by
      intro s _ t _ hst
      rw [BoundedContinuousFunction.indicator_union _ _ hst, map_add])

@[simp 900] -- Prefer normalization at the whole space to expanding the content.
theorem toAddContent_apply (m : (X →ᵇ ℝ) →ₗ[ℝ] ℝ) (s : Set X) :
    m.toAddContent s = m (BoundedContinuousFunction.indicator s (isClopen_discrete s)) :=
  (rfl)

@[simp]
theorem toAddContent_univ (m : (X →ᵇ ℝ) →ₗ[ℝ] ℝ) : m.toAddContent univ = m 1 := by
  simp

end LinearMap

namespace PositiveLinearMap

/-- The content of a positive functional is nonnegative. -/
theorem toAddContent_nonneg {X : Type*} [TopologicalSpace X] [DiscreteTopology X]
    (m : (X →ᵇ ℝ) →ₚ[ℝ] ℝ) (s : Set X) : 0 ≤ m.toLinearMap.toAddContent s :=
  m.map_nonneg (BoundedContinuousFunction.indicator_nonneg _ _)

variable {X : Type*} [TopologicalSpace X] [DiscreteTopology X]

section ofAddContent

/-! ### Integration against a nonnegative content

A nonnegative real content `ν` on all subsets of `X` is integrated first on finite-valued
functions, by `∑ c, c * ν {x | f x = c}`, and then on all bounded functions by uniform
approximation. For the finite sums we use Mathlib's `SimpleFunc.setToSimpleFunc`, with every
subset measurable. We take the zero measure there: for it, `FinMeasAdditive` is plain finite
additivity on disjoint sets, and every function is integrable. -/

/-- Every subset is measurable, so every finite-valued function on `X` is a simple function. -/
private local instance : MeasurableSpace X := ⊤

/-- A finite-valued function as a bounded function. -/
private def simpleFuncToBCF : SimpleFunc X ℝ →ₗ[ℝ] X →ᵇ ℝ where
  toFun g := BoundedContinuousFunction.mkOfDiscrete g (Metric.diam (range g)) fun x y =>
    Metric.dist_le_diam_of_mem g.finite_range.isBounded (mem_range_self x) (mem_range_self y)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
private theorem simpleFuncToBCF_apply (g : SimpleFunc X ℝ) (x : X) :
    simpleFuncToBCF g x = g x :=
  (rfl)

private theorem simpleFuncToBCF_piecewise {s : Set X} (hs : MeasurableSet s) (c : ℝ) :
    simpleFuncToBCF (SimpleFunc.piecewise s hs
      (SimpleFunc.const X c) (SimpleFunc.const X 0)) =
      c • BoundedContinuousFunction.indicator s (isClopen_discrete s) := by
  ext x
  by_cases hx : x ∈ s <;> simp [hx]

/-- Finite-valued functions are uniformly dense in the bounded functions. -/
private theorem denseRange_simpleFuncToBCF :
    DenseRange (simpleFuncToBCF : SimpleFunc X ℝ →ₗ[ℝ] X →ᵇ ℝ) := by
  refine Metric.denseRange_iff.2 fun f ε hε => ?_
  obtain ⟨g, hg, hfg⟩ := f.exists_finite_range_dist_lt hε
  let g' : SimpleFunc X ℝ := ⟨g, fun _ => MeasurableSpace.measurableSet_top, hg⟩
  have hg' : simpleFuncToBCF g' = g := by
    ext x
    simp [g']
  exact ⟨g', hg' ▸ hfg⟩

variable (ν : AddContent ℝ (univ : Set (Set X)))

/-- The set function `s ↦ ν s • id`, in the form used by `SimpleFunc.setToSimpleFunc`. -/
private def contentCLM (s : Set X) : ℝ →L[ℝ] ℝ :=
  ν s • ContinuousLinearMap.id ℝ ℝ

omit [TopologicalSpace X] [DiscreteTopology X] in
private theorem finMeasAdditive_contentCLM :
    FinMeasAdditive (0 : Measure X) (contentCLM ν) := by
  intro s t _ _ _ _ hst
  simp [contentCLM, addContent_union isSetRing_univ (mem_univ s) (mem_univ t) hst, add_smul]

/-- The integral of finite-valued functions against `ν`. -/
private def integralSimple : SimpleFunc X ℝ →ₗ[ℝ] ℝ where
  toFun := SimpleFunc.setToSimpleFunc (contentCLM ν)
  map_add' _ _ := SimpleFunc.setToSimpleFunc_add _ (finMeasAdditive_contentCLM ν)
    integrable_zero_measure integrable_zero_measure
  map_smul' c _ := SimpleFunc.setToSimpleFunc_smul_real _ (finMeasAdditive_contentCLM ν) c
    integrable_zero_measure

omit [TopologicalSpace X] [DiscreteTopology X] in
private theorem integralSimple_apply (g : SimpleFunc X ℝ) :
    integralSimple ν g = SimpleFunc.setToSimpleFunc (contentCLM ν) g :=
  (rfl)

omit [TopologicalSpace X] [DiscreteTopology X] in
private theorem integralSimple_piecewise {s : Set X} (hs : MeasurableSet s) (c : ℝ) :
    integralSimple ν (SimpleFunc.piecewise s hs
      (SimpleFunc.const X c) (SimpleFunc.const X 0)) = c * ν s := by
  rw [integralSimple_apply, SimpleFunc.setToSimpleFunc_indicator _ (by simp [contentCLM])]
  simp [contentCLM, mul_comm]

/-- The integral of bounded functions against `ν`, extending `integralSimple ν` by
continuity. It is meaningful when `ν` is nonnegative. -/
private def integral : (X →ᵇ ℝ) →L[ℝ] ℝ :=
  (integralSimple ν).extendOfNorm simpleFuncToBCF

variable {ν} (hν : ∀ s, 0 ≤ ν s)
include hν

omit [TopologicalSpace X] [DiscreteTopology X] in
private theorem integralSimple_le {g : SimpleFunc X ℝ} {c : ℝ} (h : ∀ x, g x ≤ c) :
    integralSimple ν g ≤ c * ν univ := by
  have := SimpleFunc.setToSimpleFunc_mono (finMeasAdditive_contentCLM ν)
    (fun s _ _ x hx => by simpa [contentCLM] using mul_nonneg (hν s) hx)
    integrable_zero_measure integrable_zero_measure (show g ≤ SimpleFunc.const X c from h)
  rw [SimpleFunc.setToSimpleFunc_const _ (by simp [contentCLM])] at this
  simpa [integralSimple_apply, contentCLM, mul_comm] using this

private theorem norm_integralSimple_le (g : SimpleFunc X ℝ) :
    ‖integralSimple ν g‖ ≤ ν univ * ‖simpleFuncToBCF g‖ := by
  have h x : |g x| ≤ ‖simpleFuncToBCF g‖ := by
    simpa using (simpleFuncToBCF g).norm_coe_le_norm x
  rw [Real.norm_eq_abs, abs_le, mul_comm]
  refine ⟨?_, integralSimple_le hν fun x => (le_abs_self _).trans (h x)⟩
  have := integralSimple_le hν (g := -g) fun x => (neg_le_abs _).trans (h x)
  rw [map_neg] at this
  linarith

private theorem integral_simpleFuncToBCF (g : SimpleFunc X ℝ) :
    integral ν (simpleFuncToBCF g) = integralSimple ν g :=
  LinearMap.extendOfNorm_eq denseRange_simpleFuncToBCF ⟨_, norm_integralSimple_le hν⟩ g

private theorem norm_integral_apply_le (f : X →ᵇ ℝ) : ‖integral ν f‖ ≤ ν univ * ‖f‖ :=
  LinearMap.norm_extendOfNorm_apply_le denseRange_simpleFuncToBCF _ (norm_integralSimple_le hν) f

private theorem integral_indicator (s : Set X) :
    integral ν (BoundedContinuousFunction.indicator s (isClopen_discrete s)) = ν s := by
  have := integral_simpleFuncToBCF hν (SimpleFunc.piecewise s
    MeasurableSpace.measurableSet_top (SimpleFunc.const X 1) (SimpleFunc.const X 0))
  rwa [simpleFuncToBCF_piecewise, integralSimple_piecewise, one_smul, one_mul] at this

/-- The integral against a nonnegative content is positive. -/
private theorem integral_nonneg {f : X →ᵇ ℝ} (hf : 0 ≤ f) : 0 ≤ integral ν f := by
  -- For `0 ≤ f`, the function `‖f‖ - f` has norm at most `‖f‖`, so applying the bound
  -- `|integral g| ≤ ν univ * ‖g‖` to it gives `‖f‖ * ν univ - integral f ≤ ‖f‖ * ν univ`.
  have hbound := norm_integral_apply_le hν (‖f‖ • 1 - f)
  have hnorm : ‖‖f‖ • (1 : X →ᵇ ℝ) - f‖ ≤ ‖f‖ :=
    (BoundedContinuousFunction.norm_le (norm_nonneg f)).2 fun x => by
      have h₁ := f.apply_le_norm x
      have h₀ : 0 ≤ f x := by simpa using hf x
      simp only [BoundedContinuousFunction.coe_sub, BoundedContinuousFunction.coe_smul,
        BoundedContinuousFunction.coe_one, Pi.sub_apply, Pi.one_apply, smul_eq_mul, mul_one,
        Real.norm_eq_abs]
      rw [abs_of_nonneg (by linarith)]
      linarith
  have h₁ : integral ν 1 = ν univ := by
    simpa using integral_indicator hν univ
  rw [map_sub, map_smul, h₁, smul_eq_mul, Real.norm_eq_abs] at hbound
  have := (le_abs_self _).trans hbound
  nlinarith [mul_le_mul_of_nonneg_left hnorm (hν univ)]

omit hν in
/-- A positive functional on bounded functions integrates finite-valued functions against its
content. -/
private theorem comp_simpleFuncToBCF (m : (X →ᵇ ℝ) →ₚ[ℝ] ℝ) :
    m.toLinearMap ∘ₗ simpleFuncToBCF = integralSimple m.toLinearMap.toAddContent := by
  ext g
  induction g using SimpleFunc.induction with
  | const c hs =>
    rw [LinearMap.comp_apply, simpleFuncToBCF_piecewise, integralSimple_piecewise]
    simp
  | add _ hf hg => simp_all

end ofAddContent

variable (X) in
/-- On a discrete space, positive linear functionals on bounded real functions correspond to
nonnegative finitely additive real set functions on all subsets, by evaluating at
characteristic functions. The inverse integrates a bounded function against the content. -/
def addContentEquiv :
    ((X →ᵇ ℝ) →ₚ[ℝ] ℝ) ≃ {ν : AddContent ℝ (univ : Set (Set X)) // ∀ s, 0 ≤ ν s} where
  toFun m := ⟨m.toLinearMap.toAddContent, m.toAddContent_nonneg⟩
  invFun ν := mk₀ (integral ν.1).toLinearMap fun _ hf => integral_nonneg ν.2 hf
  left_inv m := by
    let mL : (X →ᵇ ℝ) →L[ℝ] ℝ :=
      { toLinearMap := m.toLinearMap
        cont := PositiveLinearMap.continuous_of_forall_le_norm_smul m (u := 1) fun f x => by
          simpa using f.apply_le_norm x }
    have h := LinearMap.extendOfNorm_unique denseRange_simpleFuncToBCF _
      (norm_integralSimple_le m.toAddContent_nonneg) mL (comp_simpleFuncToBCF m)
    ext f
    exact congrArg (· f) h
  right_inv ν := by
    ext s
    exact integral_indicator ν.2 s

@[simp]
theorem coe_addContentEquiv_apply (m : (X →ᵇ ℝ) →ₚ[ℝ] ℝ) :
    (addContentEquiv X m : AddContent ℝ (univ : Set (Set X))) = m.toLinearMap.toAddContent :=
  (rfl)

/-- The functional associated to a content takes the value `ν s` at the characteristic
function of `s`. -/
@[simp]
theorem addContentEquiv_symm_apply_indicator
    (ν : {ν : AddContent ℝ (univ : Set (Set X)) // ∀ s, 0 ≤ ν s}) (s : Set X) :
    (addContentEquiv X).symm ν (BoundedContinuousFunction.indicator s (isClopen_discrete s)) =
      ν.1 s :=
  integral_indicator ν.2 s

/-- The functional associated to a content takes its total mass at the constant one. -/
@[simp]
theorem addContentEquiv_symm_apply_one
    (ν : {ν : AddContent ℝ (univ : Set (Set X)) // ∀ s, 0 ≤ ν s}) :
    (addContentEquiv X).symm ν 1 = ν.1 univ := by
  simpa using addContentEquiv_symm_apply_indicator ν univ

end PositiveLinearMap
