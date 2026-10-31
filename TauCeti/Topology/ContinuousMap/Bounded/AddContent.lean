/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Analysis.Normed.Operator.Extend
public import TauCeti.Analysis.Normed.Order.PositiveLinearMap
public import TauCeti.MeasureTheory.Integral.AddContent
public import TauCeti.MeasureTheory.Measure.AddContent
public import TauCeti.Topology.ContinuousMap.Bounded.SimpleFunc

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
that also applies without discreteness. The finite sums are
`MeasureTheory.AddContent.integralSimple`, the density of finite-valued functions is
`MeasureTheory.SimpleFunc.denseRange_toBoundedContinuousFunction`, and the extension is
`LinearMap.extendOfNorm`.

## Main definitions

* `LinearMap.toAddContent`: the real content `s ↦ m (indicator s)` of a linear functional `m`.
* `PositiveLinearMap.addContentEquiv`: positive linear functionals on bounded functions on a
  discrete space correspond to nonnegative real contents on all subsets.

## Main results

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
functions, by `∑ c, c * ν {x | f x = c}` (`MeasureTheory.AddContent.integralSimple`, with every
subset measurable), and then on all bounded functions by uniform approximation. -/

/-- Every subset is measurable, so every finite-valued function on `X` is a simple function. -/
private local instance : MeasurableSpace X := ⊤

variable (ν : AddContent ℝ (univ : Set (Set X)))

/-- The integral of bounded functions against `ν`, extending `ν.integralSimple` by continuity. It
is meaningful when `ν` is nonnegative. -/
private def integral : (X →ᵇ ℝ) →L[ℝ] ℝ :=
  (ν.integralSimple fun s _ => mem_univ s).extendOfNorm
    (SimpleFunc.toBoundedContinuousFunctionLinearMap ℝ)

variable {ν} (hν : ∀ s, 0 ≤ ν s)
include hν

private theorem norm_integralSimple_le (g : SimpleFunc X ℝ) :
    ‖ν.integralSimple (fun s _ => mem_univ s) g‖ ≤
      ν univ * ‖SimpleFunc.toBoundedContinuousFunctionLinearMap ℝ g‖ := by
  rw [Real.norm_eq_abs, mul_comm]
  exact AddContent.abs_integralSimple_le _ (fun s _ => hν s) fun x => by
    simpa using g.toBoundedContinuousFunction.norm_coe_le_norm x

private theorem integral_toBoundedContinuousFunctionLinearMap (g : SimpleFunc X ℝ) :
    integral ν (SimpleFunc.toBoundedContinuousFunctionLinearMap ℝ g) =
      ν.integralSimple (fun s _ => mem_univ s) g :=
  LinearMap.extendOfNorm_eq SimpleFunc.denseRange_toBoundedContinuousFunctionLinearMap
    ⟨_, norm_integralSimple_le hν⟩ g

private theorem norm_integral_apply_le (f : X →ᵇ ℝ) : ‖integral ν f‖ ≤ ν univ * ‖f‖ :=
  LinearMap.norm_extendOfNorm_apply_le SimpleFunc.denseRange_toBoundedContinuousFunctionLinearMap _
    (norm_integralSimple_le hν) f

private theorem integral_indicator (s : Set X) :
    integral ν (BoundedContinuousFunction.indicator s (isClopen_discrete s)) = ν s := by
  have := integral_toBoundedContinuousFunctionLinearMap hν (SimpleFunc.piecewise s
    MeasurableSpace.measurableSet_top (SimpleFunc.const X 1) (SimpleFunc.const X 0))
  rwa [SimpleFunc.toBoundedContinuousFunctionLinearMap_apply,
    SimpleFunc.toBoundedContinuousFunction_piecewise_const, AddContent.integralSimple_piecewise,
    one_smul, one_mul] at this

/-- The integral against a nonnegative content is positive. -/
private theorem integral_nonneg {f : X →ᵇ ℝ} (hf : 0 ≤ f) : 0 ≤ integral ν f := by
  have h₁ : integral ν 1 = ν univ := by
    simpa using integral_indicator hν univ
  refine (integral ν).toLinearMap.apply_nonneg_of_norm_smul_sub_le (u := 1)
    (fun g => by simpa [h₁, ← Real.norm_eq_abs] using norm_integral_apply_le hν g) ?_
  refine (BoundedContinuousFunction.norm_le (norm_nonneg f)).2 fun x => ?_
  have hle := f.apply_le_norm x
  have h₀ : 0 ≤ f x := by simpa using hf x
  simp only [BoundedContinuousFunction.coe_sub, BoundedContinuousFunction.coe_smul,
    BoundedContinuousFunction.coe_one, Pi.sub_apply, Pi.one_apply, smul_eq_mul, mul_one,
    Real.norm_eq_abs]
  rw [abs_of_nonneg (by linarith)]
  linarith

omit hν in
/-- A positive functional on bounded functions is the integral against its content. -/
private theorem integral_toAddContent (m : (X →ᵇ ℝ) →ₚ[ℝ] ℝ) (f : X →ᵇ ℝ) :
    integral m.toLinearMap.toAddContent f = m f := by
  let mL : (X →ᵇ ℝ) →L[ℝ] ℝ :=
    { toLinearMap := m.toLinearMap
      cont := PositiveLinearMap.continuous_of_forall_le_norm_smul m (u := 1) fun f x => by
        simpa using f.apply_le_norm x }
  -- On finite-valued functions, `m` is the integral against its content.
  have hm := AddContent.eq_integralSimple m.toLinearMap.toAddContent (fun s _ => mem_univ s)
    (L := m.toLinearMap ∘ₗ SimpleFunc.toBoundedContinuousFunctionLinearMap ℝ) fun s hs c => by
      rw [LinearMap.comp_apply, SimpleFunc.toBoundedContinuousFunctionLinearMap_apply,
        SimpleFunc.toBoundedContinuousFunction_piecewise_const]
      simp
  have h := LinearMap.extendOfNorm_unique SimpleFunc.denseRange_toBoundedContinuousFunctionLinearMap
    _ (norm_integralSimple_le m.toAddContent_nonneg) mL hm
  exact congrArg (· f) h

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
    ext f
    exact integral_toAddContent m f
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
