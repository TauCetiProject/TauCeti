/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.MeasureTheory.Measure.OpenPos
public import TauCeti.MeasureTheory.Function.Lp.One

/-!
# Bounded continuous functions in `L∞`

Every bounded continuous function is essentially bounded, for any measure. Mathlib's
`BoundedContinuousFunction.toLp` sends bounded continuous functions to `Lp E p μ` only for a
finite measure; for `p = ∞` no finiteness is needed, and `BoundedContinuousFunction.toLpTop`
is the corresponding continuous linear map `(α →ᵇ E) →L[𝕜] Lp E ∞ μ`, of norm at most one.

When `μ` is positive on nonempty open sets, the essential supremum of a continuous function is
its supremum, so `toLpTop` preserves norms and is injective. For real-valued functions it is
monotone, an order embedding when `μ` is positive on open sets, and sends the constant
function one to the constant class `TauCeti.linftyOne`. This is the comparison between
supremum and essential-supremum norms used, for instance, to compare means on bounded
uniformly continuous functions on a locally compact group with means on Haar `L∞`.

On a discrete space, if `μ` charges every point, the only null set is empty, so every
essentially bounded function is bounded and `toLpTop` is onto: it identifies bounded functions
with `L∞` as normed spaces and, for real values, as ordered spaces. For instance, `L∞` of a
counting measure, or of a Haar measure on a discrete group, consists of all bounded functions.

## Main definitions

* `BoundedContinuousFunction.toLpTop μ 𝕜`: the class of a bounded continuous function in
  `Lp E ∞ μ`, as a continuous linear map.
* `BoundedContinuousFunction.toLpTopLinearIsometryEquiv μ 𝕜`: on a discrete space, for a
  measure charging every point, `toLpTop` as a linear isometry equivalence.

## Main results

* `BoundedContinuousFunction.coeFn_toLpTop`: the class of `f` is almost everywhere `f`.
* `BoundedContinuousFunction.toLp_top_eq_toLpTop`: for a finite measure it agrees with
  `BoundedContinuousFunction.toLp`.
* `BoundedContinuousFunction.norm_toLpTop_le`: `‖[f]‖ ≤ ‖f‖` for every measure.
* `BoundedContinuousFunction.norm_toLpTop`: `‖[f]‖ = ‖f‖` when `μ` is positive on open sets.
* `BoundedContinuousFunction.toLpTop_le_toLpTop_iff`: for such `μ`, the map is an order
  embedding on real-valued functions.
* `BoundedContinuousFunction.toLpTop_surjective`: on a discrete space, for a measure charging
  every point, every class in `L∞` is the class of a bounded function.
* `BoundedContinuousFunction.toLpTop_one`: the constant function one goes to the constant one.
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal BoundedContinuousFunction

namespace BoundedContinuousFunction

variable {α E : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [NormedAddCommGroup E] [SecondCountableTopologyEither α E] (μ : Measure α)

/-- The almost-everywhere class of a bounded continuous function lies in `L∞`, whatever the
measure. -/
theorem mem_Lp_top (f : α →ᵇ E) : f.toContinuousMap.toAEEqFun μ ∈ Lp E ∞ μ := by
  rw [Lp.mem_Lp_iff_memLp]
  exact (memLp_top f).ae_eq (f.toContinuousMap.coeFn_toAEEqFun μ).symm

private theorem norm_toAEEqFun_le (f : α →ᵇ E) :
    ‖(⟨f.toContinuousMap.toAEEqFun μ, mem_Lp_top μ f⟩ : Lp E ∞ μ)‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable _)]
  refine ENNReal.toReal_le_of_le_ofReal (norm_nonneg f) (eLpNormEssSup_le_of_ae_bound ?_)
  filter_upwards [f.toContinuousMap.coeFn_toAEEqFun μ] with x hx
  exact hx ▸ f.norm_coe_le_norm x

variable (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- The class in `L∞` of a bounded continuous function, as a continuous linear map. Unlike
`BoundedContinuousFunction.toLp`, no finiteness of the measure is required. -/
def toLpTop : (α →ᵇ E) →L[𝕜] Lp E ∞ μ :=
  LinearMap.mkContinuous
    (LinearMap.codRestrict (Lp.LpSubmodule 𝕜 E ∞ μ)
      ((ContinuousMap.toAEEqFunLinearMap μ).comp (toContinuousMapLinearMap α E 𝕜))
      (mem_Lp_top μ))
    1 fun f => (one_mul ‖f‖).symm ▸ norm_toAEEqFun_le μ f

variable {𝕜}

/-- The class of `f` in `L∞` is almost everywhere equal to `f`. -/
theorem coeFn_toLpTop (f : α →ᵇ E) : toLpTop μ 𝕜 f =ᵐ[μ] f :=
  f.toContinuousMap.coeFn_toAEEqFun μ

/-- For a finite measure, `toLpTop` is Mathlib's `BoundedContinuousFunction.toLp` with
exponent `∞`. -/
theorem toLp_top_eq_toLpTop [IsFiniteMeasure μ] :
    (toLp ∞ μ 𝕜 : (α →ᵇ E) →L[𝕜] Lp E ∞ μ) = toLpTop μ 𝕜 :=
  ContinuousLinearMap.ext fun f => Lp.ext ((coeFn_toLp ∞ μ 𝕜 f).trans (coeFn_toLpTop μ f).symm)

/-- The essential supremum norm of a bounded continuous function is at most its supremum norm. -/
theorem norm_toLpTop_le (f : α →ᵇ E) : ‖toLpTop μ 𝕜 f‖ ≤ ‖f‖ :=
  norm_toAEEqFun_le μ f

variable [μ.IsOpenPosMeasure]

/-- If `μ` is positive on nonempty open sets, the essential supremum norm of a bounded continuous
function is its supremum norm. -/
@[simp]
theorem norm_toLpTop (f : α →ᵇ E) : ‖toLpTop μ 𝕜 f‖ = ‖f‖ := by
  refine (norm_toLpTop_le μ f).antisymm ((norm_le (norm_nonneg _)).2 fun x => ?_)
  have h := ae_le_lpNorm_exponent_top (Lp.memLp (toLpTop μ 𝕜 f))
  rw [← toReal_eLpNorm, ← Lp.norm_def] at h
  have hae : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖toLpTop μ 𝕜 f‖ := by
    filter_upwards [coeFn_toLpTop μ (𝕜 := 𝕜) f, h] with x hx h
    exact hx ▸ h
  -- A closed conull set is everything, since `μ` charges every nonempty open set.
  have hclosed : IsClosed {x | ‖f x‖ ≤ ‖toLpTop μ 𝕜 f‖} := isClosed_le (by fun_prop) (by fun_prop)
  exact Set.eq_univ_iff_forall.1 (hclosed.ae_eq_univ_iff_eq.1 (ae_eq_univ.2 hae)) x

/-- If `μ` is positive on nonempty open sets, a bounded continuous function is determined by its
class in `L∞`. -/
theorem toLpTop_injective : Function.Injective (toLpTop μ 𝕜 : (α →ᵇ E) →L[𝕜] Lp E ∞ μ) :=
  fun f g h => by
    rw [← sub_eq_zero, ← norm_eq_zero, ← norm_toLpTop μ (𝕜 := 𝕜), map_sub, h, sub_self,
      norm_zero]

section Discrete

variable [DiscreteTopology α]

/-- On a discrete space, if `μ` charges every point, every class in `L∞` is the class of a
bounded function. -/
theorem toLpTop_surjective :
    Function.Surjective (toLpTop μ 𝕜 : (α →ᵇ E) →L[𝕜] Lp E ∞ μ) := by
  intro φ
  -- Singletons are open, so the only `μ`-null set is empty and a.e. bounds hold everywhere.
  have hae : ae μ = ⊤ := ae_eq_top.2 fun x =>
    (isOpen_discrete {x}).measure_ne_zero μ (Set.singleton_nonempty x)
  have h := ae_le_lpNorm_exponent_top (Lp.memLp φ)
  rw [hae, eventually_top] at h
  exact ⟨ofNormedAddCommGroupDiscrete φ _ h, Lp.ext (coeFn_toLpTop μ _)⟩

variable (𝕜) in
/-- On a discrete space, if `μ` charges every point, taking classes identifies bounded functions
with `L∞`, isometrically. -/
def toLpTopLinearIsometryEquiv : (α →ᵇ E) ≃ₗᵢ[𝕜] Lp E ∞ μ :=
  LinearIsometryEquiv.ofSurjective ⟨(toLpTop μ 𝕜).toLinearMap, norm_toLpTop μ⟩
    (toLpTop_surjective μ)

@[simp]
theorem coe_toLpTopLinearIsometryEquiv :
    ⇑(toLpTopLinearIsometryEquiv μ 𝕜 : (α →ᵇ E) ≃ₗᵢ[𝕜] Lp E ∞ μ) = toLpTop μ 𝕜 :=
  (rfl)

@[simp]
theorem toLpTop_toLpTopLinearIsometryEquiv_symm (φ : Lp E ∞ μ) :
    toLpTop μ 𝕜 ((toLpTopLinearIsometryEquiv μ 𝕜).symm φ) = φ :=
  (toLpTopLinearIsometryEquiv μ 𝕜).apply_symm_apply φ

@[simp]
theorem toLpTopLinearIsometryEquiv_symm_toLpTop (f : α →ᵇ E) :
    (toLpTopLinearIsometryEquiv μ 𝕜).symm (toLpTop μ 𝕜 f) = f :=
  (toLpTopLinearIsometryEquiv μ 𝕜).symm_apply_apply f

end Discrete

end BoundedContinuousFunction

namespace BoundedContinuousFunction

/-! ### Real-valued functions -/

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  (μ : Measure α)

/-- The class in `L∞` of a pointwise smaller bounded continuous function is smaller. -/
theorem toLpTop_mono {f g : α →ᵇ ℝ} (h : f ≤ g) : toLpTop μ ℝ f ≤ toLpTop μ ℝ g := by
  rw [← Lp.coeFn_le]
  filter_upwards [coeFn_toLpTop μ (𝕜 := ℝ) f, coeFn_toLpTop μ (𝕜 := ℝ) g] with x hf hg
  exact hf ▸ hg ▸ h x

/-- If `μ` is positive on nonempty open sets, comparing classes in `L∞` compares bounded
continuous functions pointwise. -/
@[simp]
theorem toLpTop_le_toLpTop_iff [μ.IsOpenPosMeasure] {f g : α →ᵇ ℝ} :
    toLpTop μ ℝ f ≤ toLpTop μ ℝ g ↔ f ≤ g := by
  refine ⟨fun h x => ?_, toLpTop_mono μ⟩
  have hclosed : IsClosed {x | f x ≤ g x} := isClosed_le (by fun_prop) (by fun_prop)
  have hae : ∀ᵐ x ∂μ, f x ≤ g x := by
    filter_upwards [coeFn_toLpTop μ (𝕜 := ℝ) f, coeFn_toLpTop μ (𝕜 := ℝ) g,
      (Lp.coeFn_le _ _).2 h] with x hf hg hfg
    exact hf ▸ hg ▸ hfg
  exact Set.eq_univ_iff_forall.1 (hclosed.ae_eq_univ_iff_eq.1 (ae_eq_univ.2 hae)) x

/-- On a discrete space, if `μ` charges every point, the inverse identification of `L∞` with
bounded functions preserves and reflects the order. -/
@[simp]
theorem toLpTopLinearIsometryEquiv_symm_le_symm_iff [DiscreteTopology α] [μ.IsOpenPosMeasure]
    {φ ψ : Lp ℝ ∞ μ} :
    (toLpTopLinearIsometryEquiv μ ℝ).symm φ ≤ (toLpTopLinearIsometryEquiv μ ℝ).symm ψ ↔ φ ≤ ψ := by
  rw [← toLpTop_le_toLpTop_iff μ, toLpTop_toLpTopLinearIsometryEquiv_symm,
    toLpTop_toLpTopLinearIsometryEquiv_symm]

/-- The constant function one goes to the constant class one in `L∞`. -/
@[simp]
theorem toLpTop_one : toLpTop μ ℝ (1 : α →ᵇ ℝ) = TauCeti.linftyOne :=
  Lp.ext ((coeFn_toLpTop μ 1).trans TauCeti.coeFn_linftyOne.symm)

end BoundedContinuousFunction
