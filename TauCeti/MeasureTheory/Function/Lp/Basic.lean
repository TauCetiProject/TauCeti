/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Finite sums of `MemLp.toLp` classes, and composition with a continuous linear map

Mathlib provides `MeasureTheory.MemLp.toLp_zero`, `MeasureTheory.MemLp.toLp_add`, and
`MeasureTheory.Lp.coeFn_finsetSum`, as well as `MeasureTheory.memLp_finsetSum` and
`MeasureTheory.memLp_finsetSum'`. This file records the companion identities identifying the `Lp`
class of a finite sum of `Lᵖ` functions with the sum of their `Lp` classes, for any `MemLp`
witness on the sum.

Mathlib composes `f : Lp E p μ` with `L : E →SL[σ] F` both as an element `L.compLp f` and through
the bundled continuous semilinear map `L.compLpL p μ`; this file also records that the two agree.
For a linear isometry equivalence `R` of the values, the composition `f ↦ R ∘ f` is a linear
isometry equivalence of `Lp`, with inverse `f ↦ R.symm ∘ f`.

## Main declarations

* `MeasureTheory.MemLp.toLp_finsetSum'`: `hsum.toLp (∑ i ∈ s, f i) = ∑ i ∈ s, (hf i).toLp (f i)`.
* `MeasureTheory.MemLp.toLp_finsetSum`:
  `hsum.toLp (fun x ↦ ∑ i ∈ s, f i x) = ∑ i ∈ s, (hf i).toLp (f i)`.
* `ContinuousLinearMap.compLpL_apply`: the bundled composition applied to `f` is `L.compLp f`.
* `LinearIsometryEquiv.compLpₗᵢEquiv`: pointwise composition with a linear isometry equivalence
  of the values, as a linear isometry equivalence of `Lp`, with
  `LinearIsometryEquiv.coeFn_compLpₗᵢEquiv`, and its identity, composition and inverse laws
  `LinearIsometryEquiv.compLpₗᵢEquiv_refl`, `LinearIsometryEquiv.compLpₗᵢEquiv_trans` and
  `LinearIsometryEquiv.compLpₗᵢEquiv_symm`.
-/

public section

open scoped ENNReal

namespace MeasureTheory.MemLp

variable {α E ι : Type*} {_ : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]
  {p : ℝ≥0∞} {s : Finset ι} {f : ι → α → E}

/-- The `Lp` class of a finite sum of `Lᵖ` functions is the sum of their `Lp` classes. -/
theorem toLp_finsetSum' (hsum : MemLp (∑ i ∈ s, f i) p μ) (hf : ∀ i, MemLp (f i) p μ) :
    hsum.toLp (∑ i ∈ s, f i) = ∑ i ∈ s, (hf i).toLp (f i) :=
  Lp.ext_iff.2 <| hsum.coeFn_toLp.trans <|
    (eventuallyEq_sum fun i _ ↦ (hf i).coeFn_toLp.symm).trans
      (Lp.coeFn_finsetSum s fun i ↦ (hf i).toLp (f i)).symm

/-- The `Lp` class of a pointwise finite sum `fun x ↦ ∑ i ∈ s, f i x` of `Lᵖ` functions is the
sum of their `Lp` classes. -/
theorem toLp_finsetSum (hsum : MemLp (fun x ↦ ∑ i ∈ s, f i x) p μ) (hf : ∀ i, MemLp (f i) p μ) :
    hsum.toLp (fun x ↦ ∑ i ∈ s, f i x) = ∑ i ∈ s, (hf i).toLp (f i) := by
  convert (memLp_finsetSum' s fun i _ ↦ hf i).toLp_finsetSum' hf using 1
  exact toLp_congr _ _ (.of_forall fun x ↦ (Finset.sum_apply x s f).symm)

end MeasureTheory.MemLp

namespace ContinuousLinearMap

open MeasureTheory

variable {α E F 𝕜 𝕜' : Type*} {_ : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}
  [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜'] {σ : 𝕜 →+* 𝕜'} [RingHomIsometric σ]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜' F]

/-- The bundled composition `L.compLpL p μ` applied to `f` is the composition `L.compLp f`. -/
@[simp]
theorem compLpL_apply [Fact (1 ≤ p)] (L : E →SL[σ] F) (f : Lp E p μ) :
    L.compLpL p μ f = L.compLp f :=
  rfl

end ContinuousLinearMap

namespace LinearIsometryEquiv

open MeasureTheory

variable {α E F G 𝕜 : Type*} {_ : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- **Pointwise composition with a linear isometry equivalence, on `Lp`.** For
`R : E ≃ₗᵢ[𝕜] F`, the map `f ↦ R ∘ f` is a linear isometry equivalence
`Lp E p μ ≃ₗᵢ[𝕜] Lp F p μ`, with inverse `f ↦ R.symm ∘ f`. Following it or preceding it by
`MeasureTheory.Lp.compMeasurePreservingₗᵢEquiv` moves the points and rotates the values. -/
noncomputable def compLpₗᵢEquiv (R : E ≃ₗᵢ[𝕜] F) (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure α) :
    Lp E p μ ≃ₗᵢ[𝕜] Lp F p μ where
  toLinearEquiv := .ofLinearMap (R.toLinearIsometry.toContinuousLinearMap.compLpₗ p μ)
    (R.symm.toLinearIsometry.toContinuousLinearMap.compLpₗ p μ)
    (LinearMap.ext fun f ↦ Lp.ext <| by
      filter_upwards [R.toLinearIsometry.toContinuousLinearMap.coeFn_compLp
          (R.symm.toLinearIsometry.toContinuousLinearMap.compLp f),
        R.symm.toLinearIsometry.toContinuousLinearMap.coeFn_compLp f] with a h₁ h₂
      simp [h₁, h₂])
    (LinearMap.ext fun f ↦ Lp.ext <| by
      filter_upwards [R.symm.toLinearIsometry.toContinuousLinearMap.coeFn_compLp
          (R.toLinearIsometry.toContinuousLinearMap.compLp f),
        R.toLinearIsometry.toContinuousLinearMap.coeFn_compLp f] with a h₁ h₂
      simp [h₁, h₂])
  norm_map' f := by
    simp only [LinearEquiv.coe_ofLinearMap, ContinuousLinearMap.compLpₗ_apply, Lp.norm_def]
    refine congrArg ENNReal.toReal
      (eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) ?_)
    filter_upwards [R.toLinearIsometry.toContinuousLinearMap.coeFn_compLp f] with a ha
    simp [ha]

variable (R : E ≃ₗᵢ[𝕜] F)

/-- `LinearIsometryEquiv.compLpₗᵢEquiv` is Mathlib's composition
`ContinuousLinearMap.compLp` with the underlying continuous linear map. -/
theorem compLpₗᵢEquiv_apply (f : Lp E p μ) :
    R.compLpₗᵢEquiv p μ f = R.toLinearIsometry.toContinuousLinearMap.compLp f :=
  (rfl)

/-- `LinearIsometryEquiv.compLpₗᵢEquiv` is almost everywhere pointwise composition. -/
theorem coeFn_compLpₗᵢEquiv (f : Lp E p μ) : ⇑(R.compLpₗᵢEquiv p μ f) =ᵐ[μ] fun a ↦ R (f a) := by
  rw [compLpₗᵢEquiv_apply]
  exact ContinuousLinearMap.coeFn_compLp R.toLinearIsometry.toContinuousLinearMap f

/-- Composition with the identity is the identity of `Lp`. -/
@[simp]
theorem compLpₗᵢEquiv_refl :
    (LinearIsometryEquiv.refl 𝕜 E).compLpₗᵢEquiv p μ = .refl 𝕜 (Lp E p μ) := by
  refine LinearIsometryEquiv.ext fun f ↦ Lp.ext ?_
  filter_upwards [(LinearIsometryEquiv.refl 𝕜 E).coeFn_compLpₗᵢEquiv f] with a ha
  simp [ha]

/-- Composition with `R` and then with `R'` is composition with `R.trans R'`. -/
@[simp]
theorem compLpₗᵢEquiv_trans (R' : F ≃ₗᵢ[𝕜] G) :
    (R.trans R').compLpₗᵢEquiv p μ = (R.compLpₗᵢEquiv p μ).trans (R'.compLpₗᵢEquiv p μ) := by
  refine LinearIsometryEquiv.ext fun f ↦ Lp.ext ?_
  filter_upwards [(R.trans R').coeFn_compLpₗᵢEquiv f,
    R'.coeFn_compLpₗᵢEquiv (R.compLpₗᵢEquiv p μ f), R.coeFn_compLpₗᵢEquiv f] with a h₁ h₂ h₃
  rw [LinearIsometryEquiv.trans_apply, h₁, h₂, h₃, LinearIsometryEquiv.trans_apply]

/-- The inverse of composition with `R` is composition with `R.symm`. -/
@[simp]
theorem compLpₗᵢEquiv_symm : (R.compLpₗᵢEquiv p μ).symm = R.symm.compLpₗᵢEquiv p μ := by
  refine LinearIsometryEquiv.ext fun f ↦ (LinearIsometryEquiv.symm_apply_eq _).2 (Lp.ext ?_)
  filter_upwards [R.coeFn_compLpₗᵢEquiv (R.symm.compLpₗᵢEquiv p μ f),
    R.symm.coeFn_compLpₗᵢEquiv f] with a h₁ h₂
  rw [h₁, h₂, LinearIsometryEquiv.apply_symm_apply]

end LinearIsometryEquiv
