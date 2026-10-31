/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
public import Mathlib.MeasureTheory.Group.Integral
public import TauCeti.MeasureTheory.Function.Lp.BoundedContinuous

/-!
# Left translation on `Lᵖ` of a group

Let `μ` be a left-invariant measure on a group `G`. Left translation of functions,

```text
(L_g f)(x) = f (g⁻¹ * x),        L_g L_h = L_(g * h),
```

preserves `Lᵖ` classes and norms, so it gives a group homomorphism
`MeasureTheory.Lp.leftTranslation μ p 𝕜 : G →* (Lp E p μ ≃ₗᵢ[𝕜] Lp E p μ)`. It is the
action of `DomMulAct.mk g⁻¹` from Mathlib's `DomMulAct` action on `Lp`, reindexed so that it is
a left action of `G` itself.

For real-valued functions, left translation is an order automorphism, preserves integrals and
fixes the constant class one of `L∞`. The class of the left translate of a bounded continuous
function is the left translate of its class, so `BoundedContinuousFunction.toLpTop` is
equivariant. These are the translation-invariance properties needed to compare invariant means
on bounded uniformly continuous functions with invariant means on `L∞` of a Haar measure.

## Main definitions

* `MeasureTheory.Lp.leftTranslation μ p 𝕜`: left translation `g ↦ L_g` on `Lp E p μ`, as a group
  homomorphism to linear isometry equivalences.

## Main results

* `MeasureTheory.Lp.coeFn_leftTranslation`: `L_g f` is almost everywhere `x ↦ f (g⁻¹ * x)`.
* `MeasureTheory.Lp.leftTranslation_le_leftTranslation_iff`: left translation is an order
  automorphism of real `Lᵖ`.
* `MeasureTheory.Lp.leftTranslation_linftyOne`: it fixes the constant class one in `L∞`.
* `MeasureTheory.Lp.integral_leftTranslation`: left translation preserves integrals.
* `MeasureTheory.Lp.leftTranslation_toLpTop`: the class in `L∞` of a bounded continuous
  function commutes with left translation.
-/

public section

noncomputable section

open Filter
open scoped ENNReal BoundedContinuousFunction

namespace MeasureTheory.Lp

variable {G E : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
  [μ.IsMulLeftInvariant] [NormedAddCommGroup E] (p : ℝ≥0∞) [Fact (1 ≤ p)]
  (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- Left translation `g ↦ L_g` on `Lp E p μ` for a left-invariant measure `μ`, where
`(L_g f)(x) = f (g⁻¹ * x)`, as a group homomorphism to linear isometry equivalences. -/
def leftTranslation : G →* (Lp E p μ ≃ₗᵢ[𝕜] Lp E p μ) where
  toFun g :=
    { toLinearEquiv := DistribMulAction.toLinearEquiv 𝕜 (Lp E p μ) (DomMulAct.mk g⁻¹)
      norm_map' := DomMulAct.norm_smul_Lp _ }
  map_one' := by
    ext f : 1
    simp [DomMulAct.mk_one]
  map_mul' g h := by
    ext f : 1
    simp only [mul_inv_rev, DomMulAct.mk_mul, DomMulAct.mk_inv, LinearIsometryEquiv.coe_mk,
      DistribMulAction.toLinearEquiv_apply, LinearIsometryEquiv.coe_mul, Function.comp_apply,
      smul_smul]

variable {μ p 𝕜}

/-- Left translation by `g` is the `DomMulAct` action of `g⁻¹`. -/
theorem leftTranslation_apply (g : G) (f : Lp E p μ) :
    leftTranslation μ p 𝕜 g f = DomMulAct.mk g⁻¹ • f :=
  (rfl)

/-- The left translate `L_g f` is almost everywhere the function `x ↦ f (g⁻¹ * x)`. -/
theorem coeFn_leftTranslation (g : G) (f : Lp E p μ) :
    leftTranslation μ p 𝕜 g f =ᵐ[μ] fun x => f (g⁻¹ * x) := by
  rw [leftTranslation_apply]
  exact DomMulAct.smul_Lp_ae_eq _ f

/-- The inverse of left translation by `g` is left translation by `g⁻¹`. -/
@[simp]
theorem leftTranslation_symm (g : G) :
    (leftTranslation μ p 𝕜 g).symm = leftTranslation μ p 𝕜 (E := E) g⁻¹ := by
  rw [map_inv, LinearIsometryEquiv.inv_def]

/-- Left translation is monotone on real `Lᵖ`. -/
theorem leftTranslation_mono (g : G) {f f' : Lp ℝ p μ} (h : f ≤ f') :
    leftTranslation μ p ℝ g f ≤ leftTranslation μ p ℝ g f' := by
  rw [← coeFn_le] at h ⊢
  filter_upwards [coeFn_leftTranslation (𝕜 := ℝ) g f, coeFn_leftTranslation (𝕜 := ℝ) g f',
    (measurePreserving_mul_left μ g⁻¹).quasiMeasurePreserving.ae h] with x hx hx' hle
  exact hx ▸ hx' ▸ hle

/-- Left translation is an order automorphism of real `Lᵖ`. -/
@[simp]
theorem leftTranslation_le_leftTranslation_iff {g : G} {f f' : Lp ℝ p μ} :
    leftTranslation μ p ℝ g f ≤ leftTranslation μ p ℝ g f' ↔ f ≤ f' := by
  refine ⟨fun h => ?_, leftTranslation_mono g⟩
  simpa [← leftTranslation_symm] using leftTranslation_mono (μ := μ) g⁻¹ h

/-- Left translation fixes the constant class one of `L∞`. -/
@[simp]
theorem leftTranslation_linftyOne (g : G) :
    leftTranslation μ ∞ ℝ g TauCeti.linftyOne = TauCeti.linftyOne := by
  refine ext ?_
  filter_upwards [coeFn_leftTranslation (𝕜 := ℝ) g TauCeti.linftyOne, TauCeti.coeFn_linftyOne,
    (measurePreserving_mul_left μ g⁻¹).quasiMeasurePreserving.ae TauCeti.coeFn_linftyOne]
    with x hx h1 h1'
  rw [hx, h1, h1']

/-- Left translation preserves the integral of an `Lᵖ` class, since `μ` is left invariant. -/
@[simp]
theorem integral_leftTranslation [NormedSpace ℝ E] (g : G) (f : Lp E p μ) :
    ∫ x, leftTranslation μ p 𝕜 g f x ∂μ = ∫ x, f x ∂μ := by
  rw [integral_congr_ae (coeFn_leftTranslation g f), integral_mul_left_eq_self]

/-- The class in `L∞` of the left translate `x ↦ f (g⁻¹ * x)` of a bounded continuous function
is the left translate of its class. -/
theorem leftTranslation_toLpTop [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G]
    [SecondCountableTopologyEither G E] (g : G) (f : G →ᵇ E) :
    leftTranslation μ ∞ 𝕜 g (BoundedContinuousFunction.toLpTop μ 𝕜 f) =
      BoundedContinuousFunction.toLpTop μ 𝕜 (f.compContinuous (ContinuousMap.mulLeft g⁻¹)) := by
  refine ext ?_
  filter_upwards [coeFn_leftTranslation (𝕜 := 𝕜) g (BoundedContinuousFunction.toLpTop μ 𝕜 f),
    BoundedContinuousFunction.coeFn_toLpTop μ (𝕜 := 𝕜)
      (f.compContinuous (ContinuousMap.mulLeft g⁻¹)),
    (measurePreserving_mul_left μ g⁻¹).quasiMeasurePreserving.ae
      (BoundedContinuousFunction.coeFn_toLpTop μ (𝕜 := 𝕜) f)] with x hx hc hf
  simp [hx, hc, hf]

end MeasureTheory.Lp
