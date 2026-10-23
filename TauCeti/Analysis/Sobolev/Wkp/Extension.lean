/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Zero
public import TauCeti.Analysis.Sobolev.Wkp.Restriction
public import TauCeti.MeasureTheory.Function.Lp.ExtendByZero
import TauCeti.Analysis.Sobolev.W1p.Extension
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Zero extension of arbitrary-order Sobolev functions with zero boundary values

Extension by zero from an open set `Ω` to a larger open set `Ω'` is a linear isometry
`W^{k,p}_0(Ω) → W^{k,p}_0(Ω')` for every natural order and `1 ≤ p ≤ ∞`. Its value and
highest weak derivative are the zero extensions of the corresponding `Lᵖ` fields.
Restriction back to `Ω` recovers the original Sobolev function, and extensions compose.
No boundary regularity or boundedness is required.

This transport lets whole-space approximation and derivative estimates apply to
zero-boundary functions on a domain. The zero-boundary condition is essential: a general
domain Sobolev function can acquire singular distributional derivatives across the boundary.

The extension is characterized by continuity and its action on the dense family of test
functions: a test function on `Ω` becomes the same function on `Ω'`.

## References

L. C. Evans, *Partial Differential Equations*, §5.5; H. Brezis, *Functional Analysis,
Sobolev Spaces and Partial Differential Equations*, Lemma 9.5.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega Omega' Omega'' : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

private theorem extend_testFunction_iteratedGradient (hsub : Omega ≤ Omega') (k : ℕ)
    (phi : 𝓓(Omega, ℝ)) :
    extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet (SetLike.coe_subset_coe.mpr hsub)
        (iteratedGradientTestFunctionLp (mu := mu) p k phi) =
      iteratedGradientTestFunctionLp (mu := mu) (Omega := Omega') p k
        (TestFunction.monoCLM ℝ phi) := by
  have hs : tsupport (iteratedGradientTestFunction phi k) ⊆ tsupport (phi : E → ℝ) := by
    rw [iteratedGradientTestFunction_def]
    exact tsupport_iteratedGradientChain_subset (phi : E → ℝ) k
  refine extendByZeroLpₗᵢ_eq_of_ae_eq ℝ Omega.isOpen.measurableSet
    (SetLike.coe_subset_coe.mpr hsub)
    ((subset_tsupport _).trans (hs.trans phi.tsupport_subset))
    (iteratedGradientTestFunctionLp_apply_ae p k phi) ?_
  have heq : ((TestFunction.monoCLM ℝ phi : 𝓓(Omega', ℝ)) : E → ℝ) = phi := by
    simp [TestFunction.monoCLM_apply, hsub]
  simpa only [iteratedGradientTestFunction_def, heq] using
    iteratedGradientTestFunctionLp_apply_ae (mu := mu) p k
      (TestFunction.monoCLM ℝ phi : 𝓓(Omega', ℝ))

private theorem norm_testFunction_mono (hsub : Omega ≤ Omega') (k : ℕ)
    (phi : 𝓓(Omega, ℝ)) :
    ‖Wkp.ofTestFunctionₗ (mu := mu) (Omega := Omega') (p := p) k
        (TestFunction.monoCLM ℝ phi)‖ =
      ‖Wkp.ofTestFunctionₗ (mu := mu) (p := p) k phi‖ := by
  induction k using Nat.twoStepInduction with
  | zero =>
      rw [← Wkp.value_zero (Wkp.ofTestFunctionₗ (mu := mu) (Omega := Omega')
        (p := p) 0 (TestFunction.monoCLM ℝ phi)),
        ← Wkp.value_zero (Wkp.ofTestFunctionₗ (mu := mu) (p := p) 0 phi),
        Wkp.value_ofTestFunctionₗ, Wkp.value_ofTestFunctionₗ]
      rw [← toReal_enorm, ← toReal_enorm,
        enorm_testFunctionLp_eq_eLpNorm, enorm_testFunctionLp_eq_eLpNorm,
        TestFunction.monoCLM_apply]
      simp [hsub]
  | one =>
      -- Reuse the first-order zero-extension isometry for value-gradient jets.
      have h := (Sobolev1JetLp.extendByZeroₗᵢ (mu := mu) (p := p) hsub).norm_map
        (W1p.ofTestFunctionₗ mu Omega p phi : Sobolev1JetLp mu Omega p)
      rw [Sobolev1JetLp.extendByZeroₗᵢ_ofTestFunctionₗ] at h
      -- The order-one norm is the inherited norm of the first-order value-gradient jet.
      rw [Wkp.ofTestFunctionₗ_one, Wkp.ofTestFunctionₗ_one]
      convert h using 1 <;> rfl
  | more k _ ih =>
      have hd := (extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet
        (SetLike.coe_subset_coe.mpr hsub)).norm_map
          (iteratedGradientTestFunctionLp (mu := mu) p (k + 1) phi)
      rw [extend_testFunction_iteratedGradient hsub] at hd
      have hs : ‖Wkp.ofTestFunctionₗ (mu := mu) (Omega := Omega') (p := p) (k + 2)
          (TestFunction.monoCLM ℝ phi)‖ ^ 2 =
          ‖Wkp.ofTestFunctionₗ (mu := mu) (p := p) (k + 2) phi‖ ^ 2 := by
        rw [Wkp.norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ,
          Wkp.norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ]
        rw [Wkp.lowerOrder_ofTestFunctionₗ (k + 1),
          Wkp.lowerOrder_ofTestFunctionₗ (k + 1) phi,
          Wkp.iteratedGradient_ofTestFunctionₗ (k + 1),
          Wkp.iteratedGradient_ofTestFunctionₗ (k + 1) phi]
        rw [ih, hd]
      nlinarith [norm_nonneg (Wkp.ofTestFunctionₗ (mu := mu) (Omega := Omega')
        (p := p) (k + 2) (TestFunction.monoCLM ℝ phi)),
        norm_nonneg (Wkp.ofTestFunctionₗ (mu := mu) (p := p) (k + 2) phi)]

/-- Extension by zero to a larger open set, as a linear isometry of zero-boundary
Sobolev spaces. This preserves the full norm at every order, including at `p = ∞`. -/
def Wkp0.extendByZeroₗᵢ (hsub : Omega ≤ Omega') (k : ℕ) :
    Wkp0 mu Omega p k →ₗᵢ[ℝ] Wkp0 mu Omega' p k :=
  -- Extend the dense test-function inclusion using Mathlib's `LinearMap.extendOfIsometry`.
  ((Wkp0.ofTestFunctionₗ (mu := mu) (Omega := Omega') (p := p) k).comp
    (TestFunction.monoCLM ℝ).toLinearMap).extendOfIsometry
    (Wkp0.denseRange_ofTestFunctionₗ k) (fun phi => by
      simpa only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, ← Submodule.norm_coe,
        Wkp0.coe_ofTestFunctionₗ] using norm_testFunction_mono (mu := mu) (p := p) hsub k phi)

/-- A test function extends to the same test function on the larger domain. -/
@[simp]
theorem Wkp0.extendByZeroₗᵢ_ofTestFunctionₗ (hsub : Omega ≤ Omega') (k : ℕ)
    (phi : 𝓓(Omega, ℝ)) :
    Wkp0.extendByZeroₗᵢ hsub k (Wkp0.ofTestFunctionₗ (mu := mu) (p := p) k phi) =
      Wkp0.ofTestFunctionₗ (mu := mu) (Omega := Omega') (p := p) k
        (TestFunction.monoCLM ℝ phi) := by
  rw [Wkp0.extendByZeroₗᵢ, LinearMap.extendOfIsometry_eq]
  rfl

/-- The value of the extension is the zero extension of the original value. -/
@[simp]
theorem Wkp0.value_extendByZeroₗᵢ (hsub : Omega ≤ Omega') (k : ℕ)
    (u : Wkp0 mu Omega p k) :
    Wkp.value k (Wkp0.extendByZeroₗᵢ hsub k u : Wkp mu Omega' p k) =
      extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet (SetLike.coe_subset_coe.mpr hsub)
        (Wkp.value k (u : Wkp mu Omega p k)) := by
  refine (Wkp0.denseRange_ofTestFunctionₗ (mu := mu) (Omega := Omega) (p := p) k).induction_on
    u (isClosed_eq ?_ ?_) ?_
  · simpa only [Function.comp_def, Wkp.valueL_apply] using
      (Wkp.valueL (mu := mu) (Omega := Omega') (p := p) k).continuous.comp
      (continuous_subtype_val.comp (Wkp0.extendByZeroₗᵢ hsub k).continuous)
  · simpa only [Function.comp_def, Wkp.valueL_apply] using
      (extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet
        (SetLike.coe_subset_coe.mpr hsub)).continuous.comp
          ((Wkp.valueL (mu := mu) (Omega := Omega) (p := p) k).continuous.comp
            continuous_subtype_val)
  · intro phi
    have h := congrArg Sobolev1JetLp.value
      (Sobolev1JetLp.extendByZeroₗᵢ_ofTestFunctionₗ (mu := mu) (p := p) hsub phi)
    simpa only [Wkp0.extendByZeroₗᵢ_ofTestFunctionₗ, Wkp0.coe_ofTestFunctionₗ,
      Wkp.value_ofTestFunctionₗ, Sobolev1JetLp.value_extendByZeroₗᵢ,
      ← W1p.value_coe, W1p.value_ofTestFunctionₗ] using h.symm

/-- The highest recorded weak derivative extends by zero along with the value. -/
-- The dependent successor index prevents this rule from matching in `simp`.
theorem Wkp0.iteratedGradient_extendByZeroₗᵢ (hsub : Omega ≤ Omega') (k : ℕ)
    (u : Wkp0 mu Omega p (k + 1)) :
    Wkp.iteratedGradient k
        (Wkp0.extendByZeroₗᵢ hsub (k + 1) u : Wkp mu Omega' p (k + 1)) =
      extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet (SetLike.coe_subset_coe.mpr hsub)
        (Wkp.iteratedGradient k (u : Wkp mu Omega p (k + 1))) := by
  refine (Wkp0.denseRange_ofTestFunctionₗ (mu := mu) (Omega := Omega) (p := p)
    (k + 1)).induction_on u (isClosed_eq ?_ ?_) ?_
  · simp_rw [← Wkp.iteratedGradientL_apply]
    exact (Wkp.iteratedGradientL (mu := mu) (Omega := Omega') (p := p) k).continuous.comp
      (continuous_subtype_val.comp (Wkp0.extendByZeroₗᵢ hsub (k + 1)).continuous)
  · simp_rw [← Wkp.iteratedGradientL_apply]
    exact (extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet
        (SetLike.coe_subset_coe.mpr hsub)).continuous.comp
          ((Wkp.iteratedGradientL (mu := mu) (Omega := Omega) (p := p) k).continuous.comp
            continuous_subtype_val)
  · intro phi
    rw [Wkp0.extendByZeroₗᵢ_ofTestFunctionₗ]
    rw [Wkp0.coe_ofTestFunctionₗ, Wkp0.coe_ofTestFunctionₗ,
      Wkp.iteratedGradient_ofTestFunctionₗ k, Wkp.iteratedGradient_ofTestFunctionₗ k phi]
    exact (extend_testFunction_iteratedGradient hsub k phi).symm

/-- Zero extension commutes with forgetting the highest weak derivative. -/
-- The dependent successor index prevents this rule from matching in `simp`.
theorem Wkp0.lowerOrderL_extendByZeroₗᵢ (hsub : Omega ≤ Omega') (k : ℕ)
    (u : Wkp0 mu Omega p (k + 1)) :
    Wkp0.lowerOrderL k (Wkp0.extendByZeroₗᵢ hsub (k + 1) u) =
      Wkp0.extendByZeroₗᵢ hsub k (Wkp0.lowerOrderL k u) := by
  apply Subtype.ext
  apply Wkp.ext k
  rw [Wkp0.coe_lowerOrderL, ← Wkp.value_succ, Wkp0.value_extendByZeroₗᵢ,
    Wkp0.value_extendByZeroₗᵢ, Wkp0.coe_lowerOrderL, ← Wkp.value_succ]

/-- Extending along the identity inclusion does nothing. -/
@[simp]
theorem Wkp0.extendByZeroₗᵢ_self (k : ℕ) (u : Wkp0 mu Omega p k) :
    Wkp0.extendByZeroₗᵢ le_rfl k u = u := by
  apply Subtype.ext
  apply Wkp.ext k
  simp only [Wkp0.value_extendByZeroₗᵢ, extendByZeroLpₗᵢ_self]

/-- Zero extensions compose along inclusions of open sets. -/
@[simp]
theorem Wkp0.extendByZeroₗᵢ_extendByZeroₗᵢ (hsub : Omega ≤ Omega')
    (hsub' : Omega' ≤ Omega'') (k : ℕ) (u : Wkp0 mu Omega p k) :
    Wkp0.extendByZeroₗᵢ hsub' k (Wkp0.extendByZeroₗᵢ hsub k u) =
      Wkp0.extendByZeroₗᵢ (hsub.trans hsub') k u := by
  apply Subtype.ext
  apply Wkp.ext k
  simp only [Wkp0.value_extendByZeroₗᵢ, extendByZeroLpₗᵢ_extendByZeroLpₗᵢ]

/-- Restricting the zero extension to its original domain recovers the Sobolev function. -/
@[simp]
theorem Wkp0.restrictL_extendByZeroₗᵢ (hsub : Omega ≤ Omega') (k : ℕ)
    (u : Wkp0 mu Omega p k) :
    Wkp.restrictL hsub k (Wkp0.extendByZeroₗᵢ hsub k u : Wkp mu Omega' p k) = u := by
  apply Wkp.ext k
  apply Lp.ext
  exact (Wkp.value_restrictL_ae hsub k _).trans (by
    rw [Wkp0.value_extendByZeroₗᵢ]
    exact coeFn_extendByZeroLpₗᵢ_restrict ℝ _ _ _)

end TauCeti
