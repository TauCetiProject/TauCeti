/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Zero
public import TauCeti.Analysis.Sobolev.Wkp.Restriction
public import TauCeti.MeasureTheory.Function.Lp.ExtendByZero
import TauCeti.Analysis.Sobolev.CompactSupport
import TauCeti.Analysis.Sobolev.W1p.Extension
import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
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

Without zero boundary values, extension by zero still works across the part of `∂Ω` that a
function avoids. If `u ∈ W^{k,p}(Ω)` vanishes outside a closed set `K` with `Ω' ∩ K ⊆ Ω`, its
extension by zero lies in `W^{k,p}(Ω')`
(`TauCeti.Wkp.exists_value_eq_extendByZeroLpₗᵢ_of_isClosed`), with highest weak derivative the
extension of that of `u` (`TauCeti.Wkp.iteratedGradient_eq_extendByZeroLpₗᵢ_of_isClosed`, and
pointwise `TauCeti.Wkp.iteratedGradient_ae_eq_indicator_of_isClosed`). Here
`K` may meet `∂Ω` outside `Ω'`. This is how a function cut off near a flat part of `∂Ω` becomes a
function on a half-space, with no condition on the flat part.

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

/-- Extension by zero from `Ω` to a larger open set `Ω'` preserves the `W^{k,p}` norm of a test
function. -/
theorem Wkp.norm_ofTestFunctionₗ_monoCLM (hsub : Omega ≤ Omega') (k : ℕ)
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
        Wkp0.coe_ofTestFunctionₗ] using
          Wkp.norm_ofTestFunctionₗ_monoCLM (mu := mu) (p := p) hsub k phi)

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

section ClosedSupport

variable {K : Set E}

/-- **Extension by zero across a closed support.** Let `Ω ≤ Ω'` be open and let `K` be closed
with `Ω' ∩ K ⊆ Ω`. If `u ∈ W^{k,p}(Ω)` vanishes almost everywhere on `Ω` outside `K`, then its
extension by zero lies in `W^{k,p}(Ω')`. Unlike `TauCeti.Wkp0.extendByZeroₗᵢ`, no zero boundary
values are assumed: `K` may meet `∂Ω`, provided it does so outside `Ω'`. -/
theorem Wkp.exists_value_eq_extendByZeroLpₗᵢ_of_isClosed (hsub : Omega ≤ Omega')
    (hK : IsClosed K) (hKΩ : (Omega' : Set E) ∩ K ⊆ Omega) :
    ∀ (k : ℕ) (u : Wkp mu Omega p k),
      (∀ᵐ x ∂mu.restrict Omega, x ∉ K → Wkp.value k u x = 0) →
      ∃ w : Wkp mu Omega' p k, Wkp.value k w =
        extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet (SetLike.coe_subset_coe.mpr hsub)
          (Wkp.value k u)
  | 0, u, _ => ⟨extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet
      (SetLike.coe_subset_coe.mpr hsub) (Wkp.value 0 u), Wkp.value_zero _⟩
  | k + 1, u, hu => by
    -- In every direction, the extension of `∂ᵥu ∈ W^{k,p}(Ω)` is a weak derivative of the
    -- extension of `u`, and lies in `W^{k,p}(Ω')` by induction.
    have key : ∀ v : E, ∃ z : Wkp mu Omega' p k, HasWeakLineDerivOn mu Omega'
        (extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet (SetLike.coe_subset_coe.mpr hsub)
          (Wkp.value (k + 1) u) : E → ℝ) (Wkp.value k z) v := by
      intro v
      obtain ⟨d, hd⟩ := Wkp.exists_hasWeakLineDerivOn_value k u v
      have hd0 := hd.ae_eq_zero_of_isOpen hK.isOpen_compl hu
      obtain ⟨z, hz⟩ := Wkp.exists_value_eq_extendByZeroLpₗᵢ_of_isClosed hsub hK hKΩ k d hd0
      refine ⟨z, ((hd.indicator_of_isClosed hK hKΩ hu hd0).congr_ae ?_).congr_ae_deriv ?_⟩
      · exact (coeFn_extendByZeroLpₗᵢ ℝ _ _ _).symm
      · rw [hz]
        exact (coeFn_extendByZeroLpₗᵢ ℝ _ _ _).symm
    choose z hz using key
    obtain ⟨w, hw⟩ := Wkp.exists_value_ae_eq_of_forall_hasWeakLineDerivOn k (Lp.memLp _) z hz
    exact ⟨w, Lp.ext hw⟩

/-- **The weak derivatives of an extension across a closed support.** In the situation of
`TauCeti.Wkp.exists_value_eq_extendByZeroLpₗᵢ_of_isClosed`, the highest weak derivative of the
extension of `u` is the extension of the highest weak derivative of `u`. -/
theorem Wkp.iteratedGradient_eq_extendByZeroLpₗᵢ_of_isClosed (hsub : Omega ≤ Omega')
    (hK : IsClosed K) (hKΩ : (Omega' : Set E) ∩ K ⊆ Omega) (k : ℕ)
    {u : Wkp mu Omega p (k + 1)} {w : Wkp mu Omega' p (k + 1)}
    (hu : ∀ᵐ x ∂mu.restrict Omega, x ∉ K → Wkp.value (k + 1) u x = 0)
    (hw : Wkp.value (k + 1) w =
      extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet (SetLike.coe_subset_coe.mpr hsub)
        (Wkp.value (k + 1) u)) :
    Wkp.iteratedGradient k w =
      extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet (SetLike.coe_subset_coe.mpr hsub)
        (Wkp.iteratedGradient k u) := by
  have hΩ : MeasurableSet (Omega : Set E) := Omega.isOpen.measurableSet
  -- On `Ω`, `w` restricts to `u`, so the two highest derivatives agree there.
  have hres : Wkp.restrictL hsub (k + 1) w = u := by
    apply Wkp.ext (k + 1)
    apply Lp.ext
    refine (Wkp.value_restrictL_ae hsub (k + 1) w).trans ?_
    rw [hw]
    exact coeFn_extendByZeroLpₗᵢ_restrict ℝ _ _ _
  have hΩeq := Wkp.iteratedGradient_restrictL_ae hsub k w
  rw [hres] at hΩeq
  -- Off `K`, `w` vanishes, and hence so does its highest derivative.
  have hw0 : ∀ᵐ x ∂mu.restrict Omega', x ∈ Kᶜ → Wkp.value (k + 1) w x = 0 := by
    rw [hw]
    filter_upwards [coeFn_extendByZeroLpₗᵢ ℝ hΩ (SetLike.coe_subset_coe.mpr hsub)
      (Wkp.value (k + 1) u), ae_restrict_of_ae ((ae_restrict_iff' hΩ).1 hu)] with x he hx hxK
    rw [he]
    by_cases hxΩ : x ∈ (Omega : Set E)
    · rw [Set.indicator_of_mem hxΩ, hx hxΩ hxK]
    · rw [Set.indicator_of_notMem hxΩ]
  have hK0 := Wkp.iteratedGradient_ae_eq_zero_of_value_ae_eq_zero_of_isOpen k w hK.isOpen_compl hw0
  apply Lp.ext
  filter_upwards [coeFn_extendByZeroLpₗᵢ ℝ hΩ (SetLike.coe_subset_coe.mpr hsub)
    (Wkp.iteratedGradient k u), ae_restrict_of_ae ((ae_restrict_iff' hΩ).1 hΩeq), hK0,
    ae_restrict_mem Omega'.isOpen.measurableSet] with x he hx hx0 hxΩ'
  rw [he]
  by_cases hxΩ : x ∈ (Omega : Set E)
  · rw [Set.indicator_of_mem hxΩ, hx hxΩ]
  · rw [Set.indicator_of_notMem hxΩ, hx0 fun hxK => hxΩ (hKΩ ⟨hxΩ', hxK⟩)]

/-- The pointwise form of `TauCeti.Wkp.iteratedGradient_eq_extendByZeroLpₗᵢ_of_isClosed`: almost
everywhere on `Ω'`, the highest weak derivative of the extension is that of `u` on `Ω` and `0`
off `Ω`. -/
theorem Wkp.iteratedGradient_ae_eq_indicator_of_isClosed (hsub : Omega ≤ Omega')
    (hK : IsClosed K) (hKΩ : (Omega' : Set E) ∩ K ⊆ Omega) (k : ℕ)
    {u : Wkp mu Omega p (k + 1)} {w : Wkp mu Omega' p (k + 1)}
    (hu : ∀ᵐ x ∂mu.restrict Omega, x ∉ K → Wkp.value (k + 1) u x = 0)
    (hw : Wkp.value (k + 1) w =
      extendByZeroLpₗᵢ ℝ mu Omega.isOpen.measurableSet (SetLike.coe_subset_coe.mpr hsub)
        (Wkp.value (k + 1) u)) :
    (Wkp.iteratedGradient k w : E → IteratedGradient E k) =ᵐ[mu.restrict Omega']
      (Omega : Set E).indicator (Wkp.iteratedGradient k u) := by
  rw [Wkp.iteratedGradient_eq_extendByZeroLpₗᵢ_of_isClosed hsub hK hKΩ k hu hw]
  exact coeFn_extendByZeroLpₗᵢ ℝ _ _ _

end ClosedSupport

end TauCeti
