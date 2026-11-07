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

Without the zero-boundary condition, a function still extends by zero when it vanishes near the
part of `∂Ω` that the extension crosses: if `u ∈ W^{k,p}(Ω)` vanishes almost everywhere off a
closed set `K` with `V ∩ K ⊆ Ω`, then its extension by zero lies in `W^{k,p}(V)`
(`TauCeti.Wkp.exists_value_ae_eq_indicator_of_isClosed`), whose highest weak derivative is the
extension by zero of that of `u` (`TauCeti.Wkp.iteratedGradient_ae_eq_indicator_of_isClosed`).
Here `Ω` need not lie in `V`, and `K`
may meet `∂Ω` outside `V`. This is how a function on a domain, cut off near a boundary point,
becomes a function on the model half-space of a boundary chart.

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

/-! ### Extension by zero across an artificial boundary -/

/-- **Extension by zero across an artificial boundary.** Let `u ∈ W^{k,p}(Ω)` vanish almost
everywhere on `Ω` off a closed set `K`, and let `V` be open with `V ∩ K ⊆ Ω`. Then the extension of
`u` by zero, restricted to `V`, is the value of an element of `W^{k,p}(V)`. The set `Ω` need not lie
in `V`, and no boundary condition is imposed on the part of `∂Ω` outside `V`. -/
theorem Wkp.exists_value_ae_eq_indicator_of_isClosed {V : Opens E} {K : Set E} (hK : IsClosed K)
    (hKV : (V : Set E) ∩ K ⊆ Omega) :
    ∀ (k : ℕ) (u : Wkp mu Omega p k), (∀ᵐ x ∂mu.restrict Omega, x ∉ K → Wkp.value k u x = 0) →
      ∃ w : Wkp mu V p k,
        Wkp.value k w =ᵐ[mu.restrict V] (Omega : Set E).indicator (Wkp.value k u) := by
  have hΩ : MeasurableSet (Omega : Set E) := Omega.isOpen.measurableSet
  -- The extension by zero of an element of `Lᵖ(Ω)` lies in `Lᵖ(V)`.
  have hLp : ∀ g : Lp ℝ p (mu.restrict Omega),
      MemLp ((Omega : Set E).indicator g) p (mu.restrict V) := fun g =>
    ((memLp_indicator_iff_restrict hΩ.nullMeasurableSet).2 (Lp.memLp g)).restrict _
  intro k
  induction k with
  | zero => exact fun u _ => ⟨(hLp (Wkp.value 0 u)).toLp _, by
      rw [Wkp.value_zero]
      exact (hLp _).coeFn_toLp⟩
  | succ k ih =>
    intro u hu
    refine (Wkp.exists_value_eq_of_forall_hasWeakLineDerivOn (stdOrthonormalBasis ℝ E)
      ((hLp (Wkp.value (k + 1) u)).toLp _) k fun i => ?_).imp
        fun w (hw : Wkp.value (k + 1) w = _) => hw ▸
        (hLp (Wkp.value (k + 1) u)).coeFn_toLp
    -- A directional derivative `d` of `u` vanishes off `K`, so it extends by induction.
    obtain ⟨d, hd⟩ := Wkp.exists_hasWeakLineDerivOn_value k u (stdOrthonormalBasis ℝ E i)
    have hd0 : ∀ᵐ x ∂mu.restrict Omega, x ∉ K → Wkp.value k d x = 0 :=
      hd.ae_eq_zero_of_isOpen hK.isOpen_compl hu
    obtain ⟨w, hw⟩ := ih d hd0
    exact ⟨w, ((hd.indicator_of_isClosed hK hKV hu hd0).congr_ae
      (hLp (Wkp.value (k + 1) u)).coeFn_toLp.symm).congr_ae_deriv hw.symm⟩

/-- **Weak derivatives of an extension by zero.** In the situation of
`TauCeti.Wkp.exists_value_ae_eq_indicator_of_isClosed`, let `w ∈ W^{k+1,p}(V)` have value the
extension by zero of `u ∈ W^{k+1,p}(Ω)`. Then the highest weak derivative of `w` is the extension by
zero of the highest weak derivative of `u`, almost everywhere on `V`. -/
theorem Wkp.iteratedGradient_ae_eq_indicator_of_isClosed {V : Opens E} {K : Set E}
    (hK : IsClosed K) (hKV : (V : Set E) ∩ K ⊆ Omega) (k : ℕ) {u : Wkp mu Omega p (k + 1)}
    {w : Wkp mu V p (k + 1)} (hu : ∀ᵐ x ∂mu.restrict Omega, x ∉ K → Wkp.value (k + 1) u x = 0)
    (hw : Wkp.value (k + 1) w =ᵐ[mu.restrict V] (Omega : Set E).indicator (Wkp.value (k + 1) u)) :
    Wkp.iteratedGradient k w =ᵐ[mu.restrict V]
      (Omega : Set E).indicator (Wkp.iteratedGradient k u) := by
  set W : Opens E := V ⊓ Omega
  have hWm : MeasurableSet (W : Set E) := W.isOpen.measurableSet
  -- On `V ∩ Ω`, the restrictions of `w` and `u` have the same value, hence are equal.
  have hres : Wkp.restrictL (inf_le_left : W ≤ V) (k + 1) w =
      Wkp.restrictL (inf_le_right : W ≤ Omega) (k + 1) u := by
    refine Wkp.ext (k + 1) (Lp.ext ?_)
    filter_upwards [Wkp.value_restrictL_ae (inf_le_left : W ≤ V) (k + 1) w,
      Wkp.value_restrictL_ae (inf_le_right : W ≤ Omega) (k + 1) u,
      ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.mpr inf_le_left) hw,
      ae_restrict_mem hWm] with x h₁ h₂ h₃ hx
    rw [h₁, h₂, h₃, Set.indicator_of_mem (Opens.mem_inf.1 hx).2]
  have hW : Wkp.iteratedGradient k w =ᵐ[mu.restrict W] Wkp.iteratedGradient k u := by
    have h₁ := Wkp.iteratedGradient_restrictL_ae (inf_le_left : W ≤ V) k w
    rw [hres] at h₁
    exact h₁.symm.trans (Wkp.iteratedGradient_restrictL_ae (inf_le_right : W ≤ Omega) k u)
  -- Off `K`, the value of `w` vanishes, hence so does its highest weak derivative.
  have hw0 : ∀ᵐ x ∂mu.restrict V, x ∈ Kᶜ → Wkp.value (k + 1) w x = 0 := by
    filter_upwards [hw, ae_restrict_of_ae ((ae_restrict_iff' Omega.isOpen.measurableSet).1 hu)]
      with x h₁ h₂ hxK
    rw [h₁]
    by_cases hxΩ : x ∈ (Omega : Set E)
    · rw [Set.indicator_of_mem hxΩ, h₂ hxΩ hxK]
    · exact Set.indicator_of_notMem hxΩ _
  filter_upwards [ae_restrict_of_ae ((ae_restrict_iff' hWm).1 hW),
    Wkp.iteratedGradient_ae_eq_zero_of_value_ae_eq_zero_of_isOpen k w hK.isOpen_compl hw0,
    ae_restrict_mem V.isOpen.measurableSet] with x h₁ h₂ hxV
  by_cases hxΩ : x ∈ (Omega : Set E)
  · rw [Set.indicator_of_mem hxΩ, h₁ (Opens.mem_inf.2 ⟨hxV, hxΩ⟩)]
  · rw [Set.indicator_of_notMem hxΩ, h₂ fun hxK => hxΩ (hKV ⟨hxV, hxK⟩)]

end TauCeti
