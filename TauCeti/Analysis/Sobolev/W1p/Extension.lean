/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Zero
public import TauCeti.Analysis.Sobolev.W1p.Restriction
public import TauCeti.MeasureTheory.Function.Lp.ExtendByZero
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import TauCeti.Analysis.Distribution.TestFunction.Basic

/-!
# Extending a `W^{1,p}_0` function by zero

A function in `W^{1,p}(Ω)` has no reason to stay Sobolev when it is extended by zero across `∂Ω`:
without some condition forcing it to vanish towards the boundary, the extension can fail to be
weakly differentiable on the larger set at all.  For `W^{1,p}_0(Ω)`, the closure of `C_c^∞(Ω)`,
that obstruction disappears, and this file proves it: the zero-extension of a `W^{1,p}_0(Ω)`
function to any larger open set `Ω'` lies in `W^{1,p}_0(Ω')`, and its weak gradient is the
zero-extension of the original weak gradient.

This is the half of the Sobolev extension theorem that needs no boundary regularity.  Taking
`Ω' = ⊤` gives an extension operator `W^{1,p}_0(Ω) → W^{1,p}(ℝⁿ)`, which is what lets whole-space
statements (Gagliardo--Nirenberg--Sobolev, translation estimates, and through them
Rellich--Kondrachov) be applied to functions given on a domain.  The extension operator for
`W^{1,p}(Ω)` itself is a genuinely harder theorem needing Lipschitz `∂Ω`, and is not proved here.

## The argument

Everything rests on `TauCeti.w1p0Submodule_subset_of_isClosed`: the zero-extension map is
continuous, and the property "the extension is a test-function limit on `Ω'`" is closed, so it is
enough to check it on test functions.  For a test function it is immediate, because a test
function on `Ω` *is* a test function on `Ω'` — `TestFunction.monoCLM` — and extending it by zero
does not change it at all: it already vanished off `Ω`, as did its gradient.

The zero-extension itself is `TauCeti.extendByZeroLpₗᵢ`, applied once to the value component,
once to the gradient component, and once to the value-gradient jet that carries both.  It is an
isometry of `Lᵖ` spaces, so the extension operator is an isometry of Sobolev spaces:
`TauCeti.W1p0.norm_extendByZeroL`.

## Main declarations

* `TauCeti.Sobolev1JetLp.extendByZeroₗᵢ`: extension by zero of an `Lᵖ` value-gradient jet.
* `TauCeti.Sobolev1JetLp.extendByZeroₗᵢ_mem_w1pSubmodule`: the zero-extension of a `W^{1,p}_0(Ω)`
  function is a Sobolev function on `Ω'`.
* `TauCeti.W1p0.extendByZeroL`: the extension operator `W^{1,p}_0(Ω) →L[ℝ] W^{1,p}_0(Ω')`, with
  `TauCeti.W1p0.norm_extendByZeroL` and its value and gradient components; it is functorial in
  `Ω` by `TauCeti.W1p0.extendByZeroL_self` and
  `TauCeti.W1p0.extendByZeroL_extendByZeroL`.
* `TauCeti.W1p0.value_extendByZeroL_ae_eq_zero_compl`: the whole-space extension vanishes almost
  everywhere off `Ω`.
* `TauCeti.W1p0.norm_value_extendByZeroL`, `TauCeti.W1p0.norm_gradient_extendByZeroL`: the
  extension preserves the norms of both components.
* `TauCeti.W1p0.restrictL_extendByZeroL`: restricting the extension back to `Ω` recovers `u`.
* `TauCeti.W1p0.restrictL_extendByZeroL_of_le`: restricting it to an open subset of `Ω` gives the
  restriction of `u`.
* `TauCeti.W1p0.value_restrictL_extendByZeroL_ae`,
  `TauCeti.W1p0.gradient_restrictL_extendByZeroL_ae`: restricting the extension to `Ω'` to another
  open set `V ⊆ Ω'` gives `1_Ω u` and `1_Ω ∇u` on `V`.
* `TauCeti.W1p0.setIntegral_gradient_restrictL_extendByZeroL`: integrating a density, vanishing at
  `0`, of the gradient of that restriction over `V` is integrating it over `V ∩ Ω`.
* `TauCeti.W1p0.value_extendByZeroL_ae`, `TauCeti.W1p0.gradient_extendByZeroL_ae`: the two
  components of the extension are almost everywhere the indicators of those of `u`.
* `TauCeti.W1p0.value_extendByZeroL_top_ae`, `TauCeti.W1p0.gradient_extendByZeroL_top_ae`: the
  same identities for the whole-space extension, almost everywhere for `mu` itself.
* `TauCeti.W1p0.dense_iUnion_range_extendByZeroL`: for a directed family of open sets covering
  `Ω`, the zero extensions of their `W^{1,p}_0` functions are dense in `W^{1,p}_0(Ω)`.
* `TauCeti.W1p0.hasWeakFDerivOn_indicator`: the analytic content, that the
  zero-extension of `u` is weakly differentiable on `Ω'` with the zero-extension of `∇u` as its
  weak gradient.
* `TauCeti.W1p0.setIntegral_inner_gradient_eq_zero`: on a bounded `Ω`, the weak gradient of
  `u ∈ W^{1,p}_0(Ω)` has integral zero.
* `TauCeti.W1p0.not_exists_value_ae_eq_const_of_inner_gradient_eq_one`: on a bounded nonempty
  `Ω`, a function with the boundary values of `g`, where `⟪∇g, w⟫ = 1`, is not constant.

## References

L. C. Evans, *Partial Differential Equations*, Section 5.5, and H. Brezis, *Functional Analysis,
Sobolev Spaces and Partial Differential Equations*, Lemma 9.5.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace

open scoped Distributions ENNReal Gradient InnerProductSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega Omega' Omega'' : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-! ### Extension by zero of `Lᵖ` jets -/

omit [mu.IsAddHaarMeasure] in
/-- **Extension by zero of an `Lᵖ` value-gradient jet** from `Ω` to a larger open set `Ω'`: both
components are declared zero on `Ω' \ Ω`.  It is an isometry, since the added region contributes
nothing to the `Lᵖ` norm of the jet: both of its components vanish there. -/
def Sobolev1JetLp.extendByZeroₗᵢ (hsub : Omega ≤ Omega') :
    Sobolev1JetLp mu Omega p →ₗᵢ[ℝ] Sobolev1JetLp mu Omega' p :=
  extendByZeroLpₗᵢ ℝ mu Omega.isOpen.nullMeasurableSet (SetLike.coe_subset_coe.mpr hsub)

omit [FiniteDimensional ℝ E] [mu.IsAddHaarMeasure] in
/-- The extension of a jet is the indicator of the original jet. -/
theorem Sobolev1JetLp.coeFn_extendByZeroₗᵢ (hsub : Omega ≤ Omega')
    (J : Sobolev1JetLp mu Omega p) :
    (Sobolev1JetLp.extendByZeroₗᵢ hsub J : E → Sobolev1Jet E) =ᵐ[mu.restrict Omega']
      (Omega : Set E).indicator (J : E → Sobolev1Jet E) :=
  coeFn_extendByZeroLpₗᵢ _ _ _ _

omit [FiniteDimensional ℝ E] [mu.IsAddHaarMeasure] in
/-- The value component of an extended jet is the extension of the value component: taking a
component is a pointwise postcomposition, and `TauCeti.coeFn_extendByZeroLpₗᵢ_comp` says that
those commute with extension by zero. -/
@[simp]
theorem Sobolev1JetLp.value_extendByZeroₗᵢ (hsub : Omega ≤ Omega')
    (J : Sobolev1JetLp mu Omega p) :
    Sobolev1JetLp.value (Sobolev1JetLp.extendByZeroₗᵢ hsub J) =
      extendByZeroLpₗᵢ ℝ mu Omega.isOpen.nullMeasurableSet (SetLike.coe_subset_coe.mpr hsub)
        (Sobolev1JetLp.value J) :=
  (Lp.ext ((coeFn_extendByZeroLpₗᵢ_comp ℝ Omega.isOpen.nullMeasurableSet
    (SetLike.coe_subset_coe.mpr hsub) WithLp.fst rfl (Sobolev1JetLp.value_apply_ae J)).trans
      (Filter.EventuallyEq.symm (Sobolev1JetLp.value_apply_ae _)))).symm

omit [FiniteDimensional ℝ E] [mu.IsAddHaarMeasure] in
/-- The gradient component of an extended jet is the extension of the gradient component; as for
`TauCeti.Sobolev1JetLp.value_extendByZeroₗᵢ`, this is postcomposition commuting with extension. -/
@[simp]
theorem Sobolev1JetLp.gradient_extendByZeroₗᵢ (hsub : Omega ≤ Omega')
    (J : Sobolev1JetLp mu Omega p) :
    Sobolev1JetLp.gradient (Sobolev1JetLp.extendByZeroₗᵢ hsub J) =
      extendByZeroLpₗᵢ ℝ mu Omega.isOpen.nullMeasurableSet (SetLike.coe_subset_coe.mpr hsub)
        (Sobolev1JetLp.gradient J) :=
  (Lp.ext ((coeFn_extendByZeroLpₗᵢ_comp ℝ Omega.isOpen.nullMeasurableSet
    (SetLike.coe_subset_coe.mpr hsub) WithLp.snd rfl (Sobolev1JetLp.gradient_apply_ae J)).trans
      (Filter.EventuallyEq.symm (Sobolev1JetLp.gradient_apply_ae _)))).symm

/-! ### Test functions extend to test functions -/

omit [FiniteDimensional ℝ E] in
/-- Extending a test function's `Lᵖ` class by zero gives the class of the same test function on
the larger open set: it already vanished outside `Ω`. -/
private theorem extendByZeroLpₗᵢ_testFunctionLp (hsub : Omega ≤ Omega') (phi : 𝓓(Omega, ℝ)) :
    extendByZeroLpₗᵢ ℝ mu Omega.isOpen.nullMeasurableSet (SetLike.coe_subset_coe.mpr hsub)
        (testFunctionLp p phi) =
      testFunctionLp (mu := mu) (Omega := Omega') p (TestFunction.monoCLM ℝ phi) :=
  extendByZeroLpₗᵢ_eq_of_ae_eq ℝ Omega.isOpen.nullMeasurableSet (SetLike.coe_subset_coe.mpr hsub)
    ((subset_tsupport _).trans phi.tsupport_subset) (testFunctionLp_apply_ae (mu := mu) p phi) <| by
      filter_upwards [testFunctionLp_apply_ae (mu := mu) (Omega := Omega') p
        (TestFunction.monoCLM ℝ phi)] with x hx
      rw [hx, TestFunction.coe_monoCLM_of_le le_rfl hsub phi]

/-- Extending a test function's gradient by zero gives the gradient of the same test function on
the larger open set. -/
private theorem extendByZeroLpₗᵢ_gradientTestFunctionLp (hsub : Omega ≤ Omega')
    (phi : 𝓓(Omega, ℝ)) :
    extendByZeroLpₗᵢ ℝ mu Omega.isOpen.nullMeasurableSet (SetLike.coe_subset_coe.mpr hsub)
        (gradientTestFunctionLp p phi) =
      gradientTestFunctionLp (mu := mu) (Omega := Omega') p (TestFunction.monoCLM ℝ phi) :=
  extendByZeroLpₗᵢ_eq_of_ae_eq ℝ Omega.isOpen.nullMeasurableSet (SetLike.coe_subset_coe.mpr hsub)
    (support_gradient_testFunction_subset phi)
    (gradientTestFunctionLp_apply_ae (mu := mu) p phi) <| by
      filter_upwards [gradientTestFunctionLp_apply_ae (mu := mu) (Omega := Omega') p
        (TestFunction.monoCLM ℝ phi)] with x hx
      rw [hx, TestFunction.coe_monoCLM_of_le le_rfl hsub phi]

/-- The zero-extension of a test-function jet is the jet of the same test function on the larger
open set. -/
@[simp]
theorem Sobolev1JetLp.extendByZeroₗᵢ_ofTestFunctionₗ (hsub : Omega ≤ Omega')
    (phi : 𝓓(Omega, ℝ)) :
    Sobolev1JetLp.extendByZeroₗᵢ hsub
        (W1p.ofTestFunctionₗ mu Omega p phi : Sobolev1JetLp mu Omega p) =
      (W1p.ofTestFunctionₗ mu Omega' p (TestFunction.monoCLM ℝ phi) :
        Sobolev1JetLp mu Omega' p) := by
  refine Sobolev1JetLp.ext ?_ ?_
  · rw [Sobolev1JetLp.value_extendByZeroₗᵢ, ← W1p.value_coe, ← W1p.value_coe,
      W1p.value_ofTestFunctionₗ, W1p.value_ofTestFunctionₗ]
    exact extendByZeroLpₗᵢ_testFunctionLp hsub phi
  · rw [Sobolev1JetLp.gradient_extendByZeroₗᵢ, ← W1p.gradient_coe, ← W1p.gradient_coe,
      W1p.gradient_ofTestFunctionₗ, W1p.gradient_ofTestFunctionₗ]
    exact extendByZeroLpₗᵢ_gradientTestFunctionLp hsub phi

/-! ### The extension theorem -/

/-- The zero-extension of a `W^{1,p}_0(Ω)` function belongs to the image of
`W^{1,p}_0(Ω')` in the ambient jet space. -/
private theorem extendByZero_mem_image (hsub : Omega ≤ Omega') {u : W1p mu Omega p}
    (hu : u ∈ w1p0Submodule mu Omega p) :
    Sobolev1JetLp.extendByZeroₗᵢ hsub (u : Sobolev1JetLp mu Omega p) ∈
      Subtype.val '' (w1p0Submodule mu Omega' p : Set (W1p mu Omega' p)) := by
  have hclosed : IsClosed
      (Subtype.val '' (w1p0Submodule mu Omega' p : Set (W1p mu Omega' p))) :=
    ((w1pSubmodule mu Omega' p).isClosed.isClosedEmbedding_subtypeVal).isClosedMap _
      (w1p0Submodule mu Omega' p).isClosed
  have hcont : Continuous fun v : W1p mu Omega p =>
      Sobolev1JetLp.extendByZeroₗᵢ (mu := mu) (p := p) hsub (v : Sobolev1JetLp mu Omega p) :=
    (Sobolev1JetLp.extendByZeroₗᵢ hsub).continuous.comp continuous_subtypeVal
  refine w1p0Submodule_subset_of_isClosed (hclosed.preimage hcont) (fun phi => ?_) hu
  exact ⟨W1p.ofTestFunctionₗ mu Omega' p (TestFunction.monoCLM ℝ phi),
    W1p.ofTestFunctionₗ_mem_w1p0Submodule _,
    (Sobolev1JetLp.extendByZeroₗᵢ_ofTestFunctionₗ hsub phi).symm⟩

/-- Transporting `TauCeti.extendByZero_mem_image` to any Sobolev function on `Ω'` whose ambient
jet is the zero-extension. -/
private theorem mem_w1p0Submodule_of_coe_eq (hsub : Omega ≤ Omega') {u : W1p mu Omega p}
    (hu : u ∈ w1p0Submodule mu Omega p) {v : W1p mu Omega' p}
    (hv : (v : Sobolev1JetLp mu Omega' p) =
      Sobolev1JetLp.extendByZeroₗᵢ hsub (u : Sobolev1JetLp mu Omega p)) :
    v ∈ w1p0Submodule mu Omega' p := by
  obtain ⟨w, hw, hwval⟩ := extendByZero_mem_image hsub hu
  exact Subtype.ext (hwval.trans hv.symm) ▸ hw

/-- **The zero-extension of a `W^{1,p}_0(Ω)` function is a Sobolev function on `Ω'`.**  No
regularity of `∂Ω` is needed, and no boundedness of either open set; the boundary condition
carried by membership in `W^{1,p}_0(Ω)` is what makes the extension weakly differentiable. -/
theorem Sobolev1JetLp.extendByZeroₗᵢ_mem_w1pSubmodule (hsub : Omega ≤ Omega')
    {u : W1p mu Omega p} (hu : u ∈ w1p0Submodule mu Omega p) :
    Sobolev1JetLp.extendByZeroₗᵢ hsub (u : Sobolev1JetLp mu Omega p) ∈
      w1pSubmodule mu Omega' p := by
  obtain ⟨v, -, hv⟩ := extendByZero_mem_image hsub hu
  exact hv ▸ v.property

/-- **Extension by zero as an operator `W^{1,p}_0(Ω) →L[ℝ] W^{1,p}_0(Ω')`.**  The extension of a
limit of test functions on `Ω` is again a limit of test functions, on `Ω'`, so the operator lands
in `W^{1,p}_0(Ω')` and not merely in `W^{1,p}(Ω')`; compose with
`(TauCeti.w1p0Submodule mu Omega' p).toSubmodule.subtypeL` for the `W^{1,p}(Ω')`-valued map.
Taking `Ω' = ⊤`, that is `hsub = le_top`, gives the extension operator to the whole space. -/
def W1p0.extendByZeroL (hsub : Omega ≤ Omega') :
    W1p0 mu Omega p →L[ℝ] W1p0 mu Omega' p :=
  ContinuousLinearMap.codRestrict
    (ContinuousLinearMap.codRestrict
      ((Sobolev1JetLp.extendByZeroₗᵢ (mu := mu) (p := p) hsub).toContinuousLinearMap.comp
        ((w1pSubmodule mu Omega p).toSubmodule.subtypeL.comp
          (w1p0Submodule mu Omega p).toSubmodule.subtypeL))
      (w1pSubmodule mu Omega' p).toSubmodule
      fun u => Sobolev1JetLp.extendByZeroₗᵢ_mem_w1pSubmodule hsub u.property)
    (w1p0Submodule mu Omega' p).toSubmodule
    fun u => mem_w1p0Submodule_of_coe_eq hsub u.property rfl

/-- The ambient jet of the extension is the extension of the ambient jet. -/
@[simp]
theorem W1p0.coe_extendByZeroL (hsub : Omega ≤ Omega') (u : W1p0 mu Omega p) :
    ((W1p0.extendByZeroL hsub u : W1p mu Omega' p) : Sobolev1JetLp mu Omega' p) =
      Sobolev1JetLp.extendByZeroₗᵢ hsub ((u : W1p mu Omega p) : Sobolev1JetLp mu Omega p) :=
  (rfl)

/-- **Extending by zero from `Ω` to `Ω` does nothing.** -/
@[simp]
theorem W1p0.extendByZeroL_self (u : W1p0 mu Omega p) : W1p0.extendByZeroL le_rfl u = u :=
  Subtype.ext (Subtype.ext (extendByZeroLpₗᵢ_self ℝ _ _))

/-- **Extending by zero twice is extending by zero once.** -/
@[simp]
theorem W1p0.extendByZeroL_extendByZeroL (hsub : Omega ≤ Omega') (hsub' : Omega' ≤ Omega'')
    (u : W1p0 mu Omega p) :
    W1p0.extendByZeroL hsub' (W1p0.extendByZeroL hsub u) =
      W1p0.extendByZeroL (hsub.trans hsub') u :=
  Subtype.ext (Subtype.ext (extendByZeroLpₗᵢ_extendByZeroLpₗᵢ ℝ _ _ _ _ _))

/-- **Extension by zero is an isometry of Sobolev spaces.**  The `W^{1,p}` norm — the `Lᵖ` norm
of the value-gradient jet — is unchanged; the extension adds a region on which both components
vanish. -/
theorem W1p0.norm_extendByZeroL (hsub : Omega ≤ Omega') (u : W1p0 mu Omega p) :
    ‖W1p0.extendByZeroL hsub u‖ = ‖u‖ :=
  (Sobolev1JetLp.extendByZeroₗᵢ hsub).norm_map _

/-- The value component of the extension is the zero-extension of the value component. -/
@[simp]
theorem W1p0.value_extendByZeroL (hsub : Omega ≤ Omega') (u : W1p0 mu Omega p) :
    W1p.value (W1p0.extendByZeroL hsub u : W1p mu Omega' p) =
      extendByZeroLpₗᵢ ℝ mu Omega.isOpen.nullMeasurableSet (SetLike.coe_subset_coe.mpr hsub)
        (W1p.value (u : W1p mu Omega p)) := by
  rw [W1p.value_coe, W1p.value_coe, W1p0.coe_extendByZeroL,
    Sobolev1JetLp.value_extendByZeroₗᵢ]

/-- The value component of the whole-space zero extension of `u ∈ W^{1,p}_0(Ω)` vanishes almost
everywhere off `Ω`. Thus its support is contained in `Ω` up to a null set; when `Ω` is bounded,
this is the fixed-bounded-support input for Fréchet--Kolmogorov. -/
theorem W1p0.value_extendByZeroL_ae_eq_zero_compl (u : W1p0 mu Omega p) :
    ∀ᵐ x ∂mu, x ∉ (Omega : Set E) →
      W1p.value (W1p0.extendByZeroL le_top u : W1p mu ⊤ p) x = 0 := by
  rw [W1p0.value_extendByZeroL (Omega' := ⊤) le_top u]
  have hvalue : ⇑(extendByZeroLpₗᵢ ℝ mu Omega.isOpen.nullMeasurableSet
      (SetLike.coe_subset_coe.mpr (le_top : Omega ≤ ⊤))
      (W1p.value (u : W1p mu Omega p))) =ᵐ[mu]
      (Omega : Set E).indicator (W1p.value (u : W1p mu Omega p) : E → ℝ) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      coeFn_extendByZeroLpₗᵢ ℝ Omega.isOpen.nullMeasurableSet
        (SetLike.coe_subset_coe.mpr (le_top : Omega ≤ ⊤)) (W1p.value (u : W1p mu Omega p))
  filter_upwards [hvalue] with x hx hxo
  rw [hx, Set.indicator_of_notMem hxo]

/-- The gradient component of the extension is the zero-extension of the gradient component. -/
@[simp]
theorem W1p0.gradient_extendByZeroL (hsub : Omega ≤ Omega') (u : W1p0 mu Omega p) :
    W1p.gradient (W1p0.extendByZeroL hsub u : W1p mu Omega' p) =
      extendByZeroLpₗᵢ ℝ mu Omega.isOpen.nullMeasurableSet (SetLike.coe_subset_coe.mpr hsub)
        (W1p.gradient (u : W1p mu Omega p)) := by
  rw [W1p.gradient_coe, W1p.gradient_coe, W1p0.coe_extendByZeroL,
    Sobolev1JetLp.gradient_extendByZeroₗᵢ]

/-- Extension by zero preserves the `Lᵖ` norm of the value component. -/
theorem W1p0.norm_value_extendByZeroL (hsub : Omega ≤ Omega') (u : W1p0 mu Omega p) :
    ‖W1p.value (W1p0.extendByZeroL hsub u : W1p mu Omega' p)‖ = ‖W1p.value (u : W1p mu Omega p)‖ :=
  by rw [W1p0.value_extendByZeroL, LinearIsometry.norm_map]

/-- Extension by zero preserves the `Lᵖ` norm of the weak gradient. -/
theorem W1p0.norm_gradient_extendByZeroL (hsub : Omega ≤ Omega') (u : W1p0 mu Omega p) :
    ‖W1p.gradient (W1p0.extendByZeroL hsub u : W1p mu Omega' p)‖ =
      ‖W1p.gradient (u : W1p mu Omega p)‖ := by
  rw [W1p0.gradient_extendByZeroL, LinearIsometry.norm_map]

/-- **Restricting a zero extension recovers the original function.** For `u ∈ W^{1,p}_0(Ω)` and
`Ω ⊆ Ω'`, the restriction to `Ω` of the zero-extension of `u` to `Ω'` is `u`. -/
@[simp]
theorem W1p0.restrictL_extendByZeroL (hsub : Omega ≤ Omega') (u : W1p0 mu Omega p) :
    W1p.restrictL hsub (W1p0.extendByZeroL hsub u : W1p mu Omega' p) = u :=
  W1p.ext_value (Lp.ext ((W1p.value_restrictL_ae hsub _).trans (by
    rw [W1p0.value_extendByZeroL]
    exact coeFn_extendByZeroLpₗᵢ_restrict ℝ _ _ _)))

/-- **Restricting a zero extension to a smaller open set.** For `u ∈ W^{1,p}_0(Ω)`, `Ω ⊆ Ω'` and
an open `V ⊆ Ω`, the restriction to `V` of the zero extension of `u` to `Ω'` is the restriction of
`u` to `V`. -/
theorem W1p0.restrictL_extendByZeroL_of_le {V : Opens E} (hsub : Omega ≤ Omega')
    (hV : V ≤ Omega') (hVΩ : V ≤ Omega) (u : W1p0 mu Omega p) :
    W1p.restrictL hV (W1p0.extendByZeroL hsub u : W1p mu Omega' p) =
      W1p.restrictL hVΩ (u : W1p mu Omega p) := by
  conv_rhs => rw [← W1p0.restrictL_extendByZeroL hsub u]
  rw [W1p.restrictL_restrictL]

/-- **Restricting a zero extension to another open set.** For `u ∈ W^{1,p}_0(Ω)`, `Ω ⊆ Ω'` and an
open `V ⊆ Ω'`, the restriction to `V` of the zero extension of `u` to `Ω'` has, almost everywhere
on `V`, the zero extension `1_Ω u` of the value of `u` as its value. -/
theorem W1p0.value_restrictL_extendByZeroL_ae {V : Opens E} (hsub : Omega ≤ Omega')
    (hV : V ≤ Omega') (u : W1p0 mu Omega p) :
    ∀ᵐ x ∂mu.restrict V, W1p.value (W1p.restrictL hV
      (W1p0.extendByZeroL hsub u : W1p mu Omega' p)) x =
        (Omega : Set E).indicator (W1p.value (u : W1p mu Omega p)) x := by
  filter_upwards [W1p.value_restrictL_ae hV (W1p0.extendByZeroL hsub u : W1p mu Omega' p),
    ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.mpr hV)
      (coeFn_extendByZeroLpₗᵢ ℝ Omega.isOpen.nullMeasurableSet (SetLike.coe_subset_coe.mpr hsub)
        (W1p.value (u : W1p mu Omega p)))] with x h1 h2
  rw [h1, W1p0.value_extendByZeroL, h2]

/-- **Restricting a zero extension to another open set.** For `u ∈ W^{1,p}_0(Ω)`, `Ω ⊆ Ω'` and an
open `V ⊆ Ω'`, the restriction to `V` of the zero extension of `u` to `Ω'` has, almost everywhere
on `V`, the zero extension `1_Ω ∇u` of the weak gradient of `u` as its weak gradient. -/
theorem W1p0.gradient_restrictL_extendByZeroL_ae {V : Opens E} (hsub : Omega ≤ Omega')
    (hV : V ≤ Omega') (u : W1p0 mu Omega p) :
    ∀ᵐ x ∂mu.restrict V, W1p.gradient (W1p.restrictL hV
      (W1p0.extendByZeroL hsub u : W1p mu Omega' p)) x =
        (Omega : Set E).indicator (W1p.gradient (u : W1p mu Omega p)) x := by
  filter_upwards [W1p.gradient_restrictL_ae hV (W1p0.extendByZeroL hsub u : W1p mu Omega' p),
    ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.mpr hV)
      (coeFn_extendByZeroLpₗᵢ ℝ Omega.isOpen.nullMeasurableSet (SetLike.coe_subset_coe.mpr hsub)
        (W1p.gradient (u : W1p mu Omega p)))] with x h1 h2
  rw [h1, W1p0.gradient_extendByZeroL, h2]

/-- **Integrating against the gradient of a zero extension.** For `u ∈ W^{1,p}_0(Ω)`, `Ω ⊆ Ω'`,
an open `V ⊆ Ω'` and a density `φ` with `φ x 0 = 0`, the integral over `V` of `φ x` applied to
the gradient of the zero extension of `u` is the integral of `φ x (∇u x)` over `V ∩ Ω`. -/
theorem W1p0.setIntegral_gradient_restrictL_extendByZeroL {V : Opens E} (hsub : Omega ≤ Omega')
    (hV : V ≤ Omega') (u : W1p0 mu Omega p) (φ : E → E → ℝ) (hφ : ∀ x, φ x 0 = 0) :
    ∫ x in V, φ x (W1p.gradient (W1p.restrictL hV
        (W1p0.extendByZeroL hsub u : W1p mu Omega' p)) x) ∂mu =
      ∫ x in (V : Set E) ∩ Omega, φ x (W1p.gradient (u : W1p mu Omega p) x) ∂mu := by
  rw [← setIntegral_indicator Omega.isOpen.measurableSet]
  refine integral_congr_ae ?_
  filter_upwards [W1p0.gradient_restrictL_extendByZeroL_ae hsub hV u] with x h1
  rw [h1]
  by_cases hxO : x ∈ (Omega : Set E)
  · rw [indicator_of_mem hxO, indicator_of_mem hxO]
  · rw [indicator_of_notMem hxO, indicator_of_notMem hxO, hφ]

/-- The value component of the extension agrees almost everywhere on `Ω'` with the indicator of
`Ω` applied to the value component of `u`. -/
theorem W1p0.value_extendByZeroL_ae (hsub : Omega ≤ Omega') (u : W1p0 mu Omega p) :
    (W1p.value (W1p0.extendByZeroL hsub u : W1p mu Omega' p) : E → ℝ) =ᵐ[mu.restrict Omega']
      (Omega : Set E).indicator (W1p.value (u : W1p mu Omega p) : E → ℝ) := by
  rw [W1p0.value_extendByZeroL]
  exact coeFn_extendByZeroLpₗᵢ _ _ _ _

/-- The gradient component of the extension agrees almost everywhere on `Ω'` with the indicator
of `Ω` applied to the weak gradient of `u`. -/
theorem W1p0.gradient_extendByZeroL_ae (hsub : Omega ≤ Omega') (u : W1p0 mu Omega p) :
    (W1p.gradient (W1p0.extendByZeroL hsub u : W1p mu Omega' p) : E → E) =ᵐ[mu.restrict Omega']
      (Omega : Set E).indicator (W1p.gradient (u : W1p mu Omega p) : E → E) := by
  rw [W1p0.gradient_extendByZeroL]
  exact coeFn_extendByZeroLpₗᵢ _ _ _ _

/-- The value component of the whole-space extension is almost everywhere the indicator of `Ω`
applied to the value component of `u`. -/
theorem W1p0.value_extendByZeroL_top_ae (u : W1p0 mu Omega p) :
    (W1p.value (W1p0.extendByZeroL le_top u : W1p mu ⊤ p) : E → ℝ) =ᵐ[mu]
      (Omega : Set E).indicator (W1p.value (u : W1p mu Omega p) : E → ℝ) := by
  simpa only [Opens.coe_top, Measure.restrict_univ] using W1p0.value_extendByZeroL_ae le_top u

/-- The gradient component of the whole-space extension is almost everywhere the indicator of `Ω`
applied to the weak gradient of `u`. -/
theorem W1p0.gradient_extendByZeroL_top_ae (u : W1p0 mu Omega p) :
    (W1p.gradient (W1p0.extendByZeroL le_top u : W1p mu ⊤ p) : E → E) =ᵐ[mu]
      (Omega : Set E).indicator (W1p.gradient (u : W1p mu Omega p) : E → E) := by
  simpa only [Opens.coe_top, Measure.restrict_univ] using W1p0.gradient_extendByZeroL_ae le_top u

/-- **Zero extensions from an exhaustion are dense.** If a directed family of open sets `U k ⊆ Ω`
covers `Ω`, then the zero extensions to `Ω` of the functions of `W^{1,p}_0(U k)`, over all `k`, are
dense in `W^{1,p}_0(Ω)`. The compact support of a test function on `Ω` lies in a single `U k`, so
every test function on `Ω` is such a zero extension. -/
theorem W1p0.dense_iUnion_range_extendByZeroL {κ : Type*} [Nonempty κ] {U : κ → Opens E}
    (hdir : Directed (· ≤ ·) U) (hU : ∀ k, U k ≤ Omega)
    (hcover : (Omega : Set E) ⊆ ⋃ k, (U k : Set E)) :
    Dense (⋃ k, range (W1p0.extendByZeroL (mu := mu) (p := p) (hU k))) := by
  set D := ⋃ k, range (W1p0.extendByZeroL (mu := mu) (p := p) (hU k))
  have htest : ∀ phi : 𝓓(Omega, ℝ),
      W1p.ofTestFunctionₗ mu Omega p phi ∈ ((↑) '' D : Set (W1p mu Omega p)) := by
    intro phi
    obtain ⟨k, hk⟩ := phi.hasCompactSupport.isCompact.elim_directed_cover (fun k ↦ (U k : Set E))
      (fun k ↦ (U k).isOpen) (phi.tsupport_subset.trans hcover)
      (fun i j ↦ (hdir i j).imp fun _ h ↦ ⟨SetLike.coe_subset_coe.2 h.1,
        SetLike.coe_subset_coe.2 h.2⟩)
    let psi : 𝓓(U k, ℝ) := ⟨phi, phi.contDiff, phi.hasCompactSupport, hk⟩
    refine ⟨W1p0.extendByZeroL (hU k) ⟨W1p.ofTestFunctionₗ mu (U k) p psi,
      W1p.ofTestFunctionₗ_mem_w1p0Submodule psi⟩, mem_iUnion.2 ⟨k, mem_range_self _⟩, ?_⟩
    refine Subtype.ext ?_
    rw [W1p0.coe_extendByZeroL, Sobolev1JetLp.extendByZeroₗᵢ_ofTestFunctionₗ]
    congr 2
    exact TestFunction.ext fun x ↦ congrFun (TestFunction.coe_monoCLM_of_le le_rfl (hU k) psi) x
  have hsub : (w1p0Submodule mu Omega p : Set (W1p mu Omega p)) ⊆ closure ((↑) '' D) :=
    w1p0Submodule_subset_of_isClosed isClosed_closure fun phi ↦ subset_closure (htest phi)
  intro u
  rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
  exact hsub u.property

/-- **The analytic content of the extension theorem.**  The zero-extension of `u ∈ W^{1,p}_0(Ω)`
is weakly differentiable on the larger open set `Ω'`, with weak gradient the zero-extension of the
weak gradient of `u`.  This is the statement that can *fail* for a general `u ∈ W^{1,p}(Ω)`: with
no condition forcing `u` to vanish towards `∂Ω`, its zero-extension need not be weakly
differentiable on `Ω'` at all. -/
theorem W1p0.hasWeakFDerivOn_indicator (hsub : Omega ≤ Omega')
    (u : W1p0 mu Omega p) :
    HasWeakFDerivOn mu Omega'
      ((Omega : Set E).indicator (W1p.value (u : W1p mu Omega p) : E → ℝ))
      fun x => innerSL ℝ
        ((Omega : Set E).indicator (W1p.gradient (u : W1p mu Omega p) : E → E) x) := by
  have hbridge :=
    (W1p.value_coe (W1p0.extendByZeroL hsub u : W1p mu Omega' p)).symm
  have hmem := (mem_w1pSubmodule_iff_hasWeakFDerivOn
    ((W1p0.extendByZeroL hsub u : W1p mu Omega' p) : Sobolev1JetLp mu Omega' p)).mp
      (W1p0.extendByZeroL hsub u : W1p mu Omega' p).property
  rw [hbridge] at hmem
  refine (hmem.congr_ae (W1p0.value_extendByZeroL_ae hsub u)).congr_ae_deriv ?_
  filter_upwards [W1p0.gradient_extendByZeroL_ae hsub u] with x hx
  rw [Sobolev1JetLp.candidateWeakFDeriv_def, ← W1p.gradient_coe, hx]

/-- **The weak gradient of a `W^{1,p}_0` function on a bounded set has integral zero.** If `Ω` is
bounded and `u ∈ W^{1,p}_0(Ω)`, then `∫_Ω ⟪∇u, w⟫ = 0` for every direction `w`. A function of
`W^{1,p}(Ω)` need not have this property, so it detects functions with nonzero boundary values:
a function of `W^{1,p}(Ω)` with `∫_Ω ⟪∇u, w⟫ ≠ 0` for some `w` is not in `W^{1,p}_0(Ω)`. -/
theorem W1p0.setIntegral_inner_gradient_eq_zero (hΩ : Bornology.IsBounded (Omega : Set E))
    (u : W1p0 mu Omega p) (w : E) :
    ∫ x in Omega, ⟪W1p.gradient (u : W1p mu Omega p) x, w⟫_ℝ ∂mu = 0 := by
  -- Test the weak derivative of the zero-extension against a bump function equal to `1` on a
  -- neighbourhood of `Ω`.
  obtain ⟨R, hR⟩ := hΩ.subset_ball (0 : E)
  let φ : ContDiffBump (0 : E) := ⟨max R 1, max R 1 + 1, by positivity, by linarith⟩
  have hφΩ : ∀ x ∈ (Omega : Set E), φ =ᶠ[nhds x] fun _ => (1 : ℝ) := fun x hx =>
    Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball
        (le_max_left R 1) (hR hx)))
      fun y hy => φ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
  have hweak := (hasWeakFDerivOn_iff.1 (W1p0.hasWeakFDerivOn_indicator le_top u)) w
  have hid := hweak.integral_lineDeriv_smul_eq_neg_integral_smul
    ⟨φ, φ.contDiff, φ.hasCompactSupport, by simp⟩
  rw [TestFunction.coe_mk] at hid
  have hleft : ∀ x, lineDeriv ℝ (φ : E → ℝ) x w •
      (Omega : Set E).indicator (W1p.value (u : W1p mu Omega p) : E → ℝ) x = 0 := fun x => by
    by_cases hx : x ∈ (Omega : Set E)
    · simp [((φ.contDiff (n := 1)).differentiable one_ne_zero x).lineDeriv_eq_fderiv,
        (hφΩ x hx).fderiv_eq]
    · rw [Set.indicator_of_notMem hx, smul_zero]
  have hright : ∀ x, (φ : E → ℝ) x • innerSL ℝ
      ((Omega : Set E).indicator (W1p.gradient (u : W1p mu Omega p) : E → E) x) w =
      (Omega : Set E).indicator (fun x => ⟪W1p.gradient (u : W1p mu Omega p) x, w⟫_ℝ) x :=
    fun x => by
      by_cases hx : x ∈ (Omega : Set E)
      · simp [Set.indicator_of_mem hx, (hφΩ x hx).eq_of_nhds]
      · simp [Set.indicator_of_notMem hx]
  simp only [hleft, integral_zero, hright,
    integral_indicator Omega.isOpen.measurableSet] at hid
  linarith

/-- **A function with the boundary values of `g` is not constant when `⟪∇g, w⟫ = 1`.**
On a bounded nonempty `Ω`, if `⟪∇g, w⟫ = 1` almost everywhere, then no `u ∈ W^{1,p}(Ω)` with
`u - g ∈ W^{1,p}_0(Ω)` is almost everywhere constant: otherwise `∫_Ω ⟪∇(u - g), w⟫ = -μ(Ω)` would
vanish by `TauCeti.W1p0.setIntegral_inner_gradient_eq_zero`. -/
theorem W1p0.not_exists_value_ae_eq_const_of_inner_gradient_eq_one
    (hΩ : Bornology.IsBounded (Omega : Set E)) (hne : (Omega : Set E).Nonempty)
    {u g : W1p mu Omega p} {w : E}
    (hg : ∀ᵐ x ∂mu.restrict Omega, ⟪W1p.gradient g x, w⟫_ℝ = 1)
    (hug : u - g ∈ w1p0Submodule mu Omega p) :
    ¬ ∃ c : ℝ, W1p.value u =ᵐ[mu.restrict Omega] fun _ => c := by
  rintro ⟨c, hc⟩
  have hfin : mu (Omega : Set E) < ⊤ := hΩ.measure_lt_top
  have : IsFiniteMeasure (mu.restrict (Omega : Set E)) := isFiniteMeasure_restrict.2 hfin.ne
  have hconst : W1p.value u = W1p.value (W1p.const c : W1p mu Omega p) := by
    exact Lp.ext (hc.trans (W1p.value_const_ae c).symm)
  have hgu : W1p.gradient (u - g) = -W1p.gradient g := by
    simp [W1p.ext_value hconst]
  have hgrad : ∀ᵐ x ∂mu.restrict Omega, ⟪W1p.gradient (u - g) x, w⟫_ℝ = -1 := by
    filter_upwards [hg, Lp.coeFn_neg (W1p.gradient g)] with x hgx hnx
    simp only [hgu, hnx, Pi.neg_apply, inner_neg_left, hgx]
  have hint := W1p0.setIntegral_inner_gradient_eq_zero hΩ ⟨u - g, hug⟩ w
  rw [integral_congr_ae hgrad] at hint
  have hpos : 0 < mu.real (Omega : Set E) :=
    ENNReal.toReal_pos (Omega.isOpen.measure_pos mu hne).ne' hfin.ne
  simp at hint
  linarith

end TauCeti
