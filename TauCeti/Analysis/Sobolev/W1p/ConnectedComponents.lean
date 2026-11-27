/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic
public import TauCeti.Analysis.Sobolev.W1p.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.Connected.Clopen
public import TauCeti.Topology.LocallyConstant.ConnectedComponents
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.MeasureTheory.Measure.OpenPos
import TauCeti.Analysis.Sobolev.LipschitzDomain.ConnectedComponents
import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.W1p
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz
import TauCeti.MeasureTheory.Function.LocallyAEConst
import TauCeti.Topology.Connected.Basic
import TauCeti.Topology.ConnectedComponents

/-!
# Sobolev functions with vanishing gradient and the components of the domain

On any open set `Ω`, a Sobolev function has vanishing weak gradient exactly when it agrees almost
everywhere with a function that is locally constant on `Ω`
(`TauCeti.W1p.gradient_eq_zero_iff_exists_isLocallyConstant`), that is, constant on each
connected component of `Ω`. When `Ω` has finite measure and finitely many components, every
function on the set of components defines such a Sobolev function, and different functions give
different Sobolev functions, since each component is a nonempty open set and so has positive
measure. The kernel of the weak gradient on `W^{1,p}(Ω)` is therefore a vector space whose
dimension is the number of connected components of `Ω`.

For `p = 2` this kernel is the eigenspace of the eigenvalue `0` of the Neumann Laplacian, so the
dimension count is the multiplicity of that eigenvalue. A bounded Lipschitz domain has finite
measure and finitely many components
(`Set.IsLipschitzDomain.finite_connectedComponents_of_isBounded`), so the count applies to it.

On a preconnected `Ω` of finite measure the kernel consists of the constants, and the only one with
`∫_Ω u = 0` is `0` (`TauCeti.W1p.eq_zero_of_gradient_eq_zero_of_setIntegral_eq_zero`). This fails
as soon as `Ω` is not preconnected: a splitting into two disjoint nonempty open pieces gives a
nonzero function, constant on each piece, of mean zero.

## Main declarations

* `TauCeti.W1p.ofIsLocallyConstant`: the Sobolev function of an `Lᵖ` function that is locally
  constant on `Ω`, whose weak gradient vanishes.
* `TauCeti.W1p.componentFunEquivKerGradientL`: on a domain of finite measure with finitely many
  connected components, the Sobolev functions with vanishing weak gradient are identified, as a
  linear equivalence, with the functions on the set of components.
* `TauCeti.W1p.finrank_ker_gradientL`: on a domain of finite measure with finitely many connected
  components, the Sobolev functions with vanishing weak gradient form a space whose dimension is
  the number of components.
* `TauCeti.W1p.finrank_ker_gradientL_of_isLipschitzDomain`: the same on a bounded Lipschitz
  domain.
* `TauCeti.W1p.exists_value_ae_eq_indicator_add_indicator_and_gradient_eq_zero_and_setIntegral_eq`:
  if `Ω` is the union of two disjoint open sets, a function constant on each of them is a Sobolev
  function with vanishing weak gradient.
* `TauCeti.W1p.exists_ne_zero_and_gradient_eq_zero_and_setIntegral_eq_zero`: on an open set of
  finite measure that is not preconnected, some nonzero Sobolev function with vanishing weak
  gradient has mean zero.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Module Set TopologicalSpace
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Omega : Opens E}

section LocallyConstant

variable [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E}
  [mu.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)] {g : E → ℝ}

/-- The Sobolev function with value `g`, for a function `g` in `Lᵖ(Ω)` that is locally constant on
`Ω`. Its weak gradient vanishes. -/
def W1p.ofIsLocallyConstant (hg : IsLocallyConstant ((Omega : Set E).domRestrict g))
    (hgp : MemLp g p (mu.restrict Omega)) : W1p mu Omega p :=
  W1p.mk (hgp.toLp g) 0 <|
    ((hg.hasWeakFDerivOn_zero (μ := mu)).congr_ae hgp.coeFn_toLp.symm).congr_ae_deriv <| by
      filter_upwards [Lp.coeFn_zero E p (mu.restrict Omega)] with x hx
      rw [hx, Pi.zero_apply, Pi.zero_apply, map_zero]

/-- The value of `W1p.ofIsLocallyConstant hg hgp` is the class of `g` in `Lᵖ(Ω)`. -/
@[simp]
theorem W1p.value_ofIsLocallyConstant (hg : IsLocallyConstant ((Omega : Set E).domRestrict g))
    (hgp : MemLp g p (mu.restrict Omega)) :
    W1p.value (W1p.ofIsLocallyConstant hg hgp) = hgp.toLp g :=
  W1p.value_mk _ _ _

/-- The value of `W1p.ofIsLocallyConstant hg hgp` agrees almost everywhere on `Ω` with `g`. -/
theorem W1p.value_ofIsLocallyConstant_ae (hg : IsLocallyConstant ((Omega : Set E).domRestrict g))
    (hgp : MemLp g p (mu.restrict Omega)) :
    W1p.value (W1p.ofIsLocallyConstant hg hgp) =ᵐ[mu.restrict Omega] g := by
  rw [W1p.value_ofIsLocallyConstant]
  exact hgp.coeFn_toLp

/-- The Sobolev function `W1p.ofIsLocallyConstant hg hgp` has vanishing weak gradient. -/
@[simp]
theorem W1p.gradient_ofIsLocallyConstant (hg : IsLocallyConstant ((Omega : Set E).domRestrict g))
    (hgp : MemLp g p (mu.restrict Omega)) : W1p.gradient (W1p.ofIsLocallyConstant hg hgp) = 0 :=
  W1p.gradient_mk _ _ _

end LocallyConstant

section Components

variable [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E}
  {p : ℝ≥0∞} [IsFiniteMeasure (mu.restrict (Omega : Set E))]
  [Finite (ConnectedComponents (Omega : Set E))]

omit [FiniteDimensional ℝ E] in
/-- With finitely many components, `componentFun φ` is bounded, hence in `Lᵖ(Ω)` on a domain of
finite measure. -/
private theorem memLp_componentFun (φ : ConnectedComponents (Omega : Set E) → ℝ) :
    MemLp (componentFun φ) p (mu.restrict Omega) := by
  obtain ⟨C, hC⟩ := (Set.finite_range fun c => |φ c|).bddAbove
  have hcont : ContinuousOn (componentFun φ) Omega :=
    continuousOn_iff_continuous_domRestrict.2
      (isLocallyConstant_componentFun Omega.isOpen φ).continuous
  refine MemLp.of_bound (hcont.aestronglyMeasurable Omega.isOpen.measurableSet) (max C 0)
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs]
  by_cases hx : x ∈ Omega
  · rw [componentFun_of_mem φ hx]
    exact (hC ⟨_, rfl⟩).trans (le_max_left _ _)
  · simp [componentFun_of_notMem φ hx]

variable [mu.IsAddHaarMeasure] [Fact (1 ≤ p)]

/-- The Sobolev function equal to `φ c` on the component `c` of `Ω`. -/
private def componentW1p (φ : ConnectedComponents (Omega : Set E) → ℝ) : W1p mu Omega p :=
  W1p.ofIsLocallyConstant (isLocallyConstant_componentFun Omega.isOpen φ) (memLp_componentFun φ)

private theorem value_componentW1p (φ : ConnectedComponents (Omega : Set E) → ℝ) :
    W1p.value (componentW1p (mu := mu) (p := p) φ) = (memLp_componentFun φ).toLp _ :=
  W1p.value_ofIsLocallyConstant _ _

/-- The Sobolev functions that are constant on each component of `Ω`, as a linear map. -/
private def componentW1pₗ :
    (ConnectedComponents (Omega : Set E) → ℝ) →ₗ[ℝ] W1p mu Omega p where
  toFun := componentW1p
  map_add' φ ψ := W1p.ext_value <| by
    simp only [W1p.value_add, value_componentW1p, ← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (by rw [componentFun_add])
  map_smul' c φ := W1p.ext_value <| by
    simp only [W1p.value_smul, value_componentW1p, RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (by rw [componentFun_smul])

private theorem componentW1pₗ_apply (φ : ConnectedComponents (Omega : Set E) → ℝ) :
    componentW1pₗ (mu := mu) (p := p) φ = componentW1p φ :=
  rfl

/-- Distinct functions on the components give distinct Sobolev functions: each component is a
nonempty open set, of positive measure. -/
private theorem componentW1pₗ_injective :
    Function.Injective (componentW1pₗ (mu := mu) (Omega := Omega) (p := p)) := by
  refine (injective_iff_map_eq_zero _).2 fun φ hφ => funext fun c => ?_
  have hval : componentFun φ =ᵐ[mu.restrict Omega] 0 := by
    have h := congrArg W1p.value hφ
    rw [componentW1pₗ_apply, value_componentW1p, W1p.value_zero] at h
    filter_upwards [(memLp_componentFun φ).coeFn_toLp, Lp.coeFn_zero ℝ p (mu.restrict Omega),
      Lp.ext_iff.1 h] with x h1 h2 h3
    rw [← h1, h3, h2]
  -- On the carrier of `c`, an open subset of `Ω`, `componentFun φ` is the constant `φ c`.
  obtain ⟨x, hx⟩ := c.carrierIn_nonempty
  have hopen : IsOpen c.carrierIn := by
    rw [ConnectedComponents.carrierIn_eq_connectedComponentIn hx]
    exact Omega.isOpen.connectedComponentIn
  refine eq_of_ae_eq_of_mem_nhds (μ := mu) (hopen.mem_nhds hx) (hopen.mem_nhds hx) ?_
    (ae_restrict_of_ae_restrict_of_subset c.carrierIn_subset hval)
  filter_upwards [ae_restrict_mem hopen.measurableSet] with y hy
  obtain ⟨hyΩ, hyc⟩ := ConnectedComponents.mem_carrierIn_iff.1 hy
  rw [componentFun_of_mem φ hyΩ, hyc]

/-- The Sobolev functions constant on each component of `Ω` are exactly those with vanishing weak
gradient. -/
private theorem range_componentW1pₗ :
    LinearMap.range (componentW1pₗ (mu := mu) (Omega := Omega) (p := p)) =
      LinearMap.ker
        (W1p.gradientL : W1p mu Omega p →L[ℝ] Lp E p (mu.restrict Omega)).toLinearMap := by
  ext u
  simp only [LinearMap.mem_range, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    W1p.gradientL_apply]
  constructor
  · rintro ⟨φ, rfl⟩
    exact W1p.gradient_ofIsLocallyConstant (isLocallyConstant_componentFun Omega.isOpen φ)
      (memLp_componentFun φ)
  · intro hu
    obtain ⟨g, hg, hug⟩ := W1p.exists_isLocallyConstant_ae_eq_of_gradient_eq_zero hu
    -- The value of `u` on a component is the value of `g` at a chosen point of it.
    let rep := Function.surjInv (ConnectedComponents.surjective_coe (α := (Omega : Set E)))
    refine ⟨fun c => g (rep c), W1p.ext_value ?_⟩
    have hpt : ∀ x ∈ Omega, componentFun (fun c => g (rep c)) x = g x := fun x hx => by
      rw [componentFun_of_mem _ hx]
      have hrep : rep (ConnectedComponents.mk ⟨x, hx⟩) ∈ connectedComponent ⟨x, hx⟩ :=
        ConnectedComponents.coe_eq_coe'.1
          (Function.surjInv_eq ConnectedComponents.surjective_coe _)
      exact hg.apply_eq_of_isPreconnected isPreconnected_connectedComponent hrep
        mem_connectedComponent
    rw [componentW1pₗ_apply, value_componentW1p]
    refine Lp.ext ?_
    filter_upwards [(memLp_componentFun (mu := mu) (p := p) fun c => g (rep c)).coeFn_toLp, hug,
      ae_restrict_mem Omega.isOpen.measurableSet] with x h1 h2 hx
    rw [h1, h2, hpt x hx]

/-- **The kernel of the weak gradient is the space of functions on the components.** On an open
set `Ω` of finite measure with finitely many connected components, a function `φ` on the
components of `Ω` corresponds to the Sobolev function `componentFun φ`, equal to `φ c` on the
component `c`; these are exactly the Sobolev functions with vanishing weak gradient. -/
def W1p.componentFunEquivKerGradientL :
    (ConnectedComponents (Omega : Set E) → ℝ) ≃ₗ[ℝ] LinearMap.ker
      (W1p.gradientL : W1p mu Omega p →L[ℝ] Lp E p (mu.restrict Omega)).toLinearMap :=
  (LinearEquiv.ofInjective componentW1pₗ componentW1pₗ_injective).trans
    (LinearEquiv.ofEq _ _ range_componentW1pₗ)

/-- The Sobolev function attached to `φ` by `W1p.componentFunEquivKerGradientL` is almost
everywhere equal on `Ω` to `componentFun φ`. -/
theorem W1p.coeFn_value_componentFunEquivKerGradientL_apply
    (φ : ConnectedComponents (Omega : Set E) → ℝ) :
    W1p.value (W1p.componentFunEquivKerGradientL (mu := mu) (p := p) φ : W1p mu Omega p) =ᵐ[
      mu.restrict Omega] componentFun φ := by
  simp only [W1p.componentFunEquivKerGradientL, LinearEquiv.trans_apply,
    LinearEquiv.coe_ofEq_apply, LinearEquiv.ofInjective_apply, componentW1pₗ_apply,
    value_componentW1p]
  exact (memLp_componentFun φ).coeFn_toLp

/-- **The kernel of the weak gradient counts the connected components.** On an open set `Ω` of
finite measure with finitely many connected components, the Sobolev functions `u ∈ W^{1,p}(Ω)`
with vanishing weak gradient form a space whose dimension is the number of connected components
of `Ω`: they are the functions constant on each component. -/
theorem W1p.finrank_ker_gradientL :
    finrank ℝ (LinearMap.ker
        (W1p.gradientL : W1p mu Omega p →L[ℝ] Lp E p (mu.restrict Omega)).toLinearMap) =
      Nat.card (ConnectedComponents (Omega : Set E)) := by
  have := Fintype.ofFinite (ConnectedComponents (Omega : Set E))
  rw [← (W1p.componentFunEquivKerGradientL (mu := mu) (p := p)).finrank_eq,
    Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

end Components

section Disconnected

variable [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E}
  [mu.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)] [IsFiniteMeasure (mu.restrict (Omega : Set E))]

/-- **A function constant on each of two open pieces of `Ω` is a Sobolev function.** If `Ω` is
the union of disjoint open sets `U` and `V`, some `u ∈ W^{1,p}(Ω)` agrees almost everywhere with
the function equal to `c` on `U` and to `d` on `V`, has vanishing weak gradient, and has
`∫_Ω u = c μ(U) + d μ(V)`. -/
theorem W1p.exists_value_ae_eq_indicator_add_indicator_and_gradient_eq_zero_and_setIntegral_eq
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V) (hd : Disjoint U V)
    (hUV : (Omega : Set E) = U ∪ V) (c d : ℝ) :
    ∃ u : W1p mu Omega p,
      W1p.value u =ᵐ[mu.restrict Omega] U.indicator (fun _ => c) + V.indicator (fun _ => d) ∧
        W1p.gradient u = 0 ∧ ∫ x in Omega, W1p.value u x ∂mu = c * mu.real U + d * mu.real V := by
  have hloc := isLocallyConstant_domRestrict_indicator_add_indicator hU hV hd hUV c d
  have hgp : MemLp (U.indicator (fun _ => c) + V.indicator (fun _ => d)) p (mu.restrict Omega) :=
    ((memLp_const c).indicator hU.measurableSet.nullMeasurableSet).add
      ((memLp_const d).indicator hV.measurableSet.nullMeasurableSet)
  have hval := W1p.value_ofIsLocallyConstant_ae hloc hgp
  refine ⟨W1p.ofIsLocallyConstant hloc hgp, hval, W1p.gradient_ofIsLocallyConstant _ _, ?_⟩
  rw [integral_congr_ae hval, integral_add'
    ((integrable_const c).indicator hU.measurableSet)
    ((integrable_const d).indicator hV.measurableSet)]
  simp [integral_indicator_const _ hU.measurableSet, integral_indicator_const _ hV.measurableSet,
    measureReal_restrict_apply hU.measurableSet, measureReal_restrict_apply hV.measurableSet, hUV,
    mul_comm]

/-- **A disconnected domain carries a nonzero gradient-free function of mean zero.** If the open
set `Ω` has finite measure and is not preconnected, some nonzero `u ∈ W^{1,p}(Ω)` has vanishing
weak gradient and `∫_Ω u = 0`. For a splitting of `Ω` into disjoint nonempty open pieces `U` and
`V`, the function equal to `μ(V)` on `U` and to `-μ(U)` on `V` is one. On a preconnected `Ω` there
is no such function (`TauCeti.W1p.eq_zero_of_gradient_eq_zero_of_setIntegral_eq_zero`). -/
theorem W1p.exists_ne_zero_and_gradient_eq_zero_and_setIntegral_eq_zero
    (hΩ : ¬IsPreconnected (Omega : Set E)) :
    ∃ u : W1p mu Omega p, u ≠ 0 ∧ W1p.gradient u = 0 ∧ ∫ x in Omega, W1p.value u x ∂mu = 0 := by
  obtain ⟨U, V, hU, hV, hUne, hVne, hd, hUV⟩ := Omega.isOpen.not_isPreconnected_iff.1 hΩ
  obtain ⟨u, hval, hgrad, hint⟩ :=
    W1p.exists_value_ae_eq_indicator_add_indicator_and_gradient_eq_zero_and_setIntegral_eq
      (mu := mu) (p := p) hU hV hd hUV (mu.real V) (-mu.real U)
  refine ⟨u, fun h0 => ?_, hgrad, by rw [hint]; ring⟩
  -- On `U`, of positive measure, `u` is the constant `μ(V) > 0`, so `u` is not `0`.
  have ha : mu.real V ≠ 0 := by
    refine ENNReal.toReal_ne_zero.2 ⟨hV.measure_ne_zero mu hVne, ne_top_of_le_ne_top ?_
      (measure_mono (hUV ▸ subset_union_right : V ⊆ Omega))⟩
    rw [← Measure.restrict_apply_univ]
    exact measure_ne_top _ _
  have hfalse : ∀ᵐ _ ∂mu.restrict U, False := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (hUV ▸ subset_union_left) hval,
      ae_restrict_of_ae_restrict_of_subset (hUV ▸ subset_union_left)
        (Lp.coeFn_zero ℝ p (mu.restrict Omega)), ae_restrict_mem hU.measurableSet] with z h1 h2 hzU
    rw [h0, W1p.value_zero, h2, hd.indicator_add_indicator_apply_of_mem_left _ _ hzU] at h1
    exact ha h1.symm
  exact hU.measure_ne_zero mu hUne
    (Measure.restrict_eq_zero.1 (ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 hfalse)))

end Disconnected

/-- **On a bounded Lipschitz domain the kernel of the weak gradient counts the components.** For
a bounded Lipschitz domain `Ω`, the Sobolev functions `u ∈ W^{1,p}(Ω)` with vanishing weak
gradient form a space whose dimension is the number of connected components of `Ω`, which is
finite. -/
theorem W1p.finrank_ker_gradientL_of_isLipschitzDomain [MeasurableSpace E] [FiniteDimensional ℝ E]
    [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hΩ : (Omega : Set E).IsLipschitzDomain F) (hb : Bornology.IsBounded (Omega : Set E)) :
    finrank ℝ (LinearMap.ker
        (W1p.gradientL : W1p mu Omega p →L[ℝ] Lp E p (mu.restrict Omega)).toLinearMap) =
      Nat.card (ConnectedComponents (Omega : Set E)) := by
  have := isFiniteMeasure_restrict.2 (hb.measure_lt_top (μ := mu)).ne
  have := hΩ.finite_connectedComponents_of_isBounded hb
  exact W1p.finrank_ker_gradientL

end TauCeti
