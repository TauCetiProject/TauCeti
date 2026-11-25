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
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.MeasureTheory.Measure.OpenPos
import TauCeti.Analysis.Sobolev.LipschitzDomain.ConnectedComponents
import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.W1p
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz
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
measure and finitely many components (`Set.IsLipschitzDomain.finite_connectedComponents`), so
the count applies to it.

## Main declarations

* `TauCeti.W1p.finrank_ker_gradientL`: on a domain of finite measure with finitely many connected
  components, the Sobolev functions with vanishing weak gradient form a space whose dimension is
  the number of components.
* `TauCeti.W1p.finrank_ker_gradientL_of_isLipschitzDomain`: the same on a bounded Lipschitz
  domain.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Module Set TopologicalSpace
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Omega : Opens E}

section Components

open scoped Classical in
/-- The function equal to `φ c` on the connected component `c` of `Ω`, and to `0` off `Ω`. -/
private def componentFun (φ : ConnectedComponents (Omega : Set E) → ℝ) (x : E) : ℝ :=
  if hx : x ∈ Omega then φ (ConnectedComponents.mk ⟨x, hx⟩) else 0

omit [InnerProductSpace ℝ E] in
private theorem componentFun_of_mem (φ : ConnectedComponents (Omega : Set E) → ℝ) {x : E}
    (hx : x ∈ Omega) : componentFun φ x = φ (ConnectedComponents.mk ⟨x, hx⟩) := by
  simp [componentFun, hx]

omit [InnerProductSpace ℝ E] in
private theorem componentFun_add (φ ψ : ConnectedComponents (Omega : Set E) → ℝ) :
    componentFun (φ + ψ) = componentFun φ + componentFun ψ := by
  funext x
  by_cases hx : x ∈ Omega <;> simp [componentFun, hx]

omit [InnerProductSpace ℝ E] in
private theorem componentFun_smul (c : ℝ) (φ : ConnectedComponents (Omega : Set E) → ℝ) :
    componentFun (c • φ) = c • componentFun φ := by
  funext x
  by_cases hx : x ∈ Omega <;> simp [componentFun, hx]

/-- `componentFun φ` is locally constant on `Ω`, whose components are open. -/
private theorem isLocallyConstant_componentFun (φ : ConnectedComponents (Omega : Set E) → ℝ) :
    IsLocallyConstant ((Omega : Set E).domRestrict (componentFun φ)) := by
  have := Omega.isOpen.locallyConnectedSpace
  refine IsLocallyConstant.of_constant_on_connected_components fun x y hy => ?_
  simp only [domRestrict_apply, componentFun_of_mem φ x.property,
    componentFun_of_mem φ y.property]
  exact congrArg φ (ConnectedComponents.coe_eq_coe'.2 hy)

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
    continuousOn_iff_continuous_domRestrict.2 (isLocallyConstant_componentFun φ).continuous
  refine MemLp.of_bound (hcont.aestronglyMeasurable Omega.isOpen.measurableSet) (max C 0)
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs]
  by_cases hx : x ∈ Omega
  · rw [componentFun_of_mem φ hx]
    exact (hC ⟨_, rfl⟩).trans (le_max_left _ _)
  · simp [componentFun, hx]

variable [mu.IsAddHaarMeasure] [Fact (1 ≤ p)]

/-- The Sobolev function equal to `φ c` on the component `c` of `Ω`. -/
private def componentW1p (φ : ConnectedComponents (Omega : Set E) → ℝ) : W1p mu Omega p :=
  W1p.mk ((memLp_componentFun φ).toLp _) 0 <|
    (((isLocallyConstant_componentFun φ).hasWeakFDerivOn_zero (μ := mu)).congr_ae
      (memLp_componentFun φ).coeFn_toLp.symm).congr_ae_deriv <| by
        filter_upwards [Lp.coeFn_zero E p (mu.restrict Omega)] with x hx
        rw [hx, Pi.zero_apply, Pi.zero_apply, map_zero]

private theorem value_componentW1p (φ : ConnectedComponents (Omega : Set E) → ℝ) :
    W1p.value (componentW1p (mu := mu) (p := p) φ) = (memLp_componentFun φ).toLp _ :=
  W1p.value_mk _ _ _

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
  have : (ae (mu.restrict c.carrierIn)).NeBot :=
    ae_restrict_neBot.2 (hopen.measure_pos mu ⟨x, hx⟩).ne'
  obtain ⟨y, hy0, hyc⟩ := ((ae_restrict_of_ae_restrict_of_subset c.carrierIn_subset hval).and
    (ae_restrict_mem hopen.measurableSet)).exists
  obtain ⟨hyΩ, rfl⟩ := ConnectedComponents.mem_carrierIn_iff.1 hyc
  rw [← componentFun_of_mem φ hyΩ, hy0, Pi.zero_apply, Pi.zero_apply]

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
    exact W1p.gradient_mk _ _ _
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

/-- **The kernel of the weak gradient counts the connected components.** On an open set `Ω` of
finite measure with finitely many connected components, the Sobolev functions `u ∈ W^{1,p}(Ω)`
with vanishing weak gradient form a space whose dimension is the number of connected components
of `Ω`: they are the functions constant on each component. -/
theorem W1p.finrank_ker_gradientL :
    finrank ℝ (LinearMap.ker
        (W1p.gradientL : W1p mu Omega p →L[ℝ] Lp E p (mu.restrict Omega)).toLinearMap) =
      Nat.card (ConnectedComponents (Omega : Set E)) := by
  have := Fintype.ofFinite (ConnectedComponents (Omega : Set E))
  rw [← range_componentW1pₗ, LinearMap.finrank_range_of_inj componentW1pₗ_injective,
    Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

end Components

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
