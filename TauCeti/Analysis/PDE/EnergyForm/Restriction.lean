/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Sobolev
public import TauCeti.Analysis.Sobolev.W1p.Extension
public import TauCeti.Analysis.Sobolev.W1p.Restriction

/-!
# The energy form under restriction to a smaller domain

Let `U ⊆ Ω` be open sets. Testing the restriction `u|_U ∈ H¹(U)` of `u ∈ H¹(Ω)` against
`v ∈ H¹₀(U)` is the same as testing `u` against the zero extension of `v` to `Ω`: both jets of
the extension vanish off `U`, and on `U` the jets of `u` and `u|_U` agree. Consequently a weak
subsolution or supersolution on `Ω` restricts to one on `U`, and a weak solution of `L u = f` on
`Ω` restricts to a weak solution of `L u = f` on `U`. This lets local estimates for weak
subsolutions and supersolutions be proved on a ball, which has finite measure, without global
integrability hypotheses on `Ω`.

## Main declarations

* `TauCeti.PDE.energyFormH1_restrictL`: `a(u|_U, v) = a(u, v₀)` for `v ∈ H¹₀(U)` with zero
  extension `v₀ ∈ H¹₀(Ω)`.
* `TauCeti.PDE.energyFormH1_restrictL_nonpos`: weak subsolutions restrict to weak subsolutions.
* `TauCeti.PDE.energyFormH1_restrictL_nonneg`: weak supersolutions restrict to weak
  supersolutions.
* `TauCeti.PDE.energyFormH1_restrictL_add_const_nonpos`,
  `TauCeti.PDE.energyFormH1_restrictL_add_const_nonneg`: the restriction of a weak subsolution
  or supersolution with no mass term, shifted by a constant, is again one.
* `TauCeti.PDE.energyFormH1_restrictL_eq_setIntegral`: weak solutions restrict to weak solutions.
* `TauCeti.PDE.forall_energyFormH1_restrictL_eq_inner`: if `u` solves `-∂ⱼ(aⁱʲ ∂ᵢu) = -div G`
  weakly on `Ω`, tested against test functions, then on every open `B ⊆ Ω` on which `a` is
  essentially bounded it satisfies `a(u, v) = ⟪G - c, ∇v⟫_{L²(B)}` for every `v ∈ H¹₀(B)` and
  every constant `c` with `G - c ∈ L²(B)`, since constants have zero divergence. This is the
  hypothesis of the energy estimate for the replacement on a ball.
* `TauCeti.PDE.inner_toLp_gradient_ofTestFunctionₗ`: the test-function case,
  `⟪G - c, ∇φ⟫_{L²(B)} = ∫_B ⟨G, ∇φ⟩`.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega U : Opens (EuclideanSpace ℝ ι)}

/-- **The energy form of a restriction.** For open sets `U ⊆ Ω`, `u ∈ H¹(Ω)` and `v ∈ H¹₀(U)`,
the energy form on `U` of the restriction `u|_U` against `v` equals the energy form on `Ω` of `u`
against the zero extension of `v`. -/
theorem energyFormH1_restrictL (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (c : EuclideanSpace ℝ ι → ℝ) (hU : U ≤ Omega)
    (u : W1p mu Omega 2) (v : W1p0 mu U 2) :
    energyFormH1 a b c (W1p.restrictL hU u) (v : W1p mu U 2) =
      energyFormH1 a b c u (W1p0.extendByZeroL hU v : W1p mu Omega 2) := by
  have hUm := U.isOpen.measurableSet
  have hUO : (U : Set (EuclideanSpace ℝ ι)) ⊆ Omega := SetLike.coe_subset_coe.mpr hU
  -- The jet field of the zero extension is the zero extension of the jet field.
  have hjet : jetField (W1p0.extendByZeroL hU v : W1p mu Omega 2) =ᵐ[mu.restrict Omega]
      (U : Set (EuclideanSpace ℝ ι)).indicator (jetField (v : W1p mu U 2)) := by
    filter_upwards [coeFn_extendByZeroLpₗᵢ ℝ hUm hUO (W1p.value (v : W1p mu U 2)),
      coeFn_extendByZeroLpₗᵢ ℝ hUm hUO (W1p.gradient (v : W1p mu U 2))] with x hx hy
    rw [jetField_apply, W1p0.value_extendByZeroL, W1p0.gradient_extendByZeroL, hx, hy]
    by_cases hxU : x ∈ (U : Set (EuclideanSpace ℝ ι))
    · rw [indicator_of_mem hxU, indicator_of_mem hxU, indicator_of_mem hxU, jetField_apply]
    · rw [indicator_of_notMem hxU, indicator_of_notMem hxU, indicator_of_notMem hxU]
      rfl
  -- On `U`, the jet field of the restriction is that of `u`.
  have hjetU : jetField (W1p.restrictL hU u) =ᵐ[mu.restrict U] jetField u := by
    filter_upwards [W1p.value_restrictL_ae hU u, W1p.gradient_restrictL_ae hU u] with x hx hy
    rw [jetField_apply, jetField_apply, hx, hy]
  rw [energyFormH1_def, energyFormH1_def]
  calc ∫ x in U, energyIntegrand (a x) (b x) (c x) (jetField (W1p.restrictL hU u) x)
          (jetField (v : W1p mu U 2) x) ∂mu
      = ∫ x in U, energyIntegrand (a x) (b x) (c x) (jetField u x)
          (jetField (v : W1p mu U 2) x) ∂mu :=
        integral_congr_ae (by filter_upwards [hjetU] with x hx; rw [hx])
    _ = ∫ x in Omega, (U : Set (EuclideanSpace ℝ ι)).indicator (fun x => energyIntegrand (a x)
          (b x) (c x) (jetField u x) (jetField (v : W1p mu U 2) x)) x ∂mu := by
        rw [integral_indicator hUm, Measure.restrict_restrict hUm, inter_eq_left.2 hUO]
    _ = ∫ x in Omega, energyIntegrand (a x) (b x) (c x) (jetField u x)
          (jetField (W1p0.extendByZeroL hU v : W1p mu Omega 2) x) ∂mu := by
        refine integral_congr_ae ?_
        filter_upwards [hjet] with x hx
        by_cases hxU : x ∈ (U : Set (EuclideanSpace ℝ ι))
        · rw [hx, indicator_of_mem hxU, indicator_of_mem hxU]
        · rw [hx, indicator_of_notMem hxU, indicator_of_notMem hxU, map_zero]

/-- **Weak subsolutions restrict to weak subsolutions.** If `u ∈ H¹(Ω)` satisfies `a(u, v) ≤ 0`
for every nonnegative `v ∈ H¹₀(Ω)`, then for every open `U ⊆ Ω` its restriction `u|_U` satisfies
`a(u|_U, v) ≤ 0` for every nonnegative `v ∈ H¹₀(U)`. -/
theorem energyFormH1_restrictL_nonpos {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ} (hU : U ≤ Omega)
    {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a b c u (v : W1p mu Omega 2) ≤ 0)
    (v : W1p0 mu U 2) (hv : ∀ᵐ x ∂mu.restrict U, 0 ≤ W1p.value (v : W1p mu U 2) x) :
    energyFormH1 a b c (W1p.restrictL hU u) (v : W1p mu U 2) ≤ 0 := by
  have hUm := U.isOpen.measurableSet
  rw [energyFormH1_restrictL]
  refine hu _ ?_
  rw [W1p0.value_extendByZeroL]
  filter_upwards [coeFn_extendByZeroLpₗᵢ ℝ hUm (SetLike.coe_subset_coe.mpr hU)
      (W1p.value (v : W1p mu U 2)),
    ae_restrict_of_ae ((ae_restrict_iff' hUm).1 hv)] with x hx hxv
  rw [hx]
  by_cases hxU : x ∈ (U : Set (EuclideanSpace ℝ ι))
  · rw [indicator_of_mem hxU]
    exact hxv hxU
  · rw [indicator_of_notMem hxU]

/-- **Weak supersolutions restrict to weak supersolutions.** If `u ∈ H¹(Ω)` satisfies
`a(u, v) ≥ 0` for every nonnegative `v ∈ H¹₀(Ω)`, then for every open `U ⊆ Ω` its restriction
`u|_U` satisfies `a(u|_U, v) ≥ 0` for every nonnegative `v ∈ H¹₀(U)`. -/
theorem energyFormH1_restrictL_nonneg {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ} (hU : U ≤ Omega)
    {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        0 ≤ energyFormH1 a b c u (v : W1p mu Omega 2))
    (v : W1p0 mu U 2) (hv : ∀ᵐ x ∂mu.restrict U, 0 ≤ W1p.value (v : W1p mu U 2) x) :
    0 ≤ energyFormH1 a b c (W1p.restrictL hU u) (v : W1p mu U 2) := by
  have hneg := energyFormH1_restrictL_nonpos hU (u := (-1 : ℝ) • u)
    (fun v hv => by rw [energyFormH1_smul_left]; linarith [hu v hv]) v hv
  rw [map_smul, energyFormH1_smul_left] at hneg
  linarith

/-- **Shifted weak subsolutions.** If `u ∈ H¹(Ω)` satisfies `a(u, v) ≤ 0` for every nonnegative
`v ∈ H¹₀(Ω)`, for an energy form with no mass term, then for every open `U ⊆ Ω` of finite measure
and every constant `δ`, the shifted restriction `u|_U + δ ∈ H¹(U)` satisfies `a(u|_U + δ, v) ≤ 0`
for every nonnegative `v ∈ H¹₀(U)`. -/
theorem energyFormH1_restrictL_add_const_nonpos {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (hU : U ≤ Omega)
    [IsFiniteMeasure (mu.restrict U)] {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a b 0 u (v : W1p mu Omega 2) ≤ 0)
    (δ : ℝ) (v : W1p0 mu U 2) (hv : ∀ᵐ x ∂mu.restrict U, 0 ≤ W1p.value (v : W1p mu U 2) x) :
    energyFormH1 a b 0 (W1p.restrictL hU u + W1p.const δ) (v : W1p mu U 2) ≤ 0 := by
  rw [energyFormH1_add_const_left]
  exact energyFormH1_restrictL_nonpos hU hu v hv

/-- **Shifted weak supersolutions.** If `u ∈ H¹(Ω)` satisfies `a(u, v) ≥ 0` for every nonnegative
`v ∈ H¹₀(Ω)`, for an energy form with no mass term, then for every open `U ⊆ Ω` of finite measure
and every constant `δ`, the shifted restriction `u|_U + δ ∈ H¹(U)` satisfies `a(u|_U + δ, v) ≥ 0`
for every nonnegative `v ∈ H¹₀(U)`. -/
theorem energyFormH1_restrictL_add_const_nonneg {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (hU : U ≤ Omega)
    [IsFiniteMeasure (mu.restrict U)] {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        0 ≤ energyFormH1 a b 0 u (v : W1p mu Omega 2))
    (δ : ℝ) (v : W1p0 mu U 2) (hv : ∀ᵐ x ∂mu.restrict U, 0 ≤ W1p.value (v : W1p mu U 2) x) :
    0 ≤ energyFormH1 a b 0 (W1p.restrictL hU u + W1p.const δ) (v : W1p mu U 2) := by
  rw [energyFormH1_add_const_left]
  exact energyFormH1_restrictL_nonneg hU hu v hv

/-- **Weak solutions restrict to weak solutions.** If `u ∈ H¹(Ω)` satisfies
`a(u, v) = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`, then for every open `U ⊆ Ω` its restriction `u|_U`
satisfies `a(u|_U, v) = ∫_U f v` for every `v ∈ H¹₀(U)`. -/
theorem energyFormH1_restrictL_eq_setIntegral {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ} (hU : U ≤ Omega)
    {u : W1p mu Omega 2} {f : EuclideanSpace ℝ ι → ℝ}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    (v : W1p0 mu U 2) :
    energyFormH1 a b c (W1p.restrictL hU u) (v : W1p mu U 2) =
      ∫ x in U, f x * W1p.value (v : W1p mu U 2) x ∂mu := by
  have hUm := U.isOpen.measurableSet
  have hUO : (U : Set (EuclideanSpace ℝ ι)) ⊆ Omega := SetLike.coe_subset_coe.mpr hU
  rw [energyFormH1_restrictL, hu, W1p0.value_extendByZeroL]
  calc ∫ x in Omega, f x * extendByZeroLpₗᵢ ℝ mu hUm hUO (W1p.value (v : W1p mu U 2)) x ∂mu
      = ∫ x in Omega, (U : Set (EuclideanSpace ℝ ι)).indicator
          (fun x => f x * W1p.value (v : W1p mu U 2) x) x ∂mu := by
        refine integral_congr_ae ?_
        filter_upwards [coeFn_extendByZeroLpₗᵢ ℝ hUm hUO (W1p.value (v : W1p mu U 2))] with x hx
        rw [hx]
        by_cases hxU : x ∈ (U : Set (EuclideanSpace ℝ ι))
        · rw [indicator_of_mem hxU, indicator_of_mem hxU]
        · rw [indicator_of_notMem hxU, indicator_of_notMem hxU, mul_zero]
    _ = ∫ x in U, f x * W1p.value (v : W1p mu U 2) x ∂mu := by
        rw [integral_indicator hUm, Measure.restrict_restrict hUm, inter_eq_left.2 hUO]

section Transfer

open InnerProductSpace
open scoped Distributions Gradient InnerProductSpace

/-- Subtracting a constant `c` from a square-integrable field `G` on `B` does not change its
pairing with gradients of test functions on `B`. -/
theorem inner_toLp_gradient_ofTestFunctionₗ {B : Opens (EuclideanSpace ℝ ι)}
    {G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι}
    (hGc : MemLp (fun x => G x - c) 2 (mu.restrict B)) (φ : 𝓓(B, ℝ)) :
    ⟪hGc.toLp, W1p.gradient (W1p.ofTestFunctionₗ mu B 2 φ)⟫_ℝ =
      ∫ x in B, ⟪G x, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ ∂mu := by
  -- The constant `c` integrates to zero against `∇φ`.
  have hpt : ∀ x, ⟪c, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ = lineDeriv ℝ (φ : _ → ℝ) x c :=
    fun x => by
      rw [real_inner_comm, gradient, InnerProductSpace.toDual_symm_apply,
        (φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv]
  have hcint : IntegrableOn (fun x => ⟪c, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ) B mu := by
    simpa [hpt] using (integrable_lineDeriv_smul_of_locallyIntegrableOn
      (locallyIntegrableOn_const (1 : ℝ) (μ := mu) (s := B)) φ c).integrableOn
  have hc : ∫ x in B, ⟪c, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ ∂mu = 0 := by
    rw [φ.setIntegral_inner_gradient_eq_integral_inner_gradient _ φ.tsupport_subset]
    simpa only [hpt] using TestFunction.integral_lineDeriv_eq_zero (μ := mu) φ c
  have hGint : IntegrableOn (fun x => ⟪G x - c, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ) B mu := by
    refine (L2.integrable_inner hGc.toLp
      (gradientTestFunctionLp (mu := mu) (Omega := B) 2 φ)).congr ?_
    filter_upwards [hGc.coeFn_toLp,
      gradientTestFunctionLp_apply_ae (mu := mu) (Omega := B) 2 φ] with x hx hφx
    rw [hx, hφx]
  rw [L2.inner_def]
  calc ∫ x in B, ⟪MemLp.toLp _ hGc x, W1p.gradient (W1p.ofTestFunctionₗ mu B 2 φ) x⟫_ℝ ∂mu
      = ∫ x in B, (⟪G x, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ -
          ⟪c, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ) ∂mu := by
        refine integral_congr_ae ?_
        filter_upwards [hGc.coeFn_toLp,
          gradientTestFunctionLp_apply_ae (mu := mu) (Omega := B) 2 φ] with x hx hφx
        rw [W1p.gradient_ofTestFunctionₗ, hx, hφx, inner_sub_left]
    _ = ∫ x in B, ⟪G x, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ ∂mu := by
        rw [integral_sub ((hGint.add hcint).congr (ae_of_all _ fun x => by simp)) hcint, hc,
          sub_zero]

/-- The weak equation `-∂ⱼ(aⁱʲ ∂ᵢu) = -div G` on `Ω`, tested against test functions, holds on
every open `B ⊆ Ω` against all of `H¹₀(B)` once `G` is replaced by `G - c` for a constant `c`,
provided `G - c` is square integrable on `B` and the coefficients are essentially bounded on `B`:
constants have zero divergence. -/
theorem forall_energyFormH1_restrictL_eq_inner {B : Opens (EuclideanSpace ℝ ι)}
    (hB : B ≤ Omega) {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (ha : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict B)) {u : W1p mu Omega 2}
    {G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (hu : ∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ mu Omega 2 φ) =
      ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ ∂mu)
    {c : EuclideanSpace ℝ ι} (hGc : MemLp (fun x => G x - c) 2 (mu.restrict B))
    (v : W1p0 mu B 2) :
    energyFormH1 a 0 0 (W1p.restrictL hB u) (v : W1p mu B 2) =
      ⟪hGc.toLp, W1p.gradient (v : W1p mu B 2)⟫_ℝ := by
  set L : W1p mu B 2 →L[ℝ] ℝ :=
    energyFormH1L ha (W1p.restrictL hB u) - (innerSL ℝ hGc.toLp).comp W1p.gradientL
  have hL : ∀ w, L w = energyFormH1 a 0 0 (W1p.restrictL hB u) w -
      ⟪hGc.toLp, W1p.gradient w⟫_ℝ := fun w => by
    simp only [L, sub_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, W1p.gradientL_apply, energyFormH1L_apply, Pi.zero_def]
  -- The functional `L` is continuous, so it suffices that it vanishes on test functions.
  suffices hzero : (w1p0Submodule mu B 2 : Set (W1p mu B 2)) ⊆ {w | L w = 0} by
    have := hzero v.2
    simp only [mem_ofPred_eq, hL] at this
    linarith
  refine w1p0Submodule_subset_of_isClosed (isClosed_eq L.continuous continuous_const) fun φ => ?_
  simp only [mem_ofPred_eq, hL, inner_toLp_gradient_ofTestFunctionₗ hGc φ, sub_eq_zero]
  -- The zero extension of `φ` from `B` to `Ω` is `φ` regarded as a test function on `Ω`, so
  -- `a(u|_B, φ) = a(u, φ) = ∫_Ω ⟪G, ∇φ⟫ = ∫_B ⟪G, ∇φ⟫`.
  have hext : ((W1p0.extendByZeroL hB
      (⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩ : W1p0 mu B 2) : W1p0 mu Omega 2) :
      W1p mu Omega 2) = W1p.ofTestFunctionₗ mu Omega 2 (TestFunction.monoCLM ℝ φ) := by
    apply Subtype.ext
    rw [W1p0.coe_extendByZeroL]
    exact Sobolev1JetLp.extendByZeroₗᵢ_ofTestFunctionₗ hB φ
  have hφ := energyFormH1_restrictL a 0 0 hB u ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩
  have hmono : ((TestFunction.monoCLM ℝ φ : 𝓓(Omega, ℝ)) : EuclideanSpace ℝ ι → ℝ) = φ := by
    rw [TestFunction.monoCLM_apply]
    simp [hB]
  rw [hext, hu, hmono] at hφ
  rw [hφ, φ.setIntegral_inner_gradient_eq_integral_inner_gradient G (φ.tsupport_subset.trans hB),
    φ.setIntegral_inner_gradient_eq_integral_inner_gradient G φ.tsupport_subset]

end Transfer

end PDE

end TauCeti
