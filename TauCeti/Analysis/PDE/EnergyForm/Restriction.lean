/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Sobolev
public import TauCeti.Analysis.Sobolev.W1p.Extension
public import TauCeti.Analysis.Sobolev.W1p.Restriction
import TauCeti.Analysis.Distribution.TestFunction.Integral
import TauCeti.Analysis.PDE.DirichletProblem

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
* `TauCeti.PDE.energyFormH1_extendByZeroL`: `a(u₀, v₀) = a(u, v)` for `u, v ∈ H¹₀(U)` with zero
  extensions `u₀, v₀ ∈ H¹₀(Ω)`.
* `TauCeti.PDE.isCoercive_energyFormH1L0_of_domain_le`: coercivity passes to smaller domains.
* `TauCeti.PDE.energyFormH1_restrictL_nonpos`: weak subsolutions restrict to weak subsolutions.
* `TauCeti.PDE.energyFormH1_restrictL_nonneg`: weak supersolutions restrict to weak
  supersolutions.
* `TauCeti.PDE.energyFormH1_restrictL_add_const_nonpos`,
  `TauCeti.PDE.energyFormH1_restrictL_add_const_nonneg`: the restriction of a weak subsolution
  or supersolution with no mass term, shifted by a constant, is again one.
* `TauCeti.PDE.energyFormH1_restrictL_eq_setIntegral`: weak solutions restrict to weak solutions.
* `TauCeti.PDE.exists_forcing_restrictL_of_eqOn`: for `b, c ∈ L∞(Ω)`, the restriction of a weak
  solution to a set where the principal coefficient is replaced by an essentially bounded one
  solves the equation without lower-order terms, with some `L²` forcing.
* `TauCeti.PDE.energyFormH1_restrictL_eq_neg_setIntegral_inner`: weak solutions of `L u = div F`
  restrict to weak solutions of the same equation.
* `TauCeti.PDE.energyFormH1_restrictL_eq_of_forall_testFunction`: if a continuous functional
  `ℓ` on `H¹(B)` agrees with `a(u, ·)` on test functions on `B ⊆ Ω`, then `a(u|_B, v) = ℓ(v)`
  for every `v ∈ H¹₀(B)`.
* `TauCeti.PDE.forall_energyFormH1_restrictL_eq_inner`: if `u` solves `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G`
  weakly on `Ω`, tested against test functions, then on every open `B ⊆ Ω` on which `a` is
  essentially bounded it satisfies `a(u, v) = ⟪G - c, ∇v⟫_{L²(B)}` for every `v ∈ H¹₀(B)` and
  every constant `c` with `G - c ∈ L²(B)`, since constants have zero divergence. This is the
  hypothesis of the energy estimate for the replacement on a ball.
* `TauCeti.PDE.forall_energyFormH1_restrictL_eq_setIntegral`: if `u` solves `-∂ᵢ(aⁱʲ ∂ⱼu) = f`
  weakly on `Ω`, tested against test functions, then on every open `B ⊆ Ω` on which `a` is
  essentially bounded and `f` is square integrable it satisfies `a(u, v) = ∫_B f v` for every
  `v ∈ H¹₀(B)`, with no integrability of `f` on all of `Ω`.
* `TauCeti.PDE.inner_toLp_gradient_ofTestFunctionₗ`: the test-function case,
  `⟪G - c, ∇φ⟫_{L²(B)} = ∫_B ⟨G, ∇φ⟩`, in any finite-dimensional real inner product space.
* `TauCeti.PDE.inner_gradient_restrictL_eq_inner_toLp`: the same restriction statement for the
  Laplacian, `⟪∇(u|_B), ∇v⟫_{L²(B)} = ⟪G - c, ∇v⟫_{L²(B)}` for `v ∈ H¹₀(B)`, in any
  finite-dimensional real inner product space.
* `TauCeti.PDE.forall_energyFormH1_restrictL_top_eq_setIntegral`: if `v ∈ H¹(ℝⁿ)` solves `Δv = G`
  weakly, tested against compactly supported smooth functions, and `G = -F` on an open `Ω` with
  `F ∈ L²(Ω)`, then `v|_Ω` solves `-Δv = F` weakly on `Ω`, tested against `H¹₀(Ω)`.
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

/-- **The energy form of zero extensions.** For open sets `U ⊆ Ω` and `u, v ∈ H¹₀(U)`, the energy
form on `Ω` of the zero-extensions of `u` and `v` equals the energy form of `u` and `v` on `U`. -/
theorem energyFormH1_extendByZeroL (a : EuclideanSpace ℝ ι → Matrix ι ι ℝ)
    (b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (c : EuclideanSpace ℝ ι → ℝ) (hU : U ≤ Omega)
    (u v : W1p0 mu U 2) :
    energyFormH1 a b c (W1p0.extendByZeroL hU u : W1p mu Omega 2)
        (W1p0.extendByZeroL hU v : W1p mu Omega 2) =
      energyFormH1 a b c (u : W1p mu U 2) (v : W1p mu U 2) := by
  have h := energyFormH1_restrictL a b c hU (W1p0.extendByZeroL hU u : W1p mu Omega 2) v
  rw [W1p0.restrictL_extendByZeroL] at h
  exact h.symm

/-- **Coercivity passes to smaller domains.** Zero extension preserves both the Sobolev norm
and the energy, so the same coercivity constant works on every smaller open set. -/
theorem isCoercive_energyFormH1L0_of_domain_le {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
    (hU : U ≤ Omega)
    (hcoeff : MemLp (fun x ↦ energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) :
    IsCoercive (energyFormH1L0
      (hcoeff.mono_measure (Measure.restrict_mono (SetLike.coe_subset_coe.mpr hU) le_rfl))) := by
  obtain ⟨C, hC, hbound⟩ := hcoercive
  refine ⟨C, hC, fun u ↦ ?_⟩
  simpa only [W1p0.norm_extendByZeroL, energyFormH1L0_apply, energyFormH1_extendByZeroL]
    using hbound (W1p0.extendByZeroL hU u)

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

/-- If `a'` agrees with `a` on an open `U ≤ Ω`, is essentially bounded on `U`, `b, c ∈ L∞(Ω)`, and
`u ∈ H¹(Ω)` solves the equation with coefficients `a, b, c` and right-hand side `f`, then the
restriction of `u` to `U` solves the equation with principal part `a'` and no lower-order terms,
with some forcing `g ∈ L²(U)`. -/
theorem exists_forcing_restrictL_of_eqOn {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {a' : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}
    (hU : U ≤ Omega) (haa' : EqOn a' a U)
    (ha' : MemLp (fun x => energyIntegrand (a' x) 0 0) ⊤ (mu.restrict U))
    (hb : MemLp b ⊤ (mu.restrict Omega)) (hc : MemLp c ⊤ (mu.restrict Omega))
    {f : Lp ℝ 2 (mu.restrict Omega)} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) :
    ∃ g : Lp ℝ 2 (mu.restrict U), ∀ v : W1p0 mu U 2,
      energyFormH1 a' 0 0 (W1p.restrictL hU u) (v : W1p mu U 2) =
        ∫ x in U, g x * W1p.value (v : W1p mu U 2) x ∂mu := by
  have hle : mu.restrict U ≤ mu.restrict Omega :=
    Measure.restrict_mono (SetLike.coe_subset_coe.mpr hU) le_rfl
  have hfU : MemLp f 2 (mu.restrict U) := (Lp.memLp f).mono_measure hle
  have hu₁ : ∀ v : W1p0 mu U 2, energyFormH1 a' b c (W1p.restrictL hU u) (v : W1p mu U 2) =
      ∫ x in U, hfU.toLp f x * W1p.value (v : W1p mu U 2) x ∂mu := by
    intro v
    have h := energyFormH1_restrictL_eq_setIntegral hU hu v
    rw [energyFormH1_def] at h ⊢
    rw [setIntegral_congr_fun U.isOpen.measurableSet fun x hx => by rw [haa' hx], h]
    refine integral_congr_ae ?_
    filter_upwards [hfU.coeFn_toLp] with x hx
    rw [hx]
  exact exists_forcing_energyFormH1_principal_eq ha'
    (hb.mono_measure hle) (hc.mono_measure hle) hu₁

open scoped InnerProductSpace in
/-- **Weak solutions with a datum in divergence form restrict to weak solutions.** If
`u ∈ H¹(Ω)` satisfies `a(u, v) = -∫_Ω ⟪F, ∇v⟫` for every `v ∈ H¹₀(Ω)`, that is, `u` solves
`L u = div F` weakly, then for every open `U ⊆ Ω` its restriction `u|_U` satisfies
`a(u|_U, v) = -∫_U ⟪F, ∇v⟫` for every `v ∈ H¹₀(U)`. -/
theorem energyFormH1_restrictL_eq_neg_setIntegral_inner {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ} (hU : U ≤ Omega)
    {u : W1p mu Omega 2} {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a b c u (v : W1p mu Omega 2) =
      -∫ x in Omega, ⟪F x, W1p.gradient (v : W1p mu Omega 2) x⟫_ℝ ∂mu)
    (v : W1p0 mu U 2) :
    energyFormH1 a b c (W1p.restrictL hU u) (v : W1p mu U 2) =
      -∫ x in U, ⟪F x, W1p.gradient (v : W1p mu U 2) x⟫_ℝ ∂mu := by
  have hUm := U.isOpen.measurableSet
  have hUO : (U : Set (EuclideanSpace ℝ ι)) ⊆ Omega := SetLike.coe_subset_coe.mpr hU
  rw [energyFormH1_restrictL, hu, W1p0.gradient_extendByZeroL, neg_inj]
  calc ∫ x in Omega, ⟪F x, extendByZeroLpₗᵢ ℝ mu hUm hUO (W1p.gradient (v : W1p mu U 2)) x⟫_ℝ ∂mu
      = ∫ x in Omega, (U : Set (EuclideanSpace ℝ ι)).indicator
          (fun x => ⟪F x, W1p.gradient (v : W1p mu U 2) x⟫_ℝ) x ∂mu := by
        refine integral_congr_ae ?_
        filter_upwards [coeFn_extendByZeroLpₗᵢ ℝ hUm hUO (W1p.gradient (v : W1p mu U 2))]
          with x hx
        rw [hx]
        by_cases hxU : x ∈ (U : Set (EuclideanSpace ℝ ι))
        · rw [indicator_of_mem hxU, indicator_of_mem hxU]
        · rw [indicator_of_notMem hxU, indicator_of_notMem hxU, inner_zero_right]
    _ = ∫ x in U, ⟪F x, W1p.gradient (v : W1p mu U 2) x⟫_ℝ ∂mu := by
        rw [integral_indicator hUm, Measure.restrict_restrict hUm, inter_eq_left.2 hUO]

section Transfer

open InnerProductSpace
open scoped ContDiff Distributions Gradient InnerProductSpace

/-- Subtracting a constant `c` from a square-integrable field `G` on `B` does not change its
pairing with gradients of test functions on `B`. -/
theorem inner_toLp_gradient_ofTestFunctionₗ {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    {mu : Measure F} [mu.IsAddHaarMeasure] {B : Opens F} {G : F → F} {c : F}
    (hGc : MemLp (fun x => G x - c) 2 (mu.restrict B)) (φ : 𝓓(B, ℝ)) :
    ⟪hGc.toLp, W1p.gradient (W1p.ofTestFunctionₗ mu B 2 φ)⟫_ℝ =
      ∫ x in B, ⟪G x, ∇ (φ : F → ℝ) x⟫_ℝ ∂mu := by
  -- The constant `c` integrates to zero against `∇φ`.
  have hpt : ∀ x, ⟪c, ∇ (φ : F → ℝ) x⟫_ℝ = lineDeriv ℝ (φ : _ → ℝ) x c :=
    fun x => by
      rw [real_inner_comm, gradient, InnerProductSpace.toDual_symm_apply,
        (φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv]
  have hcint : IntegrableOn (fun x => ⟪c, ∇ (φ : F → ℝ) x⟫_ℝ) B mu := by
    simpa [hpt] using (integrable_lineDeriv_smul_of_locallyIntegrableOn
      (locallyIntegrableOn_const (1 : ℝ) (μ := mu) (s := B)) φ c).integrableOn
  have hc : ∫ x in B, ⟪c, ∇ (φ : F → ℝ) x⟫_ℝ ∂mu = 0 := by
    rw [φ.setIntegral_inner_gradient_eq_integral_inner_gradient _ φ.tsupport_subset]
    simpa only [hpt] using TestFunction.integral_lineDeriv_eq_zero (μ := mu) φ c
  have hGint : IntegrableOn (fun x => ⟪G x - c, ∇ (φ : F → ℝ) x⟫_ℝ) B mu := by
    refine (L2.integrable_inner hGc.toLp
      (gradientTestFunctionLp (mu := mu) (Omega := B) 2 φ)).congr ?_
    filter_upwards [hGc.coeFn_toLp,
      gradientTestFunctionLp_apply_ae (mu := mu) (Omega := B) 2 φ] with x hx hφx
    rw [hx, hφx]
  rw [L2.inner_def]
  calc ∫ x in B, ⟪MemLp.toLp _ hGc x, W1p.gradient (W1p.ofTestFunctionₗ mu B 2 φ) x⟫_ℝ ∂mu
      = ∫ x in B, (⟪G x, ∇ (φ : F → ℝ) x⟫_ℝ -
          ⟪c, ∇ (φ : F → ℝ) x⟫_ℝ) ∂mu := by
        refine integral_congr_ae ?_
        filter_upwards [hGc.coeFn_toLp,
          gradientTestFunctionLp_apply_ae (mu := mu) (Omega := B) 2 φ] with x hx hφx
        rw [W1p.gradient_ofTestFunctionₗ, hx, hφx, inner_sub_left]
    _ = ∫ x in B, ⟪G x, ∇ (φ : F → ℝ) x⟫_ℝ ∂mu := by
        rw [integral_sub ((hGint.add hcint).congr (ae_of_all _ fun x => by simp)) hcint, hc,
          sub_zero]

/-- **Weak solutions of `-Δu = -div G` restrict to smaller domains.** Let `B ⊆ Ω` be open sets
of a finite-dimensional real inner product space, and let `u ∈ H¹(Ω)` solve `-Δu = -div G`
weakly on `Ω`, tested against test functions: `∫_Ω ⟪∇u, ∇φ⟫ = ∫_Ω ⟪G, ∇φ⟫`. If `G - c` is
square integrable on `B` for a constant `c`, then
`⟪∇(u|_B), ∇v⟫_{L²(B)} = ⟪G - c, ∇v⟫_{L²(B)}` for every `v ∈ H¹₀(B)`: constants have zero
divergence. This is the Laplacian case of `forall_energyFormH1_restrictL_eq_inner`, without
coordinates. -/
theorem inner_gradient_restrictL_eq_inner_toLp {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    {mu : Measure F} [mu.IsAddHaarMeasure] {Omega B : Opens F} (hB : B ≤ Omega)
    {u : W1p mu Omega 2} {G : F → F}
    (hu : ∀ φ : 𝓓(Omega, ℝ), ∫ x in Omega, ⟪W1p.gradient u x, ∇ (φ : F → ℝ) x⟫_ℝ ∂mu =
      ∫ x in Omega, ⟪G x, ∇ (φ : F → ℝ) x⟫_ℝ ∂mu)
    {c : F} (hGc : MemLp (fun x => G x - c) 2 (mu.restrict B)) {v : W1p mu B 2}
    (hv : v ∈ w1p0Submodule mu B 2) :
    ⟪W1p.gradient (W1p.restrictL hB u), W1p.gradient v⟫_ℝ = ⟪hGc.toLp, W1p.gradient v⟫_ℝ := by
  set L : W1p mu B 2 →L[ℝ] ℝ :=
    (innerSL ℝ (W1p.gradient (W1p.restrictL hB u)) - innerSL ℝ hGc.toLp).comp W1p.gradientL
  have hL : ∀ w, L w = ⟪W1p.gradient (W1p.restrictL hB u), W1p.gradient w⟫_ℝ -
      ⟪hGc.toLp, W1p.gradient w⟫_ℝ := fun w => by
    simp [L, W1p.gradientL_apply]
  -- The functional `L` is continuous, so it suffices that it vanishes on test functions.
  suffices hzero : (w1p0Submodule mu B 2 : Set (W1p mu B 2)) ⊆ {w | L w = 0} by
    have := hzero hv
    simp only [mem_ofPred_eq, hL, sub_eq_zero] at this
    exact this
  refine w1p0Submodule_subset_of_isClosed (isClosed_eq L.continuous continuous_const) fun φ => ?_
  simp only [mem_ofPred_eq, hL, sub_eq_zero]
  rw [inner_toLp_gradient_ofTestFunctionₗ hGc φ, L2.inner_def]
  -- `⟪∇(u|_B), ∇φ⟫_{L²(B)} = ∫_Ω ⟪∇u, ∇φ⟫ = ∫_Ω ⟪G, ∇φ⟫ = ∫_B ⟪G, ∇φ⟫`.
  have hψ : ((TestFunction.monoCLM ℝ φ : 𝓓(Omega, ℝ)) : F → ℝ) = φ := by
    rw [TestFunction.monoCLM_apply]
    simp [hB]
  have h := hu (TestFunction.monoCLM ℝ φ)
  rw [hψ, φ.setIntegral_inner_gradient_eq_integral_inner_gradient _ (φ.tsupport_subset.trans hB),
    φ.setIntegral_inner_gradient_eq_integral_inner_gradient _ (φ.tsupport_subset.trans hB)] at h
  rw [φ.setIntegral_inner_gradient_eq_integral_inner_gradient G φ.tsupport_subset, ← h,
    ← φ.setIntegral_inner_gradient_eq_integral_inner_gradient _ φ.tsupport_subset]
  refine integral_congr_ae ?_
  filter_upwards [W1p.gradient_restrictL_ae hB u,
    gradientTestFunctionLp_apply_ae (mu := mu) (Omega := B) 2 φ] with x hx hφx
  rw [W1p.gradient_ofTestFunctionₗ, hx, hφx]

/-- **Weak equations restrict to smaller domains.** Let `B ⊆ Ω` be open, let the coefficients
be essentially bounded on `B`, and let `ℓ` be a continuous linear functional on `H¹(B)`. If
`a(u, ψ) = ℓ(φ)` whenever the test function `ψ` on `Ω` is a test function `φ` on `B`, then
`a(u|_B, v) = ℓ(v)` for every `v ∈ H¹₀(B)`. -/
theorem energyFormH1_restrictL_eq_of_forall_testFunction {B : Opens (EuclideanSpace ℝ ι)}
    (hB : B ≤ Omega) {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (ha : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict B)) {u : W1p mu Omega 2}
    (ℓ : W1p mu B 2 →L[ℝ] ℝ)
    (hℓ : ∀ (φ : 𝓓(B, ℝ)) (ψ : 𝓓(Omega, ℝ)), (ψ : EuclideanSpace ℝ ι → ℝ) = φ →
      energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ mu Omega 2 ψ) = ℓ (W1p.ofTestFunctionₗ mu B 2 φ))
    (v : W1p0 mu B 2) :
    energyFormH1 a 0 0 (W1p.restrictL hB u) (v : W1p mu B 2) = ℓ v := by
  set L : W1p mu B 2 →L[ℝ] ℝ := energyFormH1L ha (W1p.restrictL hB u) - ℓ
  have hL : ∀ w, L w = energyFormH1 a 0 0 (W1p.restrictL hB u) w - ℓ w := fun w => by
    simp only [L, sub_apply, energyFormH1L_apply, Pi.zero_def]
  -- The functional `L` is continuous, so it suffices that it vanishes on test functions.
  suffices hzero : (w1p0Submodule mu B 2 : Set (W1p mu B 2)) ⊆ {w | L w = 0} by
    have := hzero v.2
    simp only [mem_ofPred_eq, hL] at this
    linarith
  refine w1p0Submodule_subset_of_isClosed (isClosed_eq L.continuous continuous_const) fun φ => ?_
  simp only [mem_ofPred_eq, hL, sub_eq_zero]
  -- The zero extension of `φ` from `B` to `Ω` is `φ` regarded as a test function on `Ω`, so
  -- `a(u|_B, φ) = a(u, φ)`.
  have hext : ((W1p0.extendByZeroL hB
      (⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩ : W1p0 mu B 2) : W1p0 mu Omega 2) :
      W1p mu Omega 2) = W1p.ofTestFunctionₗ mu Omega 2 (TestFunction.monoCLM ℝ φ) := by
    apply Subtype.ext
    rw [W1p0.coe_extendByZeroL]
    exact Sobolev1JetLp.extendByZeroₗᵢ_ofTestFunctionₗ hB φ
  have hφ := energyFormH1_restrictL a 0 0 hB u ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩
  rw [hext] at hφ
  rw [hφ]
  exact hℓ φ _ (by rw [TestFunction.monoCLM_apply]; simp [hB])

/-- The weak equation `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` on `Ω`, tested against test functions, holds on
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
  refine (energyFormH1_restrictL_eq_of_forall_testFunction hB ha
    ((innerSL ℝ hGc.toLp).comp W1p.gradientL) (fun φ ψ hψ => ?_) v).trans (by
      simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, W1p.gradientL_apply])
  -- `a(u, φ) = ∫_Ω ⟪G, ∇φ⟫ = ∫_B ⟪G, ∇φ⟫`.
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, W1p.gradientL_apply,
    inner_toLp_gradient_ofTestFunctionₗ hGc φ]
  rw [hu, hψ, φ.setIntegral_inner_gradient_eq_integral_inner_gradient G
    (φ.tsupport_subset.trans hB),
    φ.setIntegral_inner_gradient_eq_integral_inner_gradient G φ.tsupport_subset]

/-- The weak equation `-∂ᵢ(aⁱʲ ∂ⱼu) = f` on `Ω`, tested against test functions, holds on every
open `B ⊆ Ω` against all of `H¹₀(B)`, provided `f` is square integrable on `B` and the
coefficients are essentially bounded on `B`. Nothing is assumed about `f` outside `B`, so this
applies to right-hand sides that are only locally integrable on `Ω`. -/
theorem forall_energyFormH1_restrictL_eq_setIntegral {B : Opens (EuclideanSpace ℝ ι)}
    (hB : B ≤ Omega) {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (ha : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (mu.restrict B)) {u : W1p mu Omega 2}
    {f : EuclideanSpace ℝ ι → ℝ}
    (hu : ∀ φ : 𝓓(Omega, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ mu Omega 2 φ) =
      ∫ x in Omega, f x * φ x ∂mu)
    (hf : MemLp f 2 (mu.restrict B)) (v : W1p0 mu B 2) :
    energyFormH1 a 0 0 (W1p.restrictL hB u) (v : W1p mu B 2) =
      ∫ x in B, f x * W1p.value (v : W1p mu B 2) x ∂mu := by
  -- On `B`, the integral against `f` is the `L²` inner product with `f`.
  have hinner (w : W1p mu B 2) :
      ⟪hf.toLp, W1p.value w⟫_ℝ = ∫ x in B, f x * W1p.value w x ∂mu := by
    rw [L2.inner_def]
    refine integral_congr_ae (hf.coeFn_toLp.mono fun x hx => ?_)
    simp [hx, RCLike.inner_apply, mul_comm]
  rw [← hinner]
  refine (energyFormH1_restrictL_eq_of_forall_testFunction hB ha
    ((innerSL ℝ hf.toLp).comp W1p.valueL) (fun φ ψ hψ => ?_) v).trans (by
      simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, W1p.valueL_apply])
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, W1p.valueL_apply, hinner]
  rw [hu, hψ]
  -- `a(u, φ) = ∫_Ω f φ = ∫_B f φ`: both integrals vanish off `tsupport φ ⊆ B`, and on `B` the
  -- value of `φ` is `φ`.
  have hsupp : ∀ x ∉ (B : Set (EuclideanSpace ℝ ι)), f x * φ x = 0 := fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport fun h => hx (φ.tsupport_subset h), mul_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => hsupp x fun h => hx (hB h),
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
  exact integral_congr_ae ((W1p.value_ofTestFunctionₗ_ae (p := 2) φ).mono fun x hx => by
    simp only [hx])

/-- **Global weak solutions of Poisson's equation restrict to weak solutions.** If `v ∈ H¹(ℝⁿ)`
solves `Δv = G` weakly, tested against compactly supported smooth functions, and `G` agrees on an
open set `Ω` with `-F` for some `F ∈ L²(Ω)`, then the restriction of `v` to `Ω` is a weak solution
of `-Δv = F` on `Ω`, tested against `H¹₀(Ω)`. -/
theorem forall_energyFormH1_restrictL_top_eq_setIntegral [DecidableEq ι] {v : W1p mu ⊤ 2}
    {G F : EuclideanSpace ℝ ι → ℝ} (hF : MemLp F 2 (mu.restrict Omega))
    (hGF : G =ᵐ[mu.restrict Omega] fun x => -F x)
    (hv : ∀ φ : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, ⟪W1p.gradient v x, ∇ φ x⟫_ℝ ∂mu) + ∫ x, G x * φ x ∂mu = 0) :
    ∀ w : W1p0 mu Omega 2, energyFormH1 (fun _ => 1) 0 0 (W1p.restrictL le_top v)
      (w : W1p mu Omega 2) = ∫ x in Omega, F x * W1p.value (w : W1p mu Omega 2) x ∂mu := by
  have hcoeff : MemLp (fun x => energyIntegrand ((fun _ => (1 : Matrix ι ι ℝ)) x)
      ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x)
      ((0 : EuclideanSpace ℝ ι → ℝ) x)) ⊤ (mu.restrict Omega) := by
    simpa using memLp_top_const (μ := mu.restrict (Omega : Set (EuclideanSpace ℝ ι)))
      (energyIntegrand (1 : Matrix ι ι ℝ) 0 0)
  intro w
  refine ((forall_energyFormH1_eq_setIntegral_iff_forall_testFunction hcoeff (hF.toLp F)
    (W1p.restrictL le_top v)).2 (fun φ => ?_) w).trans (integral_congr_ae ?_)
  · -- Both sides vanish off the support of `φ`, which lies in `Ω`.
    have hglob := hv φ φ.contDiff φ.hasCompactSupport
    have e2 : ∫ x in Omega, G x * φ x ∂mu = ∫ x, G x * φ x ∂mu :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        simp [φ.zero_on_compl hx]
    rw [← φ.setIntegral_inner_gradient_eq_integral_inner_gradient (W1p.gradient v)
      φ.tsupport_subset, ← e2] at hglob
    rw [energyFormH1_zero_zero_eq_setIntegral]
    have h1 : ∫ x in Omega, (matrixBilinearForm ((fun _ => (1 : Matrix ι ι ℝ)) x))
        (W1p.gradient (W1p.ofTestFunctionₗ mu Omega 2 φ) x)
        (W1p.gradient (W1p.restrictL (show Omega ≤ ⊤ from le_top) v) x) ∂mu =
        ∫ x in Omega, ⟪W1p.gradient v x, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ ∂mu := by
      refine integral_congr_ae ?_
      filter_upwards [gradientTestFunctionLp_apply_ae (mu := mu) 2 φ,
        W1p.gradient_restrictL_ae (show Omega ≤ ⊤ from le_top) v] with x hx hx'
      rw [W1p.gradient_ofTestFunctionₗ, hx, hx', matrixBilinearForm_one_apply,
        real_inner_comm]
      exact ((EuclideanSpace.inner_eq_star_dotProduct _ _).trans (dotProduct_comm _ _)).symm
    have h2 : ∫ x in Omega, G x * φ x ∂mu = -∫ x in Omega, (hF.toLp F) x * φ x ∂mu := by
      rw [← integral_neg]
      refine integral_congr_ae ?_
      filter_upwards [hGF, hF.coeFn_toLp] with x hx hx'
      rw [hx, hx']
      ring
    rw [h1]
    linarith
  · filter_upwards [hF.coeFn_toLp] with x hx
    rw [hx]

end Transfer

end PDE

end TauCeti
