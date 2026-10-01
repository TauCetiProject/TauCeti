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
# Restricting the energy form to a subdomain

Let `U ⊆ Ω` be open sets, `u ∈ H¹(Ω)` and `v ∈ H¹₀(U)`. Testing the restriction of `u` to `U`
against `v` in the energy form of `U` gives the same number as testing `u` against the extension
of `v` by zero in the energy form of `Ω`: the extension and its weak gradient vanish off `U`, so
the integrand of the larger form is supported in `U`.

Consequently weak subsolutions restrict: if `a(u, v) ≤ 0` for every nonnegative `v ∈ H¹₀(Ω)`,
the same holds for the restriction of `u` to `U` and every nonnegative `v ∈ H¹₀(U)`. Interior
regularity arguments use this to pass from a domain `Ω` to a ball inside it, where the ball's
finite measure puts constants, and hence shifted functions `u - k`, in `H¹`.

## Main declarations

* `TauCeti.PDE.energyFormH1_restrictL_extendByZeroL`: the restriction identity.
* `TauCeti.PDE.energyFormH1_restrictL_nonpos`: weak subsolutions restrict to subdomains.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open MeasureTheory Set TopologicalSpace

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega U : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι → ℝ}

/-- **The energy form of a restriction.** For open `U ⊆ Ω`, `u ∈ H¹(Ω)` and `v ∈ H¹₀(U)`, the
energy form on `U` of the restriction of `u` against `v` is the energy form on `Ω` of `u` against
the extension of `v` by zero. No hypothesis on the coefficients is needed. -/
theorem energyFormH1_restrictL_extendByZeroL (hU : U ≤ Omega) (u : W1p mu Omega 2)
    (v : W1p0 mu U 2) :
    energyFormH1 a b c (W1p.restrictL hU u) (v : W1p mu U 2) =
      energyFormH1 a b c u (W1p0.extendByZeroL hU v : W1p mu Omega 2) := by
  have hUm : MeasurableSet (U : Set (EuclideanSpace ℝ ι)) := U.isOpen.measurableSet
  have hsub : (U : Set (EuclideanSpace ℝ ι)) ⊆ Omega := SetLike.coe_subset_coe.mpr hU
  -- The jet of the extension is the extension of the jet.
  have hext : ∀ᵐ x ∂mu.restrict Omega,
      jetField (W1p0.extendByZeroL hU v : W1p mu Omega 2) x =
        (U : Set (EuclideanSpace ℝ ι)).indicator (jetField (v : W1p mu U 2)) x := by
    filter_upwards [coeFn_extendByZeroLpₗᵢ ℝ hUm hsub (W1p.value (v : W1p mu U 2)),
      coeFn_extendByZeroLpₗᵢ ℝ hUm hsub (W1p.gradient (v : W1p mu U 2))] with x h1 h2
    rw [jetField_apply, W1p0.value_extendByZeroL, W1p0.gradient_extendByZeroL, h1, h2]
    by_cases hx : x ∈ (U : Set (EuclideanSpace ℝ ι))
    · simp [indicator_of_mem hx]
    · simp [indicator_of_notMem hx]
  rw [energyFormH1_def, energyFormH1_def]
  calc ∫ x in U, energyIntegrand (a x) (b x) (c x) (jetField (W1p.restrictL hU u) x)
          (jetField (v : W1p mu U 2) x) ∂mu
      = ∫ x in U, energyIntegrand (a x) (b x) (c x) (jetField u x)
          (jetField (v : W1p mu U 2) x) ∂mu := by
        refine integral_congr_ae ?_
        filter_upwards [W1p.value_restrictL_ae hU u, W1p.gradient_restrictL_ae hU u]
          with x h1 h2
        simp only [jetField_apply, h1, h2]
    _ = ∫ x in Omega, (U : Set (EuclideanSpace ℝ ι)).indicator (fun x =>
          energyIntegrand (a x) (b x) (c x) (jetField u x) (jetField (v : W1p mu U 2) x)) x
            ∂mu := by
        rw [setIntegral_indicator hUm, inter_eq_right.2 hsub]
    _ = ∫ x in Omega, energyIntegrand (a x) (b x) (c x) (jetField u x)
          (jetField (W1p0.extendByZeroL hU v : W1p mu Omega 2) x) ∂mu := by
        refine integral_congr_ae ?_
        filter_upwards [hext] with x hx
        rw [hx]
        by_cases hxU : x ∈ (U : Set (EuclideanSpace ℝ ι))
        · rw [indicator_of_mem hxU, indicator_of_mem hxU]
        · rw [indicator_of_notMem hxU, indicator_of_notMem hxU, map_zero]

/-- **Weak subsolutions restrict to subdomains.** If `u ∈ H¹(Ω)` satisfies `a(u, v) ≤ 0` for every
nonnegative `v ∈ H¹₀(Ω)`, then for every open `U ⊆ Ω` the restriction of `u` to `U` satisfies
`a(u|_U, v) ≤ 0` for every nonnegative `v ∈ H¹₀(U)`. -/
theorem energyFormH1_restrictL_nonpos (hU : U ≤ Omega) {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a b c u (v : W1p mu Omega 2) ≤ 0)
    (v : W1p0 mu U 2) (hv : ∀ᵐ x ∂mu.restrict U, 0 ≤ W1p.value (v : W1p mu U 2) x) :
    energyFormH1 a b c (W1p.restrictL hU u) (v : W1p mu U 2) ≤ 0 := by
  have hUm : MeasurableSet (U : Set (EuclideanSpace ℝ ι)) := U.isOpen.measurableSet
  have hsub : (U : Set (EuclideanSpace ℝ ι)) ⊆ Omega := SetLike.coe_subset_coe.mpr hU
  rw [energyFormH1_restrictL_extendByZeroL]
  refine hu _ ?_
  rw [W1p0.value_extendByZeroL]
  filter_upwards [coeFn_extendByZeroLpₗᵢ ℝ hUm hsub (W1p.value (v : W1p mu U 2)),
    ae_restrict_of_ae ((ae_restrict_iff' hUm).1 hv)] with x h1 h2
  rw [h1]
  exact indicator_nonneg (fun y hy => h2 hy) x

end PDE

end TauCeti
