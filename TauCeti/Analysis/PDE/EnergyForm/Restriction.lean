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
subsolution on `Ω` restricts to a weak subsolution on `U`, and a weak solution of `L u = f` on `Ω`
restricts to a weak solution of `L u = f` on `U`. This lets local estimates for weak
subsolutions be proved on a ball, which has finite measure, without global integrability
hypotheses on `Ω`.

## Main declarations

* `TauCeti.PDE.energyFormH1_restrictL`: `a(u|_U, v) = a(u, v₀)` for `v ∈ H¹₀(U)` with zero
  extension `v₀ ∈ H¹₀(Ω)`.
* `TauCeti.PDE.energyFormH1_restrictL_nonpos`: weak subsolutions restrict to weak subsolutions.
* `TauCeti.PDE.energyFormH1_restrictL_eq_setIntegral`: weak solutions restrict to weak solutions.
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

end PDE

end TauCeti
