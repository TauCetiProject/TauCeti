/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Scaling
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Curvature
public import Mathlib.Analysis.Calculus.Deriv.Mul
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# Einstein metrics as explicit Ricci flows

A family of metrics `g τ = φ(τ) g₀`, a time-dependent constant multiple of a fixed metric `g₀`, has
the Ricci tensor of `g₀` at every time, because constant rescaling does not change the Ricci tensor.
Its time derivative is `φ'(τ) g₀`. Hence it satisfies the Ricci flow equation `∂_τ g = -2 Ric(g)`
exactly when `Ric(g₀) = -(φ'/2) g₀`, that is, when `g₀` is Einstein with constant `-φ'/2`.

In particular, if `Ric(g₀) = c g₀` then `g τ = (1 - 2 c τ) g₀` is a Ricci flow on its positive-scale
interval `2 c τ < 1`. For `c > 0` this interval ends at `T = 1 / (2 c)`, and there the flow dies:
its scalar curvature `Scal(g τ) = n c / (1 - 2 c τ)` tends to `+∞` as `τ → T`, where `n ≥ 1` is the
dimension. The round unit `n`-sphere has `Ric = (n - 1) g`, so its Ricci flow lives for time
`1 / (2 (n - 1))` when `n ≥ 2`. For `φ = 1` the family is constant, and a constant family is a
Ricci flow exactly when `g₀` is Ricci-flat; in dimension at most one every metric is Ricci-flat.

Families are known only through their inner products on a time set `s`, as for
`TauCeti.hasDerivWithinAt_chartVolumeDensity_of_ricciFlow`, so the factor `φ` need not be positive
off `s`, and the flow equation is stated pointwise as a derivative within `s`.

## Main results

* `TauCeti.hasDerivWithinAt_inner_of_inner_eq_smul` and its converse
  `TauCeti.hasDerivWithinAt_inner_iff_of_inner_eq_smul`: `τ ↦ φ(τ) g₀` satisfies the Ricci flow
  equation at `x` exactly when `Ric(g₀) = -(φ'/2) g₀` at `x`.
* `TauCeti.hasDerivWithinAt_inner_of_inner_eq_one_sub_two_mul_smul`: the Einstein solution
  `g τ = (1 - 2 c τ) g₀` of a metric with `Ric(g₀) = c g₀`.
* `TauCeti.scalarCurvature_eq_of_inner_eq_one_sub_two_mul_smul` and
  `TauCeti.tendsto_scalarCurvature_of_inner_eq_one_sub_two_mul_smul`: along the Einstein solution
  `Scal = n c / (1 - 2 c τ)`, which blows up at the extinction time `1 / (2 c)` when `c > 0`.
* `TauCeti.hasDerivWithinAt_inner_const_iff`: a constant family is a Ricci flow exactly when the
  metric is Ricci-flat, and `TauCeti.hasDerivWithinAt_inner_const_of_finrank_le_one` shows that
  every metric in dimension at most one is stationary.
* `TauCeti.hasDerivWithinAt_inner_sphere` and `TauCeti.tendsto_scalarCurvature_sphere`: the
  shrinking round sphere `(1 - 2 (n - 1) τ) g_round` and its extinction at `1 / (2 (n - 1))`.

## References

* P. Topping, *Lectures on the Ricci flow*, LMS Lecture Note Series 325, Cambridge University
  Press (2006), §1.2.1 (Einstein solutions and the round sphere).
-/

public section

open Bundle CovariantDerivative Filter Metric Module Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g₀ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
  {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
  {s : Set ℝ} {t : ℝ} {x : M}

section Homothetic

variable {φ : ℝ → ℝ} {φ' : ℝ}

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The inner products of a family `g τ = φ(τ) g₀` on `s` have derivative `φ' g₀` within `s`. -/
private theorem hasDerivWithinAt_inner_of_inner_eq_smul_aux
    (hg : ∀ τ ∈ s, ∀ y, (g τ).inner y = φ τ • g₀.inner y) (hφ : HasDerivWithinAt φ φ' s t)
    (ht : t ∈ s) (u v : TangentSpace I x) :
    HasDerivWithinAt (fun τ ↦ (g τ).inner x u v) (φ' * g₀.inner x u v) s t :=
  (hφ.mul_const _).congr_of_mem (fun τ hτ ↦ by simp [hg τ hτ]) ht

/-- **Homothetic Ricci flows.** Let `g τ = φ(τ) g₀` for `τ ∈ s`, and let `φ` have derivative `φ'`
at `t ∈ s` within `s`. If `Ric(g₀) = -(φ'/2) g₀` at `x`, then the family satisfies the Ricci flow
equation `∂_τ g = -2 Ric(g)` at `x` at time `t` within `s`. -/
theorem hasDerivWithinAt_inner_of_inner_eq_smul
    (hg : ∀ τ ∈ s, ∀ y, (g τ).inner y = φ τ • g₀.inner y) (hφ : HasDerivWithinAt φ φ' s t)
    (ht : t ∈ s)
    (hRic : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩;
      (leviCivitaConnection I M).ricciTensor x = (-(φ' / 2)) • innerₗ (TangentSpace I x))
    (u v : TangentSpace I x) :
    HasDerivWithinAt (fun τ ↦ (g τ).inner x u v)
      (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
        (leviCivitaConnection I M).ricciTensor x u v)) s t := by
  convert hasDerivWithinAt_inner_of_inner_eq_smul_aux hg hφ ht u v using 1
  rw [ContMDiffRiemannianMetric.ricciTensor_leviCivitaConnection_eq_of_inner_eq_smul g₀ (g t)
    (hg t ht) x, hRic]
  simp only [LinearMap.smul_apply, innerₗ_apply_apply, smul_eq_mul]
  rw [ContMDiffRiemannianMetric.inner_riemannianBundle]
  ring

/-- **Homothetic Ricci flows are Einstein.** Let `g τ = φ(τ) g₀` for `τ ∈ s`, let `φ` have
derivative `φ'` at `t ∈ s` within `s`, and let `s` have unique derivatives at `t`. Then the family
satisfies the Ricci flow equation `∂_τ g = -2 Ric(g)` at `x` at time `t` exactly when
`Ric(g₀) = -(φ'/2) g₀` at `x`. -/
theorem hasDerivWithinAt_inner_iff_of_inner_eq_smul
    (hg : ∀ τ ∈ s, ∀ y, (g τ).inner y = φ τ • g₀.inner y) (hφ : HasDerivWithinAt φ φ' s t)
    (ht : t ∈ s) (hs : UniqueDiffWithinAt ℝ s t) :
    (∀ u v : TangentSpace I x, HasDerivWithinAt (fun τ ↦ (g τ).inner x u v)
      (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
        (leviCivitaConnection I M).ricciTensor x u v)) s t) ↔
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩;
      (leviCivitaConnection I M).ricciTensor x = (-(φ' / 2)) • innerₗ (TangentSpace I x)) := by
  refine ⟨fun hflow ↦ ?_, hasDerivWithinAt_inner_of_inner_eq_smul hg hφ ht⟩
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩
  refine LinearMap.ext₂ fun u v ↦ ?_
  have h := hs.eq_deriv _ (hasDerivWithinAt_inner_of_inner_eq_smul_aux hg hφ ht u v) (hflow u v)
  rw [ContMDiffRiemannianMetric.ricciTensor_leviCivitaConnection_eq_of_inner_eq_smul g₀ (g t)
    (hg t ht) x] at h
  simp only [LinearMap.smul_apply, innerₗ_apply_apply, smul_eq_mul,
    ContMDiffRiemannianMetric.inner_riemannianBundle]
  linarith

end Homothetic

section Einstein

variable {c : ℝ}

/-- **Einstein solutions of the Ricci flow.** If `Ric(g₀) = c g₀` at `x` and
`g τ = (1 - 2 c τ) g₀` for `τ ∈ s`, then the family satisfies the Ricci flow equation
`∂_τ g = -2 Ric(g)` at `x` at every time `t ∈ s`, within `s`. -/
theorem hasDerivWithinAt_inner_of_inner_eq_one_sub_two_mul_smul
    (hg : ∀ τ ∈ s, ∀ y, (g τ).inner y = (1 - 2 * c * τ) • g₀.inner y) (ht : t ∈ s)
    (hRic : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩;
      (leviCivitaConnection I M).ricciTensor x = c • innerₗ (TangentSpace I x))
    (u v : TangentSpace I x) :
    HasDerivWithinAt (fun τ ↦ (g τ).inner x u v)
      (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
        (leviCivitaConnection I M).ricciTensor x u v)) s t := by
  have hφ : HasDerivWithinAt (fun τ ↦ 1 - 2 * c * τ) (-(2 * c)) s t := by
    simpa using ((hasDerivWithinAt_id t s).const_mul (2 * c)).const_sub 1
  exact hasDerivWithinAt_inner_of_inner_eq_smul hg hφ ht (by rw [hRic]; congr 1; ring) u v

/-- Along the Einstein solution `g τ = (1 - 2 c τ) g₀` of a metric with `Ric(g₀) = c g₀` at `x`,
the scalar curvature at `x` is `Scal(g τ) = n c / (1 - 2 c τ)`, where `n` is the dimension. -/
theorem scalarCurvature_eq_of_inner_eq_one_sub_two_mul_smul
    (hg : ∀ τ ∈ s, ∀ y, (g τ).inner y = (1 - 2 * c * τ) • g₀.inner y) (ht : t ∈ s)
    (hRic : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩;
      (leviCivitaConnection I M).ricciTensor x = c • innerₗ (TangentSpace I x)) :
    (g t).scalarCurvature x = finrank ℝ E * c / (1 - 2 * c * t) := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩
  rw [ContMDiffRiemannianMetric.scalarCurvature_eq_inv_mul_of_inner_eq_smul g₀ (g t) (hg t ht) x,
    ContMDiffRiemannianMetric.scalarCurvature_def,
    (leviCivitaConnection I M).scalarCurvature_eq_of_ricciTensor_eq_smul_inner x c hRic,
    finrank_tangentSpace, inv_mul_eq_div]

/-- **Extinction of an Einstein solution.** Let `Ric(g₀) = c g₀` at `x` with `c > 0`, in positive
dimension, and let `g τ = (1 - 2 c τ) g₀` on a time set `s` containing a left neighbourhood of
`T = (2 c)⁻¹`. Then the scalar curvature `Scal(g τ)` at `x` tends to `+∞` as `τ → T⁻`. -/
theorem tendsto_scalarCurvature_of_inner_eq_one_sub_two_mul_smul (hc : 0 < c)
    (hE : 0 < finrank ℝ E) (hs : s ∈ 𝓝[<] (2 * c)⁻¹)
    (hg : ∀ τ ∈ s, ∀ y, (g τ).inner y = (1 - 2 * c * τ) • g₀.inner y)
    (hRic : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩;
      (leviCivitaConnection I M).ricciTensor x = c • innerₗ (TangentSpace I x)) :
    Tendsto (fun τ ↦ (g τ).scalarCurvature x) (𝓝[<] (2 * c)⁻¹) atTop := by
  have h2c : 0 < 2 * c := by positivity
  -- The scale factor `1 - 2 c τ` tends to `0` from above as `τ → (2 c)⁻¹` from below.
  have hscale : Tendsto (fun τ ↦ 1 - 2 * c * τ) (𝓝[<] (2 * c)⁻¹) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun τ hτ ↦ ?_⟩
    · have hcont : Continuous fun τ : ℝ ↦ 1 - 2 * c * τ := by fun_prop
      have h0 : 1 - 2 * c * (2 * c)⁻¹ = 0 := by field_simp; ring
      exact h0 ▸ hcont.continuousWithinAt.tendsto
    · have hτ' : τ < (2 * c)⁻¹ := hτ
      have : 2 * c * τ < 1 := by
        calc 2 * c * τ < 2 * c * (2 * c)⁻¹ := by gcongr
          _ = 1 := mul_inv_cancel₀ h2c.ne'
      simp only [mem_Ioi]
      linarith
  have hnc : 0 < finrank ℝ E * c := by positivity
  refine ((tendsto_inv_nhdsGT_zero.comp hscale).atTop_mul_const hnc).congr' ?_
  filter_upwards [hs] with τ hτ
  rw [scalarCurvature_eq_of_inner_eq_one_sub_two_mul_smul hg hτ hRic, Function.comp_apply,
    div_eq_inv_mul]

end Einstein

section Stationary

/-- **Stationary Ricci flows.** If `s` has unique derivatives at `t`, the constant family `g₀`
satisfies the Ricci flow equation `∂_τ g = -2 Ric(g)` at `x` at time `t` within `s` exactly when
`g₀` is Ricci-flat at `x`. -/
theorem hasDerivWithinAt_inner_const_iff (hs : UniqueDiffWithinAt ℝ s t) :
    (∀ u v : TangentSpace I x, HasDerivWithinAt (fun _ : ℝ ↦ g₀.inner x u v)
      (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩;
        (leviCivitaConnection I M).ricciTensor x u v)) s t) ↔
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩;
      (leviCivitaConnection I M).ricciTensor x = 0) := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩
  refine ⟨fun hflow ↦ LinearMap.ext₂ fun u v ↦ ?_, fun h u v ↦ ?_⟩
  · have := hs.eq_deriv _ (hasDerivWithinAt_const t s _) (hflow u v)
    simp only [LinearMap.zero_apply]
    linarith
  · simpa [h] using hasDerivWithinAt_const t s (g₀.inner x u v)

/-- **Ricci flow in dimension at most one.** In dimension at most one the Ricci tensor vanishes,
so the constant family of every metric is a Ricci flow. -/
theorem hasDerivWithinAt_inner_const_of_finrank_le_one (hE : finrank ℝ E ≤ 1)
    (u v : TangentSpace I x) :
    HasDerivWithinAt (fun _ : ℝ ↦ g₀.inner x u v)
      (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩;
        (leviCivitaConnection I M).ricciTensor x u v)) s t := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩
  simpa [ricciTensor_eq_zero_of_finrank_le_one _ x hE] using hasDerivWithinAt_const t s _

end Stationary

section Sphere

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {n : ℕ}
  [Fact (finrank ℝ F = n + 1)]
  {g : ℝ → ContMDiffRiemannianMetric (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
    (fun p : sphere (0 : F) 1 ↦ TangentSpace (𝓡 n) p)}

/-- **The shrinking round sphere.** The family `g τ = (1 - 2 (n - 1) τ) g_round` of multiples of
the round metric on the unit `n`-sphere satisfies the Ricci flow equation `∂_τ g = -2 Ric(g)` at
every point and at every time `t ∈ s`, within `s`. -/
theorem hasDerivWithinAt_inner_sphere
    (hg : ∀ τ ∈ s, ∀ p, (g τ).inner p =
      (1 - 2 * ((n : ℝ) - 1) * τ) •
        ((sphereRoundMetric (E := F) (n := n)).ofLE (m := ∞) le_top).inner p)
    (ht : t ∈ s) (p : sphere (0 : F) 1) (u v : TangentSpace (𝓡 n) p) :
    HasDerivWithinAt (fun τ ↦ (g τ).inner p u v)
      (-2 * (letI : RiemannianBundle (fun p : sphere (0 : F) 1 ↦ TangentSpace (𝓡 n) p) :=
          ⟨(g t).toRiemannianMetric⟩;
        (leviCivitaConnection (𝓡 n) (sphere (0 : F) 1)).ricciTensor p u v)) s t :=
  hasDerivWithinAt_inner_of_inner_eq_one_sub_two_mul_smul hg ht
    (ricciTensor_sphereRoundMetric_ofLE p) u v

/-- **Extinction of the shrinking round sphere.** For `n ≥ 2`, along the family
`g τ = (1 - 2 (n - 1) τ) g_round` on a time set `s` containing a left neighbourhood of
`T = (2 (n - 1))⁻¹`, the scalar curvature at every point tends to `+∞` as `τ → T⁻`: the flow
starting at the unit sphere becomes extinct at time `1 / (2 (n - 1))`. -/
theorem tendsto_scalarCurvature_sphere (hn : 2 ≤ n) (hs : s ∈ 𝓝[<] (2 * ((n : ℝ) - 1))⁻¹)
    (hg : ∀ τ ∈ s, ∀ p, (g τ).inner p =
      (1 - 2 * ((n : ℝ) - 1) * τ) •
        ((sphereRoundMetric (E := F) (n := n)).ofLE (m := ∞) le_top).inner p)
    (p : sphere (0 : F) 1) :
    Tendsto (fun τ ↦ (g τ).scalarCurvature p) (𝓝[<] (2 * ((n : ℝ) - 1))⁻¹) atTop := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  refine tendsto_scalarCurvature_of_inner_eq_one_sub_two_mul_smul (by linarith) ?_ hs hg
    (ricciTensor_sphereRoundMetric_ofLE p)
  rw [finrank_euclideanSpace_fin]
  omega

end Sphere

end TauCeti
