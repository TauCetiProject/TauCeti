/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Action.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Path
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Homotopy

/-!
# Action variables as loop integrals of a primitive

Let `σ` be a symplectic form on a boundaryless manifold `M`, and let `F : M → (ι → ℝ)` be a smooth
family of pairwise Poisson-commuting functions with complete Hamiltonian vector fields, with the
conventions `ι_{X_f} σ = df` and `{f, g} = σ(X_f, X_g) = df(X_g)`. Their flows generate an action
`v • y` of `ι → ℝ` on `M` (`TauCeti.SmoothTwoForm.IsSymplectic.hamiltonianFlowAction`).

Let `s` be a local section of `F`, `F (s c) = c`, and let `λ` be a family of periods along it,
`λ(c) • s(c) = s(c)`. Each period gives a closed curve through `s c` in the level `F⁻¹(c)`,

`γ_c(τ) = (τ λ(c)) • s(c)`, `τ ∈ [0, 1]`.

Suppose that `σ = -dβ` along these level sets for a one-form `β`, as for the Liouville form of a
cotangent bundle, whose canonical symplectic form is `ω = -dλ`
(`TauCeti.CotangentBundle.symplecticForm_eq_neg_mextDeriv`). This file proves that the loop
integrals of `β` are action functions for the period family:

`d((2π)⁻¹ ∮_{γ_c} β) = (2π)⁻¹ ∑ⱼ λⱼ(c) dcⱼ`

(`hasFDerivAt_inv_two_pi_mul_pathIntegral_hamiltonianFlowAction`, in the namespace
`TauCeti.SmoothTwoForm.IsSymplectic`).
This holds for any family of periods, including zero or non-primitive ones. When the periods
`λ⁽¹⁾, …, λ⁽ⁿ⁾` form a basis of the full period lattice at each `c`, the corresponding loop
integrals are action variables of the Liouville–Arnold theorem
(`TauCeti.SmoothTwoForm.IsSymplectic.exists_isLocalDiffeomorphAt_action_of_isCompact`): such
action variables are characterized by this differential and are locally unique up to integral
affine changes (`TauCeti.exists_eq_mulVec_add_of_forall_eq_transposeLattice`). So in an exact
neighbourhood of a Liouville torus the classical formula `Iᵢ = (2π)⁻¹ ∮_{γᵢ} p dq`, over loops
`γᵢ` whose periods form a lattice basis, gives the actions.

The computation sweeps the loops over a `C²` curve `κ` of values: the map
`u(r, τ) = (τ λ(κ r)) • s(κ r)` is a cylinder between the loops over `κ 0` and `κ 1`. Its two other
sides are the curve `r ↦ s(κ r)` traversed twice, since `0 • y = y` and `λ(κ r) • s(κ r) = s(κ r)`,
so Stokes' formula for the cylinder (`TauCeti.rectangleIntegral_mextDeriv`) makes the difference
of the two loop integrals the integral of `-σ` over `u`. Moving `s ∘ κ` by the flow action changes
its pullback of `σ` by `∑ᵢ dhᵢ ∧ d(Fᵢ ∘ s ∘ κ)`
(`TauCeti.SmoothTwoForm.IsSymplectic.eval₂_mfderiv_hamiltonianFlowAction_comp`), and `s ∘ κ` does
not depend on `τ`, so

`σ(∂_r u, ∂_τ u) = -λ(κ r) ⬝ᵥ κ'(r)`

(`eval₂_mfderiv_hamiltonianFlowAction_smul_comp`). Hence the change of the loop integral along `κ`
is the integral of the period one-form `∑ⱼ λⱼ dcⱼ` along `κ`.

## Main results

All in the namespace `TauCeti.SmoothTwoForm.IsSymplectic`:

* `eval₂_mfderiv_hamiltonianFlowAction_smul_comp`: the area density of the cylinder swept by the
  loops over a curve of values is `-λ(κ r) ⬝ᵥ κ'(r)`.
* `pathIntegral_sub_pathIntegral_hamiltonianFlowAction_eq_integral`:
  `∮_{γ_(κ 1)} β - ∮_{γ_(κ 0)} β = ∫₀¹ λ(κ r) ⬝ᵥ κ'(r) dr`.
* `hasFDerivAt_inv_two_pi_mul_pathIntegral_hamiltonianFlowAction`: `(2π)⁻¹ ∮_{γ_c} β` is an action
  function for the period family.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 50 (the action variables `I = (2π)⁻¹ ∮ p dq`).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 18.4.
-/

public section

open Set Filter Topology Function Real
open ContinuousLinearMap (proj)
open scoped Manifold ContDiff Matrix

namespace TauCeti

namespace SmoothTwoForm

namespace IsSymplectic

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]
  {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
  {ι : Type*} [Fintype ι] {F : M → ι → ℝ} (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F)
  (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
  (hc : ∀ i, IsCompleteVectorField (σ.hamiltonianVectorField (F · i)))
  {D : Set (ι → ℝ)} {s : (ι → ℝ) → M} {p : (ι → ℝ) → ι → ℝ} {β : RoughForm I M ℝ 1}

include hσ hF hcomm hc

/-- **The area density of the cylinder swept by the loops over a curve of values.** Let `κ` be a
curve of values of `F` with `F (s (κ r)) = κ r`. If `κ`, `s ∘ κ` and `λ ∘ κ` are differentiable
at `r`, then the map `u(r, τ) = (τ λ(κ r)) • s(κ r)` satisfies

`σ(∂_r u, ∂_τ u) = -λ(κ r) ⬝ᵥ κ'(r)`

at `(r, τ)`. No period condition on `λ` is needed. -/
theorem eval₂_mfderiv_hamiltonianFlowAction_smul_comp {κ : ℝ → ι → ℝ} (hFs : ∀ r, F (s (κ r)) = κ r)
    {z : ℝ × ℝ} (hκ : DifferentiableAt ℝ κ z.1) (hsκ : MDifferentiableAt 𝓘(ℝ, ℝ) I (s ∘ κ) z.1)
    (hpκ : DifferentiableAt ℝ (p ∘ κ) z.1) :
    SmoothBundleForm.eval₂ σ
        ((hσ.hamiltonianFlowAction hF hcomm hc (z.2 • p (κ z.1))).toMul (s (κ z.1)))
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦
          (hσ.hamiltonianFlowAction hF hcomm hc (z.2 • p (κ z.1))).toMul (s (κ z.1))) z (1, 0))
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun z : ℝ × ℝ ↦
          (hσ.hamiltonianFlowAction hF hcomm hc (z.2 • p (κ z.1))).toMul (s (κ z.1))) z (0, 1)) =
      -(p (κ z.1) ⬝ᵥ deriv κ z.1) := by
  -- The cylinder is `h • g` for `h(r, τ) = τ λ(κ r)` and `g(r, τ) = s(κ r)`.
  set h : ℝ × ℝ → ι → ℝ := fun z ↦ z.2 • p (κ z.1)
  set g : ℝ × ℝ → M := fun z ↦ s (κ z.1)
  have hFg : F ∘ g = κ ∘ Prod.fst := funext fun z ↦ hFs z.1
  have hκd : HasFDerivAt (κ ∘ Prod.fst) ((fderiv ℝ κ z.1).comp
      (ContinuousLinearMap.fst ℝ ℝ ℝ)) z :=
    hκ.hasFDerivAt.comp z hasFDerivAt_fst
  have hhd : HasFDerivAt h (z.2 • ((fderiv ℝ (p ∘ κ) z.1).comp
      (ContinuousLinearMap.fst ℝ ℝ ℝ)) + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
        (p (κ z.1))) z :=
    hasFDerivAt_snd.smul (hpκ.hasFDerivAt.comp z hasFDerivAt_fst)
  -- `g` does not depend on `τ`.
  have hgm : HasMFDerivAt 𝓘(ℝ, ℝ × ℝ) I g z
      ((mfderiv 𝓘(ℝ, ℝ) I (s ∘ κ) z.1).comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) :=
    hsκ.hasMFDerivAt.comp z (hasFDerivAt_fst (p := z)).hasMFDerivAt
  have hgd : mfderiv 𝓘(ℝ, ℝ × ℝ) I g z (0, 1) = 0 := by
    rw [hgm.mfderiv]
    -- The first projection kills `(0, 1)`.
    exact (ContinuousLinearMap.comp_apply _ _ _).trans (map_zero _)
  have h0 : SmoothBundleForm.eval₂ σ (g z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I g z (1, 0)) 0 = 0 := by
    rw [← SmoothForm.bilinFormAt_apply]
    exact map_zero _
  -- The derivatives of `h` and `κ ∘ Prod.fst` along the coordinate vectors. They are computed
  -- for `fderiv` and transferred to `mfderiv`, whose tangent spaces are the model spaces only up
  -- to unfolding `TangentSpace`.
  have hdh : fderiv ℝ h z (0, 1) = p (κ z.1) := by
    rw [hhd.fderiv]
    simp
  have hdκ₁ : fderiv ℝ (κ ∘ Prod.fst) z (1, 0) = deriv κ z.1 := by
    rw [hκd.fderiv]
    simp
  have hdκ₂ : fderiv ℝ (κ ∘ Prod.fst) z (0, 1) = 0 := by
    rw [hκd.fderiv]
    simp
  have hmh := hhd.hasMFDerivAt.mfderiv.trans hhd.fderiv.symm
  have hmκ := hκd.hasMFDerivAt.mfderiv.trans hκd.fderiv.symm
  have h₁ : mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ι → ℝ) h z (0, 1) = p (κ z.1) :=
    (congrArg (fun L ↦ L (0, 1)) hmh).trans hdh
  have h₂ : mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ι → ℝ) (κ ∘ Prod.fst) z (1, 0) = deriv κ z.1 :=
    (congrArg (fun L ↦ L (1, 0)) hmκ).trans hdκ₁
  have h₃ : mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ι → ℝ) (κ ∘ Prod.fst) z (0, 1) = (0 : ι → ℝ) :=
    (congrArg (fun L ↦ L (0, 1)) hmκ).trans hdκ₂
  -- Moving `g` by `h` adds `∑ᵢ dhᵢ ∧ d(Fᵢ ∘ g)` to the pullback of `σ`.
  have hev := hσ.eval₂_mfderiv_hamiltonianFlowAction_comp hF hcomm hc (n := z)
    hhd.hasMFDerivAt.mdifferentiableAt hgm.mdifferentiableAt
    ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)
  rw [hFg, h₁, h₂, h₃, hgd, h0, zero_add] at hev
  rw [hev]
  -- `dotProduct_zero` does not rewrite here, as the vector `(1, 0)` lives in a tangent space.
  exact (congrArg (· - _) (dotProduct_zero _)).trans (zero_sub _)

/-- **The change of the loop integrals along a curve of values.** Let `s` be a `C²` section of
`F` over `D`, let `λ` be a `C²` family of periods along it, and let `β` be a `C¹` one-form with
`dβ = -σ` on the orbits of the points `s c`. For a `C²` curve `κ` in `D`, the integrals of `β`
around the closed curves `τ ↦ (τ λ(c)) • s(c)` at the two ends of `κ` differ by the integral of
the period one-form `∑ⱼ λⱼ dcⱼ` along `κ`. -/
theorem pathIntegral_sub_pathIntegral_hamiltonianFlowAction_eq_integral
    (hs : ContMDiffOn 𝓘(ℝ, ι → ℝ) I 2 s D) (hFs : ∀ c ∈ D, F (s c) = c)
    (hp : ContDiffOn ℝ 2 p D)
    (hps : ∀ c ∈ D, p c ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc (s c))
    (hβ : IsSmoothForm I 1 β)
    (hdβ : ∀ c ∈ D, ∀ v, mextDeriv β ((hσ.hamiltonianFlowAction hF hcomm hc v).toMul (s c)) =
      -σ.1 ((hσ.hamiltonianFlowAction hF hcomm hc v).toMul (s c)))
    {κ : ℝ → ι → ℝ} (hκ : ContDiff ℝ 2 κ) (hκD : ∀ r, κ r ∈ D) :
    pathIntegral β
        (fun τ ↦ (hσ.hamiltonianFlowAction hF hcomm hc (τ • p (κ 1))).toMul (s (κ 1))) 0 1 -
      pathIntegral β
        (fun τ ↦ (hσ.hamiltonianFlowAction hF hcomm hc (τ • p (κ 0))).toMul (s (κ 0))) 0 1 =
      ∫ r in 0..1, p (κ r) ⬝ᵥ deriv κ r := by
  -- The cylinder `u(r, τ) = (τ λ(κ r)) • s(κ r)` swept by the loops over `κ`.
  set u : ℝ × ℝ → M := fun z ↦
    (hσ.hamiltonianFlowAction hF hcomm hc (z.2 • p (κ z.1))).toMul (s (κ z.1)) with hu_def
  have hpκ : ContDiff ℝ 2 (p ∘ κ) := hp.comp_contDiff hκ hκD
  have hsκ : ContMDiff 𝓘(ℝ, ℝ) I 2 (s ∘ κ) := hs.comp_contMDiff hκ.contMDiff hκD
  have hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 u :=
    ((hσ.contMDiff_hamiltonianFlowAction_uncurry hF hcomm hc).of_le (by simp)).comp
      ((contDiff_snd.smul (hpκ.comp contDiff_fst)).contMDiff.prodMk
        (hsκ.comp contDiff_fst.contMDiff))
  -- The two sides `τ = 0` and `τ = 1` of the cylinder are both the curve `r ↦ s(κ r)`, so by
  -- Stokes' formula the difference of the loop integrals is the integral of `dβ` over `u`.
  have hside : (fun r ↦ u (r, 1)) = fun r ↦ u (r, 0) := by
    funext r
    simp only [hu_def, one_smul, zero_smul, hσ.hamiltonianFlowAction_zero_apply hF hcomm hc]
    exact (hσ.mem_hamiltonianFlowStabilizer hF hcomm hc).1 (hps _ (hκD r))
  have hrect := rectangleIntegral_mextDeriv hβ hu (0, 0) (1, 1)
  simp only [hside, sub_self, sub_zero] at hrect
  rw [← hrect, rectangleIntegral_eq]
  -- On the cylinder `dβ = -σ`, and the integrand of `σ` does not depend on `τ`.
  have hneg (z : ℝ × ℝ) :
      mextDeriv β (u z) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (1, 0), mfderiv 𝓘(ℝ, ℝ × ℝ) I u z (0, 1)] =
        p (κ z.1) ⬝ᵥ deriv κ z.1 := by
    rw [hu_def, hdβ _ (hκD z.1), ContinuousAlternatingMap.neg_apply, neg_eq_iff_eq_neg,
      ← SmoothBundleForm.eval₂_apply]
    exact hσ.eval₂_mfderiv_hamiltonianFlowAction_smul_comp hF hcomm hc (fun r ↦ hFs _ (hκD r))
      ((hκ.differentiable (by simp)) z.1) ((hsκ z.1).mdifferentiableAt two_ne_zero)
      ((hpκ.differentiable (by simp)) z.1)
  calc _ = ∫ r in (0 : ℝ)..1, ∫ _ in (0 : ℝ)..1, p (κ r) ⬝ᵥ deriv κ r :=
        intervalIntegral.integral_congr fun r _ ↦
          intervalIntegral.integral_congr fun t _ ↦ hneg (r, t)
    _ = _ := by simp

/-- **Loop integrals of a primitive are action functions.** Let `s` be a `C²` section of `F` over
an open set `D`, let `λ` be a `C²` family of periods along it, and let `β` be a `C¹` one-form with
`dβ = -σ` on the orbits of the points `s c`. Then the function

`c ↦ (2π)⁻¹ ∮_{γ_c} β`, `γ_c(τ) = (τ λ(c)) • s(c)`, `τ ∈ [0, 1]`,

has differential `(2π)⁻¹ ∑ⱼ λⱼ(c) dcⱼ` at every `c ∈ D`: it is an action function for the period
family `λ`, which may be any family of periods. When the families `λ⁽¹⁾, …, λ⁽ⁿ⁾` form a basis of
the full period lattice, the corresponding functions are Liouville–Arnold action coordinates,
locally unique up to integral affine changes. For the Liouville form `β = p dq` of a cotangent
bundle this is the formula `Iᵢ = (2π)⁻¹ ∮_{γᵢ} p dq` for the action variables. -/
theorem hasFDerivAt_inv_two_pi_mul_pathIntegral_hamiltonianFlowAction (hD : IsOpen D)
    (hs : ContMDiffOn 𝓘(ℝ, ι → ℝ) I 2 s D) (hFs : ∀ c ∈ D, F (s c) = c)
    (hp : ContDiffOn ℝ 2 p D)
    (hps : ∀ c ∈ D, p c ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc (s c))
    (hβ : IsSmoothForm I 1 β)
    (hdβ : ∀ c ∈ D, ∀ v, mextDeriv β ((hσ.hamiltonianFlowAction hF hcomm hc v).toMul (s c)) =
      -σ.1 ((hσ.hamiltonianFlowAction hF hcomm hc v).toMul (s c)))
    {c : ι → ℝ} (hcD : c ∈ D) :
    HasFDerivAt (fun c ↦ (2 * π)⁻¹ * pathIntegral β
        (fun τ ↦ (hσ.hamiltonianFlowAction hF hcomm hc (τ • p c)).toMul (s c)) 0 1)
      ((2 * π)⁻¹ • ∑ j, p c j • (proj j : (ι → ℝ) →L[ℝ] ℝ)) c := by
  set J : (ι → ℝ) → ℝ := fun c ↦ pathIntegral β
    (fun τ ↦ (hσ.hamiltonianFlowAction hF hcomm hc (τ • p c)).toMul (s c)) 0 1 with hJ
  -- On a ball `B ⊆ D` around `c`, the period one-form has a primitive `A`.
  obtain ⟨ε, hε, hB⟩ := Metric.isOpen_iff.1 hD c hcD
  obtain ⟨A, hA⟩ := hσ.exists_forall_hasFDerivAt_of_mem_hamiltonianFlowStabilizer hF hcomm hc
    (convex_ball c ε) Metric.isOpen_ball ((hs.mdifferentiableOn two_ne_zero).mono hB)
    (fun c hc ↦ hFs c (hB hc)) ((hp.differentiableOn two_ne_zero).mono hB)
    fun c hc ↦ hps c (hB hc)
  -- Along the segment from `c` to `c'`, smoothed at its ends, the loop integral changes by
  -- `2π (A c' - A c)`.
  have hkey (c' : ι → ℝ) (hc' : c' ∈ Metric.ball c ε) :
      (2 * π)⁻¹ * J c' = (2 * π)⁻¹ * J c + (A c' - A c) := by
    set κ : ℝ → ι → ℝ := fun r ↦ c + smoothTransition r • (c' - c) with hκ_def
    have hκ : ContDiff ℝ 2 κ := contDiff_const.add (smoothTransition.contDiff.smul contDiff_const)
    have hκB (r : ℝ) : κ r ∈ Metric.ball c ε :=
      (convex_ball c ε).add_smul_sub_mem (Metric.mem_ball_self hε) hc'
        ⟨smoothTransition.nonneg r, smoothTransition.le_one r⟩
    have hκ0 : κ 0 = c := by simp [hκ_def]
    have hκ1 : κ 1 = c' := by simp [hκ_def]
    have h := hσ.pathIntegral_sub_pathIntegral_hamiltonianFlowAction_eq_integral hF hcomm hc
      (hs.mono hB) (fun c hc ↦ hFs c (hB hc)) (hp.mono hB) (fun c hc ↦ hps c (hB hc)) hβ
      (fun c hc ↦ hdβ c (hB hc)) hκ hκB
    rw [hκ0, hκ1] at h
    -- The fundamental theorem of calculus for `A ∘ κ`.
    have hd (r : ℝ) : HasDerivAt (fun r ↦ A (κ r)) ((2 * π)⁻¹ * (p (κ r) ⬝ᵥ deriv κ r)) r := by
      rw [← fderiv_apply_eq_of_hasFDerivAt_action (hA (κ r) (hκB r)), (hA (κ r) (hκB r)).fderiv]
      exact (hA (κ r) (hκB r)).comp_hasDerivAt r ((hκ.differentiable (by simp)) r).hasDerivAt
    have hcont : Continuous fun r ↦ (2 * π)⁻¹ * (p (κ r) ⬝ᵥ deriv κ r) :=
      continuous_const.mul
        ((hp.comp_contDiff hκ fun r ↦ hB (hκB r)).continuous.dotProduct
          (hκ.continuous_deriv (by simp)))
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ ↦ hd r)
      (hcont.intervalIntegrable 0 1)
    rw [intervalIntegral.integral_const_mul, ← h, hκ0, hκ1] at hftc
    rw [← hftc, hJ]
    ring
  refine ((((hA c (Metric.mem_ball_self hε)).sub_const (A c)).const_add
    ((2 * π)⁻¹ * J c))).congr_of_eventuallyEq ?_
  exact eventually_of_mem (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε)) hkey

end IsSymplectic

end SmoothTwoForm

end TauCeti
