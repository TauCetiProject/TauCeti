/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Action.FirstVariation
public import TauCeti.Geometry.Symplectic.Hamiltonian.ContractibleAction.FirstVariation
public import TauCeti.Geometry.Symplectic.TameMetric

/-!
# The weak gradient of the action for tame almost complex structures

Let `σ` be a nondegenerate two-form on a manifold `M`, `H : ℝ → M → ℝ` a time-dependent
Hamiltonian and `w : ℝ × ℝ → M` a variation through loops, `1`-periodic in `t`, with loops
`γ_s = w (s, ·)`. The first variation formula expresses the derivative of the action of `γ_s`,
for the contractible action
(`TauCeti.SmoothTwoForm.IsNondegenerate.hasDerivAt_contractibleLoopAction`) and for the action
relative to a reference loop (`TauCeti.SmoothTwoForm.IsNondegenerate.hasDerivAt_referenceAction`),
as

`d/ds A_H(γ_s) = ∫₀¹ σ(∂_t w - X_{H_t}(w), ∂_s w) dt`.

This is the weak differential of the action in the direction `ξ = ∂_s w`. To read it as a
gradient one needs a metric along the loop. A loop `J_t` of almost complex structures on
`T_{γ(t)} M` tamed by `σ` determines the positive symmetric metric
`g_t = gₛ / 2`, `gₛ(v, w) = σ(v, J_t w) + σ(w, J_t v)`
(`TauCeti.SymplecticForm.symmetrizedBilinForm`), and the gradient operator `A_t` of the tame pair,
`g_t(A_t u, v) = σ(u, v)` (`TauCeti.SymplecticForm.Tames.gradientOperator`). The first variation
then becomes

`d/ds A_H(γ_s) = ∫₀¹ g_t(∂_s w, A_t (∂_t w - X_{H_t}(w))) dt`,

so `A_t (γ' - X_{H_t}(γ))` is the weak `L²` gradient of the action at `γ` for the metric `g_t`
(`TauCeti.SmoothTwoForm.IsNondegenerate.hasDerivAt_contractibleLoopAction_of_tames`,
`TauCeti.SmoothTwoForm.IsNondegenerate.hasDerivAt_referenceAction_of_tames`).

When `J_t` is compatible with `σ`, `A_t = J_t`
(`TauCeti.SymplecticForm.Compatible.gradientOperator_eq`) and `g_t = σ(·, J_t ·)`, so the
gradient is the familiar `J_t (γ' - X_{H_t}(γ))`
(`TauCeti.SmoothTwoForm.IsNondegenerate.hasDerivAt_contractibleLoopAction_of_compatible`), for
which the Floer equation `∂_s u + J_t (∂_t u - X_{H_t}(u)) = 0` is the negative gradient flow.
For a merely tame `J_t` the gradient operator differs from `J_t` exactly where compatibility fails
(`TauCeti.SymplecticForm.Tames.gradientOperator_eq_iff`), and tame structures need not be
compatible (`TauCeti.SymplecticForm.exists_tames_not_compatible`). The Floer equation for such a
`J_t` then need not be the gradient flow of the action for `g_t`, although its solutions still
decrease the action.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.apply_eq_symmetrizedBilinForm_gradientOperator`: the
  pointwise identity `σ(a, ξ) = gₛ(ξ, A a) / 2`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.hasDerivAt_contractibleLoopAction_of_tames`,
  `TauCeti.SmoothTwoForm.IsNondegenerate.hasDerivAt_referenceAction_of_tames`:
  the first variation formula as the `L²` pairing of `∂_s w` with the gradient
  `A_t (∂_t w - X_{H_t}(w))`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.hasDerivAt_contractibleLoopAction_of_compatible`: for
  compatible `J_t`, the pairing of `∂_s w` with `J_t (∂_t w - X_{H_t}(w))` for the metric
  `σ(·, J_t ·)`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 2.5 (the metric
  of a tame almost complex structure) and Section 12.1 (Floer trajectories as gradient lines).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1 (the gradient of the symplectic action).
-/

public section

noncomputable section

open Function Set
open scoped Manifold Interval ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [FiniteDimensional ℝ E] {σ : SmoothTwoForm I M}

/-- **The two-form through the gradient operator.** For a nondegenerate two-form `σ` and an
almost complex structure `J` on `T_x M` tamed by `σ`, with symmetric metric `gₛ` and gradient
operator `A`, `σ(a, ξ) = gₛ(ξ, A a) / 2`. -/
theorem SmoothTwoForm.IsNondegenerate.apply_eq_symmetrizedBilinForm_gradientOperator
    (h : σ.IsNondegenerate) {x : M} {J : AlmostComplexStructure (TangentSpace I x)}
    (hJ : (h.symplecticFormAt x).Tames J) (a ξ : TangentSpace I x) :
    σ.val x ![a, ξ] =
      (h.symplecticFormAt x).symmetrizedBilinForm J ξ (hJ.gradientOperator a) / 2 := by
  rw [hJ.symmetrizedBilinForm_gradientOperator_right, h.symplecticFormAt_apply,
    SmoothBundleForm.eval₂_apply]
  ring

variable {H : ℝ → M → ℝ} {w : ℝ × ℝ → M}

/-- **The weak gradient of the contractible action for tame almost complex structures.** Let `σ` be
a nondegenerate weakly exact two-form, `H` a jointly `C¹` time-dependent Hamiltonian and `w` a `C²`
variation through loops, `1`-periodic in `t`, whose loop `w (s₀, ·)` has a cap. Let `J_t` be almost
complex structures on `T_{w(s₀, t)} M` tamed by `σ`, with symmetric metrics `gₛ` and gradient
operators `A_t`. Then the action of the loops `w (s, ·)` has derivative
`∫₀¹ gₛ(∂_s w, A_t (∂_t w - X_{H_t}(w))) / 2 dt` at `s₀`, with all terms taken at `(s₀, t)`. -/
theorem SmoothTwoForm.IsNondegenerate.hasDerivAt_contractibleLoopAction_of_tames
    (h : σ.IsNondegenerate) (hw : IsWeaklyExact σ.val)
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hwc : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 w)
    (hper : ∀ z : ℝ × ℝ, w (z.1, z.2 + 1) = w z) {s₀ : ℝ}
    (hcap : ∃ u, IsCap I u fun t ↦ w (s₀, t))
    {J : (t : ℝ) → AlmostComplexStructure (TangentSpace I (w (s₀, t)))}
    (hJ : ∀ t, (h.symplecticFormAt (w (s₀, t))).Tames (J t)) :
    HasDerivAt (fun s ↦ contractibleLoopAction σ.val H fun t ↦ w (s, t))
      (∫ t in 0..1, (h.symplecticFormAt (w (s₀, t))).symmetrizedBilinForm (J t)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (1, 0))
        ((hJ t).gradientOperator (mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (0, 1) -
          σ.hamiltonianVectorField (H t) (w (s₀, t)))) / 2) s₀ :=
  (h.hasDerivAt_contractibleLoopAction hw hH hwc hper hcap).congr_deriv <|
    intervalIntegral.integral_congr fun t _ ↦
      h.apply_eq_symmetrizedBilinForm_gradientOperator (hJ t) _ _

/-- **The gradient of the contractible action for compatible almost complex structures.** Under
the hypotheses of
`TauCeti.SmoothTwoForm.IsNondegenerate.hasDerivAt_contractibleLoopAction_of_tames`, if every
`J_t` is compatible with `σ`, the action of the loops `w (s, ·)` has derivative
`∫₀¹ g_{J_t}(∂_s w, J_t (∂_t w - X_{H_t}(w))) dt` at `s₀` for the metric `g_{J_t} = σ(·, J_t ·)`,
with all terms taken at `(s₀, t)`. So `J_t (γ' - X_{H_t}(γ))` is the weak `L²` gradient. -/
theorem SmoothTwoForm.IsNondegenerate.hasDerivAt_contractibleLoopAction_of_compatible
    (h : σ.IsNondegenerate) (hw : IsWeaklyExact σ.val)
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hwc : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 w)
    (hper : ∀ z : ℝ × ℝ, w (z.1, z.2 + 1) = w z) {s₀ : ℝ}
    (hcap : ∃ u, IsCap I u fun t ↦ w (s₀, t))
    {J : (t : ℝ) → AlmostComplexStructure (TangentSpace I (w (s₀, t)))}
    (hJ : ∀ t, (h.symplecticFormAt (w (s₀, t))).Compatible (J t)) :
    HasDerivAt (fun s ↦ contractibleLoopAction σ.val H fun t ↦ w (s, t))
      (∫ t in 0..1, (h.symplecticFormAt (w (s₀, t))).associatedBilinForm (J t)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (1, 0))
        (J t (mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (0, 1) -
          σ.hamiltonianVectorField (H t) (w (s₀, t))))) s₀ := by
  refine (h.hasDerivAt_contractibleLoopAction_of_tames hw hH hwc hper hcap
    fun t ↦ (hJ t).tames).congr_deriv (intervalIntegral.integral_congr fun t _ ↦ ?_)
  simp only [(hJ t).gradientOperator_eq, (hJ t).symmetrizedBilinForm_apply,
    SymplecticForm.associatedBilinForm_apply]
  ring

/-- **The weak gradient of the action relative to a reference loop for tame almost complex
structures.** Let `σ` be a nondegenerate two-form vanishing on tori, `H` a jointly `C¹`
time-dependent Hamiltonian and `w` a smooth variation through loops, `1`-periodic in `t`, whose loop
`w (s₀, ·)` is joined to the reference loop `γ₀` by a smooth cylinder. Let `J_t` be almost complex
structures on `T_{w(s₀, t)} M` tamed by `σ`, with symmetric metrics `gₛ` and gradient operators
`A_t`. Then the action of the loops `w (s, ·)` relative to `γ₀` has derivative
`∫₀¹ gₛ(∂_s w, A_t (∂_t w - X_{H_t}(w))) / 2 dt` at `s₀`, with all terms taken at `(s₀, t)`. -/
theorem SmoothTwoForm.IsNondegenerate.hasDerivAt_referenceAction_of_tames
    {γ₀ : ℝ → M} (h : σ.IsNondegenerate) (hT : VanishesOnTori σ.val)
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hwc : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ w)
    (hper : ∀ z : ℝ × ℝ, w (z.1, z.2 + 1) = w z) {s₀ : ℝ}
    (hcyl : ∃ u, IsSmoothCylinder I (fun t ↦ w (s₀, t)) γ₀ u)
    {J : (t : ℝ) → AlmostComplexStructure (TangentSpace I (w (s₀, t)))}
    (hJ : ∀ t, (h.symplecticFormAt (w (s₀, t))).Tames (J t)) :
    HasDerivAt (fun s ↦ σ.referenceAction H γ₀ fun t ↦ w (s, t))
      (∫ t in 0..1, (h.symplecticFormAt (w (s₀, t))).symmetrizedBilinForm (J t)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (1, 0))
        ((hJ t).gradientOperator (mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (0, 1) -
          σ.hamiltonianVectorField (H t) (w (s₀, t)))) / 2) s₀ :=
  (h.hasDerivAt_referenceAction hT hH hwc hper hcyl).congr_deriv <|
    intervalIntegral.integral_congr fun t _ ↦
      h.apply_eq_symmetrizedBilinForm_gradientOperator (hJ t) _ _

end TauCeti
