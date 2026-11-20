/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.ContractibleAction.FirstVariation
public import TauCeti.Geometry.Symplectic.TameMetric

/-!
# The gradient of the action functional for tame almost complex structures

Let `σ` be a nondegenerate weakly exact two-form on a finite-dimensional manifold `M` and `H` a
time-dependent Hamiltonian. Along a `C²` variation `w` through loops `γ_s = w (s, ·)`, the first
variation formula (`TauCeti.SmoothTwoForm.IsNondegenerate.hasDerivAt_contractibleLoopAction`) is

`d/ds A_H(γ_s) = ∫₀¹ σ(∂_t w - X_{H_t}(w), ∂_s w) dt`.

To read the integrand as a metric pairing of `∂_s w` with a gradient, choose almost complex
structures `J_t` on the tangent spaces `T_{γ(t)} M` tamed by `σ`. The symmetric part
`g_t = gₛ / 2` of `σ(·, J_t ·)`, with `gₛ(v, w) = σ(v, J_t w) + σ(w, J_t v)`, is a metric
(`TauCeti.SymplecticForm.Tames.symmetrizedBilinForm_posDef`), and the integrand is `g_t(∇_t, ∂_s w)`
for

`∇_t = -G_t (∂_t w - X_{H_t})`,

where `G_t` is the gradient for the symmetric metric of the pair `(σ, J_t)`
(`TauCeti.SymplecticForm.Tames.symmetrizedGradient`). So `∇` is the weak `L²` gradient of the
action for the metric `g`
(`TauCeti.SmoothTwoForm.IsNondegenerate.hasDerivAt_contractibleLoopAction_symmetrizedGradient`).

When every `J_t` is compatible with `σ`, `G_t = -J_t` and `g_t = σ(·, J_t ·)`, so the gradient is
`J_t (∂_t w - X_{H_t})`
(`TauCeti.SmoothTwoForm.IsNondegenerate.hasDerivAt_contractibleLoopAction_of_compatible`), and the
Floer equation `∂_s u + J (∂_t u - X_H) = 0` is the negative gradient flow of the action. With the
opposite sign convention for the action, `∫ H_t(γ(t)) dt` plus the area of a cap, the gradient is
`-J_t (∂_t w - X_{H_t})` and Floer cylinders are its positive gradient lines. For a
merely tame `J_t` this fails: `G_t = -J_t` holds exactly when `J_t` is compatible
(`TauCeti.SymplecticForm.Tames.symmetrizedGradient_eq_neg_iff`), and there are tame structures that
are not compatible (`TauCeti.SymplecticForm.exists_symmetrizedGradient_ne_neg`).

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.hasDerivAt_contractibleLoopAction_symmetrizedGradient`:
  the first variation of the action as the pairing with `-G_t (∂_t w - X_{H_t})` for the
  symmetric metric of tame almost complex structures.
* `TauCeti.SmoothTwoForm.IsNondegenerate.hasDerivAt_contractibleLoopAction_of_compatible`: for
  compatible almost complex structures, the pairing with `J_t (∂_t w - X_{H_t})` for the metric
  `σ(·, J_t ·)`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS (2012),
  Section 2.5 (tame almost complex structures and their symmetric metric).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1 (the gradient of the action functional).
-/

public section

open Function Set
open scoped Manifold Interval ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [FiniteDimensional ℝ E] {σ : SmoothTwoForm I M} {Hm : ℝ → M → ℝ}
  {w : ℝ × ℝ → M}

/-- **The gradient of the action for a tame almost complex structure.** Let `σ` be a
nondegenerate weakly exact two-form, `H` a jointly `C¹` time-dependent Hamiltonian and `w` a `C²`
variation through loops, `1`-periodic in `t`, whose loop `w (s₀, ·)` has a cap, and let `J_t` be
almost complex structures on the tangent spaces along that loop, tamed by `σ`. Then the derivative
at `s₀` of the action of the loops `w (s, ·)` is `∫₀¹ g_t(-G_t (∂_t w - X_{H_t}), ∂_s w) dt`, where
`g_t = gₛ / 2` is the symmetric metric of `(σ, J_t)` and `G_t` its gradient
`TauCeti.SymplecticForm.Tames.symmetrizedGradient`, all terms taken at `(s₀, t)`. -/
theorem SmoothTwoForm.IsNondegenerate.hasDerivAt_contractibleLoopAction_symmetrizedGradient
    (h : σ.IsNondegenerate) (hw : IsWeaklyExact σ.1)
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry Hm))
    (hwc : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 w) (hper : ∀ z : ℝ × ℝ, w (z.1, z.2 + 1) = w z)
    {s₀ : ℝ} (hcap : ∃ u, IsCap I u fun t ↦ w (s₀, t))
    (J : ∀ t, AlmostComplexStructure (TangentSpace I (w (s₀, t))))
    (hJ : ∀ t, (h.symplecticFormAt (w (s₀, t))).Tames (J t)) :
    HasDerivAt (fun s ↦ contractibleLoopAction σ.1 Hm fun t ↦ w (s, t))
      (∫ t in 0..1, (h.symplecticFormAt (w (s₀, t))).symmetrizedBilinForm (J t)
        (-(hJ t).symmetrizedGradient
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (0, 1) - σ.hamiltonianVectorField (Hm t) (w (s₀, t))))
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (1, 0)) / 2) s₀ := by
  convert h.hasDerivAt_contractibleLoopAction hw hH hwc hper hcap using 1
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  have hswap := (h.symplecticFormAt (w (s₀, t))).neg_eq (mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (1, 0))
    (mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (0, 1) - σ.hamiltonianVectorField (Hm t) (w (s₀, t)))
  simp only [SmoothTwoForm.IsNondegenerate.symplecticFormAt_apply,
    SmoothBundleForm.eval₂_apply] at hswap
  simp only [map_neg, LinearMap.neg_apply,
    SymplecticForm.Tames.symmetrizedBilinForm_symmetrizedGradient_left,
    SmoothTwoForm.IsNondegenerate.symplecticFormAt_apply, SmoothBundleForm.eval₂_apply]
  linarith

/-- **The gradient of the action for a compatible almost complex structure.** Under the hypotheses
of `TauCeti.SmoothTwoForm.IsNondegenerate.hasDerivAt_contractibleLoopAction_symmetrizedGradient`,
if every `J_t` is compatible with `σ`, the derivative at `s₀` of the action of the loops
`w (s, ·)` is `∫₀¹ g_{J_t}(J_t (∂_t w - X_{H_t}), ∂_s w) dt` for the metric
`g_{J_t} = σ(·, J_t ·)`. -/
theorem SmoothTwoForm.IsNondegenerate.hasDerivAt_contractibleLoopAction_of_compatible
    (h : σ.IsNondegenerate) (hw : IsWeaklyExact σ.1)
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry Hm))
    (hwc : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 2 w) (hper : ∀ z : ℝ × ℝ, w (z.1, z.2 + 1) = w z)
    {s₀ : ℝ} (hcap : ∃ u, IsCap I u fun t ↦ w (s₀, t))
    (J : ∀ t, AlmostComplexStructure (TangentSpace I (w (s₀, t))))
    (hJ : ∀ t, (h.symplecticFormAt (w (s₀, t))).Compatible (J t)) :
    HasDerivAt (fun s ↦ contractibleLoopAction σ.1 Hm fun t ↦ w (s, t))
      (∫ t in 0..1, (h.symplecticFormAt (w (s₀, t))).associatedBilinForm (J t)
        (J t (mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (0, 1) -
          σ.hamiltonianVectorField (Hm t) (w (s₀, t))))
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (1, 0))) s₀ := by
  refine (h.hasDerivAt_contractibleLoopAction_symmetrizedGradient hw hH hwc hper hcap J
    fun t ↦ (hJ t).tames).congr_deriv (intervalIntegral.integral_congr fun t _ ↦ ?_)
  rw [(hJ t).symmetrizedGradient_apply, neg_neg, (hJ t).symmetrizedBilinForm_apply,
    SymplecticForm.associatedBilinForm_apply]
  ring

end TauCeti
