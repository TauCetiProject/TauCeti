/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Nondegenerate.CurvatureVariation
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Ricci

/-!
# The first variation of the Ricci tensor of a family of nondegenerate metrics

Let `g` be a smooth family of nondegenerate metrics on `M`, of any signature, parametrized by a
manifold `P`, let `c` be a parameter curve which is `C²` at `t`, and let `∇ˢ` be a Levi-Civita
connection of `g_{c s}` for every `s`. Write `Γ'` for the derivative at `s = t` of the difference
tensors `∇ˢ - ∇ᵗ`, the variation of the Levi-Civita connection, so that `Γ'(Z, Y) = ∂ₛ ∇ˢ_Y Z`, and
`∇ᵗΓ'` for its covariant derivative, with `(∇ᵗ_u Γ')(w, v)` the value `∇ᵗΓ' x u w v` of the
connection induced by `∇ᵗ` on `Hom(TM, Hom(TM, TM))`. This file proves the **Palatini identity**

`∂ₛ Ric^s(u, v) = tr (w ↦ (∇ᵗ_w Γ')(v, u)) - tr (w ↦ (∇ᵗ_u Γ')(v, w))` at `s = t`,

in index notation `∂ₜ R_ij = ∇_k Γ'^k_ij - ∇_i Γ'^k_kj` with `Γ'(∂_j, ∂_i) = Γ'^k_ij ∂_k`. The
traces are written as sums of coordinates in an arbitrary basis of `T_x M`, as in
`CovariantDerivative.ricciTensor_eq_sum`. It is
the contraction of the pointwise curvature variation
`ContMDiffNondegenerateMetricFamily.hasDerivAt_curvatureTensor_of_isLeviCivitaConnection`, since
`Ric(u, v) = tr (w ↦ R(w, u) v)`.

Combined with the first variation formula of the Levi-Civita connection
(`ContMDiffNondegenerateMetricFamily.two_mul_apply_deriv_difference_eq_derivBilinearTensor`), which
expresses `Γ'` through the covariant derivative of `h = ∂ₜ g`, this is the starting point of the
variation formulas for the Ricci and scalar curvature along a family of metrics. As a first
consequence, the Ricci tensor is stationary to first order where the metric variation is parallel,
for instance along the conformal variation `h = λ g` by a constant `λ`.

## Main results

In the namespace `TauCeti.Manifold.ContMDiffNondegenerateMetricFamily`:

* `hasDerivAt_ricciTensor_of_isLeviCivitaConnection`: the Palatini identity for the first
  variation of the Ricci tensor.
* `hasDerivAt_ricciTensor_zero_of_derivBilinearTensor_eq_zero`: the Ricci tensor has zero first
  variation at points near which the metric variation is parallel.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.K, Theorem 1.174.
* B. Chow and D. Knopf, *The Ricci Flow: An Introduction*, AMS (2004), Chapter 3.
* P. Topping, *Lectures on the Ricci Flow*, LMS Lecture Note Series 325, CUP (2006), Section 2.3.
-/

public section

noncomputable section

open Bundle Filter
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold.ContMDiffNondegenerateMetricFamily

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP 1 P]
  (g : ContMDiffNondegenerateMetricFamily I M IP P) {c : ℝ → P}
  {cov : ℝ → CovariantDerivative I E (fun x : M ↦ TangentSpace I x)} {t : ℝ}
  [∀ s, CovariantDerivative.ContMDiffCovariantDerivative (cov s) ∞]

/-- **The Palatini identity: the first variation of the Ricci tensor.** Let `g` be a smooth family
of nondegenerate metrics parametrized by `P`, let `c` be a parameter curve which is `C²` at `t`,
and let `∇ˢ` be a Levi-Civita connection of `g_{c s}` for every `s`. Write `Γ'` for the
derivative at `t` of the difference tensors `∇ˢ - ∇ᵗ`, and `∇ᵗΓ'` for its covariant derivative
along the connection induced by `∇ᵗ` on `Hom(TM, Hom(TM, TM))`, so that `∇ᵗΓ' x u w v` is
`(∇ᵗ_u Γ')(w, v)`. Then for `u, v ∈ T_x M` and every basis `b` of `T_x M`,

`∂ₛ Ric^s(u, v) = ∑ᵢ bᵢ* ((∇ᵗ_{bᵢ} Γ')(v, u) - (∇ᵗ_u Γ')(v, bᵢ))` at `s = t`,

where `bᵢ*` is the `i`-th coordinate in `b`; that is,
`∂ₛ Ric^s(u, v) = tr (w ↦ (∇ᵗ_w Γ')(v, u)) - tr (w ↦ (∇ᵗ_u Γ')(v, w))`.

The smoothness instances of the connections `∇ˢ` are needed to state the Ricci tensor; they hold
for Levi-Civita connections of smooth metrics by
`ContMDiffNondegenerateMetric.IsLeviCivitaConnection.contMDiffCovariantDerivative`. -/
theorem hasDerivAt_ricciTensor_of_isLeviCivitaConnection
    (hc : ContMDiffAt 𝓘(ℝ) IP 2 c t)
    (hcov : ∀ s, (g.metric (c s)).IsLeviCivitaConnection (cov s)) (x : M)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ (TangentSpace I x)) (u v : TangentSpace I x) :
    HasDerivAt (fun s ↦ (cov s).ricciTensor x u v)
      (∑ i, b.repr ((cov t).hom ((cov t).hom (cov t))
          (fun y ↦ deriv (fun s ↦ (cov s).difference (cov t) y) t) x (b i) v u -
        (cov t).hom ((cov t).hom (cov t))
          (fun y ↦ deriv (fun s ↦ (cov s).difference (cov t) y) t) x u v (b i)) i) t := by
  -- The tangent space at `x` is the model space `E`, whose normed structure differentiates the
  -- coordinate functionals of `b`.
  let b' : Module.Basis ι ℝ E := b
  refine (HasDerivAt.fun_sum fun i _ ↦ ?_).congr_of_eventuallyEq
    (Eventually.of_forall fun s ↦ CovariantDerivative.ricciTensor_eq_sum (cov s) x b u v)
  exact (LinearMap.toContinuousLinearMap (b'.coord i)).hasFDerivAt.comp_hasDerivAt t
    (g.hasDerivAt_curvatureTensor_of_isLeviCivitaConnection hc hcov x (b i) u v)

/-- **The Ricci tensor is stationary where the metric variation is parallel.** Let `g` be a
smooth family of nondegenerate metrics parametrized by `P`, let `c` be a parameter curve which is
`C²` at `t`, and let `∇ˢ` be a Levi-Civita connection of `g_{c s}` for every `s`. If the first
variation `h = δ_{c'(t)} g` is parallel for `∇ᵗ` near `x`, as for the conformal variation
`h = λ g_{c t}` by a constant `λ`, then `s ↦ Ric^s_x(u, v)` has derivative zero at `t`. -/
theorem hasDerivAt_ricciTensor_zero_of_derivBilinearTensor_eq_zero
    (hc : ContMDiffAt 𝓘(ℝ) IP 2 c t)
    (hcov : ∀ s, (g.metric (c s)).IsLeviCivitaConnection (cov s)) {x : M}
    (hh : ∀ᶠ y in 𝓝 x,
      (cov t).derivBilinearTensor (g.variation (c t) (mfderiv 𝓘(ℝ) IP c t 1)) y = 0)
    (u v : TangentSpace I x) :
    HasDerivAt (fun s ↦ (cov s).ricciTensor x u v) 0 t := by
  -- `Γ'` vanishes near `x`, so its covariant derivative vanishes at `x`.
  have hD : (cov t).hom ((cov t).hom (cov t))
      (fun y ↦ deriv (fun s ↦ (cov s).difference (cov t) y) t) x = 0 := by
    rw [((cov t).hom ((cov t).hom (cov t))).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      ((g.contMDiff_deriv_difference_of_isLeviCivitaConnection hc hcov x).mdifferentiableAt
        one_ne_zero) (mdifferentiableAt_zeroSection ℝ _) Filter.univ_mem
      (hh.mono fun y hy ↦ g.deriv_difference_eq_zero_of_derivBilinearTensor_eq_zero hc hcov hy)]
    exact congrFun (CovariantDerivative.zero _) x
  simpa [hD] using g.hasDerivAt_ricciTensor_of_isLeviCivitaConnection hc hcov x
    (Module.finBasis ℝ E) u v

end TauCeti.Manifold.ContMDiffNondegenerateMetricFamily
