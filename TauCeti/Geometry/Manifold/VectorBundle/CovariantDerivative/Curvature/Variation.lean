/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Ricci
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Parametric
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Topology.Algebra.Module.Trace

/-!
# The first variation of the curvature of a family of connections

Let `∇ˢ` be a one-parameter family of covariant derivatives on the tangent bundle of `M`. The
difference `∇ˢ - ∇ᵗ` is a tensor, Mathlib's `CovariantDerivative.difference`, vanishing at
`s = t`; write `Γ'` for its derivative at `s = t`, so that `Γ'(Z, Y) = ∂ₛ ∇ˢ_Y Z` at `s = t`. With
the convention of `CovariantDerivative.addOneForm`, `Γ'(Z, Y)` is the one-form `Γ'` evaluated on the
direction `Y` and applied to `Z`. This file proves that if `∇ᵗ` is torsion free at `x`, then the
curvature `R^s(X, Y) Z` varies by

`∂ₛ R^s(X, Y) Z = (∇ᵗ_X Γ')(Z, Y) - (∇ᵗ_Y Γ')(Z, X)` at `s = t`,

where `(∇_X Γ')(Z, Y) = ∇_X (Γ'(Z, Y)) - Γ'(∇_X Z, Y) - Γ'(Z, ∇_X Y)` is the covariant derivative of
`Γ'` as a tensor. This is the linearization at `A = 0` of the curvature of `∇ + A`
(`CovariantDerivative.curvatureOperator_addOneForm_of_torsion_eq_zero`).

The family is only required to be differentiable in `s` through its difference tensor, and the
vector fields `∇ˢ_X Z` and `∇ˢ_Y Z` to be jointly `C²` in `(s, y)`; the step which commutes the
parameter derivative with the outer covariant derivative `∇ᵗ_X` is
`CovariantDerivative.hasDerivAt_apply_of_contMDiffAt`, and the parameter derivatives of
`∇ˢ_v σ` and `∇ˢ_v (∇ˢ_Y Z)` are
`TauCeti.Manifold.hasDerivAt_covariantDerivative_apply_of_hasDerivAt_difference` and
`TauCeti.Manifold.hasDerivAt_covariantDerivative_covariantDerivative_of_hasDerivAt_difference`.
No metric is involved.

When the vector fields `∇ˢ_X Z` are jointly `C²` for all smooth `X` and `Z`, `Γ'` is a
differentiable section of `Hom(TM, Hom(TM, TM))`, since on a local frame it is the parameter
derivative of `∇ˢ_X Z`
(`TauCeti.Manifold.mdifferentiableAt_deriv_difference_of_hasDerivAt_difference`). Then `∇ᵗΓ'`
is the covariant derivative of `Γ'` for the connection induced by `∇ᵗ` on this iterated Hom
bundle (`CovariantDerivative.hom`), and the formula becomes the pointwise identity

`∂ₛ R^s(u, v) w = (∇ᵗ_u Γ')(w, v) - (∇ᵗ_v Γ')(w, u)`

for the curvature tensors `R^s` at a point. Since `Ric(u, v) = tr (w ↦ R(w, u) v)`, the parameter
derivative of the Ricci tensor is the trace of that of the curvature tensor; this needs neither a
metric nor vanishing torsion. Contracting the curvature formula gives the Palatini identity

`∂ₛ Ric^s(u, v) = tr (w ↦ (∇ᵗ_w Γ')(v, u)) - tr (w ↦ (∇ᵗ_u Γ')(v, w))` at `s = t`.

## Main results

* `TauCeti.Manifold.hasDerivAt_curvatureOperator_of_hasDerivAt_difference`: the first variation
  of the curvature of a family of connections.
* `TauCeti.Manifold.hasDerivAt_curvatureTensor_of_hasDerivAt_difference`: the first variation of
  the curvature tensor at a point, in terms of the covariant derivative of `Γ'`.
* `TauCeti.Manifold.hasDerivAt_ricciTensor_of_hasDerivAt_curvatureTensor`: the first variation of
  the Ricci tensor is the trace of that of the curvature tensor.
* `TauCeti.Manifold.hasDerivAt_ricciTensor_of_hasDerivAt_difference`: the Palatini identity for
  the first variation of the Ricci tensor of a family of connections, and
  `TauCeti.Manifold.hasDerivAt_ricciTensor_sum_of_hasDerivAt_difference` its form in a basis.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.K, Theorem 1.174(b).
* B. Chow and D. Knopf, *The Ricci Flow: An Introduction*, AMS (2004), Chapter 3, Lemma 3.2.
-/

public section

noncomputable section

open Bundle FiberBundle Filter VectorField
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {C : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x}
  {t : ℝ} {x : M}

/-- **The first variation of the curvature of a family of connections.** Let `∇ˢ` be a family of
covariant derivatives on `TM` whose difference tensors `∇ˢ - ∇ᵗ` have derivative `Γ'` at `s = t`
near `x`, with `∇ᵗ` torsion free at `x`. Let `X`, `Y` be differentiable at `x`, let `Z` be
differentiable near `x`, and let `∇ˢ_X Z` and `∇ˢ_Y Z` be jointly `C²` in `(s, y)` at `(t, x)`.
Then the curvature `R^s(X, Y) Z` at `x` has parameter derivative

`(∇ᵗ_X Γ')(Z, Y) - (∇ᵗ_Y Γ')(Z, X)`

at `t`, where `(∇_X Γ')(Z, Y) = ∇_X (Γ'(Z, Y)) - Γ'(∇_X Z, Y) - Γ'(Z, ∇_X Y)` and `Γ'(Z, Y)` is the
one-form `Γ'` evaluated on `Y` and applied to `Z`, so that `Γ'(Z, Y) = ∂ₛ ∇ˢ_Y Z`. -/
theorem hasDerivAt_curvatureOperator_of_hasDerivAt_difference [IsManifold I 2 M]
    {cov : ℝ → CovariantDerivative I E (TangentSpace I : M → Type _)}
    (hC : ∀ᶠ y in 𝓝 x, HasDerivAt (fun s ↦ (cov s).difference (cov t) y) (C y) t)
    (htors : (cov t).torsion x = 0) {X Y Z : Π y : M, TangentSpace I y}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : ∀ᶠ y in 𝓝 x, MDiffAt (T% Z) y)
    (hXZ : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) 2
      (fun q : ℝ × M ↦ TotalSpace.mk' E q.2 (cov q.1 Z q.2 (X q.2))) (t, x))
    (hYZ : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) 2
      (fun q : ℝ × M ↦ TotalSpace.mk' E q.2 (cov q.1 Z q.2 (Y q.2))) (t, x)) :
    HasDerivAt (fun s ↦ (cov s).curvatureOperator X Y Z x)
      ((cov t (fun y ↦ C y (Z y) (Y y)) x (X x) - C x (cov t Z x (X x)) (Y x) -
          C x (Z x) (cov t Y x (X x))) -
        (cov t (fun y ↦ C y (Z y) (X y)) x (Y x) - C x (cov t Z x (Y x)) (X x) -
          C x (Z x) (cov t X x (Y x)))) t := by
  have hY' :=
    hasDerivAt_covariantDerivative_covariantDerivative_of_hasDerivAt_difference hC hZ hYZ (X x)
  have hX' :=
    hasDerivAt_covariantDerivative_covariantDerivative_of_hasDerivAt_difference hC hZ hXZ (Y x)
  have hbr := hasDerivAt_covariantDerivative_apply_of_hasDerivAt_difference hC.self_of_nhds
    hZ.self_of_nhds (mlieBracket I X Y x)
  -- The Lie bracket is `∇ᵗ_X Y - ∇ᵗ_Y X`, since `∇ᵗ` is torsion free at `x`.
  have hb : mlieBracket I X Y x = cov t Y x (X x) - cov t X x (Y x) := by
    have h := (cov t).torsion_apply hX hY
    simp only [htors, zero_apply] at h
    exact (sub_eq_zero.mp h.symm).symm
  refine (((hY'.sub hX').sub hbr).congr_deriv ?_).congr_of_eventuallyEq
    (Eventually.of_forall fun s ↦ CovariantDerivative.curvatureOperator_apply _ _ _ _ _)
  rw [hb, map_sub]
  -- Rearrange the six terms, read in the model space `E`.
  have key (a b c d p q : E) : a - d - p - (c - b - q) = a + b - (c + d) - (p - q) := by abel
  exact (key _ _ _ _ _ _).symm

section Tensor

variable [T2Space M] [IsManifold I ∞ M]
  {cov : ℝ → CovariantDerivative I E (TangentSpace I : M → Type _)}
  [∀ s, CovariantDerivative.ContMDiffCovariantDerivative (cov s) ∞]

/-- **The first variation of the curvature tensor of a family of connections.** Let `∇ˢ` be a
family of smooth covariant derivatives on `TM` whose difference tensors `∇ˢ - ∇ᵗ` have derivative
`Γ'` at `s = t` near `x`, with `∇ᵗ` torsion free at `x`. Suppose that for smooth vector fields `X`
and `Z` the vector fields `∇ˢ_X Z` are jointly `C²` in `(s, y)` at `(t, x)`; then `Γ'` is a section
of `Hom(TM, Hom(TM, TM))` differentiable at `x`. Write `∇ᵗΓ'` for the covariant derivative of
`Γ'` along the connection induced by `∇ᵗ` on `Hom(TM, Hom(TM, TM))`, so that `∇ᵗΓ' x u w v` is
`(∇ᵗ_u Γ')(w, v)`. Then for `u, v, w ∈ T_x M` the curvature tensors satisfy

`∂ₛ R^s(u, v) w = (∇ᵗ_u Γ')(w, v) - (∇ᵗ_v Γ')(w, u)` at `s = t`. -/
theorem hasDerivAt_curvatureTensor_of_hasDerivAt_difference
    (hC : ∀ᶠ y in 𝓝 x, HasDerivAt (fun s ↦ (cov s).difference (cov t) y) (C y) t)
    (htors : (cov t).torsion x = 0)
    (hreg : ∀ X Z : Π y : M, TangentSpace I y, CMDiff ∞ (T% X) → CMDiff ∞ (T% Z) →
      ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) 2
        (fun q : ℝ × M ↦ TotalSpace.mk' E q.2 (cov q.1 Z q.2 (X q.2))) (t, x))
    (u v w : TangentSpace I x) :
    HasDerivAt (fun s ↦ (cov s).curvatureTensor x u v w)
      ((cov t).hom ((cov t).hom (cov t)) C x u w v -
        (cov t).hom ((cov t).hom (cov t)) C x v w u) t := by
  obtain ⟨X, hX, rfl⟩ := exists_contMDiff_section_eq I E ∞ u
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E ∞ v
  obtain ⟨Z, hZ, rfl⟩ := exists_contMDiff_section_eq I E ∞ w
  have hXd := (hX x).mdifferentiableAt (by simp)
  have hYd := (hY x).mdifferentiableAt (by simp)
  have hZd := (hZ x).mdifferentiableAt (by simp)
  have hCd := mdifferentiableAt_deriv_difference_of_hasDerivAt_difference hC hreg
  rw [CovariantDerivative.hom_hom_apply _ _ _ hCd hZd hYd,
    CovariantDerivative.hom_hom_apply _ _ _ hCd hZd hXd]
  simp_rw [CovariantDerivative.curvatureTensor_apply _ x hX hY hZ]
  exact hasDerivAt_curvatureOperator_of_hasDerivAt_difference hC htors hXd hYd
    (Eventually.of_forall fun y ↦ (hZ y).mdifferentiableAt (by simp)) (hreg X Z hX hZ)
    (hreg Y Z hY hZ)

/-- **The first variation of the Ricci tensor is the trace of that of the curvature tensor.** Let
`∇ˢ` be a family of smooth covariant derivatives on `TM`, and let `u, v ∈ T_x M`. If for every
`w ∈ T_x M` the curve `s ↦ R^s(w, u) v` has derivative `D w` at `t`, for a linear map `D` of
`T_x M`, then `s ↦ Ric^s(u, v)` has derivative `tr D` at `t`. Neither a metric nor vanishing
torsion is needed. -/
theorem hasDerivAt_ricciTensor_of_hasDerivAt_curvatureTensor {u v : TangentSpace I x}
    {D : TangentSpace I x →ₗ[ℝ] TangentSpace I x}
    (hD : ∀ w, HasDerivAt (fun s ↦ (cov s).curvatureTensor x w u v) (D w) t) :
    HasDerivAt (fun s ↦ (cov s).ricciTensor x u v) (LinearMap.trace ℝ (TangentSpace I x) D) t := by
  -- The tangent space at `x` is the model space `E`, whose normed structure differentiates
  -- endomorphisms and their trace.
  let R : ℝ → E →L[ℝ] E := fun s ↦ LinearMap.toContinuousLinearMap
    ((((cov s).curvatureTensor x).flip u).flip v : E →ₗ[ℝ] E)
  have hR : HasDerivAt R (LinearMap.toContinuousLinearMap (D : E →ₗ[ℝ] E)) t :=
    hasDerivAt_clm_apply.mpr hD
  have h := (traceCLM ℝ E).hasFDerivAt.comp_hasDerivAt t hR
  simp only [R, Function.comp_def, traceCLM_apply] at h
  simp only [CovariantDerivative.ricciTensor_apply]
  exact h

/-- **The Palatini identity for a family of connections.** In the setting of
`hasDerivAt_curvatureTensor_of_hasDerivAt_difference`, write `∇ᵗΓ'` for the covariant derivative
of `Γ'` along the connection induced by `∇ᵗ` on `Hom(TM, Hom(TM, TM))`, so that `∇ᵗΓ' x u w v` is
`(∇ᵗ_u Γ')(w, v)`. Then for `u, v ∈ T_x M`,

`∂ₛ Ric^s(u, v) = tr (w ↦ (∇ᵗ_w Γ')(v, u)) - tr (w ↦ (∇ᵗ_u Γ')(v, w))` at `s = t`.

The first trace is that of the endomorphism `w ↦ ∇ᵗΓ' x w v u`, obtained from `∇ᵗΓ' x` by
flipping its arguments, and the second that of `∇ᵗΓ' x u v`. No metric is involved. -/
theorem hasDerivAt_ricciTensor_of_hasDerivAt_difference
    (hC : ∀ᶠ y in 𝓝 x, HasDerivAt (fun s ↦ (cov s).difference (cov t) y) (C y) t)
    (htors : (cov t).torsion x = 0)
    (hreg : ∀ X Z : Π y : M, TangentSpace I y, CMDiff ∞ (T% X) → CMDiff ∞ (T% Z) →
      ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) 2
        (fun q : ℝ × M ↦ TotalSpace.mk' E q.2 (cov q.1 Z q.2 (X q.2))) (t, x))
    (u v : TangentSpace I x) :
    HasDerivAt (fun s ↦ (cov s).ricciTensor x u v)
      (LinearMap.trace ℝ (TangentSpace I x)
          (((((cov t).hom ((cov t).hom (cov t)) C x).toLinearMap₁₂.compr₂
              (ContinuousLinearMap.coeLM ℝ)).flip v).flip u) -
        LinearMap.trace ℝ (TangentSpace I x) ((cov t).hom ((cov t).hom (cov t)) C x u v)) t := by
  rw [← map_sub]
  refine hasDerivAt_ricciTensor_of_hasDerivAt_curvatureTensor fun w ↦ ?_
  simpa using hasDerivAt_curvatureTensor_of_hasDerivAt_difference hC htors hreg w u v

/-- **The Palatini identity for a family of connections, in a basis.** In the setting of
`hasDerivAt_ricciTensor_of_hasDerivAt_difference`, for every basis `b` of `T_x M`,

`∂ₛ Ric^s(u, v) = ∑ᵢ bᵢ* ((∇ᵗ_{bᵢ} Γ')(v, u) - (∇ᵗ_u Γ')(v, bᵢ))` at `s = t`,

where `bᵢ*` is the `i`-th coordinate in `b`. -/
theorem hasDerivAt_ricciTensor_sum_of_hasDerivAt_difference
    (hC : ∀ᶠ y in 𝓝 x, HasDerivAt (fun s ↦ (cov s).difference (cov t) y) (C y) t)
    (htors : (cov t).torsion x = 0)
    (hreg : ∀ X Z : Π y : M, TangentSpace I y, CMDiff ∞ (T% X) → CMDiff ∞ (T% Z) →
      ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) 2
        (fun q : ℝ × M ↦ TotalSpace.mk' E q.2 (cov q.1 Z q.2 (X q.2))) (t, x))
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ (TangentSpace I x)) (u v : TangentSpace I x) :
    HasDerivAt (fun s ↦ (cov s).ricciTensor x u v)
      (∑ i, b.repr ((cov t).hom ((cov t).hom (cov t)) C x (b i) v u -
        (cov t).hom ((cov t).hom (cov t)) C x u v (b i)) i) t := by
  classical
  refine (hasDerivAt_ricciTensor_of_hasDerivAt_difference hC htors hreg u v).congr_deriv ?_
  rw [← map_sub, LinearMap.trace_eq_matrix_trace ℝ b]
  simp [Matrix.trace, LinearMap.toMatrix_apply]

end Tensor

end TauCeti.Manifold
