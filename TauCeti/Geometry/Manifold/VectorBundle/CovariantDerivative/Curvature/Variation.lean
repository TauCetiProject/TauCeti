/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Parametric

/-!
# The first variation of the curvature of a family of connections

Let `∇ˢ` be a one-parameter family of covariant derivatives on the tangent bundle of `M`. The
difference `∇ˢ - ∇ᵗ` is a tensor, Mathlib's `CovariantDerivative.difference`, vanishing at
`s = t`; write `Γ'` for its derivative at `s = t`, so that `Γ'(Z, Y) = ∂ₛ ∇ˢ_Y Z` at `s = t`. With
the convention of `CovariantDerivative.addOneForm`, `Γ'(Z, Y)` is the one-form `Γ'` evaluated on the
direction `Y` and applied to `Z`. This file proves that if `∇ᵗ` is torsion free, then the curvature
`R^s(X, Y) Z` varies by

`∂ₛ R^s(X, Y) Z = (∇ᵗ_X Γ')(Z, Y) - (∇ᵗ_Y Γ')(Z, X)` at `s = t`,

where `(∇_X Γ')(Z, Y) = ∇_X (Γ'(Z, Y)) - Γ'(∇_X Z, Y) - Γ'(Z, ∇_X Y)` is the covariant derivative of
`Γ'` as a tensor. This is the linearization at `A = 0` of the curvature of `∇ + A`
(`CovariantDerivative.curvatureOperator_addOneForm_of_torsion_eq_zero`).

The family is only required to be differentiable in `s` through its difference tensor, and the
vector fields `∇ˢ_X Z` and `∇ˢ_Y Z` to be jointly `C²` in `(s, y)`; the step which commutes the
parameter derivative with the outer covariant derivative `∇ᵗ_X` is
`TauCeti.Manifold.hasDerivAt_covariantDerivative_apply_of_contMDiffAt`. No metric is involved.

## Main results

* `TauCeti.Manifold.hasDerivAt_curvatureOperator_of_hasDerivAt_difference`: the first variation
  of the curvature of a family of connections.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.K, Theorem 1.174(b).
* B. Chow and D. Knopf, *The Ricci Flow: An Introduction*, AMS (2004), Chapter 3, Lemma 3.2.
-/

public section

noncomputable section

open Bundle Filter VectorField
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {cov : ℝ → CovariantDerivative I E (TangentSpace I : M → Type _)}
  {C : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x}
  {t : ℝ} {x : M}

/-- A covariant derivative of the family is the one at `t` plus the difference tensor. -/
private theorem apply_eq_apply_add_difference {σ : Π y : M, TangentSpace I y} {y : M}
    (hσ : MDiffAt (T% σ) y) (s : ℝ) (v : TangentSpace I y) :
    cov s σ y v = cov t σ y v + (cov s).difference (cov t) y (σ y) v := by
  rw [CovariantDerivative.difference_apply _ _ hσ]
  simp

/-- The parameter derivative of `∇ˢ_v σ` at `y` is `Γ'(σ, v)`, for `σ` differentiable at `y`. -/
private theorem hasDerivAt_apply_of_hasDerivAt_difference {σ : Π y : M, TangentSpace I y}
    {y : M} (hC : HasDerivAt (fun s ↦ (cov s).difference (cov t) y) (C y) t)
    (hσ : MDiffAt (T% σ) y) (v : TangentSpace I y) :
    HasDerivAt (F := E) (fun s ↦ cov s σ y v) (C y (σ y) v) t := by
  -- The tangent space at `y` is read as the model space `E`.
  have hC' : HasDerivAt (F := E →L[ℝ] E →L[ℝ] E) (fun s ↦ (cov s).difference (cov t) y) (C y) t :=
    hC
  have h := (TauCeti.hasDerivAt_clm_apply₂ (F := E) (F' := E) (G := E)).mp hC' (σ y) v
  exact (HasDerivAt.const_add (F := E) (cov t σ y v) h).congr_of_eventuallyEq
    (Eventually.of_forall fun s ↦ apply_eq_apply_add_difference hσ s v)

/-- The parameter derivative of the second covariant derivative `∇ˢ_v (∇ˢ_Y Z)` at `x`, for a
family whose vector fields `∇ˢ_Y Z` are jointly `C²`. -/
private theorem hasDerivAt_apply_apply_of_hasDerivAt_difference
    (hC : ∀ᶠ y in 𝓝 x, HasDerivAt (fun s ↦ (cov s).difference (cov t) y) (C y) t)
    {Y Z : Π y : M, TangentSpace I y} (hZ : ∀ᶠ y in 𝓝 x, MDiffAt (T% Z) y)
    (hYZ : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) 2
      (fun q : ℝ × M ↦ TotalSpace.mk' E q.2 (cov q.1 Z q.2 (Y q.2))) (t, x))
    (v : TangentSpace I x) :
    HasDerivAt (F := E) (fun s ↦ cov s (fun y ↦ cov s Z y (Y y)) x v)
      (cov t (fun y ↦ C y (Z y) (Y y)) x v + C x (cov t Z x (Y x)) v) t := by
  -- The vector fields `∇ˢ_Y Z` near `t`, and their parameter derivative `Γ'(Z, Y)`.
  have h1 := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).mp (hYZ.of_le (by norm_num))
  have hslice : ∀ᶠ s in 𝓝 t, MDiffAt (T% (fun y ↦ cov s Z y (Y y))) x :=
    ((continuous_id.prodMk continuous_const).continuousAt.eventually h1).mono fun s hs ↦
      (hs.comp x (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt one_ne_zero
  have hderiv : ∀ᶠ y in 𝓝 x, deriv (fun s ↦ cov s Z y (Y y)) t = C y (Z y) (Y y) := by
    filter_upwards [hC, hZ] with y hy hZy
    exact HasDerivAt.deriv (F := E) (hasDerivAt_apply_of_hasDerivAt_difference hy hZy (Y y))
  have hreg := (contMDiffAt_deriv_vectorField_of_contMDiffAt
    (W := fun s y ↦ cov s Z y (Y y)) hYZ (m := 1) (by norm_num)).mdifferentiableAt one_ne_zero
  -- The outer covariant derivative along `∇ᵗ`, commuted with the parameter derivative ...
  have hout := hasDerivAt_covariantDerivative_apply_of_contMDiffAt
    (W := fun s y ↦ cov s Z y (Y y)) (cov t) hYZ v
  rw [(cov t).isCovariantDerivativeOnUniv.congr_of_eventuallyEq hreg
    (hreg.congr_of_eventuallyEq (hderiv.mono fun y hy ↦ by simp only [hy]))
    Filter.univ_mem hderiv] at hout
  -- ... plus the difference tensor applied to `∇ˢ_Y Z`.
  have hval : HasDerivAt (F := E) (fun s ↦ cov s Z x (Y x)) (C x (Z x) (Y x)) t :=
    hasDerivAt_apply_of_hasDerivAt_difference hC.self_of_nhds hZ.self_of_nhds (Y x)
  have hCx : HasDerivAt (F := E →L[ℝ] E →L[ℝ] E) (fun s ↦ (cov s).difference (cov t) x) (C x) t :=
    hC.self_of_nhds
  have hdiff := HasDerivAt.clm_apply (F := E) (G := E)
    (HasDerivAt.clm_apply (F := E) (G := E →L[ℝ] E) hCx hval) (hasDerivAt_const (F := E) t v)
  -- The difference tensor vanishes at `s = t`.
  have h0 (D : E →L[ℝ] E →L[ℝ] E) (hD : D = 0) (a : E →L[ℝ] E) (b c : E) :
      (a + D b) v + D c 0 = a v := by
    simp [hD]
  refine (HasDerivAt.add (F := E) hout (hdiff.congr_deriv (h0 _ ?_ _ _ _)))
    |>.congr_of_eventuallyEq ?_
  · exact congrFun (CovariantDerivative.difference_self (cov t)) x
  filter_upwards [hslice] with s hs
  exact apply_eq_apply_add_difference hs s v

/-- **The first variation of the curvature of a family of connections.** Let `∇ˢ` be a family of
covariant derivatives on `TM` whose difference tensors `∇ˢ - ∇ᵗ` have derivative `Γ'` at `s = t`
near `x`, with `∇ᵗ` torsion free. Let `X`, `Y` be differentiable at `x`, let `Z` be
differentiable near `x`, and let `∇ˢ_X Z` and `∇ˢ_Y Z` be jointly `C²` in `(s, y)` at `(t, x)`.
Then the curvature `R^s(X, Y) Z` at `x` has parameter derivative

`(∇ᵗ_X Γ')(Z, Y) - (∇ᵗ_Y Γ')(Z, X)`

at `t`, where `(∇_X Γ')(Z, Y) = ∇_X (Γ'(Z, Y)) - Γ'(∇_X Z, Y) - Γ'(Z, ∇_X Y)` and `Γ'(Z, Y)` is the
one-form `Γ'` evaluated on `Y` and applied to `Z`, so that `Γ'(Z, Y) = ∂ₛ ∇ˢ_Y Z`. -/
theorem hasDerivAt_curvatureOperator_of_hasDerivAt_difference
    (hC : ∀ᶠ y in 𝓝 x, HasDerivAt (fun s ↦ (cov s).difference (cov t) y) (C y) t)
    (htors : (cov t).torsion = 0) {X Y Z : Π y : M, TangentSpace I y}
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
  have hY' := hasDerivAt_apply_apply_of_hasDerivAt_difference hC hZ hYZ (X x)
  have hX' := hasDerivAt_apply_apply_of_hasDerivAt_difference hC hZ hXZ (Y x)
  have hbr := hasDerivAt_apply_of_hasDerivAt_difference hC.self_of_nhds hZ.self_of_nhds
    (mlieBracket I X Y x)
  -- The Lie bracket is `∇ᵗ_X Y - ∇ᵗ_Y X`, since `∇ᵗ` is torsion free.
  have hb : mlieBracket I X Y x = cov t Y x (X x) - cov t X x (Y x) :=
    ((CovariantDerivative.torsion_eq_zero_iff (cov t)).1 htors hX hY).symm
  refine (((hY'.sub hX').sub hbr).congr_deriv ?_).congr_of_eventuallyEq
    (Eventually.of_forall fun s ↦ CovariantDerivative.curvatureOperator_apply _ _ _ _ _)
  rw [hb, map_sub]
  -- Rearrange the six terms, read in the model space `E`.
  have key (a b c d p q : E) : a - d - p - (c - b - q) = a + b - (c + d) - (p - q) := by abel
  exact (key _ _ _ _ _ _).symm

end TauCeti.Manifold
