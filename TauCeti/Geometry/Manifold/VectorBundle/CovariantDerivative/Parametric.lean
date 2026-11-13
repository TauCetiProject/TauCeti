/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
public import TauCeti.Geometry.Manifold.MFDeriv.Parametric.Basic
import TauCeti.Geometry.Manifold.VectorField.Parametric
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap

/-!
# Covariant derivatives of one-parameter families of vector fields

Let `∇` be a covariant derivative on the tangent bundle of a finite-dimensional manifold `M`, and
let `W_s` be a one-parameter family of vector fields which is jointly `C²` in `(s, y)` at
`(t, x)`, as a map into the tangent bundle. This file proves that the parameter derivative
commutes with `∇` at `x`:

`∂ₛ (∇_v W_s)(x) = ∇_v (∂ₛ W_s)(x)` at `s = t`.

No regularity of `∇` is needed: in the trivialization at `x`, `∇_v W_s` is the differential of the
coordinates of `W_s` plus the Christoffel map applied to the value of `W_s` at `x`
(`TauCeti.Manifold.covariantDerivative_symm_comp_apply_symm`). The parameter derivative of the
first term is the differential of the parameter derivative, by the symmetry of mixed partial
derivatives `TauCeti.Manifold.hasDerivAt_mvfderiv_apply`, and the second term is linear in the
value of `W_s`.

This is the step that commutes a time derivative with a fixed connection in the variation
formulas of geometric quantities along a family of metrics.

For a one-parameter family of connections `∇ˢ` whose difference tensors `∇ˢ - ∇ᵗ` (Mathlib's
`CovariantDerivative.difference`) have derivative `Γ'` at `s = t`, the file also computes the
parameter derivatives of `∇ˢ_v σ` and of the iterated covariant derivative `∇ˢ_v (∇ˢ_Y Z)`.

## Main results

* `CovariantDerivative.hasDerivAt_apply_of_contMDiffAt`: the parameter derivative of `∇_v W_s` is
  `∇_v` of the parameter derivative of `W_s`.
* `TauCeti.Manifold.hasDerivAt_covariantDerivative_apply_of_hasDerivAt_difference`: the parameter
  derivative of `∇ˢ_v σ` is `Γ'(σ, v)`.
* `TauCeti.Manifold.hasDerivAt_covariantDerivative_covariantDerivative_of_hasDerivAt_difference`:
  the parameter derivative of `∇ˢ_v (∇ˢ_Y Z)` is `∇ᵗ_v (Γ'(Z, Y)) + Γ'(∇ᵗ_Y Z, v)`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 4:
  the coordinate formula for a connection.
-/

public section

noncomputable section

open Bundle Filter Function
open scoped ContDiff Manifold Topology

namespace CovariantDerivative

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {W : ℝ → Π y : M, TangentSpace I y} {t : ℝ} {x : M}

/-- **Parameter derivatives commute with a covariant derivative.** Let `W_s` be a family of vector
fields on `M`, jointly `C²` in `(s, y)` at `(t, x)` as a map into the tangent bundle. Then for
every covariant derivative `∇` on `TM` and every `v ∈ T_x M`, the curve `s ↦ ∇_v W_s` in `T_x M`
has derivative `∇_v W'` at `t`, where `W' y = ∂ₛ W_s(y)` at `s = t`. -/
theorem hasDerivAt_apply_of_contMDiffAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hW : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) 2
      (fun q : ℝ × M ↦ TotalSpace.mk' E q.2 (W q.1 q.2)) (t, x))
    (v : TangentSpace I x) :
    HasDerivAt (fun s ↦ cov (W s) x v) (cov (fun y ↦ deriv (fun s ↦ W s y) t) x v) t := by
  -- Read the family in the trivialization `e` at `x`, with coordinates `G s y`.
  set e := trivializationAt E (TangentSpace I) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let b := Module.finBasis ℝ E
  have hcov : IsCovariantDerivativeOn E cov e.baseSet := cov.isCovariantDerivativeOn
  set G : ℝ → M → E := fun s y ↦ (e (TotalSpace.mk' E y (W s y))).2
  have hG : ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ, E) 2 (uncurry G) (t, x) :=
    (contMDiffAt_totalSpace_iff.mp hW).2
  set G' : M → E := fun y ↦ deriv (fun s ↦ G s y) t
  have hG' : MDifferentiableAt I 𝓘(ℝ, E) G' x :=
    (contMDiffAt_deriv_of_contMDiffAt_uncurry hG (by norm_num)).mdifferentiableAt one_ne_zero
  have hsymm (σ : Π y : M, TangentSpace I y) :
      ∀ᶠ y in 𝓝 x, σ y = e.symm y ((e (TotalSpace.mk' E y (σ y))).2) :=
    eventually_of_mem (e.open_baseSet.mem_nhds hx) fun y hy ↦ (e.symm_apply_apply_mk hy _).symm
  -- Near `(t, x)` the family is jointly `C¹`, so its slices are differentiable.
  have hW1 := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).mp (hW.of_le (by norm_num))
  have hslice : ∀ᶠ s in 𝓝 t, MDiffAt (T% (W s)) x :=
    ((continuous_id.prodMk continuous_const).continuousAt.eventually hW1).mono fun s hs ↦
      (hs.comp x (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt one_ne_zero
  have hcurve : DifferentiableAt ℝ (fun s ↦ G s x) t :=
    ((hG.comp t (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt
      two_ne_zero).differentiableAt
  -- `v` is the vector with coordinates `u` at `x`.
  set u : E := (e (TotalSpace.mk' E x v)).2
  have hv : e.symm x u = v := e.symm_apply_apply_mk hx v
  -- Both sides, read through the coordinate formula for `∇`.
  have hformula (σ : Π y : M, TangentSpace I y) (g : M → E) (hσ : MDiffAt (T% σ) x)
      (hg : MDifferentiableAt I 𝓘(ℝ, E) g x) (heq : ∀ᶠ y in 𝓝 x, σ y = e.symm y (g y)) :
      cov σ x v = e.symm x (mvfderiv I g x v + christoffelMap b hcov x (g x) u) := by
    have hread : ∀ᶠ y in 𝓝 x, (e ⟨y, e.symm y (g y)⟩).2 = g y :=
      eventually_of_mem (e.open_baseSet.mem_nhds hx) fun y hy ↦ by rw [e.apply_mk_symm hy]
    have hσ' : MDiffAt (T% (fun y ↦ e.symm y (g y))) x :=
      (e.mdifferentiableAt_section_iff I _ hx).2 (hg.congr_of_eventuallyEq hread)
    rw [hcov.congr_of_eventuallyEq hσ hσ' (e.open_baseSet.mem_nhds hx) heq, ← hv,
      covariantDerivative_symm_comp_apply_symm b hcov hx hg u]
  rw [hformula _ G' ((contMDiffAt_deriv_vectorField_of_contMDiffAt hW
    (by norm_num)).mdifferentiableAt one_ne_zero) hG'
    (eventually_deriv_eq_trivializationAt_symm (by norm_num) hW)]
  -- Differentiate the coordinate formula for `∇_v W_s` in `s`.
  let L : E →L[ℝ] E := e.symmL ℝ x
  have hd : HasDerivAt (fun s ↦ L (mvfderiv I (G s) x v + christoffelMap b hcov x (G s x) u))
      (L (mvfderiv I G' x v + christoffelMap b hcov x (G' x) u)) t := by
    have h1 : HasDerivAt (fun s ↦ mvfderiv I (G s) x v) (mvfderiv I G' x v) t := by
      refine hasDerivAt_mvfderiv_apply ?_ v
      rwa [minSmoothness_of_isRCLikeNormedField]
    have h2 : HasDerivAt (fun s ↦ christoffelMap b hcov x (G s x) u)
        (christoffelMap b hcov x (G' x) u) t :=
      ((christoffelMap b hcov x).hasFDerivAt.comp_hasDerivAt t
        hcurve.hasDerivAt).clm_apply (hasDerivAt_const t u) |>.congr_deriv
        (by simp [G'])
    exact L.hasFDerivAt.comp_hasDerivAt t (h1.add h2)
  rw [← e.symmL_apply (R := ℝ) hx]
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [hslice] with s hs
  exact (hformula (W s) (G s) hs ((e.mdifferentiableAt_section_iff I _ hx).1 hs)
    (hsymm (W s))).trans (e.symmL_apply (R := ℝ) hx _).symm

end CovariantDerivative

namespace TauCeti.Manifold

/-! ### Families of connections -/

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

/-- **The parameter derivative of a family of connections.** Let `∇ˢ` be a family of covariant
derivatives on `TM` whose difference tensors `(∇ˢ - ∇ᵗ)_y` have derivative `Γ'_y` at `s = t`. Then
for every vector field `σ` differentiable at `y` and every `v ∈ T_y M`, the curve `s ↦ ∇ˢ_v σ` in
`T_y M` has derivative `Γ'_y(σ y, v)` at `t`. -/
theorem hasDerivAt_covariantDerivative_apply_of_hasDerivAt_difference
    {σ : Π y : M, TangentSpace I y} {y : M}
    (hC : HasDerivAt (fun s ↦ (cov s).difference (cov t) y) (C y) t) (hσ : MDiffAt (T% σ) y)
    (v : TangentSpace I y) :
    HasDerivAt (F := E) (fun s ↦ cov s σ y v) (C y (σ y) v) t := by
  -- The tangent space at `y` is read as the model space `E`.
  have hC' : HasDerivAt (F := E →L[ℝ] E →L[ℝ] E) (fun s ↦ (cov s).difference (cov t) y) (C y) t :=
    hC
  have h := (TauCeti.hasDerivAt_clm_apply₂ (F := E) (F' := E) (G := E)).mp hC' (σ y) v
  exact (HasDerivAt.const_add (F := E) (cov t σ y v) h).congr_of_eventuallyEq
    (Eventually.of_forall fun s ↦ apply_eq_apply_add_difference hσ s v)

/-- **The parameter derivative of an iterated covariant derivative.** Let `∇ˢ` be a family of
covariant derivatives on `TM` whose difference tensors `(∇ˢ - ∇ᵗ)_y` have derivative `Γ'_y` at
`s = t` for `y` near `x`. Let `Z` be differentiable near `x`, and let the vector fields `∇ˢ_Y Z` be
jointly `C²` in `(s, y)` at `(t, x)`. Then for every `v ∈ T_x M` the curve `s ↦ ∇ˢ_v (∇ˢ_Y Z)` in
`T_x M` has derivative `∇ᵗ_v (Γ'(Z, Y)) + Γ'_x(∇ᵗ_Y Z, v)` at `t`. -/
theorem hasDerivAt_covariantDerivative_covariantDerivative_of_hasDerivAt_difference
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
    exact HasDerivAt.deriv (F := E)
      (hasDerivAt_covariantDerivative_apply_of_hasDerivAt_difference hy hZy (Y y))
  have hreg := (contMDiffAt_deriv_vectorField_of_contMDiffAt
    (W := fun s y ↦ cov s Z y (Y y)) hYZ (m := 1) (by norm_num)).mdifferentiableAt one_ne_zero
  -- The outer covariant derivative along `∇ᵗ`, commuted with the parameter derivative ...
  have hout := (cov t).hasDerivAt_apply_of_contMDiffAt
    (W := fun s y ↦ cov s Z y (Y y)) hYZ v
  rw [(cov t).isCovariantDerivativeOnUniv.congr_of_eventuallyEq hreg
    (hreg.congr_of_eventuallyEq (hderiv.mono fun y hy ↦ by simp only [hy]))
    Filter.univ_mem hderiv] at hout
  -- ... plus the difference tensor applied to `∇ˢ_Y Z`.
  have hval : HasDerivAt (F := E) (fun s ↦ cov s Z x (Y x)) (C x (Z x) (Y x)) t :=
    hasDerivAt_covariantDerivative_apply_of_hasDerivAt_difference hC.self_of_nhds
      hZ.self_of_nhds (Y x)
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

end TauCeti.Manifold
