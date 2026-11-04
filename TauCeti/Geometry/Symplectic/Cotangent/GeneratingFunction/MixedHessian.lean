/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.GeneratingFunction.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.Chart
public import TauCeti.Geometry.Manifold.MFDeriv.Parametric
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The intrinsic mixed Hessian of a function on a product of manifolds

A real function `S(q, Q)` on a product `M × N` of manifolds generates the cotangent relation
`p = d_q S`, `P = -d_Q S` between `T*M` and `T*N`. Whether this relation is locally the graph of a
canonical transformation is decided by its **mixed Hessian** at `(q, Q)`,

`d_Q (d_q S) : T_Q N → T*_q M`,

obtained by differentiating the covector `d_q S(·, Q') ∈ T*_q M`, which lies in the fixed cotangent
space at `q`, with respect to `Q'` (`TauCeti.mixedHessian I J S x`). Unlike the full second
derivative of `S`, which depends on the chart away from critical points, the mixed Hessian is
intrinsic: it uses only first derivatives in each factor separately, and the second-order terms
of a change of coordinates in one factor are killed by differentiating in the other.

This file makes this precise. The tangent space `T_q M` is the model space `E` of `M` by
definition, so the mixed Hessian is a continuous linear map from `T_Q N` to `E →L[ℝ] ℝ`.

* On normed spaces it is the linear mixed Hessian `TauCeti.cotangentMixedHessian`, which is
  invertible exactly when the derivative of the source projection of the generated relation is
  (`TauCeti.mixedHessian_modelSpace`).
* It is natural under maps of either factor: for `f : M₁ → M` and `g : N₁ → N`,
  `d_Q d_q (S ∘ (f × g)) (w, v) = d_Q d_q S (dg w, df v)`
  (`TauCeti.mixedHessian_comp_prodMap_apply`). Only differentiability of `f` and `g` is needed.
* Hence, on boundaryless manifolds, it is computed in **any** charts of the `C²` maximal atlases
  as the linear mixed Hessian of the coordinate expression of `S`, evaluated on the images of the
  tangent vectors under the chart derivatives
  (`TauCeti.mixedHessian_apply_eq_of_mem_maximalAtlas`). In the preferred charts at the point it
  is that linear mixed Hessian itself
  (`TauCeti.mixedHessian_eq_cotangentMixedHessian_extChartAt`), and its invertibility may be
  tested in any chart
  (`TauCeti.isInvertible_mixedHessian_iff_of_mem_maximalAtlas`).
* Interchanging the factors transposes it, so `d_q (d_Q S)` and `d_Q (d_q S)` agree as bilinear
  maps (`TauCeti.mixedHessian_comp_swap_apply`).

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, Springer, 1989,
  §48 (generating functions).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 4 (generating functions).
-/

public section

open Function Set Filter ContinuousLinearMap
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]

variable (I J) in
/-- The **mixed Hessian** `d_Q (d_q S)` of a real function `S` on a product of manifolds at
`x = (q, Q)`: the derivative at `Q` of the map `Q' ↦ d_q S(·, Q')` into the cotangent space at `q`.
It sends `w ∈ T_Q N` to a covector on `T_q M`, whose model space is `E`.

The definition carries no regularity hypotheses. When `S` is `C²` at `x`, it is natural in both
factors (`TauCeti.mixedHessian_comp_prodMap_apply`) and is computed in charts
(`TauCeti.mixedHessian_apply_eq_of_mem_maximalAtlas`). -/
noncomputable def mixedHessian (S : M × N → ℝ) (x : M × N) :
    TangentSpace J x.2 →L[ℝ] E →L[ℝ] ℝ :=
  mvfderiv (F := E →L[ℝ] ℝ) J (fun Q ↦ mvfderiv I (fun q ↦ S (q, Q)) x.1) x.2

/-- The mixed Hessian is the derivative in the second factor of the differential in the first. -/
theorem mixedHessian_def (S : M × N → ℝ) (x : M × N) :
    mixedHessian I J S x =
      mvfderiv (F := E →L[ℝ] ℝ) J (fun Q ↦ mvfderiv I (fun q ↦ S (q, Q)) x.1) x.2 :=
  (rfl)

/-- **The mixed Hessian on normed spaces.** For a function on a product of normed spaces which is
`C²` at `x`, the mixed Hessian is the linear mixed Hessian `δQ ↦ D²S (0, δQ) (·, 0)`. -/
theorem mixedHessian_modelSpace {S : E × E' → ℝ} {x : E × E'} (hS : ContDiffAt ℝ 2 S x) :
    mixedHessian 𝓘(ℝ, E) 𝓘(ℝ, E') S x = cotangentMixedHessian S x := by
  obtain ⟨q, Q⟩ := x
  have h1 : ∀ᶠ y in 𝓝 (q, Q), DifferentiableAt ℝ S y :=
    (hS.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt (by simp)
  have h2 : DifferentiableAt ℝ (fderiv ℝ S) (q, Q) :=
    (hS.fderiv_right (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).differentiableAt one_ne_zero
  -- Near `Q`, the differential in the first factor is the full differential restricted to `E`.
  have heq : (fun Q' ↦ precomp ℝ (inl ℝ E E') (fderiv ℝ S (q, Q'))) =ᶠ[𝓝 Q]
      fun Q' ↦ mvfderiv 𝓘(ℝ, E) (fun q' ↦ S (q', Q')) q := by
    have hc : ContinuousAt (fun Q' : E' ↦ (q, Q')) Q := by fun_prop
    filter_upwards [hc.eventually h1] with Q' hQ'
    rw [mvfderiv_eq_fderiv, fderiv_slice_left hQ']
    -- `NormedSpace.fromTangentSpace q` is the identity of `E`, the tangent space of `E` at `q`.
    rfl
  have hD := ((precomp ℝ (inl ℝ E E')).hasFDerivAt.comp Q
    (h2.hasFDerivAt.comp Q (hasFDerivAt_prodMk_right (𝕜 := ℝ) q Q))).fderiv
  ext b a
  rw [mixedHessian_def, ← heq.mvfderiv_eq, mvfderiv_eq_fderiv]
  -- As above, the tangent space of `E'` at `Q` is `E'` itself.
  erw [hD]
  exact (cotangentMixedHessian_apply_apply S (q, Q) b a).symm

section Naturality

variable {E₁ E₁' H₁ H₁' : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₁'] [NormedSpace ℝ E₁'] [TopologicalSpace H₁] [TopologicalSpace H₁']
  {I₁ : ModelWithCorners ℝ E₁ H₁} {J₁ : ModelWithCorners ℝ E₁' H₁'}
  {M₁ N₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [TopologicalSpace N₁]
  [ChartedSpace H₁' N₁]

/-- **Naturality of the mixed Hessian.** For `S` which is `C²` at `(f q, g Q)` and maps `f`, `g`
differentiable at `q` and `Q`, the mixed Hessian of `S ∘ (f × g)` at `(q, Q)` is the mixed Hessian
of `S` at `(f q, g Q)` evaluated on the images of the tangent vectors under `dg` and `df`. -/
theorem mixedHessian_comp_prodMap_apply [IsManifold I 1 M] [IsManifold J 1 N]
    {S : M × N → ℝ} {f : M₁ → M} {g : N₁ → N} {x : M₁ × N₁}
    (hS : ContMDiffAt (I.prod J) 𝓘(ℝ) 2 S (f x.1, g x.2))
    (hf : MDifferentiableAt I₁ I f x.1) (hg : MDifferentiableAt J₁ J g x.2)
    (w : TangentSpace J₁ x.2) (v : TangentSpace I₁ x.1) :
    mixedHessian I₁ J₁ (S ∘ Prod.map f g) x w v =
      mixedHessian I J S (f x.1, g x.2) (mfderiv J₁ J g x.2 w) (mfderiv I₁ I f x.1 v) := by
  obtain ⟨q, Q⟩ := x
  -- The differential of `S` in the first factor at `f q`, as a function of the second factor.
  let σ : N → E →L[ℝ] ℝ := fun P ↦ mvfderiv I (fun p ↦ S (p, P)) (f q)
  have hσ : MDifferentiableAt J 𝓘(ℝ, E →L[ℝ] ℝ) σ (g Q) := by
    have hswap : ContMDiffAt (J.prod I) 𝓘(ℝ) 2 (uncurry fun P p ↦ S (p, P)) (g Q, f q) :=
      hS.comp (g Q, f q) (contMDiffAt_snd.prodMk contMDiffAt_fst)
    exact (Manifold.contMDiffAt_mvfderiv_of_contMDiffAt_uncurry hswap
      (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).mdifferentiableAt one_ne_zero
  -- Near `Q`, the slices of `S` through `g Q'` are differentiable at `f q`.
  have hnear : ∀ᶠ Q' in 𝓝 Q, MDifferentiableAt I 𝓘(ℝ) (fun p ↦ S (p, g Q')) (f q) := by
    have h1 := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).mp
      (hS.of_le (by norm_num))
    have hc : ContinuousAt (fun Q' ↦ (f q, g Q')) Q :=
      continuousAt_const.prodMk hg.continuousAt
    filter_upwards [hc.eventually h1] with Q' hQ'
    exact (hQ'.comp (f q) (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt
      one_ne_zero
  -- Precomposition with `df`; by the chain rule in the first factor, the differential of the
  -- first slices of `S ∘ (f × g)` is `L ∘ σ ∘ g` near `Q`.
  let L : (E →L[ℝ] ℝ) →L[ℝ] E₁ →L[ℝ] ℝ := (compL ℝ E₁ E ℝ).flip (mfderiv I₁ I f q)
  have heq : L ∘ σ ∘ g =ᶠ[𝓝 Q] fun Q' ↦
      mvfderiv I₁ (fun q' ↦ (S ∘ Prod.map f g) (q', Q')) q := by
    filter_upwards [hnear] with Q' hQ'
    exact (mvfderiv_comp q hQ' hf).symm
  simp only [mixedHessian_def]
  rw [← heq.mvfderiv_eq, mvfderiv_comp_apply_of_differentiableAt L.differentiableAt (hσ.comp Q hg),
    ContinuousLinearMap.fderiv, mvfderiv_comp_apply Q hσ hg]
  -- `L φ v` unfolds to `φ (df v)`.
  rfl

end Naturality

section Chart

variable [I.Boundaryless] [J.Boundaryless] [IsManifold I 2 M] [IsManifold J 2 N]
  {S : M × N → ℝ} {x : M × N}

/-- **The mixed Hessian in arbitrary charts.** On boundaryless manifolds, the mixed Hessian at `x`
of a function `S` which is `C²` there is the linear mixed Hessian of the coordinate expression of
`S` in any charts `e`, `e'` of the `C²` maximal atlases around `x.1` and `x.2`, evaluated on the
images of the tangent vectors under the chart derivatives. -/
theorem mixedHessian_apply_eq_of_mem_maximalAtlas {e : OpenPartialHomeomorph M H}
    {e' : OpenPartialHomeomorph N H'} (he : e ∈ IsManifold.maximalAtlas I 2 M)
    (he' : e' ∈ IsManifold.maximalAtlas J 2 N) (hx : x.1 ∈ e.source) (hx' : x.2 ∈ e'.source)
    (hS : ContMDiffAt (I.prod J) 𝓘(ℝ) 2 S x) (w : TangentSpace J x.2) (v : TangentSpace I x.1) :
    mixedHessian I J S x w v =
      cotangentMixedHessian (S ∘ Prod.map (e.extend I).symm (e'.extend J).symm)
        (e.extend I x.1, e'.extend J x.2) (mvfderiv J (e'.extend J) x.2 w)
        (mvfderiv I (e.extend I) x.1 v) := by
  obtain ⟨q, Q⟩ := x
  dsimp only at *
  have he₁ : e ∈ IsManifold.maximalAtlas I 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by norm_num) he
  have he₁' : e' ∈ IsManifold.maximalAtlas J 1 N :=
    IsManifold.maximalAtlas_subset_of_le (by norm_num) he'
  have hq : q ∈ (e.extend I).source := by rwa [e.extend_source]
  have hQ : Q ∈ (e'.extend J).source := by rwa [e'.extend_source]
  have hφ : (e.extend I).symm (e.extend I q) = q := (e.extend I).left_inv hq
  have hψ : (e'.extend J).symm (e'.extend J Q) = Q := (e'.extend J).left_inv hQ
  -- The inverse charts are differentiable at the chart images, which are interior points.
  have hφd : MDifferentiableAt 𝓘(ℝ, E) I (e.extend I).symm (e.extend I q) :=
    (mdifferentiableWithinAt_extend_symm he₁ ((e.extend I).map_source hq)).mdifferentiableAt
      (by simp [ModelWithCorners.Boundaryless.range_eq_univ])
  have hψd : MDifferentiableAt 𝓘(ℝ, E') J (e'.extend J).symm (e'.extend J Q) :=
    (mdifferentiableWithinAt_extend_symm he₁' ((e'.extend J).map_source hQ)).mdifferentiableAt
      (by simp [ModelWithCorners.Boundaryless.range_eq_univ])
  have hS' : ContMDiffAt (I.prod J) 𝓘(ℝ) 2 S
      ((e.extend I).symm (e.extend I q), (e'.extend J).symm (e'.extend J Q)) := by
    rwa [hφ, hψ]
  -- The coordinate expression in the product chart `e × e'` is `C²`.
  have hT : ContDiffAt ℝ 2 (S ∘ Prod.map (e.extend I).symm (e'.extend J).symm)
      (e.extend I q, e'.extend J Q) := by
    have h := (contMDiffAt_iff_contDiffAt_comp_extend_symm
      (IsManifold.mem_maximalAtlas_prod he he') (x := (q, Q)) ⟨hx, hx'⟩).mp hS
    rwa [e.extend_prod e'] at h
  -- The derivative of the inverse chart undoes the derivative of the chart.
  have hdφ : mfderiv 𝓘(ℝ, E) I (e.extend I).symm (e.extend I q)
      (mvfderiv I (e.extend I) q v) = v := by
    have h := congr($(mfderivWithin_extend_symm_comp_mfderiv_extend' he₁ hx) v)
    rwa [ModelWithCorners.Boundaryless.range_eq_univ, mfderivWithin_univ] at h
  have hdψ : mfderiv 𝓘(ℝ, E') J (e'.extend J).symm (e'.extend J Q)
      (mvfderiv J (e'.extend J) Q w) = w := by
    have h := congr($(mfderivWithin_extend_symm_comp_mfderiv_extend' he₁' hx') w)
    rwa [ModelWithCorners.Boundaryless.range_eq_univ, mfderivWithin_univ] at h
  have key := mixedHessian_comp_prodMap_apply (x := (e.extend I q, e'.extend J Q)) hS' hφd hψd
    (mvfderiv J (e'.extend J) Q w) (mvfderiv I (e.extend I) q v)
  dsimp only at key
  rw [mixedHessian_modelSpace hT, hdφ, hdψ] at key
  refine Eq.trans ?_ key.symm
  rw [hφ, hψ]

/-- **The mixed Hessian in the preferred charts.** On boundaryless manifolds, the mixed Hessian at
`x` of a function which is `C²` there is the linear mixed Hessian of its coordinate expression in
the preferred extended charts at `x.1` and `x.2`. -/
theorem mixedHessian_eq_cotangentMixedHessian_extChartAt
    (hS : ContMDiffAt (I.prod J) 𝓘(ℝ) 2 S x) :
    mixedHessian I J S x =
      cotangentMixedHessian (S ∘ Prod.map (extChartAt I x.1).symm (extChartAt J x.2).symm)
        (extChartAt I x.1 x.1, extChartAt J x.2 x.2) := by
  -- The derivatives of the preferred charts at their centres are the identity.
  have hv (v : TangentSpace I x.1) : mvfderiv I ((chartAt H x.1).extend I) x.1 v = v := by
    rw [mvfderiv_apply_eq_mfderiv_apply, ← extChartAt, mfderiv_extChartAt_self]
    rfl
  have hw (w : TangentSpace J x.2) : mvfderiv J ((chartAt H' x.2).extend J) x.2 w = w := by
    rw [mvfderiv_apply_eq_mfderiv_apply, ← extChartAt, mfderiv_extChartAt_self]
    rfl
  ext w (v : TangentSpace I x.1)
  have h := mixedHessian_apply_eq_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x.1)
    (IsManifold.chart_mem_maximalAtlas x.2) (mem_chart_source H x.1) (mem_chart_source H' x.2)
    hS w v
  rw [hv, hw] at h
  exact h

/-- **Nondegeneracy of the mixed Hessian in arbitrary charts.** On boundaryless manifolds, the
mixed Hessian at `x` of a function which is `C²` there is invertible exactly when the linear mixed
Hessian of its coordinate expression in any charts of the `C²` maximal atlases around `x.1` and
`x.2` is invertible. -/
theorem isInvertible_mixedHessian_iff_of_mem_maximalAtlas {e : OpenPartialHomeomorph M H}
    {e' : OpenPartialHomeomorph N H'} (he : e ∈ IsManifold.maximalAtlas I 2 M)
    (he' : e' ∈ IsManifold.maximalAtlas J 2 N) (hx : x.1 ∈ e.source) (hx' : x.2 ∈ e'.source)
    (hS : ContMDiffAt (I.prod J) 𝓘(ℝ) 2 S x) :
    (mixedHessian I J S x).IsInvertible ↔
      (cotangentMixedHessian (S ∘ Prod.map (e.extend I).symm (e'.extend J).symm)
        (e.extend I x.1, e'.extend J x.2)).IsInvertible := by
  -- The chart derivatives at `x` are invertible.
  obtain ⟨A, hA⟩ := isInvertible_mfderiv_extend
    (IsManifold.maximalAtlas_subset_of_le (by norm_num) he) (by simpa using hx)
  obtain ⟨B, hB⟩ := isInvertible_mfderiv_extend
    (IsManifold.maximalAtlas_subset_of_le (by norm_num) he') (by simpa using hx')
  -- The tangent spaces involved are the model spaces `E` and `E'`.
  let A' : E ≃L[ℝ] E := A
  let B' : TangentSpace J x.2 ≃L[ℝ] E' := B
  have h : mixedHessian I J S x =
      (A'.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ) : (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ) ∘L
        cotangentMixedHessian (S ∘ Prod.map (e.extend I).symm (e'.extend J).symm)
          (e.extend I x.1, e'.extend J x.2) ∘L (B' : TangentSpace J x.2 →L[ℝ] E') := by
    ext w (v : TangentSpace I x.1)
    rw [mixedHessian_apply_eq_of_mem_maximalAtlas he he' hx hx' hS, mvfderiv_apply_eq_mfderiv_apply,
      mvfderiv_apply_eq_mfderiv_apply, ← hA, ← hB]
    rfl
  rw [h, isInvertible_equiv_comp, isInvertible_comp_equiv]

/-- **The mixed Hessian of the transposed function.** On boundaryless manifolds, for `S` which is
`C²` at `x`, interchanging the two factors transposes the mixed Hessian. The left side
differentiates `d_Q S` in `q`, so this says that the two orders of differentiation agree:
`d_q (d_Q S) (v, w) = d_Q (d_q S) (w, v)`. -/
theorem mixedHessian_comp_swap_apply (hS : ContMDiffAt (I.prod J) 𝓘(ℝ) 2 S x)
    (v : TangentSpace I x.1) (w : TangentSpace J x.2) :
    mixedHessian J I (S ∘ Prod.swap) x.swap v w = mixedHessian I J S x w v := by
  have hS' : ContMDiffAt (J.prod I) 𝓘(ℝ) 2 (S ∘ Prod.swap) x.swap :=
    hS.comp x.swap (contMDiffAt_snd.prodMk contMDiffAt_fst)
  have hT : ContDiffAt ℝ 2 (S ∘ Prod.map (extChartAt I x.1).symm (extChartAt J x.2).symm)
      (extChartAt I x.1 x.1, extChartAt J x.2 x.2) := by
    have h := (contMDiffAt_iff_contDiffAt_comp_extend_symm
      (IsManifold.mem_maximalAtlas_prod (IsManifold.chart_mem_maximalAtlas (n := 2) x.1)
        (IsManifold.chart_mem_maximalAtlas (n := 2) x.2))
      ⟨mem_chart_source H x.1, mem_chart_source H' x.2⟩).mp hS
    rwa [OpenPartialHomeomorph.extend_prod] at h
  rw [mixedHessian_eq_cotangentMixedHessian_extChartAt hS',
    mixedHessian_eq_cotangentMixedHessian_extChartAt hS]
  exact cotangentMixedHessian_comp_swap_apply hT v w

end Chart

end TauCeti
