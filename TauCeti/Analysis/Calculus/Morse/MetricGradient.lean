/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.SpectralSplitting
public import TauCeti.Analysis.InnerProductSpace.LyapunovForm.Inertia
public import TauCeti.Analysis.ODE.LyapunovPerron.VectorField
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.InnerProductSpace.Coercive
import TauCeti.Analysis.ODE.ExponentialDichotomy
import TauCeti.Analysis.ODE.ExponentialDichotomy.Hyperbolic
import TauCeti.Topology.UniformSpace.UniformConvergence.Comp
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Local stable and unstable manifolds of the gradient of a variable metric

On a finite-dimensional real inner product space `E`, a field `G : E → (E →L[ℝ] E)` of operators
defines the bilinear forms `g_y(u, v) = ⟪G y u, v⟫`. In a chart of a Riemannian manifold every
metric has this shape, with `G y` symmetric and positive definite. The gradient of `f` for `g` is
the vector `(G y)⁻¹ (∇ f y)` (`TauCeti.metricGradient`), characterized by
`g_y(metricGradient G f y, v) = df_y v` (`TauCeti.eq_metricGradient_iff`); for the constant field
`G = id` it is the gradient `∇ f`. Its zeros are the critical points of `f`.

This file transfers the local invariant-manifold theory of a hyperbolic zero of a vector field
(`ContinuousLinearMap.exists_localStableGraph_of_contDiffAt`) to the negative gradient flow of `g`
at a nondegenerate critical point `x` of `f`, without assuming that `g` is Euclidean, or even
constant, near `x`.

* If `f` is `C^(n+1)` and `G` is `C^n` at `x`, with `G x` invertible, the field
  `metricGradient G f` is `C^n` at `x` (`ContDiffAt.metricGradient`). Differentiating
  `G y (metricGradient G f y) = ∇ f y` gives its derivative
  `v ↦ (G y)⁻¹ (Hess f(y) v - DG(y)(v) (metricGradient G f y))`
  (`TauCeti.hasFDerivAt_metricGradient`). At a critical point it is `(G x)⁻¹ ∘ Hess f(x)`
  (`TauCeti.hasFDerivAt_metricGradient_of_fderiv_eq_zero`): the derivative of the metric drops
  out because `∇ f x = 0`.
* If the quadratic form of `G x` is coercive, `c ‖v‖² ≤ ⟪G x v, v⟫` with `c > 0`, then the
  linearization `A = -(G x)⁻¹ ∘ Hess f(x)` has the Lyapunov form `-Hess f(x)`, since
  `⟪Hess f(x) (G x)⁻¹ Hess f(x) v, v⟫ = ⟪(G x)⁻¹ w, w⟫` with `w = Hess f(x) v`, and the inverse of
  a coercive operator is coercive. So `A` is hyperbolic. By the inertia theorem the unstable
  subspace of `A` has dimension the Morse index of `f` at `x`, and the stable subspace the
  complementary dimension, for every such metric. Symmetry of `G x` is not used.
* Consequently, confined forward, respectively backward, trajectories of `-metricGradient G f`
  near `x` form a Lipschitz `C^n` graph over a neighbourhood of `0` in the stable, respectively
  unstable, subspace of `A`, tangent to that subspace at `x`, and every confined trajectory tends
  to `x`. These are the local stable and unstable manifolds, of dimensions `dim E - ind_x f` and
  `ind_x f`.
* The derivative of `metricGradient G f` is a continuous function of the point, of `G` and of
  `DG` there. So if metric fields `Gs i` converge to `G` in `C¹` on a compact set `K`, the
  derivatives of their metric gradients converge uniformly on `K`
  (`TauCeti.tendstoUniformlyOn_fderiv_metricGradient`); `f` stays fixed. At a nondegenerate
  critical point `x` this is `C¹` convergence of the fields `-metricGradient (Gs i) f`, which all
  vanish at `x`, so the local stable and unstable graphs of `Gs i` converge in `C¹` to those of
  `G`, with one confinement radius and one parameter radius for all of them. This is the
  `C¹`-continuous dependence of the local stable and unstable manifolds on a `C¹` metric.

These are local graph theorems at one critical point; the global stable and unstable manifolds are
not treated here.

## Main declarations

* `TauCeti.metricGradient`: the gradient `(G y)⁻¹ (∇ f y)` of `f` for the metric
  `g_y(u, v) = ⟪G y u, v⟫`.
* `TauCeti.eq_metricGradient_iff` and `TauCeti.inner_apply_metricGradient`: its characterization
  `⟪G y (metricGradient G f y), v⟫ = df_y v`.
* `TauCeti.metricGradient_eq_zero_iff`: its zeros are the critical points of `f`.
* `ContDiffAt.metricGradient` and `TauCeti.hasFDerivAt_metricGradient`: its regularity and its
  derivative; `TauCeti.hasFDerivAt_metricGradient_of_fderiv_eq_zero`: its derivative at a critical
  point.
* `TauCeti.tendstoUniformlyOn_fderiv_metricGradient`: its derivative depends continuously on the
  metric in `C¹`, uniformly on compact sets.
* `TauCeti.IsNondegenerateCriticalPoint.hasLyapunovForm_neg_inverse_comp_hessianOperator`: the
  linearization of `-metricGradient G f` at a nondegenerate critical point is hyperbolic.
* `TauCeti.IsNondegenerateCriticalPoint.finrank_unstableSubspace_neg_inverse_comp_hessianOperator`:
  its unstable dimension is the Morse index;
  `TauCeti.IsNondegenerateCriticalPoint.finrank_stableSubspace_neg_inverse_comp_hessianOperator`:
  its stable dimension is the complementary one.
* `TauCeti.IsNondegenerateCriticalPoint.exists_localStableGraph_neg_metricGradient` and
  `TauCeti.IsNondegenerateCriticalPoint.exists_localUnstableGraph_neg_metricGradient`: the local
  stable and unstable manifolds of the negative gradient flow of `g` are `C^n` graphs over the
  stable and unstable subspaces of the linearization.
* `exists_localStableGraph_neg_metricGradient_tendstoUniformlyOn_fderiv` and
  `exists_localUnstableGraph_neg_metricGradient_tendstoUniformlyOn_fderiv`, in the namespace
  `TauCeti.IsNondegenerateCriticalPoint`: these graphs depend continuously in `C¹` on the metric.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2 (stable and unstable manifolds of a pseudo-gradient field).
* C. Chicone, *Ordinary Differential Equations with Applications*, 2nd ed., Springer, 2006,
  §4.3 (the stable-manifold theorem and the dependence of invariant manifolds on the vector
  field).
* A. Ostrowski and H. Schneider, *Some theorems on the inertia of general matrices*, J. Math. Anal.
  Appl. **4** (1962), 72–84.
-/

public section

open Filter Metric Module Set Topology
open scoped Gradient InnerProductSpace NNReal

noncomputable section

namespace TauCeti

section Field

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {G : E → E →L[ℝ] E} {f : E → ℝ} {x y : E}

/-- The **gradient of `f` for the metric `g_y(u, v) = ⟪G y u, v⟫`**: the vector `(G y)⁻¹ (∇ f y)`.
When `G y` is invertible it is the unique vector `w` with `⟪G y w, v⟫ = df_y v` for every `v`
(`TauCeti.eq_metricGradient_iff`); in a chart of a Riemannian manifold this is the Riemannian
gradient `g⁻¹ df`. Where `G y` is not invertible the totalized inverse makes it `0`. -/
def metricGradient (G : E → E →L[ℝ] E) (f : E → ℝ) (y : E) : E :=
  (G y).inverse (∇ f y)

/-- Unfolding `TauCeti.metricGradient`. -/
theorem metricGradient_apply (G : E → E →L[ℝ] E) (f : E → ℝ) (y : E) :
    metricGradient G f y = (G y).inverse (∇ f y) :=
  (rfl)

/-- For the Euclidean metric `G y = id` the metric gradient is the gradient. -/
@[simp]
theorem metricGradient_id (f : E → ℝ) :
    metricGradient (fun _ ↦ ContinuousLinearMap.id ℝ E) f = ∇ f := by
  ext y
  rw [metricGradient_apply, ContinuousLinearMap.inverse_id, ContinuousLinearMap.id_apply]

/-- Applying the metric to the metric gradient recovers the gradient. -/
theorem apply_metricGradient (hG : (G y).IsInvertible) : G y (metricGradient G f y) = ∇ f y :=
  hG.self_apply_inverse _

/-- **Characterization of the metric gradient.** When `G y` is invertible, a vector `w` is the
metric gradient of `f` at `y` exactly when `⟪G y w, v⟫ = df_y v` for every `v`. -/
theorem eq_metricGradient_iff (hG : (G y).IsInvertible) {w : E} :
    w = metricGradient G f y ↔ ∀ v, ⟪G y w, v⟫_ℝ = fderiv ℝ f y v := by
  have hgrad (v : E) : ⟪∇ f y, v⟫_ℝ = fderiv ℝ f y v := InnerProductSpace.toDual_symm_apply
  refine ⟨fun hw v ↦ by rw [hw, apply_metricGradient hG, hgrad], fun hw ↦ ?_⟩
  refine hG.injective (ext_inner_right ℝ fun v ↦ ?_)
  rw [hw, apply_metricGradient hG, hgrad]

/-- The defining property of the metric gradient: `g_y(metricGradient G f y, v) = df_y v`. -/
theorem inner_apply_metricGradient (hG : (G y).IsInvertible) (v : E) :
    ⟪G y (metricGradient G f y), v⟫_ℝ = fderiv ℝ f y v :=
  (eq_metricGradient_iff hG).1 rfl v

/-- The zeros of the metric gradient are the critical points of `f`. -/
theorem metricGradient_eq_zero_iff (hG : (G y).IsInvertible) :
    metricGradient G f y = 0 ↔ fderiv ℝ f y = 0 := by
  rw [metricGradient_apply, ← gradient_eq_zero_iff]
  exact hG.inverse.injective.eq_iff' (map_zero _)

/-- **Regularity of the metric gradient.** If `f` is `C^(n+1)` and the metric field `G` is `C^n` at
`y`, with `G y` invertible, then the metric gradient of `f` is `C^n` at `y`. -/
theorem _root_.ContDiffAt.metricGradient {n : WithTop ℕ∞} (hf : ContDiffAt ℝ (n + 1) f y)
    (hG : ContDiffAt ℝ n G y) (hGy : (G y).IsInvertible) :
    ContDiffAt ℝ n (metricGradient G f) y := by
  rw [funext (metricGradient_apply G f)]
  exact (hGy.contDiffAt_map_inverse.comp y hG).clm_apply (hf.gradient_right le_rfl)

/-- **The derivative of the metric gradient.** If `f` is `C²` at `y` and the metric field `G` is
differentiable at `y`, with `G y` invertible, then the derivative of the metric gradient at `y` is
`v ↦ (G y)⁻¹ (Hess f(y) v - DG(y)(v) (metricGradient G f y))`: differentiate
`G y (metricGradient G f y) = ∇ f y`. -/
theorem hasFDerivAt_metricGradient (hf : ContDiffAt ℝ 2 f y) (hG : DifferentiableAt ℝ G y)
    (hGy : (G y).IsInvertible) :
    HasFDerivAt (metricGradient G f)
      ((G y).inverse ∘L (hessianOperator f y - (fderiv ℝ G y).flip (metricGradient G f y))) y := by
  have h := (hG.hasFDerivAt.clm_inverse_of_completeSpace hGy).clm_apply hf.hasFDerivAt_gradient
  rw [funext (metricGradient_apply G f)]
  convert h using 1
  ext v
  simp [sub_eq_add_neg]

/-- **The derivative of the metric gradient at a critical point** is `(G x)⁻¹ ∘ Hess f(x)`: the
derivative of the metric does not contribute, because the gradient vanishes at `x`. -/
theorem hasFDerivAt_metricGradient_of_fderiv_eq_zero (hf : ContDiffAt ℝ 2 f x)
    (hx : fderiv ℝ f x = 0) (hG : DifferentiableAt ℝ G x) (hGx : (G x).IsInvertible) :
    HasFDerivAt (metricGradient G f) ((G x).inverse ∘L hessianOperator f x) x := by
  have h := hasFDerivAt_metricGradient hf hG hGx
  rwa [(metricGradient_eq_zero_iff hGx).2 hx, map_zero, sub_zero] at h

/-- **The metric gradient depends continuously in `C¹` on the metric.** Let `K` be a compact set
at whose points `f` is `C²` and the metric field `G` is `C¹` and invertible. If the fields `Gs i`
are eventually differentiable at the points of `K` and converge to `G` in `C¹` on `K`, that is
`Gs i → G` and `DGs i → DG` uniformly on `K`, then the derivatives of the metric gradients of `f`
for `Gs i` converge to that for `G` uniformly on `K`. -/
theorem tendstoUniformlyOn_fderiv_metricGradient {ι : Type*} {l : Filter ι}
    {Gs : ι → E → E →L[ℝ] E} {K : Set E} (hK : IsCompact K) (hf : ∀ y ∈ K, ContDiffAt ℝ 2 f y)
    (hG : ∀ y ∈ K, ContDiffAt ℝ 1 G y) (hGK : ∀ y ∈ K, (G y).IsInvertible)
    (hGs : ∀ᶠ i in l, ∀ y ∈ K, DifferentiableAt ℝ (Gs i) y)
    (hGG : TendstoUniformlyOn Gs G l K)
    (hGG' : TendstoUniformlyOn (fun i ↦ fderiv ℝ (Gs i)) (fderiv ℝ G) l K) :
    TendstoUniformlyOn (fun i ↦ fderiv ℝ (metricGradient (Gs i) f))
      (fderiv ℝ (metricGradient G f)) l K := by
  -- The derivative at `y` is a continuous function `D` of `y`, of the metric and of its
  -- derivative at `y`, by `hasFDerivAt_metricGradient`.
  let D : E × (E →L[ℝ] E) × (E →L[ℝ] E →L[ℝ] E) → E →L[ℝ] E := fun p ↦
    p.2.1.inverse ∘L (hessianOperator f p.1 - p.2.2.flip (p.2.1.inverse (∇ f p.1)))
  have hD {H : E → E →L[ℝ] E} {y : E} (hH : DifferentiableAt ℝ H y) (hHy : (H y).IsInvertible)
      (hfy : ContDiffAt ℝ 2 f y) :
      fderiv ℝ (metricGradient H f) y = D (y, H y, fderiv ℝ H y) := by
    rw [(hasFDerivAt_metricGradient hfy hH hHy).fderiv, metricGradient_apply]
  have hGc (y : E) (hy : y ∈ K) : ContinuousAt G y := (hG y hy).continuousAt
  have hinv := hGG.eventually_forall_isInvertible
    (hK.image_of_continuousOn fun y hy ↦ (hGc y hy).continuousWithinAt) hGK
  -- The triples `(y, Gs i y, DGs i y)` converge uniformly on `K` to `(y, G y, DG y)`, whose values
  -- form a compact set at which `D` is continuous.
  have hcpt : IsCompact ((fun y ↦ (y, G y, fderiv ℝ G y)) '' K) :=
    hK.image_of_continuousOn fun y hy ↦ (continuousAt_id.prodMk ((hGc y hy).prodMk
      ((hG y hy).continuousAt_fderiv one_ne_zero))).continuousWithinAt
  have hDc : ∀ p ∈ (fun y ↦ (y, G y, fderiv ℝ G y)) '' K, ContinuousAt D p := by
    rintro _ ⟨y, hy, rfl⟩
    have hi : ContinuousAt (fun p : E × (E →L[ℝ] E) × (E →L[ℝ] E →L[ℝ] E) ↦ p.2.1.inverse)
        (y, G y, fderiv ℝ G y) :=
      ContinuousAt.comp_of_eq (g := ContinuousLinearMap.inverse)
        (f := fun p : E × (E →L[ℝ] E) × (E →L[ℝ] E →L[ℝ] E) ↦ p.2.1)
        ((hGK y hy).contDiffAt_map_inverse (n := 0)).continuousAt continuousAt_snd.fst rfl
    have hfl : ContinuousAt
        (fun p : E × (E →L[ℝ] E) × (E →L[ℝ] E →L[ℝ] E) ↦ p.2.2.flip) (y, G y, fderiv ℝ G y) :=
      (ContinuousLinearMap.flipₗᵢ ℝ E E E).continuous.continuousAt.comp continuousAt_snd.snd
    have hH : ContinuousAt (fun p : E × (E →L[ℝ] E) × (E →L[ℝ] E →L[ℝ] E) ↦
        hessianOperator f p.1) (y, G y, fderiv ℝ G y) :=
      ((hf y hy).contDiffAt_hessianOperator (m := 0) (by norm_num)).continuousAt.comp
        continuousAt_fst
    have hgrad : ContinuousAt (fun p : E × (E →L[ℝ] E) × (E →L[ℝ] E →L[ℝ] E) ↦ ∇ f p.1)
        (y, G y, fderiv ℝ G y) :=
      ContinuousAt.comp_of_eq (g := ∇ f)
        (f := fun p : E × (E →L[ℝ] E) × (E →L[ℝ] E →L[ℝ] E) ↦ p.1)
        ((hf y hy).gradient_right (m := 0) (by norm_num)).continuousAt continuousAt_fst rfl
    exact hi.clm_comp (hH.sub (hfl.clm_apply (hi.clm_apply hgrad)))
  refine ((hcpt.comp_tendstoUniformlyOn hDc (hGG.prodMk_same hGG').graph).congr ?_).congr_right
    fun y hy ↦ (hD ((hG y hy).differentiableAt one_ne_zero) (hGK y hy) (hf y hy)).symm
  filter_upwards [hGs, hinv] with i hd hi y hy
  exact (hD (hd y hy) (hi y hy) (hf y hy)).symm

/-- **The Lyapunov inequality for the negative metric gradient.** At a nondegenerate critical
point `x`, if the quadratic form of `g` is coercive, `c ‖v‖² ≤ ⟪g v, v⟫` with `c > 0`, then
`κ ‖v‖² ≤ ⟪-Hess f(x) (-(g⁻¹ ∘ Hess f(x)) v), v⟫` for some `κ > 0`: the symmetric operator
`-Hess f(x)` is a Lyapunov form of `-(g⁻¹ ∘ Hess f(x))`, the linearization of
`-metricGradient G f` at `x` when `G x = g`. -/
private theorem IsNondegenerateCriticalPoint.exists_pos_mul_norm_sq_le_inner_neg_hessianOperator
    (h : IsNondegenerateCriticalPoint f x) {g : E →L[ℝ] E} {c : ℝ} (hc : 0 < c)
    (hg : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪g v, v⟫_ℝ) :
    ∃ κ > 0, ∀ v, κ * ‖v‖ ^ 2 ≤
      ⟪(-hessianOperator f x) ((-(g.inverse ∘L hessianOperator f x)) v), v⟫_ℝ := by
  have hK (w : E) : c / (‖g‖ + 1) ^ 2 * ‖w‖ ^ 2 ≤ ⟪g.inverse w, w⟫_ℝ := by
    simpa using g.mul_norm_sq_le_re_inner_inverse_apply hc (fun z ↦ by simpa using hg z) w
  obtain ⟨α, hα, hgap⟩ := h.exists_pos_mul_norm_le_hessianOperator
  refine ⟨c / (‖g‖ + 1) ^ 2 * α ^ 2, by positivity, fun v ↦ ?_⟩
  simpa using ContinuousLinearMap.mul_sq_mul_norm_sq_le_inner_apply_comp_apply
    h.contDiffAt.isSelfAdjoint_hessianOperator.isSymmetric (by positivity) hK hα.le hgap v

/-- **The linearization of the negative metric gradient has a Lyapunov form.** At a
nondegenerate critical point `x`, for a coercive `g`, the operator `-(g⁻¹ ∘ Hess f(x))` is
hyperbolic; it is the derivative of `-metricGradient G f` at `x` when `G x = g`. -/
theorem IsNondegenerateCriticalPoint.hasLyapunovForm_neg_inverse_comp_hessianOperator
    (h : IsNondegenerateCriticalPoint f x) {g : E →L[ℝ] E} {c : ℝ} (hc : 0 < c)
    (hg : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪g v, v⟫_ℝ) :
    (-(g.inverse ∘L hessianOperator f x)).HasLyapunovForm := by
  obtain ⟨κ, hκ, hS⟩ := h.exists_pos_mul_norm_sq_le_inner_neg_hessianOperator hc hg
  exact ContinuousLinearMap.hasLyapunovForm_iff.2 ⟨-hessianOperator f x,
    h.contDiffAt.isSelfAdjoint_hessianOperator.neg.isSymmetric, κ, hκ, hS⟩

end Field

section Hyperbolic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → ℝ} {x : E}

/-- **The unstable dimension of the negative metric gradient is the Morse index.** At a
nondegenerate critical point `x`, for every coercive `g`, the unstable subspace of
`-(g⁻¹ ∘ Hess f(x))` has dimension the Morse index of `f` at `x`. -/
theorem IsNondegenerateCriticalPoint.finrank_unstableSubspace_neg_inverse_comp_hessianOperator
    (h : IsNondegenerateCriticalPoint f x) {g : E →L[ℝ] E} {c : ℝ} (hc : 0 < c)
    (hg : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪g v, v⟫_ℝ) :
    finrank ℝ (-(g.inverse ∘L hessianOperator f x)).unstableSubspace = morseIndex f x := by
  obtain ⟨κ, hκ, hS⟩ := h.exists_pos_mul_norm_sq_le_inner_neg_hessianOperator hc hg
  rw [ContinuousLinearMap.finrank_unstableSubspace_eq_finrank_pointSpectralSubspace_Ioi
    h.contDiffAt.isSelfAdjoint_hessianOperator.neg.isSymmetric hκ hS,
    ContinuousLinearMap.toLinearMap_neg, Module.End.pointSpectralSubspace_neg, neg_Ioi, neg_zero,
    h.contDiffAt.morseIndex_eq_finrank_pointSpectralSubspace]

/-- **The stable dimension of the negative metric gradient is complementary to the Morse
index.** At a nondegenerate critical point `x`, for every coercive `g`, the stable subspace of
`-(g⁻¹ ∘ Hess f(x))` has dimension `dim E` minus the Morse index of `f` at `x`. -/
theorem IsNondegenerateCriticalPoint.finrank_stableSubspace_neg_inverse_comp_hessianOperator
    (h : IsNondegenerateCriticalPoint f x) {g : E →L[ℝ] E} {c : ℝ} (hc : 0 < c)
    (hg : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪g v, v⟫_ℝ) :
    finrank ℝ (-(g.inverse ∘L hessianOperator f x)).stableSubspace =
      finrank ℝ E - morseIndex f x := by
  obtain ⟨κ, hκ, hS⟩ := h.exists_pos_mul_norm_sq_le_inner_neg_hessianOperator hc hg
  rw [ContinuousLinearMap.finrank_stableSubspace_eq_finrank_pointSpectralSubspace_Iio
    h.contDiffAt.isSelfAdjoint_hessianOperator.neg.isSymmetric hκ hS,
    ContinuousLinearMap.toLinearMap_neg, Module.End.pointSpectralSubspace_neg, neg_Iio, neg_zero,
    ← h.contDiffAt.stableLinearSubspace_eq_pointSpectralSubspace,
    ← h.finrank_stableLinearSubspace_add_morseIndex, Nat.add_sub_cancel]

variable {G : E → E →L[ℝ] E} {n : ℕ}

/-- The hypotheses shared by the local stable and unstable graph theorems for
`-metricGradient G f`: the field is `C^n` at `x`, vanishes there, and has derivative
`A = -((G x)⁻¹ ∘ Hess f(x))`, and the flow of `A` has an exponential dichotomy. -/
private theorem IsNondegenerateCriticalPoint.exists_projection_hasFDerivAt_neg_metricGradient
    (h : IsNondegenerateCriticalPoint f x) (hn : 1 ≤ n) (hf : ContDiffAt ℝ (n + 1) f x)
    (hG : ContDiffAt ℝ n G x) {c : ℝ} (hc : 0 < c) (hGx : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪G x v, v⟫_ℝ) :
    ContDiffAt ℝ n (-metricGradient G f) x ∧ (-metricGradient G f) x = 0 ∧
      HasFDerivAt (-metricGradient G f) (-((G x).inverse ∘L hessianOperator f x)) x ∧
      ∃ P : E →L[ℝ] E, IsIdempotentElem P ∧
        Commute (-((G x).inverse ∘L hessianOperator f x)) P ∧ ∃ K α : ℝ≥0, 0 < K ∧ 0 < α ∧
        (∀ t : ℝ, 0 ≤ t → ∀ v : E, ‖NormedSpace.exp (t • -((G x).inverse ∘L
          hessianOperator f x)) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖) ∧
        (∀ t : ℝ, t ≤ 0 → ∀ v : E, ‖NormedSpace.exp (t • -((G x).inverse ∘L
          hessianOperator f x)) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖) := by
  have hGi : (G x).IsInvertible :=
    (G x).isInvertible_of_coercive hc fun v ↦ by simpa using hGx v
  refine ⟨(hf.metricGradient hG hGi).neg, ?_, (hasFDerivAt_metricGradient_of_fderiv_eq_zero
    h.contDiffAt h.fderiv_eq_zero
    (hG.differentiableAt (by exact_mod_cast Nat.one_le_iff_ne_zero.1 hn)) hGi).neg,
    (h.hasLyapunovForm_neg_inverse_comp_hessianOperator hc
    hGx).exists_projection_exponential_bounds⟩
  rw [Pi.neg_apply, (metricGradient_eq_zero_iff hGi).2 h.fderiv_eq_zero, neg_zero]

/-- **Local stable manifold of the negative gradient flow of a variable metric.** Let `x` be a
nondegenerate critical point of a function `f` that is `C^(n+1)` at `x`, with `n ≥ 1`, and let `G`
be a `C^n` field of operators whose quadratic form at `x` is coercive. Then there is a projection
`P` onto the stable subspace of the linearization `-(G x)⁻¹ ∘ Hess f(x)`, of dimension
`dim E - ind_x f`
(`TauCeti.IsNondegenerateCriticalPoint.finrank_stableSubspace_neg_inverse_comp_hessianOperator`),
such that the displacements `z` from `x` of all forward trajectories of `-metricGradient G f`
confined to a small ball, truncated by `‖P z‖ ≤ ρ`, form the graph of a Lipschitz map `g`, `C^n`
on the closed ball of radius `ρ`, with values in `ker P` and tangent to `range P` at the origin.
Every forward trajectory confined to that ball tends to `x`. -/
theorem IsNondegenerateCriticalPoint.exists_localStableGraph_neg_metricGradient
    (h : IsNondegenerateCriticalPoint f x) (hn : 1 ≤ n) (hf : ContDiffAt ℝ (n + 1) f x)
    (hG : ContDiffAt ℝ n G x) {c : ℝ} (hc : 0 < c) (hGx : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪G x v, v⟫_ℝ) :
    ∃ P : E →L[ℝ] E, IsIdempotentElem P ∧
      P.range = (-((G x).inverse ∘L hessianOperator f x)).stableSubspace ∧
      ∃ r > 0, ∃ ρ > 0, ∃ g : E → E, ∃ C : ℝ≥0,
        LipschitzWith C g ∧ g 0 = 0 ∧ HasFDerivAt g (0 : E →L[ℝ] E) 0 ∧
        (∀ z ∈ closedBall (0 : E) ρ, ContDiffAt ℝ n g z) ∧
        (∀ z, P (g z) = 0) ∧ (∀ z, g (P z) = g z) ∧
        {z : E | (∃ y : ℝ → E,
          IsIntegralCurveOn y (fun _ w ↦ -metricGradient G f (x + w)) (Ici 0) ∧
          y 0 = z ∧ MapsTo y (Ici 0) (closedBall 0 r)) ∧ ‖P z‖ ≤ ρ} =
          (fun z ↦ z + g z) '' (Set.range P ∩ closedBall 0 ρ) ∧
        (∀ y : ℝ → E, IsIntegralCurveOn y (fun _ w ↦ -metricGradient G f (x + w)) (Ici 0) →
          MapsTo y (Ici 0) (closedBall 0 r) → Tendsto y atTop (𝓝 0)) := by
  obtain ⟨hV, hx, hA, P, hP, hAP, K, α, -, hα, hs, hu⟩ :=
    h.exists_projection_hasFDerivAt_neg_metricGradient hn hf hG hc hGx
  obtain ⟨r, hr, ρ, hρ, g, C, hg⟩ :=
    ContinuousLinearMap.exists_localStableGraph_of_contDiffAt _ P hs hu hα hP hAP hn hV hx hA
  exact ⟨P, hP, ContinuousLinearMap.range_eq_stableSubspace_of_exponential_bounds
    (by exact_mod_cast hα) hP hAP hs hu, r, hr, ρ, hρ, g, C, by simpa only [Pi.neg_apply] using hg⟩

/-- **Local unstable manifold of the negative gradient flow of a variable metric.** Under the
hypotheses of `TauCeti.IsNondegenerateCriticalPoint.exists_localStableGraph_neg_metricGradient`,
there is a projection `P` such that `1 - P` projects onto the unstable subspace of the
linearization `-(G x)⁻¹ ∘ Hess f(x)`, of dimension the Morse index of `f` at `x`
(`TauCeti.IsNondegenerateCriticalPoint.finrank_unstableSubspace_neg_inverse_comp_hessianOperator`),
and the displacements `z` from `x` of all backward trajectories of `-metricGradient G f` confined
to a small ball, truncated by `‖z - P z‖ ≤ ρ`, form the graph of a Lipschitz map `g`, `C^n` on the
closed ball of radius `ρ`, with values in `range P` and tangent to `range (1 - P)` at the origin.
Every backward trajectory confined to that ball tends to `x` as time tends to `-∞`. -/
theorem IsNondegenerateCriticalPoint.exists_localUnstableGraph_neg_metricGradient
    (h : IsNondegenerateCriticalPoint f x) (hn : 1 ≤ n) (hf : ContDiffAt ℝ (n + 1) f x)
    (hG : ContDiffAt ℝ n G x) {c : ℝ} (hc : 0 < c) (hGx : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪G x v, v⟫_ℝ) :
    ∃ P : E →L[ℝ] E, IsIdempotentElem P ∧
      (ContinuousLinearMap.id ℝ E - P).range =
        (-((G x).inverse ∘L hessianOperator f x)).unstableSubspace ∧
      ∃ r > 0, ∃ ρ > 0, ∃ g : E → E, ∃ C : ℝ≥0,
        LipschitzWith C g ∧ g 0 = 0 ∧ HasFDerivAt g (0 : E →L[ℝ] E) 0 ∧
        (∀ z ∈ closedBall (0 : E) ρ, ContDiffAt ℝ n g z) ∧
        (∀ z, (ContinuousLinearMap.id ℝ E - P) (g z) = 0) ∧
        (∀ z, g ((ContinuousLinearMap.id ℝ E - P) z) = g z) ∧
        {z : E | (∃ y : ℝ → E,
          IsIntegralCurveOn y (fun _ w ↦ -metricGradient G f (x + w)) (Iic 0) ∧
          y 0 = z ∧ MapsTo y (Iic 0) (closedBall 0 r)) ∧ ‖z - P z‖ ≤ ρ} =
          (fun z ↦ z + g z) '' (Set.range (ContinuousLinearMap.id ℝ E - P) ∩ closedBall 0 ρ) ∧
        (∀ y : ℝ → E, IsIntegralCurveOn y (fun _ w ↦ -metricGradient G f (x + w)) (Iic 0) →
          MapsTo y (Iic 0) (closedBall 0 r) → Tendsto y atBot (𝓝 0)) := by
  obtain ⟨hV, hx, hA, P, hP, hAP, K, α, -, hα, hs, hu⟩ :=
    h.exists_projection_hasFDerivAt_neg_metricGradient hn hf hG hc hGx
  obtain ⟨r, hr, ρ, hρ, g, C, hg⟩ :=
    ContinuousLinearMap.exists_localUnstableGraph_of_contDiffAt _ P hs hu hα hP hAP hn hV hx hA
  exact ⟨P, hP, ContinuousLinearMap.range_id_sub_eq_unstableSubspace_of_exponential_bounds
    (by exact_mod_cast hα) hP hAP hs hu, r, hr, ρ, hρ, g, C, by simpa only [Pi.neg_apply] using hg⟩

section MetricDependence

/-! ### Dependence of the local stable and unstable manifolds on the metric -/

variable {ι : Type*} {l : Filter ι} {Gs : ι → E → E →L[ℝ] E} {U : Set E}

namespace IsNondegenerateCriticalPoint

/-- The hypotheses of `ContinuousLinearMap.exists_localStableGraph_tendstoUniformlyOn_fderiv` for
the negative metric gradients of `f` along metric fields `Gs i` converging in `C¹` to `G` near a
nondegenerate critical point `x`: on a neighbourhood `K` of `x`, the fields `-metricGradient G f`
and, eventually, `-metricGradient (Gs i) f` are `C¹`, they all vanish at `x`, and their
derivatives converge uniformly on `K`. -/
private theorem exists_mem_nhds_tendstoUniformlyOn_fderiv_neg
    (h : IsNondegenerateCriticalPoint f x) (hG : ContDiffAt ℝ 1 G x) (hGx : (G x).IsInvertible)
    (hU : U ∈ 𝓝 x) (hGsU : ∀ᶠ i in l, ContDiffOn ℝ 1 (Gs i) U) (hGG : TendstoUniformlyOn Gs G l U)
    (hGG' : TendstoUniformlyOn (fun i ↦ fderiv ℝ (Gs i)) (fderiv ℝ G) l U) :
    ∃ K ∈ 𝓝 x, ContDiffOn ℝ 1 (-metricGradient G f) K ∧
      (∀ᶠ i in l, ContDiffOn ℝ 1 (-metricGradient (Gs i) f) K) ∧
      (∀ i, (-metricGradient (Gs i) f) x = 0) ∧
      TendstoUniformlyOn (fun i ↦ fderiv ℝ (-metricGradient (Gs i) f))
        (fderiv ℝ (-metricGradient G f)) l K := by
  -- Work on a closed ball `K` inside the interior of `U` on which `f` is `C²` and `G` is `C¹` and
  -- invertible.
  have hev : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 f y ∧ ContDiffAt ℝ 1 G y ∧ (G y).IsInvertible ∧
      y ∈ interior U :=
    (h.contDiffAt.eventually (by simp)).and ((hG.eventually (by simp)).and
      ((hG.continuousAt.eventually hGx.eventually_nhds).and (interior_mem_nhds.2 hU)))
  obtain ⟨ε, hε, hεK⟩ := nhds_basis_closedBall.mem_iff.1 hev
  have hKU : closedBall x ε ⊆ U := fun y hy ↦ interior_subset (hεK hy).2.2.2
  have hK := isCompact_closedBall x ε
  have hGsK : ∀ᶠ i in l, ∀ y ∈ closedBall x ε, ContDiffAt ℝ 1 (Gs i) y :=
    hGsU.mono fun i hi y hy ↦ hi.contDiffAt (mem_interior_iff_mem_nhds.1 (hεK hy).2.2.2)
  have hinv := (hGG.mono hKU).eventually_forall_isInvertible (hK.image_of_continuousOn
    fun y hy ↦ (hεK hy).2.1.continuousAt.continuousWithinAt) fun y hy ↦ (hεK hy).2.2.1
  have hfg {H : E → E →L[ℝ] E} {y : E} (hy : y ∈ closedBall x ε) (hH : ContDiffAt ℝ 1 H y)
      (hHy : (H y).IsInvertible) : ContDiffWithinAt ℝ 1 (-metricGradient H f) (closedBall x ε) y :=
    ((hεK hy).1.of_le (by norm_num) |>.metricGradient hH hHy).neg.contDiffWithinAt
  refine ⟨closedBall x ε, closedBall_mem_nhds x hε,
    fun y hy ↦ hfg hy (hεK hy).2.1 (hεK hy).2.2.1, ?_, fun i ↦ ?_, ?_⟩
  · filter_upwards [hGsK, hinv] with i hi hii y hy
    exact hfg hy (hi y hy) (hii y hy)
  · rw [Pi.neg_apply, metricGradient_apply, gradient_eq_zero_iff.2 h.fderiv_eq_zero, map_zero,
      neg_zero]
  · have hneg (H : E → E →L[ℝ] E) :
        fderiv ℝ (-metricGradient H f) = -fderiv ℝ (metricGradient H f) :=
      funext fun _ ↦ fderiv_neg
    simp only [hneg]
    exact uniformContinuous_neg.comp_tendstoUniformlyOn
      (tendstoUniformlyOn_fderiv_metricGradient hK (fun y hy ↦ (hεK hy).1)
        (fun y hy ↦ (hεK hy).2.1) (fun y hy ↦ (hεK hy).2.2.1)
        (hGsK.mono fun i hi y hy ↦ (hi y hy).differentiableAt one_ne_zero) (hGG.mono hKU)
        (hGG'.mono hKU))

/-- **Local stable manifolds depend continuously in `C¹` on the metric.** Let `x` be a
nondegenerate critical point of `f`, and let `G` be a `C¹` field of operators whose quadratic form
at `x` is coercive. Let metric fields `Gs i` converge to `G` in `C¹` on a neighbourhood `U` of `x`:
they are eventually `C¹` on `U`, and `Gs i → G` and `DGs i → DG` uniformly on `U`. Then for a
projection `P` onto the stable subspace of the linearization `-(G x)⁻¹ ∘ Hess f(x)`, and for one
confinement radius `r` and one parameter radius `ρ`, the local stable sets at `x` of
`-metricGradient G f` and, eventually, of `-metricGradient (Gs i) f`, read in displacement
coordinates and truncated by `‖P z‖ ≤ ρ`, are the graphs over `range P ∩ closedBall 0 ρ` of maps
`g` and `gs i` that are `C¹` on the closed ball of radius `ρ`. The maps `gs i` converge to `g`
uniformly, and their derivatives converge uniformly on the closed ball of radius `ρ`. -/
theorem exists_localStableGraph_neg_metricGradient_tendstoUniformlyOn_fderiv
    (h : IsNondegenerateCriticalPoint f x) (hG : ContDiffAt ℝ 1 G x) {c : ℝ} (hc : 0 < c)
    (hGx : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪G x v, v⟫_ℝ) (hU : U ∈ 𝓝 x)
    (hGsU : ∀ᶠ i in l, ContDiffOn ℝ 1 (Gs i) U) (hGG : TendstoUniformlyOn Gs G l U)
    (hGG' : TendstoUniformlyOn (fun i ↦ fderiv ℝ (Gs i)) (fderiv ℝ G) l U) :
    ∃ P : E →L[ℝ] E, IsIdempotentElem P ∧
      P.range = (-((G x).inverse ∘L hessianOperator f x)).stableSubspace ∧
      ∃ r > 0, ∃ ρ > 0, ∃ g : E → E, ∃ gs : ι → E → E,
        {z : E | (∃ y : ℝ → E,
          IsIntegralCurveOn y (fun _ w ↦ -metricGradient G f (x + w)) (Ici 0) ∧
          y 0 = z ∧ MapsTo y (Ici 0) (closedBall 0 r)) ∧ ‖P z‖ ≤ ρ} =
          (fun z ↦ z + g z) '' (Set.range P ∩ closedBall 0 ρ) ∧
        (∀ z ∈ closedBall (0 : E) ρ, ContDiffAt ℝ 1 g z) ∧
        (∀ᶠ i in l, {z : E | (∃ y : ℝ → E,
            IsIntegralCurveOn y (fun _ w ↦ -metricGradient (Gs i) f (x + w)) (Ici 0) ∧
            y 0 = z ∧ MapsTo y (Ici 0) (closedBall 0 r)) ∧ ‖P z‖ ≤ ρ} =
            (fun z ↦ z + gs i z) '' (Set.range P ∩ closedBall 0 ρ) ∧
          ∀ z ∈ closedBall (0 : E) ρ, ContDiffAt ℝ 1 (gs i) z) ∧
        TendstoUniformly gs g l ∧
        TendstoUniformlyOn (fun i ↦ fderiv ℝ (gs i)) (fderiv ℝ g) l (closedBall 0 ρ) := by
  obtain ⟨-, hx, hA, P, hP, hAP, K, α, -, hα, hs, hu⟩ :=
    h.exists_projection_hasFDerivAt_neg_metricGradient (n := 1) le_rfl
      (h.contDiffAt.of_le (by norm_num)) (by exact_mod_cast hG) hc hGx
  obtain ⟨V, hV, hVV, hVs, hVsx, hV'⟩ :=
    h.exists_mem_nhds_tendstoUniformlyOn_fderiv_neg hG
      ((G x).isInvertible_of_coercive hc fun v ↦ by simpa using hGx v) hU hGsU hGG hGG'
  obtain ⟨r, hr, ρ, hρ, g, gs, hg⟩ :=
    ContinuousLinearMap.exists_localStableGraph_tendstoUniformlyOn_fderiv _ P hs hu hα hP hAP hV
      hVV hx hA hVs tendsto_const_nhds (.of_forall hVsx) hV'
  exact ⟨P, hP, ContinuousLinearMap.range_eq_stableSubspace_of_exponential_bounds
    (by exact_mod_cast hα) hP hAP hs hu, r, hr, ρ, hρ, g, gs,
    by simpa only [Pi.neg_apply] using hg⟩

/-- **Local unstable manifolds depend continuously in `C¹` on the metric.** Under the hypotheses
of `exists_localStableGraph_neg_metricGradient_tendstoUniformlyOn_fderiv`, for a projection `P`
such that `1 - P` projects onto the unstable subspace of the linearization `-(G x)⁻¹ ∘ Hess f(x)`,
and for one confinement radius `r` and one parameter radius `ρ`, the local unstable sets at `x` of
`-metricGradient G f` and, eventually, of `-metricGradient (Gs i) f`, read in displacement
coordinates and truncated by `‖z - P z‖ ≤ ρ`, are the graphs over `range (1 - P) ∩ closedBall 0 ρ`
of maps `g` and `gs i` that are `C¹` on the closed ball of radius `ρ`. The maps `gs i` converge to
`g` uniformly, and their derivatives converge uniformly on the closed ball of radius `ρ`. -/
theorem exists_localUnstableGraph_neg_metricGradient_tendstoUniformlyOn_fderiv
    (h : IsNondegenerateCriticalPoint f x) (hG : ContDiffAt ℝ 1 G x) {c : ℝ} (hc : 0 < c)
    (hGx : ∀ v, c * ‖v‖ ^ 2 ≤ ⟪G x v, v⟫_ℝ) (hU : U ∈ 𝓝 x)
    (hGsU : ∀ᶠ i in l, ContDiffOn ℝ 1 (Gs i) U) (hGG : TendstoUniformlyOn Gs G l U)
    (hGG' : TendstoUniformlyOn (fun i ↦ fderiv ℝ (Gs i)) (fderiv ℝ G) l U) :
    ∃ P : E →L[ℝ] E, IsIdempotentElem P ∧
      (ContinuousLinearMap.id ℝ E - P).range =
        (-((G x).inverse ∘L hessianOperator f x)).unstableSubspace ∧
      ∃ r > 0, ∃ ρ > 0, ∃ g : E → E, ∃ gs : ι → E → E,
        {z : E | (∃ y : ℝ → E,
          IsIntegralCurveOn y (fun _ w ↦ -metricGradient G f (x + w)) (Iic 0) ∧
          y 0 = z ∧ MapsTo y (Iic 0) (closedBall 0 r)) ∧ ‖z - P z‖ ≤ ρ} =
          (fun z ↦ z + g z) '' (Set.range (ContinuousLinearMap.id ℝ E - P) ∩ closedBall 0 ρ) ∧
        (∀ z ∈ closedBall (0 : E) ρ, ContDiffAt ℝ 1 g z) ∧
        (∀ᶠ i in l, {z : E | (∃ y : ℝ → E,
            IsIntegralCurveOn y (fun _ w ↦ -metricGradient (Gs i) f (x + w)) (Iic 0) ∧
            y 0 = z ∧ MapsTo y (Iic 0) (closedBall 0 r)) ∧ ‖z - P z‖ ≤ ρ} =
            (fun z ↦ z + gs i z) ''
              (Set.range (ContinuousLinearMap.id ℝ E - P) ∩ closedBall 0 ρ) ∧
          ∀ z ∈ closedBall (0 : E) ρ, ContDiffAt ℝ 1 (gs i) z) ∧
        TendstoUniformly gs g l ∧
        TendstoUniformlyOn (fun i ↦ fderiv ℝ (gs i)) (fderiv ℝ g) l (closedBall 0 ρ) := by
  obtain ⟨-, hx, hA, P, hP, hAP, K, α, -, hα, hs, hu⟩ :=
    h.exists_projection_hasFDerivAt_neg_metricGradient (n := 1) le_rfl
      (h.contDiffAt.of_le (by norm_num)) (by exact_mod_cast hG) hc hGx
  obtain ⟨V, hV, hVV, hVs, hVsx, hV'⟩ :=
    h.exists_mem_nhds_tendstoUniformlyOn_fderiv_neg hG
      ((G x).isInvertible_of_coercive hc fun v ↦ by simpa using hGx v) hU hGsU hGG hGG'
  obtain ⟨r, hr, ρ, hρ, g, gs, hg⟩ :=
    ContinuousLinearMap.exists_localUnstableGraph_tendstoUniformlyOn_fderiv _ P hs hu hα hP hAP hV
      hVV hx hA hVs tendsto_const_nhds (.of_forall hVsx) hV'
  exact ⟨P, hP, ContinuousLinearMap.range_id_sub_eq_unstableSubspace_of_exponential_bounds
    (by exact_mod_cast hα) hP hAP hs hu, r, hr, ρ, hρ, g, gs,
    by simpa only [Pi.neg_apply] using hg⟩

end IsNondegenerateCriticalPoint

end MetricDependence

end Hyperbolic

end TauCeti
