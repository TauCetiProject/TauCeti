/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.SpectralSplitting
public import TauCeti.Analysis.InnerProductSpace.LyapunovForm.Inertia
public import TauCeti.Analysis.ODE.LyapunovPerron.VectorField
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.InnerProductSpace.Coercive
import TauCeti.Analysis.ODE.ExponentialDichotomy
import TauCeti.Analysis.ODE.ExponentialDichotomy.Hyperbolic
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
  `metricGradient G f` is `C^n` at `x` (`ContDiffAt.metricGradient`). At a critical point its
  derivative is `(G x)⁻¹ ∘ Hess f(x)` (`TauCeti.hasFDerivAt_metricGradient`): the derivative of
  the metric drops out because `∇ f x = 0`.
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

These are local graph theorems at one critical point for a fixed metric; the global stable and
unstable manifolds and their dependence on the metric are not treated here.

## Main declarations

* `TauCeti.metricGradient`: the gradient `(G y)⁻¹ (∇ f y)` of `f` for the metric
  `g_y(u, v) = ⟪G y u, v⟫`.
* `TauCeti.eq_metricGradient_iff` and `TauCeti.inner_apply_metricGradient`: its characterization
  `⟪G y (metricGradient G f y), v⟫ = df_y v`.
* `TauCeti.metricGradient_eq_zero_iff`: its zeros are the critical points of `f`.
* `ContDiffAt.metricGradient` and `TauCeti.hasFDerivAt_metricGradient`: its regularity and its
  derivative at a critical point.
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

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2 (stable and unstable manifolds of a pseudo-gradient field).
* C. Chicone, *Ordinary Differential Equations with Applications*, 2nd ed., Springer, 2006,
  §4.3 (the stable-manifold theorem).
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

/-- **The derivative of the metric gradient at a critical point** is `(G x)⁻¹ ∘ Hess f(x)`: the
derivative of the metric does not contribute, because the gradient vanishes at `x`. -/
theorem hasFDerivAt_metricGradient (hf : ContDiffAt ℝ 2 f x) (hx : fderiv ℝ f x = 0)
    (hG : DifferentiableAt ℝ G x) (hGx : (G x).IsInvertible) :
    HasFDerivAt (metricGradient G f) ((G x).inverse ∘L hessianOperator f x) x := by
  have hinv : DifferentiableAt ℝ (fun y ↦ (G y).inverse) x :=
    ((hGx.contDiffAt_map_inverse (n := 1)).differentiableAt one_ne_zero).comp x hG
  have h := hinv.hasFDerivAt.clm_apply hf.hasFDerivAt_gradient
  rw [gradient_eq_zero_iff.2 hx, map_zero, add_zero] at h
  rwa [funext (metricGradient_apply G f)]

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
  refine ⟨(hf.metricGradient hG hGi).neg, ?_, (hasFDerivAt_metricGradient h.contDiffAt
    h.fderiv_eq_zero (hG.differentiableAt (by exact_mod_cast Nat.one_le_iff_ne_zero.1 hn))
    hGi).neg, (h.hasLyapunovForm_neg_inverse_comp_hessianOperator hc
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

end Hyperbolic

end TauCeti
