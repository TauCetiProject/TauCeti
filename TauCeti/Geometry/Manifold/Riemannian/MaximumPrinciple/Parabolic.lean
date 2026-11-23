/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen, The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MaximumPrinciple.Parabolic.Basic
public import TauCeti.Geometry.Manifold.Riemannian.MaximumPrinciple
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

/-!
# Parabolic comparison principles on manifolds with evolving metrics

Let `g t` be a Riemannian metric on a boundaryless manifold `M` for each time `t`. This file
proves comparison principles for scalar parabolic operators built from the Laplace–Beltrami
operator `Δ_{g t} = div ∘ grad` of the metric at time `t`.

**Compact-domain heat comparison.** On a boundaryless C² manifold, heat subsolutions lie below
supersolutions on a compact spatial domain when this holds initially and on its spatial
boundary. The metric may vary arbitrarily in time: only C¹ regularity of each spatial slice is
required. The proof uses the native Laplace–Beltrami sign at a spatial local maximum and the
abstract weak parabolic principle.

**Reaction–drift comparison on a closed manifold.** Let `M` be compact. We consider the operator

`∂ₜu - Δ_{g t} u - b·∇u - F(t, u)`,

where `b` is a time-dependent vector field and `F` is a reaction term. The drift term
`b·∇u = g(b, grad u)` is the differential `du(b)`, spelled `mvfderiv I (u t) x (b t x)`, so it does
not involve the metric. A function `u : ℝ → M → ℝ` (time first, so `u t` is the spatial slice at
time `t`) is a subsolution when the operator is nonpositive on `u`, and a supersolution when it is
nonnegative.

Let `u` be a subsolution and `v` a supersolution on `(0, T) × M`, both continuous on
`[0, T] × M`, `C²` in space and differentiable in time, and let `F(t, ·)` be Lipschitz on bounded
sets, uniformly in `t`. If `u ≤ v` at time `0`, then `u ≤ v` on `[0, T] × M`. At a spatial
maximum of `u t - v t` the Laplacian of `u t - v t` is nonpositive and its differential vanishes,
so `∂ₜ(u - v) ≤ F(t, u) - F(t, v) ≤ L (u - v)` there, and the Grönwall form of the perturbation
argument, `TauCeti.le_of_deriv_sub_deriv_le_mul_of_isLocalMax_le_parabolicBoundary`, applies. The
Lipschitz constant is taken on a ball containing the values of `u` and `v`, which are bounded by
compactness. The metrics enter only through the sign of their Laplacians at a maximum, so no
regularity of `g` in time is needed.

**ODE comparison.** A spatially constant function `φ(t)` with `φ' ≥ F(t, φ)` is a supersolution,
and one with `φ' ≤ F(t, φ)` is a subsolution. Hence a subsolution starting below `φ(0)` stays below
`φ(t)`, and a supersolution starting above `φ(0)` stays above it: the extrema of the solution of
the parabolic equation are controlled by the ODE `φ' = F(t, φ)`. For instance, along Ricci flow the
scalar curvature of an `n`-manifold satisfies `∂ₜ Scal ≥ Δ Scal + (2/n) Scal²`, and comparison
with the Riccati equation `φ' = (2/n) φ²` gives `Scal ≥ s₀ / (1 - 2 s₀ t / n)` whenever
`Scal ≥ s₀` at time `0`, as long as `1 - 2 s₀ t / n > 0`.

## Main results

* `TauCeti.Manifold.compactDomain_heat_comparison`: compact-domain comparison for native metrics.
* `TauCeti.Manifold.le_of_deriv_sub_laplaceBeltrami_sub_mvfderiv_sub_le_of_le`: the comparison
  principle when `F(t, ·)` is Lipschitz from above between the two functions.
* `TauCeti.Manifold.le_of_deriv_sub_laplaceBeltrami_sub_mvfderiv_sub_le_of_lipschitzOnWith`: the
  comparison principle for a reaction which is Lipschitz on bounded sets, uniformly in time.
* `TauCeti.Manifold.le_of_deriv_le_laplaceBeltrami_add_mvfderiv_add_of_le_deriv`: a subsolution
  stays below a supersolution of the ODE `φ' = F(t, φ)`.
* `TauCeti.Manifold.ge_of_laplaceBeltrami_add_mvfderiv_add_le_deriv_of_deriv_le`: a supersolution
  stays above a subsolution of the ODE `φ' = F(t, φ)`.
* `TauCeti.Manifold.div_one_sub_mul_le_of_laplaceBeltrami_add_mvfderiv_add_mul_sq_le_deriv`: the
  Riccati lower bound `u ≥ s₀ / (1 - c s₀ t)` for supersolutions of `∂ₜu = Δu + b·∇u + c u²`,
  as long as `1 - c s₀ t > 0`.

## References

* R. S. Hamilton, *Three-manifolds with positive Ricci curvature*, J. Differential Geom. 17
  (1982), 255–306.
* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Corollary 4.14.
* P. Topping, *Lectures on the Ricci Flow*, LMS Lecture Note Series 325, Cambridge University
  Press (2006), Chapter 3 (the scalar maximum principle and the lower bound for scalar
  curvature).
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

noncomputable section

open Bundle CovariantDerivative Set Topology Filter
open scoped ContDiff Manifold NNReal

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]


/-- Heat subsolutions lie below supersolutions on a compact spatial domain. -/
theorem compactDomain_heat_comparison [I.Boundaryless] [T2Space M]
    (g : ℝ → ContMDiffRiemannianMetric I 1 E (TangentSpace I : M → Type _))
    {a b : ℝ} {U C : Set M}
    (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U)
    (u v f w : ℝ → M → ℝ)
    (hu : ContinuousOn (Function.uncurry u) (Icc a b ×ˢ C))
    (hf : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ C))
    (hud : ∀ t ∈ Ioo a b, ∀ x ∈ interior C,
      HasDerivAt (fun s ↦ u s x) (v t x) t)
    (hfd : ∀ t ∈ Ioo a b, ∀ x ∈ interior C,
      HasDerivAt (fun s ↦ f s x) (w t x) t)
    (hus : ∀ t ∈ Ioo a b, ContMDiffOn I 𝓘(ℝ) 2 (u t) U)
    (hfs : ∀ t ∈ Ioo a b, ContMDiffOn I 𝓘(ℝ) 2 (f t) U)
    (hinit : ∀ x ∈ C, u a x ≤ f a x)
    (hboundary : ∀ t ∈ Icc a b, ∀ x ∈ C \ interior C, u t x ≤ f t x)
    (hevol : ∀ t ∈ Ioo a b, ∀ x ∈ interior C,
      let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g t).toRiemannianMetric⟩
      v t x - laplaceBeltrami I (u t) x ≤ w t x - laplaceBeltrami I (f t) x) :
    ∀ t ∈ Icc a b, ∀ x ∈ C, u t x ≤ f t x := by
  have h := le_of_hasDerivAt_nonpos_of_isLocalMax_Icc hC (hu.sub hf)
    (u := fun t x ↦ u t x - f t x) (v := fun t x ↦ v t x - w t x)
    (by
      intro t ht x hx
      exact (hud t ht x hx).sub (hfd t ht x hx))
    (by
      intro t ht x hx hmax _
      let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g t).toRiemannianMetric⟩
      have hmax' : IsLocalMax (fun y ↦ u t y + (-1) * f t y) x := by
        simpa only [neg_one_mul, sub_eq_add_neg] using hmax
      have hlap := laplaceBeltrami_add_mul_nonpos_of_isLocalMax
        (((hus t ht).contMDiffAt
          (hU.mem_nhds (hCU (interior_subset hx)))).of_le (by simp))
        (((hfs t ht).contMDiffAt
          (hU.mem_nhds (hCU (interior_subset hx)))).of_le (by simp)) hmax'
      have he := hevol t ht x hx
      linarith)
    (fun x hx ↦ sub_nonpos.mpr (hinit x hx))
    (fun t ht x hx ↦ sub_nonpos.mpr (hboundary t ht x
      ⟨hC.isClosed.closure_eq ▸ hx.1, hx.2⟩))
  exact fun t ht x hx ↦ sub_nonpos.mp (h t ht x hx)


section ClosedManifold

variable [I.Boundaryless] [CompactSpace M]
  {n : ℕ∞ω} {g : ℝ → ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)}
  {T : ℝ} {u v : ℝ → M → ℝ} {b : (t : ℝ) → (x : M) → TangentSpace I x} {F : ℝ → ℝ → ℝ}

/-- **Comparison principle for `∂ₜ - Δ_{g t} - b·∇ - F` on a closed manifold.**

Let `u` and `v` be continuous on `[0, T] × M`, `C²` in space and differentiable in time on
`(0, T) × M`, with `∂ₜu - Δ_{g t} u - b·∇u - F(t, u) ≤ ∂ₜv - Δ_{g t} v - b·∇v - F(t, v)` there.
Suppose that `F(t, u) - F(t, v) ≤ L (u - v)` wherever `u > v`. If `u ≤ v` at time `0`, then
`u ≤ v` on all of `[0, T] × M`. -/
theorem le_of_deriv_sub_laplaceBeltrami_sub_mvfderiv_sub_le_of_le (hn : 1 ≤ n) {L : ℝ}
    (hucont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hvcont : ContinuousOn (Function.uncurry v) (Icc 0 T ×ˢ univ))
    (hucd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ContMDiff I 𝓘(ℝ) 2 (u t))
    (hvcd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ContMDiff I 𝓘(ℝ) 2 (v t))
    (hudiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hvdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, DifferentiableAt ℝ (fun s ↦ v s x) t)
    (hL : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x,
      deriv (fun s ↦ u s x) t -
          (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
            letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
              IsContMDiffRiemannianBundle.of_le hn;
            laplaceBeltrami I (u t) x) - mvfderiv I (u t) x (b t x) - F t (u t x) ≤
        deriv (fun s ↦ v s x) t -
          (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
            letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
              IsContMDiffRiemannianBundle.of_le hn;
            laplaceBeltrami I (v t) x) - mvfderiv I (v t) x (b t x) - F t (v t x))
    (hF : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, v t x < u t x →
      F t (u t x) - F t (v t x) ≤ L * (u t x - v t x))
    (hinit : ∀ x, u 0 x ≤ v 0 x) :
    ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ x, u t x ≤ v t x := by
  intro t ht x
  refine sub_nonpos.mp <| le_of_deriv_sub_deriv_le_mul_of_isLocalMax_le_parabolicBoundary
    (u := fun s y ↦ u s y - v s y) (φ := 0) (L := L) isCompact_univ (hucont.sub hvcont)
    continuousOn_const (fun s hs y _ ↦ (hudiff hs y).fun_sub (hvdiff hs y))
    (fun _ _ ↦ differentiableAt_const _) (fun s hs y _ hmax hpos ↦ ?_)
    (fun y _ ↦ sub_nonpos.mpr (hinit y)) (fun s _ y hy ↦ by simp at hy) ht (mem_univ x)
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g s).toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le hn
  -- At a spatial maximum of `u s - v s` the Laplacian of `u s - v s` is nonpositive ...
  have hΔ : laplaceBeltrami I (u s - v s) y ≤ 0 :=
    laplaceBeltrami_nonpos_of_isLocalMax ((hucd hs).sub (hvcd hs)).contMDiffAt hmax
  rw [laplaceBeltrami_sub I (hucd hs) (hvcd hs)] at hΔ
  -- ... and its differential vanishes, so the drift terms agree.
  have hd : mvfderiv I (u s) y = mvfderiv I (v s) y := by
    have h :=
      mem_criticalPoints.mp (IsLocalMax.mem_criticalPoints (I := I) (f := u s - v s) hmax)
    rwa [mvfderiv_sub (((hucd hs).mdifferentiable (by norm_num)) y)
      (((hvcd hs).mdifferentiable (by norm_num)) y), sub_eq_zero] at h
  simp only [Pi.zero_apply, sub_pos, sub_zero] at hpos ⊢
  rw [deriv_fun_sub (hudiff hs y) (hvdiff hs y), deriv_zero, Pi.zero_apply]
  have h1 := hL hs y
  rw [hd] at h1
  linarith [hF hs y hpos]

/-- **Comparison principle for `∂ₜ - Δ_{g t} - b·∇ - F` on a closed manifold, with a reaction
that is Lipschitz on bounded sets.**

Let `u` and `v` be continuous on `[0, T] × M`, `C²` in space and differentiable in time on
`(0, T) × M`, with `∂ₜu - Δ_{g t} u - b·∇u - F(t, u) ≤ ∂ₜv - Δ_{g t} v - b·∇v - F(t, v)` there,
and suppose that `F(t, ·)` is Lipschitz on every bounded set, with a constant independent of
`t`. If `u ≤ v` at time `0`, then `u ≤ v` on all of `[0, T] × M`. -/
theorem le_of_deriv_sub_laplaceBeltrami_sub_mvfderiv_sub_le_of_lipschitzOnWith (hn : 1 ≤ n)
    (hucont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hvcont : ContinuousOn (Function.uncurry v) (Icc 0 T ×ˢ univ))
    (hucd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ContMDiff I 𝓘(ℝ) 2 (u t))
    (hvcd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ContMDiff I 𝓘(ℝ) 2 (v t))
    (hudiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hvdiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, DifferentiableAt ℝ (fun s ↦ v s x) t)
    (hL : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x,
      deriv (fun s ↦ u s x) t -
          (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
            letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
              IsContMDiffRiemannianBundle.of_le hn;
            laplaceBeltrami I (u t) x) - mvfderiv I (u t) x (b t x) - F t (u t x) ≤
        deriv (fun s ↦ v s x) t -
          (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
            letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
              IsContMDiffRiemannianBundle.of_le hn;
            laplaceBeltrami I (v t) x) - mvfderiv I (v t) x (b t x) - F t (v t x))
    (hF : ∀ R : ℝ≥0, ∃ K : ℝ≥0, ∀ ⦃t⦄, t ∈ Ioo 0 T →
      LipschitzOnWith K (F t) (Metric.closedBall 0 R))
    (hinit : ∀ x, u 0 x ≤ v 0 x) :
    ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ x, u t x ≤ v t x := by
  -- The values of `u` and `v` on the compact cylinder lie in a common ball.
  have hcpt : IsCompact (Icc 0 T ×ˢ (univ : Set M)) := isCompact_Icc.prod isCompact_univ
  obtain ⟨Cu, hCu⟩ := hcpt.exists_bound_of_continuousOn hucont
  obtain ⟨Cv, hCv⟩ := hcpt.exists_bound_of_continuousOn hvcont
  obtain ⟨K, hK⟩ := hF (max Cu Cv).toNNReal
  have hball {w : ℝ → M → ℝ} {C : ℝ} (hC : ∀ p ∈ Icc 0 T ×ˢ (univ : Set M),
      ‖Function.uncurry w p‖ ≤ C) (hCle : C ≤ max Cu Cv) ⦃t : ℝ⦄ (ht : t ∈ Ioo 0 T) (x : M) :
      w t x ∈ Metric.closedBall (0 : ℝ) (max Cu Cv).toNNReal := by
    rw [mem_closedBall_zero_iff]
    exact (hC (t, x) ⟨Ioo_subset_Icc_self ht, mem_univ x⟩).trans
      (hCle.trans (le_max_left _ 0)) |>.trans_eq (Real.coe_toNNReal' _).symm
  refine le_of_deriv_sub_laplaceBeltrami_sub_mvfderiv_sub_le_of_le hn (L := K) hucont hvcont hucd
    hvcd hudiff hvdiff hL (fun t ht x hlt ↦ ?_) hinit
  have h := (hK ht).dist_le_mul _ (hball hCu (le_max_left _ _) ht x) _
    (hball hCv (le_max_right _ _) ht x)
  rw [Real.dist_eq, Real.dist_eq, abs_of_pos (sub_pos.mpr hlt)] at h
  exact (le_abs_self _).trans h

/-- **Comparison with an ODE supersolution.** Let `u` be continuous on `[0, T] × M`, `C²` in
space and differentiable in time on `(0, T) × M`, with `∂ₜu ≤ Δ_{g t} u + b·∇u + F(t, u)` there,
and suppose that `F(t, ·)` is Lipschitz on every bounded set, with a constant independent of `t`.
If `φ` is continuous on `[0, T]` and differentiable on `(0, T)` with `F(t, φ) ≤ φ'` there, and
`u ≤ φ(0)` at time `0`, then `u ≤ φ(t)` on all of `[0, T] × M`. -/
theorem le_of_deriv_le_laplaceBeltrami_add_mvfderiv_add_of_le_deriv (hn : 1 ≤ n) {φ : ℝ → ℝ}
    (hucont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hucd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ContMDiff I 𝓘(ℝ) 2 (u t))
    (hudiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hsub : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x,
      deriv (fun s ↦ u s x) t ≤
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
          letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
            IsContMDiffRiemannianBundle.of_le hn;
          laplaceBeltrami I (u t) x) + mvfderiv I (u t) x (b t x) + F t (u t x))
    (hφc : ContinuousOn φ (Icc 0 T)) (hφd : ∀ ⦃t⦄, t ∈ Ioo 0 T → DifferentiableAt ℝ φ t)
    (hφ : ∀ ⦃t⦄, t ∈ Ioo 0 T → F t (φ t) ≤ deriv φ t)
    (hF : ∀ R : ℝ≥0, ∃ K : ℝ≥0, ∀ ⦃t⦄, t ∈ Ioo 0 T →
      LipschitzOnWith K (F t) (Metric.closedBall 0 R))
    (hinit : ∀ x, u 0 x ≤ φ 0) :
    ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ x, u t x ≤ φ t :=
  le_of_deriv_sub_laplaceBeltrami_sub_mvfderiv_sub_le_of_lipschitzOnWith (v := fun s _ ↦ φ s) hn
    hucont (hφc.comp continuousOn_fst fun _ hp ↦ hp.1) hucd (fun _ _ ↦ contMDiff_const) hudiff
    (fun _ ht _ ↦ hφd ht)
    (fun t ht x ↦ by
      simp only [laplaceBeltrami_const, mvfderiv_const, zero_apply]
      linarith [hsub ht x, hφ ht])
    hF hinit

/-- **Comparison with an ODE subsolution.** Let `u` be continuous on `[0, T] × M`, `C²` in
space and differentiable in time on `(0, T) × M`, with `Δ_{g t} u + b·∇u + F(t, u) ≤ ∂ₜu` there,
and suppose that `F(t, ·)` is Lipschitz on every bounded set, with a constant independent of `t`.
If `φ` is continuous on `[0, T]` and differentiable on `(0, T)` with `φ' ≤ F(t, φ)` there, and
`φ(0) ≤ u` at time `0`, then `φ(t) ≤ u` on all of `[0, T] × M`. -/
theorem ge_of_laplaceBeltrami_add_mvfderiv_add_le_deriv_of_deriv_le (hn : 1 ≤ n) {φ : ℝ → ℝ}
    (hucont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hucd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ContMDiff I 𝓘(ℝ) 2 (u t))
    (hudiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hsuper : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x,
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
          letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
            IsContMDiffRiemannianBundle.of_le hn;
          laplaceBeltrami I (u t) x) + mvfderiv I (u t) x (b t x) + F t (u t x) ≤
        deriv (fun s ↦ u s x) t)
    (hφc : ContinuousOn φ (Icc 0 T)) (hφd : ∀ ⦃t⦄, t ∈ Ioo 0 T → DifferentiableAt ℝ φ t)
    (hφ : ∀ ⦃t⦄, t ∈ Ioo 0 T → deriv φ t ≤ F t (φ t))
    (hF : ∀ R : ℝ≥0, ∃ K : ℝ≥0, ∀ ⦃t⦄, t ∈ Ioo 0 T →
      LipschitzOnWith K (F t) (Metric.closedBall 0 R))
    (hinit : ∀ x, φ 0 ≤ u 0 x) :
    ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ x, φ t ≤ u t x :=
  le_of_deriv_sub_laplaceBeltrami_sub_mvfderiv_sub_le_of_lipschitzOnWith (u := fun s _ ↦ φ s) hn
    (hφc.comp continuousOn_fst fun _ hp ↦ hp.1) hucont (fun _ _ ↦ contMDiff_const) hucd
    (fun _ ht _ ↦ hφd ht) hudiff
    (fun t ht x ↦ by
      simp only [laplaceBeltrami_const, mvfderiv_const, zero_apply]
      linarith [hsuper ht x, hφ ht])
    hF hinit

/-- **Lower bound by the Riccati equation.** Let `u` be continuous on `[0, T] × M`, `C²` in space
and differentiable in time on `(0, T) × M`, with `Δ_{g t} u + b·∇u + c u² ≤ ∂ₜu` there. If
`s₀ ≤ u` at time `0` and `1 - c s₀ T > 0`, then `s₀ / (1 - c s₀ t) ≤ u` on all of `[0, T] × M`;
the left side is the solution of `φ' = c φ²` with `φ(0) = s₀`.

With `c = 2 / n` and `u` the scalar curvature along Ricci flow on an `n`-manifold, this is the
lower bound `Scal ≥ s₀ / (1 - 2 s₀ t / n)`.

For `c ≥ 0`, the abstract form of this bound on a compact space, stated through the growth of `u`
at its spatial minima, is `TauCeti.div_one_sub_mul_le_of_mul_sq_le_deriv_of_isLocalMin`; here
`c` may have either sign, and the hypothesis is the Laplace–Beltrami inequality with a drift. -/
theorem div_one_sub_mul_le_of_laplaceBeltrami_add_mvfderiv_add_mul_sq_le_deriv (hn : 1 ≤ n)
    {c s₀ : ℝ} (hucont : ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ univ))
    (hucd : ∀ ⦃t⦄, t ∈ Ioo 0 T → ContMDiff I 𝓘(ℝ) 2 (u t))
    (hudiff : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hsuper : ∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x,
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
          letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
            IsContMDiffRiemannianBundle.of_le hn;
          laplaceBeltrami I (u t) x) + mvfderiv I (u t) x (b t x) + c * u t x ^ 2 ≤
        deriv (fun s ↦ u s x) t)
    (hT : 0 < 1 - c * s₀ * T) (hinit : ∀ x, s₀ ≤ u 0 x) :
    ∀ ⦃t⦄, t ∈ Icc 0 T → ∀ x, s₀ / (1 - c * s₀ * t) ≤ u t x := by
  -- The denominator is affine in `t`, equal to `1` at `0` and positive at `T`.
  have hpos : ∀ ⦃t⦄, t ∈ Icc 0 T → 0 < 1 - c * s₀ * t := fun t ht ↦ by
    rcases le_total (c * s₀) 0 with h | h <;> nlinarith [ht.1, ht.2]
  have hφ : ∀ ⦃t⦄, t ∈ Icc 0 T →
      HasDerivAt (fun s ↦ s₀ / (1 - c * s₀ * s)) (c * (s₀ / (1 - c * s₀ * t)) ^ 2) t := by
    intro t ht
    have h := (hasDerivAt_const t s₀).fun_div
      (((hasDerivAt_id' t).const_mul (c * s₀)).const_sub 1) (hpos ht).ne'
    convert h using 1
    field_simp
    ring
  -- The reaction `y ↦ c y²` is Lipschitz with constant `2 |c| R` on the ball of radius `R`.
  have hlip (R : ℝ≥0) :
      LipschitzOnWith (‖c‖₊ * (2 * R)) (fun y : ℝ ↦ c * y ^ 2) (Metric.closedBall 0 R) := by
    refine LipschitzOnWith.of_dist_le_mul fun y hy z hz ↦ ?_
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs] at hy hz
    have hyz : |y + z| ≤ 2 * R := (abs_add_le y z).trans (by linarith)
    rw [Real.dist_eq, Real.dist_eq, show c * y ^ 2 - c * z ^ 2 = c * (y + z) * (y - z) by ring,
      abs_mul, abs_mul]
    push_cast
    rw [Real.norm_eq_abs]
    gcongr
  refine ge_of_laplaceBeltrami_add_mvfderiv_add_le_deriv_of_deriv_le (F := fun _ y ↦ c * y ^ 2) hn
    hucont hucd hudiff hsuper
    (fun t ht ↦ (hφ ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hφ (Ioo_subset_Icc_self ht)).differentiableAt)
    (fun t ht ↦ (hφ (Ioo_subset_Icc_self ht)).deriv.le)
    (fun R ↦ ⟨_, fun _ _ ↦ hlip R⟩) (fun x ↦ ?_)
  simpa using hinit x

end ClosedManifold

end TauCeti.Manifold
