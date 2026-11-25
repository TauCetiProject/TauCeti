/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen, The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MaximumPrinciple.Parabolic.Basic
public import TauCeti.Geometry.Manifold.Riemannian.MaximumPrinciple
import TauCeti.Analysis.PDE.MaximumPrinciple.Parabolic.QuadraticReaction
import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import Mathlib.Tactic

/-!
# Parabolic comparison principles on manifolds with evolving metrics

Let `g t` be a Riemannian metric on a boundaryless manifold `M` for each time `t`. This file
proves comparison principles for scalar parabolic operators built from the Laplace–Beltrami
operator `Δ_{g t} = div ∘ grad` of the metric at time `t`.

**Reaction–drift comparison on a compact cylinder.** We consider the operator

`∂ₜu - Δ_{g t} u - b·∇u - F(t, x, u)`,

where `b` is a time-dependent vector field and `F` is a reaction term. The drift term
`b·∇u = g(b, grad u)` is the differential `du(b)`, spelled `mvfderiv I (u t) x (b t x)`, so it does
not involve the metric. A function `u : ℝ → M → ℝ` (time first, so `u t` is the spatial slice at
time `t`) is a subsolution when the operator is nonpositive on `u`, and a supersolution when it is
nonnegative.

Let `C ⊆ M` be compact, let `u` be a subsolution and `v` a supersolution on
`(a, T) × interior C`, both continuous on `[a, T] × C`, `C²` in space and differentiable in time,
and let `F(t, x, ·)` be Lipschitz on bounded sets, uniformly in `(t, x)`. If `u ≤ v` on the
parabolic boundary, that is at time `a` and on `[a, T] × frontier C`, then `u ≤ v` on
`[a, T] × C`. At a spatial maximum of `u t - v t` the Laplacian of `u t - v t` is nonpositive and
its differential vanishes, so `∂ₜ(u - v) ≤ F(t, x, u) - F(t, x, v) ≤ L (u - v)` there, and the
Grönwall form of the perturbation argument,
`TauCeti.le_of_deriv_sub_deriv_le_mul_of_isLocalMax_le_parabolicBoundary`, applies. The
Lipschitz constant is taken on a ball containing the values of `u` and `v`, which are bounded by
compactness. The metrics enter only through the sign of their Laplacians at a maximum, so no
regularity of `g` in time is needed. On a closed manifold, take `C = univ`: its frontier is empty,
so only the initial comparison is needed. The heat comparison is the case `b = 0`, `F = 0`.

**ODE comparison on a closed manifold.** Let `M` be compact. A spatially constant function `φ(t)`
with `φ' ≥ F(t, φ)` is a supersolution, and one with `φ' ≤ F(t, φ)` is a subsolution. Hence a
subsolution starting below `φ(a)` stays below `φ(t)`, and a supersolution starting above `φ(a)`
stays above it: the extrema of the solution of the parabolic equation are controlled by the ODE
`φ' = F(t, φ)`. For instance, along Ricci flow the scalar curvature of an `n`-manifold satisfies
`∂ₜ Scal ≥ Δ Scal + (2/n) Scal²`, and comparison with the Riccati equation `φ' = (2/n) φ²` gives
`Scal ≥ s₀ / (1 - 2 s₀ t / n)` whenever `Scal ≥ s₀` at time `0`, as long as `1 - 2 s₀ t / n > 0`.

## Main results

* `TauCeti.Manifold.le_of_deriv_sub_laplaceBeltrami_sub_mvfderiv_sub_le_of_le_parabolicBoundary`:
  the comparison principle on a compact cylinder when `F(t, x, ·)` is Lipschitz from above
  between the two functions.
* `le_of_deriv_sub_laplaceBeltrami_sub_mvfderiv_sub_le_of_lipschitzOnWith_of_le_parabolicBoundary`:
  the comparison principle on a compact cylinder for a reaction which is Lipschitz on bounded
  sets, uniformly in time and space.
* `TauCeti.Manifold.compactDomain_heat_comparison`: compact-domain comparison for the heat
  operator of native metrics.
* `TauCeti.Manifold.le_of_deriv_le_laplaceBeltrami_add_mvfderiv_add_of_le_deriv`: on a closed
  manifold, a subsolution stays below a supersolution of the ODE `φ' = F(t, φ)`.
* `TauCeti.Manifold.ge_of_laplaceBeltrami_add_mvfderiv_add_le_deriv_of_deriv_le`: on a closed
  manifold, a supersolution stays above a subsolution of the ODE `φ' = F(t, φ)`.
* `TauCeti.Manifold.div_one_sub_mul_le_of_laplaceBeltrami_add_mvfderiv_add_mul_sq_le_deriv`: the
  Riccati lower bound `u ≥ s₀ / (1 - c s₀ (t - a))` for supersolutions of
  `∂ₜu = Δu + b·∇u + c u²` on a closed manifold, as long as `1 - c s₀ (t - a) > 0`.

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

section Cylinder

variable [I.Boundaryless]
  {n : ℕ∞ω} {g : ℝ → ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)}
  {a T : ℝ} {C : Set M} {u v : ℝ → M → ℝ} {b : (t : ℝ) → (x : M) → TangentSpace I x}
  {F : ℝ → M → ℝ → ℝ}

/-- **Comparison principle for `∂ₜ - Δ_{g t} - b·∇ - F` on a compact cylinder.**

Let `C` be compact, and let `u` and `v` be continuous on `[a, T] × C`, `C²` in space and
differentiable in time on `(a, T) × interior C`, with
`∂ₜu - Δ_{g t} u - b·∇u - F(t, x, u) ≤ ∂ₜv - Δ_{g t} v - b·∇v - F(t, x, v)` there. Suppose that
`F(t, x, u) - F(t, x, v) ≤ L (u - v)` wherever `u > v`. If `u ≤ v` at time `a` and on
`[a, T] × frontier C`, then `u ≤ v` on all of `[a, T] × C`. -/
theorem le_of_deriv_sub_laplaceBeltrami_sub_mvfderiv_sub_le_of_le_parabolicBoundary (hn : 1 ≤ n)
    {L : ℝ} (hC : IsCompact C)
    (hucont : ContinuousOn (Function.uncurry u) (Icc a T ×ˢ C))
    (hvcont : ContinuousOn (Function.uncurry v) (Icc a T ×ˢ C))
    (hucd : ∀ ⦃t⦄, t ∈ Ioo a T → ∀ ⦃x⦄, x ∈ interior C → ContMDiffAt I 𝓘(ℝ) 2 (u t) x)
    (hvcd : ∀ ⦃t⦄, t ∈ Ioo a T → ∀ ⦃x⦄, x ∈ interior C → ContMDiffAt I 𝓘(ℝ) 2 (v t) x)
    (hudiff : ∀ ⦃t⦄, t ∈ Ioo a T → ∀ ⦃x⦄, x ∈ interior C →
      DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hvdiff : ∀ ⦃t⦄, t ∈ Ioo a T → ∀ ⦃x⦄, x ∈ interior C →
      DifferentiableAt ℝ (fun s ↦ v s x) t)
    (hL : ∀ ⦃t⦄, t ∈ Ioo a T → ∀ ⦃x⦄, x ∈ interior C →
      deriv (fun s ↦ u s x) t -
          (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
            letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
              IsContMDiffRiemannianBundle.of_le hn;
            laplaceBeltrami I (u t) x) - mvfderiv I (u t) x (b t x) - F t x (u t x) ≤
        deriv (fun s ↦ v s x) t -
          (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
            letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
              IsContMDiffRiemannianBundle.of_le hn;
            laplaceBeltrami I (v t) x) - mvfderiv I (v t) x (b t x) - F t x (v t x))
    (hF : ∀ ⦃t⦄, t ∈ Ioo a T → ∀ ⦃x⦄, x ∈ interior C → v t x < u t x →
      F t x (u t x) - F t x (v t x) ≤ L * (u t x - v t x))
    (hinit : ∀ ⦃x⦄, x ∈ C → u a x ≤ v a x)
    (hlat : ∀ ⦃t⦄, t ∈ Icc a T → ∀ ⦃x⦄, x ∈ frontier C → u t x ≤ v t x) :
    ∀ ⦃t⦄, t ∈ Icc a T → ∀ ⦃x⦄, x ∈ C → u t x ≤ v t x := by
  intro t ht x hx
  refine sub_nonpos.mp <| le_of_deriv_sub_deriv_le_mul_of_isLocalMax_le_parabolicBoundary
    (u := fun s y ↦ u s y - v s y) (φ := 0) (L := L) hC (hucont.sub hvcont)
    continuousOn_const (fun s hs y hy ↦ (hudiff hs hy).fun_sub (hvdiff hs hy))
    (fun _ _ ↦ differentiableAt_const _) (fun s hs y hy hmax hpos ↦ ?_)
    (fun y hy ↦ sub_nonpos.mpr (hinit hy)) (fun s hs y hy ↦ sub_nonpos.mpr (hlat hs hy)) ht hx
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g s).toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le hn
  -- At a spatial maximum of `u s - v s` the Laplacian of `u s - v s` is nonpositive ...
  have hΔ := laplaceBeltrami_add_mul_nonpos_of_isLocalMax (k := -1) (hucd hs hy) (hvcd hs hy)
    BoundarylessManifold.isInteriorPoint (by simpa only [neg_one_mul, sub_eq_add_neg] using hmax)
  -- ... and its differential vanishes, so the drift terms agree.
  have hd : mvfderiv I (u s) y = mvfderiv I (v s) y := by
    have h :=
      mem_criticalPoints.mp (IsLocalMax.mem_criticalPoints (I := I) (f := u s - v s) hmax
        BoundarylessManifold.isInteriorPoint)
    rwa [mvfderiv_sub ((hucd hs hy).mdifferentiableAt (by norm_num))
      ((hvcd hs hy).mdifferentiableAt (by norm_num)), sub_eq_zero] at h
  simp only [Pi.zero_apply, sub_pos, sub_zero] at hpos ⊢
  rw [deriv_fun_sub (hudiff hs hy) (hvdiff hs hy), deriv_zero, Pi.zero_apply]
  have h1 := hL hs hy
  rw [hd] at h1
  linarith [hF hs hy hpos]

/-- **Comparison principle for `∂ₜ - Δ_{g t} - b·∇ - F` on a compact cylinder, with a reaction
that is Lipschitz on bounded sets.**

Let `C` be compact, and let `u` and `v` be continuous on `[a, T] × C`, `C²` in space and
differentiable in time on `(a, T) × interior C`, with
`∂ₜu - Δ_{g t} u - b·∇u - F(t, x, u) ≤ ∂ₜv - Δ_{g t} v - b·∇v - F(t, x, v)` there, and suppose
that `F(t, x, ·)` is Lipschitz on every bounded set, with a constant independent of `(t, x)`. If
`u ≤ v` at time `a` and on `[a, T] × frontier C`, then `u ≤ v` on all of `[a, T] × C`. -/
theorem
    le_of_deriv_sub_laplaceBeltrami_sub_mvfderiv_sub_le_of_lipschitzOnWith_of_le_parabolicBoundary
    (hn : 1 ≤ n) (hC : IsCompact C)
    (hucont : ContinuousOn (Function.uncurry u) (Icc a T ×ˢ C))
    (hvcont : ContinuousOn (Function.uncurry v) (Icc a T ×ˢ C))
    (hucd : ∀ ⦃t⦄, t ∈ Ioo a T → ∀ ⦃x⦄, x ∈ interior C → ContMDiffAt I 𝓘(ℝ) 2 (u t) x)
    (hvcd : ∀ ⦃t⦄, t ∈ Ioo a T → ∀ ⦃x⦄, x ∈ interior C → ContMDiffAt I 𝓘(ℝ) 2 (v t) x)
    (hudiff : ∀ ⦃t⦄, t ∈ Ioo a T → ∀ ⦃x⦄, x ∈ interior C →
      DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hvdiff : ∀ ⦃t⦄, t ∈ Ioo a T → ∀ ⦃x⦄, x ∈ interior C →
      DifferentiableAt ℝ (fun s ↦ v s x) t)
    (hL : ∀ ⦃t⦄, t ∈ Ioo a T → ∀ ⦃x⦄, x ∈ interior C →
      deriv (fun s ↦ u s x) t -
          (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
            letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
              IsContMDiffRiemannianBundle.of_le hn;
            laplaceBeltrami I (u t) x) - mvfderiv I (u t) x (b t x) - F t x (u t x) ≤
        deriv (fun s ↦ v s x) t -
          (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
            letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
              IsContMDiffRiemannianBundle.of_le hn;
            laplaceBeltrami I (v t) x) - mvfderiv I (v t) x (b t x) - F t x (v t x))
    (hF : ∀ R : ℝ≥0, ∃ K : ℝ≥0, ∀ ⦃t⦄, t ∈ Ioo a T → ∀ ⦃x⦄, x ∈ interior C →
      LipschitzOnWith K (F t x) (Metric.closedBall 0 R))
    (hinit : ∀ ⦃x⦄, x ∈ C → u a x ≤ v a x)
    (hlat : ∀ ⦃t⦄, t ∈ Icc a T → ∀ ⦃x⦄, x ∈ frontier C → u t x ≤ v t x) :
    ∀ ⦃t⦄, t ∈ Icc a T → ∀ ⦃x⦄, x ∈ C → u t x ≤ v t x := by
  -- The values of `u` and `v` on the compact cylinder lie in a common ball.
  have hcpt : IsCompact (Icc a T ×ˢ C) := isCompact_Icc.prod hC
  obtain ⟨R, hR0, hR⟩ := ((hcpt.image_of_continuousOn hucont).union
    (hcpt.image_of_continuousOn hvcont)).isBounded.subset_closedBall_lt 0 (0 : ℝ)
  obtain ⟨K, hK⟩ := hF ⟨R, hR0.le⟩
  refine le_of_deriv_sub_laplaceBeltrami_sub_mvfderiv_sub_le_of_le_parabolicBoundary hn (L := K)
    hC hucont hvcont hucd hvcd hudiff hvdiff hL (fun t ht x hx hlt ↦ ?_) hinit hlat
  have hmem : (t, x) ∈ Icc a T ×ˢ C := ⟨Ioo_subset_Icc_self ht, interior_subset hx⟩
  have h := (hK ht hx).dist_le_mul _ (hR (Or.inl (mem_image_of_mem _ hmem))) _
    (hR (Or.inr (mem_image_of_mem _ hmem)))
  rw [Real.dist_eq, Real.dist_eq, Function.uncurry_apply_pair, Function.uncurry_apply_pair,
    abs_of_pos (sub_pos.mpr hlt)] at h
  exact (le_abs_self _).trans h

end Cylinder

/-- Heat subsolutions lie below supersolutions on a compact spatial domain. -/
theorem compactDomain_heat_comparison [I.Boundaryless] [T2Space M] {n : ℕ∞ω}
    (g : ℝ → ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hn : 1 ≤ n)
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
      let : IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _) :=
        IsContMDiffRiemannianBundle.of_le hn
      v t x - laplaceBeltrami I (u t) x ≤ w t x - laplaceBeltrami I (f t) x) :
    ∀ t ∈ Icc a b, ∀ x ∈ C, u t x ≤ f t x := fun t ht x hx ↦
  le_of_deriv_sub_laplaceBeltrami_sub_mvfderiv_sub_le_of_le_parabolicBoundary (g := g) hn
    (b := fun _ _ ↦ 0) (F := fun _ _ _ ↦ 0) (L := 0) hC hu hf
    (fun t ht x hx ↦ (hus t ht).contMDiffAt (hU.mem_nhds (hCU (interior_subset hx))))
    (fun t ht x hx ↦ (hfs t ht).contMDiffAt (hU.mem_nhds (hCU (interior_subset hx))))
    (fun t ht x hx ↦ (hud t ht x hx).differentiableAt)
    (fun t ht x hx ↦ (hfd t ht x hx).differentiableAt)
    (fun t ht x hx ↦ by
      rw [(hud t ht x hx).deriv, (hfd t ht x hx).deriv]
      simpa only [map_zero, sub_zero] using hevol t ht x hx)
    (fun _ _ _ _ _ ↦ by simp) (fun x hx ↦ hinit x hx)
    (fun t ht x hx ↦ hboundary t ht x ⟨hC.isClosed.closure_eq ▸ hx.1, hx.2⟩) ht hx

section ClosedManifold

variable [I.Boundaryless] [CompactSpace M]
  {n : ℕ∞ω} {g : ℝ → ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)}
  {a T : ℝ} {u : ℝ → M → ℝ} {b : (t : ℝ) → (x : M) → TangentSpace I x} {F : ℝ → ℝ → ℝ}

/-- **Comparison with an ODE supersolution on a closed manifold.** Let `u` be continuous on
`[a, T] × M`, `C²` in space and differentiable in time on `(a, T) × M`, with
`∂ₜu ≤ Δ_{g t} u + b·∇u + F(t, u)` there. Let `φ` be continuous on `[a, T]` and differentiable on
`(a, T)` with `F(t, φ) ≤ φ'` there, and suppose that `F(t, u) - F(t, φ) ≤ L (u - φ)` wherever
`u > φ`; this holds, by compactness, when `F(t, ·)` is Lipschitz on bounded sets uniformly in `t`.
If `u ≤ φ(a)` at time `a`, then `u ≤ φ(t)` on all of `[a, T] × M`. -/
theorem le_of_deriv_le_laplaceBeltrami_add_mvfderiv_add_of_le_deriv (hn : 1 ≤ n) {φ : ℝ → ℝ}
    {L : ℝ} (hucont : ContinuousOn (Function.uncurry u) (Icc a T ×ˢ univ))
    (hucd : ∀ ⦃t⦄, t ∈ Ioo a T → ContMDiff I 𝓘(ℝ) 2 (u t))
    (hudiff : ∀ ⦃t⦄, t ∈ Ioo a T → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hsub : ∀ ⦃t⦄, t ∈ Ioo a T → ∀ x,
      deriv (fun s ↦ u s x) t ≤
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
          letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
            IsContMDiffRiemannianBundle.of_le hn;
          laplaceBeltrami I (u t) x) + mvfderiv I (u t) x (b t x) + F t (u t x))
    (hφc : ContinuousOn φ (Icc a T)) (hφd : ∀ ⦃t⦄, t ∈ Ioo a T → DifferentiableAt ℝ φ t)
    (hφ : ∀ ⦃t⦄, t ∈ Ioo a T → F t (φ t) ≤ deriv φ t)
    (hF : ∀ ⦃t⦄, t ∈ Ioo a T → ∀ x, φ t < u t x →
      F t (u t x) - F t (φ t) ≤ L * (u t x - φ t))
    (hinit : ∀ x, u a x ≤ φ a) :
    ∀ ⦃t⦄, t ∈ Icc a T → ∀ x, u t x ≤ φ t := fun t ht x ↦
  le_of_deriv_sub_laplaceBeltrami_sub_mvfderiv_sub_le_of_le_parabolicBoundary
    (v := fun s _ ↦ φ s) (F := fun s _ ↦ F s) hn isCompact_univ hucont
    (hφc.comp continuousOn_fst fun _ hp ↦ hp.1) (fun _ hs _ _ ↦ (hucd hs).contMDiffAt)
    (fun _ _ _ _ ↦ contMDiffAt_const) (fun _ hs y _ ↦ hudiff hs y) (fun _ hs _ _ ↦ hφd hs)
    (fun s hs y _ ↦ by
      simp only [laplaceBeltrami_const, mvfderiv_const, zero_apply]
      linarith [hsub hs y, hφ hs])
    (fun _ hs y _ ↦ hF hs y) (fun y _ ↦ hinit y) (fun _ _ _ hy ↦ by simp at hy) ht (mem_univ x)

/-- **Comparison with an ODE subsolution on a closed manifold.** Let `u` be continuous on
`[a, T] × M`, `C²` in space and differentiable in time on `(a, T) × M`, with
`Δ_{g t} u + b·∇u + F(t, u) ≤ ∂ₜu` there. Let `φ` be continuous on `[a, T]` and differentiable on
`(a, T)` with `φ' ≤ F(t, φ)` there, and suppose that `F(t, φ) - F(t, u) ≤ L (φ - u)` wherever
`u < φ`; this holds, by compactness, when `F(t, ·)` is Lipschitz on bounded sets uniformly in `t`.
If `φ(a) ≤ u` at time `a`, then `φ(t) ≤ u` on all of `[a, T] × M`. -/
theorem ge_of_laplaceBeltrami_add_mvfderiv_add_le_deriv_of_deriv_le (hn : 1 ≤ n) {φ : ℝ → ℝ}
    {L : ℝ} (hucont : ContinuousOn (Function.uncurry u) (Icc a T ×ˢ univ))
    (hucd : ∀ ⦃t⦄, t ∈ Ioo a T → ContMDiff I 𝓘(ℝ) 2 (u t))
    (hudiff : ∀ ⦃t⦄, t ∈ Ioo a T → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hsuper : ∀ ⦃t⦄, t ∈ Ioo a T → ∀ x,
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
          letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
            IsContMDiffRiemannianBundle.of_le hn;
          laplaceBeltrami I (u t) x) + mvfderiv I (u t) x (b t x) + F t (u t x) ≤
        deriv (fun s ↦ u s x) t)
    (hφc : ContinuousOn φ (Icc a T)) (hφd : ∀ ⦃t⦄, t ∈ Ioo a T → DifferentiableAt ℝ φ t)
    (hφ : ∀ ⦃t⦄, t ∈ Ioo a T → deriv φ t ≤ F t (φ t))
    (hF : ∀ ⦃t⦄, t ∈ Ioo a T → ∀ x, u t x < φ t →
      F t (φ t) - F t (u t x) ≤ L * (φ t - u t x))
    (hinit : ∀ x, φ a ≤ u a x) :
    ∀ ⦃t⦄, t ∈ Icc a T → ∀ x, φ t ≤ u t x := fun t ht x ↦
  le_of_deriv_sub_laplaceBeltrami_sub_mvfderiv_sub_le_of_le_parabolicBoundary
    (u := fun s _ ↦ φ s) (F := fun s _ ↦ F s) hn isCompact_univ
    (hφc.comp continuousOn_fst fun _ hp ↦ hp.1) hucont (fun _ _ _ _ ↦ contMDiffAt_const)
    (fun _ hs _ _ ↦ (hucd hs).contMDiffAt) (fun _ hs _ _ ↦ hφd hs) (fun _ hs y _ ↦ hudiff hs y)
    (fun s hs y _ ↦ by
      simp only [laplaceBeltrami_const, mvfderiv_const, zero_apply]
      linarith [hsuper hs y, hφ hs])
    (fun _ hs y _ ↦ hF hs y) (fun y _ ↦ hinit y) (fun _ _ _ hy ↦ by simp at hy) ht (mem_univ x)

/-- **Lower bound by the Riccati equation on a closed manifold.** Let `u` be continuous on
`[a, T] × M`, `C²` in space and differentiable in time on `(a, T) × M`, with
`Δ_{g t} u + b·∇u + c u² ≤ ∂ₜu` there. If `s₀ ≤ u` at time `a` and `1 - c s₀ (T - a) > 0`, then
`s₀ / (1 - c s₀ (t - a)) ≤ u` on all of `[a, T] × M`; the left side is the solution of
`φ' = c φ²` with `φ(a) = s₀`. The constant `c` may have either sign.

With `c = 2 / n` and `u` the scalar curvature along Ricci flow on an `n`-manifold, this is the
lower bound `Scal ≥ s₀ / (1 - 2 s₀ t / n)`. At a spatial minimum the Laplacian is nonnegative and
the drift vanishes, so this is the abstract bound
`TauCeti.div_one_sub_mul_le_of_mul_sq_le_deriv_of_isLocalMin`. -/
theorem div_one_sub_mul_le_of_laplaceBeltrami_add_mvfderiv_add_mul_sq_le_deriv (hn : 1 ≤ n)
    {c s₀ : ℝ} (hucont : ContinuousOn (Function.uncurry u) (Icc a T ×ˢ univ))
    (hucd : ∀ ⦃t⦄, t ∈ Ioo a T → ContMDiff I 𝓘(ℝ) 2 (u t))
    (hudiff : ∀ ⦃t⦄, t ∈ Ioo a T → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t)
    (hsuper : ∀ ⦃t⦄, t ∈ Ioo a T → ∀ x,
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩;
          letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
            IsContMDiffRiemannianBundle.of_le hn;
          laplaceBeltrami I (u t) x) + mvfderiv I (u t) x (b t x) + c * u t x ^ 2 ≤
        deriv (fun s ↦ u s x) t)
    (hT : 0 < 1 - c * s₀ * (T - a)) (hinit : ∀ x, s₀ ≤ u a x) :
    ∀ ⦃t⦄, t ∈ Icc a T → ∀ x, s₀ / (1 - c * s₀ * (t - a)) ≤ u t x :=
  div_one_sub_mul_le_of_mul_sq_le_deriv_of_isLocalMin hT hucont hudiff
    (fun t ht x hmin _ ↦ by
      let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(g t).toRiemannianMetric⟩
      let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn
      -- At a spatial minimum the Laplacian is nonnegative and the differential vanishes.
      have hΔ := laplaceBeltrami_nonneg_of_isLocalMin (hucd ht).contMDiffAt
        BoundarylessManifold.isInteriorPoint hmin
      have hd : mvfderiv I (u t) x = 0 :=
        mem_criticalPoints.mp
          (hmin.mem_criticalPoints (I := I) BoundarylessManifold.isInteriorPoint)
      have h := hsuper ht x
      rw [hd, zero_apply] at h
      linarith)
    hinit

end ClosedManifold

end TauCeti.Manifold
