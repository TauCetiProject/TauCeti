/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.MaximumPrinciple
public import TauCeti.Analysis.PDE.MaximumPrinciple.Parabolic.Basic
import Mathlib.Tactic

/-!
# Compact-domain heat comparison

On a boundaryless C² manifold, heat subsolutions lie below supersolutions on a compact spatial
domain when this holds initially and on its spatial boundary. The metric may vary arbitrarily
in time: only C¹ regularity of each spatial slice is required. The proof uses the native
Laplace–Beltrami sign at a spatial local maximum and the abstract weak parabolic principle.

## Main results

* `TauCeti.Manifold.compactDomain_heat_comparison`: compact-domain comparison for native metrics.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*, Corollary 4.14.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public noncomputable section
open Bundle CovariantDerivative Set Topology Filter
open scoped ContDiff Manifold

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

end TauCeti.Manifold
