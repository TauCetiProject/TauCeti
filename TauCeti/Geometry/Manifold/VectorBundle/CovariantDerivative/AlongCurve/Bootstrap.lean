/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Regularity

/-!
# Recovering regularity from a tangent-bundle covariant derivative

If a tangent-bundle section along a curve and its covariant derivative are both `C^n`,
with `n ≥ 1`,
the section is `C^(n + 1)`, provided the connection is `C^n` and the base curve is `C^(n + 1)`.
This is the converse regularity estimate to differentiation losing one derivative.
It allows bootstrapping differential equations for sections without extending them to
ambient vector fields or choosing a parallel frame. Derivatives remain within the
parameter set, including at closed interval endpoints.

In a fixed trivialization, solve `DV = v' + Γ(v, γ')` for `v'` and apply the usual
criterion for continuous differentiability in terms of the derivative.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Chapter 4.
-/

public section

open Bundle Filter Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace CovariantDerivative

open TauCeti.Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {n : ℕ} [IsManifold I (n + 1 : ℕ) M]
  [ContMDiffVectorBundle (n + 1 : ℕ) E (TangentSpace I : M → Type _) I]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]

/-- For a tangent-bundle connection that is `C^n` on the trivialization at each point
of a `C^(n + 1)` curve in the parameter set, a section along the curve of class `C^n`,
with `n ≥ 1`, whose covariant derivative is `C^n` is of class `C^(n + 1)`.
The statement holds within any parameter set with unique derivatives. -/
theorem contMDiffOn_succ_of_alongCurveWithin
    (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
    (γ : 𝕜 → M) (V : ∀ t, TangentSpace I (γ t)) {s : Set 𝕜}
    (hn : 1 ≤ n)
    (hcov : ∀ t ∈ s, ContMDiffCovariantDerivativeOn E n cov.toFun
      (trivializationAt E (TangentSpace I) (γ t)).baseSet)
    (hs : UniqueDiffOn 𝕜 s)
    (hγ : ContMDiffOn 𝓘(𝕜, 𝕜) I (n + 1 : ℕ) γ s)
    (hV : ContMDiffOn 𝓘(𝕜, 𝕜) I.tangent n
      (fun r ↦ TotalSpace.mk' E (γ r) (V r)) s)
    (hDV : ContMDiffOn 𝓘(𝕜, 𝕜) I.tangent n
      (fun r ↦ TotalSpace.mk' E (γ r) (alongCurveWithin cov γ V s r)) s) :
    ContMDiffOn 𝓘(𝕜, 𝕜) I.tangent (n + 1 : ℕ)
      (fun r ↦ TotalSpace.mk' E (γ r) (V r)) s := by
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    ContMDiffVectorBundle.of_le (n := (n + 1 : ℕ)) (by exact_mod_cast Nat.le_succ n)
  let : ContMDiffVectorBundle ((n : ℕ∞ω) + 1) E (TangentSpace I : M → Type _) I := by
    simpa using (inferInstance : ContMDiffVectorBundle (n + 1 : ℕ) E (TangentSpace I) I)
  let : IsManifold I ((n : ℕ∞ω) + 1) M := by
    simpa using (inferInstance : IsManifold I (n + 1 : ℕ) M)
  have hn' : n ≠ 0 := by omega
  have hn0 : (n : ℕ∞ω) ≠ 0 := by exact_mod_cast hn'
  intro t ht
  let e := trivializationAt E (TangentSpace I) (γ t)
  let Γ := christoffelMap (Module.finBasis 𝕜 E)
    (cov.isCovariantDerivativeOn (s := e.baseSet))
  let v := sectionCoord (F := E) γ V (γ t)
  let d := sectionCoord (F := E) γ (alongCurveWithin cov γ V s) (γ t)
  let u := extChartAt I (γ t) ∘ γ
  have hx : γ t ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt _ _ _
  have hγn : ContMDiffWithinAt 𝓘(𝕜, 𝕜) I n γ s t :=
    (hγ t ht).of_le (by exact_mod_cast Nat.le_succ n)
  have hv : ContDiffWithinAt 𝕜 n v s t :=
    (contDiffWithinAt_sectionCoord_iff γ V hγn hx).2 (hV t ht)
  have hd : ContDiffWithinAt 𝕜 n d s t :=
    (contDiffWithinAt_sectionCoord_iff γ _ hγn hx).2 (hDV t ht)
  have hu : ContDiffWithinAt 𝕜 (n + 1 : ℕ) u s t :=
    ((contMDiffAt_extChartAt' (by
      simpa only [e, TangentBundle.trivializationAt_baseSet] using hx)).comp_contMDiffWithinAt
        t (hγ t ht)).contDiffWithinAt
  let := hcov t ht
  have hΓ : ContMDiffAt I 𝓘(𝕜, E →L[𝕜] E →L[𝕜] E) n Γ (γ t) :=
    (contMDiffOn_christoffelMap (Module.finBasis 𝕜 E)
      (cov.isCovariantDerivativeOn (s := e.baseSet))).contMDiffAt (e.open_baseSet.mem_nhds hx)
  -- Solving the fixed-chart connection formula gives a C^n candidate for v'.
  have hderiv : ContDiffWithinAt 𝕜 n
      (fun r ↦ d r - Γ (γ r) (v r) (derivWithin u s r)) s t :=
    hd.sub (((hΓ.comp_contMDiffWithinAt t hγn).contDiffWithinAt.clm_apply hv).clm_apply
      (hu.derivWithin hs (by simp) ht))
  apply (contDiffWithinAt_sectionCoord_iff γ V (hγ t ht) hx).1
  rw [Nat.cast_add, Nat.cast_one, contDiffWithinAt_succ_iff_hasFDerivWithinAt' (by simp)]
  have hbase : ∀ᶠ r in 𝓝[s] t, γ r ∈ e.baseSet :=
    (hγ t ht).continuousWithinAt.preimage_mem_nhdsWithin (e.open_baseSet.mem_nhds hx)
  have hdeq := eventuallyEq_sectionCoord_alongCurveWithin cov γ V hs ht hx
    ((hV t ht).of_le (by exact_mod_cast hn))
  refine ⟨{r | r ∈ s ∧ γ r ∈ e.baseSet ∧
    d r = alongCurveInChartWithin cov γ V s (γ t) r}, ?_, ?_, by simp, fun r ↦
    ContinuousLinearMap.toSpanSingleton 𝕜 (d r - Γ (γ r) (v r) (derivWithin u s r)), ?_, ?_⟩
  · rw [insert_eq_of_mem ht]
    exact inter_mem self_mem_nhdsWithin (inter_mem hbase hdeq)
  · exact fun r hr ↦ subset_insert t s hr.1
  · intro r hr
    -- Chart independence identifies that candidate with the actual within derivative.
    have hVr : DifferentiableWithinAt 𝕜 v s r := differentiableWithinAt_sectionCoord γ V
      ((hV r hr.1).mdifferentiableWithinAt hn0) hr.2.1
    have heq : d r = derivWithin v s r + Γ (γ r) (v r) (derivWithin u s r) :=
      hr.2.2.trans (alongCurveInChartWithin_apply cov γ V s (γ t) r)
    simpa only [heq, add_sub_cancel_right] using hVr.hasDerivWithinAt.hasFDerivWithinAt
  · exact ContinuousLinearMap.toSpanSingletonCLE.contDiff.comp_contDiffWithinAt hderiv

end CovariantDerivative
