/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Regularity
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import TauCeti.Analysis.Calculus.ContDiff.ClosedInterval

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
criterion for continuous differentiability in terms of the derivative. We also record
subset restriction of `alongCurveWithin` for `C¹` sections and `C¹` gluing across an interior point
of a closed real interval when the two one-sided covariant derivatives agree.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Chapter 4.
-/

public section

open Bundle Filter Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace CovariantDerivative

open TauCeti.Manifold

section Bootstrap

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {n : ℕ} [IsManifold I (n + 1 : ℕ) M]
  [ContMDiffVectorBundle (n + 1 : ℕ) E (TangentSpace I : M → Type _) I]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]

/-- **The connection candidate for the derivative.** At a point `t` of the parameter set, solving
the fixed-chart connection formula `DV = v' + Γ(v, γ')` for `v'` gives a `C^n` function of the
parameter: the coordinates of `DV`, minus the Christoffel term of the coordinates of `V` and
`γ'`. -/
private theorem contDiffWithinAt_alongCurveWithin_sub_christoffel
    (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
    (γ : 𝕜 → M) (V : ∀ t, TangentSpace I (γ t)) {s : Set 𝕜}
    (hcov : ∀ t ∈ s, ContMDiffCovariantDerivativeOn E n cov.toFun
      (trivializationAt E (TangentSpace I) (γ t)).baseSet)
    (hs : UniqueDiffOn 𝕜 s)
    (hγ : ContMDiffOn 𝓘(𝕜, 𝕜) I (n + 1 : ℕ) γ s)
    (hV : ContMDiffOn 𝓘(𝕜, 𝕜) I.tangent n
      (fun r ↦ TotalSpace.mk' E (γ r) (V r)) s)
    (hDV : ContMDiffOn 𝓘(𝕜, 𝕜) I.tangent n
      (fun r ↦ TotalSpace.mk' E (γ r) (alongCurveWithin cov γ V s r)) s)
    {t : 𝕜} (ht : t ∈ s) :
    ContDiffWithinAt 𝕜 n
      (fun r ↦ sectionCoord (F := E) γ (alongCurveWithin cov γ V s) (γ t) r
        - christoffelMap (Module.finBasis 𝕜 E)
          (cov.isCovariantDerivativeOn
            (s := (trivializationAt E (TangentSpace I) (γ t)).baseSet)) (γ r)
          (sectionCoord (F := E) γ V (γ t) r)
          (derivWithin (extChartAt I (γ t) ∘ γ) s r)) s t := by
  let : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    ContMDiffVectorBundle.of_le (n := (n + 1 : ℕ)) (by exact_mod_cast Nat.le_succ n)
  let : ContMDiffVectorBundle ((n : ℕ∞ω) + 1) E (TangentSpace I : M → Type _) I := by
    simpa using (inferInstance : ContMDiffVectorBundle (n + 1 : ℕ) E (TangentSpace I) I)
  let : IsManifold I ((n : ℕ∞ω) + 1) M := by
    simpa using (inferInstance : IsManifold I (n + 1 : ℕ) M)
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
  exact hd.sub (((hΓ.comp_contMDiffWithinAt t hγn).contDiffWithinAt.clm_apply hv).clm_apply
      (hu.derivWithin hs (by simp) ht))

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
  -- Solving the fixed-chart connection formula gives a C^n candidate for v'.
  have hderiv : ContDiffWithinAt 𝕜 n
      (fun r ↦ d r - Γ (γ r) (v r) (derivWithin u s r)) s t :=
    contDiffWithinAt_alongCurveWithin_sub_christoffel cov γ V hcov hs hγ hV hDV ht
  apply (contDiffWithinAt_sectionCoord_iff γ V (hγ t ht) hx).1
  rw [Nat.cast_add, Nat.cast_one, contDiffWithinAt_succ_iff_hasFDerivWithinAt' (by simp)]
  have hbase : ∀ᶠ r in 𝓝[s] t, γ r ∈ e.baseSet :=
    (hγ t ht).continuousWithinAt.preimage_mem_nhdsWithin (e.open_baseSet.mem_nhds hx)
  have hdeq := eventuallyEq_sectionCoord_alongCurveWithin cov γ V hx
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

end Bootstrap

/-- Restricting `alongCurveWithin` from `u` to a subset `s ⊆ u` at a point of unique
differentiability for a `C¹` tangent-bundle section along `γ`. -/
theorem alongCurveWithin_subset_of_contMDiffOn_one
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
    (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
    {γ : 𝕜 → M} {W : ∀ t, TangentSpace I (γ t)} {s u : Set 𝕜} {r : 𝕜}
    (hsub : s ⊆ u) (hs : UniqueDiffWithinAt 𝕜 s r)
    (hW : ContMDiffOn 𝓘(𝕜, 𝕜) I.tangent 1 (fun t ↦ TotalSpace.mk' E (γ t) (W t)) u)
    (hr : r ∈ s) :
    alongCurveWithin cov γ W s r = alongCurveWithin cov γ W u r := by
  let _ : IsManifold I (1 + 1) M := ‹IsManifold I 2 M›
  let _ : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  have hγr : ContMDiffWithinAt 𝓘(𝕜, 𝕜) I 1 γ u r :=
    (Bundle.contMDiff_proj (TangentSpace I)).contMDiffAt.comp_contMDiffWithinAt r (hW r (hsub hr))
  exact alongCurveWithin_subset cov γ W hsub hs
    (differentiableWithinAt_sectionCoord γ W ((hW r (hsub hr)).mdifferentiableWithinAt one_ne_zero)
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ r)))
    (by
      simpa [writtenInExtChartAt] using
        (hγr.mdifferentiableWithinAt one_ne_zero).differentiableWithinAt_writtenInExtChartAt)

section ClosedInterval

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]

/-- Matching one-sided covariant derivatives at `c ∈ (a, b)` imply matching one-sided derivatives
of `sectionCoord` at `c`. -/
private lemma derivWithin_sectionCoord_eq_of_alongCurveWithin_eq
    (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
    {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (hD : alongCurveWithin cov γ V (Icc a c) c = alongCurveWithin cov γ V (Icc c b) c) :
    derivWithin (sectionCoord (F := E) γ V (γ c)) (Icc a c) c =
      derivWithin (sectionCoord (F := E) γ V (γ c)) (Icc c b) c := by
  have hc : c ∈ Icc a b := ⟨hac.le, hcb.le⟩
  have hu_diff : DifferentiableWithinAt ℝ (extChartAt I (γ c) ∘ γ) (Icc a b) c := by
    simpa [writtenInExtChartAt] using
      ((hγ c hc).mdifferentiableWithinAt one_ne_zero).differentiableWithinAt_writtenInExtChartAt
  have hu₁ := (hu_diff.hasDerivWithinAt.mono (Icc_subset_Icc_right hcb.le)).derivWithin
    (uniqueDiffOn_Icc hac c ⟨hac.le, le_rfl⟩)
  have hu₂ := (hu_diff.hasDerivWithinAt.mono (Icc_subset_Icc_left hac.le)).derivWithin
    (uniqueDiffOn_Icc hcb c ⟨le_rfl, hcb.le⟩)
  have hCLM := congrArg ((trivializationAt E (TangentSpace I) (γ c)).continuousLinearMapAt ℝ
    (γ c)) hD
  rw [continuousLinearMapAt_alongCurveWithin cov rfl V,
    continuousLinearMapAt_alongCurveWithin cov rfl V, hu₁, hu₂] at hCLM
  exact add_right_cancel hCLM

/-- `C¹` smoothness within `[a, b]` at an interior parameter `c` where two `C¹` tangent-bundle
lifts have matching one-sided covariant derivatives. -/
private theorem contMDiffWithinAt_one_union_Icc_at_corner
    (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
    {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (hV₁ : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (Icc a c))
    (hV₂ : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (Icc c b))
    (hD : alongCurveWithin cov γ V (Icc a c) c = alongCurveWithin cov γ V (Icc c b) c) :
    ContMDiffWithinAt 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (Icc a b) c := by
  let _ : IsManifold I (1 + 1) M := ‹IsManifold I 2 M›
  let _ : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  let e := trivializationAt E (TangentSpace I) (γ c)
  let v := sectionCoord (F := E) γ V (γ c)
  have hc : c ∈ Icc a b := ⟨hac.le, hcb.le⟩
  have hx : γ c ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ c)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1
    ((hγ c hc).continuousWithinAt.preimage_mem_nhdsWithin (e.open_baseSet.mem_nhds hx))
  let δ := min ε (min (c - a) (b - c)) / 2
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hp_ge : a ≤ c - δ := by
    dsimp only [δ]; linarith [min_le_right ε (min (c - a) (b - c)), min_le_left (c - a) (b - c)]
  have hq_le : c + δ ≤ b := by
    dsimp only [δ]; linarith [min_le_right ε (min (c - a) (b - c)), min_le_right (c - a) (b - c)]
  have hbase : ∀ r ∈ Icc (c - δ) (c + δ), γ r ∈ e.baseSet := fun r hr ↦ by
    have hδ_le : δ ≤ ε / 2 := by dsimp only [δ]; linarith [min_le_left ε (min (c - a) (b - c))]
    refine hball ⟨Metric.mem_ball.2 ?_, hp_ge.trans hr.1, hr.2.trans hq_le⟩
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hv₁ : ContDiffOn ℝ 1 v (Icc (c - δ) c) := fun r hr ↦
    (contDiffWithinAt_sectionCoord_iff γ V ((hγ.mono (Icc_subset_Icc hp_ge hcb.le)) r hr)
      (hbase r ⟨hr.1, by linarith [hr.2]⟩)).2 (hV₁.mono (Icc_subset_Icc hp_ge le_rfl) r hr)
  have hv₂ : ContDiffOn ℝ 1 v (Icc c (c + δ)) := fun r hr ↦
    (contDiffWithinAt_sectionCoord_iff γ V ((hγ.mono (Icc_subset_Icc hac.le hq_le)) r hr)
      (hbase r ⟨by linarith [hr.1], hr.2⟩)).2 (hV₂.mono (Icc_subset_Icc le_rfl hq_le) r hr)
  have hdv₁ : derivWithin v (Icc (c - δ) c) c = derivWithin v (Icc a c) c :=
    (((contDiffWithinAt_sectionCoord_iff γ V (hγ.mono (Icc_subset_Icc_right hcb.le) c
        ⟨hac.le, le_rfl⟩) hx).2 (hV₁ c ⟨hac.le, le_rfl⟩)).differentiableWithinAt one_ne_zero
      |>.hasDerivWithinAt.mono (Icc_subset_Icc_left hp_ge)).derivWithin
      (uniqueDiffOn_Icc (by linarith) c ⟨by linarith, le_rfl⟩)
  have hdv₂ : derivWithin v (Icc c (c + δ)) c = derivWithin v (Icc c b) c :=
    (((contDiffWithinAt_sectionCoord_iff γ V (hγ.mono (Icc_subset_Icc_left hac.le) c
        ⟨le_rfl, hcb.le⟩) hx).2 (hV₂ c ⟨le_rfl, hcb.le⟩)).differentiableWithinAt one_ne_zero
      |>.hasDerivWithinAt.mono (Icc_subset_Icc_right hq_le)).derivWithin
      (uniqueDiffOn_Icc (by linarith) c ⟨le_rfl, by linarith⟩)
  have hv_union := hv₁.union_Icc_of_derivWithin_eq hv₂
    (hdv₁.trans ((derivWithin_sectionCoord_eq_of_alongCurveWithin_eq cov hac hcb hγ hD).trans
      hdv₂.symm))
  refine (contDiffWithinAt_sectionCoord_iff γ V (hγ c hc) hx).1
    ((hv_union c ⟨by linarith, by linarith⟩).mono_of_mem_nhdsWithin ?_)
  exact mem_nhdsWithin.2 ⟨Ioo (c - δ) (c + δ), isOpen_Ioo, ⟨by linarith, by linarith⟩,
    fun r hr ↦ Ioo_subset_Icc_self hr.1⟩

/-- If `V` has `C¹` tangent-bundle lifts along a `C¹` curve `γ` on `[a, c]` and `[c, b]` with
matching one-sided covariant derivatives at `c`, then `V` has a `C¹` tangent-bundle lift on
`[a, b]`. When `c ≤ a` or `b ≤ c`, one piece already covers `[a, b]`. -/
theorem contMDiffOn_one_union_Icc_of_alongCurveWithin_eq
    (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
    {γ : ℝ → M} {V : ∀ t, TangentSpace I (γ t)} {a c b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (hV₁ : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (Icc a c))
    (hV₂ : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (Icc c b))
    (hD : alongCurveWithin cov γ V (Icc a c) c = alongCurveWithin cov γ V (Icc c b) c) :
    ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1 (fun r ↦ TotalSpace.mk' E (γ r) (V r)) (Icc a b) := by
  rcases le_or_gt c a with hca | hac
  · exact hV₂.mono (Icc_subset_Icc hca le_rfl)
  rcases le_or_gt b c with hbc | hcb
  · exact hV₁.mono (Icc_subset_Icc le_rfl hbc)
  intro t ht
  rcases lt_trichotomy t c with htc | rfl | hct
  · exact (hV₁ t ⟨ht.1, htc.le⟩).mono_of_mem_nhdsWithin
      (mem_nhdsWithin.2 ⟨Iio c, isOpen_Iio, htc, fun r hr ↦ ⟨hr.2.1, hr.1.le⟩⟩)
  · exact contMDiffWithinAt_one_union_Icc_at_corner cov hac hcb hγ hV₁ hV₂ hD
  · exact (hV₂ t ⟨hct.le, ht.2⟩).mono_of_mem_nhdsWithin
      (mem_nhdsWithin.2 ⟨Ioi c, isOpen_Ioi, hct, fun r hr ↦ ⟨hr.1.le, hr.2.2⟩⟩)

end ClosedInterval

end CovariantDerivative
