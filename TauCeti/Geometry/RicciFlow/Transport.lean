/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Analysis.ODE.MetricTransport
public import
  TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Ricci.Endomorphism
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Moving-frame transport for Ricci flow

On a closed time interval, a metric family with `C¹` time pairings satisfying `∂ₜ g = -2 Ric`
admits invertible transport on every fixed tangent fibre solving `P' = Ric♯ P`. This preserves the
evolving metric and hence transports any initial orthonormal family to orthonormal families.
The coefficient is the actual native Ricci tensor with one index raised by the metric.

Continuity of the coefficient in time follows from the `C¹` metric pairings and the flow
equation; no curvature evolution equation is assumed. The construction is fibrewise and makes
no assertion about smooth dependence on the spatial point.

## References

* B. Cook and B. Kotschwar, *The full holonomy group under the Ricci flow*, Section 2.1.
* Formalization references: https://github.com/frenzymath/lean-eval-submissions and
  https://github.com/frenzymath/PoincareConjecture.
-/

public noncomputable section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

namespace TauCeti

variable {g : ℝ → ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
  {cov : ℝ → CovariantDerivative I E (TangentSpace I : M → Type _)}
  [∀ t, ContMDiffCovariantDerivative (cov t) ∞] {a b t₀ : ℝ}

/-- For a metric family with `C¹` time pairings solving the Ricci flow equation, the raised Ricci
tensor is continuous in time on each tangent fibre, including empty and singleton
closed slabs. -/
theorem continuousOn_ricciEndomorphism_of_ricciFlow
    (x : M) (hg : ∀ v w : TangentSpace I x, ContDiffOn ℝ 1 (fun t ↦ (g t).inner x v w) (Icc a b))
    (hflow : ∀ t ∈ Icc a b, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s ↦ (g s).inner x v w)
        (-2 * (cov t).ricciTensor x v w) (Icc a b) t) :
    ContinuousOn (fun t ↦ (cov t).ricciEndomorphism (g t).toNondegenerateMetric x) (Icc a b) := by
  by_cases hab : a < b
  swap
  · exact (Set.subsingleton_Icc_of_ge (not_lt.mp hab)).continuousOn _
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g a).toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  let G : ℝ → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
    fun t ↦ (g t).inner x
  let R : ℝ → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
    fun t ↦ ((cov t).ricciTensor x).toContinuousBilinearMap
  have hG : ContinuousOn G (Icc a b) :=
    continuousOn_clm_apply.mpr fun v ↦ continuousOn_clm_apply.mpr fun w ↦
      (hg v w).continuousOn
  have hR : ContinuousOn R (Icc a b) := by
    apply (continuousOn_clm_apply (𝕜 := ℝ) (E := TangentSpace I x)
      (F := TangentSpace I x →L[ℝ] ℝ) (f := R)).mpr
    intro v
    apply (continuousOn_clm_apply (𝕜 := ℝ) (E := TangentSpace I x)
      (F := ℝ) (f := fun t ↦ R t v)).mpr
    intro w
    apply ((hg v w).continuousOn_derivWithin
      (uniqueDiffOn_Icc hab) (by simp)).const_mul (-1 / 2) |>.congr
    intro t ht
    -- Evaluating the continuous bilinear representative gives the native Ricci pairing.
    change (cov t).ricciTensor x v w = _
    have hd := (hflow t ht v w).derivWithin (uniqueDiffOn_Icc hab t ht)
    dsimp only
    linarith
  have hcoeff : (fun t ↦ (cov t).ricciEndomorphism (g t).toNondegenerateMetric x) =
      fun t ↦ (G t).inverse ∘L R t := by
    funext t
    rw [CovariantDerivative.ricciEndomorphism_def]
    have heq : (g t).toNondegenerateMetric x = G t := by ext v w; simp [G]
    rw [heq]
  rw [hcoeff]
  intro t ht
  have heq : (g t).toNondegenerateMetric x = G t := by ext v w; simp [G]
  have hinv := (g t).toNondegenerateMetric.isInvertible x
  rw [heq] at hinv
  have hi : ContinuousAt (ContinuousLinearMap.inverse :
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) →
        (TangentSpace I x →L[ℝ] ℝ) →L[ℝ] TangentSpace I x) (G t) :=
    (ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse
      (𝕜 := ℝ) (E := TangentSpace I x) (F := TangentSpace I x →L[ℝ] ℝ)
      (e := G t) (n := ∞) hinv).continuousAt
  have hc : ContinuousWithinAt (fun s ↦ (G s).inverse) (Icc a b) t :=
    hi.comp_continuousWithinAt (hG t ht)
  exact ContinuousWithinAt.clm_comp (𝕜 := ℝ) (E := TangentSpace I x)
    (F := TangentSpace I x →L[ℝ] ℝ) (G := TangentSpace I x) hc (hR t ht)

/-- Fibrewise moving-frame transport for the native Ricci tensor. Starting at any included
time, it solves `P' = Ric♯ P`, is invertible, and preserves the evolving metric throughout the
closed slab. No choice of background Riemannian norm is part of the statement. -/
theorem exists_ricciTransport_Icc (ht₀ : t₀ ∈ Icc a b)
    (x : M) (hg : ∀ v w : TangentSpace I x, ContDiffOn ℝ 1 (fun t ↦ (g t).inner x v w) (Icc a b))
    (hflow : ∀ t ∈ Icc a b, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s ↦ (g s).inner x v w)
        (-2 * (cov t).ricciTensor x v w) (Icc a b) t) :
    ∃ P : ℝ → TangentSpace I x →L[ℝ] TangentSpace I x,
      P t₀ = 1 ∧
      (∀ t ∈ Icc a b, HasDerivAt P
        ((cov t).ricciEndomorphism (g t).toNondegenerateMetric x * P t) t) ∧
      (∀ t, (P t).IsInvertible) ∧
      ∀ t ∈ Icc a b, ∀ v w, (g t).inner x (P t v) (P t w) = (g t₀).inner x v w := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g a).toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  let G : ℝ → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
    fun t ↦ (g t).inner x
  let R : ℝ → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
    fun t ↦ ((cov t).ricciTensor x).toContinuousBilinearMap
  let A : ℝ → TangentSpace I x →L[ℝ] TangentSpace I x :=
    fun t ↦ (cov t).ricciEndomorphism (g t).toNondegenerateMetric x
  have hA : ContinuousOn A (Icc a b) :=
    continuousOn_ricciEndomorphism_of_ricciFlow x hg hflow
  by_cases hab : a < b
  swap
  · obtain ⟨P, hi, hd, hinv⟩ := exists_isInvertible_hasDerivAt_clm_Icc ht₀ A hA
    refine ⟨P, hi, hd, hinv, ?_⟩
    intro t ht v w
    have heq : t = t₀ := Set.subsingleton_Icc_of_ge (not_lt.mp hab) ht ht₀
    simp only [heq, hi, one_apply_eq_self]
  have hderiv : ∀ t ∈ Icc a b, HasDerivWithinAt G ((-2 : ℝ) • R t) (Icc a b) t := by
    intro t ht
    apply (hasDerivWithinAt_clm_apply₂ (uniqueDiffOn_Icc hab t ht)).mpr
    intro v w
    simpa only [G, R, smul_apply, smul_eq_mul, LinearMap.toContinuousBilinearMap_apply]
      using hflow t ht v w
  apply exists_pairing_preserving_transport_Icc ht₀ A
    hA G
    (fun t ↦ (-2 : ℝ) • R t) hderiv
  intro t ht v w
  have hsymm : (cov t).ricciTensor x v w = (cov t).ricciTensor x w v := by
    have heq := (uniqueDiffOn_Icc hab t ht).eq_deriv (Icc a b) (hflow t ht v w)
      ((hflow t ht w v).congr_of_mem (fun s _ ↦ (g s).symm x v w) ht)
    linarith
  -- Evaluate the operator-valued cancellation identity as the geometric Ricci pairing.
  change (-2 * (cov t).ricciTensor x v w) +
    (g t).inner x ((cov t).ricciEndomorphism (g t).toNondegenerateMetric x v) w +
    (g t).inner x v ((cov t).ricciEndomorphism (g t).toNondegenerateMetric x w) = 0
  rw [(g t).symm x v ((cov t).ricciEndomorphism (g t).toNondegenerateMetric x w)]
  simp only [← Bundle.ContMDiffRiemannianMetric.toNondegenerateMetric_apply,
    CovariantDerivative.inner_ricciEndomorphism, ← hsymm]
  ring

/-- A fibrewise orthonormal family can be propagated by the Ricci moving-frame equation
throughout the closed time interval. Orthonormality is measured using the metric at that time. -/
theorem exists_orthonormal_ricciFrame_Icc (ht₀ : t₀ ∈ Icc a b)
    (x : M) (hg : ∀ v w : TangentSpace I x, ContDiffOn ℝ 1 (fun t ↦ (g t).inner x v w) (Icc a b))
    (hflow : ∀ t ∈ Icc a b, ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s ↦ (g s).inner x v w)
        (-2 * (cov t).ricciTensor x v w) (Icc a b) t)
    {ι : Type*} (e₀ : ι → TangentSpace I x)
    (he₀ : letI : RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨(g t₀).toRiemannianMetric⟩; Orthonormal ℝ e₀) :
    ∃ e : ℝ → ι → TangentSpace I x,
      e t₀ = e₀ ∧
      (∀ t ∈ Icc a b, ∀ i, HasDerivAt (fun s ↦ e s i)
        ((cov t).ricciEndomorphism (g t).toNondegenerateMetric x (e t i)) t) ∧
      ∀ t ∈ Icc a b,
        letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g t).toRiemannianMetric⟩;
        Orthonormal ℝ (e t) := by
  classical
  have hinit : ∀ i j, (g t₀).inner x (e₀ i) (e₀ j) = if i = j then 1 else 0 := by
    let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g t₀).toRiemannianMetric⟩
    exact orthonormal_iff_ite.mp he₀
  obtain ⟨P, hi, hd, _, hpair⟩ := exists_ricciTransport_Icc ht₀ x hg hflow
  refine ⟨fun t i ↦ P t (e₀ i), by simp [hi], ?_, ?_⟩
  · intro t ht i
    let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g a).toRiemannianMetric⟩
    simpa only [mul_apply_eq_comp, map_zero, add_zero] using
      (hd t ht).clm_apply (hasDerivAt_const t (e₀ i))
  · intro t ht
    let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g t).toRiemannianMetric⟩
    apply orthonormal_iff_ite.mpr
    intro i j
    -- The installed native Riemannian structure pairs by this time slice of the metric.
    change (g t).inner x (P t (e₀ i)) (P t (e₀ j)) = _
    rw [hpair t ht]
    exact hinit i j

end TauCeti
