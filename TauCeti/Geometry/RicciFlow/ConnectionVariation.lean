/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Nondegenerate.RicciVariation
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ContractedBianchi
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.BilinearTensor.SMul

/-!
# Levi-Civita connection variation under Ricci flow

The native metric equation identifies its first variation with `-2 Ric`. The Koszul variation
formula then gives the native connection velocity as three covariant derivatives of Ricci.
Both scalar and tensor curvature evolution use these shared identities.

## References

* P. Topping, *Lectures on the Ricci Flow*, §2.5.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public noncomputable section

open Bundle FiberBundle CovariantDerivative
open scoped ContDiff Manifold Topology RealInnerProductSpace

namespace TauCeti.Manifold.ContMDiffNondegenerateMetricFamily

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  (g : ContMDiffNondegenerateMetricFamily I M 𝓘(ℝ) ℝ)
  {cov : ℝ → CovariantDerivative I E (TangentSpace I : M → Type _)} {t : ℝ}
  [∀ s, CovariantDerivative.ContMDiffCovariantDerivative (cov s) ∞]

/-- The native first metric variation is `-2 Ric` when the metric evaluations satisfy
Ricci flow at the time under consideration. -/
theorem variation_eq_neg_two_ricciTensor
    (hflow : ∀ (y : M) (u v : TangentSpace I y),
      HasDerivAt (fun s ↦ g (s, y) u v) (-2 * (cov t).ricciTensor y u v) t) :
    g.variation t 1 = (-2 : ℝ) • fun y ↦ (cov t).ricciTensor y |>.toContinuousBilinearMap := by
  funext y
  ext u v
  have hn := g.hasDerivAt_apply_apply_comp (c := id) (t := t) mdifferentiableAt_id y u v
  simpa using hn.unique (hflow y u v)

/-- The actual Levi-Civita connection velocity under Ricci flow is given by the three
covariant derivatives of Ricci in the Koszul variation formula. -/
theorem apply_deriv_difference_eq_neg_derivRicciTensor
    (hcov : ∀ s, (g.metric s).IsLeviCivitaConnection (cov s))
    (hflow : ∀ (y : M) (u v : TangentSpace I y),
      HasDerivAt (fun s ↦ g (s, y) u v) (-2 * (cov t).ricciTensor y u v) t)
    (y : M) (u v w : TangentSpace I y) :
    g (t, y) (deriv (fun s ↦ (cov s).difference (cov t) y) t u v) w =
      -(cov t).derivRicciTensor y u w v - (cov t).derivRicciTensor y v w u +
        (cov t).derivRicciTensor y v u w := by
  have hh := g.variation_eq_neg_two_ricciTensor hflow
  have heq := g.two_mul_apply_deriv_difference_eq_derivBilinearTensor
    (c := id) (t := t) contMDiffAt_id hcov y u v w
  simp only [mfderiv_id, ContinuousLinearMap.id_apply, id_eq] at heq
  rw [hh] at heq
  have hs (a b c : TangentSpace I y) :=
    (cov t).derivBilinearTensor_const_smul
      (b := fun z ↦ ((cov t).ricciTensor z).toContinuousBilinearMap) (x := y)
      (-2) a b c
  rw [hs, hs, hs] at heq
  rw [← CovariantDerivative.derivRicciTensor_def] at heq
  linarith

end TauCeti.Manifold.ContMDiffNondegenerateMetricFamily
