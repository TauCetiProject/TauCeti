/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Relative.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Variation
import TauCeti.Geometry.Manifold.ContMDiff.ParametricIntegral.Deriv
import TauCeti.Geometry.Manifold.ContMDiff.Prod

/-!
# Volume variation along Ricci flow

The relative volume density has derivative `-Scal J` for any fixed reference
metric. On a compact manifold, a jointly `C¹` integrand differentiates against
the evolving volume as `d/dt ∫ u dV = ∫ (∂ₜu - Scal u) dV`. The integral identity
allows manifolds with boundary and requires the Ricci equation only at the base time.

## References

* J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture* (2007), Chapter 13.
* P. Topping, *Lectures on the Ricci Flow* (2006), Section 2.3.

Formalization references: https://github.com/frenzymath/lean-eval-submissions and
https://github.com/frenzymath/PoincareConjecture.
-/

public noncomputable section

open Bundle Function Set MeasureTheory Riemannian.Tensor
open scoped ContDiff Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}

namespace Bundle.ContMDiffRiemannianMetric

/-- Along the native Ricci equation the relative volume density satisfies
`J' = -Scal(g) J`, for an arbitrary fixed reference metric. -/
theorem hasDerivWithinAt_relativeVolumeDensity_of_ricciFlow
    {n : ℕ∞ω} (g₀ : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    {s : Set ℝ} {t : ℝ} (x : M)
    (hg : ∀ v w, HasDerivWithinAt (fun τ ↦ (g τ).inner x v w)
      (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g t).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w)) s t) :
    HasDerivWithinAt (fun τ ↦ relativeVolumeDensity g₀ (g τ) x)
      (-(g t).scalarCurvature x * relativeVolumeDensity g₀ (g t) x) s t := by
  let ρ (τ : ℝ) : ℝ :=
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨(g τ).toRiemannianMetric⟩
    TauCeti.chartVolumeDensity (I := I) x x
  let ρ₀ : ℝ := TauCeti.chartVolumeDensity (I := I)
    (TauCeti.WithMetric.toWithMetric g₀ x) (TauCeti.WithMetric.toWithMetric g₀ x)
  have heq (τ : ℝ) : relativeVolumeDensity g₀ (g τ) x = ρ τ / ρ₀ := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨(g τ).toRiemannianMetric⟩
    rw [relativeVolumeDensity_eq_div_chartVolumeDensity g₀ (g τ) (mem_chart_source H x)]
    congr 1
    simp only [TauCeti.chartVolumeDensity_def, chartGramMatrix_toWithMetric, ρ]
    congr 2
    ext i j
    exact (chartGramMatrix_apply (I := I) (E := E) x x i j).symm
  have hd : HasDerivWithinAt ρ (-(g t).scalarCurvature x * ρ t) s t :=
    TauCeti.hasDerivWithinAt_chartVolumeDensity_of_ricciFlow x (mem_chart_source H x) hg
  simpa only [← heq, mul_div_assoc] using hd.div_const ρ₀

end Bundle.ContMDiffRiemannianMetric

namespace TauCeti

open Bundle.ContMDiffRiemannianMetric

variable [CompactSpace M] {u : ℝ → M → ℝ} {t₀ : ℝ}

/-- **Differentiation against a Ricci-flow volume measure.** A jointly `C¹` integrand has
derivative `∫ (∂ₜu - Scal u) dV` when the metric satisfies the Ricci equation at the base time.
The metric and integrand need only be jointly `C¹` along that time slice. -/
theorem hasDerivAt_integral_riemannianVolume_of_ricciFlow
    (hg : ∀ x : M, ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2
        ((g p.1).inner p.2)) (t₀, x))
    (hflow : ∀ x v w, HasDerivAt (fun τ ↦ (g τ).inner x v w)
      (-2 * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g t₀).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w)) t₀)
    (hu : ∀ x, ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry u) (t₀, x)) :
    HasDerivAt (fun t ↦ ∫ x, u t x.ofWithMetric ∂riemannianVolume I (WithMetric (g t)))
      (∫ x, deriv (fun s ↦ u s x.ofWithMetric) t₀ -
        (g t₀).scalarCurvature x.ofWithMetric * u t₀ x.ofWithMetric
        ∂riemannianVolume I (WithMetric (g t₀))) t₀ := by
  let F (t : ℝ) (x : WithMetric (g t₀)) :=
    relativeVolumeDensity (g t₀) (g t) x.ofWithMetric * u t x.ofWithMetric
  have hF (x : WithMetric (g t₀)) :
      ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry F) (t₀, x) := by
    have : IsManifold I (1 + 1) M := IsManifold.of_le (n := ∞) (by simp)
    have hc : ContMDiffAt (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) 1
        (fun p : ℝ × WithMetric (g t₀) ↦ (p.1, p.2.ofWithMetric)) (t₀, x) :=
      contMDiffAt_fst.prodMk
        ((WithMetric.contMDiff_ofWithMetric (g := g t₀)).contMDiffAt.comp _ contMDiffAt_snd)
    exact ((contMDiffAt_uncurry_relativeVolumeDensity (g₀ := g t₀) (g := g)
      ((hg x.ofWithMetric).comp x.ofWithMetric (contMDiffAt_const.prodMk contMDiffAt_id))
      (hg x.ofWithMetric)).comp (t₀, x) hc).mul ((hu x.ofWithMetric).comp (t₀, x) hc)
  have hd (x : WithMetric (g t₀)) :
      deriv (fun t ↦ F t x) t₀ = deriv (fun t ↦ u t x.ofWithMetric) t₀ -
        (g t₀).scalarCurvature x.ofWithMetric * u t₀ x.ofWithMetric := by
    have hJ : HasDerivAt (fun t ↦ relativeVolumeDensity (g t₀) (g t) x.ofWithMetric)
        (-(g t₀).scalarCurvature x.ofWithMetric) t₀ := by
      simpa only [hasDerivWithinAt_univ, relativeVolumeDensity_self, mul_one] using
        hasDerivWithinAt_relativeVolumeDensity_of_ricciFlow (g t₀) x.ofWithMetric
          (fun v w ↦ (hflow x.ofWithMetric v w).hasDerivWithinAt (s := univ))
    have hu' : DifferentiableAt ℝ (fun t ↦ u t x.ofWithMetric) t₀ :=
      (hu x.ofWithMetric).differentiableAt_slice_fst one_ne_zero
    simpa only [Pi.mul_def, F, relativeVolumeDensity_self, one_mul, neg_mul,
      sub_eq_add_neg, add_comm]
      using (hJ.mul hu'.hasDerivAt).deriv
  have h := hasDerivAt_parametric_integral (J := I)
    (μ := riemannianVolume I (WithMetric (g t₀))) hF
  have hmass : (fun t ↦ ∫ x, u t x.ofWithMetric
      ∂riemannianVolume I (WithMetric (g t))) =
      fun t ↦ ∫ x, F t x ∂riemannianVolume I (WithMetric (g t₀)) := by
    funext t
    simpa only [F, smul_eq_mul] using
      integral_riemannianVolume_eq_integral_relativeVolumeDensity_smul (g t₀) (g t) (u t)
  rw [hmass]
  simpa only [hd] using h

end TauCeti
