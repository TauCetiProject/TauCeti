/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.VanishingMeanOscillation.Basic
public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Matrix.EuclideanLin.Measurable
import TauCeti.Analysis.PDE.DirichletProblem
import TauCeti.Analysis.PDE.DirichletProblem.ContinuousDependence
import TauCeti.Analysis.PDE.EnergyForm.Poincare
import TauCeti.Analysis.PDE.Ellipticity.Integral
import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.Analysis.PDE.Regularity.DivergenceFormSchauder.Basic
import TauCeti.Analysis.Sobolev.W1p.Convex
import TauCeti.MeasureTheory.Function.BoundedMeanOscillation.Sarason
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Topology.MetricSpace.Holder

/-!
# Interior `W^{1,p}` regularity for coefficients of vanishing mean oscillation

Let `a` be a measurable coefficient matrix on `ℝ^{n+1}`, uniformly elliptic with constants
`0 < λ ≤ Λ`, neither symmetric nor continuous in general, whose operators `a(x)` have small mean
oscillation below a radius `r₀`: its VMO modulus `η_a(r₀)` (`TauCeti.vmoModulus`) is at most a
threshold `δ`. Let `u ∈ H¹(Ω)` be a local weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` in `Ω`,

and let `G ∈ Lᵖ(B(x₀, R))`, `2 < p < ∞`, on a ball `B(x₀, R) ⊆ Ω` with `4 R ≤ r₀`. This file
proves that `∇u ∈ Lᵖ(B(x₀, R/2))`, with

`‖∇u‖_{Lᵖ(B(x₀, R/2))} ≤ C (‖G‖_{Lᵖ(B(x₀, R))} + |B(x₀, R)|^(1/p - 1/2) ‖∇u‖_{L²(B(x₀, R))})`,

where `C` and `δ` depend only on `n`, `p`, `λ` and `Λ`
(`TauCeti.PDE.exists_memLp_gradient_ball_and_eLpNorm_le_of_vmoModulus_le`). For coefficients of
vanishing mean oscillation the threshold is reached below some radius, so `∇u ∈ Lᵖ_loc(Ω)` whenever
`G ∈ Lᵖ_loc(Ω)` (`TauCeti.PDE.exists_memLp_gradient_ball_and_eLpNorm_le_of_memVMO`).

The interior estimate `TauCeti.PDE.exists_eLpNorm_gradient_ball_le_eLpNorm_two_of_setAverage_le`
is an a priori estimate: it assumes `u, ∇u ∈ Lᵖ(B(x₀, R))` and bounds the norm. Here only
`u ∈ H¹(Ω)` is assumed, and the integrability of `∇u` is a conclusion. This regularity statement is
what a duality argument for exponents `1 < p < 2` needs: there the adjoint problem is solved in
`H¹` and its solution must be shown to have a gradient in the dual exponent.

## The argument

* **Mollified coefficients.** The mollifications `aₖ = ψₖ ⋆ a` at scales `r₀ / (k + 1)`, taken in
  the operators on `ℝ^{n+1}`, are smooth and uniformly elliptic with the same constants, since the
  elliptic operators form a closed convex set
  (`ContDiffBump.normed_convolution_mem_of_convex`). Their VMO modulus at the scale `r₀` is at most
  `(4 + 4ⁿ⁺² 2ⁿ⁺¹) η_a(r₀)`, by Sarason's estimate of the BMO distance from `a` to its
  mollification (`TauCeti.bmoSeminorm_sub_normed_convolution_le`), so the a priori estimate applies
  to them with the same constants. They converge to `a` almost everywhere.
* **Approximate solutions.** With the data `Gₖ`, mollifications of `G` cut off outside the ball,
  let `uₖ` solve `-∂ᵢ(aₖⁱʲ ∂ⱼuₖ) = -div Gₖ` in `B(x₀, R)` with the boundary values of `u`. By
  continuous dependence on the coefficients
  (`TauCeti.PDE.tendsto_of_forall_energyFormH1_eq_of_tendsto_ae`) and on the data, `uₖ → u` in
  `H¹(B(x₀, R))`.
* **A priori integrability.** The coefficients and data of the approximate problems are Hölder, so
  the interior Schauder estimate for divergence-form equations of
  `TauCeti.Analysis.PDE.Regularity.DivergenceFormSchauder.Basic` bounds `∇uₖ` on every smaller
  ball, and `uₖ` is Lipschitz there. Hence the a priori estimate
  applies to `uₖ` on the balls `B(x₀, ρ)`, `ρ < R`, with constants independent of `k`.
* **Passing to the limit.** Along a subsequence `∇uₖ → ∇u` almost everywhere, and Fatou's lemma
  carries the estimates to `u` on `B(x₀, ρ / 2)`; letting `ρ → R` gives the estimate on
  `B(x₀, R / 2)`.

## Main declarations

* `TauCeti.PDE.exists_memLp_gradient_ball_and_eLpNorm_le_of_vmoModulus_le`: interior `W^{1,p}`
  regularity, `2 < p < ∞`, for coefficients of small mean oscillation below a radius.
* `TauCeti.PDE.exists_memLp_gradient_ball_and_eLpNorm_le_of_memVMO`: the same for coefficients of
  vanishing mean oscillation, below a radius depending on the coefficients.

## References

* N. V. Krylov, *Parabolic and elliptic equations with VMO coefficients*, Comm. Partial
  Differential Equations **32** (2007), 453–475.
* G. Di Fazio, *Lᵖ estimates for divergence form elliptic equations with discontinuous
  coefficients*, Boll. Un. Mat. Ital. A (7) **10** (1996), 409–420, Theorem 2.1.
* D. Sarason, *Functions of vanishing mean oscillation*, Trans. Amer. Math. Soc. **207** (1975),
  391–405 (mollification in BMO).
-/

public section

noncomputable section

open Filter InnerProductSpace MeasureTheory Metric Module Set TopologicalSpace Matrix
  ContinuousLinearMap
open scoped ENNReal NNReal Convolution ContDiff Distributions Gradient InnerProductSpace Topology

namespace TauCeti

namespace PDE

variable {n : ℕ}

section Mollification

variable {lam Lam : ℝ} {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}

/-- The mollification of a coefficient field by a normalized bump, taken in the operators on
`ℝ^{n+1}` and read back as a matrix. -/
private def mollifiedCoeff (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin (n + 1))))
    (a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun x =>
  (toEuclideanCLM (𝕜 := ℝ)).symm
    ((φ.normed volume ⋆[lsmul ℝ ℝ, volume] fun y => toEuclideanCLM (𝕜 := ℝ) (a y)) x)

/-- The operator of the mollified coefficient field is the mollification of the operators. -/
private theorem toEuclideanCLM_mollifiedCoeff
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin (n + 1)))) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    toEuclideanCLM (𝕜 := ℝ) (mollifiedCoeff φ a x) =
      (φ.normed volume ⋆[lsmul ℝ ℝ, volume] fun y => toEuclideanCLM (𝕜 := ℝ) (a y)) x :=
  StarAlgEquiv.apply_symm_apply _ _

/-- Mollification keeps a coefficient field uniformly elliptic with the same constants. -/
private theorem uniformlyEllipticOn_mollifiedCoeff (ha : AEStronglyMeasurable a volume)
    (hell : UniformlyEllipticOn univ a lam Lam)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin (n + 1)))) :
    UniformlyEllipticOn univ (mollifiedCoeff φ a) lam Lam :=
  uniformlyEllipticOn_of_forall_toEuclideanCLM_mem hell.pos hell.le fun x _ => by
    rw [toEuclideanCLM_mollifiedCoeff]
    exact φ.normed_convolution_mem_of_convex (convex_ellipticCLMSet lam Lam)
      (isClosed_ellipticCLMSet lam Lam) (hell.locallyIntegrable_toEuclideanCLM ha)
      (fun y => (toEuclideanCLM_mem_ellipticCLMSet_iff _).2
        ((uniformlyEllipticOn_iff.1 hell).2.2 (mem_univ y))) x

/-- A mollified coefficient field is `α`-Hölder on every bounded set, for every `α ≤ 1`. -/
private theorem exists_holderOnWith_mollifiedCoeff (ha : AEStronglyMeasurable a volume)
    (hell : UniformlyEllipticOn univ a lam Lam)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin (n + 1)))) {α : ℝ≥0} (hα : α ≤ 1)
    {S : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hS : Bornology.IsBounded S) :
    ∃ K, HolderOnWith K α (fun x => matrixBilinearForm (mollifiedCoeff φ a x)) S := by
  have hsmooth : ContDiff ℝ 1
      (φ.normed volume ⋆[lsmul ℝ ℝ, volume] fun y => toEuclideanCLM (𝕜 := ℝ) (a y)) :=
    φ.contDiff_normed_convolution (hell.locallyIntegrable_toEuclideanCLM ha)
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_holderOnWith_of_isCompact
    (hsmooth.locallyLipschitz.locallyLipschitzOn (s := univ)) hα hS.isCompact_closure
    (subset_univ _)
  refine ⟨K, fun x hx y hy => ?_⟩
  calc edist (matrixBilinearForm (mollifiedCoeff φ a x)) (matrixBilinearForm (mollifiedCoeff φ a y))
      = edist ((φ.normed volume ⋆[lsmul ℝ ℝ, volume] fun y => toEuclideanCLM (𝕜 := ℝ) (a y)) x)
          ((φ.normed volume ⋆[lsmul ℝ ℝ, volume] fun y => toEuclideanCLM (𝕜 := ℝ) (a y)) y) := by
        rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm,
          norm_matrixBilinearForm_sub_eq_norm_toEuclideanCLM_sub, toEuclideanCLM_mollifiedCoeff,
          toEuclideanCLM_mollifiedCoeff]
    _ ≤ _ := hK x (subset_closure hx) y (subset_closure hy)

/-- A mollified coefficient field is measurable. -/
private theorem aestronglyMeasurable_mollifiedCoeff (ha : AEStronglyMeasurable a volume)
    (hell : UniformlyEllipticOn univ a lam Lam)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin (n + 1)))) :
    AEStronglyMeasurable (mollifiedCoeff φ a) volume :=
  Matrix.aestronglyMeasurable_toEuclideanCLM_iff.1
    ((φ.contDiff_normed_convolution (hell.locallyIntegrable_toEuclideanCLM ha)
      (n := 0)).continuous.aestronglyMeasurable.congr
        (ae_of_all _ fun x => (toEuclideanCLM_mollifiedCoeff φ x).symm))

/-- Along bumps whose radii tend to zero, the mollified coefficient fields converge to the field
almost everywhere. -/
private theorem ae_tendsto_mollifiedCoeff (ha : AEStronglyMeasurable a volume)
    (hell : UniformlyEllipticOn univ a lam Lam)
    {φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin (n + 1)))}
    (hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0)) (hφ2 : ∀ k, (φ k).rOut ≤ 2 * (φ k).rIn) :
    ∀ᵐ x, Tendsto (fun k => mollifiedCoeff (φ k) a x) atTop (𝓝 (a x)) := by
  filter_upwards [ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hφ
    (Eventually.of_forall hφ2) (hell.locallyIntegrable_toEuclideanCLM ha)] with x hx
  have h := (Matrix.continuous_toEuclideanCLM_symm.tendsto _).comp hx
  rw [StarAlgEquiv.symm_apply_apply] at h
  exact h

/-- **Mollified coefficients keep a small mean oscillation.** If the VMO modulus of `a` at the
scale `r₀` is at most `δ`, then on every ball of radius at most `r₀` a mollification of `a` at a
scale at most `r₀` deviates in mean from an elliptic constant matrix by at most a dimensional
multiple of `δ`: the BMO distance from `a` to its mollification is controlled by Sarason's
estimate `TauCeti.bmoSeminorm_sub_normed_convolution_le`. -/
private theorem exists_setAverage_norm_mollifiedCoeff_sub_le (ha : AEStronglyMeasurable a volume)
    (hell : UniformlyEllipticOn univ a lam Lam) {r₀ δ : ℝ} (hδ : 0 ≤ δ)
    (hη : vmoModulus (fun x => toEuclideanCLM (𝕜 := ℝ) (a x)) volume r₀ ≤ ENNReal.ofReal δ)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin (n + 1)))) (hφ : φ.rOut ≤ 2 * φ.rIn)
    (hφr : φ.rOut ≤ r₀) (c : EuclideanSpace ℝ (Fin (n + 1))) {r : ℝ} (hr : 0 < r)
    (hrr : r ≤ r₀) :
    ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
      UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam ∧
        ⨍ x in ball c r, ‖matrixBilinearForm (mollifiedCoeff φ a x) - matrixBilinearForm A‖ ≤
          (4 + 4 ^ (finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) + 1) *
            2 ^ finrank ℝ (EuclideanSpace ℝ (Fin (n + 1)))) * δ := by
  set e := toEuclideanCLM (𝕜 := ℝ) (n := Fin (n + 1))
  set d := finrank ℝ (EuclideanSpace ℝ (Fin (n + 1)))
  set β : EuclideanSpace ℝ (Fin (n + 1)) → _ := fun x => e (a x)
  set βφ := φ.normed volume ⋆[lsmul ℝ ℝ, volume] β
  have hβ := hell.locallyIntegrable_toEuclideanCLM ha
  have hβφc : Continuous βφ := (φ.contDiff_normed_convolution hβ (n := 0)).continuous
  -- The VMO modulus of the mollification at the scale `r₀`.
  have hbmo : bmoSeminorm (β - βφ) volume ≤ (3 + 4 ^ (d + 1) * 2 ^ d) * ENNReal.ofReal δ :=
    (bmoSeminorm_sub_normed_convolution_le φ hφ hβ).trans
      (by gcongr; exact (monotone_vmoModulus β volume hφr).trans hη)
  have hvmo : vmoModulus βφ volume r₀ ≤ (4 + 4 ^ (d + 1) * 2 ^ d) * ENNReal.ofReal δ := by
    have h := vmoModulus_sub_le hβ.aestronglyMeasurable
      (hβ.aestronglyMeasurable.sub hβφc.aestronglyMeasurable) r₀ (μ := volume)
    rw [sub_sub_cancel] at h
    refine h.trans ((add_le_add hη ((vmoModulus_le_bmoSeminorm _ _ _).trans hbmo)).trans_eq ?_)
    ring
  -- Freeze at the average of the mollification over the ball, which is elliptic.
  have hD : (4 + 4 ^ (d + 1) * 2 ^ d : ℝ≥0∞) * ENNReal.ofReal δ =
      ENNReal.ofReal ((4 + 4 ^ (d + 1) * 2 ^ d) * δ) := by
    rw [ENNReal.ofReal_mul (by positivity)]
    norm_cast
  refine ((uniformlyEllipticOn_mollifiedCoeff ha hell φ).mono_set (subset_univ _)
    |>.exists_uniformlyEllipticOn_const_and_setAverage_le measurableSet_ball
      (aestronglyMeasurable_mollifiedCoeff ha hell φ).restrict (measure_ball_pos volume c hr).ne'
      measure_ball_lt_top.ne (by positivity) ?_)
  simpa only [toEuclideanCLM_mollifiedCoeff, hD] using
    (setLAverage_enorm_sub_setAverage_le_vmoModulus βφ volume c hrr).trans hvmo

end Mollification

section Approximation

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace
  instSeminormedAddCommGroupW1p instNormedSpaceW1p

variable {lam Lam : ℝ} {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}

/-- The energy integrand of a uniformly elliptic field, with no lower-order terms, is essentially
bounded on every set. -/
private theorem memLp_energyIntegrand_of_uniformlyEllipticOn (ha : AEStronglyMeasurable a volume)
    (hell : UniformlyEllipticOn univ a lam Lam) (U : Set (EuclideanSpace ℝ (Fin (n + 1)))) :
    MemLp (fun x => energyIntegrand (a x)
      ((0 : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) x)
      ((0 : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)) ⊤ (volume.restrict U) :=
  (memLp_energyIntegrand_of_bounds (mu := volume) (Omega := ⊤) (b := 0) (c := 0)
    hell.upper_nonneg ha.restrict aestronglyMeasurable_const aestronglyMeasurable_const
    (fun x _ η ξ => hell.upper_bound (mem_univ x) η ξ)
    (fun _ _ => (by simp : ‖(0 : EuclideanSpace ℝ (Fin (n + 1)))‖ ≤ 0))
    (fun _ _ => (by simp : ‖(0 : ℝ)‖ ≤ 0))).mono_measure
      (Measure.restrict_mono (subset_univ _) le_rfl)

/-- On an open set inside a ball, the energy forms of all uniformly elliptic fields with the
constants `λ, Λ` are coercive on `H¹₀` with one constant. -/
private theorem exists_pos_forall_mul_norm_sq_le_energyFormH1 (hlam : 0 < lam)
    {U : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {z : EuclideanSpace ℝ (Fin (n + 1))} {ρ : ℝ}
    (hU : (U : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ ball z ρ) :
    ∃ C, 0 < C ∧ ∀ {b : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
      UniformlyEllipticOn univ b lam Lam → AEStronglyMeasurable b volume →
      ∀ w : W1p0 volume U 2,
        C * ‖w‖ ^ 2 ≤ energyFormH1 b 0 0 (w : W1p volume U 2) (w : W1p volume U 2) := by
  refine ⟨(lam ^ 2 - 0 ^ 2 * (2 * ρ) ^ 2) / (2 * lam * ((2 * ρ) ^ 2 + 1)),
    div_pos (by rw [zero_pow two_ne_zero, zero_mul, sub_zero]; positivity) (by positivity),
    fun {b} hell hb w => ?_⟩
  rw [← Submodule.norm_coe w]
  exact (hell.mono_set (subset_univ _)).mul_norm_sq_le_energyFormH1_self_of_subset_ball
    (beta := 0) (gamma := 0) hb.restrict aestronglyMeasurable_const aestronglyMeasurable_const
    (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => le_rfl) hU
    ((ClosedSubmodule.mem_toSubmodule_iff _ _).1 w.property)

/-- The Dirichlet problem `-∂ᵢ(bⁱʲ ∂ⱼw) = ℓ` in `U`, `w - g ∈ H¹₀(U)`, for a uniformly elliptic
field `b` on an open set `U` inside a ball, has exactly one weak solution. -/
private theorem existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_of_subset_ball
    {U : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {z : EuclideanSpace ℝ (Fin (n + 1))} {ρ : ℝ}
    (hU : (U : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ ball z ρ)
    {b : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hb : AEStronglyMeasurable b volume) (hell : UniformlyEllipticOn univ b lam Lam)
    (ℓ : StrongDual ℝ (W1p0 volume U 2)) (g : W1p volume U 2) :
    ∃! w : W1p volume U 2, w - g ∈ w1p0Submodule volume U 2 ∧
      ∀ v : W1p0 volume U 2, energyFormH1 b 0 0 w (v : W1p volume U 2) = ℓ v :=
  UniformlyEllipticOn.existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_of_subset_ball
    (hell.mono_set (subset_univ _)) hb.restrict aestronglyMeasurable_const
    aestronglyMeasurable_const (fun _ _ => (by simp : ‖(0 : EuclideanSpace ℝ (Fin (n + 1)))‖ ≤ 0))
    (fun _ _ => (by simp : ‖(0 : ℝ)‖ ≤ 0)) (fun _ _ => le_rfl) hU (by simpa using hell.pos) ℓ g

/-- Two solutions of `-∂ᵢ(bⁱʲ ∂ⱼw) = -div F` with the same coefficients and the same boundary
values, for data `F` and `F'`, differ in `H¹` by at most `‖F - F'‖_{L²} / C`, where `C` is a
coercivity constant of the energy form on `H¹₀`. -/
private theorem norm_sub_le_of_forall_energyFormH1_eq_inner
    {U : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {b : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hb : AEStronglyMeasurable b volume) (hell : UniformlyEllipticOn univ b lam Lam) {C : ℝ}
    (hC : 0 < C) (hlower : ∀ w : W1p0 volume U 2,
      C * ‖w‖ ^ 2 ≤ energyFormH1 b 0 0 (w : W1p volume U 2) (w : W1p volume U 2))
    {F F' : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2
      (volume.restrict (U : Set (EuclideanSpace ℝ (Fin (n + 1)))))}
    {w w' : W1p volume U 2} (hsub : w - w' ∈ w1p0Submodule volume U 2)
    (hw : ∀ v : W1p0 volume U 2, energyFormH1 b 0 0 w (v : W1p volume U 2) =
      ⟪F, W1p.gradient (v : W1p volume U 2)⟫_ℝ)
    (hw' : ∀ v : W1p0 volume U 2, energyFormH1 b 0 0 w' (v : W1p volume U 2) =
      ⟪F', W1p.gradient (v : W1p volume U 2)⟫_ℝ) :
    ‖w - w'‖ ≤ ‖F - F'‖ / C := by
  have hℓ (F : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2
      (volume.restrict (U : Set (EuclideanSpace ℝ (Fin (n + 1)))))) (v : W1p0 volume U 2) :
      (-divergenceForcing F) v = ⟪F, W1p.gradient (v : W1p volume U 2)⟫_ℝ := by
    simp
  have hnorm : ‖-divergenceForcing F - -divergenceForcing F'‖ ≤ ‖F - F'‖ := by
    have : -divergenceForcing F - -divergenceForcing F' = divergenceForcing (F' - F) := by
      ext v
      simp [inner_sub_left]
    rw [this]
    exact (norm_divergenceForcing_le _).trans_eq (norm_sub_rev _ _)
  have h := norm_sub_le_of_sub_sub_mem_w1p0Submodule_of_forall_energyFormH1_eq
    (memLp_energyIntegrand_of_uniformlyEllipticOn hb hell _) hC hlower (h := 0) le_rfl
    (fun v => by simp) le_rfl
    (fun v => le_of_eq (by rw [zero_mul, abs_eq_zero, sub_eq_zero])) (by rwa [sub_zero])
    (fun v => (hw v).trans (hℓ F v).symm) (fun v => (hw' v).trans (hℓ F' v).symm)
  rw [norm_zero, zero_add, add_zero, add_zero] at h
  exact h.trans (div_le_div_of_nonneg_right hnorm hC.le)

/-- **Approximation of a weak solution.** On an open set inside a ball, let `u` solve
`-∂ᵢ(aⁱʲ ∂ⱼu) = -div F` against `H¹₀`, and let `uₖ` solve the equations with coefficients `aₖ`
and data `Fₖ`, with the boundary values of `u`. If the `aₖ` are uniformly elliptic with the
constants of `a` and converge to `a` almost everywhere, and `Fₖ → F` in `L²`, then `uₖ → u` in
`H¹`. The solutions `wₖ` with coefficients `aₖ` and datum `F` converge to `u` by continuous
dependence on the coefficients, and `uₖ - wₖ` is controlled by `Fₖ - F`. -/
private theorem tendsto_of_forall_energyFormH1_eq_inner
    {U : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {z : EuclideanSpace ℝ (Fin (n + 1))} {ρ : ℝ}
    (hU : (U : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ ball z ρ)
    (hell : UniformlyEllipticOn univ a lam Lam) (ha : AEStronglyMeasurable a volume)
    {ak : ℕ → EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hellk : ∀ k, UniformlyEllipticOn univ (ak k) lam Lam)
    (hak : ∀ k, AEStronglyMeasurable (ak k) volume)
    (hlim : ∀ᵐ x, Tendsto (fun k => ak k x) atTop (𝓝 (a x)))
    {F : Lp (EuclideanSpace ℝ (Fin (n + 1))) 2
      (volume.restrict (U : Set (EuclideanSpace ℝ (Fin (n + 1)))))}
    {Fk : ℕ → Lp (EuclideanSpace ℝ (Fin (n + 1))) 2
      (volume.restrict (U : Set (EuclideanSpace ℝ (Fin (n + 1)))))}
    (hF : Tendsto Fk atTop (𝓝 F)) {u : W1p volume U 2}
    (hu : ∀ v : W1p0 volume U 2, energyFormH1 a 0 0 u (v : W1p volume U 2) =
      ⟪F, W1p.gradient (v : W1p volume U 2)⟫_ℝ)
    {uk : ℕ → W1p volume U 2} (hsub : ∀ k, uk k - u ∈ w1p0Submodule volume U 2)
    (huk : ∀ k, ∀ v : W1p0 volume U 2, energyFormH1 (ak k) 0 0 (uk k) (v : W1p volume U 2) =
      ⟪Fk k, W1p.gradient (v : W1p volume U 2)⟫_ℝ) :
    Tendsto uk atTop (𝓝 u) := by
  obtain ⟨C, hC, hlower⟩ := exists_pos_forall_mul_norm_sq_le_energyFormH1 (Lam := Lam) hell.pos hU
  -- The solutions `wₖ` with coefficients `aₖ`, the datum `F` and the boundary values of `u`.
  choose w hw _ using fun k =>
    existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_of_subset_ball hU (hak k) (hellk k)
      (-divergenceForcing F) u
  have hw_lim : Tendsto w atTop (𝓝 u) :=
    tendsto_of_forall_energyFormH1_eq_of_tendsto_ae
      (memLp_energyIntegrand_of_uniformlyEllipticOn ha hell _)
      (fun k => memLp_energyIntegrand_of_uniformlyEllipticOn (hak k) (hellk k) _) hC
      (fun k => hlower (hellk k) (hak k)) (fun k => (hak k).restrict)
      (fun k => ae_of_all _ fun x η ξ => abs_dotProduct_sub_mulVec_le
        (hell.upper_bound (mem_univ x)) ((hellk k).upper_bound (mem_univ x)) η ξ)
      (ae_restrict_of_ae hlim) (fun v => (hu v).trans (by simp)) (fun k => (hw k).2)
      (fun k => (hw k).1)
  -- `uₖ - wₖ` is controlled by the data: `‖uₖ - wₖ‖ ≤ ‖Fₖ - F‖ / C`.
  have hdiff (k : ℕ) : ‖uk k - w k‖ ≤ ‖Fk k - F‖ / C := by
    have hmem := (w1p0Submodule volume U 2).toSubmodule.sub_mem
      ((ClosedSubmodule.mem_toSubmodule_iff _ _).2 (hsub k))
      ((ClosedSubmodule.mem_toSubmodule_iff _ _).2 (hw k).1)
    rw [sub_sub_sub_cancel_right, ClosedSubmodule.mem_toSubmodule_iff] at hmem
    exact norm_sub_le_of_forall_energyFormH1_eq_inner (hak k) (hellk k) hC
      (hlower (hellk k) (hak k)) hmem (huk k) fun v => ((hw k).2 v).trans (by simp)
  have hsmall : Tendsto (fun k => uk k - w k) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) hdiff ?_
    simpa using (tendsto_iff_norm_sub_tendsto_zero.1 hF).div_const C
  simpa using hw_lim.add hsmall

/-- **Hölder coefficients and data give a bounded gradient.** On a ball `B(x₀, R)`, let `w` solve
`-∂ᵢ(bⁱʲ ∂ⱼw) = -div H` with `b` uniformly elliptic and `b`, `H` Hölder. Then `∇w` is essentially
bounded on every smaller concentric ball, by the interior Schauder estimate. -/
private theorem exists_ae_norm_gradient_le_of_holderOnWith {x₀ : EuclideanSpace ℝ (Fin (n + 1))}
    {R r : ℝ} (hr : 0 < r) (hrR : r < R)
    {b : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hell : UniformlyEllipticOn univ b lam Lam)
    (hb : ∃ K, HolderOnWith K 2⁻¹ (fun x => matrixBilinearForm (b x)) (ball x₀ R))
    {H : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hH : ∃ K, HolderOnWith K 2⁻¹ H (ball x₀ R))
    {w : W1p volume (⟨ball x₀ R, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2}
    (hw : ∀ φ : 𝓓((⟨ball x₀ R, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
      energyFormH1 b 0 0 w (W1p.ofTestFunctionₗ volume _ 2 φ) =
        ∫ x in ball x₀ R, ⟪H x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) :
    ∃ M : ℝ, ∀ᵐ x ∂volume.restrict (ball x₀ r), ‖W1p.gradient w x‖ ≤ M := by
  have hthick : thickening (R - r) (ball x₀ r) = ball x₀ R := by
    rw [_root_.thickening_ball (by linarith) hr, sub_add_cancel]
  obtain ⟨Kb, hKb⟩ := hb
  obtain ⟨KH, hKH⟩ := hH
  obtain ⟨C, -, hC⟩ :=
    exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_matrixBilinearForm
      (n := n) (α := 2⁻¹) (by norm_num) (by norm_num) (lam := lam) (Lam := Lam)
      (M := Kb * (R - r) ^ ((2⁻¹ : ℝ≥0) : ℝ))
  -- The precise representative of `∇w` is Hölder, hence bounded, on `B(x₀, r)`.
  have hP := hC (u := w) (S := ball x₀ r) (hell.mono_set (subset_univ _))
    (hthick ▸ hKb) (hthick ▸ hKH) le_rfl hw (by linarith) hthick.subset
  obtain ⟨M, hM⟩ := (hP.isBounded_image isBounded_ball).exists_norm_le
  refine ⟨M, ?_⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hrR.le)
    (MeasureTheory.ae_eq_restrict_preciseRepresentative isOpen_ball
      (W1p.locallyIntegrableOn_gradient w)), ae_restrict_mem measurableSet_ball] with x hx hxB
  rw [hx]
  exact hM _ (mem_image_of_mem _ hxB)

/-- **Hölder coefficients and data give bounded solutions.** In the setting of
`exists_ae_norm_gradient_le_of_holderOnWith`, the value and the gradient of `w` are essentially
bounded on every smaller concentric ball, hence lie in every `Lᵖ` there: with a bounded gradient,
`w` is Lipschitz. -/
private theorem memLp_value_and_memLp_gradient_ball_of_holderOnWith
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {R ρ : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    {b : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hell : UniformlyEllipticOn univ b lam Lam)
    (hb : ∃ K, HolderOnWith K 2⁻¹ (fun x => matrixBilinearForm (b x)) (ball x₀ R))
    {H : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hH : ∃ K, HolderOnWith K 2⁻¹ H (ball x₀ R))
    {w : W1p volume (⟨ball x₀ R, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2}
    (hw : ∀ φ : 𝓓((⟨ball x₀ R, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
      energyFormH1 b 0 0 w (W1p.ofTestFunctionₗ volume _ 2 φ) =
        ∫ x in ball x₀ R, ⟪H x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    (p : ℝ≥0∞) :
    MemLp (W1p.value w) p (volume.restrict (ball x₀ ρ)) ∧
      MemLp (W1p.gradient w) p (volume.restrict (ball x₀ ρ)) := by
  set t := (R - ρ) / 2
  have ht : 0 < t := by simp only [t]; linarith
  have hfin (r : ℝ) : IsFiniteMeasure (volume.restrict (ball x₀ r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hsubB : ball x₀ ρ ⊆ ball x₀ R := ball_subset_ball hρR.le
  obtain ⟨M, hgrad⟩ := exists_ae_norm_gradient_le_of_holderOnWith (r := ρ + t) (by positivity)
    (by simp only [t]; linarith) hell hb hH hw
  refine ⟨?_, MemLp.of_bound ((Lp.aestronglyMeasurable _).mono_measure
    (Measure.restrict_mono hsubB le_rfl)) M (ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (by linarith)) hgrad)⟩
  -- The precise representative of `w` is Lipschitz, hence bounded, on `B(x₀, ρ)`.
  have hthickρ : thickening t (ball x₀ ρ) = ball x₀ (ρ + t) := by
    rw [_root_.thickening_ball ht hρ]
    congr 1
    ring
  obtain ⟨Cv, hCv⟩ := W1p.exists_holderOnWith_preciseRepresentative_of_ae_norm_gradient_le w
    (S := ball x₀ ρ) (ρ := t) (hthickρ ▸ (ball_subset_ball (by simp only [t]; linarith)))
    (M := M.toNNReal) (hthickρ ▸ hgrad.mono fun x hx => hx.trans (Real.le_coe_toNNReal M))
    (γ := 1) le_rfl
  have hCvρ := hCv.mono (self_subset_thickening (half_pos ht) (ball x₀ ρ))
  obtain ⟨Mv, hMv⟩ := (hCvρ.isBounded_image isBounded_ball).exists_norm_le
  refine MemLp.of_bound ((Lp.aestronglyMeasurable _).mono_measure
    (Measure.restrict_mono hsubB le_rfl)) Mv ?_
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsubB
    (MeasureTheory.ae_eq_restrict_preciseRepresentative isOpen_ball
      (Lp.locallyIntegrableOn (W1p.value w) Fact.out)),
    ae_restrict_mem measurableSet_ball] with x hx hxB
  rw [hx]
  exact hMv _ (mem_image_of_mem _ hxB)

/-- **Mollified data.** A field `G ∈ Lᵖ(B(x₀, R))`, `2 ≤ p < ∞`, cut off outside the ball and
mollified, gives fields `Gₖ ∈ L²`, Hölder on the ball, with `‖Gₖ‖_{Lᵖ} ≤ ‖G‖_{Lᵖ(B(x₀, R))}` and
`Gₖ → G` in `L²(B(x₀, R))`. -/
private theorem exists_holderOnWith_eLpNorm_le_tendsto_eLpNorm_sub {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 2 ≤ p) (hp_top : p ≠ ⊤) {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hG : MemLp G p (volume.restrict (ball x₀ R))) :
    ∃ Gk : ℕ → EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)),
      (∀ k, ∃ K, HolderOnWith K 2⁻¹ (Gk k) (ball x₀ R)) ∧
      (∀ k, eLpNorm (Gk k) p volume ≤ eLpNorm G p (volume.restrict (ball x₀ R))) ∧
      (∀ k, MemLp (Gk k) 2 volume) ∧
      Tendsto (fun k => eLpNorm (Gk k - G) 2 (volume.restrict (ball x₀ R))) atTop (𝓝 0) := by
  have : IsFiniteMeasure (volume.restrict (ball x₀ R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  set Gt := (ball x₀ R).indicator G
  have hGtp : MemLp Gt p volume :=
    (memLp_indicator_iff_restrict measurableSet_ball.nullMeasurableSet).2 hG
  have hGt2 : MemLp Gt 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_ball.nullMeasurableSet).2 (hG.mono_exponent hp)
  set φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin (n + 1))) :=
    fun k => ContDiffBump.shrinking one_pos k
  refine ⟨fun k => (φ k).normed volume ⋆[lsmul ℝ ℝ, volume] Gt, fun k => ?_,
    fun k => (eLpNorm_normed_convolution_le hp_top (φ k) hGtp).trans_eq
      (eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball.nullMeasurableSet),
    fun k => (eLpNorm_normed_convolution_le ENNReal.ofNat_ne_top (φ k) hGt2).trans_lt hGt2, ?_⟩
  · -- The mollifications are smooth, hence Hölder on the ball.
    have hsmooth : ContDiff ℝ 1 ((φ k).normed volume ⋆[lsmul ℝ ℝ, volume] Gt) :=
      (φ k).contDiff_normed_convolution (hGt2.locallyIntegrable one_le_two)
    obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_holderOnWith_of_isCompact
      (hsmooth.locallyLipschitz.locallyLipschitzOn (s := univ)) (α := 2⁻¹) (by norm_num)
      (isCompact_closedBall x₀ R) (subset_univ _)
    exact ⟨K, hK.mono ball_subset_closedBall⟩
  -- On the ball, `Gₖ - G = Gₖ - Gt`, and `Gₖ → Gt` in `L²`.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_eLpNorm_normed_convolution_sub ENNReal.ofNat_ne_top
      (ContDiffBump.tendsto_rOut_shrinking one_pos) hGt2) (fun _ => zero_le) fun k => ?_
  refine (eLpNorm_congr_ae ?_).trans_le (eLpNorm_mono_measure _ Measure.restrict_le_self)
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  simp only [Pi.sub_apply, Gt, φ, indicator_of_mem hx]

/-- **The approximating problems.** Let `u ∈ H¹(Ω)` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly, let
`B = B(x₀, R) ⊆ Ω`, let `aₖ → a` almost everywhere be uniformly elliptic with the constants of `a`,
and let `Gₖ → G` in `L²(B)`. Then there are solutions `uₖ ∈ H¹(B)` of
`-∂ᵢ(aₖⁱʲ ∂ⱼuₖ) = -div Gₖ` in `B` with `uₖ → u|_B` in `H¹(B)`: those with the boundary values
of `u`. -/
private theorem exists_forall_energyFormH1_eq_and_tendsto (ha : AEStronglyMeasurable a volume)
    (hell : UniformlyEllipticOn univ a lam Lam)
    {ak : ℕ → EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hellk : ∀ k, UniformlyEllipticOn univ (ak k) lam Lam)
    (hak : ∀ k, AEStronglyMeasurable (ak k) volume)
    (hlim : ∀ᵐ x, Tendsto (fun k => ak k x) atTop (𝓝 (a x)))
    {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ}
    (hB : (⟨ball x₀ R, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) ≤ Ω)
    {u : W1p volume Ω 2} {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hu : ∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      ∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    (hG : MemLp G 2 (volume.restrict (ball x₀ R)))
    {Gk : ℕ → EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hGk : ∀ k, MemLp (Gk k) 2 volume)
    (hGlim : Tendsto (fun k => eLpNorm (Gk k - G) 2 (volume.restrict (ball x₀ R))) atTop (𝓝 0)) :
    ∃ uk : ℕ → W1p volume (⟨ball x₀ R, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2,
      (∀ k, ∀ φ : 𝓓((⟨ball x₀ R, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
        energyFormH1 (ak k) 0 0 (uk k) (W1p.ofTestFunctionₗ volume _ 2 φ) =
          ∫ x in ball x₀ R, ⟪Gk k x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) ∧
      Tendsto uk atTop (𝓝 (W1p.restrictL hB u)) := by
  set B : Opens (EuclideanSpace ℝ (Fin (n + 1))) := ⟨ball x₀ R, isOpen_ball⟩
  -- The restriction of `u` to `B`, and the data as elements of `L²(B)`.
  have hG0 : MemLp (fun x => G x - 0) 2 (volume.restrict B) := by
    simp only [sub_zero]
    exact hG
  have huB := forall_energyFormH1_restrictL_eq_inner hB
    (memLp_energyIntegrand_of_uniformlyEllipticOn ha hell _) hu hG0
  have hGk0 (k : ℕ) : MemLp (fun x => Gk k x - 0) 2 (volume.restrict B) := by
    simpa using (hGk k).restrict (B : Set (EuclideanSpace ℝ (Fin (n + 1))))
  have hF : Tendsto (fun k => (hGk0 k).toLp) atTop (𝓝 hG0.toLp) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    refine hGlim.congr fun k => eLpNorm_congr_ae ?_
    filter_upwards [(hGk0 k).coeFn_toLp, hG0.coeFn_toLp] with x h₁ h₂
    rw [Pi.sub_apply, Pi.sub_apply, h₁, h₂, sub_zero, sub_zero]
  -- The approximating solutions, with the boundary values of `u` on `B`.
  choose uk huk _ using fun k =>
    existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_of_subset_ball (U := B)
      (subset_refl (ball x₀ R)) (hak k) (hellk k) (-divergenceForcing (hGk0 k).toLp)
      (W1p.restrictL hB u)
  have hukeq (k : ℕ) (v : W1p0 volume B 2) :
      energyFormH1 (ak k) 0 0 (uk k) (v : W1p volume B 2) =
        ⟪(hGk0 k).toLp, W1p.gradient (v : W1p volume B 2)⟫_ℝ :=
    ((huk k).2 v).trans (by simp)
  exact ⟨uk, fun k ψ => (hukeq k ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule ψ⟩).trans
      (inner_toLp_gradient_ofTestFunctionₗ (hGk0 k) ψ),
    tendsto_of_forall_energyFormH1_eq_inner (U := B) (z := x₀) (ρ := R) subset_rfl hell ha hellk
      hak hlim hF huB (fun k => (huk k).1) hukeq⟩

end Approximation

section Limit

/-- **Passing to the limit on growing balls.** Let `fₖ → g` almost everywhere on `B(x₀, R)`, and let
the `Lᵖ` norms of `fₖ` on the balls `B(x₀, ρₖ / 2)` be bounded by `bₖ → c`, where `ρₖ ≤ R` and
`ρₖ → R`. Then the `Lᵖ` norm of `g` on `B(x₀, R / 2)` is at most `c`, by Fatou's lemma. -/
private theorem eLpNorm_ball_half_le_of_tendsto {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞}
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ} (hR : 0 ≤ R) {ρ : ℕ → ℝ} (hρR : ∀ k, ρ k ≤ R)
    (hρ : Tendsto ρ atTop (𝓝 R)) {f : ℕ → EuclideanSpace ℝ (Fin (n + 1)) → F}
    {g : EuclideanSpace ℝ (Fin (n + 1)) → F}
    (hf : ∀ k, AEStronglyMeasurable (f k) (volume.restrict (ball x₀ R)))
    (hlim : ∀ᵐ x ∂volume.restrict (ball x₀ R), Tendsto (fun k => f k x) atTop (𝓝 (g x)))
    {b : ℕ → ℝ≥0∞} {c : ℝ≥0∞}
    (hb : ∀ k, eLpNorm (f k) p (volume.restrict (ball x₀ (ρ k / 2))) ≤ b k)
    (hc : Tendsto b atTop (𝓝 c)) :
    eLpNorm g p (volume.restrict (ball x₀ (R / 2))) ≤ c := by
  set μ := volume.restrict (ball x₀ R)
  have hind {r : ℝ} (hr : r ≤ R) (h : EuclideanSpace ℝ (Fin (n + 1)) → F) :
      eLpNorm ((ball x₀ r).indicator h) p μ = eLpNorm h p (volume.restrict (ball x₀ r)) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball.nullMeasurableSet,
      Measure.restrict_restrict measurableSet_ball, inter_eq_left.2 (ball_subset_ball hr)]
  have hhalf {r : ℝ} (hr : r ≤ R) : r / 2 ≤ R := by linarith
  have hg : AEStronglyMeasurable g μ := aestronglyMeasurable_of_tendsto_ae atTop hf hlim
  -- The cut-off functions converge almost everywhere: a point of `B(x₀, R / 2)` lies in
  -- `B(x₀, ρₖ / 2)` for all large `k`, and a point outside it lies in none of these balls.
  have hlim' : ∀ᵐ x ∂μ, Tendsto (fun k => (ball x₀ (ρ k / 2)).indicator (f k) x) atTop
      (𝓝 ((ball x₀ (R / 2)).indicator g x)) := by
    filter_upwards [hlim] with x hx
    by_cases hxR : x ∈ ball x₀ (R / 2)
    · rw [indicator_of_mem hxR]
      have hev : ∀ᶠ k in atTop, x ∈ ball x₀ (ρ k / 2) :=
        ((hρ.div_const 2).eventually (lt_mem_nhds (mem_ball.1 hxR))).mono fun k hk => hk
      exact hx.congr' (hev.mono fun k hk => (indicator_of_mem hk _).symm)
    · rw [indicator_of_notMem hxR]
      refine tendsto_const_nhds.congr fun k => (indicator_of_notMem (fun hk => hxR ?_) _).symm
      exact ball_subset_ball (by linarith [hρR k]) hk
  have h := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := p)
    (fun k => (hf k).indicator measurableSet_ball) _ (hg.indicator measurableSet_ball) hlim'
  rw [hind (hhalf le_rfl)] at h
  refine h.trans ((liminf_le_liminf (Eventually.of_forall fun k => ?_)).trans_eq hc.liminf_eq)
  rw [hind (hhalf (hρR k))]
  exact hb k

/-- **The limit of the approximating estimates.** Let `uₖ → u|_B` in `H¹(B)`, `B = B(x₀, R)`,
and suppose that on balls `B(x₀, ρₖ / 2)` with `ρₖ ≤ R`, `ρₖ → R`, the gradients satisfy
`‖∇uₖ‖_{Lᵖ(B(x₀, ρₖ/2))} ≤ C (Γ + 2^d V ‖∇uₖ‖_{L²(B)})` with finite `Γ` and `V`. Then
`∇u ∈ Lᵖ(B(x₀, R/2))` and `‖∇u‖_{Lᵖ(B(x₀, R/2))} ≤ C 2^d (Γ + V ‖∇u‖_{L²(B)})`. -/
private theorem memLp_gradient_and_eLpNorm_le_of_tendsto {p : ℝ≥0∞}
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ} (hR : 0 ≤ R)
    {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (hB : (⟨ball x₀ R, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) ≤ Ω)
    (u : W1p volume Ω 2)
    {uk : ℕ → W1p volume (⟨ball x₀ R, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2}
    (hconv : Tendsto uk atTop (𝓝 (W1p.restrictL hB u))) {ρ : ℕ → ℝ} (hρR : ∀ k, ρ k ≤ R)
    (hρ : Tendsto ρ atTop (𝓝 R)) (C : ℝ≥0) (d : ℕ) {Γ V : ℝ≥0∞} (hΓ : Γ ≠ ⊤) (hV : V ≠ ⊤)
    (hbound : ∀ k, eLpNorm (W1p.gradient (uk k)) p (volume.restrict (ball x₀ (ρ k / 2))) ≤
      C * (Γ + 2 ^ d * V * eLpNorm (W1p.gradient (uk k)) 2 (volume.restrict (ball x₀ R)))) :
    MemLp (W1p.gradient u) p (volume.restrict (ball x₀ (R / 2))) ∧
      eLpNorm (W1p.gradient u) p (volume.restrict (ball x₀ (R / 2))) ≤
        (C * 2 ^ d : ℝ≥0) * (Γ + V * eLpNorm (W1p.gradient u) 2 (volume.restrict (ball x₀ R))) := by
  have hgrad : Tendsto (fun k => W1p.gradient (uk k)) atTop
      (𝓝 (W1p.gradient (W1p.restrictL hB u))) := by
    simpa only [Function.comp_def, W1p.gradientL_apply] using
      (W1p.gradientL.continuous.tendsto _).comp hconv
  have hgradu : W1p.gradient (W1p.restrictL hB u) =ᵐ[volume.restrict (ball x₀ R)]
      W1p.gradient u := W1p.gradient_restrictL_ae hB u
  set X := eLpNorm (W1p.gradient u) 2 (volume.restrict (ball x₀ R))
  have hX : Tendsto (fun k => eLpNorm (W1p.gradient (uk k)) 2 (volume.restrict (ball x₀ R)))
      atTop (𝓝 X) := by
    have h := (continuous_eNorm.tendsto _).comp hgrad
    simp only [Function.comp_def, Lp.eNorm_def] at h
    convert h using 2
    exact (eLpNorm_congr_ae hgradu).symm
  have hXfin : X ≠ ⊤ :=
    ((eLpNorm_mono_measure _ (Measure.restrict_mono hB le_rfl)).trans_lt (Lp.memLp _)).ne
  -- Along a subsequence the gradients converge almost everywhere; Fatou's lemma concludes.
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hgrad).exists_seq_tendsto_ae
  have hlim := eLpNorm_ball_half_le_of_tendsto (p := p) hR (fun j => hρR (ns j))
    (hρ.comp hns.tendsto_atTop) (fun j => Lp.aestronglyMeasurable _) hae (fun j => hbound (ns j))
    (ENNReal.Tendsto.const_mul (tendsto_const_nhds.add (ENNReal.Tendsto.const_mul
      (hX.comp hns.tendsto_atTop) (Or.inr (ENNReal.mul_ne_top (by simp) hV))))
      (Or.inr ENNReal.coe_ne_top))
  rw [eLpNorm_congr_ae (ae_restrict_of_ae_restrict_of_subset
    (ball_subset_ball (by linarith)) hgradu)] at hlim
  have hle : eLpNorm (W1p.gradient u) p (volume.restrict (ball x₀ (R / 2))) ≤
      (C * 2 ^ d : ℝ≥0) * (Γ + V * X) := by
    refine hlim.trans (le_of_le_of_eq (b := (C : ℝ≥0∞) * (2 ^ d * Γ + 2 ^ d * V * X)) ?_ ?_)
    · gcongr
      exact le_mul_of_one_le_left zero_le (one_le_pow₀ one_le_two)
    · push_cast
      ring
  exact ⟨hle.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.add_lt_top.2
    ⟨hΓ.lt_top, ENNReal.mul_lt_top hV.lt_top hXfin.lt_top⟩)), hle⟩

end Limit

section Main

variable {lam Lam : ℝ}

/-- **Interior `W^{1,p}` regularity for coefficients of small mean oscillation.** Let `2 < p < ∞`
and `0 < λ ≤ Λ`. There are constants `C` and `δ > 0`, depending only on `n`, `p`, `λ` and `Λ`, with
the following property. Let `a` be a measurable coefficient matrix on `ℝ^{n+1}`, uniformly elliptic
with constants `λ, Λ`, whose VMO modulus at the scale `r₀`, as a field of operators on `ℝ^{n+1}`, is
at most `δ`. Let `u ∈ H¹(Ω)` solve `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly in `Ω`, let `B(x₀, R) ⊆ Ω`
with `4 R ≤ r₀`, and let `G ∈ Lᵖ(B(x₀, R))`. Then `∇u ∈ Lᵖ(B(x₀, R/2))` and

`‖∇u‖_{Lᵖ(B(x₀, R/2))} ≤ C (‖G‖_{Lᵖ(B(x₀, R))} + |B(x₀, R)|^(1/p - 1/2) ‖∇u‖_{L²(B(x₀, R))})`.

Unlike the a priori estimate
`TauCeti.PDE.exists_eLpNorm_gradient_ball_le_eLpNorm_two_of_setAverage_le`, nothing is assumed about
the integrability of `u` or `∇u` beyond `u ∈ H¹(Ω)`: the membership `∇u ∈ Lᵖ` is part of the
conclusion. The coefficients need not be symmetric or continuous. -/
theorem exists_memLp_gradient_ball_and_eLpNorm_le_of_vmoModulus_le {p : ℝ≥0∞} (hp : 2 < p)
    (hp_top : p ≠ ⊤) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {r₀ : ℝ},
        AEStronglyMeasurable a volume → UniformlyEllipticOn univ a lam Lam →
        vmoModulus (fun x => toEuclideanCLM (𝕜 := ℝ) (a x)) volume r₀ ≤ ENNReal.ofReal δ →
        ∀ {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {x₀ : EuclideanSpace ℝ (Fin (n + 1))}
          {R : ℝ}, 0 < R → 4 * R ≤ r₀ → ball x₀ R ⊆ (Ω : Set _) →
        ∀ (u : W1p volume Ω 2)
          (G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))),
          (∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
            ∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
          MemLp G p (volume.restrict (ball x₀ R)) →
          MemLp (W1p.gradient u) p (volume.restrict (ball x₀ (R / 2))) ∧
            eLpNorm (W1p.gradient u) p (volume.restrict (ball x₀ (R / 2))) ≤
              C * (eLpNorm G p (volume.restrict (ball x₀ R)) +
                volume (ball x₀ R) ^ (p.toReal⁻¹ - 2⁻¹) *
                  eLpNorm (W1p.gradient u) 2 (volume.restrict (ball x₀ R))) := by
  have : Fact (1 ≤ p) := ⟨one_le_two.trans hp.le⟩
  obtain ⟨C₀, δ₀, hδ₀, hap⟩ :=
    exists_eLpNorm_gradient_ball_le_eLpNorm_two_of_setAverage_le (n := n) hp hp_top lam Lam
  set d := finrank ℝ (EuclideanSpace ℝ (Fin (n + 1)))
  set K : ℝ := 4 + 4 ^ (d + 1) * 2 ^ d
  have hK : 0 < K := by positivity
  refine ⟨C₀ * 2 ^ d, δ₀ / K, div_pos hδ₀ hK,
    fun {a r₀} ha hell hη {Ω x₀ R} hR hRr₀ hball u G hu hG => ?_⟩
  have hr₀ : 0 < r₀ := by linarith
  have : IsFiniteMeasure (volume.restrict (ball x₀ R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  -- Mollify the coefficients at the scales `r₀ / (k + 1)`, and the datum.
  set φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin (n + 1))) :=
    fun k => ContDiffBump.shrinking hr₀ k
  have hφ2 (k : ℕ) : (φ k).rOut ≤ 2 * (φ k).rIn :=
    (ContDiffBump.rOut_shrinking_eq_two_mul_rIn hr₀ k).le
  have hellk (k : ℕ) := uniformlyEllipticOn_mollifiedCoeff ha hell (φ k)
  have hakm (k : ℕ) := aestronglyMeasurable_mollifiedCoeff ha hell (φ k)
  obtain ⟨Gk, hGkc, hGkp, hGk2, hGlim⟩ := exists_holderOnWith_eLpNorm_le_tendsto_eLpNorm_sub hp.le
    hp_top hG
  obtain ⟨uk, hukφ, hconv⟩ := exists_forall_energyFormH1_eq_and_tendsto ha hell hellk hakm
    (ae_tendsto_mollifiedCoeff ha hell (ContDiffBump.tendsto_rOut_shrinking hr₀) hφ2) hball hu
    (hG.mono_exponent hp.le) hGk2 hGlim
  -- Radii `R / 2 < ρₖ < R` increasing to `R`.
  obtain ⟨ρ, -, hρ, hρlim⟩ := exists_seq_strictMono_tendsto' (half_lt_self hR)
  -- The a priori estimate applies to the approximate solutions, with uniform constants.
  have hbound (k : ℕ) : eLpNorm (W1p.gradient (uk k)) p (volume.restrict (ball x₀ (ρ k / 2))) ≤
      C₀ * (eLpNorm G p (volume.restrict (ball x₀ R)) + 2 ^ d *
        volume (ball x₀ R) ^ (p.toReal⁻¹ - 2⁻¹) *
          eLpNorm (W1p.gradient (uk k)) 2 (volume.restrict (ball x₀ R))) := by
    have hρk := hρ k
    have hreg := memLp_value_and_memLp_gradient_ball_of_holderOnWith (by linarith [hρk.1])
      hρk.2 (hellk k) (exists_holderOnWith_mollifiedCoeff ha hell (φ k) (by norm_num)
        isBounded_ball) (hGkc k) (hukφ k) p
    refine (hap (hakm k) (fun x => (hellk k).opNorm_matrixBilinearForm_le (mem_univ x))
      (fun c r hr hrr => (exists_setAverage_norm_mollifiedCoeff_sub_le ha hell
        (div_pos hδ₀ hK).le hη (φ k) (hφ2 k) (ContDiffBump.rOut_shrinking_le hr₀ k) c hr hrr).imp
          fun A hA => ⟨hA.1, hA.2.trans_eq (by simp only [K, d]; field_simp)⟩)
      (by linarith [hρk.1]) (by linarith [hρk.2]) (ball_subset_ball hρk.2.le) (uk k) (Gk k)
      (hukφ k) hreg.1 hreg.2 ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans_lt
        ((hGkp k).trans_lt hG))).trans ?_
    gcongr
    · exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hGkp k)
    · have hp2 : 2 ≤ p.toReal := (ENNReal.ofReal_le_iff_le_toReal hp_top).1 (by simpa using hp.le)
      exact Measure.addHaar_ball_rpow_le_of_half_le volume x₀ hR hρk.1.le
        (by linarith [inv_nonneg.2 (zero_le_two.trans hp2)]) (by linarith [inv_anti₀ two_pos hp2])
    · exact hρk.2.le
  exact memLp_gradient_and_eLpNorm_le_of_tendsto hR.le hball u hconv (fun k => (hρ k).2.le)
    hρlim C₀ d hG.ne (ENNReal.rpow_ne_top_of_ne_zero (measure_ball_pos volume x₀ hR).ne'
      measure_ball_lt_top.ne) hbound

/-- **Interior `W^{1,p}` regularity for coefficients of vanishing mean oscillation.** Let
`2 < p < ∞` and `0 < λ ≤ Λ`. There is a constant `C`, depending only on `n`, `p`, `λ` and `Λ`, with
the following property. Let `a` be a coefficient matrix on `ℝ^{n+1}`, uniformly elliptic with
constants `λ, Λ`, whose operators `a(x)` have vanishing mean oscillation. Then there is a radius
`r₀ > 0` such that, whenever `u ∈ H¹(Ω)` solves `-∂ᵢ(aⁱʲ ∂ⱼu) = -div G` weakly in `Ω`,
`B(x₀, R) ⊆ Ω` with `R ≤ r₀` and `G ∈ Lᵖ(B(x₀, R))`, the gradient `∇u` lies in `Lᵖ(B(x₀, R/2))` and

`‖∇u‖_{Lᵖ(B(x₀, R/2))} ≤ C (‖G‖_{Lᵖ(B(x₀, R))} + |B(x₀, R)|^(1/p - 1/2) ‖∇u‖_{L²(B(x₀, R))})`.

In particular `∇u ∈ Lᵖ_loc(Ω)` whenever `G ∈ Lᵖ_loc(Ω)`. For the dependence of `r₀` on the VMO
modulus of `a`, see `TauCeti.PDE.exists_memLp_gradient_ball_and_eLpNorm_le_of_vmoModulus_le`. -/
theorem exists_memLp_gradient_ball_and_eLpNorm_le_of_memVMO {p : ℝ≥0∞} (hp : 2 < p)
    (hp_top : p ≠ ⊤) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∀ {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
      MemVMO (fun x => toEuclideanCLM (𝕜 := ℝ) (a x)) volume →
      UniformlyEllipticOn univ a lam Lam →
      ∃ r₀ : ℝ, 0 < r₀ ∧
        ∀ {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {x₀ : EuclideanSpace ℝ (Fin (n + 1))}
          {R : ℝ}, 0 < R → R ≤ r₀ → ball x₀ R ⊆ (Ω : Set _) →
        ∀ (u : W1p volume Ω 2)
          (G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))),
          (∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
            ∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
          MemLp G p (volume.restrict (ball x₀ R)) →
          MemLp (W1p.gradient u) p (volume.restrict (ball x₀ (R / 2))) ∧
            eLpNorm (W1p.gradient u) p (volume.restrict (ball x₀ (R / 2))) ≤
              C * (eLpNorm G p (volume.restrict (ball x₀ R)) +
                volume (ball x₀ R) ^ (p.toReal⁻¹ - 2⁻¹) *
                  eLpNorm (W1p.gradient u) 2 (volume.restrict (ball x₀ R))) := by
  obtain ⟨C, δ, hδ, hmain⟩ :=
    exists_memLp_gradient_ball_and_eLpNorm_le_of_vmoModulus_le (n := n) hp hp_top lam Lam
  refine ⟨C, fun {a} hvmo hell => ?_⟩
  obtain ⟨hbmo, hlim⟩ := memVMO_iff_tendsto.1 hvmo
  -- The VMO modulus is below `δ` on `(0, r₁)`.
  obtain ⟨r₁, hr₁, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1
    (hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hδ)))
  have hr₁' : 0 < r₁ := hr₁
  refine ⟨r₁ / 8, by positivity, fun {Ω x₀ R} hR hRr hball u G hu hG => ?_⟩
  have hη : vmoModulus (fun x => toEuclideanCLM (𝕜 := ℝ) (a x)) volume (4 * R) ≤
      ENNReal.ofReal δ := (hsub ⟨by positivity, by linarith⟩).le
  exact hmain (Matrix.aestronglyMeasurable_toEuclideanCLM_iff.1
    hbmo.locallyIntegrable.aestronglyMeasurable) hell hη hR le_rfl hball u G hu hG

end Main

end PDE

end TauCeti
