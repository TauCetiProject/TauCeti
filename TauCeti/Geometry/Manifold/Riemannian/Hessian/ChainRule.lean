/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.ChainRule

/-!
# The chain rule for the Riemannian Hessian

If `h : ℝ → ℝ` is `C²` near `f x` and `f` is `C²` at `x`, then

`Hess (h ∘ f) = h'(f) Hess f + h''(f) df ⊗ df`

at `x`. The gradient chain rule gives `grad (h ∘ f) = h'(f) • grad f` near `x`, and the Leibniz
rule of the Levi-Civita connection differentiates this product. Only pointwise `C²` regularity
of `f` and a `C¹` metric are needed. The square `f ^ 2` is the special case used for squared
distance functions.

See J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 5.
-/

public noncomputable section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff InnerProductSpace Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- **Chain rule for the Hessian.** If `h` is `C²` near `f x` and `f` is `C²` at `x`, then
`Hess (h ∘ f) = h'(f) Hess f + h''(f) df ⊗ df` at `x`. -/
theorem hessian_comp {h : ℝ → ℝ} {f : M → ℝ} {x : M} (hh : ContDiffAt ℝ 2 h (f x))
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (v w : TangentSpace I x) :
    hessian I (h ∘ f) x v w =
      deriv h (f x) * hessian I f x v w +
        deriv (deriv h) (f x) * mvfderiv I f x v * mvfderiv I f x w := by
  have : IsManifold I (1 + 1) M := by
    simpa only [one_add_one_eq_two] using (inferInstance : IsManifold I 2 M)
  let cov := leviCivitaConnection I M
  obtain ⟨u, hu, hhu⟩ := hh.contDiffOn le_rfl (by simp)
  obtain ⟨s, hsu, hs, hxs⟩ := mem_nhds_iff.1 hu
  have hhs : ContDiffOn ℝ 2 h s := hhu.mono hsu
  have hh' : ContDiffOn ℝ 1 (deriv h) s := hhs.deriv_of_isOpen hs (by norm_num)
  have hfx : MDifferentiableAt I 𝓘(ℝ) f x := hf.mdifferentiableAt (by norm_num)
  have hdx : DifferentiableAt ℝ (deriv h) (f x) :=
    (hh'.differentiableOn one_ne_zero _ hxs).differentiableAt (hs.mem_nhds hxs)
  let G := mgradient I f
  let g : M → ℝ := deriv h ∘ f
  have hG : MDiffAt (T% G) x := (contMDiffAt_mgradient (n := 1) hf).mdifferentiableAt (by simp)
  have hg : MDiffAt g x := hdx.comp_mdifferentiableAt hfx
  have hgrad : MDiffAt (T% (mgradient I (h ∘ f))) x :=
    (contMDiffAt_mgradient (n := 1) (hh.contMDiffAt.comp x hf)).mdifferentiableAt (by simp)
  have hprod : MDiffAt (T% (g • G)) x := hg.smul_section hG
  have heq : ∀ᶠ y in 𝓝 x, mgradient I (h ∘ f) y = (g • G) y := by
    filter_upwards [hf.continuousAt.preimage_mem_nhds (hs.mem_nhds hxs),
      hf.eventually_mdifferentiableAt (by norm_num)] with y hys hy
    exact mgradient_comp_deriv
      ((hhs.differentiableOn (by norm_num) _ hys).differentiableAt (hs.mem_nhds hys)) hy
  have hdg : mvfderiv I g x v = deriv (deriv h) (f x) * mvfderiv I f x v := by
    rw [← inner_mgradient, mgradient_comp_deriv hdx hfx, real_inner_smul_left,
      inner_mgradient]
  have hcov := cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hgrad hprod
    Filter.univ_mem heq
  rw [hessian_def, hcov, cov.isCovariantDerivativeOnUniv.leibniz hG hg]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    inner_add_left,
    real_inner_smul_left, inner_mgradient, hdg, hessian_def, G, g, cov, Function.comp_apply]

/-- The Hessian of the square of a `C²` function. -/
theorem hessian_sq {f : M → ℝ} {x : M} (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (v w : TangentSpace I x) :
    hessian I (fun y ↦ f y ^ 2) x v w =
      2 * mvfderiv I f x v * mvfderiv I f x w + 2 * f x * hessian I f x v w := by
  have hd : deriv (fun t : ℝ ↦ t ^ 2) = fun t ↦ 2 * t := by
    funext t
    simp
  have hdd : deriv (fun t : ℝ ↦ 2 * t) (f x) = 2 := by simp
  have := hessian_comp (h := fun t : ℝ ↦ t ^ 2) (contDiffAt_id.pow 2) hf v w
  rw [hd, hdd] at this
  refine this.trans ?_
  beta_reduce
  ring

end TauCeti.Manifold
