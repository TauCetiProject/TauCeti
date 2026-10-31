/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Hessian
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Ricci
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Trace
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# The Bochner formula for functions

For a smooth function `f` on a Riemannian manifold with Levi-Civita connection `∇`, the
**Bochner formula** is

`½ Δ |grad f|² = |Hess f|² + ⟨grad f, grad Δ f⟩ + Ric(grad f, grad f)`,

where `Δ = div ∘ grad` is `TauCeti.Manifold.laplaceBeltrami` and
`|Hess f|² = ∑ᵢⱼ Hess f(eᵢ, eⱼ)²` in an orthonormal basis `eᵢ`. With the nonnegative Laplacian
`Δ⁺ = -Δ` it reads `Δ⁺ |df|² + 2 |Hess f|² + 2 Ric(grad f, grad f) = 2 ⟨df, d Δ⁺ f⟩`. The
statement is pointwise: it needs neither compactness nor completeness, and it holds in every
dimension, including zero and one. Integrated over a closed manifold it is the source of the
Lichnerowicz eigenvalue estimate and of Bochner's vanishing theorems.

The formula combines three local identities for the gradient `G = grad f`, all stated with the
second covariant derivative `∇²G(u, v) = ∇_u ∇_V G - ∇_{∇_u V} G`
(`CovariantDerivative.secondCovariantDerivative`).

* For every smooth vector field `X`, metric compatibility gives
  `Hess |X|²(u, v) = 2 ⟨∇²X(u, v), X⟩ + 2 ⟨∇_u X, ∇_v X⟩`; tracing gives the first term.
* Since `Hess f(v, w) = ⟨∇_v G, w⟩` is symmetric, so is `w ↦ ⟨∇²G(u, v), w⟩` in `(v, w)`:
  the third covariant derivative of `f` is symmetric in its last two slots.
* The Ricci identity `∇²G(u, v) - ∇²G(v, u) = R(u, v) G` moves the traced direction past the
  free one, and the trace of `∇_w Hess f` is `d(Δ f)(w)`
  (`CovariantDerivative.IsMetricCompatible.mvfderiv_bilinFormTrace`). Together they give the
  contracted identity `∑ᵢ ⟨∇²G(eᵢ, eᵢ), w⟩ = d(Δ f)(w) + Ric(w, G)`, which says that the rough
  Laplacian of `grad f` is `grad Δ f + Ric(grad f)`.

## Main results

* `TauCeti.Manifold.hessian_norm_sq`: the Hessian of the squared length of a smooth vector field.
* `TauCeti.Manifold.inner_secondCovariantDerivative_mgradient_comm`: the third covariant
  derivative of a smooth function is symmetric in its last two slots.
* `TauCeti.Manifold.sum_inner_secondCovariantDerivative_mgradient_self`: the contracted Ricci
  identity `∑ᵢ ⟨∇²(grad f)(eᵢ, eᵢ), w⟩ = d(Δ f)(w) + Ric(w, grad f)`.
* `TauCeti.Manifold.laplaceBeltrami_norm_sq_mgradient`: **the Bochner formula**.

## References

* P. Petersen, *Riemannian Geometry*, 3rd ed., Springer GTM 171 (2016), Chapter 9 (the Bochner
  technique).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 7 (the Ricci identities).
-/

public section

open Bundle
open scoped ContDiff InnerProductSpace Manifold

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **The Hessian of the squared length of a vector field.** For a smooth vector field `X`,
`Hess |X|²(u, v) = 2 ⟨∇²X(u, v), X⟩ + 2 ⟨∇_u X, ∇_v X⟩`, where `∇` is the Levi-Civita connection
and `∇²X(u, v) = ∇_u ∇_V X - ∇_{∇_u V} X`, for any smooth vector field `V` with `V x = v`, is its
second covariant derivative. -/
theorem hessian_norm_sq {X : Π x : M, TangentSpace I x} (hX : CMDiff ∞ (T% X)) (x : M)
    (u v : TangentSpace I x) :
    letI cov := CovariantDerivative.leviCivitaConnection I M
    hessian I (fun y ↦ ‖X y‖ ^ 2) x u v =
      2 * ⟪cov.secondCovariantDerivative cov X x u v, X x⟫_ℝ + 2 * ⟪cov X x u, cov X x v⟫_ℝ := by
  set cov := CovariantDerivative.leviCivitaConnection I M
  have hcov := CovariantDerivative.isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  have hXd (y : M) : MDiffAt (T% X) y := hX.mdifferentiable (by simp) y
  have hfun : (fun y ↦ ‖X y‖ ^ 2) = fun y ↦ ⟪X y, X y⟫_ℝ :=
    funext fun y ↦ (real_inner_self_eq_norm_sq (X y)).symm
  -- The directional derivative of `|X|²` is `⟨∇_w X, X⟩ + ⟨X, ∇_w X⟩`.
  have hd (y : M) (w : TangentSpace I y) :
      mvfderiv I (fun y ↦ ‖X y‖ ^ 2) y w =
        ⟪cov X y w, X y⟫_ℝ + ⟪X y, cov X y w⟫_ℝ := by
    have h := hcov.mvfderiv_inner_eq (FiberBundle.extend E w) (hXd y) (hXd y)
    simp only [FiberBundle.extend_apply_self] at h
    rw [hfun]
    exact h
  obtain ⟨U, hU, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E u
  obtain ⟨V, hV, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E v
  -- The bundle argument of `ContMDiff.inner_bundle` is not inferred through `TangentSpace`.
  have hXX : CMDiff ∞ fun y ↦ ⟪X y, X y⟫_ℝ :=
    ContMDiff.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x) (b := id) hX hX
  have hsq : ContMDiffAt I 𝓘(ℝ) 2 (fun y ↦ ‖X y‖ ^ 2) x := by
    rw [hfun]
    exact (hXX.of_le (by simp)).contMDiffAt
  have hVX : MDiffAt (T% (fun y ↦ cov X y (V y))) x :=
    (cov.contMDiff_apply hV hX).mdifferentiableAt (by simp)
  have hdV : (fun y ↦ mvfderiv I (fun y ↦ ‖X y‖ ^ 2) y (V y)) =
      (fun y ↦ ⟪cov X y (V y), X y⟫_ℝ) + fun y ↦ ⟪X y, cov X y (V y)⟫_ℝ :=
    funext fun y ↦ hd y (V y)
  -- The bundle argument of `MDifferentiableAt.inner_bundle` is not inferred through
  -- `TangentSpace`.
  have hinner {A B : Π y : M, TangentSpace I y} (hA : MDiffAt (T% A) x)
      (hB : MDiffAt (T% B) x) : MDiffAt (fun y ↦ ⟪A y, B y⟫_ℝ) x :=
    MDifferentiableAt.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x)
      (b := id) hA hB
  have h₁ := hcov.mvfderiv_inner_eq U hVX (hXd x)
  have h₂ := hcov.mvfderiv_inner_eq U (hXd x) hVX
  rw [hessian_apply_eq_mvfderiv_sub x hsq U V (hV.mdifferentiableAt (by simp)), hdV,
    mvfderiv_add (hinner hVX (hXd x)) (hinner (hXd x) hVX), hd,
    cov.secondCovariantDerivative_apply cov hX x hV]
  simp only [add_apply] at h₁ h₂ ⊢
  rw [h₁, h₂]
  simp only [cov, inner_sub_right, real_inner_comm (X x),
    real_inner_comm (CovariantDerivative.leviCivitaConnection I M X x (U x))]
  ring

section Gradient

variable {f : M → ℝ}

/-- The Hessian of `f` at `y` as a continuous bilinear form, `(v, w) ↦ ⟪∇_v grad f, w⟫`. -/
private def hessianForm (f : M → ℝ) (y : M) :
    TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ :=
  (innerSL ℝ : TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ).comp
    (CovariantDerivative.leviCivitaConnection I M (mgradient I f) y)

omit [T2Space M] in
private theorem hessianForm_apply (f : M → ℝ) (y : M) (v w : TangentSpace I y) :
    hessianForm f y v w = hessian I f y v w := by
  simp [hessianForm, hessian_def]

omit [T2Space M] in
/-- The Hessian of a smooth function pairs vector fields differentiable at `x` to a function
differentiable at `x`. -/
private theorem mdifferentiableAt_hessianForm_apply (hf : ContMDiff I 𝓘(ℝ) ∞ f) {x : M}
    {σ τ : Π y : M, TangentSpace I y} (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) :
    MDiffAt (fun y ↦ hessianForm f y (σ y) (τ y)) x := by
  let _ : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  set cov := CovariantDerivative.leviCivitaConnection I M
  have hG : CMDiff ∞ (T% (mgradient I f)) := contMDiff_mgradient hf
  have hhom : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (cov (mgradient I f) y)) Set.univ :=
    (inferInstance : CovariantDerivative.ContMDiffCovariantDerivative cov ∞).contMDiff.contMDiff
      hG.contMDiffOn
  have hGσ : MDiffAt (T% (fun y ↦ cov (mgradient I f) y (σ y))) x :=
    ((hhom.contMDiffAt Filter.univ_mem).mdifferentiableAt (by simp)).clm_bundle_apply hσ
  simp only [hessianForm, ContinuousLinearMap.coe_comp, Function.comp_apply, innerSL_apply_apply]
  -- The bundle argument of `MDifferentiableAt.inner_bundle` is not inferred through
  -- `TangentSpace`.
  exact MDifferentiableAt.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x)
    (b := id) hGσ hτ

/-- Pairing the second covariant derivative of `grad f` with a vector is the covariant derivative
of the Hessian: `⟪∇²(grad f)(u, v), w⟫ = (∇_u Hess f)(v, w)`. -/
private theorem inner_secondCovariantDerivative_mgradient_eq (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (x : M) (u v w : TangentSpace I x) :
    letI cov := CovariantDerivative.leviCivitaConnection I M
    ⟪cov.secondCovariantDerivative cov (mgradient I f) x u v, w⟫_ℝ =
      cov.derivBilinearTensor (hessianForm f) x v w u := by
  let _ : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  set cov := CovariantDerivative.leviCivitaConnection I M
  have hcov := CovariantDerivative.isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  have hG : CMDiff ∞ (T% (mgradient I f)) := contMDiff_mgradient hf
  obtain ⟨V, hV, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E v
  obtain ⟨W, hW, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E w
  have hVd : MDiffAt (T% V) x := hV.mdifferentiable (by simp) x
  have hWd : MDiffAt (T% W) x := hW.mdifferentiable (by simp) x
  have hGV : MDiffAt (T% (fun y ↦ cov (mgradient I f) y (V y))) x :=
    (cov.contMDiff_apply hV hG).mdifferentiable (by simp) x
  have hpair : (fun y ↦ hessianForm f y (V y) (W y)) =
      fun y ↦ ⟪cov (mgradient I f) y (V y), W y⟫_ℝ := by
    funext y
    simp [hessianForm, cov]
  have hd := hcov.mvfderiv_inner_eq (FiberBundle.extend E u) hGV hWd
  simp only [FiberBundle.extend_apply_self] at hd
  rw [cov.derivBilinearTensor_apply (fun _ _ hσ hτ ↦ mdifferentiableAt_hessianForm_apply hf hσ hτ)
    hVd hWd u, hpair, hd, cov.secondCovariantDerivative_apply cov hG x hV]
  simp only [hessianForm, ContinuousLinearMap.coe_comp, Function.comp_apply, innerSL_apply_apply,
    inner_sub_left]
  ring

/-- The third covariant derivative of a smooth function is symmetric in its last two slots:
`⟪∇²(grad f)(u, v), w⟫ = ⟪∇²(grad f)(u, w), v⟫`, since it is the covariant derivative of the
symmetric Hessian. -/
theorem inner_secondCovariantDerivative_mgradient_comm (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    (u v w : TangentSpace I x) :
    letI cov := CovariantDerivative.leviCivitaConnection I M
    ⟪cov.secondCovariantDerivative cov (mgradient I f) x u v, w⟫_ℝ =
      ⟪cov.secondCovariantDerivative cov (mgradient I f) x u w, v⟫_ℝ := by
  have hsymm (y : M) (a c : TangentSpace I y) : hessianForm f y a c = hessianForm f y c a := by
    rw [hessianForm_apply, hessianForm_apply, hessian_symm y (hf.of_le (by simp)).contMDiffAt]
  rw [inner_secondCovariantDerivative_mgradient_eq hf,
    inner_secondCovariantDerivative_mgradient_eq hf,
    (CovariantDerivative.leviCivitaConnection I M).derivBilinearTensor_apply_comm hsymm]

/-- **The contracted Ricci identity for the gradient.** In every orthonormal basis `eᵢ` of the
tangent space at `x`, `∑ᵢ ⟪∇²(grad f)(eᵢ, eᵢ), w⟫ = d(Δ f)(w) + Ric(w, grad f)`, where
`Δ = div ∘ grad` is `TauCeti.Manifold.laplaceBeltrami`. Equivalently, the rough Laplacian of
`grad f` is `grad Δ f + Ric(grad f)`. -/
theorem sum_inner_secondCovariantDerivative_mgradient_self (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (w : TangentSpace I x) :
    letI cov := CovariantDerivative.leviCivitaConnection I M
    ∑ i, ⟪cov.secondCovariantDerivative cov (mgradient I f) x (b i) (b i), w⟫_ℝ =
      mvfderiv I (laplaceBeltrami I f) x w + cov.ricciTensor x w (mgradient I f x) := by
  let _ : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  set cov := CovariantDerivative.leviCivitaConnection I M
  have hcov := CovariantDerivative.isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  have hG : CMDiff ∞ (T% (mgradient I f)) := contMDiff_mgradient hf
  have ht : cov.IsTorsionFree := (CovariantDerivative.isTorsionFree_iff_torsion_eq_zero cov).2
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I)
  -- Move the traced direction past `w` by symmetry and the Ricci identity.
  have hswap (i : ι) :
      ⟪cov.secondCovariantDerivative cov (mgradient I f) x (b i) (b i), w⟫_ℝ =
        cov.derivBilinearTensor (hessianForm f) x (b i) (b i) w +
          ⟪b i, cov.curvatureTensor x (b i) w (mgradient I f x)⟫_ℝ := by
    have hR := cov.secondCovariantDerivative_sub_swap_of_isTorsionFree cov ht hG x (b i) w
    simp only [cov] at hR ⊢
    rw [inner_secondCovariantDerivative_mgradient_comm hf,
      ← inner_secondCovariantDerivative_mgradient_eq hf, ← hR, inner_sub_right,
      real_inner_comm (b i), real_inner_comm (b i)]
    ring
  -- The trace of `∇_w Hess f` is `d(Δ f)(w)`.
  have hlap : (fun y ↦ TauCeti.bilinFormTrace
      (ContinuousLinearMap.toLinearMap₁₂ (hessianForm (I := I) f y))) = laplaceBeltrami I f := by
    funext y
    rw [TauCeti.bilinFormTrace_eq_sum _ (stdOrthonormalBasis ℝ (TangentSpace I y)),
      laplaceBeltrami_eq_sum_hessian I f y (stdOrthonormalBasis ℝ (TangentSpace I y))]
    simp [hessianForm_apply]
  have htr := hcov.mvfderiv_bilinFormTrace
    (fun _ _ hσ hτ ↦ mdifferentiableAt_hessianForm_apply hf hσ hτ) b w
  rw [hlap] at htr
  rw [Finset.sum_congr rfl fun i _ ↦ hswap i, Finset.sum_add_distrib, ← htr,
    cov.ricciTensor_eq_sum_inner x b]

/-- **The Bochner formula.** For a smooth function `f` and every orthonormal basis `eᵢ` of the
tangent space at `x`,
`Δ |grad f|² = 2 ∑ᵢⱼ Hess f(eᵢ, eⱼ)² + 2 d(Δ f)(grad f) + 2 Ric(grad f, grad f)`,
where `Δ = div ∘ grad` is `TauCeti.Manifold.laplaceBeltrami` and `Ric` is the Ricci tensor of the
Levi-Civita connection. For the nonnegative Laplacian `Δ⁺ = -Δ` this is
`Δ⁺ |df|² + 2 |Hess f|² + 2 Ric(grad f, grad f) = 2 ⟨df, d Δ⁺ f⟩`. -/
theorem laplaceBeltrami_norm_sq_mgradient (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    laplaceBeltrami I (fun y ↦ ‖mgradient I f y‖ ^ 2) x =
      2 * ∑ i, ∑ j, hessian I f x (b i) (b j) ^ 2 +
        2 * mvfderiv I (laplaceBeltrami I f) x (mgradient I f x) +
        2 * (CovariantDerivative.leviCivitaConnection I M).ricciTensor x (mgradient I f x)
          (mgradient I f x) := by
  let _ : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hG : CMDiff ∞ (T% (mgradient I f)) := contMDiff_mgradient hf
  -- `‖∇_{eᵢ} grad f‖² = ∑ⱼ Hess f(eᵢ, eⱼ)²`.
  have hnorm (i : ι) :
      ⟪CovariantDerivative.leviCivitaConnection I M (mgradient I f) x (b i),
          CovariantDerivative.leviCivitaConnection I M (mgradient I f) x (b i)⟫_ℝ =
        ∑ j, hessian I f x (b i) (b j) ^ 2 := by
    rw [← b.sum_inner_mul_inner]
    simp only [hessian_def, real_inner_comm (b _), sq]
  rw [laplaceBeltrami_eq_sum_hessian I _ x b]
  simp only [hessian_norm_sq hG x, hnorm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_inner_secondCovariantDerivative_mgradient_self hf x b]
  ring

end Gradient

end TauCeti.Manifold
