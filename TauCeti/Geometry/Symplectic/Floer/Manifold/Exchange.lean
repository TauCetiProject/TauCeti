/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Manifold

/-!
# The exchange `w ↦ 1 - w` preserves the Floer equation

The exchange `σ'(z) = (1, 0) - z` of the plane, which is `w ↦ 1 - w` in the real coordinates
`ℝ × ℝ ≃ ℂ`, is holomorphic, and a datum `P` on `ℂ` pulls back along it to `-P` at `1 - w`
(`TauCeti.Floer.perturbationPullback_one_sub`). So by the naturality of the perturbed derivative
(`TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_perturbationPullback`), composing a
solution of the Floer equation for `P` with `σ'` gives a solution for the datum `w ↦ -P (1 - w)`.

## Main results

* `TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_one_sub`: the exchange preserves
  the Floer equation with a manifold target.
-/

public noncomputable section

open scoped Manifold

namespace TauCeti.SmoothTwoForm

open Floer

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  {u : ℝ × ℝ → M} {w : ℝ × ℝ}

/-- **The exchange `w ↦ 1 - w` preserves the Floer equation.** Let `σ'(z) = (1, 0) - z` be the
exchange in the real coordinates `ℝ × ℝ ≃ ℂ`, and let data `P` and `P'` on `ℂ` satisfy
`P' w = -P (1 - w)`, so that `P'` is the pullback of `P` along `σ'`
(`TauCeti.Floer.perturbationPullback_one_sub`). If `P` is differentiable in the target point and
`u` solves the Floer equation for `P` at `σ'(z)` for an almost complex structure `J`, then
`u ∘ σ'` solves the Floer equation for `P'` at `z`. -/
theorem isComplexLinearMap_perturbedMFDeriv_comp_one_sub (ω : SmoothTwoForm I M)
    {P P' : ℂ → M → ℂ →L[ℝ] ℝ} (hP : ∀ w x, P' w x = -P (1 - w) x)
    {J : AlmostComplexStructure (TangentSpace I (u ((1, 0) - w)))}
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u ((1, 0) - w))
    (hK : ∀ v, MDifferentiableAt I 𝓘(ℝ)
      (fun x ↦ P (Complex.equivRealProdCLM.symm ((1, 0) - w)) x v) (u ((1, 0) - w)))
    (h : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv (fun z x ↦ P (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ P (Complex.equivRealProdCLM.symm z) x Complex.I) u ((1, 0) - w)).toLinearMap) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv (fun z x ↦ P' (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ P' (Complex.equivRealProdCLM.symm z) x Complex.I)
        (u ∘ fun z ↦ (1, 0) - z) w).toLinearMap := by
  set e := Complex.equivRealProdCLM.symm
  set Ks : ℝ × ℝ → M → ℝ := fun z x ↦ P (e z) x 1
  set Kt : ℝ × ℝ → M → ℝ := fun z x ↦ P (e z) x Complex.I
  -- The datum `P'` is the pullback of `P` along `σ'`.
  have hpull (v : ℝ × ℝ) :
      (fun z x ↦ P' (e z) x (e v)) = perturbationPullback (fun z ↦ (1, 0) - z) Ks Kt v := by
    funext z x
    rw [perturbationPullback_one_sub, hP, neg_apply]
  have hD : ω.perturbedMFDeriv (fun z x ↦ P' (e z) x 1) (fun z x ↦ P' (e z) x Complex.I)
      (u ∘ fun z ↦ (1, 0) - z) w =
      ω.perturbedMFDeriv (perturbationPullback (fun z ↦ (1, 0) - z) Ks Kt stdComplexLineReal)
        (perturbationPullback (fun z ↦ (1, 0) - z) Ks Kt stdComplexLineImag)
        (u ∘ fun z ↦ (1, 0) - z) w := by
    conv_lhs => rw [← equivRealProdCLM_symm_stdComplexLineReal,
      ← equivRealProdCLM_symm_stdComplexLineImag, hpull, hpull]
  rw [hD]
  -- The exchange is holomorphic: its derivative is `-1`.
  have hφJ : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ)
      (fderiv ℝ (fun z : ℝ × ℝ ↦ (1, 0) - z) w : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) := by
    rw [fderiv_const_sub, fderiv_fun_id]
    simp
  exact ω.isComplexLinearMap_perturbedMFDeriv_perturbationPullback
    ((differentiableAt_const _).sub differentiableAt_id) hu (hK 1) (hK Complex.I) hφJ h

end TauCeti.SmoothTwoForm
