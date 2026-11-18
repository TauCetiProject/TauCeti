/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.MaximumPrinciple

/-!
# Hessians at upper contact

The scalar Hessian is linear at a point where the functions are twice continuously
differentiable. On a boundaryless Riemannian manifold, a function that touches another function
from above has larger diagonal Hessian and larger Laplace–Beltrami operator at the contact point.
Only pointwise `C²` regularity of the functions and a `C¹` metric are required.
-/

public noncomputable section

open Bundle Filter
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {f g : M → ℝ} {x : M}

/-- The Hessian is additive at a point where both functions are `C²`. -/
theorem hessian_add_of_contMDiffAt (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hg : ContMDiffAt I 𝓘(ℝ) 2 g x) (v w : TangentSpace I x) :
    hessian I (f + g) x v w = hessian I f x v w + hessian I g x v w := by
  let _ : IsManifold I ((1 : ℕ∞ω) + 1) M := by
    simpa only [one_add_one_eq_two] using (inferInstance : IsManifold I 2 M)
  have hgrad {u : M → ℝ} (hu : ContMDiffAt I 𝓘(ℝ) 2 u x) :
      MDifferentiableAt I I.tangent (fun y ↦ (⟨y, mgradient I u y⟩ : TangentBundle I M)) x :=
    (contMDiffAt_mgradient (I := I) (n := 1)
      (by simpa only [one_add_one_eq_two] using hu)).mdifferentiableAt (by simp)
  have hev : ∀ᶠ y in 𝓝 x, mgradient I (f + g) y = (mgradient I f + mgradient I g) y := by
    filter_upwards [(contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hf,
      (contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hg] with y hfy hgy
    apply ext_inner_right ℝ
    intro z
    rw [Pi.add_apply, inner_add_left, inner_mgradient, inner_mgradient, inner_mgradient,
      mvfderiv_add (hfy.mdifferentiableAt (by simp)) (hgy.mdifferentiableAt (by simp))]
    rfl
  have hcov := (CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOnUniv
  rw [hessian_def, hcov.congr_of_eventuallyEq (hgrad (hf.add hg))
    (mdifferentiableAt_add_section (hgrad hf) (hgrad hg)) Filter.univ_mem hev,
    hcov.add (hgrad hf) (hgrad hg), add_apply, inner_add_left,
    ← hessian_def, ← hessian_def]

/-- The Hessian commutes with constant scalar multiplication at a point of `C²` regularity. -/
theorem hessian_smul_of_contMDiffAt (c : ℝ) (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (v w : TangentSpace I x) :
    hessian I (c • f) x v w = c * hessian I f x v w := by
  let _ : IsManifold I ((1 : ℕ∞ω) + 1) M := by
    simpa only [one_add_one_eq_two] using (inferInstance : IsManifold I 2 M)
  have hgrad := (contMDiffAt_mgradient (I := I) (n := 1)
    (by simpa only [one_add_one_eq_two] using hf)).mdifferentiableAt (by simp)
  simp only [hessian_def, mgradient_smul,
    (CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOnUniv.smul_const c hgrad,
    smul_apply, real_inner_smul_left]

/-- Negating a function negates its Hessian at a point of `C²` regularity. -/
theorem hessian_neg_of_contMDiffAt (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (v w : TangentSpace I x) :
    hessian I (-f) x v w = -hessian I f x v w := by
  simpa only [neg_one_smul, neg_one_mul] using hessian_smul_of_contMDiffAt (-1) hf v w

/-- The Hessian respects subtraction at a point where both functions are `C²`. -/
theorem hessian_sub_of_contMDiffAt (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hg : ContMDiffAt I 𝓘(ℝ) 2 g x) (v w : TangentSpace I x) :
    hessian I (f - g) x v w = hessian I f x v w - hessian I g x v w := by
  rw [sub_eq_add_neg, hessian_add_of_contMDiffAt (g := -g) hf hg.neg,
    hessian_neg_of_contMDiffAt hg, sub_eq_add_neg]

variable [I.Boundaryless]

/-- If `g` touches `f` from above, its diagonal Hessian at the contact point is larger. -/
theorem hessian_self_le_of_eventuallyLE_of_eq (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hg : ContMDiffAt I 𝓘(ℝ) 2 g x) (hle : ∀ᶠ y in 𝓝 x, f y ≤ g y)
    (heq : f x = g x) (v : TangentSpace I x) : hessian I f x v v ≤ hessian I g x v v := by
  have hmin : IsLocalMin (g - f) x := by
    filter_upwards [hle] with y hy
    simpa only [Pi.sub_apply, ← heq, sub_self] using sub_nonneg.mpr hy
  have hh : 0 ≤ hessian I (g - f) x v v :=
    hessian_self_nonneg_of_isLocalMin (hg.sub hf) hmin v
  rw [hessian_sub_of_contMDiffAt (f := g) (g := f) hg hf] at hh
  exact sub_nonneg.mp hh

/-- If `g` touches `f` from above, its Laplace–Beltrami operator is larger at contact. -/
theorem laplaceBeltrami_le_of_eventuallyLE_of_eq (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    (hg : ContMDiffAt I 𝓘(ℝ) 2 g x) (hle : ∀ᶠ y in 𝓝 x, f y ≤ g y)
    (heq : f x = g x) : laplaceBeltrami I f x ≤ laplaceBeltrami I g x := by
  have hmax : IsLocalMax (f - g) x := by
    filter_upwards [hle] with y hy
    simpa only [Pi.sub_apply, heq, sub_self] using sub_nonpos.mpr hy
  have hsub : ContMDiffAt I 𝓘(ℝ) 2 (f - g) x := hf.sub hg
  have hadd := laplaceBeltrami_add_of_contMDiffAt I hsub hg
  rw [sub_add_cancel] at hadd
  have hΔ := laplaceBeltrami_nonpos_of_isLocalMax hsub hmax
  linarith

end TauCeti.Manifold
