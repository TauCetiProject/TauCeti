/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.MeanZero
public import TauCeti.Geometry.Manifold.DifferentialOperator.LaplaceType.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
import TauCeti.Geometry.Manifold.Riemannian.Harmonic
import TauCeti.Geometry.Manifold.Riemannian.Poisson.Basic
import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Regularity

/-!
# Smooth solutions of the Poisson equation on a closed manifold

Let `M` be a closed connected smooth Riemannian manifold without boundary, with Riemannian volume
`dV` and nonnegative Laplacian `Δ⁺ = -div grad`. Combining the weak Poisson solver
(`TauCeti.Manifold.SobolevH1.existsUnique_dirichletForm_eq`) with linear elliptic regularity
(`SobolevH1.exists_eq_ofSmooth_and_neg_laplaceBeltrami_add_mul_eq_of_dirichletForm_add_eq`),
every smooth function `f` with `∫ f dV = 0` has a smooth solution `u` with `∫ u dV = 0` and
`Δ⁺u = f`. Classical uniqueness for `C²` functions under a `C¹` metric
(`TauCeti.Manifold.eq_of_laplaceBeltrami_eq_of_integral_eq`) then yields unique smooth solvability
(`TauCeti.Manifold.existsUnique_contMDiff_integral_eq_zero_and_neg_laplaceBeltrami_eq`). For a
smooth `1`-form `a` on a closed connected oriented Riemannian manifold of positive dimension, this
solves the scalar equation `Δ⁺f = d*a` of the global Coulomb gauge `d*(a - df) = 0`
(`TauCeti.SmoothForm.existsUnique_codifferential_sub_mextDerivₗ_eq_zero`).

Restricting `-TauCeti.smoothLaplaceBeltrami I M` to
`meanZeroSmoothFunctions I M (riemannianVolume I M) ∞` and using `LinearEquiv.ofBijective` gives
the linear automorphism `TauCeti.Manifold.negLaplaceBeltramiEquiv`, whose inverse is the smooth
Poisson solution operator.

## Main definitions

* `TauCeti.Manifold.negLaplaceBeltramiEquiv`: the nonnegative Laplacian `u ↦ Δ⁺u` as a linear
  equivalence on `meanZeroSmoothFunctions I M (riemannianVolume I M) ∞`.

## Main results

* `TauCeti.Manifold.smoothLaplaceBeltrami_mem_meanZeroSmoothFunctions`: the Laplace–Beltrami
  operator sends every smooth function on a closed manifold into
  `meanZeroSmoothFunctions I M (riemannianVolume I M) ∞`.
* `TauCeti.Manifold.exists_neg_laplaceBeltrami_eq`: smooth solvability of `Δ⁺u = f` with
  `∫ u dV = 0` on a closed connected smooth manifold.
* `TauCeti.Manifold.coe_negLaplaceBeltramiEquiv_apply`: bundled projection of
  `negLaplaceBeltramiEquiv`.
* `TauCeti.Manifold.neg_laplaceBeltrami_negLaplaceBeltramiEquiv_symm`: the inverse of
  `negLaplaceBeltramiEquiv` solves `Δ⁺u = f`.
* `TauCeti.Manifold.eq_negLaplaceBeltramiEquiv_symm_iff`: pointwise characterization of the
  inverse of `negLaplaceBeltramiEquiv`.
* `TauCeti.Manifold.existsUnique_contMDiff_integral_eq_zero_and_neg_laplaceBeltrami_eq`: smooth
  solvability and uniqueness of `∫ u dV = 0` and `Δ⁺u = f` on a closed connected smooth manifold.
-/

public section

open Bundle MeasureTheory
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] [T2Space M]
  [PreconnectedSpace M] [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

local instance instIsContinuousRiemannianBundlePoisson :
    IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)

omit [PreconnectedSpace M] in
/-- The Laplace–Beltrami operator sends every smooth function on a closed manifold into the
mean-zero submodule `meanZeroSmoothFunctions I M (riemannianVolume I M) ∞`. -/
theorem smoothLaplaceBeltrami_mem_meanZeroSmoothFunctions (u : C^∞⟮I, M; ℝ⟯) :
    smoothLaplaceBeltrami I M u ∈ meanZeroSmoothFunctions I M (riemannianVolume I M) ∞ := by
  let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  rw [mem_meanZeroSmoothFunctions_iff]
  simpa only [smoothLaplaceBeltrami_apply] using
    integral_laplaceBeltrami_eq_zero (u.contMDiff.of_le (by simp))
      (HasCompactSupport.of_compactSpace _)

/-- Two smooth functions on a closed connected smooth Riemannian manifold with the same
nonnegative Laplacian `-Δ` and zero Riemannian integral coincide. -/
private theorem eq_of_neg_laplaceBeltrami_eq_of_integral_eq_zero {u v : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ) ∞ u) (hv : ContMDiff I 𝓘(ℝ) ∞ v)
    (hΔ : ∀ x, -laplaceBeltrami I u x = -laplaceBeltrami I v x)
    (hu0 : ∫ x, u x ∂riemannianVolume I M = 0)
    (hv0 : ∫ x, v x ∂riemannianVolume I M = 0) :
    u = v := by
  let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (by simp)
  exact eq_of_laplaceBeltrami_eq_of_integral_eq (hu.of_le (by simp)) (hv.of_le (by simp))
    (fun x ↦ neg_inj.1 (hΔ x)) (hu0.trans hv0.symm)

/-- **Existence for the smooth Poisson equation on a closed manifold.** On a closed connected
smooth Riemannian manifold of any dimension, every smooth function `f` of integral zero is `Δ⁺u`
for a smooth function `u` of integral zero, where `Δ⁺ = -div grad` is the nonnegative Laplacian. -/
theorem exists_neg_laplaceBeltrami_eq {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf0 : ∫ x, f x ∂riemannianVolume I M = 0) :
    ∃ u : C^∞⟮I, M; ℝ⟯, ∫ x, u x ∂riemannianVolume I M = 0 ∧
      ∀ x, -laplaceBeltrami I u x = f x := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  have hf2 : MemLp f 2 (riemannianVolume I M) :=
    hf.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  obtain ⟨w, hw₀, hw⟩ := (SobolevH1.existsUnique_dirichletForm_eq (hf2.toLp f)
    ((integral_congr_ae hf2.coeFn_toLp).trans hf0)).exists
  obtain ⟨u, rfl, hu⟩ :=
    SobolevH1.exists_eq_ofSmooth_and_neg_laplaceBeltrami_add_mul_eq_of_dirichletForm_add_eq
      (V := 0) contMDiff_const hf (w := w) fun φ ↦ by
        rw [hw, integral_congr_ae ((hf2.coeFn_toLp.mul (SobolevH1.toLp_ofSmooth_ae_eq φ)).mono
          fun x hx ↦ by simpa only [Pi.mul_apply] using hx)]
        simp
  exact ⟨u, (integral_congr_ae (SobolevH1.toLp_ofSmooth_ae_eq u)).symm.trans hw₀,
    fun x ↦ by simpa using hu x⟩

variable (I M) in
/-- The nonnegative Laplacian `-smoothLaplaceBeltrami I M` restricted to mean-zero smooth
functions. -/
private def negLaplaceBeltramiMeanZero :
    meanZeroSmoothFunctions I M (riemannianVolume I M) ∞ →ₗ[ℝ]
      meanZeroSmoothFunctions I M (riemannianVolume I M) ∞ :=
  -((smoothLaplaceBeltrami I M).restrict fun u _ ↦
    smoothLaplaceBeltrami_mem_meanZeroSmoothFunctions u)

omit [PreconnectedSpace M] in
private theorem coe_negLaplaceBeltramiMeanZero_apply
    (u : meanZeroSmoothFunctions I M (riemannianVolume I M) ∞) :
    (negLaplaceBeltramiMeanZero I M u).val = -(smoothLaplaceBeltrami I M u.val) :=
  rfl

omit [PreconnectedSpace M] in
private theorem negLaplaceBeltramiMeanZero_apply
    (u : meanZeroSmoothFunctions I M (riemannianVolume I M) ∞) (x : M) :
    (negLaplaceBeltramiMeanZero I M u).val x = -laplaceBeltrami I u.val x := by
  simp [coe_negLaplaceBeltramiMeanZero_apply]

private theorem negLaplaceBeltrami_injective :
    Function.Injective (negLaplaceBeltramiMeanZero I M) := by
  intro u₁ u₂ hu
  refine Subtype.ext (ContMDiffMap.ext (congrFun
    (eq_of_neg_laplaceBeltrami_eq_of_integral_eq_zero
      u₁.val.contMDiff u₂.val.contMDiff (fun x ↦ ?_)
      (integral_coe_meanZeroSmoothFunctions_eq_zero u₁)
      (integral_coe_meanZeroSmoothFunctions_eq_zero u₂))))
  simpa only [negLaplaceBeltramiMeanZero_apply] using congrArg (fun g ↦ g.val x) hu

private theorem negLaplaceBeltrami_surjective :
    Function.Surjective (negLaplaceBeltramiMeanZero I M) := by
  intro f
  obtain ⟨u, hu0, hu⟩ := exists_neg_laplaceBeltrami_eq f.val.contMDiff
    (integral_coe_meanZeroSmoothFunctions_eq_zero f)
  refine ⟨⟨u, mem_meanZeroSmoothFunctions_iff.2 hu0⟩, Subtype.ext (ContMDiffMap.ext fun x ↦ ?_)⟩
  simpa only [negLaplaceBeltramiMeanZero_apply] using hu x

variable (I M) in
/-- **The nonnegative Laplacian as a linear equivalence on mean-zero smooth functions.** On a
closed connected smooth Riemannian manifold, `u ↦ Δ⁺u` is a linear automorphism of the submodule
`meanZeroSmoothFunctions I M (riemannianVolume I M) ∞`, whose inverse solves the smooth Poisson
equation. -/
def negLaplaceBeltramiEquiv :
    meanZeroSmoothFunctions I M (riemannianVolume I M) ∞ ≃ₗ[ℝ]
      meanZeroSmoothFunctions I M (riemannianVolume I M) ∞ :=
  LinearEquiv.ofBijective (negLaplaceBeltramiMeanZero I M)
    ⟨negLaplaceBeltrami_injective, negLaplaceBeltrami_surjective⟩

/-- Applying `negLaplaceBeltramiEquiv` as a bundled smooth function gives
`-(smoothLaplaceBeltrami I M u.val)`. -/
@[simp]
theorem coe_negLaplaceBeltramiEquiv_apply
    (u : meanZeroSmoothFunctions I M (riemannianVolume I M) ∞) :
    (negLaplaceBeltramiEquiv I M u).val = -(smoothLaplaceBeltrami I M u.val) :=
  coe_negLaplaceBeltramiMeanZero_apply u

/-- A mean-zero smooth function `u` equals `(negLaplaceBeltramiEquiv I M).symm f` if and only if
it solves `-laplaceBeltrami I u x = f x` pointwise. -/
theorem eq_negLaplaceBeltramiEquiv_symm_iff
    {u f : meanZeroSmoothFunctions I M (riemannianVolume I M) ∞} :
    u = (negLaplaceBeltramiEquiv I M).symm f ↔
      ∀ x, -laplaceBeltrami I u.val x = f.val x := by
  rw [LinearEquiv.eq_symm_apply, Subtype.ext_iff, ContMDiffMap.ext_iff]
  simp

/-- The inverse of `negLaplaceBeltramiEquiv` solves the smooth Poisson equation
`-laplaceBeltrami I u x = f x` pointwise. -/
@[simp]
theorem neg_laplaceBeltrami_negLaplaceBeltramiEquiv_symm
    (f : meanZeroSmoothFunctions I M (riemannianVolume I M) ∞) (x : M) :
    -laplaceBeltrami I ((negLaplaceBeltramiEquiv I M).symm f).val x = f.val x :=
  eq_negLaplaceBeltramiEquiv_symm_iff.1 rfl x

/-- **The smooth Poisson equation on a closed manifold.** On a closed connected smooth Riemannian
manifold of any dimension, for every smooth function `f` with `∫ f dV = 0`, there is a unique
smooth function `u` with `∫ u dV = 0` and `Δ⁺u = f`, where `Δ⁺ = -div grad` is the nonnegative
Laplacian. -/
theorem existsUnique_contMDiff_integral_eq_zero_and_neg_laplaceBeltrami_eq
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf0 : ∫ x, f x ∂riemannianVolume I M = 0) :
    ∃! u : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ u ∧
      ∫ x, u x ∂riemannianVolume I M = 0 ∧ ∀ x, -laplaceBeltrami I u x = f x := by
  let f₁ := meanZeroSmoothFunctions.mk hf hf0
  let u := (negLaplaceBeltramiEquiv I M).symm f₁
  have hu : ∀ x, -laplaceBeltrami I u.val x = f x := fun x ↦
    (neg_laplaceBeltrami_negLaplaceBeltramiEquiv_symm f₁ x).trans
      (congrFun (meanZeroSmoothFunctions.coe_mk hf hf0) x)
  refine ⟨u.val, ⟨u.val.contMDiff, integral_coe_meanZeroSmoothFunctions_eq_zero u, hu⟩,
    fun u' ⟨hu'_smooth, hu'0, hu'eq⟩ ↦ ?_⟩
  exact eq_of_neg_laplaceBeltrami_eq_of_integral_eq_zero hu'_smooth u.val.contMDiff
    (fun x ↦ (hu'eq x).trans (hu x).symm) hu'0
    (integral_coe_meanZeroSmoothFunctions_eq_zero u)

end TauCeti.Manifold
