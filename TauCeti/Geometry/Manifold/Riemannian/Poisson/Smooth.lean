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
smooth `1`-form `a` on a closed four-manifold, this is the scalar equation `Δ⁺ξ = d*a / 2` of the
global Coulomb gauge `d*(a - 2 dξ) = 0`.

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
* `TauCeti.Manifold.existsUnique_contMDiff_integral_eq_zero_and_neg_laplaceBeltrami_eq`: smooth
  solvability and uniqueness of `∫ u dV = 0` and `Δ⁺u = f` on a closed connected smooth manifold.
* `TauCeti.Manifold.coe_negLaplaceBeltramiEquiv_apply`: bundled projection of
  `negLaplaceBeltramiEquiv`.
* `TauCeti.Manifold.negLaplaceBeltramiEquiv_apply`: forward evaluation of
  `negLaplaceBeltramiEquiv`.
* `TauCeti.Manifold.neg_laplaceBeltrami_negLaplaceBeltramiEquiv_symm`: the inverse of
  `negLaplaceBeltramiEquiv` solves `Δ⁺u = f`.
* `TauCeti.Manifold.eq_negLaplaceBeltramiEquiv_symm_iff`: pointwise characterization of the
  inverse of `negLaplaceBeltramiEquiv`.
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

omit [PreconnectedSpace M] in
variable (I M) in
/-- The nonnegative Laplacian `-smoothLaplaceBeltrami I M` restricted to mean-zero smooth
functions. -/
private def negLaplaceBeltramiMeanZero :
    meanZeroSmoothFunctions I M (riemannianVolume I M) ∞ →ₗ[ℝ]
      meanZeroSmoothFunctions I M (riemannianVolume I M) ∞ :=
  -((smoothLaplaceBeltrami I M).restrict fun u _ ↦
    smoothLaplaceBeltrami_mem_meanZeroSmoothFunctions u)

omit [PreconnectedSpace M] in
private theorem negLaplaceBeltramiMeanZero_apply
    (u : meanZeroSmoothFunctions I M (riemannianVolume I M) ∞) (x : M) :
    (negLaplaceBeltramiMeanZero I M u).val x = -laplaceBeltrami I u.val x := by
  simp only [negLaplaceBeltramiMeanZero, LinearMap.neg_apply, Submodule.coe_neg,
    LinearMap.restrict_apply, ContMDiffMap.coe_neg, Pi.neg_apply, smoothLaplaceBeltrami_apply]

/-- Bundled smooth existence and uniqueness for the Poisson equation `Δ⁺u = f` on a closed
connected manifold, obtained by regularizing the weak `H¹` solution and applying classical `C²`
uniqueness. -/
private theorem existsUnique_negLaplaceBeltramiMeanZero_eq
    (f : meanZeroSmoothFunctions I M (riemannianVolume I M) ∞) :
    ∃! u : meanZeroSmoothFunctions I M (riemannianVolume I M) ∞,
      negLaplaceBeltramiMeanZero I M u = f := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  have hf2 : MemLp f.val 2 (riemannianVolume I M) :=
    f.val.contMDiff.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  obtain ⟨w, hw₀, hw⟩ := (SobolevH1.existsUnique_dirichletForm_eq (hf2.toLp f.val)
    ((integral_congr_ae hf2.coeFn_toLp).trans
      (integral_coe_meanZeroSmoothFunctions_eq_zero f))).exists
  obtain ⟨u, rfl, hu⟩ :=
    SobolevH1.exists_eq_ofSmooth_and_neg_laplaceBeltrami_add_mul_eq_of_dirichletForm_add_eq (V := 0)
      contMDiff_const f.val.contMDiff (w := w) fun φ ↦ by
        rw [hw, integral_congr_ae ((hf2.coeFn_toLp.mul (SobolevH1.toLp_ofSmooth_ae_eq φ)).mono
          fun x hx ↦ by simpa only [Pi.mul_apply] using hx)]
        simp
  have hu0 : u ∈ meanZeroSmoothFunctions I M (riemannianVolume I M) ∞ :=
    mem_meanZeroSmoothFunctions_iff.2
      ((integral_congr_ae (SobolevH1.toLp_ofSmooth_ae_eq u)).symm.trans hw₀)
  refine ⟨⟨u, hu0⟩, Subtype.ext (ContMDiffMap.ext fun x ↦ ?_), fun u' hu' ↦ ?_⟩
  · rw [negLaplaceBeltramiMeanZero_apply]
    simpa using hu x
  · refine Subtype.ext (ContMDiffMap.ext (congrFun (eq_of_laplaceBeltrami_eq_of_integral_eq
      (u'.val.contMDiff.of_le (by simp)) (u.contMDiff.of_le (by simp)) (fun x ↦ ?_) ?_)))
    · have h₁ : -laplaceBeltrami I u'.val x = f.val x := by
        rw [← negLaplaceBeltramiMeanZero_apply, hu']
      have h₂ : -laplaceBeltrami I u x = f.val x := by simpa using hu x
      exact neg_inj.1 (h₁.trans h₂.symm)
    · exact (integral_coe_meanZeroSmoothFunctions_eq_zero u').trans
        (mem_meanZeroSmoothFunctions_iff.1 hu0).symm

variable (I M) in
/-- **The nonnegative Laplacian as a linear equivalence on mean-zero smooth functions.** On a
closed connected smooth Riemannian manifold, `u ↦ Δ⁺u` is a linear automorphism of the submodule
`meanZeroSmoothFunctions I M (riemannianVolume I M) ∞`, whose inverse solves the smooth Poisson
equation. -/
def negLaplaceBeltramiEquiv :
    meanZeroSmoothFunctions I M (riemannianVolume I M) ∞ ≃ₗ[ℝ]
      meanZeroSmoothFunctions I M (riemannianVolume I M) ∞ :=
  LinearEquiv.ofBijective (negLaplaceBeltramiMeanZero I M)
    ((Function.bijective_iff_existsUnique _).2 existsUnique_negLaplaceBeltramiMeanZero_eq)

/-- **The smooth Poisson equation on a closed manifold.** On a closed connected smooth Riemannian
manifold of any dimension, for every smooth function `f` with `∫ f dV = 0`, there is a unique
smooth function `u` with `∫ u dV = 0` and `Δ⁺u = f`, where `Δ⁺ = -div grad` is the nonnegative
Laplacian. -/
theorem existsUnique_contMDiff_integral_eq_zero_and_neg_laplaceBeltrami_eq
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf0 : ∫ x, f x ∂riemannianVolume I M = 0) :
    ∃! u : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ u ∧
      ∫ x, u x ∂riemannianVolume I M = 0 ∧ ∀ x, -laplaceBeltrami I u x = f x := by
  let f₀ : C^∞⟮I, M; ℝ⟯ := ⟨f, hf⟩
  have hf₀_coe : ⇑f₀ = f := ContMDiffMap.coeFn_mk f hf
  let f₁ : meanZeroSmoothFunctions I M (riemannianVolume I M) ∞ :=
    ⟨f₀, mem_meanZeroSmoothFunctions_iff.2 (by simpa only [hf₀_coe] using hf0)⟩
  obtain ⟨u, hu, huniq⟩ := existsUnique_negLaplaceBeltramiMeanZero_eq f₁
  refine ⟨u.val, ⟨u.val.contMDiff, integral_coe_meanZeroSmoothFunctions_eq_zero u, fun x ↦ ?_⟩,
    fun u' ⟨hu'_smooth, hu'0, hu'eq⟩ ↦ ?_⟩
  · have h := congrFun (congrArg (fun g ↦ (g.val : M → ℝ)) hu) x
    simpa only [negLaplaceBeltramiMeanZero_apply, f₁, Subtype.coe_mk, hf₀_coe] using h
  · let u'₀ : C^∞⟮I, M; ℝ⟯ := ⟨u', hu'_smooth⟩
    have hu'₀_coe : ⇑u'₀ = u' := ContMDiffMap.coeFn_mk u' hu'_smooth
    let u'₁ : meanZeroSmoothFunctions I M (riemannianVolume I M) ∞ :=
      ⟨u'₀, mem_meanZeroSmoothFunctions_iff.2 (by simpa only [hu'₀_coe] using hu'0)⟩
    have hu'₁_eq : negLaplaceBeltramiMeanZero I M u'₁ = f₁ := by
      refine Subtype.ext (ContMDiffMap.ext fun x ↦ ?_)
      rw [negLaplaceBeltramiMeanZero_apply]
      simpa only [u'₁, f₁, Subtype.coe_mk, hu'₀_coe, hf₀_coe] using hu'eq x
    have h := congrArg (fun g : meanZeroSmoothFunctions I M (riemannianVolume I M) ∞ ↦
      (g.val : M → ℝ)) (huniq u'₁ hu'₁_eq)
    simpa only [u'₁, Subtype.coe_mk, hu'₀_coe] using h

/-- Applying `negLaplaceBeltramiEquiv` as a bundled smooth function gives
`-(smoothLaplaceBeltrami I M u.val)`. -/
@[simp]
theorem coe_negLaplaceBeltramiEquiv_apply
    (u : meanZeroSmoothFunctions I M (riemannianVolume I M) ∞) :
    (negLaplaceBeltramiEquiv I M u).val = -(smoothLaplaceBeltrami I M u.val) := by
  rw [negLaplaceBeltramiEquiv, LinearEquiv.ofBijective_apply]
  rfl

/-- Applying `negLaplaceBeltramiEquiv` evaluates the nonnegative Laplacian `-laplaceBeltrami`. -/
theorem negLaplaceBeltramiEquiv_apply
    (u : meanZeroSmoothFunctions I M (riemannianVolume I M) ∞) (x : M) :
    (negLaplaceBeltramiEquiv I M u).val x = -laplaceBeltrami I u.val x := by
  simp

/-- The inverse of `negLaplaceBeltramiEquiv` solves the smooth Poisson equation
`-laplaceBeltrami I u x = f x` pointwise. -/
@[simp]
theorem neg_laplaceBeltrami_negLaplaceBeltramiEquiv_symm
    (f : meanZeroSmoothFunctions I M (riemannianVolume I M) ∞) (x : M) :
    -laplaceBeltrami I ((negLaplaceBeltramiEquiv I M).symm f).val x = f.val x := by
  have h := congrArg (fun g ↦ g.val x) ((negLaplaceBeltramiEquiv I M).apply_symm_apply f)
  simpa only [negLaplaceBeltramiEquiv_apply] using h

/-- A mean-zero smooth function `u` equals `(negLaplaceBeltramiEquiv I M).symm f` if and only if
it solves `-laplaceBeltrami I u x = f x` pointwise. -/
theorem eq_negLaplaceBeltramiEquiv_symm_iff
    {u f : meanZeroSmoothFunctions I M (riemannianVolume I M) ∞} :
    u = (negLaplaceBeltramiEquiv I M).symm f ↔
      ∀ x, -laplaceBeltrami I u.val x = f.val x := by
  rw [LinearEquiv.eq_symm_apply]
  refine ⟨fun h x ↦ ?_, fun h ↦ Subtype.ext (ContMDiffMap.ext fun x ↦ ?_)⟩
  · rw [← negLaplaceBeltramiEquiv_apply, h]
  · rw [negLaplaceBeltramiEquiv_apply, h x]

end TauCeti.Manifold
