/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.MeanZero
public import TauCeti.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
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

Restricting `-laplaceBeltramiLinearMap I M` to `meanZeroSmoothFunctions I M (riemannianVolume I M)`
and using `LinearEquiv.ofBijective` gives the linear automorphism
`TauCeti.Manifold.negLaplaceBeltramiEquiv`, whose inverse is the smooth Poisson solution operator.

## Main definitions

* `TauCeti.Manifold.negLaplaceBeltramiEquiv`: the nonnegative Laplacian `u ↦ Δ⁺u` as a linear
  equivalence on `meanZeroSmoothFunctions I M (riemannianVolume I M)`.

## Main results

* `TauCeti.Manifold.existsUnique_contMDiff_integral_eq_zero_and_neg_laplaceBeltrami_eq`: smooth
  solvability and uniqueness of `∫ u dV = 0` and `Δ⁺u = f` on a closed connected smooth manifold.
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

/-- Smooth existence for the Poisson equation `Δ⁺u = f` on a closed connected manifold, obtained by
regularizing the weak `H¹` solution. -/
private theorem exists_neg_laplaceBeltrami_eq {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf₀ : ∫ x, f x ∂riemannianVolume I M = 0) :
    ∃ u : C^∞⟮I, M; ℝ⟯, ∫ x, u x ∂riemannianVolume I M = 0 ∧
      ∀ x, -laplaceBeltrami I u x = f x := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  have hf2 : MemLp f 2 (riemannianVolume I M) :=
    hf.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  obtain ⟨w, hw₀, hw⟩ := (SobolevH1.existsUnique_dirichletForm_eq (hf2.toLp f)
    ((integral_congr_ae hf2.coeFn_toLp).trans hf₀)).exists
  obtain ⟨u, rfl, hu⟩ :=
    SobolevH1.exists_eq_ofSmooth_and_neg_laplaceBeltrami_add_mul_eq_of_dirichletForm_add_eq (V := 0)
      contMDiff_const hf (w := w) fun φ ↦ by
        rw [hw, integral_congr_ae ((hf2.coeFn_toLp.mul (SobolevH1.toLp_ofSmooth_ae_eq φ)).mono
          fun x hx ↦ by simpa only [Pi.mul_apply] using hx)]
        simp
  exact ⟨u, (integral_congr_ae (SobolevH1.toLp_ofSmooth_ae_eq u)).symm.trans hw₀,
    fun x ↦ by simpa using hu x⟩

/-- **The smooth Poisson equation on a closed manifold.** On a closed connected smooth Riemannian
manifold of any dimension, for every smooth function `f` with `∫ f dV = 0`, there is a unique
smooth function `u` with `∫ u dV = 0` and `Δ⁺u = f`, where `Δ⁺ = -div grad` is the nonnegative
Laplacian. -/
theorem existsUnique_contMDiff_integral_eq_zero_and_neg_laplaceBeltrami_eq
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf0 : ∫ x, f x ∂riemannianVolume I M = 0) :
    ∃! u : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ u ∧
      ∫ x, u x ∂riemannianVolume I M = 0 ∧ ∀ x, -laplaceBeltrami I u x = f x := by
  obtain ⟨u, hu0, hueq⟩ := exists_neg_laplaceBeltrami_eq hf hf0
  refine ⟨u, ⟨u.contMDiff, hu0, hueq⟩, fun u' ⟨hu'_smooth, hu'0, hu'eq⟩ ↦ ?_⟩
  exact eq_of_laplaceBeltrami_eq_of_integral_eq
    (hu'_smooth.of_le (by simp)) (u.contMDiff.of_le (by simp))
    (fun x ↦ neg_inj.1 ((hu'eq x).trans (hueq x).symm)) (hu'0.trans hu0.symm)

omit [PreconnectedSpace M] in
variable (I M) in
/-- The nonnegative Laplacian `-laplaceBeltramiLinearMap I M` restricted to mean-zero smooth
functions. -/
private def negLaplaceBeltramiMeanZero :
    meanZeroSmoothFunctions I M (riemannianVolume I M) →ₗ[ℝ]
      meanZeroSmoothFunctions I M (riemannianVolume I M) :=
  -((laplaceBeltramiLinearMap I M).restrict fun u _ ↦
    laplaceBeltramiLinearMap_mem_meanZeroSmoothFunctions u)

omit [PreconnectedSpace M] in
private theorem negLaplaceBeltramiMeanZero_apply
    (u : meanZeroSmoothFunctions I M (riemannianVolume I M)) (x : M) :
    (negLaplaceBeltramiMeanZero I M u).val x = -laplaceBeltrami I u.val x := by
  simp only [negLaplaceBeltramiMeanZero, LinearMap.neg_apply, Submodule.coe_neg,
    LinearMap.restrict_apply, ContMDiffMap.coe_neg, Pi.neg_apply, laplaceBeltramiLinearMap_apply]

variable (I M) in
/-- **The nonnegative Laplacian as a linear equivalence on mean-zero smooth functions.** On a
closed connected smooth Riemannian manifold, `u ↦ Δ⁺u` is a linear automorphism of the submodule
`meanZeroSmoothFunctions I M (riemannianVolume I M)`, whose inverse solves the smooth Poisson
equation. -/
def negLaplaceBeltramiEquiv :
    meanZeroSmoothFunctions I M (riemannianVolume I M) ≃ₗ[ℝ]
      meanZeroSmoothFunctions I M (riemannianVolume I M) :=
  LinearEquiv.ofBijective (negLaplaceBeltramiMeanZero I M)
    ((Function.bijective_iff_existsUnique _).2 fun f ↦ by
      obtain ⟨u, ⟨hu, hu0, hueq⟩, huniq⟩ :=
        existsUnique_contMDiff_integral_eq_zero_and_neg_laplaceBeltrami_eq
          f.val.contMDiff (mem_meanZeroSmoothFunctions_iff.1 f.property)
      let u₀ : C^∞⟮I, M; ℝ⟯ := ⟨u, hu⟩
      refine ⟨⟨u₀, mem_meanZeroSmoothFunctions_iff.2 hu0⟩, ?_, fun u' hu' ↦ ?_⟩
      · refine Subtype.ext (ContMDiffMap.ext fun x ↦ ?_)
        rw [negLaplaceBeltramiMeanZero_apply]
        exact hueq x
      · have hu'eq : ∀ x, -laplaceBeltrami I u'.val x = f.val x := fun x ↦ by
          rw [← negLaplaceBeltramiMeanZero_apply, hu']
        exact Subtype.ext (ContMDiffMap.ext (congrFun
          (huniq u'.val ⟨u'.val.contMDiff, mem_meanZeroSmoothFunctions_iff.1 u'.property,
            hu'eq⟩))))

/-- Applying `negLaplaceBeltramiEquiv` evaluates the nonnegative Laplacian `-laplaceBeltrami`. -/
@[simp]
theorem negLaplaceBeltramiEquiv_apply
    (u : meanZeroSmoothFunctions I M (riemannianVolume I M)) (x : M) :
    (negLaplaceBeltramiEquiv I M u).val x = -laplaceBeltrami I u.val x := by
  rw [negLaplaceBeltramiEquiv, LinearEquiv.ofBijective_apply, negLaplaceBeltramiMeanZero_apply]

/-- The inverse of `negLaplaceBeltramiEquiv` solves the smooth Poisson equation
`-laplaceBeltrami I u x = f x` pointwise. -/
@[simp]
theorem neg_laplaceBeltrami_negLaplaceBeltramiEquiv_symm
    (f : meanZeroSmoothFunctions I M (riemannianVolume I M)) (x : M) :
    -laplaceBeltrami I ((negLaplaceBeltramiEquiv I M).symm f).val x = f.val x := by
  have h := congrArg (fun g ↦ g.val x) ((negLaplaceBeltramiEquiv I M).apply_symm_apply f)
  simpa only [negLaplaceBeltramiEquiv_apply] using h

/-- A mean-zero smooth function `u` equals `(negLaplaceBeltramiEquiv I M).symm f` if and only if
it solves `-laplaceBeltrami I u x = f x` pointwise. -/
theorem eq_negLaplaceBeltramiEquiv_symm_iff
    {u f : meanZeroSmoothFunctions I M (riemannianVolume I M)} :
    u = (negLaplaceBeltramiEquiv I M).symm f ↔
      ∀ x, -laplaceBeltrami I u.val x = f.val x := by
  rw [LinearEquiv.eq_symm_apply]
  refine ⟨fun h x ↦ ?_, fun h ↦ Subtype.ext (ContMDiffMap.ext fun x ↦ ?_)⟩
  · rw [← negLaplaceBeltramiEquiv_apply, h]
  · rw [negLaplaceBeltramiEquiv_apply, h x]

end TauCeti.Manifold
