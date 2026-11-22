/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import TauCeti.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
import TauCeti.Geometry.Manifold.Riemannian.DivergenceTheorem
import TauCeti.Geometry.Manifold.Riemannian.Poisson.Basic
import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Regularity
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
import TauCeti.MeasureTheory.Integral.ContinuousMap

/-!
# Smooth solutions of the Poisson equation on a closed manifold

Let `M` be a closed connected smooth Riemannian manifold without boundary, with Riemannian volume
`dV` and nonnegative Laplacian `Δ⁺ = -div grad`. Combining the smooth Poisson existence theorem
(`TauCeti.Manifold.SobolevH1.exists_neg_laplaceBeltrami_eq`) with weak uniqueness from
`TauCeti.Manifold.SobolevH1.existsUnique_dirichletForm_eq`, for every smooth function `f` with
`∫ f dV = 0` there is a unique smooth function `u` with `∫ u dV = 0` and `Δ⁺u = f`
(`TauCeti.Manifold.existsUnique_contMDiff_integral_eq_zero_and_neg_laplaceBeltrami_eq`).

The smooth functions of vanishing Riemannian integral form the submodule
`TauCeti.Manifold.meanZeroSmoothFunctions`, and `Δ⁺` acts on it as a linear automorphism
`TauCeti.Manifold.negLaplaceBeltramiEquiv`, whose inverse is the smooth Poisson solution operator.

## Main definitions

* `TauCeti.Manifold.meanZeroSmoothFunctions`: the submodule of smooth functions on `M` with
  vanishing integral against `riemannianVolume I M`.
* `TauCeti.Manifold.negLaplaceBeltramiEquiv`: the nonnegative Laplacian `u ↦ Δ⁺u` as a linear
  equivalence `meanZeroSmoothFunctions I M ≃ₗ[ℝ] meanZeroSmoothFunctions I M`.

## Main results

* `TauCeti.Manifold.mem_meanZeroSmoothFunctions_iff`: membership characterization in
  `meanZeroSmoothFunctions I M`.
* `TauCeti.Manifold.existsUnique_contMDiff_integral_eq_zero_and_neg_laplaceBeltrami_eq`: smooth
  solvability and uniqueness of `∫ u dV = 0` and `Δ⁺u = f` on a closed connected smooth manifold.
* `TauCeti.Manifold.negLaplaceBeltramiEquiv_apply`: forward evaluation of
  `negLaplaceBeltramiEquiv`.
* `TauCeti.Manifold.neg_laplaceBeltrami_negLaplaceBeltramiEquiv_symm`: the inverse of
  `negLaplaceBeltramiEquiv` solves `Δ⁺u = f`.
-/

public section

open Bundle MeasureTheory
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

section MeanZero

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- The submodule of smooth functions on `M` with vanishing integral against the Riemannian
volume. -/
def meanZeroSmoothFunctions : Submodule ℝ C^∞⟮I, M; ℝ⟯ where
  carrier := {u | ∫ x, u x ∂riemannianVolume I M = 0}
  add_mem' {u v} hu hv := by
    have hu_int : Integrable u (riemannianVolume I M) :=
      (map_continuous u).integrable_of_compactSpace
    have hv_int : Integrable v (riemannianVolume I M) :=
      (map_continuous v).integrable_of_compactSpace
    simp only [Set.mem_ofPred_eq, ContMDiffMap.coe_add, Pi.add_apply]
    rw [integral_add hu_int hv_int, hu, hv, add_zero]
  zero_mem' := by simp
  smul_mem' c u hu := by
    simp only [Set.mem_ofPred_eq, ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul, hu, mul_zero]

variable {I M}

/-- A smooth function belongs to `meanZeroSmoothFunctions I M` exactly when its Riemannian
volume integral vanishes. -/
@[simp]
theorem mem_meanZeroSmoothFunctions_iff {u : C^∞⟮I, M; ℝ⟯} :
    u ∈ meanZeroSmoothFunctions I M ↔ ∫ x, u x ∂riemannianVolume I M = 0 :=
  Iff.rfl

end MeanZero

section SmoothPoisson

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

/-- **The smooth Poisson equation on a closed manifold.** On a closed connected smooth Riemannian
manifold of any dimension, for every smooth function `f` with `∫ f dV = 0`, there is a unique
smooth function `u` with `∫ u dV = 0` and `Δ⁺u = f`, where `Δ⁺ = -div grad` is the nonnegative
Laplacian. -/
theorem existsUnique_contMDiff_integral_eq_zero_and_neg_laplaceBeltrami_eq
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf0 : ∫ x, f x ∂riemannianVolume I M = 0) :
    ∃! u : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ u ∧
      ∫ x, u x ∂riemannianVolume I M = 0 ∧ ∀ x, -laplaceBeltrami I u x = f x := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  obtain ⟨u, hu0, hueq⟩ := SobolevH1.exists_neg_laplaceBeltrami_eq hf hf0
  refine ⟨u, ⟨u.contMDiff, hu0, hueq⟩, fun u' ⟨hu'_smooth, hu'0, hu'eq⟩ ↦ ?_⟩
  set F : Lp ℝ 2 (riemannianVolume I M) :=
    ContinuousMap.toLp 2 (riemannianVolume I M) ℝ ⟨f, hf.continuous⟩
  have hF_ae : (F : M → ℝ) =ᵐ[riemannianVolume I M] f :=
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (riemannianVolume I M) ⟨f, hf.continuous⟩
  have hF0 : ∫ x, F x ∂riemannianVolume I M = 0 := (integral_congr_ae hF_ae).trans hf0
  set u'm : C^∞⟮I, M; ℝ⟯ := ⟨u', hu'_smooth⟩
  have hsol (g : C^∞⟮I, M; ℝ⟯) (hg0 : ∫ x, g x ∂riemannianVolume I M = 0)
      (hgeq : ∀ x, -laplaceBeltrami I g x = f x) :
      ∫ x, SobolevH1.toLp (SobolevH1.ofSmooth g) x ∂riemannianVolume I M = 0 ∧
        ∀ v, SobolevH1.dirichletForm (SobolevH1.ofSmooth g) v =
          ∫ x, F x * SobolevH1.toLp v x ∂riemannianVolume I M := by
    refine ⟨(integral_congr_ae (SobolevH1.toLp_ofSmooth_ae_eq g)).trans hg0, fun v ↦ ?_⟩
    rw [SobolevH1.dirichletForm_comm, SobolevH1.dirichletForm_ofSmooth_right]
    refine integral_congr_ae ?_
    filter_upwards [hF_ae] with x hFx
    rw [hFx, ← hgeq x, mul_comm]
  have hofSmooth : SobolevH1.ofSmooth u'm = SobolevH1.ofSmooth u :=
    (SobolevH1.existsUnique_dirichletForm_eq F hF0).unique
      (hsol u'm hu'0 hu'eq) (hsol u hu0 hueq)
  have hae : u' =ᵐ[riemannianVolume I M] u :=
    (SobolevH1.toLp_ofSmooth_ae_eq u'm).symm.trans
      (hofSmooth ▸ SobolevH1.toLp_ofSmooth_ae_eq u)
  exact (hu'_smooth.continuous.ae_eq_iff_eq (riemannianVolume I M) (map_continuous u)).1 hae

omit [I.Boundaryless] [CompactSpace M] [T2Space M] [PreconnectedSpace M] [MeasurableSpace M]
  [BorelSpace M] in
private theorem contMDiff_neg_laplaceBeltrami (u : C^∞⟮I, M; ℝ⟯) :
    ContMDiff I 𝓘(ℝ) ∞ (fun x ↦ -laplaceBeltrami I u x) :=
  (contMDiff_laplaceBeltrami (n := ∞) (m := ∞) (k := ∞) (by simp) (by simp)
    u.contMDiff).neg

omit [PreconnectedSpace M] in
private theorem integral_neg_laplaceBeltrami_eq_zero (u : C^∞⟮I, M; ℝ⟯) :
    ∫ x, -laplaceBeltrami I u x ∂riemannianVolume I M = 0 := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  have h0 := integral_laplaceBeltrami_eq_zero (I := I)
    (u.contMDiff.of_le (by simp)) (HasCompactSupport.of_compactSpace _)
  rw [integral_neg, h0, neg_zero]

variable (I M) in
/-- **The nonnegative Laplacian as a linear equivalence on mean-zero smooth functions.** On a
closed connected smooth Riemannian manifold, `u ↦ Δ⁺u` is a linear automorphism of the submodule
`meanZeroSmoothFunctions I M`, whose inverse solves the smooth Poisson equation. -/
def negLaplaceBeltramiEquiv :
    haveI : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
    meanZeroSmoothFunctions I M ≃ₗ[ℝ] meanZeroSmoothFunctions I M :=
  letI : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  { toFun u :=
      ⟨⟨fun x ↦ -laplaceBeltrami I u.val x, contMDiff_neg_laplaceBeltrami u.val⟩,
        integral_neg_laplaceBeltrami_eq_zero u.val⟩
    invFun f :=
      let h :=
        existsUnique_contMDiff_integral_eq_zero_and_neg_laplaceBeltrami_eq
          f.val.contMDiff f.property
      ⟨⟨h.exists.choose, h.exists.choose_spec.1⟩, h.exists.choose_spec.2.1⟩
    map_add' u v := by
      ext x
      simp only [ContMDiffMap.coeFn_mk]
      change -(laplaceBeltrami I (u.val + v.val) x) =
        -laplaceBeltrami I u.val x + -laplaceBeltrami I v.val x
      rw [ContMDiffMap.coe_add,
        laplaceBeltrami_add I (u.val.contMDiff.of_le (by simp)) (v.val.contMDiff.of_le (by simp))]
      ring
    map_smul' c u := by
      ext x
      simp only [SetLike.val_smul, ContMDiffMap.coe_smul, RingHom.id_apply, ContMDiffMap.coeFn_mk]
      change -(laplaceBeltrami I (c • (u.val : M → ℝ)) x) = c * -laplaceBeltrami I u.val x
      rw [laplaceBeltrami_smul I c (u.val.contMDiff.of_le (by simp))]
      ring
    left_inv u := by
      have huniq := existsUnique_contMDiff_integral_eq_zero_and_neg_laplaceBeltrami_eq
        (contMDiff_neg_laplaceBeltrami u.val) (integral_neg_laplaceBeltrami_eq_zero u.val)
      have h1 := huniq.exists.choose_spec
      have h2 : ContMDiff I 𝓘(ℝ) ∞ u.val ∧
          ∫ x, u.val x ∂riemannianVolume I M = 0 ∧
            ∀ x, -laplaceBeltrami I u.val x = -laplaceBeltrami I u.val x :=
        ⟨u.val.contMDiff, u.property, fun _ ↦ rfl⟩
      exact Subtype.ext (ContMDiffMap.ext (congrFun (huniq.unique h1 h2)))
    right_inv f := by
      have h :=
        existsUnique_contMDiff_integral_eq_zero_and_neg_laplaceBeltrami_eq
          f.val.contMDiff f.property
      exact Subtype.ext (ContMDiffMap.ext h.exists.choose_spec.2.2) }

/-- Applying `negLaplaceBeltramiEquiv` evaluates the nonnegative Laplacian `-laplaceBeltrami`. -/
@[simp]
theorem negLaplaceBeltramiEquiv_apply
    (u : haveI : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
      meanZeroSmoothFunctions I M)
    (x : M) :
    ((negLaplaceBeltramiEquiv I M u).val x) = -laplaceBeltrami I u.val x := by
  rw [negLaplaceBeltramiEquiv]
  rfl

/-- The inverse of `negLaplaceBeltramiEquiv` solves the smooth Poisson equation
`-laplaceBeltrami I u x = f x` pointwise. -/
@[simp]
theorem neg_laplaceBeltrami_negLaplaceBeltramiEquiv_symm
    (f : haveI : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
      meanZeroSmoothFunctions I M)
    (x : M) :
    -laplaceBeltrami I ((negLaplaceBeltramiEquiv I M).symm f).val x = f.val x := by
  have h := congrArg (fun g ↦ g.val x) ((negLaplaceBeltramiEquiv I M).apply_symm_apply f)
  simpa only [negLaplaceBeltramiEquiv_apply] using h

end SmoothPoisson

end TauCeti.Manifold
