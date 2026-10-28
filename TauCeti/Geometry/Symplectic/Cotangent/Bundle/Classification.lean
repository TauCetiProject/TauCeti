/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.EulerField
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Lift
import TauCeti.Topology.FiberBundle.Separation

/-!
# Liouville-preserving diffeomorphisms of cotangent bundles are cotangent lifts

The cotangent lift `T*h : (x, p) ↦ (h x, p ∘ (dh_x)⁻¹)` of a smooth diffeomorphism `h : M → N`
pulls the Liouville form `λ_N` back to `λ_M` (`Diffeomorph.mpullback_cotangent_liouvilleForm`).
This file proves the converse: on Hausdorff manifolds without boundary, every smooth
diffeomorphism `ψ : T*M → T*N` with `ψ^* λ_N = λ_M` is the cotangent lift of a unique smooth
diffeomorphism `M → N` (`Diffeomorph.existsUnique_cotangent_eq_of_mpullback_liouvilleForm`).
Together with the naturality of `λ`, this characterizes cotangent lifts among diffeomorphisms
of cotangent bundles (`Diffeomorph.exists_cotangent_eq_iff_mpullback_liouvilleForm`).

The statement is about the full cotangent bundle, including the zero section. The argument has
two steps.

* **Fibres go to fibres.** A Liouville-preserving `ψ` commutes with the positive fibre
  dilations (`Diffeomorph.apply_mk_smul_of_mpullback_liouvilleForm`). Letting the dilation factor
  tend to `0` and using continuity of `ψ` at the zero section, `ψ` sends the zero covector over
  `x` to the zero covector over the base point of `ψ (x, p)`, for every covector `p` at `x`
  (`Diffeomorph.apply_mk_zero_of_mpullback_liouvilleForm`). So `ψ` covers the base map
  `f x = π (ψ (x, 0))`, and it maps the zero section onto the zero section. The same holds for
  `ψ⁻¹`, so `f` is a diffeomorphism.
* **The covector is determined.** Since `π_N ∘ ψ = f ∘ π_M`, the identity `ψ^* λ_N = λ_M`
  evaluated on a tangent vector of `T*M` over `v ∈ T_x M` reads `(ψ (x, p)) (df_x v) = p v`. Every
  `v` lifts, since the projection has surjective derivative (`Bundle.mfderiv_proj_surjective`).
  Hence `ψ (x, p) = (f x, p ∘ (df_x)⁻¹)`; in particular `ψ` is linear on fibres.

## Main results

* `Diffeomorph.apply_mk_zero_of_mpullback_liouvilleForm`: a Liouville-preserving diffeomorphism
  sends the zero covector over the base point of `z` to the zero covector over the base point of
  `ψ z`.
* `Diffeomorph.existsUnique_cotangent_eq_of_mpullback_liouvilleForm`: a Liouville-preserving
  diffeomorphism is the cotangent lift of a unique diffeomorphism of the bases.
* `Diffeomorph.exists_cotangent_eq_iff_mpullback_liouvilleForm`: a diffeomorphism of cotangent
  bundles is a cotangent lift exactly when it preserves the Liouville forms.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 2 (lifts of diffeomorphisms) and its exercises.
-/

public section

noncomputable section

open Bundle Filter Topology
open scoped Manifold ContDiff

namespace Diffeomorph

open TauCeti TauCeti.CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {F H' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ∞ N]

/-- A diffeomorphism `ψ` of cotangent bundles pulling `λ_N` back to `λ_M` and covering a
differentiable map `f` of the bases sends a covector `p` at `x` to a covector `q` at `f x` with
`q (df_x v) = p v` for every tangent vector `v` at `x`. -/
private theorem snd_apply_mfderiv_of_proj_apply_eq
    (ψ : CotangentBundle I M ≃ₘ⟮I.prod 𝓘(ℝ, E →L[ℝ] ℝ), J.prod 𝓘(ℝ, F →L[ℝ] ℝ)⟯
      CotangentBundle J N)
    (hψ : SmoothForm.mpullback ψ ψ.contMDiff (liouvilleForm J N) = liouvilleForm I M)
    {f : M → N} (hf : MDifferentiable I J f) (hproj : ∀ z, (ψ z).proj = f z.proj)
    (z : CotangentBundle I M) (v : TangentSpace I z.proj) :
    (ψ z).2 (mfderiv I J f z.proj v) = z.2 v := by
  obtain ⟨w, rfl⟩ := Bundle.mfderiv_proj_surjective (IB := I) z v
  have h := congrArg (fun α : SmoothForm _ _ ℝ 1 ↦ α.1 z fun _ ↦ w) hψ
  simp only [SmoothForm.mpullback_apply, liouvilleForm_apply] at h
  -- `ψ` covers `f`, so `dπ_N ∘ dψ = d(π_N ∘ ψ) = d(f ∘ π_M) = df ∘ dπ_M`.
  have hcomp : π (F →L[ℝ] ℝ) (fun y : N ↦ TangentSpace J y →L[ℝ] ℝ) ∘ ψ =
      f ∘ π (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) :=
    funext hproj
  have hN := mfderiv_comp_apply z
    ((contMDiff_proj (fun y : N ↦ TangentSpace J y →L[ℝ] ℝ) _).mdifferentiableAt one_ne_zero)
    (ψ.mdifferentiable (by simp) z) w
  have hM := mfderiv_comp_apply z (hf z.proj)
    ((contMDiff_proj (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) _).mdifferentiableAt one_ne_zero) w
  rw [hcomp, hM] at hN
  rw [hN]
  exact h

section Base

variable [T2Space N] [J.Boundaryless]

/-- **Liouville-preserving diffeomorphisms preserve the zero section and the fibres.** Let
`ψ : T*M → T*N` be a diffeomorphism pulling `λ_N` back to `λ_M`. For every covector `z`, `ψ` sends
the zero covector over the base point of `z` to the zero covector over the base point of `ψ z`.
In particular the base point of `ψ z` depends only on that of `z`. -/
theorem apply_mk_zero_of_mpullback_liouvilleForm
    (ψ : CotangentBundle I M ≃ₘ⟮I.prod 𝓘(ℝ, E →L[ℝ] ℝ), J.prod 𝓘(ℝ, F →L[ℝ] ℝ)⟯
      CotangentBundle J N)
    (hψ : SmoothForm.mpullback ψ ψ.contMDiff (liouvilleForm J N) = liouvilleForm I M)
    (z : CotangentBundle I M) :
    ψ ⟨z.proj, 0⟩ = ⟨(ψ z).proj, 0⟩ := by
  -- As `c → 0⁺`, `ψ (c • z)` tends to `ψ` of the zero covector by continuity, while it equals
  -- `c • ψ z`, which tends to the zero covector over the base point of `ψ z`.
  have hM : Tendsto (fun c : ℝ ↦ ψ ⟨z.proj, c • z.2⟩) (𝓝[>] 0) (𝓝 (ψ ⟨z.proj, 0⟩)) := by
    have hc : Continuous fun c : ℝ ↦ (⟨z.proj, c • z.2⟩ : CotangentBundle I M) :=
      (FiberBundle.continuous_totalSpaceMk _ _ z.proj).comp (continuous_id.smul continuous_const)
    have h := (ψ.continuous.comp hc).tendsto 0
    simp only [Function.comp_apply, zero_smul] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hN : Tendsto (fun c : ℝ ↦ ψ ⟨z.proj, c • z.2⟩) (𝓝[>] 0) (𝓝 ⟨(ψ z).proj, 0⟩) := by
    have hc : Continuous fun c : ℝ ↦ (⟨(ψ z).proj, c • (ψ z).2⟩ : CotangentBundle J N) :=
      (FiberBundle.continuous_totalSpaceMk _ _ (ψ z).proj).comp
        (continuous_id.smul continuous_const)
    have h := hc.tendsto 0
    rw [zero_smul] at h
    refine (h.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with c hc
    exact (ψ.apply_mk_smul_of_mpullback_liouvilleForm hψ z hc).symm
  exact tendsto_nhds_unique hM hN

variable [T2Space M] [I.Boundaryless]

/-- The base diffeomorphism `x ↦ π (ψ (x, 0))` of a Liouville-preserving diffeomorphism of
cotangent bundles; its inverse is the base map of `ψ⁻¹`. -/
private def baseDiffeomorph
    (ψ : CotangentBundle I M ≃ₘ⟮I.prod 𝓘(ℝ, E →L[ℝ] ℝ), J.prod 𝓘(ℝ, F →L[ℝ] ℝ)⟯
      CotangentBundle J N)
    (hψ : SmoothForm.mpullback ψ ψ.contMDiff (liouvilleForm J N) = liouvilleForm I M) :
    M ≃ₘ⟮I, J⟯ N where
  toFun x := (ψ (zeroSection _ _ x)).proj
  invFun y := (ψ.symm (zeroSection _ _ y)).proj
  left_inv x := by
    have h := ψ.symm.apply_mk_zero_of_mpullback_liouvilleForm
      (SmoothForm.mpullback_symm_eq_of_mpullback_eq hψ) (ψ (zeroSection _ _ x))
    rw [ψ.symm_apply_apply] at h
    exact congrArg TotalSpace.proj h
  right_inv y := by
    have h := ψ.apply_mk_zero_of_mpullback_liouvilleForm hψ (ψ.symm (zeroSection _ _ y))
    rw [ψ.apply_symm_apply] at h
    exact congrArg TotalSpace.proj h
  contMDiff_toFun :=
    (contMDiff_proj _).comp (ψ.contMDiff.comp (contMDiff_zeroSection ℝ _))
  contMDiff_invFun :=
    (contMDiff_proj _).comp (ψ.symm.contMDiff.comp (contMDiff_zeroSection ℝ _))

/-- A Liouville-preserving diffeomorphism is the cotangent lift of its base diffeomorphism. -/
private theorem cotangent_baseDiffeomorph
    (ψ : CotangentBundle I M ≃ₘ⟮I.prod 𝓘(ℝ, E →L[ℝ] ℝ), J.prod 𝓘(ℝ, F →L[ℝ] ℝ)⟯
      CotangentBundle J N)
    (hψ : SmoothForm.mpullback ψ ψ.contMDiff (liouvilleForm J N) = liouvilleForm I M) :
    (baseDiffeomorph ψ hψ).cotangent = ψ := by
  set h := baseDiffeomorph ψ hψ
  have hproj (z : CotangentBundle I M) : (ψ z).proj = h z.proj :=
    (congrArg TotalSpace.proj (ψ.apply_mk_zero_of_mpullback_liouvilleForm hψ z)).symm
  refine Diffeomorph.ext fun z ↦
    CotangentBundle.ext ((proj_cotangent h z).trans (hproj z).symm) fun v ↦ ?_
  -- Both covectors evaluate `v = dh_x ((dh_x)⁻¹ v)` as `z` evaluates `(dh_x)⁻¹ v`.
  exact (cotangent_snd_apply h z v).trans
    ((snd_apply_mfderiv_of_proj_apply_eq ψ hψ (h.mdifferentiable (by simp)) hproj z _).symm.trans
      (congrArg (ψ z).2 (h.mfderiv_apply_mfderiv_symm_apply (by simp) z.proj v)))

/-- **Liouville-preserving diffeomorphisms of cotangent bundles are cotangent lifts.** On
Hausdorff manifolds without boundary, a smooth diffeomorphism `ψ : T*M → T*N` with
`ψ^* λ_N = λ_M` is the cotangent lift of a unique smooth diffeomorphism `h : M → N`. Since the
lift covers `h`, necessarily `h x = π (ψ (x, 0))`. -/
theorem existsUnique_cotangent_eq_of_mpullback_liouvilleForm
    (ψ : CotangentBundle I M ≃ₘ⟮I.prod 𝓘(ℝ, E →L[ℝ] ℝ), J.prod 𝓘(ℝ, F →L[ℝ] ℝ)⟯
      CotangentBundle J N)
    (hψ : SmoothForm.mpullback ψ ψ.contMDiff (liouvilleForm J N) = liouvilleForm I M) :
    ∃! h : M ≃ₘ⟮I, J⟯ N, h.cotangent = ψ :=
  ⟨baseDiffeomorph ψ hψ, cotangent_baseDiffeomorph ψ hψ, fun _ hh ↦
    cotangent_injective (hh.trans (cotangent_baseDiffeomorph ψ hψ).symm)⟩

/-- **Characterization of cotangent lifts.** On Hausdorff manifolds without boundary, a smooth
diffeomorphism `ψ : T*M → T*N` is the cotangent lift of a smooth diffeomorphism `M → N` exactly
when it pulls the Liouville form `λ_N` back to `λ_M`. -/
theorem exists_cotangent_eq_iff_mpullback_liouvilleForm
    (ψ : CotangentBundle I M ≃ₘ⟮I.prod 𝓘(ℝ, E →L[ℝ] ℝ), J.prod 𝓘(ℝ, F →L[ℝ] ℝ)⟯
      CotangentBundle J N) :
    (∃ h : M ≃ₘ⟮I, J⟯ N, h.cotangent = ψ) ↔
      SmoothForm.mpullback ψ ψ.contMDiff (liouvilleForm J N) = liouvilleForm I M := by
  refine ⟨?_, fun hψ ↦ (existsUnique_cotangent_eq_of_mpullback_liouvilleForm ψ hψ).exists⟩
  rintro ⟨h, rfl⟩
  exact mpullback_cotangent_liouvilleForm h

end Base

end Diffeomorph
