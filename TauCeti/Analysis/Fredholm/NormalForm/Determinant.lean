/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.NormalForm.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Basic.Sign.Basic
import Mathlib.Topology.Instances.Sign
import Mathlib.Analysis.Calculus.ContDiff.Comp
import TauCeti.LinearAlgebra.Prod

/-!
# Signs of zeros under the Lyapunov–Schmidt reduction

Let `f : E → E` be a `C¹` map of a finite-dimensional real normed space whose derivative at `a`
is `T`, and fix a Fredholm package for `T`: splittings `E = X₁ ⊕ X₀` of the domain, with `X₀` the
kernel, and `E = Y₁ ⊕ Y₀` of the codomain, with `Y₁` the range. In the normal-form chart `Φ` of
`TauCeti.Analysis.Fredholm.NormalForm.Basic`, `f` reads `y ↦ y.1 + q y` with the obstruction
`q` valued in `Y₀`. Writing `v = v₁ + v₀`, the solutions of `f x = v` near `a` are the
solutions of `q (v₁, z) = v₀` for the finite-dimensional *obstruction slice*
`z ↦ q (v₁, z) : X₀ → Y₀`
(`ContinuousLinearMap.FredholmPackage.apply_normalFormOpenPartialHomeomorph_symm_eq_iff`). This is
the Lyapunov–Schmidt reduction. This file shows that it is an *oriented* correspondence: up to
one sign fixed at the base point, a solution of `f x = v` and the corresponding solution of
`q (v₁, z) = v₀` have the same Jacobian sign.

Since `X₀` and `Y₀` have the same dimension, Jacobians of the slice become determinants once an
identification `ι : Y₀ ≃ X₀` is chosen, as an orientation of a determinant line would be chosen.
With `Θ = (proj₁, ι ∘ proj₀) : E ≃ Y₁ × X₀` (`ContinuousLinearMap.FredholmPackage.codomainEquiv`),
the derivative of `Θ ∘ f ∘ Φ⁻¹` is block lower triangular, with diagonal blocks the identity of
`Y₁` and `ι ∘ S`, where `S` is the derivative of the slice. Hence

`det Df(Φ⁻¹ y) · det (DΦ⁻¹(y) ∘ Θ) = det (ι ∘ S)`

at every point of the chart
(`ContinuousLinearMap.FredholmPackage.det_fderiv_mul_det_eq`, from the block determinant formula
`LinearMap.det_eq_det_snd_comp_comp_inr`). The middle factor depends continuously on `y` and is
nonzero at the base point, where `DΦ⁻¹` is the linear normal-form coordinate change. So near the
base point its sign is the **reduction sign** `ContinuousLinearMap.FredholmPackage.reductionSign`,
which depends only on the Fredholm package and `ι`, and

`sign det Df(Φ⁻¹ y) = reductionSign ι · sign det (ι ∘ S)`

(`ContinuousLinearMap.FredholmPackage.eventually_sign_det_fderiv_eq`). Summing over solutions,
the signed count of the solutions of `f x = v` in a fixed neighbourhood of `a` is the reduction
sign times the signed count of the solutions of `q (v₁, z) = v₀`, for every `v`
(`ContinuousLinearMap.FredholmPackage.exists_mem_nhds_finsum_sign_det_eq`).

In Taubes's construction of the weighted count of pseudoholomorphic curves, the deformation
problem near a degenerate curve is reduced in this way to a finite-dimensional obstruction map
between the kernel and the cokernel of the linearized operator. Births and deaths of curves, and
the local degrees of covered tori, are then read off the obstruction map. There the problem is
infinite-dimensional, and orientations are transported by the analogous correspondence with
Jacobian signs replaced by orientations of the Fredholm determinant line; this file proves only
the finite-dimensional case. The fold and pitchfork models of
`TauCeti.Analysis.Calculus.Bifurcation` describe the one-dimensional obstruction maps that arise.

## Main definitions

* `ContinuousLinearMap.FredholmPackage.codomainEquiv`: the identification `Θ` of the codomain
  with the normal-form coordinate space determined by `ι : Y₀ ≃ X₀`.
* `ContinuousLinearMap.FredholmPackage.reductionSign`: the sign of `det (Φ₀⁻¹ ∘ Θ)`, with `Φ₀` the
  linear normal-form coordinate change.

## Main results

* `ContinuousLinearMap.FredholmPackage.det_fderiv_mul_det_eq`: the Jacobian identity above.
* `ContinuousLinearMap.FredholmPackage.eventually_sign_det_fderiv_eq`: near the base point, the
  Jacobian sign of `f` is the reduction sign times that of the obstruction slice.
* `ContinuousLinearMap.FredholmPackage.exists_mem_nhds_finsum_sign_det_eq`: the signed counts of
  solutions agree up to the reduction sign.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  44 (1996), 818–893.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., American
  Mathematical Society, 2012, Appendix A.
-/

public section

noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace ContinuousLinearMap.FredholmPackage

section CodomainEquiv

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {T : E →L[𝕜] F} (pkg : T.FredholmPackage)

/-- The identification of the codomain `F = Y₁ ⊕ Y₀` of a Fredholm package with the normal-form
coordinate space `Y₁ × X₀`, using a chosen linear equivalence `ι : Y₀ ≃ X₀` from the
complement of the range to the complement of the essential domain summand. Here `Y₁` is the
range of `T`, so `Y₀` is a cokernel and `X₀` the kernel. -/
def codomainEquiv (ι : pkg.decCodom.X₀ ≃ₗ[𝕜] pkg.decDom.X₀) :
    F ≃ₗ[𝕜] pkg.decCodom.X₁ × pkg.decDom.X₀ :=
  (Submodule.prodEquivOfIsCompl _ _ pkg.decCodom.isTopCompl.isCompl).symm.trans
    ((LinearEquiv.refl 𝕜 _).prodCongr ι)

@[simp]
theorem codomainEquiv_apply (ι : pkg.decCodom.X₀ ≃ₗ[𝕜] pkg.decDom.X₀) (v : F) :
    pkg.codomainEquiv ι v =
      (pkg.decCodom.proj v,
        ι (pkg.decCodom.X₀.projectionOntoL pkg.decCodom.X₁ pkg.decCodom.isTopCompl.symm v)) := by
  simp [codomainEquiv]

@[simp]
theorem codomainEquiv_symm_apply (ι : pkg.decCodom.X₀ ≃ₗ[𝕜] pkg.decDom.X₀)
    (w : pkg.decCodom.X₁ × pkg.decDom.X₀) :
    (pkg.codomainEquiv ι).symm w = (w.1 : F) + (ι.symm w.2 : F) := by
  simp [codomainEquiv, Submodule.coe_prodEquivOfIsCompl']

end CodomainEquiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {T : E →L[ℝ] E} (pkg : T.FredholmPackage)

/-- The **reduction sign** of a Fredholm package with index-zero identification
`ι : Y₀ ≃ X₀`: the sign of the determinant of `Φ₀⁻¹ ∘ Θ`, where `Φ₀ = pkg.normalFormEquivL` is
the linear normal-form coordinate change and `Θ = pkg.codomainEquiv ι`. It is the fixed sign
relating the Jacobian of a map to the Jacobian of its finite-dimensional obstruction slice
(`ContinuousLinearMap.FredholmPackage.eventually_sign_det_fderiv_eq`). -/
def reductionSign (ι : pkg.decCodom.X₀ ≃ₗ[ℝ] pkg.decDom.X₀) : SignType :=
  SignType.sign (LinearMap.det
    ((pkg.normalFormEquivL.symm : (pkg.decCodom.X₁ × pkg.decDom.X₀) →L[ℝ] E).toLinearMap ∘ₗ
      (pkg.codomainEquiv ι).toLinearMap))

theorem reductionSign_def (ι : pkg.decCodom.X₀ ≃ₗ[ℝ] pkg.decDom.X₀) :
    pkg.reductionSign ι = SignType.sign (LinearMap.det
      ((pkg.normalFormEquivL.symm : (pkg.decCodom.X₁ × pkg.decDom.X₀) →L[ℝ] E).toLinearMap ∘ₗ
        (pkg.codomainEquiv ι).toLinearMap)) :=
  (rfl)

theorem reductionSign_ne_zero (ι : pkg.decCodom.X₀ ≃ₗ[ℝ] pkg.decDom.X₀) :
    pkg.reductionSign ι ≠ 0 := by
  rw [reductionSign_def, Ne, sign_eq_zero_iff]
  exact (LinearEquiv.isUnit_det' ((pkg.codomainEquiv ι).trans
    pkg.normalFormEquivL.symm.toLinearEquiv)).ne_zero

variable {f : E → E} {a : E}

variable [FiniteDimensional ℝ E]

/-- **Jacobians under the Lyapunov–Schmidt reduction.** Let `Φ` be the normal-form chart of `f`
at `a`, in which `f` reads `y ↦ y.1 + q y`, and let `S = D_z q(y.1, ·)` be the derivative of the
obstruction slice. At a point `y` of the chart's target where `Φ⁻¹` is differentiable, and `f` is
differentiable at `Φ⁻¹ y`,

`det Df(Φ⁻¹ y) · det (DΦ⁻¹(y) ∘ Θ) = det (ι ∘ S)`,

with `Θ = pkg.codomainEquiv ι`. In the coordinates `Θ` of the codomain the derivative of
`f ∘ Φ⁻¹` is block lower triangular with diagonal blocks `id` and `ι ∘ S`. -/
theorem det_fderiv_mul_det_eq (hT : HasStrictFDerivAt f T a)
    (ι : pkg.decCodom.X₀ ≃ₗ[ℝ] pkg.decDom.X₀) {y : pkg.decCodom.X₁ × pkg.decDom.X₀}
    (hy : y ∈ (pkg.normalFormOpenPartialHomeomorph hT).target)
    (hsymm : DifferentiableAt ℝ (pkg.normalFormOpenPartialHomeomorph hT).symm y)
    (hfd : DifferentiableAt ℝ f ((pkg.normalFormOpenPartialHomeomorph hT).symm y)) :
    LinearMap.det (fderiv ℝ f ((pkg.normalFormOpenPartialHomeomorph hT).symm y) : E →ₗ[ℝ] E) *
        LinearMap.det ((fderiv ℝ (pkg.normalFormOpenPartialHomeomorph hT).symm y).toLinearMap ∘ₗ
          (pkg.codomainEquiv ι).toLinearMap) =
      LinearMap.det (ι.toLinearMap ∘ₗ
        (fderiv ℝ (pkg.obstructionSlice hT y.1) y.2).toLinearMap) := by
  set Φ := pkg.normalFormOpenPartialHomeomorph hT
  set q := pkg.obstructionMap hT with hqdef
  have hq : DifferentiableAt ℝ q y := by
    rw [hqdef, funext (pkg.obstructionMap_apply hT)]
    exact (ContinuousLinearMap.differentiableAt _).comp y (hfd.comp y hsymm)
  set Θ := pkg.codomainEquiv ι
  set L := fderiv ℝ f (Φ.symm y)
  set P := fderiv ℝ Φ.symm y
  -- The derivative of `f ∘ Φ⁻¹`, computed through the chart and through the normal form.
  have h₁ : HasFDerivAt (fun y' ↦ f (Φ.symm y')) (L.comp P) y :=
    hfd.hasFDerivAt.comp y hsymm.hasFDerivAt
  set u : (pkg.decCodom.X₁ × pkg.decDom.X₀) →L[ℝ] E :=
    pkg.decCodom.X₁.subtypeL.comp (ContinuousLinearMap.fst ℝ _ _) +
      pkg.decCodom.X₀.subtypeL.comp (fderiv ℝ q y) with hu
  have h₂ : HasFDerivAt (fun y' ↦ f (Φ.symm y')) u y :=
    pkg.hasFDerivAt_comp_normalFormOpenPartialHomeomorph_symm hT hy hq
  have hLP : L.comp P = u := h₁.unique h₂
  have hslice : fderiv ℝ (pkg.obstructionSlice hT y.1) y.2 =
      (fderiv ℝ q y).comp (ContinuousLinearMap.inr ℝ pkg.decCodom.X₁ pkg.decDom.X₀) :=
    (pkg.hasFDerivAt_obstructionSlice hT hq.hasFDerivAt).fderiv
  -- In the coordinates `Θ`, `u` is block lower triangular.
  have htri : ∀ w, (Θ (u w)).1 = w.1 := fun w ↦ by
    simp [Θ, hu]
  have hdiag : LinearMap.snd ℝ _ _ ∘ₗ (Θ.toLinearMap ∘ₗ u.toLinearMap) ∘ₗ LinearMap.inr ℝ _ _ =
      ι.toLinearMap ∘ₗ (fderiv ℝ (pkg.obstructionSlice hT y.1) y.2).toLinearMap := by
    ext z
    simp [Θ, hu, hslice]
  have hconj : Θ.toLinearMap ∘ₗ u.toLinearMap =
      Θ.toLinearMap ∘ₗ (L.toLinearMap ∘ₗ P.toLinearMap ∘ₗ Θ.toLinearMap) ∘ₗ
        Θ.symm.toLinearMap := by
    refine LinearMap.ext fun w ↦ ?_
    simp [← hLP]
  rw [← hdiag, ← LinearMap.det_eq_det_snd_comp_comp_inr htri, hconj, LinearMap.det_conj,
    LinearMap.det_comp]

/-- Near the base coordinate of the chart of a `C¹` map, `det (DΦ⁻¹(y) ∘ Θ)` has the reduction
sign: at the base coordinate `DΦ⁻¹` is the linear normal-form coordinate change. -/
private theorem eventually_sign_det_fderiv_symm_comp_codomainEquiv (hT : HasStrictFDerivAt f T a)
    (hf : ContDiffAt ℝ 1 f a) (ι : pkg.decCodom.X₀ ≃ₗ[ℝ] pkg.decDom.X₀) :
    ∀ᶠ y in 𝓝 (pkg.decCodom.proj (f a), (0 : pkg.decDom.X₀)),
      SignType.sign (LinearMap.det
        ((fderiv ℝ (pkg.normalFormOpenPartialHomeomorph hT).symm y).toLinearMap ∘ₗ
          (pkg.codomainEquiv ι).toLinearMap)) = pkg.reductionSign ι := by
  set y₀ : pkg.decCodom.X₁ × pkg.decDom.X₀ := (pkg.decCodom.proj (f a), 0)
  let Θ : E →L[ℝ] pkg.decCodom.X₁ × pkg.decDom.X₀ :=
    LinearMap.toContinuousLinearMap (pkg.codomainEquiv ι).toLinearMap
  let c : pkg.decCodom.X₁ × pkg.decDom.X₀ → ℝ := fun y ↦
    ((fderiv ℝ (pkg.normalFormOpenPartialHomeomorph hT).symm y).comp Θ).det
  have hc : ContinuousAt c y₀ :=
    ContinuousLinearMap.continuous_det.continuousAt.comp
      (((pkg.contDiffAt_normalFormOpenPartialHomeomorph_symm_self hT hf).continuousAt_fderiv
        one_ne_zero).clm_comp continuousAt_const)
  have hc_eq : ∀ y, c y = LinearMap.det
      ((fderiv ℝ (pkg.normalFormOpenPartialHomeomorph hT).symm y).toLinearMap ∘ₗ
        (pkg.codomainEquiv ι).toLinearMap) := fun y ↦ by
    simp only [c, ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, Θ,
      LinearMap.coe_toContinuousLinearMap]
  have hd : fderiv ℝ (pkg.normalFormOpenPartialHomeomorph hT).symm y₀ =
      pkg.normalFormEquivL.symm :=
    (pkg.hasStrictFDerivAt_normalFormOpenPartialHomeomorph_symm_self hT).hasFDerivAt.fderiv
  have hc₀ : SignType.sign (c y₀) = pkg.reductionSign ι := by
    rw [hc_eq, reductionSign_def, hd]
  have hc₀ne : c y₀ ≠ 0 := by
    rw [← sign_ne_zero, hc₀]
    exact pkg.reductionSign_ne_zero ι
  rw [← hc₀]
  filter_upwards [((continuousAt_sign_of_ne_zero hc₀ne).comp hc).eventually_mem
    ((isOpen_discrete {SignType.sign (c y₀)}).mem_nhds rfl)] with y hy
  rwa [← hc_eq]

/-- **Signs of the Jacobian under the Lyapunov–Schmidt reduction.** Let `f` be `C¹` at `a`, with
derivative `T` and a Fredholm package for `T`, and let `ι : Y₀ ≃ X₀` identify the complement of
the range with the kernel. Near the normal-form coordinate of `a`, the obstruction slice
`z ↦ q (y.1, z)` is differentiable and the sign of the Jacobian of `f` at `Φ⁻¹ y` is the fixed
sign `pkg.reductionSign ι` times the sign of the Jacobian of `ι ∘ q (y.1, ·)` at `y.2`. In
particular `Φ⁻¹ y` is a nondegenerate point of `f` exactly when `y.2` is a nondegenerate point of
the slice, and nondegenerate zeros of `f` near `a` carry the signs of the corresponding zeros of
the slice, all multiplied by one sign. -/
theorem eventually_sign_det_fderiv_eq (hT : HasStrictFDerivAt f T a) (hf : ContDiffAt ℝ 1 f a)
    (ι : pkg.decCodom.X₀ ≃ₗ[ℝ] pkg.decDom.X₀) :
    ∀ᶠ y in 𝓝 (pkg.decCodom.proj (f a), (0 : pkg.decDom.X₀)),
      y ∈ (pkg.normalFormOpenPartialHomeomorph hT).target ∧
      DifferentiableAt ℝ (pkg.obstructionSlice hT y.1) y.2 ∧
      SignType.sign (LinearMap.det
          (fderiv ℝ f ((pkg.normalFormOpenPartialHomeomorph hT).symm y) : E →ₗ[ℝ] E)) =
        pkg.reductionSign ι * SignType.sign (LinearMap.det (ι.toLinearMap ∘ₗ
          (fderiv ℝ (pkg.obstructionSlice hT y.1) y.2).toLinearMap)) := by
  have hf' : ContDiffAt ℝ ((1 : ℕ) : ℕ∞ω) f a := by simpa using hf
  filter_upwards [pkg.eventually_mem_target_contDiffAt_normalForm hT le_rfl hf',
    pkg.eventually_sign_det_fderiv_symm_comp_codomainEquiv hT hf ι]
    with y hy hcy
  obtain ⟨hy, hq, hsymm, -, hfy⟩ := hy
  have hqd : DifferentiableAt ℝ (pkg.obstructionMap hT) y := hq.differentiableAt (by simp)
  refine ⟨hy, ?_, ?_⟩
  · rw [funext (pkg.obstructionSlice_apply hT y.1)]
    exact hqd.comp y.2 (differentiableAt_const _ |>.prodMk differentiableAt_id)
  · have h := congrArg SignType.sign
      (pkg.det_fderiv_mul_det_eq hT ι hy (hsymm.differentiableAt (by simp))
        (hfy.differentiableAt (by simp)))
    rw [sign_mul, hcy] at h
    rw [← h, mul_comm _ (pkg.reductionSign ι), ← mul_assoc]
    have hσ := pkg.reductionSign_ne_zero ι
    generalize pkg.reductionSign ι = σ at hσ ⊢
    cases σ <;> simp_all

/-- **Signed counts under the Lyapunov–Schmidt reduction.** Let `f` be `C¹` at `a`, with
derivative `T`, a Fredholm package for `T` and an identification `ι : Y₀ ≃ X₀`. There is a
neighbourhood `V` of the normal-form coordinate of `a`, whose image `Φ⁻¹ V` is a neighbourhood
of `a`, such that for every value `v` the signed count of the solutions of `f x = v` in `Φ⁻¹ V`
is `pkg.reductionSign ι` times the signed count of the solutions of the finite-dimensional equation
`q (v₁, z) = v₀` in the slice of `V` over the essential part `v₁` of `v`, where `v₀` is the
complementary part. Solutions are counted by the signs of the Jacobians of `f` and of
`ι ∘ q (v₁, ·)`; a degenerate solution contributes `0` on both sides, and if infinitely many
solutions are nondegenerate, both counts are `0` (the `finsum` convention). -/
theorem exists_mem_nhds_finsum_sign_det_eq (hT : HasStrictFDerivAt f T a)
    (hf : ContDiffAt ℝ 1 f a) (ι : pkg.decCodom.X₀ ≃ₗ[ℝ] pkg.decDom.X₀) :
    ∃ V ∈ 𝓝 (pkg.decCodom.proj (f a), (0 : pkg.decDom.X₀)),
      (pkg.normalFormOpenPartialHomeomorph hT).symm '' V ∈ 𝓝 a ∧ ∀ v : E,
        ∑ᶠ x ∈ (pkg.normalFormOpenPartialHomeomorph hT).symm '' V ∩ f ⁻¹' {v},
            (SignType.sign (LinearMap.det (fderiv ℝ f x : E →ₗ[ℝ] E)) : ℤ) =
          pkg.reductionSign ι * ∑ᶠ z ∈ {z | (pkg.decCodom.proj v, z) ∈ V ∧
              pkg.obstructionSlice hT (pkg.decCodom.proj v) z =
                pkg.decCodom.X₀.projectionOntoL pkg.decCodom.X₁ pkg.decCodom.isTopCompl.symm v},
            (SignType.sign (LinearMap.det (ι.toLinearMap ∘ₗ
              (fderiv ℝ (pkg.obstructionSlice hT (pkg.decCodom.proj v)) z).toLinearMap)) : ℤ) := by
  set Φ := pkg.normalFormOpenPartialHomeomorph hT
  have hsymy₀ : Φ.symm (pkg.decCodom.proj (f a), 0) = a :=
    pkg.normalFormOpenPartialHomeomorph_symm_proj_self hT
  set V := {y | y ∈ Φ.target ∧ DifferentiableAt ℝ (pkg.obstructionSlice hT y.1) y.2 ∧
      SignType.sign (LinearMap.det (fderiv ℝ f (Φ.symm y) : E →ₗ[ℝ] E)) =
        pkg.reductionSign ι * SignType.sign (LinearMap.det (ι.toLinearMap ∘ₗ
          (fderiv ℝ (pkg.obstructionSlice hT y.1) y.2).toLinearMap))}
  have hV : V ∈ 𝓝 (pkg.decCodom.proj (f a), (0 : pkg.decDom.X₀)) :=
    pkg.eventually_sign_det_fderiv_eq hT hf ι
  refine ⟨V, hV, ?_, fun v ↦ ?_⟩
  · rw [← hsymy₀]
    exact Φ.symm.image_mem_nhds
      (by simpa using pkg.normalFormOpenPartialHomeomorph_self_mem_target hT) hV
  rw [mul_finsum_mem]
  refine finsum_mem_eq_of_bijOn (fun x ↦ (Φ x).2) ⟨?_, ?_, ?_⟩ ?_
  · rintro _ ⟨⟨y, hyV, rfl⟩, hfy⟩
    obtain ⟨h₁, h₂⟩ := (pkg.apply_normalFormOpenPartialHomeomorph_symm_eq_iff hT hyV.1 v).1 hfy
    dsimp only
    rw [Φ.right_inv hyV.1]
    refine ⟨?_, ?_⟩
    · rwa [← h₁]
    · rw [← h₁, obstructionSlice_apply]; exact h₂
  · rintro _ ⟨⟨y₁, hy₁, rfl⟩, hf₁⟩ _ ⟨⟨y₂, hy₂, rfl⟩, hf₂⟩ h
    dsimp only at h
    rw [Φ.right_inv hy₁.1, Φ.right_inv hy₂.1] at h
    have e₁ := ((pkg.apply_normalFormOpenPartialHomeomorph_symm_eq_iff hT hy₁.1 v).1 hf₁).1
    have e₂ := ((pkg.apply_normalFormOpenPartialHomeomorph_symm_eq_iff hT hy₂.1 v).1 hf₂).1
    rw [Prod.ext (e₁.trans e₂.symm) h]
  · rintro z ⟨hzV, hz⟩
    refine ⟨Φ.symm (pkg.decCodom.proj v, z), ⟨⟨_, hzV, rfl⟩,
      (pkg.apply_normalFormOpenPartialHomeomorph_symm_eq_iff hT hzV.1 v).2
        ⟨rfl, (pkg.obstructionSlice_apply hT _ _).symm.trans hz⟩⟩, ?_⟩
    dsimp only
    rw [Φ.right_inv hzV.1]
  · rintro _ ⟨⟨y, hyV, rfl⟩, hfy⟩
    obtain ⟨h₁, -⟩ := (pkg.apply_normalFormOpenPartialHomeomorph_symm_eq_iff hT hyV.1 v).1 hfy
    rw [Φ.right_inv hyV.1, hyV.2.2, ← h₁, SignType.coe_mul]

end ContinuousLinearMap.FredholmPackage
