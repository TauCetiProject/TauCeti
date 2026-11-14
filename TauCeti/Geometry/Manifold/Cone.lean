/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yangyang Li, The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# The positive-radius parametrization of a cone

This file constructs the open radial domain `radiusDomain`, its unit coordinate vector
`radialVector`, and the cone parametrization `(r, x) ↦ r • f x`, with smoothness and
differential formulas. These supply the calculus for studying the regular part of a cone over
an immersion.
The intrinsic metric is constructed separately in `TauCeti.Geometry.Manifold.Riemannian.Cone`.

Adapted from Yangyang Li's formalization, ported by Riccardo Brasca in commit
`247d17d130a24baafcb83278fbea532f606084b4` of TauCetiProject/TauCeti (Apache 2.0).
-/

public noncomputable section

open Bundle Manifold Set TopologicalSpace
open scoped ContDiff TauCeti

namespace TauCeti.Manifold.Cone

/-- The open positive-radius parameter domain. -/
def radiusDomain : Opens ℝ := ⟨Ioi 0, isOpen_Ioi⟩

/-- Membership in the radial domain is positivity. -/
@[simp]
theorem mem_radiusDomain {r : ℝ} : r ∈ radiusDomain ↔ 0 < r :=
  (Iff.rfl)

/-- The radial domain consists of positive real numbers. -/
@[simp]
theorem coe_radiusDomain : (radiusDomain : Set ℝ) = Ioi 0 :=
  (rfl)

/-- Every radius in the regular cone domain is positive. -/
theorem coe_radiusDomain_pos (r : radiusDomain) : 0 < (r : ℝ) :=
  r.property

/-- The outward radial tangent vector with coordinate velocity one. -/
def radialVector (r : radiusDomain) : TangentSpace 𝓘(ℝ) r :=
  (tangentSpaceOpenEquiv (I := 𝓘(ℝ)) r).symm
    ((NormedSpace.fromTangentSpace (r : ℝ)).symm 1)

/-- The radial vector is the inverse image of coordinate velocity one. -/
theorem radialVector_def (r : radiusDomain) :
    radialVector r = (tangentSpaceOpenEquiv (I := 𝓘(ℝ)) r).symm
      ((NormedSpace.fromTangentSpace (r : ℝ)).symm 1) :=
  (rfl)

/-- The radial vector has coordinate velocity one. -/
@[simp high]
theorem mvfderiv_subtype_val_radialVector (r : radiusDomain) :
    mvfderiv 𝓘(ℝ) (Subtype.val : radiusDomain → ℝ) r (radialVector r) = 1 := by
  simp only [radialVector, mvfderiv, ContinuousLinearMap.comp_apply, mfderiv_subtype_val,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]

/-- The radial vector field is `C^k` for every regularity order. -/
theorem contMDiff_radialVector {k : ℕ∞ω} :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ).tangent k (T% radialVector) := by
  intro r
  rw [contMDiffAt_section_iff]
  apply (contMDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq
  let t := trivializationAt ℝ (TangentSpace 𝓘(ℝ) : radiusDomain → Type) r
  filter_upwards [eventually_tangentSpaceOpenEquiv_symmL_trivializationAt_eq (I := 𝓘(ℝ)) r,
    t.open_baseSet.mem_nhds (mem_baseSet_trivializationAt ℝ _ r)] with s hs hst
  have hr : radialVector s = t.symmL ℝ s 1 := by
    apply (tangentSpaceOpenEquiv (I := 𝓘(ℝ)) s).injective
    rw [radialVector, ContinuousLinearEquiv.apply_symm_apply, hs]
    simp only [TangentBundle.symmL_model_space]
    -- The model-space tangent equivalence and the identity linear map both act as identity.
    rfl
  rw [hr, ← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ t hst]
  exact t.continuousLinearMapAt_symmL hst 1

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The positive-radius cone parametrization of a vector-valued map. -/
def parametrization (f : M → F) (p : radiusDomain × M) : F :=
  (p.1 : ℝ) • f p.2

omit [TopologicalSpace M] in
/-- Evaluation of the cone parametrization. -/
theorem parametrization_def (f : M → F) (p : radiusDomain × M) :
    parametrization f p = (p.1 : ℝ) • f p.2 :=
  (rfl)

/-- Local smoothness of a cone parametrization follows from local smoothness of its link. -/
theorem contMDiffAt_parametrization {f : M → F} {p : radiusDomain × M} {k : ℕ∞ω}
    (hf : ContMDiffAt I 𝓘(ℝ, F) k f p.2) :
    ContMDiffAt ((𝓘(ℝ)).prod I) 𝓘(ℝ, F) k (parametrization f) p := by
  exact ((contMDiff_subtype_val p.1).comp p contMDiffAt_fst).smul
    (hf.comp p contMDiffAt_snd)

/-- Smoothness of a cone parametrization follows from smoothness of its link. -/
theorem contMDiff_parametrization {f : M → F} {k : ℕ∞ω}
    (hf : ContMDiff I 𝓘(ℝ, F) k f) :
    ContMDiff ((𝓘(ℝ)).prod I) 𝓘(ℝ, F) k (parametrization f) := by
  exact fun p ↦ contMDiffAt_parametrization (hf p.2)

/-- Local differentiability of a cone parametrization only requires local differentiability
of its link. -/
theorem mdifferentiableAt_parametrization {f : M → F} {p : radiusDomain × M}
    (hf : MDifferentiableAt I 𝓘(ℝ, F) f p.2) :
    MDifferentiableAt ((𝓘(ℝ)).prod I) 𝓘(ℝ, F) (parametrization f) p := by
  unfold parametrization
  exact ((contMDiff_subtype_val.comp contMDiff_fst).mdifferentiableAt one_ne_zero).smul
    (hf.comp p mdifferentiableAt_snd)

/-- The differential of the cone parametrization is the sum of its radial and link parts. -/
theorem mvfderiv_parametrization_apply {f : M → F} {p : radiusDomain × M}
    (hf : MDifferentiableAt I 𝓘(ℝ, F) f p.2)
    (v : TangentSpace ((𝓘(ℝ)).prod I) p) :
    mvfderiv ((𝓘(ℝ)).prod I) (parametrization f) p v =
      (p.1 : ℝ) • mvfderiv I f p.2 (tangentSpaceProdEquiv p v).2 +
        mvfderiv 𝓘(ℝ) (Subtype.val : radiusDomain → ℝ) p.1
          (tangentSpaceProdEquiv p v).1 • f p.2 := by
  have hr : MDifferentiableAt ((𝓘(ℝ)).prod I) 𝓘(ℝ)
      (fun q : radiusDomain × M ↦ (q.1 : ℝ)) p := by
    exact (contMDiff_subtype_val.comp contMDiff_fst).mdifferentiableAt one_ne_zero
  have hF : MDifferentiableAt ((𝓘(ℝ)).prod I) 𝓘(ℝ, F)
      (fun q : radiusDomain × M ↦ f q.2) p := hf.comp p mdifferentiableAt_snd
  have h₁ := TauCeti.mvfderiv_comp_fst_apply (Subtype.val : radiusDomain → ℝ) p v
  have h₂ := TauCeti.mvfderiv_comp_snd_apply f p v
  unfold parametrization
  rw [mvfderiv_fun_smul hr hF]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  simp only [Function.comp_def] at h₁ h₂
  rw [h₁, h₂, tangentSpaceProdEquiv_apply]

/-- The outward radial direction maps to the link's position vector. -/
theorem mvfderiv_parametrization_radial {f : M → F} {p : radiusDomain × M}
    (hf : MDifferentiableAt I 𝓘(ℝ, F) f p.2) :
    mvfderiv ((𝓘(ℝ)).prod I) (parametrization f) p
      ((tangentSpaceProdEquiv p).symm (radialVector p.1, 0)) = f p.2 := by
  rw [mvfderiv_parametrization_apply hf, ContinuousLinearEquiv.apply_symm_apply]
  simp only [map_zero, smul_zero, zero_add, mvfderiv_subtype_val_radialVector, one_smul]

end TauCeti.Manifold.Cone
