/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.MappingTorus
public import TauCeti.Geometry.Manifold.Instances.MappingTorus.Iterate.Basic

/-!
# Forms under the integer-iterate map of mapping tori

The natural map `Y_(φ^k) → Y_φ`, `[t, x] ↦ [k * t, x]`, pulls the time form back to
`k • dt` and preserves the fiber form of every `φ`-invariant differential form. In particular,
the fiber symplectic form has no time-rescaling factor. The statements also hold at `k = 0`,
where the time form pulls back to zero.

All pullbacks use the existing smooth differential-form calculus and the quotient construction
of the time and fiber forms.
-/

public section

noncomputable section

open Function
open scoped Manifold ContDiff

namespace TauCeti.SmoothMappingTorus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M]
  (φ : M ≃ₘ⟮I, I⟯ M) (k : ℤ)

/-- The integer-iterate map multiplies the time form by its time-rescaling factor. -/
@[simp]
theorem mpullback_iterateMap_timeForm :
    SmoothForm.mpullback (iterateMap φ k) (contMDiff_iterateMap φ k) (timeForm φ) =
      (k : ℝ) • timeForm (φ ^ k) := by
  apply Subtype.ext
  have hcomp : proj φ ∘ iterateMap φ k = (fun z : UnitAddCircle ↦ k • z) ∘ proj (φ ^ k) :=
    funext (proj_iterateMap φ k)
  simp only [timeForm_def, SmoothForm.coe_mpullback, Submodule.coe_smul_of_tower]
  rw [← mpullback_comp ((contMDiff_iterateMap φ k).mdifferentiable (by simp))
    ((contMDiff_proj φ).mdifferentiable (by simp)), hcomp,
    mpullback_comp ((contMDiff_proj (φ ^ k)).mdifferentiable (by simp))
      ((contMDiff_zsmul (n := ∞) k).mdifferentiable (by simp)), AddCircle.mpullback_zsmul_timeForm,
    mpullback_smul, Int.cast_smul_eq_zsmul]

/-- The integer-iterate map preserves the fiber form of an invariant form, in every degree. -/
@[simp]
theorem mpullback_iterateMap_fiberForm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {r : ℕ} (σ : SmoothForm I M F r) (hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ) :
    SmoothForm.mpullback (iterateMap φ k) (contMDiff_iterateMap φ k) (fiberForm φ σ hσ) =
      fiberForm (φ ^ k) σ (SmoothForm.mpullback_zpow_eq_self hσ k) := by
  apply (eq_fiberForm_iff (φ := φ ^ k)).2
  have hscale : ContMDiff (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) ∞
      (fun p : ℝ × M ↦ ((k : ℝ) * p.1, p.2)) :=
    ((contDiff_const.mul contDiff_id : ContDiff ℝ ∞ fun t : ℝ ↦ (k : ℝ) * t).contMDiff.comp
      contMDiff_fst).prodMk contMDiff_snd
  apply Subtype.ext
  have hfiber := congrArg Subtype.val (mpullback_uncurry_mk_fiberForm (hσ := hσ))
  simp only [SmoothForm.coe_mpullback] at hfiber ⊢
  rw [← mpullback_comp ((contMDiff_uncurry_mk (φ ^ k)).mdifferentiable (by simp))
      ((contMDiff_iterateMap φ k).mdifferentiable (by simp)), iterateMap_comp_uncurry_mk,
    mpullback_comp (hscale.mdifferentiable (by simp))
      ((contMDiff_uncurry_mk φ).mdifferentiable (by simp)), hfiber,
    ← mpullback_comp (hscale.mdifferentiable (by simp)) mdifferentiable_snd]
  have hsnd : Prod.snd ∘ (fun p : ℝ × M ↦ ((k : ℝ) * p.1, p.2)) = Prod.snd := rfl
  rw [hsnd]

end TauCeti.SmoothMappingTorus
