/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.VectorBundle
public import TauCeti.Geometry.Manifold.Instances.MappingTorus.Vertical
public import TauCeti.Geometry.Manifold.VectorField.MappingTorus
import TauCeti.Geometry.Manifold.VectorBundle.ComplementarySubbundle

/-!
# The splitting of the tangent bundle of a mapping torus

Let `φ : M ≃ₘ⟮I, I⟯ M` be a diffeomorphism of a locally compact Hausdorff smooth manifold modelled
on a finite-dimensional space `E`, and let `Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))` be its smooth
mapping torus, with projection `p : Y_φ → ℝ / ℤ`, time form `dt` and suspension vector field
`T = ∂_t`. At each point the tangent space splits as `T Y_φ = ℝ T ⊕ V` into the line spanned by `T`
and the vertical tangent space `V = ker dp`
(`TauCeti.SmoothMappingTorus.isCompl_span_timeVectorField_ker_mfderiv_proj`). This file proves the
splitting at the level of smooth vector bundles.

* Since `dt(T) = 1`, the field `T` vanishes nowhere, so the lines `ℝ T` form a smooth distribution
  of rank one with global frame `T`
  (`TauCeti.SmoothMappingTorus.isContMDiffDistribution_span_timeVectorField`), a trivial line
  bundle.
* The vertical spaces `V` form a smooth distribution of rank `dim E`
  (`TauCeti.SmoothMappingTorus.isContMDiffDistribution_ker_mfderiv_proj`), the vertical tangent
  bundle.
* Adding the two components, `(y, a, v) ↦ (y, a + v)`, is a smooth diffeomorphism from the total
  space of the direct-sum bundle `ℝ T ×ᵇ V` onto the tangent bundle of `Y_φ`
  (`TauCeti.SmoothMappingTorus.exists_bundleDiffeomorph_prod_tangentBundle`): the tangent bundle
  of the mapping torus is the Whitney sum of the line bundle spanned by `T` and the vertical
  tangent bundle. This is the splitting of a vector bundle by two complementary smooth subbundles
  (`TauCeti.HasLocalContMDiffSubbundleFrames.exists_bundleDiffeomorph_prod_of_isCompl`).
* The projection of `T Y_φ` onto `V` along `T` sends `w` to `w - dt(w) T`
  (`TauCeti.SmoothMappingTorus.projection_ker_mfderiv_proj`), and it is a smooth map of
  total spaces from the tangent bundle to the vertical tangent bundle
  (`TauCeti.SmoothMappingTorus.contMDiff_totalSpace_projectionOnto_ker_mfderiv_proj`).

No compactness of `M` is needed.

## Main results

* `TauCeti.SmoothMappingTorus.isContMDiffDistribution_span_timeVectorField`: the line field
  spanned by `T` is a smooth distribution of rank one.
* `TauCeti.SmoothMappingTorus.exists_bundleDiffeomorph_prod_tangentBundle`: the splitting
  `T Y_φ = ℝ T ⊕ V` as a diffeomorphism of total spaces.
* `TauCeti.SmoothMappingTorus.projection_ker_mfderiv_proj`,
  `TauCeti.SmoothMappingTorus.contMDiff_totalSpace_projectionOnto_ker_mfderiv_proj`: the vertical
  projection `w ↦ w - dt(w) T` and its smoothness.

## References

* Michael Hutchings and Michael Sullivan, *The periodic Floer homology of a Dehn twist*, Algebraic
  & Geometric Topology 5 (2005), 301–354, Section 2 (the vertical tangent bundle of a mapping
  torus).
-/

public section

open Bundle Module
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothMappingTorus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M]
  (φ : M ≃ₘ⟮I, I⟯ M)

/-- The suspension vector field `T` vanishes nowhere, since `dt(T) = 1`. -/
theorem timeVectorField_ne_zero (y : SmoothMappingTorus φ) : timeVectorField φ y ≠ 0 := by
  intro h
  have hT := timeForm_timeVectorField φ y
  rw [h, ← SmoothForm.degreeOneEquiv_apply_apply_vec, map_zero] at hT
  exact zero_ne_one hT

/-- The lines `ℝ T` spanned by the suspension vector field form a smooth distribution of rank one
on the mapping torus, with global frame `T`. -/
theorem isContMDiffDistribution_span_timeVectorField :
    IsContMDiffDistribution (𝓘(ℝ).prod I) ∞ 1 fun y : SmoothMappingTorus φ ↦
      ℝ ∙ timeVectorField φ y :=
  isContMDiffDistribution_span_singleton (contMDiff_timeVectorField φ) (timeVectorField_ne_zero φ)

/-- The projection of a tangent vector `w` of the mapping torus onto the vertical space `V = ker dp`
along the suspension vector field `T` is `w - dt(w) T`. -/
@[simp]
theorem projection_ker_mfderiv_proj (y : SmoothMappingTorus φ)
    (w : TangentSpace (𝓘(ℝ).prod I) y) :
    (mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ) (proj φ) y).ker.projection (ℝ ∙ timeVectorField φ y)
        (isCompl_span_timeVectorField_ker_mfderiv_proj φ y).symm w =
      w - (timeForm φ).val y ![w] • timeVectorField φ y := by
  set c : ℝ := (timeForm φ).val y ![w]
  have hc : mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ) (proj φ) y w = c := (timeForm_apply φ y ![w]).symm
  -- `w - dt(w) T` is vertical, since `dp(T) = 1`, and `dt(w) T` lies on the line of `T`.
  have hv : w - c • timeVectorField φ y ∈ (mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ) (proj φ) y).ker := by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, map_smul,
      mfderiv_proj_timeVectorField, hc]
    exact sub_eq_zero.2 (mul_one c).symm
  have hu : c • timeVectorField φ y ∈ ℝ ∙ timeVectorField φ y :=
    Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
  set P := (mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ) (proj φ) y).ker.projectionOnto (ℝ ∙ timeVectorField φ y)
    (isCompl_span_timeVectorField_ker_mfderiv_proj φ y).symm
  have hP₁ : P (w - c • timeVectorField φ y) = ⟨_, hv⟩ :=
    Submodule.projectionOnto_apply_left _ ⟨_, hv⟩
  have hP₂ : P (c • timeVectorField φ y) = 0 := Submodule.projectionOnto_apply_right _ ⟨_, hu⟩
  rw [← Submodule.coe_projectionOnto_apply, ← sub_add_cancel w (c • timeVectorField φ y), map_add,
    hP₁, hP₂, add_zero, sub_add_cancel]

variable [FiniteDimensional ℝ E]

/-- **The splitting `T Y_φ = ℝ T ⊕ V` of the tangent bundle of a mapping torus.** Adding a
multiple of the suspension vector field `T` to a vertical vector, `(y, a, v) ↦ (y, a + v)`, is a
smooth diffeomorphism from the total space of the direct-sum bundle `ℝ T ×ᵇ V` of the line bundle
spanned by `T` and the vertical tangent bundle `V = ker dp` onto the tangent bundle of `Y_φ`. Both
summands carry their structures as smooth subbundles of the tangent bundle
(`TauCeti.HasLocalContMDiffSubbundleFrames.fiberBundle`). -/
theorem exists_bundleDiffeomorph_prod_tangentBundle :
    letI := subbundleTopology (ℝ × E) (F' := Fin 1 → ℝ)
      fun y : SmoothMappingTorus φ ↦ ℝ ∙ timeVectorField φ y
    letI := (isContMDiffDistribution_span_timeVectorField φ).hasLocalContMDiffSubbundleFrames
      |>.fiberBundle
    letI := subbundleTopology (ℝ × E) (F' := Fin (finrank ℝ E) → ℝ)
      fun y : SmoothMappingTorus φ ↦ (mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ) (proj φ) y).ker
    letI := (isContMDiffDistribution_ker_mfderiv_proj φ (m := ∞)
      (by simp)).hasLocalContMDiffSubbundleFrames.fiberBundle
    ∃ Φ : TotalSpace ((Fin 1 → ℝ) × (Fin (finrank ℝ E) → ℝ))
          ((fun y : SmoothMappingTorus φ ↦ ℝ ∙ timeVectorField φ y) ×ᵇ
            fun y ↦ (mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ) (proj φ) y).ker)
        ≃ₘ⟮(𝓘(ℝ).prod I).prod 𝓘(ℝ, (Fin 1 → ℝ) × (Fin (finrank ℝ E) → ℝ)),
          (𝓘(ℝ).prod I).tangent⟯ TangentBundle (𝓘(ℝ).prod I) (SmoothMappingTorus φ),
      ∀ v, Φ v = ⟨v.proj, (v.snd.1 : TangentSpace (𝓘(ℝ).prod I) v.proj) + v.snd.2⟩ := by
  have : ContMDiffVectorBundle ∞ (ℝ × E)
      (TangentSpace (𝓘(ℝ).prod I) : SmoothMappingTorus φ → Type _) (𝓘(ℝ).prod I) :=
    TangentBundle.contMDiffVectorBundle
  exact (isContMDiffDistribution_span_timeVectorField φ).hasLocalContMDiffSubbundleFrames
    |>.exists_bundleDiffeomorph_prod_of_isCompl
      (isContMDiffDistribution_ker_mfderiv_proj φ (m := ∞)
        (by simp)).hasLocalContMDiffSubbundleFrames
      (isCompl_span_timeVectorField_ker_mfderiv_proj φ)

/-- **The vertical projection of a mapping torus is smooth.** The projection of the tangent bundle
onto the vertical tangent bundle `V = ker dp` along the suspension vector field `T`, which sends `w`
to `w - dt(w) T` (`TauCeti.SmoothMappingTorus.projection_ker_mfderiv_proj`), is a smooth
map of total spaces. -/
theorem contMDiff_totalSpace_projectionOnto_ker_mfderiv_proj :
    letI := subbundleTopology (ℝ × E) (F' := Fin (finrank ℝ E) → ℝ)
      fun y : SmoothMappingTorus φ ↦ (mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ) (proj φ) y).ker
    letI := (isContMDiffDistribution_ker_mfderiv_proj φ (m := ∞)
      (by simp)).hasLocalContMDiffSubbundleFrames.fiberBundle
    ContMDiff (𝓘(ℝ).prod I).tangent ((𝓘(ℝ).prod I).prod 𝓘(ℝ, Fin (finrank ℝ E) → ℝ)) ∞
      (fun w : TangentBundle (𝓘(ℝ).prod I) (SmoothMappingTorus φ) ↦
        (⟨w.proj, (mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ) (proj φ) w.proj).ker.projectionOnto
          (ℝ ∙ timeVectorField φ w.proj)
          (isCompl_span_timeVectorField_ker_mfderiv_proj φ w.proj).symm w.snd⟩ :
          TotalSpace (Fin (finrank ℝ E) → ℝ)
            fun y ↦ (mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ) (proj φ) y).ker)) := by
  have : ContMDiffVectorBundle ∞ (ℝ × E)
      (TangentSpace (𝓘(ℝ).prod I) : SmoothMappingTorus φ → Type _) (𝓘(ℝ).prod I) :=
    TangentBundle.contMDiffVectorBundle
  exact (isContMDiffDistribution_ker_mfderiv_proj φ (m := ∞)
      (by simp)).hasLocalContMDiffSubbundleFrames
    |>.contMDiff_totalSpace_projectionOnto_of_isCompl
      (isContMDiffDistribution_span_timeVectorField φ).hasLocalContMDiffSubbundleFrames
      fun y ↦ (isCompl_span_timeVectorField_ker_mfderiv_proj φ y).symm

end SmoothMappingTorus

end TauCeti
