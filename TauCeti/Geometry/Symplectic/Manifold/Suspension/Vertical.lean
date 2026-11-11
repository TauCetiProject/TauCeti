/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.MappingTorus.Vertical
public import TauCeti.Geometry.Symplectic.Manifold.Suspension.Horizontal
public import TauCeti.LinearAlgebra.BilinearForm.Orthogonal

/-!
# The vertical symplectic bundles of a symplectic suspension

Let `φ` be a diffeomorphism of a locally compact Hausdorff smooth manifold `M` preserving a
two-form `σ`, let `Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))` be its smooth mapping torus, with
projection `p : Y_φ → ℝ / ℤ`, vector field `T = ∂_t` and fiber form `σ_v`, and let
`X_φ = (ℝ / ℤ)_s × Y_φ`, with `ω_v` the pullback of `σ_v` along the projection `X_φ → Y_φ`.

The vertical tangent spaces `V_Y = ker dp` form a smooth distribution of rank `dim M` on `Y_φ`
(`TauCeti.SmoothMappingTorus.isContMDiffDistribution_ker_mfderiv_proj`). This file shows that their
pullback `V_X` to `X_φ` (`TauCeti.SmoothMappingTorus.suspensionVerticalSubspace`), the tangent
vectors with zero circle component and vertical mapping torus component, is the kernel of the
differential of the submersion `(s, y) ↦ (s, p y)` onto the torus `(ℝ / ℤ) × (ℝ / ℤ)`. So `V_X` is
a smooth distribution of rank `dim M` on `X_φ` as well, and the vertical projections along the
horizontal plane `H = span(∂_s, T)` used for pseudoholomorphic curves in `X_φ` are projections onto
the fibres of a smooth vector bundle. In the coordinates `(s, t, x)` of `ℝ × ℝ × M`, the vectors of
`V_X` at `([s], [t, x])` are exactly the vectors `0 ∂_s + 0 ∂_t + v` with `v` tangent to `M` at `x`,
and `ω_v` evaluates on `a ∂_s + b ∂_t + v` and `a' ∂_s + b' ∂_t + v'` as `σ(v, v')`.

When `σ` is nondegenerate, both vertical bundles are symplectic vector bundles. On `Y_φ` the kernel
of `σ_v` is the line spanned by `T` (`TauCeti.SmoothMappingTorus.ker_bilinFormAt_fiberForm`), which
is complementary to `V_Y`, so `σ_v` is nondegenerate on every fibre of `V_Y`. On `X_φ` the kernel of
`ω_v` is exactly the horizontal plane `H`, which is complementary to `V_X`, so `ω_v` is
nondegenerate on every fibre of `V_X`. This is the symplectic structure against which the
restriction of a block almost complex structure to `V_X` is tamed.

## Main results

* `TauCeti.SmoothMappingTorus.suspensionVerticalSubspace_eq_ker_mfderiv`: `V_X` is the kernel of
  the differential of `(s, y) ↦ (s, p y)`.
* `TauCeti.SmoothMappingTorus.isContMDiffDistribution_suspensionVerticalSubspace`: `V_X` is a
  `C^m` distribution of rank `dim M` for every `m ≤ ∞`.
* `TauCeti.SmoothMappingTorus.symm_tangentSpaceProdEquiv_mem_suspensionVerticalSubspace_iff`,
  `TauCeti.SmoothMappingTorus.mem_suspensionVerticalSubspace_mk_iff`: the vectors of `V_X` in the
  coordinates `(s, t, x)`.
* `TauCeti.SmoothMappingTorus.eval₂_mpullback_snd_fiberForm_mk`: `ω_v` in the coordinates
  `(s, t, x)`.
* `TauCeti.SmoothMappingTorus.nondegenerate_restrict_bilinFormAt_fiberForm`: `σ_v` is
  nondegenerate on `V_Y`.
* `TauCeti.SmoothMappingTorus.ker_bilinFormAt_mpullback_snd_fiberForm`: the kernel of `ω_v` is the
  horizontal plane `H`.
* `TauCeti.SmoothMappingTorus.nondegenerate_restrict_bilinFormAt_mpullback_snd_fiberForm`: `ω_v`
  is nondegenerate on `V_X`.

## References

* Michael Hutchings and Michael Sullivan, *The periodic Floer homology of a Dehn twist*, Algebraic
  & Geometric Topology 5 (2005), 301–354, Section 2 (the vertical tangent bundle of a mapping torus
  and the symplectic suspension).
-/

public section

open Function Manifold Module
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothMappingTorus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [LocallyCompactSpace M] [IsManifold I ∞ M]
  (φ : M ≃ₘ⟮I, I⟯ M)

/-! ### The vertical distribution of `X_φ` -/

/-- The vertical space `V_X` of `X_φ = (ℝ / ℤ) × Y_φ` at `q` is the kernel of the differential of
the map `(s, y) ↦ (s, p y)` to the torus `(ℝ / ℤ) × (ℝ / ℤ)`. -/
theorem suspensionVerticalSubspace_eq_ker_mfderiv (q : UnitAddCircle × SmoothMappingTorus φ) :
    suspensionVerticalSubspace φ q =
      (mfderiv (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (𝓘(ℝ).prod 𝓘(ℝ)) (Prod.map id (proj φ)) q).ker := by
  ext ξ
  obtain ⟨v, rfl⟩ :=
    (Manifold.tangentSpaceProdEquiv (I := 𝓘(ℝ)) (J := 𝓘(ℝ).prod I) q).symm.surjective ξ
  simp only [mem_suspensionVerticalSubspace_iff, ContinuousLinearEquiv.apply_symm_apply,
    LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    Manifold.mfderiv_prodMap_apply mdifferentiableAt_id
      ((contMDiff_proj φ).mdifferentiableAt (by simp)),
    ContinuousLinearEquiv.map_eq_zero_iff, mfderiv_id, ContinuousLinearMap.id_apply,
    Prod.mk_eq_zero]

/-- **The vertical distribution of a symplectic suspension.** The vertical spaces `V_X` of
`X_φ = (ℝ / ℤ) × Y_φ` form a `C^m` distribution of rank `dim M` for every `m ≤ ∞`. -/
theorem isContMDiffDistribution_suspensionVerticalSubspace [FiniteDimensional ℝ E] {m : ℕ∞ω}
    (hm : m + 1 ≤ ∞) :
    IsContMDiffDistribution (𝓘(ℝ).prod (𝓘(ℝ).prod I)) m (finrank ℝ E)
      (suspensionVerticalSubspace φ) := by
  have hid : IsSubmersionOfComplement PUnit.{1} 𝓘(ℝ) 𝓘(ℝ) ∞ (@id UnitAddCircle) :=
    IsSubmersionOfComplement.id
  have h := (hid.prodMap
    (isSubmersionOfComplement_proj φ)).isSubmersion.isContMDiffDistribution_ker_mfderiv hm
  rw [funext (suspensionVerticalSubspace_eq_ker_mfderiv φ)]
  -- The rank is `dim (ℝ × (ℝ × E)) - dim (ℝ × ℝ) = dim E`.
  rwa [finrank_prod, finrank_prod, finrank_prod, finrank_self,
    show 1 + (1 + finrank ℝ E) - (1 + 1) = finrank ℝ E by omega] at h

variable {φ}

/-! ### The vertical space and the fiber form in the coordinates `(s, t, x)` -/

/-- In the coordinates `(s, t, x)`, the tangent vector `a ∂_s + b ∂_t + v` of
`X_φ = (ℝ / ℤ) × Y_φ` at `(θ, [t, x])` is vertical exactly when `a` and `b` vanish. -/
theorem symm_tangentSpaceProdEquiv_mem_suspensionVerticalSubspace_iff (θ : UnitAddCircle) (t : ℝ)
    (x : M) (a b : ℝ) (v : TangentSpace I x) :
    (Manifold.tangentSpaceProdEquiv (I := 𝓘(ℝ)) (J := 𝓘(ℝ).prod I) (θ, mk φ t x)).symm
        (a, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
          ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, v))) ∈
        suspensionVerticalSubspace φ (θ, mk φ t x) ↔
      a = 0 ∧ b = 0 := by
  rw [mem_suspensionVerticalSubspace_iff, ContinuousLinearEquiv.apply_symm_apply]
  -- The circle component is `a`, and `dp` sends the mapping torus component to `b`.
  dsimp only
  rw [mfderiv_proj_mfderiv_uncurry_mk]
  exact Iff.rfl

/-- At `(θ, [t, x])`, a tangent vector of `X_φ = (ℝ / ℤ) × Y_φ` is vertical exactly when, in the
coordinates `(s, t, x)`, it is `0 ∂_s + 0 ∂_t + v` for a tangent vector `v` of `M` at `x`. -/
theorem mem_suspensionVerticalSubspace_mk_iff {θ : UnitAddCircle} {t : ℝ} {x : M}
    {ξ : TangentSpace (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (θ, mk φ t x)} :
    ξ ∈ suspensionVerticalSubspace φ (θ, mk φ t x) ↔
      ∃ v : TangentSpace I x, ξ = (Manifold.tangentSpaceProdEquiv _).symm
        ((0 : ℝ), mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
          ((Manifold.tangentSpaceProdEquiv (t, x)).symm ((0 : ℝ), v))) := by
  refine ⟨fun hξ ↦ ?_, fun ⟨v, hv⟩ ↦ hv ▸
    (symm_tangentSpaceProdEquiv_mem_suspensionVerticalSubspace_iff θ t x 0 0 v).2 ⟨rfl, rfl⟩⟩
  obtain ⟨a, b, v, rfl⟩ := exists_eq_symm_tangentSpaceProdEquiv θ t x ξ
  obtain ⟨rfl, rfl⟩ :=
    (symm_tangentSpaceProdEquiv_mem_suspensionVerticalSubspace_iff θ t x a b v).1 hξ
  exact ⟨v, rfl⟩

/-- In the coordinates `(s, t, x)` of `ℝ × ℝ × M`, the fiber form `τ_v` pulled back to `X_φ` is
`τ`: at `(θ, [t, x])` it pairs `a ∂_s + b ∂_t + v` with `a' ∂_s + b' ∂_t + v'` to `τ(v, v')`. -/
theorem eval₂_mpullback_snd_fiberForm_mk {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {τ : SmoothForm I M F 2} {hτ : SmoothForm.mpullback φ φ.contMDiff τ = τ} (θ : UnitAddCircle)
    (t : ℝ) (x : M) (a a' b b' : ℝ) (v v' : TangentSpace I x) :
    SmoothBundleForm.eval₂ (SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ τ hτ))
        (θ, mk φ t x)
        ((Manifold.tangentSpaceProdEquiv (I := 𝓘(ℝ)) (J := 𝓘(ℝ).prod I) _).symm
          (a, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
            ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, v))))
        ((Manifold.tangentSpaceProdEquiv _).symm
          (a', mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
            ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b', v')))) =
      SmoothBundleForm.eval₂ τ x v v' := by
  rw [SmoothForm.eval₂_mpullback_snd]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  rw [eval₂_fiberForm_mfderiv_uncurry_mk]
  simp only [ContinuousLinearEquiv.apply_symm_apply]

/-! ### Nondegeneracy on the vertical bundles -/

variable {σ : SmoothTwoForm I M} {hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ}

/-- The fiber form `σ_v` of a nondegenerate two-form `σ` preserved by `φ` is nondegenerate on the
vertical tangent space `ker dp` at every point of the mapping torus. -/
theorem nondegenerate_restrict_bilinFormAt_fiberForm (h : σ.IsNondegenerate)
    (y : SmoothMappingTorus φ) :
    (((fiberForm φ σ hσ).bilinFormAt y).restrict
      (mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ) (proj φ) y).ker).Nondegenerate :=
  LinearMap.BilinForm.IsRefl.nondegenerate_restrict_of_isCompl_ker
    (SmoothForm.isAlt_bilinFormAt _ y).isRefl
    (ker_bilinFormAt_fiberForm (hσ := hσ) h y ▸
      (isCompl_span_timeVectorField_ker_mfderiv_proj φ y).symm)

/-- For a nondegenerate two-form `σ` preserved by `φ`, the kernel of the pulled back fiber form
`ω_v` at a point of `X_φ = (ℝ / ℤ) × Y_φ` is the horizontal plane `H = span(∂_s, T)`. -/
theorem ker_bilinFormAt_mpullback_snd_fiberForm (h : σ.IsNondegenerate)
    (q : UnitAddCircle × SmoothMappingTorus φ) :
    LinearMap.ker ((SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ σ hσ)).bilinFormAt q) =
      suspensionHorizontalSubspace φ q := by
  rw [SmoothTwoForm.ker_bilinFormAt_mpullback contMDiff_snd _
    (by rw [mfderiv_snd]; exact LinearMap.snd_surjective), ker_bilinFormAt_fiberForm h]
  -- Both sides ask that the mapping torus component of `ξ` lie in `ℝ ∙ T`.
  ext ξ
  rw [mem_suspensionHorizontalSubspace_iff, Submodule.mem_comap, mfderiv_snd,
    Manifold.tangentSpaceProdEquiv_apply]
  -- `TangentSpace (I.prod J) q` is by definition the product of the factor tangent spaces, so
  -- `ContinuousLinearMap.snd` applied to `ξ` unfolds to `ξ.2`. Rewriting with
  -- `ContinuousLinearMap.coe_snd'` fails, as its domain is only definitionally the type of `ξ`.
  rfl

/-- The pulled back fiber form `ω_v` of a nondegenerate two-form `σ` preserved by `φ` is
nondegenerate on the vertical space `V_X` at every point of `X_φ = (ℝ / ℤ) × Y_φ`. -/
theorem nondegenerate_restrict_bilinFormAt_mpullback_snd_fiberForm (h : σ.IsNondegenerate)
    (q : UnitAddCircle × SmoothMappingTorus φ) :
    (((SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ σ hσ)).bilinFormAt q).restrict
      (suspensionVerticalSubspace φ q)).Nondegenerate :=
  LinearMap.BilinForm.IsRefl.nondegenerate_restrict_of_isCompl_ker
    (SmoothForm.isAlt_bilinFormAt _ q).isRefl
    (ker_bilinFormAt_mpullback_snd_fiberForm h q ▸
      isCompl_suspensionVerticalSubspace_suspensionHorizontalSubspace φ q)

end SmoothMappingTorus

end TauCeti
