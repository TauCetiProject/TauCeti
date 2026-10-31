/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Projection
public import TauCeti.Geometry.Manifold.Orientation.Basic
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic
public import TauCeti.Geometry.Symplectic.Manifold.Suspension.Basic

/-!
# Horizontal tangent planes and the vertical energy density of a symplectic suspension

Let `φ` be a diffeomorphism of a locally compact Hausdorff smooth manifold `M`, let
`Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))` be its smooth mapping torus, with projection
`p : Y_φ → ℝ / ℤ`, vector field `T = ∂_t` and fiber form `σ_v` of a `φ`-invariant two-form `σ`, and
let `X_φ = (ℝ / ℤ)_s × Y_φ`. At each point of `X_φ` this file splits the tangent space as

`T X_φ = H ⊕ V`,

where the *horizontal plane* `H = span(∂_s, T)`
(`TauCeti.SmoothMappingTorus.suspensionHorizontalSubspace`) consists of the vectors whose mapping
torus component is a multiple of `T`, and the *vertical space* `V`
(`TauCeti.SmoothMappingTorus.suspensionVerticalSubspace`) is the pullback along the projection
`X_φ → Y_φ` of the vertical tangent space `ker dp` of the mapping torus. The vertical component
`ξ_V` of a tangent vector `ξ` is its image under Mathlib's projection
`Submodule.projection` onto `V` along `H`.

Write `ω_v` for the fiber form `σ_v` pulled back to `X_φ`. Since `ω_v` kills both `∂_s` and `T`,
it only sees vertical components: `ω_v(ξ, η) = ω_v(ξ_V, η_V)`. Now let `J` be a smooth almost
complex structure on `X_φ` of *block* form at a point: `J ∂_s = T` (hence `J T = -∂_s`) and `J`
preserves `V`. Then `J` preserves `H` too, and

`ω_v(ξ, J ξ) = ω_v(ξ_V, J ξ_V)`

(`TauCeti.SmoothMappingTorus.eval₂_mpullback_snd_fiberForm_apply_eq_projection`).
If moreover `ω_v` tames the restriction of `J` to `V`, this is nonnegative, and it vanishes exactly
when `ξ` is horizontal. For a smooth map `u` from an almost complex manifold `(C, j)` that is
pseudoholomorphic at `c`, the Cauchy–Riemann equation `du (j e) = J (du e)` turns this into the
pointwise identity for the vertical energy density

`(u^* ω_v)(e, j e) = ω_v((du e)_V, J (du e)_V) ≥ 0`,

with equality exactly when `du e` lies in the horizontal plane
(`TauCeti.SmoothMappingTorus.eval₂_mpullback_mpullback_snd_fiberForm_apply_eq_zero_iff`).
These pointwise statements are the local input to the classification of compact
pseudoholomorphic curves of zero `ω_v`-area in `X_φ` as tori `(ℝ / ℤ) × γ` over closed orbits `γ`
of the suspension flow. The block hypotheses are imposed only at the points used, and no
compatibility of `J` with the full symplectic form `Ω = ds ∧ dt + σ_v` is needed.

## Main definitions

* `TauCeti.SmoothMappingTorus.suspensionHorizontalSubspace φ q`: the plane `H = span(∂_s, T)`
  at `q`.
* `TauCeti.SmoothMappingTorus.suspensionVerticalSubspace φ q`: the vertical space `V`, the pullback
  of `ker dp`.

## Main results

* `TauCeti.SmoothMappingTorus.suspensionHorizontalSubspace_eq_span`: `H` is the span of `∂_s`
  and `T`.
* `TauCeti.SmoothMappingTorus.isCompl_suspensionVerticalSubspace_suspensionHorizontalSubspace`:
  `T X_φ = V ⊕ H`.
* `TauCeti.SmoothMappingTorus.eval₂_mpullback_snd_fiberForm_projection_projection`: `ω_v` only sees
  vertical components.
* `TauCeti.SmoothMappingTorus.apply_mem_suspensionHorizontalSubspace`: a block structure
  preserves `H`.
* `TauCeti.SmoothMappingTorus.eval₂_mpullback_snd_fiberForm_apply_eq_projection`:
  `ω_v(ξ, J ξ) = ω_v(ξ_V, J ξ_V)` for a block structure.
* `TauCeti.SmoothMappingTorus.eval₂_mpullback_snd_fiberForm_apply_nonneg`,
  `TauCeti.SmoothMappingTorus.eval₂_mpullback_snd_fiberForm_apply_eq_zero_iff`: under vertical
  tameness, `ω_v(ξ, J ξ) ≥ 0`, with equality exactly for horizontal `ξ`.
* `TauCeti.SmoothMappingTorus.eval₂_mpullback_mpullback_snd_fiberForm_apply_eq_projection`,
  `TauCeti.SmoothMappingTorus.eval₂_mpullback_mpullback_snd_fiberForm_apply_nonneg`,
  `TauCeti.SmoothMappingTorus.eval₂_mpullback_mpullback_snd_fiberForm_apply_eq_zero_iff`: the
  vertical energy density of a pseudoholomorphic map.
* `TauCeti.SmoothMappingTorus.mpullback_mpullback_snd_fiberForm_apply_basis_nonneg`: on a surface
  oriented so that the frames `(e, j e)` are positive, the top form `u^* ω_v` is nonnegative on
  positively oriented frames.
* `TauCeti.SmoothMappingTorus.mpullback_mpullback_snd_fiberForm_eq_zero`: `ω_v` pulls back to zero
  along a map whose tangent images are horizontal.

## References

* Michael Hutchings and Michael Sullivan, *The periodic Floer homology of a Dehn twist*, Algebraic
  & Geometric Topology 5 (2005), 301–354 (block almost complex structures on `ℝ × Y_φ` and the
  pointwise nonnegativity of `ω_φ` on their holomorphic curves).
* Eleny-Nicoleta Ionel and Thomas H. Parker, *Gromov invariants and symplectic maps*,
  Mathematische Annalen 314 (1999), 127–158 (pseudoholomorphic tori over periodic orbits in
  `S¹ × Y_φ`).
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothMappingTorus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [LocallyCompactSpace M]
  (φ : M ≃ₘ⟮I, I⟯ M)

/-! ### The horizontal and vertical subspaces -/

/-- The horizontal plane `H = span(∂_s, T)` of `X_φ = (ℝ / ℤ)_s × Y_φ` at `q`: the tangent vectors
whose mapping torus component is a multiple of the vector field `T = ∂_t`. -/
def suspensionHorizontalSubspace (q : UnitAddCircle × SmoothMappingTorus φ) :
    Submodule ℝ (TangentSpace (𝓘(ℝ).prod (𝓘(ℝ).prod I)) q) :=
  ((⊤ : Submodule ℝ (TangentSpace 𝓘(ℝ) q.1)).prod (ℝ ∙ timeVectorField φ q.2)).comap
    (Manifold.tangentSpaceProdEquiv (I := 𝓘(ℝ)) (J := 𝓘(ℝ).prod I) q).toLinearEquiv.toLinearMap

/-- The vertical space `V` of `X_φ = (ℝ / ℤ)_s × Y_φ` at `q`: the pullback along the projection
`X_φ → Y_φ` of the vertical tangent space `ker dp` of the mapping torus, so the tangent vectors
with zero circle component and vertical mapping torus component. -/
def suspensionVerticalSubspace (q : UnitAddCircle × SmoothMappingTorus φ) :
    Submodule ℝ (TangentSpace (𝓘(ℝ).prod (𝓘(ℝ).prod I)) q) :=
  ((⊥ : Submodule ℝ (TangentSpace 𝓘(ℝ) q.1)).prod
      (mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ) (proj φ) q.2).ker).comap
    (Manifold.tangentSpaceProdEquiv (I := 𝓘(ℝ)) (J := 𝓘(ℝ).prod I) q).toLinearEquiv.toLinearMap

variable {φ} {q : UnitAddCircle × SmoothMappingTorus φ}
  {ξ : TangentSpace (𝓘(ℝ).prod (𝓘(ℝ).prod I)) q}

/-- A tangent vector of `X_φ` is horizontal exactly when its mapping torus component is a multiple
of `T`. -/
@[simp]
theorem mem_suspensionHorizontalSubspace_iff :
    ξ ∈ suspensionHorizontalSubspace φ q ↔
      (Manifold.tangentSpaceProdEquiv q ξ).2 ∈ ℝ ∙ timeVectorField φ q.2 := by
  simp only [suspensionHorizontalSubspace, Submodule.mem_comap, Submodule.mem_prod,
    Submodule.mem_top, true_and, LinearEquiv.coe_toLinearMap,
    ContinuousLinearEquiv.coe_toLinearEquiv]

/-- A tangent vector of `X_φ` is vertical exactly when its circle component vanishes and its
mapping torus component is vertical. -/
@[simp]
theorem mem_suspensionVerticalSubspace_iff :
    ξ ∈ suspensionVerticalSubspace φ q ↔
      (Manifold.tangentSpaceProdEquiv q ξ).1 = 0 ∧
        mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ) (proj φ) q.2 (Manifold.tangentSpaceProdEquiv q ξ).2 = 0 := by
  simp only [suspensionVerticalSubspace, Submodule.mem_comap, Submodule.mem_prod, Submodule.mem_bot,
    LinearMap.mem_ker, LinearEquiv.coe_toLinearMap, ContinuousLinearEquiv.coe_toLinearEquiv,
    ContinuousLinearMap.coe_coe]

variable (φ q) in
/-- The vector `∂_s` of the circle factor is horizontal. -/
theorem symm_one_zero_mem_suspensionHorizontalSubspace :
    (Manifold.tangentSpaceProdEquiv q).symm ((1 : ℝ), 0) ∈ suspensionHorizontalSubspace φ q := by
  rw [mem_suspensionHorizontalSubspace_iff, ContinuousLinearEquiv.apply_symm_apply]
  exact Submodule.zero_mem _

variable (φ q) in
/-- The vector field `T` of the mapping torus factor is horizontal. -/
theorem symm_zero_timeVectorField_mem_suspensionHorizontalSubspace :
    (Manifold.tangentSpaceProdEquiv q).symm ((0 : ℝ), timeVectorField φ q.2) ∈
      suspensionHorizontalSubspace φ q := by
  rw [mem_suspensionHorizontalSubspace_iff, ContinuousLinearEquiv.apply_symm_apply]
  exact Submodule.mem_span_singleton_self _

variable (φ q) in
/-- The horizontal plane is the span of `∂_s` and `T`. -/
theorem suspensionHorizontalSubspace_eq_span :
    suspensionHorizontalSubspace φ q = Submodule.span ℝ
      {(Manifold.tangentSpaceProdEquiv q).symm ((1 : ℝ), 0),
        (Manifold.tangentSpaceProdEquiv q).symm ((0 : ℝ), timeVectorField φ q.2)} := by
  refine le_antisymm (fun ξ hξ ↦ Submodule.mem_span_pair.2 ?_) (Submodule.span_le.2 ?_)
  · set e := Manifold.tangentSpaceProdEquiv (I := 𝓘(ℝ)) (J := 𝓘(ℝ).prod I) q
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 (mem_suspensionHorizontalSubspace_iff.1 hξ)
    -- The circle tangent space `TangentSpace 𝓘(ℝ) q.1` is `ℝ` by definition, so the circle
    -- component of `ξ` is a real number `a`, the coefficient of `∂_s`.
    obtain ⟨a, ha⟩ : ∃ a : ℝ, (e ξ).1 = a := ⟨_, rfl⟩
    refine ⟨a, b, e.injective ?_⟩
    rw [map_add, map_smul, map_smul, e.apply_symm_apply, e.apply_symm_apply]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.smul_fst, ha]
      -- In `ℝ`, the scalar action is multiplication.
      exact (show a * 1 + b * 0 = a by ring)
    · simp only [Prod.snd_add, Prod.smul_snd, smul_zero, zero_add]
      exact hb
  · exact Set.insert_subset (symm_one_zero_mem_suspensionHorizontalSubspace φ q)
      (Set.singleton_subset_iff.2 (symm_zero_timeVectorField_mem_suspensionHorizontalSubspace φ q))

variable [IsManifold I ∞ M]

variable (φ q) in
/-- The tangent space of `X_φ` is the direct sum `V ⊕ H` of the vertical space and the horizontal
plane `span(∂_s, T)`. -/
theorem isCompl_suspensionVerticalSubspace_suspensionHorizontalSubspace :
    IsCompl (suspensionVerticalSubspace φ q) (suspensionHorizontalSubspace φ q) := by
  have hY := isCompl_span_timeVectorField_ker_mfderiv_proj φ q.2
  set e := Manifold.tangentSpaceProdEquiv (I := 𝓘(ℝ)) (J := 𝓘(ℝ).prod I) q
  refine ⟨Submodule.disjoint_def.2 fun ξ hV hH ↦ ?_, codisjoint_iff.2 ?_⟩
  · rw [mem_suspensionVerticalSubspace_iff] at hV
    rw [mem_suspensionHorizontalSubspace_iff] at hH
    -- The mapping torus component lies in `ℝ T ⊓ ker dp = 0`.
    have h₂ : (e ξ).2 = 0 := Submodule.disjoint_def.1 hY.disjoint _ hH (LinearMap.mem_ker.2 hV.2)
    exact e.map_eq_zero_iff.1 (Prod.ext hV.1 h₂)
  · refine Submodule.eq_top_iff'.2 fun ξ ↦ ?_
    -- Split the mapping torus component as `w = c T + w_V`, and put `∂_s` in the horizontal part.
    obtain ⟨c, hc, w, hw, hcw⟩ :=
      Submodule.mem_sup.1 (hY.sup_eq_top.symm ▸ Submodule.mem_top : (e ξ).2 ∈ _)
    refine Submodule.mem_sup.2 ⟨e.symm (0, w), ?_, e.symm ((e ξ).1, c), ?_, ?_⟩
    · rw [mem_suspensionVerticalSubspace_iff, ContinuousLinearEquiv.apply_symm_apply]
      exact ⟨rfl, hw⟩
    · rw [mem_suspensionHorizontalSubspace_iff, ContinuousLinearEquiv.apply_symm_apply]
      exact hc
    · rw [← map_add, e.symm_apply_eq]
      exact Prod.ext (zero_add _) ((add_comm _ _).trans hcw)

/-! ### The pulled back fiber form and vertical components -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {σ : SmoothForm I M F 2}
  {hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ}

/-- The fiber form `σ_v`, pulled back to `X_φ`, vanishes when a horizontal vector fills its first
slot. -/
theorem eval₂_mpullback_snd_fiberForm_of_mem_suspensionHorizontalSubspace_left
    (hξ : ξ ∈ suspensionHorizontalSubspace φ q) (η : TangentSpace (𝓘(ℝ).prod (𝓘(ℝ).prod I)) q) :
    SmoothBundleForm.eval₂ (SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ σ hσ)) q ξ
      η = 0 := by
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 (mem_suspensionHorizontalSubspace_iff.1 hξ)
  rw [SmoothForm.eval₂_mpullback_snd, ← hb, SmoothBundleForm.eval₂_smul_left,
    eval₂_fiberForm_timeVectorField_left, smul_zero]

/-- The fiber form `σ_v`, pulled back to `X_φ`, vanishes when a horizontal vector fills its second
slot. -/
theorem eval₂_mpullback_snd_fiberForm_of_mem_suspensionHorizontalSubspace_right
    (η : TangentSpace (𝓘(ℝ).prod (𝓘(ℝ).prod I)) q) (hξ : ξ ∈ suspensionHorizontalSubspace φ q) :
    SmoothBundleForm.eval₂ (SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ σ hσ)) q η
      ξ = 0 := by
  rw [SmoothBundleForm.eval₂_swap,
    eval₂_mpullback_snd_fiberForm_of_mem_suspensionHorizontalSubspace_left hξ, neg_zero]

/-- The fiber form `σ_v`, pulled back to `X_φ`, only sees vertical components:
`ω_v(ξ, η) = ω_v(ξ_V, η_V)`. -/
theorem eval₂_mpullback_snd_fiberForm_projection_projection
    (ξ η : TangentSpace (𝓘(ℝ).prod (𝓘(ℝ).prod I)) q) :
    SmoothBundleForm.eval₂ (SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ σ hσ)) q
        ((suspensionVerticalSubspace φ q).projection (suspensionHorizontalSubspace φ q)
          (isCompl_suspensionVerticalSubspace_suspensionHorizontalSubspace φ q) ξ)
        ((suspensionVerticalSubspace φ q).projection (suspensionHorizontalSubspace φ q)
          (isCompl_suspensionVerticalSubspace_suspensionHorizontalSubspace φ q) η) =
      SmoothBundleForm.eval₂ (SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ σ hσ)) q
        ξ η := by
  set hc := isCompl_suspensionVerticalSubspace_suspensionHorizontalSubspace φ q
  -- Split both vectors into their vertical and horizontal components.
  conv_rhs => rw [← Submodule.projection_add_projection_eq_self hc ξ,
    ← Submodule.projection_add_projection_eq_self hc η]
  have hH (ζ : TangentSpace (𝓘(ℝ).prod (𝓘(ℝ).prod I)) q) :
      (suspensionHorizontalSubspace φ q).projection (suspensionVerticalSubspace φ q) hc.symm ζ ∈
        suspensionHorizontalSubspace φ q :=
    Submodule.projection_apply_mem _ _
  rw [SmoothBundleForm.eval₂_add_left, SmoothBundleForm.eval₂_add_right,
    SmoothBundleForm.eval₂_add_right,
    eval₂_mpullback_snd_fiberForm_of_mem_suspensionHorizontalSubspace_right _ (hH η),
    eval₂_mpullback_snd_fiberForm_of_mem_suspensionHorizontalSubspace_left (hH ξ),
    eval₂_mpullback_snd_fiberForm_of_mem_suspensionHorizontalSubspace_left (hH ξ)]
  simp

/-! ### Block almost complex structures -/

variable {J : SmoothAlmostComplexStructure (𝓘(ℝ).prod (𝓘(ℝ).prod I))
  (UnitAddCircle × SmoothMappingTorus φ)}

/-- An almost complex structure with `J ∂_s = T` sends `T` to `-∂_s`. -/
theorem apply_symm_zero_timeVectorField
    (hS : J q ((Manifold.tangentSpaceProdEquiv q).symm ((1 : ℝ), 0)) =
      (Manifold.tangentSpaceProdEquiv q).symm ((0 : ℝ), timeVectorField φ q.2)) :
    J q ((Manifold.tangentSpaceProdEquiv q).symm ((0 : ℝ), timeVectorField φ q.2)) =
      -(Manifold.tangentSpaceProdEquiv q).symm ((1 : ℝ), 0) := by
  rw [← hS, SmoothAlmostComplexStructure.apply_apply]

/-- An almost complex structure with `J ∂_s = T` preserves the horizontal plane `span(∂_s, T)`. -/
theorem apply_mem_suspensionHorizontalSubspace
    (hS : J q ((Manifold.tangentSpaceProdEquiv q).symm ((1 : ℝ), 0)) =
      (Manifold.tangentSpaceProdEquiv q).symm ((0 : ℝ), timeVectorField φ q.2))
    (hξ : ξ ∈ suspensionHorizontalSubspace φ q) : J q ξ ∈ suspensionHorizontalSubspace φ q := by
  rw [suspensionHorizontalSubspace_eq_span, Submodule.mem_span_pair] at hξ ⊢
  obtain ⟨a, b, rfl⟩ := hξ
  -- `J (a ∂_s + b T) = a T - b ∂_s`.
  have hJ : J q (a • (Manifold.tangentSpaceProdEquiv q).symm ((1 : ℝ), 0) +
      b • (Manifold.tangentSpaceProdEquiv q).symm ((0 : ℝ), timeVectorField φ q.2)) =
      a • J q ((Manifold.tangentSpaceProdEquiv q).symm ((1 : ℝ), 0)) +
        b • J q ((Manifold.tangentSpaceProdEquiv q).symm ((0 : ℝ), timeVectorField φ q.2)) := by
    -- `J q` is the underlying continuous linear endomorphism of the tangent space.
    rw [← map_smul (J.toEndomorphism q), ← map_smul (J.toEndomorphism q),
      ← map_add (J.toEndomorphism q)]
  rw [hJ, hS, apply_symm_zero_timeVectorField hS]
  exact ⟨-b, a, by rw [smul_neg, neg_smul, add_comm]⟩

/-- For an almost complex structure of block form at `q`, with `J ∂_s = T` and `J V ⊆ V`, the
fiber form `σ_v` pulled back to `X_φ` evaluates on `ξ` and `J ξ` through the vertical component:
`ω_v(ξ, J ξ) = ω_v(ξ_V, J ξ_V)`. -/
theorem eval₂_mpullback_snd_fiberForm_apply_eq_projection
    (hS : J q ((Manifold.tangentSpaceProdEquiv q).symm ((1 : ℝ), 0)) =
      (Manifold.tangentSpaceProdEquiv q).symm ((0 : ℝ), timeVectorField φ q.2))
    (hV : ∀ v ∈ suspensionVerticalSubspace φ q, J q v ∈ suspensionVerticalSubspace φ q)
    (ξ : TangentSpace (𝓘(ℝ).prod (𝓘(ℝ).prod I)) q) :
    SmoothBundleForm.eval₂ (SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ σ hσ)) q ξ
        (J q ξ) =
      SmoothBundleForm.eval₂ (SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ σ hσ)) q
        ((suspensionVerticalSubspace φ q).projection (suspensionHorizontalSubspace φ q)
          (isCompl_suspensionVerticalSubspace_suspensionHorizontalSubspace φ q) ξ)
        (J q ((suspensionVerticalSubspace φ q).projection (suspensionHorizontalSubspace φ q)
          (isCompl_suspensionVerticalSubspace_suspensionHorizontalSubspace φ q) ξ)) := by
  set hc := isCompl_suspensionVerticalSubspace_suspensionHorizontalSubspace φ q
  set v := (suspensionVerticalSubspace φ q).projection (suspensionHorizontalSubspace φ q) hc ξ
  set h := (suspensionHorizontalSubspace φ q).projection (suspensionVerticalSubspace φ q) hc.symm ξ
  have hv : v ∈ suspensionVerticalSubspace φ q := Submodule.projection_apply_mem _ _
  have hh : h ∈ suspensionHorizontalSubspace φ q := Submodule.projection_apply_mem _ _
  -- Write `ξ = v + h`; then `J ξ = J v + J h` with `J v` vertical and `J h` horizontal.
  have hξ : ξ = v + h := (Submodule.projection_add_projection_eq_self hc ξ).symm
  have hJ : J q ξ = J q v + J q h := by
    rw [hξ]
    -- `J q` is the underlying continuous linear endomorphism of the tangent space.
    exact map_add (J.toEndomorphism q) v h
  have hJv : (suspensionVerticalSubspace φ q).projection (suspensionHorizontalSubspace φ q) hc
      (J q v) = J q v :=
    Submodule.projection_apply_of_mem_left hc (hV v hv)
  have hJh : (suspensionVerticalSubspace φ q).projection (suspensionHorizontalSubspace φ q) hc
      (J q h) = 0 :=
    (Submodule.projection_apply_eq_zero_iff hc).2 (apply_mem_suspensionHorizontalSubspace hS hh)
  rw [← eval₂_mpullback_snd_fiberForm_projection_projection ξ (J q ξ), hJ, map_add, hJv, hJh,
    add_zero]

/-- For an almost complex structure of block form at `q` whose restriction to the vertical space is
tamed by `ω_v`, the fiber form `σ_v` pulled back to `X_φ` is nonnegative on `ξ` and `J ξ`. -/
theorem eval₂_mpullback_snd_fiberForm_apply_nonneg {σ : SmoothTwoForm I M}
    {hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ}
    (hS : J q ((Manifold.tangentSpaceProdEquiv q).symm ((1 : ℝ), 0)) =
      (Manifold.tangentSpaceProdEquiv q).symm ((0 : ℝ), timeVectorField φ q.2))
    (hV : ∀ v ∈ suspensionVerticalSubspace φ q, J q v ∈ suspensionVerticalSubspace φ q)
    (htame : ∀ v ∈ suspensionVerticalSubspace φ q, v ≠ 0 →
      0 < SmoothBundleForm.eval₂ (SmoothForm.mpullback Prod.snd contMDiff_snd
        (fiberForm φ σ hσ)) q v (J q v))
    (ξ : TangentSpace (𝓘(ℝ).prod (𝓘(ℝ).prod I)) q) :
    0 ≤ SmoothBundleForm.eval₂ (SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ σ hσ)) q ξ
      (J q ξ) := by
  rw [eval₂_mpullback_snd_fiberForm_apply_eq_projection hS hV]
  set v := (suspensionVerticalSubspace φ q).projection (suspensionHorizontalSubspace φ q)
    (isCompl_suspensionVerticalSubspace_suspensionHorizontalSubspace φ q) ξ
  rcases eq_or_ne v 0 with hv | hv
  · rw [hv,
      eval₂_mpullback_snd_fiberForm_of_mem_suspensionHorizontalSubspace_left (Submodule.zero_mem _)]
  · exact (htame v (Submodule.projection_apply_mem _ _) hv).le

/-- For an almost complex structure of block form at `q` whose restriction to the vertical space is
tamed by `ω_v`, the value `ω_v(ξ, J ξ)` vanishes exactly when `ξ` lies in the horizontal plane
`span(∂_s, T)`. -/
theorem eval₂_mpullback_snd_fiberForm_apply_eq_zero_iff {σ : SmoothTwoForm I M}
    {hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ}
    (hS : J q ((Manifold.tangentSpaceProdEquiv q).symm ((1 : ℝ), 0)) =
      (Manifold.tangentSpaceProdEquiv q).symm ((0 : ℝ), timeVectorField φ q.2))
    (hV : ∀ v ∈ suspensionVerticalSubspace φ q, J q v ∈ suspensionVerticalSubspace φ q)
    (htame : ∀ v ∈ suspensionVerticalSubspace φ q, v ≠ 0 →
      0 < SmoothBundleForm.eval₂ (SmoothForm.mpullback Prod.snd contMDiff_snd
        (fiberForm φ σ hσ)) q v (J q v))
    (ξ : TangentSpace (𝓘(ℝ).prod (𝓘(ℝ).prod I)) q) :
    SmoothBundleForm.eval₂ (SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ σ hσ)) q ξ
        (J q ξ) = 0 ↔ ξ ∈ suspensionHorizontalSubspace φ q := by
  set hc := isCompl_suspensionVerticalSubspace_suspensionHorizontalSubspace φ q
  rw [eval₂_mpullback_snd_fiberForm_apply_eq_projection hS hV,
    ← Submodule.projection_apply_eq_zero_iff hc]
  set v := (suspensionVerticalSubspace φ q).projection (suspensionHorizontalSubspace φ q) hc ξ
  refine ⟨fun h ↦ ?_, fun hv ↦ ?_⟩
  · by_contra hv
    exact (htame v (Submodule.projection_apply_mem _ _) hv).ne' h
  · rw [hv,
      eval₂_mpullback_snd_fiberForm_of_mem_suspensionHorizontalSubspace_left (Submodule.zero_mem _)]

/-! ### The vertical energy density of a pseudoholomorphic map -/

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H' : Type*}
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} {C : Type*} [TopologicalSpace C]
  [ChartedSpace H' C] [IsManifold I' ∞ C] {j : SmoothAlmostComplexStructure I' C}
  {u : C → UnitAddCircle × SmoothMappingTorus φ} {c : C}

/-- For a smooth map `u` that is pseudoholomorphic at `c`, into `X_φ` with an almost complex
structure of block form at `u c`, the pullback of `ω_v` evaluates on `e` and `j e` through the
vertical component of `du e`: `(u^* ω_v)(e, j e) = ω_v((du e)_V, J (du e)_V)`. -/
theorem eval₂_mpullback_mpullback_snd_fiberForm_apply_eq_projection
    (hhol : IsPseudoholomorphicAt j J u c)
    (hu : ContMDiff I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u)
    (hS : J (u c) ((Manifold.tangentSpaceProdEquiv (u c)).symm ((1 : ℝ), 0)) =
      (Manifold.tangentSpaceProdEquiv (u c)).symm ((0 : ℝ), timeVectorField φ (u c).2))
    (hV : ∀ v ∈ suspensionVerticalSubspace φ (u c), J (u c) v ∈ suspensionVerticalSubspace φ (u c))
    (e : TangentSpace I' c) :
    SmoothBundleForm.eval₂ (SmoothForm.mpullback u hu
        (SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ σ hσ))) c e (j c e) =
      SmoothBundleForm.eval₂ (SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ σ hσ))
        (u c)
        ((suspensionVerticalSubspace φ (u c)).projection (suspensionHorizontalSubspace φ (u c))
          (isCompl_suspensionVerticalSubspace_suspensionHorizontalSubspace φ (u c))
          (mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c e))
        (J (u c) ((suspensionVerticalSubspace φ (u c)).projection
          (suspensionHorizontalSubspace φ (u c))
          (isCompl_suspensionVerticalSubspace_suspensionHorizontalSubspace φ (u c))
          (mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c e))) := by
  rw [SmoothForm.eval₂_mpullback, hhol.mfderiv_apply_commute,
    eval₂_mpullback_snd_fiberForm_apply_eq_projection hS hV]

/-- For a smooth map `u` that is pseudoholomorphic at `c`, into `X_φ` with an almost complex
structure of block form at `u c` whose vertical restriction is tamed by `ω_v`, the vertical energy
density `(u^* ω_v)(e, j e)` is nonnegative. -/
theorem eval₂_mpullback_mpullback_snd_fiberForm_apply_nonneg {σ : SmoothTwoForm I M}
    {hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ}
    (hhol : IsPseudoholomorphicAt j J u c) (hu : ContMDiff I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u)
    (hS : J (u c) ((Manifold.tangentSpaceProdEquiv (u c)).symm ((1 : ℝ), 0)) =
      (Manifold.tangentSpaceProdEquiv (u c)).symm ((0 : ℝ), timeVectorField φ (u c).2))
    (hV : ∀ v ∈ suspensionVerticalSubspace φ (u c), J (u c) v ∈ suspensionVerticalSubspace φ (u c))
    (htame : ∀ v ∈ suspensionVerticalSubspace φ (u c), v ≠ 0 →
      0 < SmoothBundleForm.eval₂ (SmoothForm.mpullback Prod.snd contMDiff_snd
        (fiberForm φ σ hσ)) (u c) v (J (u c) v))
    (e : TangentSpace I' c) :
    0 ≤ SmoothBundleForm.eval₂ (SmoothForm.mpullback u hu
      (SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ σ hσ))) c e (j c e) := by
  rw [SmoothForm.eval₂_mpullback, hhol.mfderiv_apply_commute]
  exact eval₂_mpullback_snd_fiberForm_apply_nonneg hS hV htame _

/-- For a smooth map `u` that is pseudoholomorphic at `c`, into `X_φ` with an almost complex
structure of block form at `u c` whose vertical restriction is tamed by `ω_v`, the vertical energy
density `(u^* ω_v)(e, j e)` vanishes exactly when `du e` lies in the horizontal plane
`span(∂_s, T)`. -/
theorem eval₂_mpullback_mpullback_snd_fiberForm_apply_eq_zero_iff {σ : SmoothTwoForm I M}
    {hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ}
    (hhol : IsPseudoholomorphicAt j J u c) (hu : ContMDiff I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u)
    (hS : J (u c) ((Manifold.tangentSpaceProdEquiv (u c)).symm ((1 : ℝ), 0)) =
      (Manifold.tangentSpaceProdEquiv (u c)).symm ((0 : ℝ), timeVectorField φ (u c).2))
    (hV : ∀ v ∈ suspensionVerticalSubspace φ (u c), J (u c) v ∈ suspensionVerticalSubspace φ (u c))
    (htame : ∀ v ∈ suspensionVerticalSubspace φ (u c), v ≠ 0 →
      0 < SmoothBundleForm.eval₂ (SmoothForm.mpullback Prod.snd contMDiff_snd
        (fiberForm φ σ hσ)) (u c) v (J (u c) v))
    (e : TangentSpace I' c) :
    SmoothBundleForm.eval₂ (SmoothForm.mpullback u hu
        (SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ σ hσ))) c e (j c e) = 0 ↔
      mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c e ∈ suspensionHorizontalSubspace φ (u c) := by
  rw [SmoothForm.eval₂_mpullback, hhol.mfderiv_apply_commute]
  exact eval₂_mpullback_snd_fiberForm_apply_eq_zero_iff hS hV htame _

/-- The fiber form `σ_v`, pulled back to `X_φ`, pulls back to zero along a smooth map whose tangent
images all lie in the horizontal plane `span(∂_s, T)`. -/
theorem mpullback_mpullback_snd_fiberForm_eq_zero
    (hu : ContMDiff I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u)
    (hH : ∀ c (e : TangentSpace I' c),
      mfderiv I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) u c e ∈ suspensionHorizontalSubspace φ (u c)) :
    SmoothForm.mpullback u hu (SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ σ hσ)) =
      0 := by
  refine SmoothBundleForm.ext_eval₂ fun c e e' ↦ ?_
  rw [SmoothForm.eval₂_mpullback,
    eval₂_mpullback_snd_fiberForm_of_mem_suspensionHorizontalSubspace_left (hH c e)]
  simp

open Module in
/-- Let `u` be a smooth map from a surface `C`, oriented so that the frames `(e, j e)` are positive,
that is pseudoholomorphic at `c`, into `X_φ` with an almost complex structure of block form at `u c`
whose vertical restriction is tamed by `ω_v`. Then the top form `u^* ω_v` is nonnegative on every
positively oriented frame of the tangent plane at `c`. -/
theorem mpullback_mpullback_snd_fiberForm_apply_basis_nonneg [FiniteDimensional ℝ E']
    {σ : SmoothTwoForm I M} {hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ}
    {o : Manifold.Orientation I' C (Fin 2)}
    (hu : ContMDiff I' (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞ u)
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hhol : IsPseudoholomorphicAt j J u c)
    (hS : J (u c) ((Manifold.tangentSpaceProdEquiv (u c)).symm ((1 : ℝ), 0)) =
      (Manifold.tangentSpaceProdEquiv (u c)).symm ((0 : ℝ), timeVectorField φ (u c).2))
    (hV : ∀ v ∈ suspensionVerticalSubspace φ (u c), J (u c) v ∈ suspensionVerticalSubspace φ (u c))
    (htame : ∀ v ∈ suspensionVerticalSubspace φ (u c), v ≠ 0 →
      0 < SmoothBundleForm.eval₂ (SmoothForm.mpullback Prod.snd contMDiff_snd
        (fiberForm φ σ hσ)) (u c) v (J (u c) v))
    (b : Basis (Fin 2) ℝ (TangentSpace I' c)) (hb : b.orientation = o.orientationAt c) :
    0 ≤ (SmoothForm.mpullback u hu
      (SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ σ hσ))).1 c b := by
  set α := (SmoothForm.mpullback u hu
    (SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ σ hσ))).1 c
  -- The frame `b₀ = (b 0, j (b 0))`.
  set b₀ := basisOfLinearIndependentOfCardEqFinrank
    ((j.almostComplexStructureAt c).linearIndependent_pair (b.ne_zero 0))
    (by simpa using (o.finrank_tangentSpace_eq c).symm)
  have hb₀ : ⇑b₀ = ![b 0, j c (b 0)] := by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank,
      SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
  -- A top form on the plane is its value on the frame `b₀` times `det_{b₀}`.
  have hα : α b = α b₀ * b₀.det b := by
    simpa using congrArg (fun f ↦ f b) (α.toAlternatingMap.eq_smul_basis_det b₀)
  rw [hα]
  refine mul_nonneg ?_ ((b₀.orientation_eq_iff_det_pos b).1 ?_).le
  · rw [hb₀, ← SmoothBundleForm.eval₂_apply]
    exact eval₂_mpullback_mpullback_snd_fiberForm_apply_nonneg hhol hu hS hV htame _
  · rw [hb, ho c b₀ (by rw [hb₀]; simp)]

end SmoothMappingTorus

end TauCeti
