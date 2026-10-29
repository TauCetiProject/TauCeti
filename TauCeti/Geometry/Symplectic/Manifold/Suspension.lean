/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Basic
public import TauCeti.Geometry.Manifold.VectorField.MappingTorus
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import TauCeti.Geometry.Manifold.DeRham.Wedge

/-!
# The symplectic form of a symplectic suspension

Let `φ : M ≃ₘ⟮I, I⟯ M` be a diffeomorphism of a locally compact Hausdorff smooth manifold preserving
a two-form `σ`, and let `Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))` be its smooth mapping torus
(`TauCeti.SmoothMappingTorus φ`), with time form `dt` and fiber form `σ_v`. On the product
`X_φ = (ℝ / ℤ)_s × Y_φ` of a second circle with the mapping torus, this file defines the two-form

`Ω = ds ∧ dt + σ_v`

(`TauCeti.SmoothMappingTorus.suspensionForm φ σ hσ`), where `ds` and `dt`, `σ_v` are pulled back
along the two projections of `X_φ`.

In the coordinates `(s, t, x)` of `ℝ × ℝ × M`, through the local diffeomorphism
`(t, x) ↦ [t, x]` onto `Y_φ`, the form `Ω` is `ds ∧ dt + σ`: it pairs `a ∂_s + b ∂_t + v` with
`a' ∂_s + b' ∂_t + v'` to `a b' - a' b + σ(v, v')`
(`TauCeti.SmoothMappingTorus.eval₂_suspensionForm_mk`). Hence `Ω` is fiberwise nondegenerate
exactly when `σ` is. Since `ds ∧ dt` is closed, and `σ_v` is closed exactly when `σ` is, `Ω` is
closed exactly when `σ` is. So a symplectomorphism `φ` of a symplectic manifold `(M, σ)` makes
`(X_φ, Ω)` a symplectic manifold. No compactness of `M` is needed.

On the mapping torus itself the fiber form `σ_v` of a nondegenerate `σ` is degenerate in exactly
one direction: its kernel at every point is the line spanned by the vector field `T = ∂_t`
(`TauCeti.SmoothMappingTorus.ker_bilinFormAt_fiberForm`).

## Main definitions

* `TauCeti.SmoothMappingTorus.suspensionForm φ σ hσ`: the two-form `Ω = ds ∧ dt + σ_v` on
  `(ℝ / ℤ) × Y_φ`.

## Main results

* `TauCeti.SmoothMappingTorus.eval₂_suspensionForm`: the evaluation of `Ω` on two tangent vectors
  of `(ℝ / ℤ) × Y_φ`, through their components.
* `TauCeti.SmoothMappingTorus.eval₂_suspensionForm_mk`: in the coordinates `(s, t, x)`, `Ω` pairs
  `a ∂_s + b ∂_t + v` with `a' ∂_s + b' ∂_t + v'` to `a b' - a' b + σ(v, v')`.
* `TauCeti.SmoothMappingTorus.ker_bilinFormAt_fiberForm`: the kernel of the fiber form `σ_v` of a
  nondegenerate `σ` is the line spanned by `T = ∂_t`.
* `TauCeti.SmoothMappingTorus.isClosed_suspensionForm_iff`,
  `TauCeti.SmoothMappingTorus.isNondegenerate_suspensionForm_iff`,
  `TauCeti.SmoothMappingTorus.isSymplectic_suspensionForm_iff`: `Ω` is closed, nondegenerate or
  symplectic exactly when `σ` is.

## References

* Michael Hutchings and Michael Sullivan, *The periodic Floer homology of a Dehn twist*, Algebraic
  & Geometric Topology 5 (2005), 301–354 (the form `ds ∧ dt + ω_φ` on `ℝ × Y_φ`).
-/

public section

noncomputable section

open Function
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothMappingTorus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M]
  (φ : M ≃ₘ⟮I, I⟯ M)

/-- The two-form `Ω = ds ∧ dt + σ_v` on the product `(ℝ / ℤ)_s × Y_φ` of a circle with the mapping
torus `Y_φ` of a diffeomorphism `φ` preserving the two-form `σ`. Here `ds` is the time form of the
circle factor, and `dt` and `σ_v` are the time form and the fiber form of `σ` on `Y_φ`. When `σ` is
symplectic, so is `Ω` (`TauCeti.SmoothMappingTorus.isSymplectic_suspensionForm_iff`). -/
def suspensionForm (σ : SmoothTwoForm I M) (hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ) :
    SmoothTwoForm (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (UnitAddCircle × SmoothMappingTorus φ) :=
  SmoothForm.wedge (SmoothForm.mpullback Prod.fst contMDiff_fst (AddCircle.timeForm 1))
      (SmoothForm.mpullback Prod.snd contMDiff_snd (timeForm φ)) +
    SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ σ hσ)

variable {φ} {σ : SmoothTwoForm I M} {hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ}

/-- The form `Ω` is the sum of the wedge `ds ∧ dt` of the pulled back time forms and of the pulled
back fiber form `σ_v`. -/
theorem suspensionForm_def :
    suspensionForm φ σ hσ =
      SmoothForm.wedge (SmoothForm.mpullback Prod.fst contMDiff_fst (AddCircle.timeForm 1))
          (SmoothForm.mpullback Prod.snd contMDiff_snd (timeForm φ)) +
        SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ σ hσ) :=
  (rfl)

/-- The form `Ω = ds ∧ dt + σ_v` evaluated on two tangent vectors of `(ℝ / ℤ) × Y_φ`, through their
circle and mapping torus components. -/
theorem eval₂_suspensionForm (p : UnitAddCircle × SmoothMappingTorus φ)
    (v w : TangentSpace (𝓘(ℝ).prod (𝓘(ℝ).prod I)) p) :
    SmoothBundleForm.eval₂ (suspensionForm φ σ hσ) p v w =
      (AddCircle.timeForm 1).1 p.1 ![(Manifold.tangentSpaceProdEquiv p v).1] *
          (timeForm φ).1 p.2 ![(Manifold.tangentSpaceProdEquiv p w).2] -
        (AddCircle.timeForm 1).1 p.1 ![(Manifold.tangentSpaceProdEquiv p w).1] *
          (timeForm φ).1 p.2 ![(Manifold.tangentSpaceProdEquiv p v).2] +
        SmoothBundleForm.eval₂ (fiberForm φ σ hσ) p.2 (Manifold.tangentSpaceProdEquiv p v).2
          (Manifold.tangentSpaceProdEquiv p w).2 := by
  rw [suspensionForm_def, SmoothBundleForm.eval₂_add, SmoothForm.eval₂_wedge_one_one,
    SmoothForm.eval₂_mpullback_snd]
  simp only [SmoothForm.mpullback_fst_apply, SmoothForm.mpullback_snd_apply,
    Matrix.vec_single_eq_const]

/-- In the coordinates `(s, t, x)` of `ℝ × ℝ × M`, the form `Ω` is `ds ∧ dt + σ`: at `(θ, [t, x])`
it pairs the vector `a ∂_s + b ∂_t + v` with `a' ∂_s + b' ∂_t + v'` to `a b' - a' b + σ(v, v')`.
Here `b ∂_t + v` is the image of the tangent vector `(b, v)` of `ℝ × M` under the differential of
`(t, x) ↦ [t, x]`. -/
theorem eval₂_suspensionForm_mk (θ : UnitAddCircle) (t : ℝ) (x : M) (a a' b b' : ℝ)
    (v v' : TangentSpace I x) :
    SmoothBundleForm.eval₂ (suspensionForm φ σ hσ) (θ, mk φ t x)
        ((Manifold.tangentSpaceProdEquiv _).symm
          (a, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
            ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, v))))
        ((Manifold.tangentSpaceProdEquiv _).symm
          (a', mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
            ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b', v')))) =
      a * b' - a' * b + SmoothBundleForm.eval₂ σ x v v' := by
  rw [eval₂_suspensionForm]
  simp only [ContinuousLinearEquiv.apply_symm_apply, AddCircle.timeForm_apply]
  rw [timeForm_apply_mfderiv_uncurry_mk, timeForm_apply_mfderiv_uncurry_mk,
    eval₂_fiberForm_mfderiv_uncurry_mk]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  -- The one-entry vectors `![a]` and `![a']` evaluate at `0` to `a` and `a'`.
  rfl

omit [T2Space M] [LocallyCompactSpace M] in
/-- Every tangent vector of `(ℝ / ℤ) × Y_φ` at `(θ, [t, x])` is `a ∂_s + b ∂_t + v` in the
coordinates `(s, t, x)`. -/
private theorem exists_eq_symm_tangentSpaceProdEquiv [T2Space M] [LocallyCompactSpace M]
    (θ : UnitAddCircle) (t : ℝ) (x : M)
    (V : TangentSpace (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (θ, mk φ t x)) :
    ∃ (a b : ℝ) (v : TangentSpace I x), V = (Manifold.tangentSpaceProdEquiv _).symm
      (a, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
        ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, v))) := by
  set e := Manifold.tangentSpaceProdEquiv (I := 𝓘(ℝ)) (J := 𝓘(ℝ).prod I) (θ, mk φ t x)
  set e' := Manifold.tangentSpaceProdEquiv (I := 𝓘(ℝ)) (J := I) (t, x)
  obtain ⟨w, hw⟩ :=
    ((isLocalDiffeomorph_uncurry_mk φ).isInvertible_mfderiv (by simp) (t, x)).surjective (e V).2
  refine ⟨(e V).1, (e' w).1, (e' w).2, ?_⟩
  rw [Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply, hw, Prod.mk.eta,
    ContinuousLinearEquiv.symm_apply_apply]

omit [T2Space M] [LocallyCompactSpace M] in
/-- In the coordinates `(s, t, x)`, the vector `a ∂_s + b ∂_t + v` vanishes exactly when `a`, `b`
and `v` do. -/
private theorem symm_tangentSpaceProdEquiv_eq_zero_iff [T2Space M] [LocallyCompactSpace M]
    (θ : UnitAddCircle) (t : ℝ) (x : M) (a b : ℝ) (v : TangentSpace I x) :
    (Manifold.tangentSpaceProdEquiv (I := 𝓘(ℝ)) (J := 𝓘(ℝ).prod I) (θ, mk φ t x)).symm
        (a, mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
          ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, v))) = 0 ↔
      a = 0 ∧ b = 0 ∧ v = 0 := by
  set D := mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
  set e := Manifold.tangentSpaceProdEquiv (I := 𝓘(ℝ)) (J := 𝓘(ℝ).prod I) (θ, mk φ t x)
  set e' := Manifold.tangentSpaceProdEquiv (I := 𝓘(ℝ)) (J := I) (t, x)
  have hD : Injective D :=
    ((isLocalDiffeomorph_uncurry_mk φ).isInvertible_mfderiv (by simp) (t, x)).injective
  constructor
  · intro h
    have h₁ := Prod.ext_iff.1 (e.symm.map_eq_zero_iff.1 h)
    have h₂ := Prod.ext_iff.1 (e'.symm.map_eq_zero_iff.1 (hD (h₁.2.trans D.map_zero.symm)))
    exact ⟨h₁.1, h₂.1, h₂.2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact e.symm.map_eq_zero_iff.2
      (Prod.ext rfl ((congrArg D (e'.symm.map_eq_zero_iff.2 rfl)).trans D.map_zero))

/-- The fiber form `σ_v` of a nondegenerate two-form `σ` preserved by `φ` has kernel the line
spanned by the vector field `T = ∂_t` at every point of the mapping torus. -/
theorem ker_bilinFormAt_fiberForm (h : σ.IsNondegenerate) (y : SmoothMappingTorus φ) :
    LinearMap.ker ((fiberForm φ σ hσ).bilinFormAt y) = ℝ ∙ timeVectorField φ y := by
  obtain ⟨⟨t, x⟩, rfl⟩ : ∃ p : ℝ × M, mk φ p.1 p.2 = y := uncurry_mk_surjective φ y
  set D := mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
  set B := (fiberForm φ σ hσ).bilinFormAt (mk φ t x)
  -- The vector `T` pairs to zero with every vector.
  have hT : B (timeVectorField φ (mk φ t x)) = 0 := LinearMap.ext fun w' ↦ by
    rw [SmoothForm.bilinFormAt_apply, eval₂_fiberForm_timeVectorField_left, LinearMap.zero_apply]
  refine le_antisymm (fun w hw ↦ ?_)
    ((Submodule.span_singleton_le_iff_mem _ _).2 (LinearMap.mem_ker.2 hT))
  obtain ⟨b, v, rfl⟩ := exists_mfderiv_uncurry_mk_eq φ t x w
  -- Pairing with the vectors `v'` tangent to the fiber gives `σ(v, v') = 0`, so `v = 0`.
  obtain rfl : v = 0 := (SmoothTwoForm.isNondegenerate_iff_separatingLeft.1 h) x v fun v' ↦ by
    have h₁ := eval₂_fiberForm_mfderiv_uncurry_mk (hτ := hσ) t x
      ((Manifold.tangentSpaceProdEquiv (t, x)).symm (b, v))
      ((Manifold.tangentSpaceProdEquiv (t, x)).symm (0, v'))
    simp only [ContinuousLinearEquiv.apply_symm_apply] at h₁
    have h₂ := LinearMap.congr_fun (LinearMap.mem_ker.1 hw)
      (D ((Manifold.tangentSpaceProdEquiv (t, x)).symm (0, v')))
    exact h₁.symm.trans ((SmoothForm.bilinFormAt_apply _ _ _ _).symm.trans
      (h₂.trans (LinearMap.zero_apply _)))
  -- The vector `b ∂_t` is the image of `(b, 0) = b • (1, 0)`.
  refine Submodule.mem_span_singleton.2
    ⟨b, (congrArg (b • ·) (timeVectorField_mk φ t x)).trans ?_⟩
  refine (D.map_smul b _).symm.trans (congrArg D
    (((Manifold.tangentSpaceProdEquiv (t, x)).symm.map_smul b _).symm.trans ?_))
  exact congrArg (Manifold.tangentSpaceProdEquiv (t, x)).symm (Prod.ext (mul_one b) (smul_zero b))

/-- The form `Ω = ds ∧ dt + σ_v` is fiberwise nondegenerate exactly when `σ` is. -/
@[simp]
theorem isNondegenerate_suspensionForm_iff :
    (suspensionForm φ σ hσ).IsNondegenerate ↔ σ.IsNondegenerate := by
  simp only [SmoothTwoForm.isNondegenerate_iff_separatingLeft]
  constructor
  · intro h x v hv
    -- The vector `v`, tangent to the fiber through `[0, x]`, pairs with `a' ∂_s + b' ∂_t + v'`
    -- to `σ(v, v') = 0`.
    have hV := h ((0 : UnitAddCircle), mk φ 0 x) ((Manifold.tangentSpaceProdEquiv _).symm
      ((0 : ℝ), mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (0, x)
        ((Manifold.tangentSpaceProdEquiv (0, x)).symm ((0 : ℝ), v)))) fun W ↦ by
      obtain ⟨a', b', v', rfl⟩ := exists_eq_symm_tangentSpaceProdEquiv _ _ _ W
      rw [eval₂_suspensionForm_mk, hv]
      ring
    exact ((symm_tangentSpaceProdEquiv_eq_zero_iff _ _ _ _ _ _).1 hV).2.2
  · rintro h ⟨θ, y⟩ V hV
    obtain ⟨⟨t, x⟩, rfl⟩ : ∃ p : ℝ × M, mk φ p.1 p.2 = y := uncurry_mk_surjective φ y
    obtain ⟨a, b, v, rfl⟩ := exists_eq_symm_tangentSpaceProdEquiv θ t x V
    -- Pair `a ∂_s + b ∂_t + v` with `∂_s`, `∂_t` and the vectors `v'` tangent to the fiber.
    have hz : SmoothBundleForm.eval₂ σ x v 0 = 0 := by
      rw [← SmoothForm.bilinFormAt_apply, map_zero]
    have hb : b = 0 := by
      have h₁ := hV ((Manifold.tangentSpaceProdEquiv _).symm
        ((1 : ℝ), mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
          ((Manifold.tangentSpaceProdEquiv (t, x)).symm ((0 : ℝ), 0))))
      rw [eval₂_suspensionForm_mk, hz] at h₁
      linarith
    have ha : a = 0 := by
      have h₁ := hV ((Manifold.tangentSpaceProdEquiv _).symm
        ((0 : ℝ), mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
          ((Manifold.tangentSpaceProdEquiv (t, x)).symm ((1 : ℝ), 0))))
      rw [eval₂_suspensionForm_mk, hz] at h₁
      linarith
    have hv : v = 0 := h x v fun v' ↦ by
      have h₁ := hV ((Manifold.tangentSpaceProdEquiv _).symm
        ((0 : ℝ), mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x)
          ((Manifold.tangentSpaceProdEquiv (t, x)).symm ((0 : ℝ), v'))))
      rw [eval₂_suspensionForm_mk] at h₁
      linarith
    exact (symm_tangentSpaceProdEquiv_eq_zero_iff _ _ _ _ _ _).2 ⟨ha, hb, hv⟩

/-- The form `Ω = ds ∧ dt + σ_v` is closed exactly when `σ` is. -/
@[simp]
theorem isClosed_suspensionForm_iff : (suspensionForm φ σ hσ).IsClosed ↔ σ.IsClosed := by
  have hclosed {k : ℕ}
      {β : SmoothForm (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (UnitAddCircle × SmoothMappingTorus φ) ℝ k} :
      β ∈ closedForms _ _ k ↔ β.IsClosed :=
    (mem_closedForms (φ := β)).trans (SmoothForm.isClosed_def β).symm
  -- The wedge `ds ∧ dt` of closed forms is closed.
  have hdsdt : (SmoothForm.wedge
      (SmoothForm.mpullback Prod.fst contMDiff_fst (AddCircle.timeForm 1))
      (SmoothForm.mpullback Prod.snd contMDiff_snd (timeForm φ))).IsClosed :=
    hclosed.1 (SmoothForm.wedge_mem_closedForms
      (hclosed.2 ((AddCircle.isClosed_timeForm 1).mpullback _ _))
      (hclosed.2 ((isClosed_timeForm φ).mpullback _ _)))
  rw [← isClosed_fiberForm_iff (hσ := hσ)]
  refine ⟨fun h ↦ ?_, fun h ↦ hdsdt.add (h.mpullback _ _)⟩
  -- Conversely, `σ_v` is the pullback of `Ω - ds ∧ dt` along the section `y ↦ (0, y)`.
  have h' := (h.sub hdsdt).mpullback (fun y ↦ ((0 : UnitAddCircle), y))
    (contMDiff_const.prodMk contMDiff_id)
  have hid : (Prod.snd ∘ fun y : SmoothMappingTorus φ ↦ ((0 : UnitAddCircle), y)) = id := rfl
  rw [suspensionForm_def, add_sub_cancel_left, ← LinearMap.comp_apply,
    ← SmoothForm.mpullback_comp] at h'
  simpa only [hid, SmoothForm.mpullback_id, LinearMap.id_apply] using h'

/-- The form `Ω = ds ∧ dt + σ_v` is symplectic exactly when `σ` is. In particular a
symplectomorphism `φ` of a symplectic manifold `(M, σ)` makes `(ℝ / ℤ) × Y_φ` a symplectic
manifold. -/
@[simp]
theorem isSymplectic_suspensionForm_iff :
    (suspensionForm φ σ hσ).IsSymplectic ↔ σ.IsSymplectic :=
  ⟨fun h ↦ ⟨isClosed_suspensionForm_iff.1 h.isClosed,
      isNondegenerate_suspensionForm_iff.1 h.isNondegenerate⟩,
    fun h ↦ ⟨isClosed_suspensionForm_iff.2 h.isClosed,
      isNondegenerate_suspensionForm_iff.2 h.isNondegenerate⟩⟩

end SmoothMappingTorus

end TauCeti
