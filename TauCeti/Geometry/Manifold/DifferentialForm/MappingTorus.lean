/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.AddCircle
public import TauCeti.Geometry.Manifold.DifferentialForm.Quotient
public import TauCeti.Geometry.Manifold.Instances.MappingTorus
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent

/-!
# The time form and fiber forms of a smooth mapping torus

Let `φ : M ≃ₘ⟮I, I⟯ M` be a diffeomorphism of a locally compact Hausdorff smooth manifold and
`Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))` its smooth mapping torus
(`TauCeti.SmoothMappingTorus φ`), with projection `p : Y_φ → ℝ / ℤ`, `[t, x] ↦ [t]`. This file
puts on `Y_φ` the two kinds of forms that split its geometry into a time direction and a fiber
direction.

* The **time form** `dt = p^* dt_1` (`TauCeti.SmoothMappingTorus.timeForm φ`) is the pullback of
  the time form of the circle `ℝ / ℤ`. It is closed, its pullback along `(t, x) ↦ [t, x]` is the
  differential of the real coordinate of `ℝ × M`, and it vanishes on every fiber.
* The **fiber form** `σ_v` of a form `σ` on `M` with `φ^* σ = σ`
  (`TauCeti.SmoothMappingTorus.fiberForm φ σ hσ`) is the descent of the pullback of `σ` along the
  projection `ℝ × M → M`. That pullback is invariant under the deck transformations
  `(t, x) ↦ (t + k, φ ^ (-k) x)` because `φ` preserves `σ`. The fiber form pulls back to `σ` on
  each fiber `x ↦ [t, x]`, and it is closed exactly when `σ` is.

For a symplectic form `σ` preserved by `φ`, the fiber form is the closed two-form `ω_v` of the
symplectic suspension of `φ`.

## Main definitions

* `TauCeti.SmoothMappingTorus.timeForm φ`: the time form `dt` of the mapping torus.
* `TauCeti.SmoothMappingTorus.fiberForm φ σ hσ`: the fiber form `σ_v` of a form `σ` preserved by
  `φ`.

## Main results

* `TauCeti.SmoothMappingTorus.timeForm_apply`: the time form is the differential of the
  projection to the circle.
* `TauCeti.SmoothMappingTorus.isClosed_timeForm`,
  `TauCeti.SmoothMappingTorus.mpullback_mk_timeForm`: the time form is closed and vanishes on the
  fibers.
* `TauCeti.SmoothMappingTorus.mpullback_uncurry_mk_timeForm`: on `ℝ × M`, the time form is the
  differential of the real coordinate.
* `TauCeti.SmoothMappingTorus.timeForm_apply_mfderiv_uncurry_mk`,
  `TauCeti.SmoothMappingTorus.eval₂_fiberForm_mfderiv_uncurry_mk`: on the image of a tangent
  vector `(b, v)` of `ℝ × M` under the differential of `(t, x) ↦ [t, x]`, the time form is `b`
  and the fiber form of a two-form `σ` evaluates as `σ` on the components `v`.
* `TauCeti.SmoothMappingTorus.mpullback_uncurry_mk_fiberForm`: on `ℝ × M`, the fiber form is the
  pullback of `σ` along the second projection; `TauCeti.SmoothMappingTorus.eq_fiberForm_iff` says
  that it is the only form on `Y_φ` with this pullback.
* `TauCeti.SmoothMappingTorus.mpullback_mk_fiberForm`: the fiber form pulls back to `σ` on each
  fiber.
* `TauCeti.SmoothMappingTorus.isClosed_fiberForm_iff`: the fiber form is closed exactly when `σ`
  is.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 21 (quotients by discrete group actions).
-/

public section

noncomputable section

open Set Filter Function
open scoped Manifold Topology ContDiff

namespace TauCeti

namespace SmoothMappingTorus

open Cover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
  (φ : M ≃ₘ⟮I, I⟯ M)

omit [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M] in
/-- The projection of the cover to `M` is smooth. -/
private theorem contMDiff_space :
    ContMDiff (𝓘(ℝ).prod I) I ∞ fun z : Cover φ ↦ ((ofProd φ).symm z).2 :=
  contMDiff_snd.comp (contMDiff_ofProd_symm φ ∞)

/-! ### The time form -/

/-- The time form `dt` of the mapping torus: the pullback of the time form of the circle `ℝ / ℤ`
along the projection `[t, x] ↦ [t]`. -/
def timeForm : SmoothForm (𝓘(ℝ).prod I) (SmoothMappingTorus φ) ℝ 1 :=
  SmoothForm.mpullback (proj φ) (contMDiff_proj φ) (AddCircle.timeForm 1)

/-- The time form is the pullback of the time form of the circle along the projection. -/
theorem timeForm_def :
    timeForm φ = SmoothForm.mpullback (proj φ) (contMDiff_proj φ) (AddCircle.timeForm 1) :=
  (rfl)

/-- The time form `dt` of the mapping torus is the differential of the projection
`p : Y_φ → ℝ / ℤ`, read in the real tangent lines of the circle. -/
theorem timeForm_apply (y : SmoothMappingTorus φ) (v : Fin 1 → TangentSpace (𝓘(ℝ).prod I) y) :
    (timeForm φ).1 y v = mfderiv (𝓘(ℝ).prod I) 𝓘(ℝ) (proj φ) y (v 0) := by
  rw [timeForm_def, SmoothForm.coe_mpullback, mpullback_apply, AddCircle.timeForm_apply]

/-- The time form of the mapping torus is closed. -/
theorem isClosed_timeForm : (timeForm φ).IsClosed :=
  (AddCircle.isClosed_timeForm 1).mpullback _ _

/-- On `ℝ × M`, the time form is the differential `dt` of the real coordinate: its pullback along
`(t, x) ↦ [t, x]` is the pullback of `dt` along the first projection. -/
theorem mpullback_uncurry_mk_timeForm :
    mpullback (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (timeForm φ).1 =
      mpullback (𝓘(ℝ).prod I) 𝓘(ℝ) Prod.fst (mextDeriv (RoughForm.ofFunction 𝓘(ℝ) id)) := by
  have hcomp : proj φ ∘ uncurry (mk φ) = ((↑) : ℝ → UnitAddCircle) ∘ Prod.fst :=
    funext fun p ↦ proj_mk φ p.1 p.2
  rw [← AddCircle.mpullback_coe_timeForm 1, timeForm, SmoothForm.coe_mpullback,
    ← mpullback_comp ((contMDiff_uncurry_mk φ).mdifferentiable (by simp))
      ((contMDiff_proj φ).mdifferentiable (by simp)), hcomp,
    mpullback_comp mdifferentiable_fst
      ((AddCircle.contMDiff_coe 1 ∞).mdifferentiable (by simp))]

/-- The time form sends the image of a tangent vector `(b, v)` of `ℝ × M` under the differential of
`(t, x) ↦ [t, x]` to its real component `b`. -/
theorem timeForm_apply_mfderiv_uncurry_mk (t : ℝ) (x : M)
    (w : TangentSpace (𝓘(ℝ).prod I) (t, x)) :
    (timeForm φ).1 (mk φ t x) ![mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x) w] =
      (Manifold.tangentSpaceProdEquiv (t, x) w).1 := by
  have h := DFunLike.congr_fun (congrFun (mpullback_uncurry_mk_timeForm φ) (t, x)) ![w]
  simp only [TauCeti.mpullback_apply, mfderiv_fst, mextDeriv_ofFunction, mvfderiv_eq_fderiv,
    fderiv_id, Matrix.vec_single_eq_const] at h
  -- `uncurry (mk φ) (t, x)` is `mk φ t x`, so `h` evaluates the time form at `[t, x]`.
  refine (congrArg ((timeForm φ).1 (mk φ t x)) (Matrix.vec_single_eq_const _)).trans (h.trans ?_)
  simp only [ContinuousAlternatingMap.ofSubsingleton_apply_apply, ContinuousLinearMap.coe_comp,
    comp_apply, ContinuousLinearMap.coe_id', id_eq]
  rw [Manifold.tangentSpaceProdEquiv_apply]
  -- Tangent vectors of `ℝ` are real numbers, on which `NormedSpace.fromTangentSpace` is the
  -- identity.
  rfl

/-- The time form vanishes on each fiber `x ↦ [t, x]` of the mapping torus. -/
theorem mpullback_mk_timeForm (t : ℝ) :
    SmoothForm.mpullback (mk φ t) (contMDiff_mk φ t) (timeForm φ) = 0 := by
  have hconst : proj φ ∘ mk φ t = fun _ ↦ (t : UnitAddCircle) := funext fun x ↦ proj_mk φ t x
  rw [timeForm, ← LinearMap.comp_apply, ← SmoothForm.mpullback_comp]
  refine Subtype.ext <| funext fun x ↦ ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [SmoothForm.coe_mpullback, mpullback_apply, hconst, mfderiv_const]
  exact (AddCircle.timeForm 1).1 _ |>.map_coord_zero 0 rfl

/-! ### Fiber forms -/

variable {φ} {σ : SmoothForm I M F k}

omit [T2Space M] [LocallyCompactSpace M] in
/-- The pullback of a form `σ` preserved by `φ` along the projection of the cover to `M` is
invariant under the deck transformations `(t, x) ↦ (t + k, φ ^ (-k) x)`. -/
private theorem mpullback_smul_mpullback_space (hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ)
    (j : Multiplicative ℤ) :
    SmoothForm.mpullback (j • · : Cover φ → Cover φ) (contMDiff_const_smul j)
        (SmoothForm.mpullback _ (contMDiff_space φ) σ) =
      SmoothForm.mpullback _ (contMDiff_space φ) σ := by
  have hcomp : (fun z : Cover φ ↦ ((ofProd φ).symm z).2) ∘ (j • ·) =
      ⇑(φ ^ (-j.toAdd)) ∘ fun z : Cover φ ↦ ((ofProd φ).symm z).2 :=
    funext fun z ↦ by simp
  rw [← LinearMap.comp_apply, ← SmoothForm.mpullback_comp]
  simp only [hcomp]
  rw [SmoothForm.mpullback_comp _ _ (contMDiff_space φ) (φ ^ (-j.toAdd)).contMDiff,
    LinearMap.comp_apply, SmoothForm.mpullback_zpow_eq_self hσ]

variable (φ σ) in
/-- The fiber form `σ_v` on the mapping torus of a form `σ` on `M` preserved by `φ`: the descent
of the pullback of `σ` along the projection `ℝ × M → M`, which is invariant under the deck
transformations because `φ^* σ = σ`. Its pullback to `ℝ × M` is the pullback of `σ` along the
second projection (`TauCeti.SmoothMappingTorus.mpullback_uncurry_mk_fiberForm`), and it restricts
to `σ` on each fiber (`TauCeti.SmoothMappingTorus.mpullback_mk_fiberForm`). -/
def fiberForm (hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ) :
    SmoothForm (𝓘(ℝ).prod I) (SmoothMappingTorus φ) F k :=
  SmoothForm.descend (SmoothForm.mpullback _ (contMDiff_space φ) σ)
    (mpullback_smul_mpullback_space hσ)

variable {hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ}

/-- On `ℝ × M`, the fiber form of `σ` is the pullback of `σ` along the second projection. -/
@[simp]
theorem mpullback_uncurry_mk_fiberForm :
    SmoothForm.mpullback (uncurry (mk φ)) (contMDiff_uncurry_mk φ) (fiberForm φ σ hσ) =
      SmoothForm.mpullback Prod.snd contMDiff_snd σ := by
  have hmk : uncurry (mk φ) =
      Quotient.mk (MulAction.orbitRel (Multiplicative ℤ) (Cover φ)) ∘ ofProd φ :=
    funext fun p ↦ mk_def φ p.1 p.2
  have hsnd : (fun z : Cover φ ↦ ((ofProd φ).symm z).2) ∘ ofProd φ = Prod.snd :=
    funext fun p ↦ by simp
  simp only [hmk]
  rw [SmoothForm.mpullback_comp _ _ (contMDiff_ofProd φ ∞) isLocalDiffeomorph_quotientMk.contMDiff,
    LinearMap.comp_apply, fiberForm, SmoothForm.mpullback_quotientMk_descend,
    ← LinearMap.comp_apply, ← SmoothForm.mpullback_comp]
  simp only [hsnd]

/-- The fiber form of `σ` is the unique form on the mapping torus whose pullback to `ℝ × M` is the
pullback of `σ` along the second projection. -/
theorem eq_fiberForm_iff {β : SmoothForm (𝓘(ℝ).prod I) (SmoothMappingTorus φ) F k} :
    β = fiberForm φ σ hσ ↔
      SmoothForm.mpullback (uncurry (mk φ)) (contMDiff_uncurry_mk φ) β =
        SmoothForm.mpullback Prod.snd contMDiff_snd σ := by
  rw [← mpullback_uncurry_mk_fiberForm (hσ := hσ)]
  refine ⟨congrArg _, fun h ↦ Subtype.ext ?_⟩
  refine (isLocalDiffeomorph_uncurry_mk φ).mpullback_injective (by simp)
    (uncurry_mk_surjective φ) ?_
  simpa only [SmoothForm.coe_mpullback] using congrArg Subtype.val h

/-- The fiber form of `σ` restricts to `σ` on each fiber `x ↦ [t, x]` of the mapping torus. -/
@[simp]
theorem mpullback_mk_fiberForm (t : ℝ) :
    SmoothForm.mpullback (mk φ t) (contMDiff_mk φ t) (fiberForm φ σ hσ) = σ := by
  have hincl : ContMDiff I (𝓘(ℝ).prod I) ∞ fun x : M ↦ (t, x) :=
    contMDiff_const.prodMk contMDiff_id
  have hmk : mk φ t = uncurry (mk φ) ∘ fun x ↦ (t, x) := rfl
  simp only [hmk]
  rw [SmoothForm.mpullback_comp _ _ hincl (contMDiff_uncurry_mk φ), LinearMap.comp_apply,
    mpullback_uncurry_mk_fiberForm, ← LinearMap.comp_apply, ← SmoothForm.mpullback_comp]
  have hid : Prod.snd ∘ (fun x : M ↦ (t, x)) = id := rfl
  simp only [hid, SmoothForm.mpullback_id, LinearMap.id_apply]

/-- The fiber form of a two-form `σ` evaluates on the images of tangent vectors `(b, v)` and
`(b', v')` of `ℝ × M` under the differential of `(t, x) ↦ [t, x]` as `σ` on `v` and `v'`. -/
theorem eval₂_fiberForm_mfderiv_uncurry_mk {τ : SmoothForm I M F 2}
    {hτ : SmoothForm.mpullback φ φ.contMDiff τ = τ} (t : ℝ) (x : M)
    (w w' : TangentSpace (𝓘(ℝ).prod I) (t, x)) :
    (fiberForm φ τ hτ).eval₂ (mk φ t x)
        (mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x) w)
        (mfderiv (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) (uncurry (mk φ)) (t, x) w') =
      τ.eval₂ x (Manifold.tangentSpaceProdEquiv (t, x) w).2
        (Manifold.tangentSpaceProdEquiv (t, x) w').2 := by
  have h := congrArg (fun β ↦ β.eval₂ (t, x) w w') (mpullback_uncurry_mk_fiberForm (hσ := hτ))
  simp only [SmoothForm.eval₂_mpullback, mfderiv_snd] at h
  rw [Manifold.tangentSpaceProdEquiv_apply, Manifold.tangentSpaceProdEquiv_apply]
  -- `uncurry (mk φ) (t, x)` is `mk φ t x`, and `ContinuousLinearMap.snd` is `Prod.snd`.
  exact h

/-- The fiber form of `σ` is closed exactly when `σ` is closed. -/
@[simp]
theorem isClosed_fiberForm_iff : (fiberForm φ σ hσ).IsClosed ↔ σ.IsClosed := by
  refine ⟨fun h ↦ ?_, fun h ↦ SmoothForm.isClosed_descend_iff.mpr (h.mpullback _ _)⟩
  rw [← mpullback_mk_fiberForm (hσ := hσ) 0]
  exact h.mpullback _ _

end SmoothMappingTorus

end TauCeti
