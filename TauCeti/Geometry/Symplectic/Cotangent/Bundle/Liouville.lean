/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Squared
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent
public import TauCeti.Geometry.Manifold.VectorBundle.Submersion
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import TauCeti.Geometry.Symplectic.Cotangent.Liouville

/-!
# The Liouville form and the canonical symplectic form of a cotangent bundle

The cotangent bundle `T*M = TauCeti.CotangentBundle I M` of a manifold carries a tautological, or
Liouville, one-form `λ`: at a covector `p` over `x`, it evaluates a tangent vector `v` of `T*M` by

`λ_p(v) = p(dπ v)`,

where `π : T*M → M` is the bundle projection (`TauCeti.CotangentBundle.liouvilleForm`). Its
negative exterior derivative is the canonical symplectic form `ω = -dλ`
(`TauCeti.CotangentBundle.symplecticForm`).

Both forms are computed in the preferred charts of `T*M`, with coordinates `(q, p)`: there `λ` is
the linear Liouville form `λ_(q,p)(δq, δp) = p(δq)`, that is `Σ pᵢ dqᵢ`
(`TauCeti.CotangentBundle.inChartAt_liouvilleForm`), and `ω` is the linear form
`TauCeti.strongDualCotangentSymplecticForm`, that is `Σ dqᵢ ∧ dpᵢ`
(`TauCeti.CotangentBundle.inChartAt_symplecticForm_apply`). The chart formula for `λ` reduces to
the derivative of the projection in a bundle chart,
`Bundle.mfderiv_proj_comp_mfderivWithin_extChartAt_symm`; it gives smoothness of `λ`, and that
of `ω` follows from the linear identity `TauCeti.neg_extDeriv_cotangentLiouvilleForm`. The sign
conventions are therefore those of the linear model. Consequently `ω` is closed and nondegenerate
(`TauCeti.CotangentBundle.isSymplectic_symplecticForm`).

The form `λ` is tautological: its pullback along the section of `T*M` defined by a one-form `α`
is `α` itself (`TauCeti.CotangentBundle.mpullback_liouvilleForm`, and its pointwise version
`TauCeti.CotangentBundle.mpullback_liouvilleForm_section`). The base may have boundary or corners,
and nothing here assumes finite dimension.

## Main declarations

* `TauCeti.CotangentBundle.liouvilleForm`: the Liouville one-form on `T*M`.
* `TauCeti.CotangentBundle.inChartAt_liouvilleForm`: its chart formula `Σ pᵢ dqᵢ`.
* `TauCeti.CotangentBundle.mpullback_liouvilleForm`: its pullback by the section of a one-form.
* `TauCeti.CotangentBundle.symplecticForm`: the canonical symplectic form `ω = -dλ`.
* `TauCeti.CotangentBundle.inChartAt_symplecticForm_apply`: its chart formula.
* `TauCeti.CotangentBundle.isSymplectic_symplecticForm`: `ω` is symplectic.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 2.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.2.
-/

public section

noncomputable section

open Bundle Set Filter
open scoped Manifold Topology ContDiff

namespace TauCeti

namespace CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section Liouville

variable [IsManifold I 2 M]

variable (I M) in
/-- The tautological one-form `z ↦ z ∘ dπ` as a rough form; `liouvilleForm` bundles its
smoothness. -/
private def liouvilleRough :
    RoughForm (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (CotangentBundle I M) ℝ 1 :=
  fun z ↦ ContinuousAlternatingMap.ofSubsingleton ℝ _ ℝ 0
    (z.2 ∘L mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I (π (E →L[ℝ] ℝ)
      (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)) z)

/-- The rough Liouville form applies the covector to the derivative of the projection. -/
private theorem liouvilleRough_apply (z : CotangentBundle I M)
    (v : Fin 1 → TangentSpace (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) z) :
    liouvilleRough I M z v =
      z.2 (mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I (π (E →L[ℝ] ℝ)
        (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)) z (v 0)) :=
  rfl

/-- In a preferred chart of the cotangent bundle, the rough Liouville form is the linear
Liouville form. -/
private theorem inChartAt_liouvilleRough (z₀ : CotangentBundle I M)
    {w : E × (E →L[ℝ] ℝ)} (hw : w ∈ (extChartAt (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) z₀).target) :
    (liouvilleRough I M).inChartAt z₀ w = cotangentLiouvilleForm w := by
  have hq : w.1 ∈ (extChartAt I z₀.proj).target := fst_mem_extChartAt_target z₀ hw
  have hx : (extChartAt I z₀.proj).symm w.1 ∈ (chartAt H z₀.proj).source := by
    simpa [extChartAt_source] using (extChartAt I z₀.proj).map_target hq
  -- The inverse tangent trivialization at the base point is the derivative of the inverse chart.
  have htriv := TangentBundle.symmL_trivializationAt (I := I) hx
  rw [(extChartAt I z₀.proj).right_inv hq] at htriv
  ext v
  -- The derivative of the projection, read in the chart, is the base-chart derivative of `δq`.
  have hv : mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I (π (E →L[ℝ] ℝ)
        (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)) ((extChartAt (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) z₀).symm w)
        (mfderivWithin 𝓘(ℝ, E × (E →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
          (extChartAt (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) z₀).symm
          (range (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))) w (v 0)) =
      (trivializationAt E (TangentSpace I) z₀.proj).symmL ℝ ((extChartAt I z₀.proj).symm w.1)
        (v 0).1 := by
    rw [htriv]
    exact DFunLike.congr_fun (mfderiv_proj_comp_mfderivWithin_extChartAt_symm z₀ hw) (v 0)
  rw [RoughForm.inChartAt_apply, liouvilleRough_apply, hv, extChartAt_symm_apply z₀ w.2 hq,
    ContinuousLinearMap.comp_apply, Trivialization.continuousLinearMapAt_symmL _ hx,
    cotangentLiouvilleForm_apply]

/-- The coordinate expression of the rough Liouville form in a preferred chart agrees with the
linear Liouville form near every point of the chart target, within the model range. -/
private theorem inChartAt_liouvilleRough_eventuallyEq (z₀ : CotangentBundle I M)
    {w : E × (E →L[ℝ] ℝ)} (hw : w ∈ (extChartAt (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) z₀).target) :
    (liouvilleRough I M).inChartAt z₀
      =ᶠ[𝓝[range (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))] w] cotangentLiouvilleForm := by
  filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem hw] with w' hw'
  exact inChartAt_liouvilleRough z₀ hw'

/-- The rough Liouville form is `C^r` for every `r`, its chart expressions being linear. -/
private theorem isSmoothForm_liouvilleRough {r : WithTop ℕ∞} :
    IsSmoothForm (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) r (liouvilleRough I M) :=
  IsSmoothForm.of_contDiffWithinAt_inChartAt_self fun z ↦
    contDiff_cotangentLiouvilleForm.contDiffWithinAt.congr_of_eventuallyEq
      (inChartAt_liouvilleRough_eventuallyEq z (mem_extChartAt_target z))
      (inChartAt_liouvilleRough z (mem_extChartAt_target z))

variable (I M) in
/-- The **Liouville form** (tautological one-form) of the cotangent bundle `T*M`: at a covector
`p` over `x`, it evaluates a tangent vector `v` of `T*M` by `p (dπ v)`, where `π : T*M → M` is the
bundle projection. It is a smooth one-form on `T*M`, and in every bundle chart it is the linear
Liouville form `TauCeti.cotangentLiouvilleForm`, that is `Σ pᵢ dqᵢ`. -/
def liouvilleForm : SmoothForm (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (CotangentBundle I M) ℝ 1 :=
  ⟨liouvilleRough I M, isSmoothForm_liouvilleRough.mem_smoothForms⟩

/-- The underlying rough form of `liouvilleForm`. -/
private theorem coe_liouvilleForm : (liouvilleForm I M).1 = liouvilleRough I M :=
  rfl

/-- The Liouville form evaluates a tangent vector of `T*M` at the covector `z` by applying `z` to
the image of the vector under the derivative of the bundle projection. -/
@[simp]
theorem liouvilleForm_apply (z : CotangentBundle I M)
    (v : Fin 1 → TangentSpace (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) z) :
    (liouvilleForm I M).1 z v =
      z.2 (mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I (π (E →L[ℝ] ℝ)
        (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)) z (v 0)) :=
  (rfl)

/-- **Chart formula for the Liouville form.** In every preferred chart of the cotangent bundle,
with coordinates `(q, p)`, the Liouville form is the linear Liouville form
`λ_(q,p)(δq, δp) = p(δq)`, that is `Σ pᵢ dqᵢ`. -/
theorem inChartAt_liouvilleForm (z₀ : CotangentBundle I M) {w : E × (E →L[ℝ] ℝ)}
    (hw : w ∈ (extChartAt (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) z₀).target) :
    (liouvilleForm I M).1.inChartAt z₀ w = cotangentLiouvilleForm w :=
  inChartAt_liouvilleRough z₀ hw

/-- **The Liouville form is tautological.** Pulling it back along the section `x ↦ σ x` of the
cotangent bundle defined by a family of covectors `σ` gives back `σ`, at every point where that
section is differentiable. -/
theorem mpullback_liouvilleForm_section {σ : (x : M) → TangentSpace I x →L[ℝ] ℝ} {x : M}
    (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] ℝ) y (σ y)) x) :
    mpullback I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (fun y ↦ TotalSpace.mk' (E →L[ℝ] ℝ) y (σ y))
        (liouvilleForm I M).1 x =
      ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) ℝ 0 (σ x) := by
  have hcomp := mfderiv_comp x
    ((Bundle.contMDiff_proj (fun y : M ↦ TangentSpace I y →L[ℝ] ℝ) _).mdifferentiableAt
      one_ne_zero) hσ
  -- The projection of the section is the identity of `M`.
  rw [show (π (E →L[ℝ] ℝ) (fun y : M ↦ TangentSpace I y →L[ℝ] ℝ) ∘
      fun y ↦ TotalSpace.mk' (E →L[ℝ] ℝ) y (σ y)) = id from rfl, mfderiv_id] at hcomp
  ext v
  rw [mpullback_apply, liouvilleForm_apply, ContinuousAlternatingMap.ofSubsingleton_apply_apply]
  exact congrArg (σ x) (DFunLike.congr_fun hcomp (v 0)).symm

/-- **The Liouville form is tautological.** Pulling it back along the smooth section of the
cotangent bundle defined by a smooth one-form `α` gives back `α`. -/
theorem mpullback_liouvilleForm (α : SmoothForm I M ℝ 1) :
    SmoothForm.mpullback (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) x (SmoothForm.degreeOneEquiv α x))
      (SmoothForm.degreeOneEquiv α).contMDiff (liouvilleForm I M) = α := by
  apply Subtype.ext
  funext x
  rw [SmoothForm.coe_mpullback, mpullback_liouvilleForm_section
    (((SmoothForm.degreeOneEquiv α).contMDiff x).mdifferentiableAt (by simp))]
  ext v
  rw [ContinuousAlternatingMap.ofSubsingleton_apply_apply, SmoothForm.degreeOneEquiv_apply_apply]
  exact congrArg (α.1 x) (funext fun i ↦ by rw [Fin.fin_one_eq_zero i])

/-- The Liouville form pulled back by a smooth self-map `g` of the cotangent bundle covering the
identity evaluates a tangent vector at `z` by applying the covector `g z` to its image under the
derivative of the projection. -/
theorem mpullback_liouvilleForm_apply_of_proj_eq {g : CotangentBundle I M → CotangentBundle I M}
    (hg : ContMDiff (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ g)
    (hproj : ∀ z, (g z).proj = z.proj) (z : CotangentBundle I M)
    (v : Fin 1 → TangentSpace (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) z) :
    (SmoothForm.mpullback g hg (liouvilleForm I M)).1 z v =
      (g z).2 (mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) I
        (π (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)) z (v 0)) := by
  rw [SmoothForm.mpullback_apply, liouvilleForm_apply]
  exact congrArg (g z).2 (DFunLike.congr_fun
    (mfderiv_proj_comp_mfderiv_of_proj_eq ((hg z).mdifferentiableAt (by simp)) hproj) (v 0))

end Liouville

section Symplectic

variable [IsManifold I ∞ M]

variable (I M) in
/-- The **canonical symplectic form** `ω = -dλ` of the cotangent bundle `T*M`, where `λ` is the
Liouville form `TauCeti.CotangentBundle.liouvilleForm`. In every bundle chart it is the linear
form `TauCeti.strongDualCotangentSymplecticForm`, that is `Σ dqᵢ ∧ dpᵢ`. -/
def symplecticForm : SmoothTwoForm (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (CotangentBundle I M) :=
  -mextDerivₗ (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1 (liouvilleForm I M)

/-- The canonical symplectic form is minus the bundled exterior derivative of the Liouville
form. -/
theorem symplecticForm_eq_neg_mextDerivₗ :
    symplecticForm I M = -mextDerivₗ (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1 (liouvilleForm I M) :=
  (rfl)

/-- The canonical symplectic form is minus the exterior derivative of the Liouville form. -/
theorem symplecticForm_eq_neg_mextDeriv :
    (symplecticForm I M).1 = -mextDeriv (liouvilleForm I M).1 := by
  rw [symplecticForm, NegMemClass.coe_neg, mextDerivₗ_apply]

/-- **Chart formula for the canonical symplectic form.** In every preferred chart of the cotangent
bundle, the canonical symplectic form is the linear form
`TauCeti.strongDualCotangentSymplecticForm`, `ω((δq, δp), (δq', δp')) = δp'(δq) - δp(δq')`. -/
theorem inChartAt_symplecticForm_apply (z₀ : CotangentBundle I M) {w : E × (E →L[ℝ] ℝ)}
    (hw : w ∈ (extChartAt (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) z₀).target)
    (v : Fin 2 → E × (E →L[ℝ] ℝ)) :
    (symplecticForm I M).1.inChartAt z₀ w v = strongDualCotangentSymplecticForm (v 0) (v 1) := by
  have huniq : UniqueDiffWithinAt ℝ (range (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))) w :=
    (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).uniqueDiffOn w (extChartAt_target_subset_range z₀ hw)
  have hd : (mextDeriv (liouvilleRough I M)).inChartAt z₀ w =
      extDerivWithin ((liouvilleRough I M).inChartAt z₀) (range (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))) w :=
    isSmoothForm_liouvilleRough.inChartAt_mextDeriv_eq z₀ hw
  rw [symplecticForm_eq_neg_mextDeriv, coe_liouvilleForm, RoughForm.inChartAt_neg, Pi.neg_apply,
    ContinuousAlternatingMap.neg_apply, hd,
    (inChartAt_liouvilleRough_eventuallyEq z₀ hw).extDerivWithin_eq
      (inChartAt_liouvilleRough z₀ hw), extDerivWithin,
    fderivWithin_eq_fderiv huniq (differentiableAt_cotangentLiouvilleForm w),
    ← extDeriv]
  exact neg_extDeriv_cotangentLiouvilleForm_apply w v

/-- At a covector `z`, read in the preferred chart at `z` itself, where tangent vectors are their
own coordinates, the canonical symplectic form is the linear form. -/
@[simp]
theorem symplecticForm_apply (z : CotangentBundle I M)
    (v : Fin 2 → TangentSpace (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) z) :
    (symplecticForm I M).1 z v = strongDualCotangentSymplecticForm (V := E) (v 0) (v 1) := by
  have h := inChartAt_symplecticForm_apply z (mem_extChartAt_target z) v
  rw [RoughForm.inChartAt_extChartAt_self] at h
  -- Tangent vectors at `z` are their own coordinates in the chart at `z`.
  exact h

/-- The canonical symplectic form, evaluated on an ordered pair of tangent vectors at a covector
`z`, is the linear form `TauCeti.strongDualCotangentSymplecticForm`. -/
theorem eval₂_symplecticForm (z : CotangentBundle I M)
    (v w : TangentSpace (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) z) :
    SmoothForm.eval₂ (symplecticForm I M) z v w =
      strongDualCotangentSymplecticForm (V := E) v w := by
  simp

/-- The canonical symplectic form of the cotangent bundle is closed and nondegenerate. -/
theorem isSymplectic_symplecticForm : (symplecticForm I M).IsSymplectic where
  isClosed := by
    rw [SmoothForm.isClosed_def, symplecticForm_eq_neg_mextDeriv, mextDeriv_neg,
      SmoothForm.mextDeriv_mextDeriv, neg_zero]
  isNondegenerate := by
    rw [SmoothTwoForm.isNondegenerate_iff_separatingLeft]
    intro z v hv
    exact (strongDualCotangentSymplecticForm (V := E)).nondegenerate.1 v fun w ↦
      (eval₂_symplecticForm z v w).symm.trans (hv w)

end Symplectic

end CotangentBundle

end TauCeti
