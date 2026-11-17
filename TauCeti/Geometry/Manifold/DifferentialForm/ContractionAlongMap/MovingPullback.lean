/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.ContractionAlongMap.Family
public import TauCeti.Geometry.Manifold.DifferentialForm.Flow.Family
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Family

/-!
# Differentiation of moving pullbacks of differential forms

Let `P : M × ℝ → N` (or `P : M × ↥J → N` for `J : TopologicalSpace.Opens ℝ`) be a `C²` moving
family of maps between `C²` manifolds (possibly with boundary or corners), with slices
`p_t x = P (x, t)` and parameter velocity `V_t x = dP_{(x, t)} (0, 1)` (`TauCeti.mfamilyVelocity`).
Without assuming invertibility of the slices `p_t`, boundarylessness of `M` or `N`, or completeness
of the coefficient space `F`, the pulled-back forms `(p_u^* ω)_x` satisfy the Cartan-type variation
formula

`d/du |_{u = t} (p_u^* ω)_x = d(C_(p_t, V_t) ω)_x + C_(p_t, V_t)(dω)_x`

in the fixed alternating-form fiber `E [⋀^Fin (k + 1)]→L[ℝ] F`
(`TauCeti.hasDerivAt_mpullback_family`, `TauCeti.hasMFDerivAt_mpullback_family_opens`), where
`C_(p_t, V_t)` is `TauCeti.mfamilyContraction`.

Allowing the form `ω_u` to vary smoothly with `u` adds the temporal derivative `(p_t^* (∂_t ω_t))_x`
(`TauCeti.hasDerivAt_mpullback_family_form`, `TauCeti.hasMFDerivAt_mpullback_family_form_opens`),
proved by lifting `ω` horizontally to `ℝ × N` and applying `TauCeti.hasDerivAt_mpullback_family`
along `(y, u) ↦ (u, P (y, u))`. Specializing to `TauCeti.timeDependentFlowOf` connects the moving
contraction and variation identity to Moser's Lie-derivative formula
`TauCeti.hasDerivAt_mpullback_timeDependentFlowOf_mpullback_prodMk`.

## Main results

* `TauCeti.hasMFDerivAt_comp_family_mfamilyContraction_mextDeriv`,
  `TauCeti.hasDerivAt_comp_family_mfamilyContraction_mextDeriv`: degree-zero counterpart
  `∂_t (f ∘ p_t)_x = C_(p_t, V_t)(df)_x 0` for differentiable `P : M × T → N` (general `T` and
  `T = ℝ`) and `f`.
* `TauCeti.hasDerivAt_mpullback_family`, `TauCeti.hasDerivAt_mpullback_family_apply`,
  `TauCeti.hasMFDerivAt_mpullback_family_opens`,
  `TauCeti.hasMFDerivAt_mpullback_family_opens_apply`: differentiation of `u ↦ (p_u^* ω)_x` over
  `ℝ` and over `J : Opens ℝ` in the fixed alternating-form fiber and evaluated on tangent tuples.
* `TauCeti.hasDerivAt_mpullback_family_form`, `TauCeti.hasMFDerivAt_mpullback_family_form_opens`:
  for a jointly differentiable moving family of forms `ω_u` (over `ℝ` or `J : Opens ℝ`),
  `∂_t (p_t^* ω_t)_x = (p_t^* (∂_t ω_t))_x + d(C_(p_t, V_t) ω_t)_x + C_(p_t, V_t)(dω_t)_x`.
* `TauCeti.mfamilyContraction_timeDependentFlowOf_of_mem`,
  `TauCeti.mpullback_timeDependentFlowOf_add_mlieDerivForm_eq_add_mfamilyContraction_of_mem`: on a
  finite-dimensional Hausdorff boundaryless `C¹` manifold `M` with a jointly `C¹` time-dependent
  vector field `X` and flow `φ_{s, t}`, `C_(φ_{s, t}, V_t) ω = φ_{s, t}^* (ω.interior (X t))`.
  When `M` is `C²` with `[I.Boundaryless]`, `X` is `C²`, and `α` is a `C¹` form on `ℝ × M`, this
  identifies the moving-form derivative with the Moser Lie-derivative sum of
  `TauCeti.hasDerivAt_mpullback_timeDependentFlowOf_mpullback_prodMk`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapters 14, 17, and 22.
* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., §3.2.
-/

public section

noncomputable section

open Bundle Set Filter TopologicalSpace ContinuousAlternatingMap
open scoped Manifold Topology

namespace TauCeti

variable {E H M E' H' N F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace N] [ChartedSpace H' N] {I' : ModelWithCorners ℝ E' H'}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {k : ℕ}

/-! ### Helpers for open parameter intervals `J : Opens ℝ` -/

private theorem hasMFDerivAt_subtype_val_opens (J : Opens ℝ) (t : J) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (Subtype.val : J → ℝ) t (ContinuousLinearMap.id ℝ ℝ) := by
  have h := ((contMDiff_subtype_val (I := 𝓘(ℝ, ℝ)) (U := J) (n := 1)).mdifferentiableAt
    one_ne_zero (x := t)).hasMFDerivAt
  have hid : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (Subtype.val : J → ℝ) t =
      (ContinuousLinearMap.id ℝ ℝ :
        TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) (t : ℝ)) := by
    rw [Manifold.mfderiv_subtype_val]
    exact ContinuousLinearMap.ext fun v ↦ Manifold.tangentSpaceOpenEquiv_apply t v
  exact hid ▸ h

private def retractOpensAt {J : Opens ℝ} (t : J) : ℝ → ↥J :=
  Subtype.val.extend id (fun _ ↦ t)

private theorem retractOpensAt_coe {J : Opens ℝ} (t u : J) :
    retractOpensAt t (u : ℝ) = u :=
  Subtype.val_injective.extend_apply id _ u

private theorem contMDiffAt_retractOpensAt {r : WithTop ℕ∞} {J : Opens ℝ} (t : J) :
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) r (retractOpensAt t) (t : ℝ) :=
  contMDiffAt_id.extend_subtypeVal _

/-! ### Differentiation of pullbacks along moving maps -/

/-- **Differentiation of moving pullbacks in degree zero over a general parameter manifold `T`.**
For a `1`-dimensional real parameter space `T` modelled on `𝓘(ℝ, ℝ)` (such as `ℝ` or `↥J` for
`J : Opens ℝ`), `P : M × T → N` differentiable at `(x, t)`, and `f : N → F` differentiable at
`P (x, t)`, `u ↦ f (P (x, u))` has manifold derivative
`(1 : ℝ →L[ℝ] ℝ).smulRight (C_(p_t, V_t)(df)_x 0)` at `t`. -/
theorem hasMFDerivAt_comp_family_mfamilyContraction_mextDeriv
    {T : Type*} [TopologicalSpace T] [ChartedSpace ℝ T]
    {P : M × T → N} {f : N → F} {x : M} {t : T}
    (hP : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) I' P (x, t))
    (hf : MDifferentiableAt I' 𝓘(ℝ, F) f (P (x, t))) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (fun u : T ↦ f (P (x, u))) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (mfamilyContraction I I' P t (mextDeriv (RoughForm.ofFunction I' f)) x 0)) := by
  have hcurve : MDifferentiableAt 𝓘(ℝ, ℝ) I' (fun u : T ↦ P (x, u)) t :=
    hP.comp t (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  have hcomp := hf.hasMFDerivAt.comp t hcurve.hasMFDerivAt
  have hderiv : (mfderiv I' 𝓘(ℝ, F) f (P (x, t))).comp
      (mfderiv 𝓘(ℝ, ℝ) I' (fun u : T ↦ P (x, u)) t) =
      (1 : ℝ →L[ℝ] ℝ).smulRight
        (mfamilyContraction I I' P t (mextDeriv (RoughForm.ofFunction I' f)) x 0) := by
    let oneT : TangentSpace 𝓘(ℝ, ℝ) t := (1 : ℝ)
    have h1 : ((mfderiv I' 𝓘(ℝ, F) f (P (x, t))).comp
        (mfderiv 𝓘(ℝ, ℝ) I' (fun u : T ↦ P (x, u)) t)) oneT =
        mfamilyContraction I I' P t (mextDeriv (RoughForm.ofFunction I' f)) x 0 := by
      rw [ContinuousLinearMap.comp_apply, ← mfamilyVelocity_eq_mfderiv_slice_right_apply hP,
        mfamilyContraction_apply]
      have hvec : (Matrix.vecCons (mfamilyVelocity I I' P t x)
          fun i : Fin 0 ↦ mfderiv I I' (fun y ↦ P (y, t)) x ((0 : Fin 0 → TangentSpace I x) i)) =
          ![mfamilyVelocity I I' P t x] :=
        congrArg (Matrix.vecCons _) (Subsingleton.elim _ ![])
      rw [mfamilyVelocity_def] at hvec
      rw [hvec, mextDeriv_ofFunction_apply, mfamilyVelocity_def]
    refine ContinuousLinearMap.ext fun (v : TangentSpace 𝓘(ℝ, ℝ) t) ↦ ?_
    let r : ℝ := v
    have hv : v = r • oneT := (mul_one r).symm
    have hstep : ((mfderiv I' 𝓘(ℝ, F) f (P (x, t))).comp
        (mfderiv 𝓘(ℝ, ℝ) I' (fun u : T ↦ P (x, u)) t)) v =
        r • ((mfderiv I' 𝓘(ℝ, F) f (P (x, t))).comp
          (mfderiv 𝓘(ℝ, ℝ) I' (fun u : T ↦ P (x, u)) t)) oneT := by
      rw [← map_smul, ← hv]
    exact hstep.trans (by rw [h1]; rfl)
  exact hderiv ▸ hcomp

/-- **Differentiation of moving pullbacks in degree zero over `ℝ`.** For `P : M × ℝ → N`
differentiable at `(x, t)` and `f : N → F` differentiable at `P (x, t)`, `u ↦ f (P (x, u))` has
derivative `C_(p_t, V_t)(df)_x 0` at `t`. -/
theorem hasDerivAt_comp_family_mfamilyContraction_mextDeriv
    {P : M × ℝ → N} {f : N → F} {x : M} {t : ℝ}
    (hP : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) I' P (x, t))
    (hf : MDifferentiableAt I' 𝓘(ℝ, F) f (P (x, t))) :
    HasDerivAt (fun u ↦ f (P (x, u)))
      (mfamilyContraction I I' P t (mextDeriv (RoughForm.ofFunction I' f)) x 0) t :=
  hasDerivAt_iff_hasFDerivAt.mpr
    (hasMFDerivAt_comp_family_mfamilyContraction_mextDeriv hP hf).hasFDerivAt

/-- Chart chain-rule step: pushing forward the flat spatial derivative of
`e' ∘ P ∘ (e.symm × id)` at `(y, t)` along `e'.symm` recovers the manifold derivative of the slice
`z ↦ P (z, t)` applied to `de.symm_y w`. -/
private theorem mfderivWithin_extChartAt_symm_fderivWithin_slice
    [IsManifold I 1 M] [IsManifold I' 1 N] {P : M × ℝ → N} {t : ℝ} (x₀ : M) (y₀ : N)
    {s : Set E} {y : E} (hy_tar : y ∈ (extChartAt I x₀).target) (hset : s =ᶠ[𝓝 y] range I)
    (hft : MDifferentiableAt I I' (fun z ↦ P (z, t)) ((extChartAt I x₀).symm y))
    (hy' : P ((extChartAt I x₀).symm y, t) ∈ (extChartAt I' y₀).source) (w : E) :
    mfderivWithin 𝓘(ℝ, E') I' (extChartAt I' y₀).symm (range I')
        (extChartAt I' y₀ (P ((extChartAt I x₀).symm y, t)))
        (fderivWithin ℝ
          (fun z ↦ (extChartAt I' y₀ ∘ P ∘ Prod.map (extChartAt I x₀).symm id) (z, t)) s y w) =
      mfderiv I I' (fun z ↦ P (z, t)) ((extChartAt I x₀).symm y)
        (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm (range I) y w) := by
  set e := extChartAt I x₀; set e' := extChartAt I' y₀
  set G : E × ℝ → E' := e' ∘ P ∘ Prod.map e.symm id
  have hy_rng : y ∈ range I := extChartAt_target_subset_range x₀ hy_tar
  have he'd : MDifferentiableAt I' 𝓘(ℝ, E') e' (P (e.symm y, t)) :=
    mdifferentiableAt_extChartAt (by simpa only [e', extChartAt_source] using hy')
  have h1 : fderivWithin ℝ (fun z ↦ G (z, t)) s y w =
      fderivWithin ℝ (fun z ↦ G (z, t)) (range I) y w :=
    congrArg (fun L : E →L[ℝ] E' ↦ L w)
      (fderivWithin_congr_set (𝕜 := ℝ) (f := fun z ↦ G (z, t)) hset)
  have he_symm : MDifferentiableWithinAt 𝓘(ℝ, E) I e.symm (range I) y :=
    mdifferentiableWithinAt_extChartAt_symm hy_tar
  have hef : MDifferentiableAt I 𝓘(ℝ, E') (e' ∘ fun z ↦ P (z, t)) (e.symm y) :=
    he'd.comp (e.symm y) hft
  have hmw : HasMFDerivWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E') (fun z ↦ G (z, t)) (range I) y
      ((mfderiv I 𝓘(ℝ, E') (e' ∘ fun z ↦ P (z, t)) (e.symm y)).comp
        (mfderivWithin 𝓘(ℝ, E) I e.symm (range I) y)) :=
    hef.hasMFDerivAt.comp_hasMFDerivWithinAt y he_symm.hasMFDerivWithinAt
  have h2' := congrArg (fun L : TangentSpace 𝓘(ℝ, E) y →L[ℝ]
    TangentSpace 𝓘(ℝ, E') (G (y, t)) ↦ L w) (hmw.mfderivWithin (I.uniqueMDiffOn y hy_rng))
  rw [mfderivWithin_eq_fderivWithin] at h2'
  have h2 : fderivWithin ℝ (fun z ↦ G (z, t)) (range I) y w =
      mfderiv I 𝓘(ℝ, E') (e' ∘ fun z ↦ P (z, t)) (e.symm y)
        (mfderivWithin 𝓘(ℝ, E) I e.symm (range I) y w) := h2'
  have hcomp2 := mfderiv_comp_apply (e.symm y) he'd hft
    (mfderivWithin 𝓘(ℝ, E) I e.symm (range I) y w)
  have hchain : fderivWithin ℝ (fun z ↦ G (z, t)) s y w =
      mfderiv I' 𝓘(ℝ, E') e' (P (e.symm y, t))
        (mfderiv I I' (fun z ↦ P (z, t)) (e.symm y)
          (mfderivWithin 𝓘(ℝ, E) I e.symm (range I) y w)) :=
    h1.trans (h2.trans hcomp2)
  exact (congrArg
    (mfderivWithin 𝓘(ℝ, E') I' e'.symm (range I') (e' (P (e.symm y, t)))) hchain).trans
    (congrArg (fun L : TangentSpace I' (P (e.symm y, t)) →L[ℝ]
      TangentSpace I' (P (e.symm y, t)) ↦ L _)
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hy'))

/-- In preferred charts centred at `x₀` and `y₀`, `mfamilyContraction` read at `y ∈ s` agrees with
the flat `familyContractionWithin` of the coordinate expression of the form. -/
private theorem inChartAt_mfamilyContraction_eq_familyContractionWithin
    [IsManifold I 1 M] [IsManifold I' 1 N] {m : ℕ} {P : M × ℝ → N} {t : ℝ} (x₀ : M) (y₀ : N)
    {s : Set E} (hs : s ⊆ (extChartAt I x₀).target) {y : E} (hy : y ∈ s) (hset : s =ᶠ[𝓝 y] range I)
    (hPy : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) I' P ((extChartAt I x₀).symm y, t))
    (hy' : P ((extChartAt I x₀).symm y, t) ∈ (extChartAt I' y₀).source)
    (η : RoughForm I' N F (m + 1)) :
    (mfamilyContraction I I' P t η).inChartAt x₀ y =
      familyContractionWithin (extChartAt I' y₀ ∘ P ∘ Prod.map (extChartAt I x₀).symm id)
        s t (η.inChartAt y₀) y := by
  set e := extChartAt I x₀; set e' := extChartAt I' y₀
  set G : E × ℝ → E' := e' ∘ P ∘ Prod.map e.symm id
  have hy_tar : y ∈ e.target := hs hy
  have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I' (fun u ↦ P (e.symm y, u)) t :=
    hPy.comp t (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  have he'd : MDifferentiableAt I' 𝓘(ℝ, E') e' (P (e.symm y, t)) :=
    mdifferentiableAt_extChartAt (by simpa only [e', extChartAt_source] using hy')
  have hvel : mfderivWithin 𝓘(ℝ, E') I' e'.symm (range I') (e' (P (e.symm y, t)))
      (deriv (fun u ↦ G (y, u)) t) = mfamilyVelocity I I' P t (e.symm y) := by
    let L : ℝ →L[ℝ] E' :=
      (mfderiv I' 𝓘(ℝ, E') e' (P (e.symm y, t))).comp
        (mfderiv 𝓘(ℝ, ℝ) I' (fun u ↦ P (e.symm y, u)) t)
    have hfd : HasFDerivAt (fun u ↦ G (y, u)) L t :=
      (he'd.hasMFDerivAt.comp t hγ.hasMFDerivAt).hasFDerivAt
    have hderiv : deriv (fun u ↦ G (y, u)) t =
        mfderiv I' 𝓘(ℝ, E') e' (P (e.symm y, t))
          (mfderiv 𝓘(ℝ, ℝ) I' (fun u ↦ P (e.symm y, u)) t (1 : ℝ)) :=
      hfd.hasDerivAt.deriv
    have hc1 := congrArg
      (mfderivWithin 𝓘(ℝ, E') I' e'.symm (range I') (e' (P (e.symm y, t)))) hderiv
    have hc2 := congrArg
      (fun L ↦ L (mfderiv 𝓘(ℝ, ℝ) I' (fun u ↦ P (e.symm y, u)) t (1 : ℝ)))
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hy')
    exact hc1.trans (hc2.trans (mfamilyVelocity_eq_mfderiv_slice_right_apply hPy).symm)
  have hft : MDifferentiableAt I I' (fun w ↦ P (w, t)) (e.symm y) :=
    hPy.comp (e.symm y) (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  ext v
  rw [RoughForm.inChartAt_apply, mfamilyContraction_apply, familyContractionWithin_apply,
    RoughForm.inChartAt_apply]
  have hGyt : G (y, t) = e' (P (e.symm y, t)) := rfl
  rw [hGyt, e'.left_inv hy']
  refine congrArg (η (P (e.symm y, t))) (funext fun i ↦ ?_)
  cases i using Fin.cases with
  | zero =>
    simp only [Matrix.cons_val_zero]
    rw [← mfamilyVelocity_def]
    exact hvel.symm
  | succ i =>
    simp only [Matrix.cons_val_succ]
    exact (mfderivWithin_extChartAt_symm_fderivWithin_slice x₀ y₀ hy_tar hset hft hy' (v i)).symm

/-- **Differentiation of moving pullbacks on manifolds.** Let `P : M × ℝ → N` be `C^r` (`2 ≤ r`) at
`(x₀, t)` between `C²` manifolds (possibly with boundary or corners), and let `ω` be a
`(k + 1)`-form on `N` differentiable at `P (x₀, t)`. Then `u ↦ (p_u^* ω)_{x₀}` has derivative
`d(C_(p_t, V_t) ω)_{x₀} + C_(p_t, V_t)(dω)_{x₀}` at `t` in the fixed fiber
`TangentSpace I x₀ [⋀^Fin (k + 1)]→L[ℝ] F`, with neither completeness of `F` nor invertibility of
the slices `p_u`. -/
theorem hasDerivAt_mpullback_family [IsManifold I 2 M] [IsManifold I' 2 N]
    {r : WithTop ℕ∞} {P : M × ℝ → N} {ω : RoughForm I' N F (k + 1)} {x₀ : M} {t : ℝ}
    (hP : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I' r P (x₀, t)) (hr : 2 ≤ r)
    (hω : MDifferentiableAt I' (I'.prod 𝓘(ℝ, E' [⋀^Fin (k + 1)]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E' [⋀^Fin (k + 1)]→L[ℝ] F) z (ω z)) (P (x₀, t))) :
    HasDerivAt (F := E [⋀^Fin (k + 1)]→L[ℝ] F)
      (fun u ↦ mpullback I I' (fun y ↦ P (y, u)) ω x₀)
      (mextDeriv (mfamilyContraction I I' P t ω) x₀ +
        mfamilyContraction I I' P t (mextDeriv ω) x₀) t := by
  have : IsManifold I 1 M := IsManifold.of_le one_le_two
  have : IsManifold I' 1 N := IsManifold.of_le one_le_two
  have : IsManifold I ((1 : ℕ∞) + 1 : WithTop ℕ∞) M := IsManifold.of_le (n := 2) (by norm_num)
  have hP2 : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I' 2 P (x₀, t) := hP.of_le hr
  obtain ⟨s, hsub, hsu, -, hsn, hxs, hxc⟩ :=
    exists_convex_uniqueDiffOn_mem_nhdsWithin_extChartAt (I := I) x₀
  set e := extChartAt I x₀; set z₀ := e x₀; set y₀ := P (x₀, t); set e' := extChartAt I' y₀
  have hz₀_inv : e.symm z₀ = x₀ := extChartAt_to_inv x₀
  have hset : s =ᶠ[𝓝 z₀] range I := by
    filter_upwards [mem_nhdsWithin_iff_eventually.1 hsn] with y hy
    exact ⟨fun h ↦ extChartAt_target_subset_range x₀ (hsub h), hy⟩
  set φ : E × ℝ → M × ℝ := Prod.map e.symm id
  set G : E × ℝ → E' := e' ∘ P ∘ φ
  have hφ_pt : φ (z₀, t) = (x₀, t) := Prod.ext hz₀_inv rfl
  have hG_pt : G (z₀, t) = e' y₀ := congrArg (e' ∘ P) hφ_pt
  have hφ_smooth : ContMDiffWithinAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) 2 φ
      (s ×ˢ univ) (z₀, t) :=
    ((contMDiffOn_extChartAt_symm (n := 2) x₀).mono hsub z₀ hxs).prodMap
      (contMDiffWithinAt_id (I := 𝓘(ℝ, ℝ)))
  have hPφ_smooth : ContMDiffWithinAt (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) I' 2 (P ∘ φ) (s ×ˢ univ) (z₀, t) :=
    hP2.comp_contMDiffWithinAt_of_eq hφ_smooth hφ_pt
  have hG_smooth : ContDiffWithinAt ℝ 2 G (s ×ˢ univ) (z₀, t) := by
    have hG_m := (contMDiffAt_extChartAt (I := I') (n := 2) (x := y₀)).comp_contMDiffWithinAt_of_eq
      hPφ_smooth (congrArg P hφ_pt)
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod,
      contMDiffWithinAt_iff_contDiffWithinAt] at hG_m
    exact hG_m
  have hmaps : G ⁻¹' range I' ∈ 𝓝[s ×ˢ univ] (z₀, t) := by
    have hpre : (P ∘ φ) ⁻¹' e'.source ∈ 𝓝[s ×ˢ univ] (z₀, t) :=
      hPφ_smooth.continuousWithinAt.preimage_mem_nhdsWithin
        (by simpa only [Function.comp_apply, hφ_pt] using extChartAt_source_mem_nhds (I := I') y₀)
    filter_upwards [hpre] with q hq
    exact extChartAt_target_subset_range y₀ (e'.map_source hq)
  have hform : DifferentiableWithinAt ℝ (ω.inChartAt y₀) (range I') (G (z₀, t)) := by
    rw [hG_pt]
    exact ω.differentiableWithinAt_range_inChartAt_of_mdifferentiableAt hω
  have hflat := hasDerivAt_compContinuousLinearMap_fderivWithin_family hsu hxc hxs isOpen_univ
    (mem_univ t) hG_smooth le_rfl hmaps hform
  -- 1. Identify the pulled-back curve near `t`.
  have hcurve_eq : (fun u ↦ mpullback I I' (fun y ↦ P (y, u)) ω x₀) =ᶠ[𝓝 t]
      fun u ↦ (ω.inChartAt y₀ (G (z₀, u))).compContinuousLinearMap
        (fderivWithin ℝ (fun y ↦ G (y, u)) s z₀) := by
    have hP_nhds : ∀ᶠ u in 𝓝 t, ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I' 2 P (x₀, u) :=
      ((continuous_const.prodMk continuous_id).tendsto t).eventually
        ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hP2)
    have hsrc_nhds : ∀ᶠ u in 𝓝 t, P (x₀, u) ∈ e'.source :=
      (hP2.continuousAt.comp (continuous_const.prodMk continuous_id).continuousAt).preimage_mem_nhds
        (extChartAt_source_mem_nhds (I := I') y₀)
    filter_upwards [hP_nhds, hsrc_nhds] with u hPu hyu
    have hPu_d : MDifferentiableAt I I' (fun y ↦ P (y, u)) x₀ :=
      (hPu.comp x₀ (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt two_ne_zero
    rw [ω.mpullback_eq_compContinuousLinearMap y₀ hPu_d hyu, ← fderivWithin_congr_set hset]
    have hGu : G (z₀, u) = e' (P (x₀, u)) := by
      simp only [G, φ, Function.comp_apply, Prod.map_apply, hz₀_inv, id_eq]
    rw [hGu]; rfl
  -- 2. Identify the first derivative term `d(C_(p_t, V_t) ω)_{x₀}`.
  obtain ⟨O, hO_eq, hO_open, hzO⟩ := mem_nhds_iff.mp hset
  have hd_contr : mextDeriv (mfamilyContraction I I' P t ω) x₀ =
      extDerivWithin (familyContractionWithin G s t (ω.inChartAt y₀)) s z₀ := by
    have he_cont : ContinuousWithinAt (fun y : E ↦ (e.symm y, t)) s z₀ :=
      (((contMDiffOn_extChartAt_symm (n := 1) x₀).mono hsub z₀ hxs).continuousWithinAt).prodMk
        continuousWithinAt_const
    have hP_s : ∀ᶠ y in 𝓝[s] z₀, ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I' 2 P (e.symm y, t) :=
      he_cont.tendsto.eventually
        (by simpa only [hz₀_inv] using (contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hP2)
    have hsrc_s : ∀ᶠ y in 𝓝[s] z₀, P (e.symm y, t) ∈ e'.source :=
      (ContinuousAt.comp_continuousWithinAt
        (by simpa only [hz₀_inv] using hP2.continuousAt) he_cont).preimage_mem_nhdsWithin
        (by simpa only [Function.comp_apply, hz₀_inv, y₀] using
          extChartAt_source_mem_nhds (I := I') y₀)
    have heq : (mfamilyContraction I I' P t ω).inChartAt x₀ =ᶠ[𝓝[s] z₀]
        familyContractionWithin G s t (ω.inChartAt y₀) := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hO_open.mem_nhds hzO),
        hP_s, hsrc_s] with y hys hyO hPy hy'
      have hset_y : s =ᶠ[𝓝 y] range I :=
        Filter.eventually_of_mem (hO_open.mem_nhds hyO) fun w hw ↦ hO_eq hw
      exact inChartAt_mfamilyContraction_eq_familyContractionWithin (P := P) (t := t)
        x₀ y₀ hsub hys hset_y (hPy.mdifferentiableAt two_ne_zero) hy' ω
    rw [mextDeriv_def, ← extDerivWithin_congr_set hset]
    exact heq.extDerivWithin_eq (heq.self_of_nhdsWithin hxs)
  -- 3. Identify the second derivative term `C_(p_t, V_t)(dω)_{x₀}`.
  have hcontr_d : mfamilyContraction I I' P t (mextDeriv ω) x₀ =
      familyContractionWithin G s t (extDerivWithin (ω.inChartAt y₀) (range I')) z₀ := by
    have h1 := (RoughForm.inChartAt_extChartAt_self
      (mfamilyContraction I I' P t (mextDeriv ω)) x₀).symm
    have h2 := inChartAt_mfamilyContraction_eq_familyContractionWithin (P := P) (t := t)
      x₀ y₀ hsub hxs hset
      (by rw [extChartAt_to_inv]; exact hP2.mdifferentiableAt two_ne_zero)
      (by rw [extChartAt_to_inv]; exact mem_extChartAt_source y₀) (mextDeriv ω)
    have hG_def : e' ∘ P ∘ Prod.map e.symm id = G := rfl
    rw [hG_def] at h2
    refine (h1.trans h2).trans ?_
    ext v
    simp only [familyContractionWithin_apply, hG_pt]
    have hd_pt : (mextDeriv ω).inChartAt y₀ (e' y₀) =
        extDerivWithin (ω.inChartAt y₀) (range I') (e' y₀) :=
      (RoughForm.inChartAt_extChartAt_self (mextDeriv ω) y₀).trans (mextDeriv_def ω y₀)
    rw [hd_pt]
  rw [hd_contr, hcontr_d]
  exact hflat.congr_of_eventuallyEq hcurve_eq

/-- Pointwise evaluation of `hasDerivAt_mpullback_family` on a fixed tuple of tangent vectors. -/
theorem hasDerivAt_mpullback_family_apply [IsManifold I 2 M] [IsManifold I' 2 N]
    {r : WithTop ℕ∞} {P : M × ℝ → N} {ω : RoughForm I' N F (k + 1)} {x₀ : M} {t : ℝ}
    (hP : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I' r P (x₀, t)) (hr : 2 ≤ r)
    (hω : MDifferentiableAt I' (I'.prod 𝓘(ℝ, E' [⋀^Fin (k + 1)]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E' [⋀^Fin (k + 1)]→L[ℝ] F) z (ω z)) (P (x₀, t)))
    (v : Fin (k + 1) → TangentSpace I x₀) :
    HasDerivAt (fun u ↦ mpullback I I' (fun y ↦ P (y, u)) ω x₀ v)
      (mextDeriv (mfamilyContraction I I' P t ω) x₀ v +
        mfamilyContraction I I' P t (mextDeriv ω) x₀ v) t := by
  let ev : (E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] F :=
    ContinuousAlternatingMap.apply ℝ E F v
  exact ev.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_mpullback_family hP hr hω)

/-- **Differentiation of moving pullbacks over an open parameter set `J : Opens ℝ`.** For a `C^r`
(`2 ≤ r`) family `P : M × ↥J → N` between `C²` manifolds and `ω` differentiable at `P (x₀, t)`,
`u ↦ (p_u^* ω)_{x₀}` has manifold derivative `(1 : ℝ →L[ℝ] ℝ).smulRight (d(C_(p_t, V_t) ω)_{x₀} +
C_(p_t, V_t)(dω)_{x₀})` at `t` in the fixed alternating-form fiber `E [⋀^Fin (k + 1)]→L[ℝ] F`. -/
theorem hasMFDerivAt_mpullback_family_opens [IsManifold I 2 M] [IsManifold I' 2 N]
    {r : WithTop ℕ∞} {J : Opens ℝ} {P : M × ↥J → N} {ω : RoughForm I' N F (k + 1)}
    {x₀ : M} {t : J}
    (hP : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I' r P (x₀, t)) (hr : 2 ≤ r)
    (hω : MDifferentiableAt I' (I'.prod 𝓘(ℝ, E' [⋀^Fin (k + 1)]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E' [⋀^Fin (k + 1)]→L[ℝ] F) z (ω z)) (P (x₀, t))) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E [⋀^Fin (k + 1)]→L[ℝ] F) (M' := E [⋀^Fin (k + 1)]→L[ℝ] F)
      (fun u : J ↦ (mpullback I I' (fun y ↦ P (y, u)) ω x₀ : E [⋀^Fin (k + 1)]→L[ℝ] F)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (M₂ := E [⋀^Fin (k + 1)]→L[ℝ] F)
        (mextDeriv (mfamilyContraction I I' P t ω) x₀ +
          mfamilyContraction I I' P t (mextDeriv ω) x₀)) := by
  let P' : M × ℝ → N := P ∘ Prod.map id (retractOpensAt t)
  have hP'_apply (y : M) (u : J) : P' (y, (u : ℝ)) = P (y, u) :=
    congrArg P (Prod.ext rfl (retractOpensAt_coe t u))
  have hP'_eq : P' ∘ Prod.map id (Subtype.val : J → ℝ) = P :=
    funext fun q ↦ hP'_apply q.1 q.2
  have hP'_smooth : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I' r P' (x₀, (t : ℝ)) :=
    hP.comp_of_eq (contMDiffAt_id.prodMap (contMDiffAt_retractOpensAt t))
      (Prod.ext rfl (retractOpensAt_coe t t))
  have hω' : MDifferentiableAt I' (I'.prod 𝓘(ℝ, E' [⋀^Fin (k + 1)]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E' [⋀^Fin (k + 1)]→L[ℝ] F) z (ω z)) (P' (x₀, (t : ℝ))) := by
    rwa [hP'_apply x₀ t]
  have hcomp := (hasDerivAt_mpullback_family hP'_smooth hr hω').hasFDerivAt.hasMFDerivAt.comp t
    (hasMFDerivAt_subtype_val_opens J t)
  have hval :
      (mextDeriv (mfamilyContraction I I' P' (t : ℝ) ω) x₀ +
        mfamilyContraction I I' P' (t : ℝ) (mextDeriv ω) x₀ : E [⋀^Fin (k + 1)]→L[ℝ] F) =
      mextDeriv (mfamilyContraction I I' P t ω) x₀ +
        mfamilyContraction I I' P t (mextDeriv ω) x₀ := by
    simp only [← mfamilyContraction_comp_prodMap_subtype_val J P' t ω,
      ← mfamilyContraction_comp_prodMap_subtype_val J P' t (mextDeriv ω), hP'_eq]
  have hder := (ContinuousLinearMap.toSpanSingleton_comp (ContinuousLinearMap.id ℝ ℝ) _).trans
    (congrArg ((1 : ℝ →L[ℝ] ℝ).smulRight (M₂ := E [⋀^Fin (k + 1)]→L[ℝ] F)) hval)
  have hfun : (fun u : ℝ ↦ (mpullback I I' (fun y ↦ P' (y, u)) ω x₀ : E [⋀^Fin (k + 1)]→L[ℝ] F)) ∘
        (Subtype.val : J → ℝ) =
      fun u : J ↦ (mpullback I I' (fun y ↦ P (y, u)) ω x₀ : E [⋀^Fin (k + 1)]→L[ℝ] F) :=
    funext fun u ↦ congrArg (fun p ↦ (mpullback I I' p ω x₀ : E [⋀^Fin (k + 1)]→L[ℝ] F))
      (funext fun y ↦ hP'_apply y u)
  exact hfun ▸ hder ▸ hcomp

/-- Pointwise evaluation of `hasMFDerivAt_mpullback_family_opens` on a fixed tuple of tangent
vectors. -/
theorem hasMFDerivAt_mpullback_family_opens_apply [IsManifold I 2 M] [IsManifold I' 2 N]
    {r : WithTop ℕ∞} {J : Opens ℝ} {P : M × ↥J → N} {ω : RoughForm I' N F (k + 1)}
    {x₀ : M} {t : J}
    (hP : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I' r P (x₀, t)) (hr : 2 ≤ r)
    (hω : MDifferentiableAt I' (I'.prod 𝓘(ℝ, E' [⋀^Fin (k + 1)]→L[ℝ] F))
      (fun z ↦ TotalSpace.mk' (E' [⋀^Fin (k + 1)]→L[ℝ] F) z (ω z)) (P (x₀, t)))
    (v : Fin (k + 1) → TangentSpace I x₀) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F)
      (fun u : J ↦ mpullback I I' (fun y ↦ P (y, u)) ω x₀ v) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (mextDeriv (mfamilyContraction I I' P t ω) x₀ v +
          mfamilyContraction I I' P t (mextDeriv ω) x₀ v)) := by
  let ev : (E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] F :=
    ContinuousAlternatingMap.apply ℝ E F v
  have hcomp := HasMFDerivAt.comp (I := 𝓘(ℝ, ℝ)) t ev.hasFDerivAt.hasMFDerivAt
    (hasMFDerivAt_mpullback_family_opens hP hr hω)
  have hder : ev.comp ((1 : ℝ →L[ℝ] ℝ).smulRight (M₂ := E [⋀^Fin (k + 1)]→L[ℝ] F)
      (mextDeriv (mfamilyContraction I I' P t ω) x₀ +
        mfamilyContraction I I' P t (mextDeriv ω) x₀)) =
      (1 : ℝ →L[ℝ] ℝ).smulRight
        (mextDeriv (mfamilyContraction I I' P t ω) x₀ v +
          mfamilyContraction I I' P t (mextDeriv ω) x₀ v) := by
    apply ContinuousLinearMap.ext_ring
    let d : E [⋀^Fin (k + 1)]→L[ℝ] F :=
      mextDeriv (mfamilyContraction I I' P t ω) x₀ +
        mfamilyContraction I I' P t (mextDeriv ω) x₀
    exact (congrArg ev (one_smul ℝ d)).trans (one_smul ℝ (ev d)).symm
  exact hder ▸ hcomp

/-! ### Differentiation of moving pullbacks of moving forms -/

/-- Horizontal lift of a time-dependent form `ω : ℝ → RoughForm I' N F (k + 1)` to `ℝ × N`,
dropping the `dt` component via `ContinuousLinearMap.snd ℝ ℝ E'`. -/
private def horizontalLift (I' : ModelWithCorners ℝ E' H')
    (ω : ℝ → RoughForm I' N F (k + 1)) : RoughForm (𝓘(ℝ, ℝ).prod I') (ℝ × N) F (k + 1) :=
  fun p ↦ (ω p.1 p.2).compContinuousLinearMap (.snd ℝ ℝ E')

private theorem horizontalLift_apply (ω : ℝ → RoughForm I' N F (k + 1)) (p : ℝ × N)
    (v : Fin (k + 1) → TangentSpace (𝓘(ℝ, ℝ).prod I') p) :
    horizontalLift I' ω p v = ω p.1 p.2 (fun i ↦ (v i).2) := rfl

/-- Joint differentiability of a moving family of forms `ω : ℝ → RoughForm I' N F (k + 1)` implies
differentiability within `univ ×ˢ range I'` of the coordinate map
`(u, y) ↦ (ω u).inChartAt y₀ y`. -/
private theorem differentiableWithinAt_family_inChartAt [IsManifold I' 1 N]
    {ω : ℝ → RoughForm I' N F (k + 1)} {t : ℝ} {y₀ : N}
    (hω : MDifferentiableAt (𝓘(ℝ, ℝ).prod I') (I'.prod 𝓘(ℝ, E' [⋀^Fin (k + 1)]→L[ℝ] F))
      (fun p : ℝ × N ↦ TotalSpace.mk' (E' [⋀^Fin (k + 1)]→L[ℝ] F)
        (E := fun z : N ↦ TangentSpace I' z [⋀^Fin (k + 1)]→L[ℝ] Trivial N F z)
        p.2 (ω p.1 p.2))
      (t, y₀)) :
    DifferentiableWithinAt ℝ
      (fun q : ℝ × E' ↦ (ω q.1).inChartAt y₀ q.2) (univ ×ˢ range I') (t, extChartAt I' y₀ y₀) := by
  set e' := extChartAt I' y₀
  have hω_coord : MDifferentiableAt (𝓘(ℝ, ℝ).prod I') 𝓘(ℝ, E' [⋀^Fin (k + 1)]→L[ℝ] F)
      (fun p : ℝ × N ↦ inCoordinates E' F y₀ p.2 y₀ p.2 (ω p.1 p.2)) (t, y₀) := by
    simpa only [← mdifferentiableWithinAt_univ] using
      ((mdifferentiableWithinAt_continuousAlternatingMap_bundle _).mp
        hω.mdifferentiableWithinAt).2
  let ψ : ℝ × E' → ℝ × N := Prod.map id e'.symm
  have hψ : MDifferentiableWithinAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E')) (𝓘(ℝ, ℝ).prod I') ψ
      (univ ×ˢ range I') (t, e' y₀) :=
    (mdifferentiableWithinAt_id (I := 𝓘(ℝ, ℝ))).prodMap
      (mdifferentiableWithinAt_extChartAt_symm (mem_extChartAt_target y₀))
  have hψ_pt : ψ (t, e' y₀) = (t, y₀) := Prod.ext rfl (extChartAt_to_inv y₀)
  have hcomp : DifferentiableWithinAt ℝ ((fun p : ℝ × N ↦
      inCoordinates E' F y₀ p.2 y₀ p.2 (ω p.1 p.2)) ∘ ψ) (univ ×ˢ range I') (t, e' y₀) := by
    have hcomp_m := hω_coord.comp_mdifferentiableWithinAt_of_eq (t, e' y₀) hψ hψ_pt
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod,
      mdifferentiableWithinAt_iff_differentiableWithinAt] at hcomp_m
    exact hcomp_m
  have hev : (fun q : ℝ × E' ↦ (ω q.1).inChartAt y₀ q.2) =ᶠ[𝓝[univ ×ˢ range I'] (t, e' y₀)]
      (fun p : ℝ × N ↦ inCoordinates E' F y₀ p.2 y₀ p.2 (ω p.1 p.2)) ∘ ψ := by
    have hmem : univ ×ˢ e'.target ∈ 𝓝[univ ×ˢ range I'] (t, e' y₀) := by
      rw [nhdsWithin_prod_eq]
      exact Filter.prod_mem_prod univ_mem (extChartAt_target_mem_nhdsWithin y₀)
    filter_upwards [hmem] with q hq
    have hsrc : e'.symm q.2 ∈ e'.source := e'.map_target hq.2
    simp only [ψ, Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
    rw [(ω q.1).inCoordinates_eq_inChartAt hsrc, e'.right_inv hq.2]
  exact hcomp.congr_of_eventuallyEq hev
    (hev.self_of_nhdsWithin
      ⟨trivial, extChartAt_target_subset_range y₀ (mem_extChartAt_target y₀)⟩)

private theorem range_prod_real (I' : ModelWithCorners ℝ E' H') :
    range (𝓘(ℝ, ℝ).prod I') = univ ×ˢ range I' := by
  rw [ModelWithCorners.range_prod, modelWithCornersSelf_coe, range_id]

/-- Coordinate expression of `horizontalLift I' ω` in the preferred chart at `(t, y₀)`. -/
private theorem horizontalLift_inChartAt_eq [IsManifold I' 1 N]
    (ω : ℝ → RoughForm I' N F (k + 1)) (t : ℝ) (y₀ : N) {q : ℝ × E'}
    (hq : q.2 ∈ (extChartAt I' y₀).target) :
    (horizontalLift I' ω).inChartAt (t, y₀) q =
      compContinuousLinearMapCLM (𝕜 := ℝ) (F := F) (ι := Fin (k + 1)) (.snd ℝ ℝ E')
        ((ω q.1).inChartAt y₀ q.2) := by
  set e' := extChartAt I' y₀
  have hsymm_eq : ⇑(extChartAt (𝓘(ℝ, ℝ).prod I') (t, y₀)).symm = Prod.map id e'.symm := rfl
  ext u
  rw [RoughForm.inChartAt_apply]
  have hd_prod : mfderivWithin 𝓘(ℝ, ℝ × E') (𝓘(ℝ, ℝ).prod I')
      (extChartAt (𝓘(ℝ, ℝ).prod I') (t, y₀)).symm (range (𝓘(ℝ, ℝ).prod I')) q =
      ContinuousLinearMap.prodMap (ContinuousLinearMap.id ℝ ℝ)
        (mfderivWithin 𝓘(ℝ, E') I' e'.symm (range I') q.2) := by
    rw [hsymm_eq, range_prod_real, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod,
      mfderivWithin_prodMap (mdifferentiableWithinAt_id (I := 𝓘(ℝ, ℝ)))
        (mdifferentiableWithinAt_extChartAt_symm hq)
        (uniqueMDiffWithinAt_univ (I := 𝓘(ℝ, ℝ)))
        (I'.uniqueMDiffOn _ (extChartAt_target_subset_range y₀ hq)),
      mfderivWithin_univ, mfderiv_id]
    rfl
  simp only [compContinuousLinearMapCLM_apply, compContinuousLinearMap_apply,
    RoughForm.inChartAt_apply, horizontalLift, hd_prod, hsymm_eq]
  rfl

/-- Coordinate-germ equality of `horizontalLift I' ω` near `(t, e' y₀)`. -/
private theorem horizontalLift_inChartAt_eventuallyEq [IsManifold I' 1 N]
    (ω : ℝ → RoughForm I' N F (k + 1)) (t : ℝ) (y₀ : N) :
    (horizontalLift I' ω).inChartAt (t, y₀) =ᶠ[𝓝[range (𝓘(ℝ, ℝ).prod I')]
      (extChartAt (𝓘(ℝ, ℝ).prod I') (t, y₀) (t, y₀))]
      (compContinuousLinearMapCLM (𝕜 := ℝ) (F := F) (ι := Fin (k + 1)) (.snd ℝ ℝ E')) ∘
        fun q : ℝ × E' ↦ (ω q.1).inChartAt y₀ q.2 := by
  rw [show extChartAt (𝓘(ℝ, ℝ).prod I') (t, y₀) (t, y₀) = (t, extChartAt I' y₀ y₀) from rfl,
    range_prod_real, nhdsWithin_prod_eq]
  filter_upwards [Filter.prod_mem_prod univ_mem (extChartAt_target_mem_nhdsWithin y₀)]
    with q hq using horizontalLift_inChartAt_eq ω t y₀ hq.2

/-- Joint differentiability of a moving family of forms implies differentiability of its
horizontal lift on `ℝ × N`. -/
private theorem mdifferentiableAt_horizontalLift_of_family [IsManifold I' 1 N]
    {ω : ℝ → RoughForm I' N F (k + 1)} {t : ℝ} {y₀ : N}
    (hω : MDifferentiableAt (𝓘(ℝ, ℝ).prod I') (I'.prod 𝓘(ℝ, E' [⋀^Fin (k + 1)]→L[ℝ] F))
      (fun p : ℝ × N ↦ TotalSpace.mk' (E' [⋀^Fin (k + 1)]→L[ℝ] F)
        (E := fun z : N ↦ TangentSpace I' z [⋀^Fin (k + 1)]→L[ℝ] Trivial N F z)
        p.2 (ω p.1 p.2))
      (t, y₀)) :
    MDifferentiableAt (𝓘(ℝ, ℝ).prod I')
      ((𝓘(ℝ, ℝ).prod I').prod 𝓘(ℝ, (ℝ × E') [⋀^Fin (k + 1)]→L[ℝ] F))
      (fun p ↦ TotalSpace.mk' ((ℝ × E') [⋀^Fin (k + 1)]→L[ℝ] F) p (horizontalLift I' ω p))
      (t, y₀) := by
  let C := compContinuousLinearMapCLM (𝕜 := ℝ) (F := F) (ι := Fin (k + 1)) (.snd ℝ ℝ E')
  refine mdifferentiableAt_form_of_differentiableWithinAt_inChartAt_self ?_
  have hc : DifferentiableWithinAt ℝ (C ∘ fun q : ℝ × E' ↦ (ω q.1).inChartAt y₀ q.2)
      (range (𝓘(ℝ, ℝ).prod I')) (extChartAt (𝓘(ℝ, ℝ).prod I') (t, y₀) (t, y₀)) := by
    rw [range_prod_real]
    exact C.differentiableAt.comp_differentiableWithinAt (t, extChartAt I' y₀ y₀)
      (differentiableWithinAt_family_inChartAt hω)
  exact hc.congr_of_eventuallyEq (horizontalLift_inChartAt_eventuallyEq ω t y₀)
    (horizontalLift_inChartAt_eq ω t y₀ (mem_extChartAt_target y₀))

/-- Temporal/spatial split of `mextDeriv (horizontalLift I' ω)` at `(t, y₀)` on a tangent tuple
whose leading vector is `(1, V₀)` and whose remaining vectors `(0, W i)` are horizontal. -/
private theorem mextDeriv_horizontalLift_vecCons [IsManifold I' 1 N]
    {ω : ℝ → RoughForm I' N F (k + 1)} {t : ℝ} {y₀ : N}
    (hω : MDifferentiableAt (𝓘(ℝ, ℝ).prod I') (I'.prod 𝓘(ℝ, E' [⋀^Fin (k + 1)]→L[ℝ] F))
      (fun p : ℝ × N ↦ TotalSpace.mk' (E' [⋀^Fin (k + 1)]→L[ℝ] F)
        (E := fun z : N ↦ TangentSpace I' z [⋀^Fin (k + 1)]→L[ℝ] Trivial N F z)
        p.2 (ω p.1 p.2))
      (t, y₀))
    (V₀ : TangentSpace I' y₀) (W : Fin (k + 1) → TangentSpace I' y₀) :
    mextDeriv (horizontalLift I' ω) (t, y₀)
        (Matrix.vecCons ((1 : ℝ), V₀) fun i ↦ ((0 : ℝ), W i)) =
      deriv (fun v ↦ ω v y₀) t W + mextDeriv (ω t) y₀ (Matrix.vecCons V₀ W) := by
  set e' := extChartAt I' y₀
  let Φ : ℝ × E' → E' [⋀^Fin (k + 1)]→L[ℝ] F := fun q ↦ (ω q.1).inChartAt y₀ q.2
  let C := compContinuousLinearMapCLM (𝕜 := ℝ) (F := F) (ι := Fin (k + 1)) (.snd ℝ ℝ E')
  have hpt_chart : extChartAt (𝓘(ℝ, ℝ).prod I') (t, y₀) (t, y₀) = (t, e' y₀) := rfl
  have hΦ_diff := differentiableWithinAt_family_inChartAt hω
  set B := fderivWithin ℝ Φ (univ ×ˢ range I') (t, e' y₀)
  have hu_prod : UniqueDiffWithinAt ℝ (univ ×ˢ range I') (t, e' y₀) :=
    uniqueDiffWithinAt_univ.prod
      (I'.uniqueDiffOn (e' y₀) (extChartAt_target_subset_range y₀ (mem_extChartAt_target y₀)))
  have hdα_pt : mextDeriv (horizontalLift I' ω) (t, y₀) = alternatizeUncurryFin (C ∘L B) := by
    rw [mextDeriv_def, (horizontalLift_inChartAt_eventuallyEq ω t y₀).extDerivWithin_eq
      (horizontalLift_inChartAt_eq ω t y₀ (mem_extChartAt_target y₀)),
      hpt_chart, range_prod_real, extDerivWithin,
      (C.hasFDerivAt.comp_hasFDerivWithinAt (t, e' y₀) hΦ_diff.hasFDerivWithinAt).fderivWithin
        hu_prod]
  have hB10 : B ((1 : ℝ), (0 : E')) W = deriv (fun v ↦ ω v y₀) t W := by
    have hmaps_in : MapsTo (fun v : ℝ ↦ (v, e' y₀)) univ (univ ×ˢ range I') :=
      fun _ _ ↦ ⟨trivial, extChartAt_target_subset_range y₀ (mem_extChartAt_target y₀)⟩
    have hcurve_Φ : HasFDerivWithinAt (Φ ∘ fun v ↦ (v, e' y₀)) (B ∘L .inl ℝ ℝ E') univ t :=
      hΦ_diff.hasFDerivWithinAt.comp t
        (hasFDerivAt_prodMk_left (𝕜 := ℝ) t (e' y₀)).hasFDerivWithinAt hmaps_in
    have hd_Φ : HasDerivAt (F := E' [⋀^Fin (k + 1)]→L[ℝ] F) (fun v ↦ Φ (v, e' y₀))
        (B ((1 : ℝ), (0 : E'))) t := by
      simpa [Function.comp_def] using (hasFDerivWithinAt_univ.mp hcurve_Φ).hasDerivAt
    have hd_ω : HasDerivAt (F := E' [⋀^Fin (k + 1)]→L[ℝ] F) (fun v ↦ ω v y₀)
        (B ((1 : ℝ), (0 : E'))) t :=
      hd_Φ.congr_of_eventuallyEq
        (Eventually.of_forall fun v ↦ (RoughForm.inChartAt_extChartAt_self (ω v) y₀).symm)
    exact congrArg (fun η : E' [⋀^Fin (k + 1)]→L[ℝ] F ↦ η W) hd_ω.deriv.symm
  have hBinr : alternatizeUncurryFin (B ∘L .inr ℝ ℝ E') = mextDeriv (ω t) y₀ := by
    have hslice_Φ : HasFDerivWithinAt (Φ ∘ fun w ↦ (t, w)) (B ∘L .inr ℝ ℝ E') (range I')
        (e' y₀) :=
      hΦ_diff.hasFDerivWithinAt.comp (e' y₀)
        (hasFDerivAt_prodMk_right (𝕜 := ℝ) t (e' y₀)).hasFDerivWithinAt
        fun _ hw ↦ ⟨trivial, hw⟩
    have hslice_Φ' : HasFDerivWithinAt (fun w ↦ Φ (t, w)) (B ∘L .inr ℝ ℝ E') (range I')
        (e' y₀) := by
      simpa [Function.comp_def] using hslice_Φ
    rw [mextDeriv_def, extDerivWithin,
      hslice_Φ'.fderivWithin
        (I'.uniqueDiffOn (e' y₀) (extChartAt_target_subset_range y₀ (mem_extChartAt_target y₀)))]
  let v₀ : E' := V₀
  let w : Fin (k + 1) → E' := fun i ↦ W i
  have hdecomp : ((1 : ℝ), v₀) = ((1 : ℝ), (0 : E')) + ((0 : ℝ), v₀) := by simp
  have hpt_apply : mextDeriv (horizontalLift I' ω) (t, y₀)
      (Matrix.vecCons ((1 : ℝ), V₀) fun i ↦ ((0 : ℝ), W i)) =
      alternatizeUncurryFin (C ∘L B) (Matrix.vecCons ((1 : ℝ), v₀) fun i ↦ ((0 : ℝ), w i)) :=
    congrArg (fun η : TangentSpace (𝓘(ℝ, ℝ).prod I') (t, y₀) [⋀^Fin (k + 2)]→L[ℝ] F ↦
      η (Matrix.vecCons ((1 : ℝ), V₀) fun i ↦ ((0 : ℝ), W i))) hdα_pt
  refine hpt_apply.trans ?_
  rw [hdecomp]
  refine ((alternatizeUncurryFin (C ∘L B)).toAlternatingMap.map_vecCons_add
    (fun i ↦ ((0 : ℝ), w i)) ((1 : ℝ), (0 : E')) ((0 : ℝ), v₀)).trans ?_
  congr 1
  · dsimp only [ContinuousAlternatingMap.coe_toAlternatingMap]
    rw [alternatizeUncurryFin_apply, Fin.sum_univ_succ]
    simp only [ContinuousLinearMap.comp_apply]
    have hzero_tail (j : Fin (k + 1)) :
        ((-1 : ℤ) ^ j.succ.val) •
          (C (B (Matrix.vecCons ((1 : ℝ), (0 : E')) (fun i ↦ ((0 : ℝ), w i)) j.succ)))
            (Fin.removeNth j.succ
              (Matrix.vecCons ((1 : ℝ), (0 : E')) fun i ↦ ((0 : ℝ), w i))) = 0 := by
      have h0 : (ContinuousLinearMap.snd ℝ ℝ E') (Fin.removeNth j.succ
          (Matrix.vecCons ((1 : ℝ), (0 : E')) fun i ↦ ((0 : ℝ), w i)) 0) = 0 := rfl
      rw [show (C (B _)) _ = 0 from (B _).map_coord_zero 0 h0, smul_zero]
    rw [Finset.sum_eq_zero fun j _ ↦ hzero_tail j, add_zero]
    simp only [Fin.val_zero, pow_zero, one_smul, Matrix.cons_val_zero,
      Fin.removeNth_zero, C, compContinuousLinearMapCLM_apply,
      compContinuousLinearMap_apply, ContinuousLinearMap.coe_snd']
    exact hB10
  · dsimp only [ContinuousAlternatingMap.coe_toAlternatingMap]
    have hinr_vec : (Matrix.vecCons ((0 : ℝ), v₀) fun i ↦ ((0 : ℝ), w i)) =
        fun i ↦ ((0 : ℝ), Matrix.vecCons v₀ w i) := by
      funext i; cases i using Fin.cases <;> rfl
    have hCB_inr : alternatizeUncurryFin (C ∘L B)
        (Matrix.vecCons ((0 : ℝ), v₀) fun i ↦ ((0 : ℝ), w i)) =
        alternatizeUncurryFin (B ∘L .inr ℝ ℝ E') (Matrix.vecCons V₀ W) := by
      rw [hinr_vec, alternatizeUncurryFin_apply, alternatizeUncurryFin_apply]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [ContinuousLinearMap.comp_apply, C, compContinuousLinearMapCLM_apply,
        compContinuousLinearMap_apply, ContinuousLinearMap.inr_apply]
      rfl
    exact hCB_inr.trans (congrArg (fun η : E' [⋀^Fin (k + 2)]→L[ℝ] F ↦ η (Matrix.vecCons V₀ W))
      hBinr)

/-- **Differentiation of moving pullbacks for a moving family of forms.** Let `P : M × ℝ → N` be
`C^r` (`2 ≤ r`) at `(x₀, t)` between `C²` manifolds (possibly with boundary or corners), and let
`ω : ℝ → RoughForm I' N F (k + 1)` be jointly differentiable as a section along `Prod.snd` at
`(t, P (x₀, t))`. Then `u ↦ (p_u^* ω_u)_{x₀}` has derivative
`(p_t^* (∂_t ω_t))_{x₀} + d(C_(p_t, V_t) ω_t)_{x₀} + C_(p_t, V_t)(d(ω_t))_{x₀}` at `t`. -/
theorem hasDerivAt_mpullback_family_form [IsManifold I 2 M] [IsManifold I' 2 N]
    {r : WithTop ℕ∞} {P : M × ℝ → N} {ω : ℝ → RoughForm I' N F (k + 1)} {x₀ : M} {t : ℝ}
    (hP : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I' r P (x₀, t)) (hr : 2 ≤ r)
    (hω : MDifferentiableAt (𝓘(ℝ, ℝ).prod I') (I'.prod 𝓘(ℝ, E' [⋀^Fin (k + 1)]→L[ℝ] F))
      (fun p : ℝ × N ↦ TotalSpace.mk' (E' [⋀^Fin (k + 1)]→L[ℝ] F)
        (E := fun z : N ↦ TangentSpace I' z [⋀^Fin (k + 1)]→L[ℝ] Trivial N F z)
        p.2 (ω p.1 p.2))
      (t, P (x₀, t))) :
    HasDerivAt (F := E [⋀^Fin (k + 1)]→L[ℝ] F)
      (fun u ↦ mpullback I I' (fun y ↦ P (y, u)) (ω u) x₀)
      (mpullback I I' (fun y ↦ P (y, t)) (fun z ↦ deriv (fun v ↦ ω v z) t) x₀ +
        mextDeriv (mfamilyContraction I I' P t (ω t)) x₀ +
        mfamilyContraction I I' P t (mextDeriv (ω t)) x₀) t := by
  have : IsManifold I 1 M := IsManifold.of_le one_le_two
  have : IsManifold I' 1 N := IsManifold.of_le one_le_two
  let P_lift : M × ℝ → ℝ × N := fun q ↦ (q.2, P q)
  have hP_lift : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I') r P_lift (x₀, t) :=
    contMDiffAt_snd.prodMk hP
  have hlift_deriv :=
    hasDerivAt_mpullback_family hP_lift hr (mdifferentiableAt_horizontalLift_of_family hω)
  -- 1. Slices `(p_lift_u)^* (horizontalLift I' ω)` agree with `p_u^* (ω u)` for all `u`.
  have hcurve_eq (u : ℝ) :
      mpullback I (𝓘(ℝ, ℝ).prod I') (fun y ↦ P_lift (y, u)) (horizontalLift I' ω) x₀ =
        mpullback I I' (fun y ↦ P (y, u)) (ω u) x₀ := by
    by_cases hPu : MDifferentiableAt I I' (fun y ↦ P (y, u)) x₀
    · ext v
      rw [mpullback_apply, mpullback_apply, horizontalLift_apply]
      refine congrArg (ω u (P (x₀, u))) (funext fun i ↦ ?_)
      dsimp only [P_lift]
      rw [mfderiv_prodMk mdifferentiableAt_const hPu]; rfl
    · have hPu' : ¬MDifferentiableAt I (𝓘(ℝ, ℝ).prod I') (fun y ↦ P_lift (y, u)) x₀ :=
        fun h ↦ hPu (mdifferentiableAt_snd.comp x₀ h)
      ext v
      rw [mpullback_apply, mpullback_apply, mfderiv_zero_of_not_mdifferentiableAt hPu,
        mfderiv_zero_of_not_mdifferentiableAt hPu']
      simp only [zero_apply]
      rw [(horizontalLift I' ω (P_lift (x₀, u))).map_coord_zero 0 rfl,
        (ω u (P (x₀, u))).map_coord_zero 0 rfl]
  -- 2. Near `x₀`, `mfamilyContraction` of `horizontalLift` along `P_lift` agrees with `ω t`.
  have hcontr_eq : ∀ᶠ y in 𝓝 x₀,
      mfamilyContraction I (𝓘(ℝ, ℝ).prod I') P_lift t (horizontalLift I' ω) y =
        mfamilyContraction I I' P t (ω t) y := by
    have hP2 : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I' 2 P (x₀, t) := hP.of_le hr
    have hnhds : ∀ᶠ y in 𝓝 x₀, ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I' 2 P (y, t) :=
      ((continuous_id.prodMk continuous_const).tendsto x₀).eventually
        ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hP2)
    filter_upwards [hnhds] with y hy
    have hyd : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) I' P (y, t) := hy.mdifferentiableAt two_ne_zero
    have hy_slice : MDifferentiableAt I I' (fun z ↦ P (z, t)) y :=
      hyd.comp y (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
    ext v
    rw [mfamilyContraction_apply, mfamilyContraction_apply, horizontalLift_apply]
    refine congrArg (ω t (P (y, t))) (funext fun i ↦ ?_)
    cases i using Fin.cases with
    | zero =>
      simp only [Matrix.cons_val_zero, P_lift]
      rw [mfderiv_prodMk mdifferentiableAt_snd hyd]; rfl
    | succ j =>
      simp only [Matrix.cons_val_succ, P_lift]
      rw [mfderiv_prodMk mdifferentiableAt_const hy_slice]; rfl
  -- 3. Split `mfamilyContraction` of `mextDeriv (horizontalLift I' ω)` into temporal and spatial
  --    pieces via `mextDeriv_horizontalLift_vecCons`.
  have hsplit : mfamilyContraction I (𝓘(ℝ, ℝ).prod I') P_lift t
        (mextDeriv (horizontalLift I' ω)) x₀ =
      mpullback I I' (fun y ↦ P (y, t)) (fun z ↦ deriv (fun v ↦ ω v z) t) x₀ +
        mfamilyContraction I I' P t (mextDeriv (ω t)) x₀ := by
    have hPd : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) I' P (x₀, t) :=
      (hP.of_le hr).mdifferentiableAt two_ne_zero
    have hPtd : MDifferentiableAt I I' (fun y ↦ P (y, t)) x₀ :=
      hPd.comp x₀ (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
    ext u
    rw [mfamilyContraction_apply]
    have hvel_lift : mfderiv (I.prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I') P_lift (x₀, t) ((0 : E), (1 : ℝ)) =
        ((1 : ℝ), mfamilyVelocity I I' P t x₀) := by
      rw [mfderiv_prodMk mdifferentiableAt_snd hPd, mfderiv_snd]
      exact Prod.ext rfl (mfamilyVelocity_def P t x₀).symm
    have hslice_lift (i : Fin (k + 1)) :
        mfderiv I (𝓘(ℝ, ℝ).prod I') (fun y ↦ P_lift (y, t)) x₀ (u i) =
          ((0 : ℝ), mfderiv I I' (fun y ↦ P (y, t)) x₀ (u i)) := by
      rw [mfderiv_prodMk mdifferentiableAt_const hPtd, mfderiv_const]; rfl
    rw [hvel_lift]
    simp_rw [hslice_lift]
    exact (mextDeriv_horizontalLift_vecCons hω _ _).trans
      (by rw [ContinuousAlternatingMap.add_apply, mpullback_apply, mfamilyContraction_apply,
        mfamilyVelocity_def])
  simp_rw [← hcurve_eq]
  refine hlift_deriv.congr_deriv ?_
  rw [mextDeriv_congr_of_eventuallyEq hcontr_eq, hsplit]; abel

/-- **Differentiation of moving pullbacks for a moving family of forms over `J : Opens ℝ`.** Let
`P : M × ↥J → N` be `C^r` (`2 ≤ r`) at `(x₀, t)` between `C²` manifolds (possibly with boundary or
corners), and let `ω : ↥J → RoughForm I' N F (k + 1)` be jointly differentiable as a section along
`Prod.snd` at `(t, P (x₀, t))`. Then `u ↦ (p_u^* ω_u)_{x₀}` has manifold derivative
`(1 : ℝ →L[ℝ] ℝ).smulRight ((p_t^* (∂_t ω_t))_{x₀} + d(C_(p_t, V_t) ω_t)_{x₀} +
C_(p_t, V_t)(d(ω_t))_{x₀})` at `t` in the fixed alternating-form fiber
`E [⋀^Fin (k + 1)]→L[ℝ] F`, where `∂_t ω_t` is evaluated by `mfderiv` at `(1 : ℝ)`. -/
theorem hasMFDerivAt_mpullback_family_form_opens [IsManifold I 2 M] [IsManifold I' 2 N]
    {r : WithTop ℕ∞} {J : Opens ℝ} {P : M × ↥J → N} {ω : ↥J → RoughForm I' N F (k + 1)}
    {x₀ : M} {t : J}
    (hP : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I' r P (x₀, t)) (hr : 2 ≤ r)
    (hω : MDifferentiableAt (𝓘(ℝ, ℝ).prod I') (I'.prod 𝓘(ℝ, E' [⋀^Fin (k + 1)]→L[ℝ] F))
      (fun p : ↥J × N ↦ TotalSpace.mk' (E' [⋀^Fin (k + 1)]→L[ℝ] F)
        (E := fun z : N ↦ TangentSpace I' z [⋀^Fin (k + 1)]→L[ℝ] Trivial N F z)
        p.2 (ω p.1 p.2))
      (t, P (x₀, t))) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E [⋀^Fin (k + 1)]→L[ℝ] F) (M' := E [⋀^Fin (k + 1)]→L[ℝ] F)
      (fun u : J ↦ (mpullback I I' (fun y ↦ P (y, u)) (ω u) x₀ : E [⋀^Fin (k + 1)]→L[ℝ] F)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (M₂ := E [⋀^Fin (k + 1)]→L[ℝ] F)
        (mpullback I I' (fun y ↦ P (y, t))
            (fun z ↦ mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E' [⋀^Fin (k + 1)]→L[ℝ] F)
              (M' := E' [⋀^Fin (k + 1)]→L[ℝ] F)
              (fun v : J ↦ (ω v z : E' [⋀^Fin (k + 1)]→L[ℝ] F)) t (1 : ℝ)) x₀ +
          mextDeriv (mfamilyContraction I I' P t (ω t)) x₀ +
          mfamilyContraction I I' P t (mextDeriv (ω t)) x₀)) := by
  let P' : M × ℝ → N := P ∘ Prod.map id (retractOpensAt t)
  have hP'_apply (y : M) (u : J) : P' (y, (u : ℝ)) = P (y, u) :=
    congrArg P (Prod.ext rfl (retractOpensAt_coe t u))
  have hP'_eq : P' ∘ Prod.map id (Subtype.val : J → ℝ) = P :=
    funext fun q ↦ hP'_apply q.1 q.2
  have hP'_smooth : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I' r P' (x₀, (t : ℝ)) :=
    hP.comp_of_eq (contMDiffAt_id.prodMap (contMDiffAt_retractOpensAt t))
      (Prod.ext rfl (retractOpensAt_coe t t))
  let ω' : ℝ → RoughForm I' N F (k + 1) := ω ∘ retractOpensAt t
  have hω'_apply (u : J) : ω' (u : ℝ) = ω u := congrArg ω (retractOpensAt_coe t u)
  have hω' : MDifferentiableAt (𝓘(ℝ, ℝ).prod I') (I'.prod 𝓘(ℝ, E' [⋀^Fin (k + 1)]→L[ℝ] F))
      (fun p : ℝ × N ↦ TotalSpace.mk' (E' [⋀^Fin (k + 1)]→L[ℝ] F)
        (E := fun z : N ↦ TangentSpace I' z [⋀^Fin (k + 1)]→L[ℝ] Trivial N F z)
        p.2 (ω' p.1 p.2))
      ((t : ℝ), P' (x₀, (t : ℝ))) :=
    MDifferentiableAt.comp_of_eq ((t : ℝ), P' (x₀, (t : ℝ))) hω
      (((contMDiffAt_retractOpensAt (r := 1) t).mdifferentiableAt one_ne_zero).prodMap
        mdifferentiableAt_id)
      (Prod.ext (retractOpensAt_coe t t) (hP'_apply x₀ t))
  have hcomp := (hasDerivAt_mpullback_family_form hP'_smooth hr hω').hasFDerivAt.hasMFDerivAt.comp t
    (hasMFDerivAt_subtype_val_opens J t)
  have hdt : (fun z : N ↦ (deriv (fun v : ℝ ↦ (ω' v z : E' [⋀^Fin (k + 1)]→L[ℝ] F)) (t : ℝ) :
        TangentSpace I' z [⋀^Fin (k + 1)]→L[ℝ] Trivial N F z)) =
      fun z : N ↦ (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E' [⋀^Fin (k + 1)]→L[ℝ] F)
        (M' := E' [⋀^Fin (k + 1)]→L[ℝ] F)
        (fun v : J ↦ (ω v z : E' [⋀^Fin (k + 1)]→L[ℝ] F)) t (1 : ℝ) :
          TangentSpace I' z [⋀^Fin (k + 1)]→L[ℝ] Trivial N F z) := by
    funext z
    let fz : ℝ → E' [⋀^Fin (k + 1)]→L[ℝ] F := fun v ↦ ω' v z
    let gz : J → E' [⋀^Fin (k + 1)]→L[ℝ] F := fun v ↦ ω v z
    let oneT : TangentSpace 𝓘(ℝ, ℝ) t := (1 : ℝ)
    have hcomp_z : gz = fz ∘ (Subtype.val : J → ℝ) :=
      funext fun v ↦ congrFun (hω'_apply v).symm z
    have h1 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E' [⋀^Fin (k + 1)]→L[ℝ] F)
        (M' := E' [⋀^Fin (k + 1)]→L[ℝ] F) gz t oneT = deriv fz (t : ℝ) := by
      refine (congrArg (fun h ↦ mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E' [⋀^Fin (k + 1)]→L[ℝ] F)
          (M' := E' [⋀^Fin (k + 1)]→L[ℝ] F) h t oneT) hcomp_z).trans ?_
      refine (Manifold.mfderiv_comp_subtype_val_apply (I := 𝓘(ℝ, E' [⋀^Fin (k + 1)]→L[ℝ] F))
          (M := E' [⋀^Fin (k + 1)]→L[ℝ] F) (f := fz) (x := t) oneT).trans ?_
      rw [mfderiv_eq_fderiv]; rfl
    exact h1.symm
  have hpt_slice : (fun y : M ↦ P' (y, (t : ℝ))) = fun y : M ↦ P (y, t) :=
    funext fun y ↦ hP'_apply y t
  have hval :
      (mpullback I I' (fun y ↦ P' (y, (t : ℝ))) (fun z ↦ deriv (fun v ↦ ω' v z) (t : ℝ)) x₀ +
        mextDeriv (mfamilyContraction I I' P' (t : ℝ) (ω' (t : ℝ))) x₀ +
        mfamilyContraction I I' P' (t : ℝ) (mextDeriv (ω' (t : ℝ))) x₀ :
          E [⋀^Fin (k + 1)]→L[ℝ] F) =
      mpullback I I' (fun y ↦ P (y, t))
          (fun z ↦ mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E' [⋀^Fin (k + 1)]→L[ℝ] F)
            (M' := E' [⋀^Fin (k + 1)]→L[ℝ] F)
            (fun v : J ↦ (ω v z : E' [⋀^Fin (k + 1)]→L[ℝ] F)) t (1 : ℝ)) x₀ +
        mextDeriv (mfamilyContraction I I' P t (ω t)) x₀ +
        mfamilyContraction I I' P t (mextDeriv (ω t)) x₀ := by
    simp only [hω'_apply t, hdt, hpt_slice,
      ← mfamilyContraction_comp_prodMap_subtype_val J P' t (ω t),
      ← mfamilyContraction_comp_prodMap_subtype_val J P' t (mextDeriv (ω t)), hP'_eq]
  have hder := (ContinuousLinearMap.toSpanSingleton_comp (ContinuousLinearMap.id ℝ ℝ) _).trans
    (congrArg ((1 : ℝ →L[ℝ] ℝ).smulRight (M₂ := E [⋀^Fin (k + 1)]→L[ℝ] F)) hval)
  have hfun : (fun u : ℝ ↦ (mpullback I I' (fun y ↦ P' (y, u)) (ω' u) x₀ :
          E [⋀^Fin (k + 1)]→L[ℝ] F)) ∘ (Subtype.val : J → ℝ) =
      fun u : J ↦ (mpullback I I' (fun y ↦ P (y, u)) (ω u) x₀ : E [⋀^Fin (k + 1)]→L[ℝ] F) := by
    funext u
    dsimp only [Function.comp_apply]
    rw [hω'_apply u]
    exact congrArg (fun p ↦ (mpullback I I' p (ω u) x₀ : E [⋀^Fin (k + 1)]→L[ℝ] F))
      (funext fun y ↦ hP'_apply y u)
  exact hfun ▸ hder ▸ hcomp

/-! ### Specialization to time-dependent flows and Moser's identity -/

section TimeDependentFlow

variable [FiniteDimensional ℝ E] [T2Space M]

/-- Swapping `(y, u) ↦ timeDependentFlowOf X s u y` is `C^n` at `(x, t)` for any `1 ≤ n` on a
finite-dimensional Hausdorff boundaryless `C^n` manifold `M`. -/
private theorem contMDiffAt_timeDependentFlowOf_swap
    {n : ℕ∞} (hn : 1 ≤ n) [BoundarylessManifold I M] [IsManifold I 1 M] [IsManifold I n M]
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent n
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    {s t : ℝ} {x : M} (h : ((s, t), x) ∈ timeDependentFlowDomain X) :
    ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I n
      (fun q : M × ℝ ↦ timeDependentFlowOf X s q.2 q.1) (x, t) := by
  have hX₁ : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)) :=
    hX.of_le (WithTop.coe_le_coe.mpr hn)
  have hflow : ContMDiffAt ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I n
      (fun p : (ℝ × ℝ) × M ↦ timeDependentFlowOf X p.1.1 p.1.2 p.2) ((s, t), x) :=
    (contMDiffOn_timeDependentFlowOf hn hX).contMDiffAt
      ((isOpen_timeDependentFlowDomain hX₁).mem_nhds h)
  exact hflow.comp (x, t)
    (((contMDiff_const (c := s)).prodMk contMDiff_snd).prodMk contMDiff_fst).contMDiffAt

/-- **Contraction along a time-dependent flow.** On a finite-dimensional Hausdorff boundaryless
`C¹` manifold `M`, wherever the flow `φ_{s, t}` of a jointly `C¹` time-dependent vector field `X`
is defined at `x`, `mfamilyContraction` along `(y, u) ↦ φ_{s, u} y` at time `t` equals
`φ_{s, t}^* (ω.interior (X t))` at `x`. -/
theorem mfamilyContraction_timeDependentFlowOf_of_mem [BoundarylessManifold I M] [IsManifold I 1 M]
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    {s t : ℝ} {x : M} (h : ((s, t), x) ∈ timeDependentFlowDomain X)
    (ω : RoughForm I M F (k + 1)) :
    mfamilyContraction I I (fun q : M × ℝ ↦ timeDependentFlowOf X s q.2 q.1) t ω x =
      mpullback I I (timeDependentFlowOf X s t) (ω.interior (X t)) x := by
  let P : M × ℝ → M := fun q ↦ timeDependentFlowOf X s q.2 q.1
  have hP : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) I P (x, t) :=
    (contMDiffAt_timeDependentFlowOf_swap (n := 1) le_rfl hX h).mdifferentiableAt one_ne_zero
  have hvel : mfamilyVelocity I I P t x = X t (timeDependentFlowOf X s t x) :=
    (mfamilyVelocity_eq_mfderiv_slice_right_apply hP).trans
      ((congrArg (fun L : ℝ →L[ℝ] E ↦ L (1 : ℝ))
        (hasMFDerivAt_timeDependentFlowOf hX h).mfderiv).trans (one_smul ℝ _))
  rw [mfamilyContraction_def]
  exact (mcontractionAlongMap_congr_field_at (I := I) (I' := I) ω hvel).trans
    (congrFun (mcontractionAlongMap_comp_field (I := I) (I' := I) (timeDependentFlowOf X s t) (X t)
      ω) x)

/-- **Moser Lie-derivative identification with moving-pullback contraction.** On a
finite-dimensional Hausdorff boundaryless (`[I.Boundaryless]`) `C²` manifold `M`, for a jointly
`C²` time-dependent vector field `X` with flow `φ_{s, t}` defined at `x` and a `(k + 1)`-form `α`
on `ℝ × M` that is `C¹` at `(t, φ_{s, t} x)`, the Lie-derivative sum
`φ_{s, t}^* (ι_t^* L_{∂_t} α + L_{X_t} α_t)` of
`TauCeti.hasDerivAt_mpullback_timeDependentFlowOf_mpullback_prodMk` equals
`(φ_{s, t}^* (ι_t^* L_{∂_t} α))_x + d(C_(φ_{s, t}, V_t) α_t)_x + C_(φ_{s, t}, V_t)(dα_t)_x`. -/
theorem mpullback_timeDependentFlowOf_add_mlieDerivForm_eq_add_mfamilyContraction_of_mem
    [I.Boundaryless] [IsManifold I 2 M]
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    {α : RoughForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) F (k + 1)}
    {s t : ℝ} {x : M} (h : ((s, t), x) ∈ timeDependentFlowDomain X)
    (hα : ContMDiffAt (𝓘(ℝ, ℝ).prod I)
      ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, (ℝ × E) [⋀^Fin (k + 1)]→L[ℝ] F)) 1
      (fun p ↦ TotalSpace.mk' ((ℝ × E) [⋀^Fin (k + 1)]→L[ℝ] F) p (α p))
      (t, timeDependentFlowOf X s t x)) :
    mpullback I I (timeDependentFlowOf X s t)
        (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
            (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α) +
          mlieDerivForm (X t) (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α)) x =
      mpullback I I (timeDependentFlowOf X s t)
          (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
            (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α)) x +
        mextDeriv
          (mfamilyContraction I I (fun q : M × ℝ ↦ timeDependentFlowOf X s q.2 q.1) t
            (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α)) x +
        mfamilyContraction I I (fun q : M × ℝ ↦ timeDependentFlowOf X s q.2 q.1) t
          (mextDeriv (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α)) x := by
  have : IsManifold I 1 M := IsManifold.of_le one_le_two
  let P : M × ℝ → M := fun q ↦ timeDependentFlowOf X s q.2 q.1
  have hP : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I 2 P (x, t) :=
    contMDiffAt_timeDependentFlowOf_swap (n := 2) (by norm_num) hX h
  let slice : ℝ → RoughForm I M F (k + 1) := fun u ↦ mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u) α
  have hslice_smooth : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E [⋀^Fin (k + 1)]→L[ℝ] F)) 1
      (fun p : ℝ × M ↦ TotalSpace.mk' (E [⋀^Fin (k + 1)]→L[ℝ] F)
        (E := fun z : M ↦ TangentSpace I z [⋀^Fin (k + 1)]→L[ℝ] Trivial M F z)
        p.2 (slice p.1 p.2)) (t, P (x, t)) := by
    let f_mk : ℝ × M → M → ℝ × M := fun p z ↦ (p.1, z)
    have hf_mk : ContMDiff ((𝓘(ℝ, ℝ).prod I).prod I) (𝓘(ℝ, ℝ).prod I) 2 (Function.uncurry f_mk) :=
      (contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd
    exact hα.mpullback_form_family (f := f_mk) (g := Prod.snd) hf_mk.contMDiffAt
      contMDiffAt_snd le_rfl
  have hd1 := hasDerivAt_mpullback_timeDependentFlowOf_mpullback_prodMk hX h hα
  have hd2 := hasDerivAt_mpullback_family_form hP le_rfl
    (hslice_smooth.mdifferentiableAt one_ne_zero)
  have hslice_deriv : deriv (fun v ↦ slice v (timeDependentFlowOf X s t x)) t =
      mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
        (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α) (timeDependentFlowOf X s t x) :=
    (hasDerivAt_mpullback_prodMk t (timeDependentFlowOf X s t x)
      (hα.mdifferentiableAt one_ne_zero)).deriv
  have hterm1 : mpullback I I (fun y ↦ P (y, t)) (fun z ↦ deriv (fun v ↦ slice v z) t) x =
      mpullback I I (timeDependentFlowOf X s t)
        (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
          (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α)) x := by
    ext w
    rw [mpullback_apply, mpullback_apply]
    dsimp only [P]
    rw [hslice_deriv]
  exact (hd1.unique hd2).trans (by rw [hterm1])

end TimeDependentFlow

end TauCeti
