/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Stabilizer
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Flow
public import TauCeti.Geometry.Manifold.DifferentialForm.Interior
public import TauCeti.Geometry.Symplectic.Flux.Trans

/-!
# The flux as the integral of the velocity contractions

Let `σ` be a two-form on a manifold `M` and let `φ_t`, `t ∈ [0, 1]`, be a smooth diffeotopy of `M`
with velocity field `X_t = (∂ₜ φ_t) ∘ φ_t⁻¹` (`TauCeti.Diffeotopy.velocity`). The **Eulerian flux
form** is the time integral of the contractions `α_t = ι_{X_t} σ`,

`x ↦ ∫₀¹ σ_x(X_t x, ·) dt`

(`TauCeti.Diffeotopy.eulerianFluxForm`). The flux form of `TauCeti.Diffeotopy.fluxForm` is instead
the integral `∫₀¹ φ_t^* α_t dt` of the pulled back contractions. For a closed two-form `σ` and a
symplectic isotopy, one whose every time slice `φ_t` preserves `σ`, the two integrals have the same
de Rham class: both represent the flux (`TauCeti.Diffeotopy.flux_eq_mk_eulerianFluxForm`).

The comparison is through the inverse diffeotopy `φ_t⁻¹`. The time derivative of `φ_t⁻¹ x` is
`-(dφ_t)⁻¹ (X_t x)` (`TauCeti.Diffeotopy.mfderiv_timeSlice_mfderiv_cylinderMap_symm`), and the
spatial derivative of `φ_t⁻¹` at `x` is `(dφ_t)⁻¹`. Since `φ_t` preserves `σ`, the integrand
`σ(∂ₜ (φ_t⁻¹ x), d(φ_t⁻¹) v)` of the flux form of `φ_t⁻¹` at time `t` is therefore
`-σ_x(X_t x, v)` (`TauCeti.Diffeotopy.apply_vecCons_mfderiv_cylinderMap_symm`, which holds for
forms of every degree). So the Eulerian flux form of `φ` is minus the flux form of `φ⁻¹`
(`TauCeti.Diffeotopy.eulerianFluxForm_eq_neg_fluxForm_symm`). In particular it is a smooth form,
closed when `σ` is closed, and since reversing a diffeotopy negates its flux
(`TauCeti.Diffeotopy.flux_symm`) its class is the flux of `φ`.

## Main definitions

* `TauCeti.Diffeotopy.eulerianFluxForm`: the one-form `∫₀¹ ι_{X_t} σ dt`.

## Main results

* `TauCeti.Diffeotopy.eulerianFluxForm_eq_neg_fluxForm_symm`: for a symplectic isotopy, the
  Eulerian flux form is minus the flux form of the inverse diffeotopy.
* `TauCeti.Diffeotopy.isSmoothForm_eulerianFluxForm`,
  `TauCeti.Diffeotopy.mextDeriv_eulerianFluxForm_eq_zero`: it is smooth, and closed for closed `σ`.
* `TauCeti.Diffeotopy.flux_eq_mk_eulerianFluxForm`: the flux of a symplectic isotopy is the
  de Rham class of its Eulerian flux form.
* `TauCeti.Diffeotopy.eulerianFluxForm_globalFlowDiffeotopy`: running a complete vector field `v`
  for duration `a` has Eulerian flux form `a ι_v σ`.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2 (the flux homomorphism, defined by `∫₀¹ ι_{X_t} ω dt`).
* Augustin Banyaga, *The Structure of Classical Diffeomorphism Groups*, Kluwer, 1997,
  Chapter 3.
-/

public section

noncomputable section

open Set
open scoped ContDiff Manifold

namespace TauCeti

namespace Diffeotopy

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold J ∞ M] (Φ : Diffeotopy J ∞ M)

/-- The **Eulerian flux form** `x ↦ ∫₀¹ σ_x(X_t x, ·) dt` of a diffeotopy with respect to a
two-form `σ`: the time integral of the contractions `ι_{X_t} σ` of `σ` with the velocity field
`X_t = (∂ₜ φ_t) ∘ φ_t⁻¹`. For an isotopy whose time slices preserve `σ` it is smooth; when `σ` is
moreover closed it is closed and represents the flux
(`TauCeti.Diffeotopy.flux_eq_mk_eulerianFluxForm`). -/
def eulerianFluxForm (σ : SmoothForm J M ℝ 2) : RoughForm J M ℝ 1 :=
  fun x ↦ intervalIntegral (E := E [⋀^Fin 1]→L[ℝ] ℝ)
    (fun t ↦ RoughForm.interior (Φ.velocity (projIcc 0 1 zero_le_one t)) σ.val x)
    0 1 MeasureTheory.volume

/-- The Eulerian flux form at `x` is the time integral of the contractions `ι_{X_t} σ` at `x`. -/
theorem eulerianFluxForm_apply (σ : SmoothForm J M ℝ 2) (x : M) :
    Φ.eulerianFluxForm σ x = intervalIntegral (E := E [⋀^Fin 1]→L[ℝ] ℝ)
      (fun t ↦ RoughForm.interior (Φ.velocity (projIcc 0 1 zero_le_one t)) σ.val x)
      0 1 MeasureTheory.volume :=
  (rfl)

/-- The constant diffeotopy has zero Eulerian flux form: its velocity field vanishes. -/
@[simp]
theorem eulerianFluxForm_refl (σ : SmoothForm J M ℝ 2) :
    (refl J ∞ M).eulerianFluxForm σ = 0 := by
  funext x
  rw [eulerianFluxForm_apply, Pi.zero_apply]
  refine (intervalIntegral.integral_congr (g := fun _ ↦ (0 : E [⋀^Fin 1]→L[ℝ] ℝ))
    fun t _ ↦ ?_).trans intervalIntegral.integral_zero
  rw [velocity_refl, RoughForm.interior_zero_field, Pi.zero_apply]
  -- The two zeros differ only in reading the form's values over `TangentSpace J x` or over `E`.
  rfl

/-- **The homotopy-operator integrand of the inverse diffeotopy.** If every time slice `φ_t`
preserves a form `σ`, then `σ` at `φ_t⁻¹ x`, evaluated on the time derivative `∂ₜ (φ_t⁻¹ x)`
followed by the spatial derivatives `d(φ_t⁻¹) v`, is `-σ_x(X_t x, v)`. For a two-form this is the
integrand of the flux form of `φ_t⁻¹` at `(x, t)`. -/
theorem apply_vecCons_mfderiv_cylinderMap_symm {k : ℕ} {σ : SmoothForm J M ℝ (k + 1)}
    (hΦ : ∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ) (p : M × unitInterval)
    (v : Fin k → E) :
    σ.val (Φ.symm.cylinderMap p) (Matrix.vecCons
        (mfderiv (J.prod (𝓡∂ 1)) J Φ.symm.cylinderMap p
          ((0 : E), (1 : TangentSpace (𝓡∂ 1) p.2)))
        fun i ↦ mfderiv (J.prod (𝓡∂ 1)) J Φ.symm.cylinderMap p
          ((v i : E), (0 : EuclideanSpace ℝ (Fin 1)))) =
      -σ.val p.1 (Matrix.vecCons (Φ.velocity p.2 p.1) v) := by
  obtain ⟨x, t⟩ := p
  set h := Φ.timeSlice t
  have hhy : h (Φ.symm.cylinderMap (x, t)) = x := by
    rw [cylinderMap_apply, timeSlice_apply]
    exact Φ.apply_mk_symm_apply t x
  -- The value of `σ` at a point only depends on the point, read in the model space.
  have hpt : ∀ {z z' : M}, z = z' → ∀ w : Fin (k + 1) → E, σ.val z w = σ.val z' w := by
    rintro z _ rfl w
    rfl
  -- The time derivative of `φ_t⁻¹ x` is carried by `dφ_t` to `-X_t x`.
  have htime := Φ.mfderiv_timeSlice_mfderiv_cylinderMap_symm (by simp) t x
  rw [← Φ.symm.cylinderMap_apply (x, t)] at htime
  -- The spatial derivative of `φ_t⁻¹` at `x` is undone by `dφ_t`.
  have hspace := Φ.mfderiv_timeSlice_mfderiv_cylinderMap_symm_inl (by simp) t x
  rw [← Φ.symm.cylinderMap_apply (x, t)] at hspace
  -- Since `φ_t` preserves `σ`, evaluate `σ` after pushing every vector forward by `dφ_t`.
  have hpres := (SmoothForm.mem_diffeomorphStabilizer_iff_forall.1 (hΦ t))
    (Φ.symm.cylinderMap (x, t))
  rw [← hpres, mpullback_apply]
  refine Eq.trans ?_ (((σ.val x).vecCons_smul v (-1) (Φ.velocity t x)).trans (neg_one_smul ℝ _))
  refine (congrArg (σ.val (h (Φ.symm.cylinderMap (x, t)))) (funext fun i ↦ ?_)).trans
    (hpt hhy _)
  cases i using Fin.cases with
  | zero => exact htime.trans (neg_one_smul ℝ (Φ.velocity t x : E)).symm
  | succ i => exact hspace (v i)

/-- **The Eulerian flux form is minus the flux form of the inverse.** If every time slice `φ_t` of
a diffeotopy preserves `σ`, then `∫₀¹ ι_{X_t} σ dt` is minus the flux form
`∫₀¹ ψ_t^* (ι_{Y_t} σ) dt` of the inverse diffeotopy `ψ_t = φ_t⁻¹`, with velocity field `Y_t`. -/
theorem eulerianFluxForm_eq_neg_fluxForm_symm {σ : SmoothForm J M ℝ 2}
    (hΦ : ∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ) :
    Φ.eulerianFluxForm σ = -(Φ.symm.fluxForm σ).val := by
  funext x
  rw [Pi.neg_apply, fluxForm_apply, eulerianFluxForm_apply]
  refine (intervalIntegral.integral_congr fun t _ ↦ ContinuousAlternatingMap.ext fun v ↦ ?_).trans
    intervalIntegral.integral_neg
  rw [ContinuousAlternatingMap.neg_apply, curryLeft_mfderiv_cylinderMap_apply,
    Φ.apply_vecCons_mfderiv_cylinderMap_symm hΦ, neg_neg]
  exact RoughForm.interior_apply _ _ x v

/-- For a symplectic isotopy the Eulerian flux form is smooth. -/
theorem isSmoothForm_eulerianFluxForm {σ : SmoothForm J M ℝ 2}
    (hΦ : ∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ) :
    IsSmoothForm J ∞ (Φ.eulerianFluxForm σ) := by
  rw [Φ.eulerianFluxForm_eq_neg_fluxForm_symm hΦ, ← Submodule.coe_neg]
  exact (-Φ.symm.fluxForm σ).isSmoothForm

/-- For a closed two-form `σ` and a symplectic isotopy, the Eulerian flux form is closed. -/
theorem mextDeriv_eulerianFluxForm_eq_zero {σ : SmoothForm J M ℝ 2} (hσ : σ.IsClosed)
    (hΦ : ∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ) :
    mextDeriv (Φ.eulerianFluxForm σ) = 0 := by
  have hclosed := Φ.symm.fluxForm_mem_closedForms hσ
    (SmoothForm.final_mem_diffeomorphStabilizer
      (SmoothForm.timeSlice_symm_mem_diffeomorphStabilizer hΦ))
  rw [Φ.eulerianFluxForm_eq_neg_fluxForm_symm hΦ, ← Submodule.coe_neg]
  exact (mem_closedForms J _).1 (neg_mem hclosed)

/-- **The flux is the class of the Eulerian flux form.** For a closed two-form `σ` and a diffeotopy
`φ_t` every time slice of which preserves `σ`, the flux `[∫₀¹ φ_t^* (ι_{X_t} σ) dt]` is also the
de Rham class of `∫₀¹ ι_{X_t} σ dt`. -/
theorem flux_eq_mk_eulerianFluxForm (σ : closedForms J M 2)
    (hΦ : ∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ.val) :
    Φ.flux σ (SmoothForm.final_mem_diffeomorphStabilizer hΦ) =
      deRhamCohomology.mk J 1
        ⟨⟨Φ.eulerianFluxForm σ.val, (Φ.isSmoothForm_eulerianFluxForm hΦ).mem_smoothBundleForms⟩,
          (mem_closedForms J _).2 (Φ.mextDeriv_eulerianFluxForm_eq_zero
            ((SmoothForm.isClosed_def _).mpr ((mem_closedForms J σ.val).mp σ.property)) hΦ)⟩ := by
  have hsymm := SmoothForm.final_mem_diffeomorphStabilizer
    (SmoothForm.timeSlice_symm_mem_diffeomorphStabilizer hΦ)
  rw [← neg_neg (Φ.flux σ _), ← Φ.flux_symm σ _ hsymm, flux_def, ← map_neg]
  congr 1
  refine Subtype.ext (Subtype.ext ?_)
  exact (Φ.eulerianFluxForm_eq_neg_fluxForm_symm hΦ).symm

/-! ### Flows -/

section Flow

variable [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold J M]
  {v : (x : M) → TangentSpace J x}

/-- **The Eulerian flux form of a flow.** The diffeotopy which runs a complete smooth vector field
`v` for duration `a` has Eulerian flux form `a ι_v σ`, since its velocity field is the
time-independent field `a v`. Unlike the corresponding formula for the flux form
(`TauCeti.Diffeotopy.fluxForm_globalFlowDiffeotopy`), no condition on `ι_v σ` is needed. -/
theorem eulerianFluxForm_globalFlowDiffeotopy
    (hv : CMDiff ∞ (fun y ↦ (⟨y, v y⟩ : TangentBundle J M))) (hc : IsCompleteVectorField v)
    (a : ℝ) (σ : SmoothForm J M ℝ 2) :
    (globalFlowDiffeotopy le_top hv hc a).eulerianFluxForm σ = a • RoughForm.interior v σ.val := by
  funext x
  rw [eulerianFluxForm_apply]
  -- The integrand is the constant `a ι_v σ`, read in the model space of the integral.
  refine (intervalIntegral.integral_congr
    (g := fun _ ↦ show E [⋀^Fin 1]→L[ℝ] ℝ from a • RoughForm.interior v σ.val x)
    fun t _ ↦ ContinuousAlternatingMap.ext fun w ↦ ?_).trans ?_
  · refine (RoughForm.interior_apply _ _ x w).trans ?_
    rw [velocity_globalFlowDiffeotopy]
    exact ((σ.val x).vecCons_smul w a (v x)).trans
      (congrArg (a • ·) (RoughForm.interior_apply _ _ x w).symm)
  · rw [intervalIntegral.integral_const, sub_zero, one_smul, Pi.smul_apply]

end Flow

end Diffeotopy

end TauCeti
