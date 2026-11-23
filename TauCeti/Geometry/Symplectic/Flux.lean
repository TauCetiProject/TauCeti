/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Homotopy
public import TauCeti.Geometry.Manifold.DeRham.Map
public import TauCeti.Geometry.Manifold.DifferentialForm.HomotopyOperator
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# The flux of a diffeotopy

Let `σ` be a closed two-form on a manifold `M` (for instance a symplectic form) and let `φ_t`,
`t ∈ [0, 1]`, be a smooth diffeotopy of `M`. Its **flux form** is the one-form

`(Flux φ)ₓ(v) = ∫₀¹ σ_{φ_t x}(∂ₜ φ_t x, dφ_t v) dt`,

that is, `∫₀¹ φ_t^* (ι_{X_t} σ) dt` for the velocity field `X_t = (∂ₜ φ_t) ∘ φ_t⁻¹`. It is the
homotopy operator (`TauCeti.homotopyOperator`) of the pullback of `σ` along the motion
`M × [0, 1] → M`, `(x, t) ↦ φ_t x`, so the cochain-homotopy identity gives

`d (Flux φ) = φ₁^* σ - σ`.

Hence the flux form is closed whenever the final diffeomorphism `φ₁` preserves `σ`, and its de Rham
class is the **flux** `Flux(φ) ∈ H¹_dR(M)`. Only the endpoint condition is needed for this; the
intermediate diffeomorphisms of a symplectic isotopy also preserve `σ`, but that is not used here.

For an exact form `σ = dθ` the flux form is `φ₁^* θ - θ - d g` for some smooth function `g`
which vanishes at the points that the diffeotopy never moves
(`TauCeti.Diffeotopy.exists_fluxForm_mextDerivₗ_eq`); the proof constructs `g` as
`x ↦ ∫₀¹ θ(∂ₜ φ_t x) dt`. So the flux depends only on the final
diffeomorphism: it is the class of the closed form `φ₁^* θ - θ`
(`TauCeti.Diffeotopy.flux_mextDerivₗ`). In particular a
diffeotopy whose final diffeomorphism is the identity has zero flux for an exact form
(`TauCeti.Diffeotopy.flux_eq_zero_of_final_eq_refl`).

Conjugating a diffeotopy by a diffeomorphism `f` transports its flux along `f`
(`TauCeti.Diffeotopy.flux_transDiffeomorph`); the corresponding naturality of the homotopy
operator is `TauCeti.homotopyOperator_mpullback_prodMap_id`. More generally, if a smooth map
`g : M' → M`, not necessarily a diffeomorphism, intertwines diffeotopies `φ'_t` of `M'` and `φ_t`
of `M`, `g ∘ φ'_t = φ_t ∘ g`, then the flux of `φ'_t` for `g^* σ` is the pullback along `g` of the
flux of `φ_t` for `σ` (`TauCeti.Diffeotopy.flux_mpullback_of_semiconj`).

The flux depends only on the homotopy class of the motion relative to both time ends: if a smooth
map `G : (M × [0, 1]) × [0, 1] → M` joins the motions of two diffeotopies and satisfies
`G (x, 0, s) = x` and `G (x, 1, s) = φ₁ x` for every `s`, their flux forms differ by an exact form
(`TauCeti.Diffeotopy.fluxForm_sub_fluxForm_mem_exactForms`). This holds for every closed `σ`,
without assuming that the maps of the homotopy are diffeomorphisms or preserve `σ`; it is the
double-cylinder identity `TauCeti.mextDeriv_homotopyOperator_homotopyOperator` applied to `G^* σ`,
whose terms at the time ends vanish because `G` is stationary in `s` there.

## Main definitions

* `TauCeti.Diffeotopy.fluxForm`: the one-form `∫₀¹ φ_t^* (ι_{X_t} σ) dt` of a smooth diffeotopy.
* `TauCeti.Diffeotopy.flux`: its class in `H¹_dR(M)`, when `φ₁^* σ = σ` for a closed `σ`.

## Main results

* `TauCeti.Diffeotopy.fluxForm_apply`: the integral formula for the flux form.
* `TauCeti.Diffeotopy.curryLeft_mfderiv_cylinderMap_apply`: its integrand, evaluated on tangent
  vectors.
* `TauCeti.Diffeotopy.mextDerivₗ_fluxForm`: `d (Flux φ) = φ₁^* σ - σ` for closed `σ`.
* `TauCeti.Diffeotopy.flux_refl`: the constant diffeotopy has zero flux.
* `TauCeti.Diffeotopy.exists_fluxForm_mextDerivₗ_eq`: for `σ = dθ`, the flux form is
  `φ₁^* θ - θ - d g` for a function `g` vanishing where the diffeotopy is stationary.
* `TauCeti.Diffeotopy.flux_mextDerivₗ`: for `σ = dθ`, the flux is the class of `φ₁^* θ - θ`.
* `TauCeti.Diffeotopy.flux_eq_of_final_eq`: for exact `σ`, diffeotopies with the same final
  diffeomorphism have the same flux.
* `TauCeti.Diffeotopy.flux_transDiffeomorph`: naturality of the flux under conjugation by a
  diffeomorphism.
* `TauCeti.Diffeotopy.flux_transDiffeomorph_of_mem_diffeomorphStabilizer`: its specialization
  to a self-diffeomorphism preserving `σ`.
* `TauCeti.Diffeotopy.fluxForm_mpullback_of_semiconj`,
  `TauCeti.Diffeotopy.flux_mpullback_of_semiconj`: naturality of the flux form and of the flux
  under smooth maps intertwining two diffeotopies.
* `TauCeti.Diffeotopy.fluxForm_sub_fluxForm_mem_exactForms`: homotopy invariance of the flux
  form relative to both time ends.
* `TauCeti.Diffeotopy.flux_eq_of_homotopy`: diffeotopies whose motions are homotopic relative to
  both time ends have the same flux.
* `TauCeti.Diffeotopy.Homotopic.flux_eq`: the same for homotopic diffeotopies
  (`TauCeti.Diffeotopy.Homotopic`).
* `TauCeti.Diffeotopy.flux_eq_zero_of_homotopy_refl`: a diffeotopy homotopic relative to both time
  ends to the constant one has zero flux.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2 (the flux homomorphism).
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
  (Φ : Diffeotopy J ∞ M)

variable [IsManifold J ∞ M]

/-- The **flux form** of a smooth diffeotopy `φ_t` with respect to a two-form `σ`: the one-form
`x ↦ ∫₀¹ σ_{φ_t x}(∂ₜ φ_t x, dφ_t ·) dt`, the homotopy operator of the pullback of `σ` along
the motion `(x, t) ↦ φ_t x`. It is `∫₀¹ φ_t^* (ι_{X_t} σ) dt` for the velocity field `X_t` of the
diffeotopy. -/
def fluxForm (σ : SmoothForm J M ℝ 2) : SmoothForm J M ℝ 1 :=
  have : IsManifold J ((⊤ : ℕ∞) + 1 : WithTop ℕ∞) M := IsManifold.of_le (n := ∞) (by simp)
  ⟨homotopyOperator (SmoothForm.mpullback Φ.cylinderMap Φ.contMDiff_cylinderMap σ).val,
    (IsSmoothForm.homotopyOperator (SmoothForm.mpullback Φ.cylinderMap Φ.contMDiff_cylinderMap
      σ).isSmoothForm).mem_smoothBundleForms⟩

/-- The flux form is the homotopy operator of the pullback of `σ` to the cylinder. -/
theorem coe_fluxForm (σ : SmoothForm J M ℝ 2) :
    (Φ.fluxForm σ).val =
      homotopyOperator (SmoothForm.mpullback Φ.cylinderMap Φ.contMDiff_cylinderMap σ).val :=
  (rfl)

/-- The flux form of the zero form vanishes. -/
@[simp]
theorem fluxForm_zero : Φ.fluxForm 0 = 0 := by
  apply Subtype.ext
  rw [coe_fluxForm, map_zero, Submodule.coe_zero, homotopyOperator_zero, Submodule.coe_zero]

/-- The flux form is additive in the two-form. -/
theorem fluxForm_add (σ τ : SmoothForm J M ℝ 2) :
    Φ.fluxForm (σ + τ) = Φ.fluxForm σ + Φ.fluxForm τ := by
  apply Subtype.ext
  rw [coe_fluxForm, map_add, Submodule.coe_add,
    homotopyOperator_add ((SmoothForm.mpullback _ _ σ).isSmoothForm.of_le (by simp))
      ((SmoothForm.mpullback _ _ τ).isSmoothForm.of_le (by simp)),
    Submodule.coe_add, coe_fluxForm, coe_fluxForm]

/-- The flux form is homogeneous in the two-form. -/
@[simp]
theorem fluxForm_smul (c : ℝ) (σ : SmoothForm J M ℝ 2) :
    Φ.fluxForm (c • σ) = c • Φ.fluxForm σ := by
  apply Subtype.ext
  rw [coe_fluxForm, map_smul, Submodule.coe_smul, homotopyOperator_smul, Submodule.coe_smul,
    coe_fluxForm]

/-- **The flux form as a time integral.** At `x`, the flux form is the integral over `t ∈ [0, 1]`
of the contraction of `σ` with the time derivative `∂ₜ φ_t x` of the motion, composed with the
spatial derivative of the motion. -/
theorem fluxForm_apply (σ : SmoothForm J M ℝ 2) (x : M) :
    (Φ.fluxForm σ).val x = intervalIntegral (E := E [⋀^Fin 1]→L[ℝ] ℝ) (fun t ↦
      (ContinuousAlternatingMap.curryLeft (E := E)
        (σ.val (Φ.cylinderMap (x, projIcc 0 1 zero_le_one t)) : E [⋀^Fin 2]→L[ℝ] ℝ)
        (mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap (x, projIcc 0 1 zero_le_one t)
          ((0 : E), (1 : TangentSpace (𝓡∂ 1) (projIcc 0 1 zero_le_one t))))).compContinuousLinearMap
        ((mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap (x, projIcc 0 1 zero_le_one t) :
          E × EuclideanSpace ℝ (Fin 1) →L[ℝ] E).comp (.inl ℝ E (EuclideanSpace ℝ (Fin 1)))))
      0 1 MeasureTheory.volume := by
  rw [coe_fluxForm, homotopyOperator_apply]
  congr 1
  funext t
  ext v
  -- Both sides evaluate `σ` on the derivative of the motion applied to `∂ₜ` and `(v, 0)`; the
  -- currying and composition operators are unfolded definitionally.
  refine (SmoothForm.mpullback_apply Φ.cylinderMap Φ.contMDiff_cylinderMap σ _
    (Fin.cons _ fun i ↦ ((v i : E), (0 : EuclideanSpace ℝ (Fin 1))))).trans ?_
  exact congrArg _ (funext fun i ↦ by cases i using Fin.cases <;> rfl)

/-- **The integrand of the flux form, evaluated.** On spatial tangent vectors `v`, the integrand
of `TauCeti.Diffeotopy.fluxForm_apply` at `p = (x, t)` is `σ` at the moving point applied to the
time derivative `∂ₜ φ_t x` of the motion followed by the spatial derivatives `dφ_t (v i)`. -/
theorem curryLeft_mfderiv_cylinderMap_apply (σ : SmoothForm J M ℝ 2) (p : M × unitInterval)
    (v : Fin 1 → E) :
    (ContinuousAlternatingMap.curryLeft (E := E)
        (σ.val (Φ.cylinderMap p) : E [⋀^Fin 2]→L[ℝ] ℝ)
        (mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap p
          ((0 : E), (1 : TangentSpace (𝓡∂ 1) p.2)))).compContinuousLinearMap
        ((mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap p :
          E × EuclideanSpace ℝ (Fin 1) →L[ℝ] E).comp (.inl ℝ E (EuclideanSpace ℝ (Fin 1)))) v =
      σ.val (Φ.cylinderMap p) (Matrix.vecCons
        (mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap p ((0 : E), (1 : TangentSpace (𝓡∂ 1) p.2)))
        fun i ↦ mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap p
          ((v i : E), (0 : EuclideanSpace ℝ (Fin 1)))) :=
  -- The tangent spaces of the cylinder are the model spaces by definition, so the currying and
  -- composition operators unfold definitionally.
  (rfl)

/-- Pulling a form back to the cylinder along the motion and then restricting to the initial time
`t = 0` gives the form itself. -/
theorem mpullback_slice_zero_mpullback_cylinderMap {k : ℕ} (ψ : SmoothForm J M ℝ k) :
    SmoothForm.mpullback (fun x ↦ (x, (0 : unitInterval))) (contMDiff_id.prodMk contMDiff_const)
      (SmoothForm.mpullback Φ.cylinderMap Φ.contMDiff_cylinderMap ψ) = ψ := by
  have hslice : MDifferentiable J (J.prod (𝓡∂ 1)) fun x : M ↦ (x, (0 : unitInterval)) :=
    (contMDiff_id.prodMk contMDiff_const).mdifferentiable (n := 1) one_ne_zero
  apply Subtype.ext
  rw [SmoothForm.coe_mpullback, SmoothForm.coe_mpullback,
    ← TauCeti.mpullback_comp hslice (Φ.contMDiff_cylinderMap.mdifferentiable (by simp)),
    cylinderMap_comp_zero, TauCeti.mpullback_id]

/-- Pulling a form back to the cylinder along the motion and then restricting to the final time
`t = 1` gives the pullback of the form by the final diffeomorphism. -/
theorem mpullback_slice_one_mpullback_cylinderMap {k : ℕ} (ψ : SmoothForm J M ℝ k) :
    SmoothForm.mpullback (fun x ↦ (x, (1 : unitInterval))) (contMDiff_id.prodMk contMDiff_const)
      (SmoothForm.mpullback Φ.cylinderMap Φ.contMDiff_cylinderMap ψ) =
        SmoothForm.mpullback Φ.final Φ.final.contMDiff ψ := by
  have hslice : MDifferentiable J (J.prod (𝓡∂ 1)) fun x : M ↦ (x, (1 : unitInterval)) :=
    (contMDiff_id.prodMk contMDiff_const).mdifferentiable (n := 1) one_ne_zero
  apply Subtype.ext
  rw [SmoothForm.coe_mpullback, SmoothForm.coe_mpullback,
    ← TauCeti.mpullback_comp hslice (Φ.contMDiff_cylinderMap.mdifferentiable (by simp)),
    cylinderMap_comp_one, SmoothForm.coe_mpullback]

/-- Pulling a form back to the cylinder along the motion and then restricting to the two ends
gives the pullback by the final diffeomorphism and the form itself. -/
private theorem mpullback_slice_one_sub_mpullback_slice_zero {k : ℕ} (ψ : SmoothForm J M ℝ k)
    (x : M) :
    mpullback J (J.prod (𝓡∂ 1)) (fun y ↦ (y, 1))
        (SmoothForm.mpullback Φ.cylinderMap Φ.contMDiff_cylinderMap ψ).val x -
      mpullback J (J.prod (𝓡∂ 1)) (fun y ↦ (y, 0))
        (SmoothForm.mpullback Φ.cylinderMap Φ.contMDiff_cylinderMap ψ).val x =
      (SmoothForm.mpullback Φ.final Φ.final.contMDiff ψ).val x - ψ.val x := by
  rw [← SmoothForm.coe_mpullback (fun y ↦ (y, 1)) (contMDiff_id.prodMk contMDiff_const),
    ← SmoothForm.coe_mpullback (fun y ↦ (y, 0)) (contMDiff_id.prodMk contMDiff_const),
    mpullback_slice_one_mpullback_cylinderMap, mpullback_slice_zero_mpullback_cylinderMap]

/-- **The exterior derivative of the flux form.** For a closed two-form `σ`, the flux form of a
diffeotopy is a primitive of the difference between the pullback of `σ` by the final
diffeomorphism and `σ`: `d (Flux φ) = φ₁^* σ - σ`. -/
theorem mextDerivₗ_fluxForm {σ : SmoothForm J M ℝ 2} (hσ : SmoothForm.IsClosed σ) :
    mextDerivₗ J 1 (Φ.fluxForm σ) = SmoothForm.mpullback Φ.final Φ.final.contMDiff σ - σ := by
  set φ := SmoothForm.mpullback Φ.cylinderMap Φ.contMDiff_cylinderMap σ
  have hφ : IsSmoothForm (J.prod (𝓡∂ 1)) 1 φ.val := φ.isSmoothForm.of_le (by simp)
  have hclosed : mextDeriv φ.val = 0 :=
    (SmoothForm.isClosed_def _).mp (hσ.mpullback Φ.cylinderMap Φ.contMDiff_cylinderMap)
  apply Subtype.ext
  funext x
  rw [mextDerivₗ_apply, coe_fluxForm, mextDeriv_homotopyOperator hφ hclosed x,
    mpullback_slice_one_sub_mpullback_slice_zero, Submodule.coe_sub, Pi.sub_apply]

/-- The flux form of a diffeotopy is closed when `σ` is closed and the final diffeomorphism
preserves `σ`. -/
theorem fluxForm_mem_closedForms {σ : SmoothForm J M ℝ 2} (hσ : SmoothForm.IsClosed σ)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ) :
    Φ.fluxForm σ ∈ closedForms J M 1 := by
  rw [mem_closedForms_iff_mextDerivₗ_eq_zero, Φ.mextDerivₗ_fluxForm hσ,
    SmoothForm.mem_diffeomorphStabilizer.mp hΦ, sub_self]

/-- The **flux** of a diffeotopy `φ` with respect to a closed two-form `σ` preserved by its final
diffeomorphism: the de Rham class of the closed flux form `∫₀¹ φ_t^* (ι_{X_t} σ) dt`. For a
symplectic form `σ` and a symplectic isotopy this is the flux of the isotopy. -/
def flux (σ : closedForms J M 2) (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.val) :
    deRhamCohomology J M 1 :=
  deRhamCohomology.mk J 1
    ⟨Φ.fluxForm σ.val, Φ.fluxForm_mem_closedForms
      ((SmoothForm.isClosed_def _).mpr ((mem_closedForms J σ.val).mp σ.property)) hΦ⟩

/-- The flux is the de Rham class of the flux form. -/
theorem flux_def (σ : closedForms J M 2)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.val) :
    Φ.flux σ hΦ = deRhamCohomology.mk J 1
      ⟨Φ.fluxForm σ.val, Φ.fluxForm_mem_closedForms
      ((SmoothForm.isClosed_def _).mpr ((mem_closedForms J σ.val).mp σ.property)) hΦ⟩ :=
  (rfl)

/-! ### The constant diffeotopy -/

/-- The constant diffeotopy has zero flux form: its motion has no time derivative. -/
@[simp]
theorem fluxForm_refl (σ : SmoothForm J M ℝ 2) : (refl J ∞ M).fluxForm σ = 0 := by
  have hcyl : (refl J ∞ M).cylinderMap = Prod.fst := funext fun p ↦ by simp
  -- The motion of the constant diffeotopy is the projection to `M`, which kills the time vector.
  apply Subtype.ext
  rw [coe_fluxForm, SmoothForm.coe_mpullback, hcyl, homotopyOperator_mpullback_fst,
    Submodule.coe_zero]

/-- The constant diffeotopy has zero flux. -/
@[simp]
theorem flux_refl (σ : closedForms J M 2)
    (h : (refl J ∞ M).final ∈ SmoothForm.diffeomorphStabilizer σ.val) :
    (refl J ∞ M).flux σ h = 0 := by
  rw [flux_def, deRhamCohomology.mk_eq_zero_iff]
  simp only [fluxForm_refl, zero_mem]

/-! ### Exact forms -/

/-- **The flux form of an exact form.** For an exact two-form `dθ`, the flux form is
`φ₁^* θ - θ - d g` for some smooth function `g` vanishing at every point which no map of the
diffeotopy moves. The proof takes `g x = ∫₀¹ θ(∂ₜ φ_t x) dt`, the homotopy operator of the
pullback of `θ` along the motion. -/
theorem exists_fluxForm_mextDerivₗ_eq (θ : SmoothForm J M ℝ 1) :
    ∃ g : SmoothForm J M ℝ 0, (∀ x, (∀ t, Φ (t, x) = x) → g.val x = 0) ∧
      Φ.fluxForm (mextDerivₗ J 1 θ) =
        SmoothForm.mpullback Φ.final Φ.final.contMDiff θ - θ - mextDerivₗ J 0 g := by
  have : IsManifold J ((⊤ : ℕ∞) + 1 : WithTop ℕ∞) M := IsManifold.of_le (n := ∞) (by simp)
  set φ := SmoothForm.mpullback Φ.cylinderMap Φ.contMDiff_cylinderMap θ with hφ_def
  have hφ : IsSmoothForm (J.prod (𝓡∂ 1)) 1 φ.val := φ.isSmoothForm.of_le (by simp)
  have hd : mextDeriv φ.val =
      (SmoothForm.mpullback Φ.cylinderMap Φ.contMDiff_cylinderMap (mextDerivₗ J 1 θ)).val := by
    rw [← SmoothForm.mextDerivₗ_mpullback, mextDerivₗ_apply]
  refine ⟨⟨homotopyOperator φ.val,
    (IsSmoothForm.homotopyOperator φ.isSmoothForm).mem_smoothBundleForms⟩, fun x hx ↦ ?_,
    Subtype.ext (funext fun x ↦ ?_)⟩
  · -- Over a point which is never moved, the motion is stationary in time.
    have h0 := homotopyOperator_mpullback_apply_eq_zero (I := J) (f := Φ.cylinderMap)
      (fun t ↦ (Φ.cylinderMap_apply (x, t)).trans (hx t)) θ.val
    rwa [← SmoothForm.coe_mpullback Φ.cylinderMap Φ.contMDiff_cylinderMap, ← hφ_def] at h0
  -- The cochain-homotopy identity for `φ = Φ^* θ` on the cylinder, with `d φ = Φ^* (d θ)`.
  have key := mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv hφ x
  rw [hd, mpullback_slice_one_sub_mpullback_slice_zero] at key
  rw [Submodule.coe_sub, Pi.sub_apply, Submodule.coe_sub, Pi.sub_apply, mextDerivₗ_apply, ← key,
    coe_fluxForm]
  abel

/-- For an exact two-form `dθ`, the flux form differs from `φ₁^* θ - θ` by an exact form, namely
`-d g` for a smooth function `g` (`TauCeti.Diffeotopy.exists_fluxForm_mextDerivₗ_eq`). -/
theorem fluxForm_mextDerivₗ_sub_mem_exactForms (θ : SmoothForm J M ℝ 1) :
    Φ.fluxForm (mextDerivₗ J 1 θ) - (SmoothForm.mpullback Φ.final Φ.final.contMDiff θ - θ) ∈
      exactForms J M 1 := by
  obtain ⟨g, -, hg⟩ := Φ.exists_fluxForm_mextDerivₗ_eq θ
  rw [exactForms_succ]
  exact ⟨-g, by rw [map_neg, hg, sub_sub_cancel_left]⟩

/-- **The flux of an exact form.** For `σ = dθ`, the flux of a diffeotopy whose final
diffeomorphism `φ₁` preserves `σ` is the class of the closed form `φ₁^* θ - θ`. In particular it
depends only on `φ₁`. -/
theorem flux_mextDerivₗ (θ : SmoothForm J M ℝ 1)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer (mextDerivₗ J 1 θ)) :
    Φ.flux ⟨mextDerivₗ J 1 θ, mextDerivₗ_mem_closedForms J 1 θ⟩ hΦ =
      deRhamCohomology.mk J 1 ⟨SmoothForm.mpullback Φ.final Φ.final.contMDiff θ - θ, by
        rw [mem_closedForms_iff_mextDerivₗ_eq_zero, map_sub, SmoothForm.mextDerivₗ_mpullback,
          SmoothForm.mem_diffeomorphStabilizer.mp hΦ, sub_self]⟩ := by
  rw [flux_def, ← sub_eq_zero, ← map_sub, deRhamCohomology.mk_eq_zero_iff]
  exact Φ.fluxForm_mextDerivₗ_sub_mem_exactForms θ

/-- For an exact two-form, two diffeotopies with the same final diffeomorphism have the same
flux. -/
theorem flux_eq_of_final_eq {Ψ : Diffeotopy J ∞ M} (σ : closedForms J M 2)
    (hσ : σ.val ∈ exactForms J M 2) (h : Φ.final = Ψ.final)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (hΨ : Ψ.final ∈ SmoothForm.diffeomorphStabilizer σ.val) :
    Φ.flux σ hΦ = Ψ.flux σ hΨ := by
  obtain ⟨σ, hσc⟩ := σ
  rw [exactForms_succ] at hσ
  obtain ⟨θ, rfl⟩ := hσ
  rw [flux_mextDerivₗ, flux_mextDerivₗ]
  congr 2
  rw [h]

/-- For an exact two-form, a diffeotopy whose final diffeomorphism is the identity has zero
flux. -/
theorem flux_eq_zero_of_final_eq_refl (σ : closedForms J M 2) (hσ : σ.val ∈ exactForms J M 2)
    (h : Φ.final = Diffeomorph.refl J M ∞)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.val) : Φ.flux σ hΦ = 0 := by
  have h' : Φ.final = (refl J ∞ M).final := h.trans final_refl.symm
  rw [Φ.flux_eq_of_final_eq σ hσ h' hΦ (h' ▸ hΦ), flux_refl]

/-! ### Naturality under intertwining maps -/

section Semiconj

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J' : ModelWithCorners ℝ E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  [IsManifold J' ∞ M'] {Φ' : Diffeotopy J' ∞ M'} {g : M' → M}

/-- **Naturality of the flux form under intertwining maps.** If a smooth map `g : M' → M`
intertwines a diffeotopy `φ'_t` of `M'` with the diffeotopy `φ_t` of `M`, `g ∘ φ'_t = φ_t ∘ g` for
every `t`, then the flux form of `φ'_t` for the pullback `g^* σ` is the pullback along `g` of the
flux form of `φ_t` for `σ`. The map `g` need not be a diffeomorphism; the projections of a product
onto its factors are the main examples. -/
theorem fluxForm_mpullback_of_semiconj (hg : ContMDiff J' J ∞ g)
    (h : ∀ t, Function.Semiconj g (Φ'.timeSlice t) (Φ.timeSlice t)) (σ : SmoothForm J M ℝ 2) :
    Φ'.fluxForm (SmoothForm.mpullback g hg σ) = SmoothForm.mpullback g hg (Φ.fluxForm σ) := by
  have hg' : MDifferentiable J' J g := hg.mdifferentiable (by simp)
  have hcyl' : MDifferentiable (J'.prod (𝓡∂ 1)) J' Φ'.cylinderMap :=
    Φ'.contMDiff_cylinderMap.mdifferentiable (by simp)
  have hcyl : MDifferentiable (J.prod (𝓡∂ 1)) J Φ.cylinderMap :=
    Φ.contMDiff_cylinderMap.mdifferentiable (by simp)
  have hprod : MDifferentiable (J'.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1))
      (Prod.map g (id : unitInterval → unitInterval)) :=
    (hg.prodMap contMDiff_id).mdifferentiable (by simp)
  apply Subtype.ext
  rw [coe_fluxForm, SmoothForm.coe_mpullback, SmoothForm.coe_mpullback,
    ← TauCeti.mpullback_comp hcyl' hg', Φ.comp_cylinderMap_of_semiconj h,
    TauCeti.mpullback_comp hprod hcyl,
    ← SmoothForm.coe_mpullback Φ.cylinderMap Φ.contMDiff_cylinderMap σ,
    homotopyOperator_mpullback_prodMap_id_of_isSmoothForm hg'
      ((SmoothForm.mpullback Φ.cylinderMap Φ.contMDiff_cylinderMap σ).isSmoothForm.of_le
        (by simp)),
    SmoothForm.coe_mpullback g hg, coe_fluxForm]

/-- **Naturality of the flux under intertwining maps.** If a smooth map `g : M' → M` intertwines
a diffeotopy `φ'_t` of `M'` with the diffeotopy `φ_t` of `M` at every time, then the flux of `φ'_t`
for the closed form `g^* σ` is the pullback along `g` of the flux of `φ_t` for `σ`. -/
theorem flux_mpullback_of_semiconj (hg : ContMDiff J' J ∞ g)
    (h : ∀ t, Function.Semiconj g (Φ'.timeSlice t) (Φ.timeSlice t)) (σ : closedForms J M 2)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (hΦ' : Φ'.final ∈ SmoothForm.diffeomorphStabilizer (closedForms.mpullback g hg 2 σ).val) :
    Φ'.flux (closedForms.mpullback g hg 2 σ) hΦ' =
      deRhamCohomology.map g hg 1 (Φ.flux σ hΦ) := by
  rw [flux_def, flux_def, deRhamCohomology.map_mk]
  congr 1
  apply Subtype.ext
  simp only [closedForms.coe_mpullback]
  exact Φ.fluxForm_mpullback_of_semiconj hg h σ.val

end Semiconj

/-! ### Naturality -/

section Naturality

variable {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold J ∞ P]

/-- The final diffeomorphism of a diffeotopy conjugated by `f` preserves `σ` exactly when the
original final diffeomorphism preserves `f^* σ`. -/
theorem final_transDiffeomorph_mem_diffeomorphStabilizer_iff (f : M ≃ₘ⟮J, J⟯ P)
    (σ : SmoothForm J P ℝ 2) :
    (Φ.transDiffeomorph f).final ∈ SmoothForm.diffeomorphStabilizer σ ↔
      Φ.final ∈ SmoothForm.diffeomorphStabilizer (SmoothForm.mpullback f f.contMDiff σ) := by
  rw [SmoothForm.mem_diffeomorphStabilizer, SmoothForm.mem_diffeomorphStabilizer,
    final_transDiffeomorph, SmoothForm.mpullback_trans, SmoothForm.mpullback_trans]
  constructor
  · intro h
    have h' := congrArg (SmoothForm.mpullback f f.contMDiff) h
    rwa [SmoothForm.mpullback_mpullback_symm] at h'
  · intro h
    rw [h, SmoothForm.mpullback_symm_mpullback]

/-- **Naturality of the flux form.** Conjugating a diffeotopy by a diffeomorphism `f` transports
its flux form: the flux form of `f ∘ φ_t ∘ f⁻¹` for `σ` is the pullback along `f⁻¹` of the flux
form of `φ_t` for `f^* σ`. -/
theorem fluxForm_transDiffeomorph (f : M ≃ₘ⟮J, J⟯ P) (σ : SmoothForm J P ℝ 2) :
    (Φ.transDiffeomorph f).fluxForm σ = SmoothForm.mpullback f.symm f.symm.contMDiff
      (Φ.fluxForm (SmoothForm.mpullback f f.contMDiff σ)) := by
  rw [← Φ.fluxForm_mpullback_of_semiconj f.symm.contMDiff
      (Φ.semiconj_symm_timeSlice_transDiffeomorph f), SmoothForm.mpullback_symm_mpullback]

/-- **Naturality of the flux.** The flux of a diffeotopy conjugated by a diffeomorphism `f` is
the pullback along `f⁻¹` of the flux of the original diffeotopy for `f^* σ`. -/
theorem flux_transDiffeomorph (f : M ≃ₘ⟮J, J⟯ P) (σ : closedForms J P 2)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer (closedForms.mpullback f f.contMDiff 2 σ).val)
        :
    (Φ.transDiffeomorph f).flux σ ((Φ.final_transDiffeomorph_mem_diffeomorphStabilizer_iff f
        σ.val).2
        (by rwa [← closedForms.coe_mpullback])) =
      deRhamCohomology.map f.symm f.symm.contMDiff 1
        (Φ.flux (closedForms.mpullback f f.contMDiff 2 σ) hΦ) := by
  rw [flux_def, flux_def, deRhamCohomology.map_mk]
  congr 1
  apply Subtype.ext
  simp only [closedForms.coe_mpullback]
  exact Φ.fluxForm_transDiffeomorph f σ.val

/-- **Naturality of the flux under diffeomorphisms preserving `σ`.** Conjugating a diffeotopy by
a diffeomorphism `f` preserving `σ` transports its flux by the pullback along `f⁻¹`. -/
theorem flux_transDiffeomorph_of_mem_diffeomorphStabilizer {σ : closedForms J M 2}
    {f : M ≃ₘ⟮J, J⟯ M} (hf : f ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (h : (Φ.transDiffeomorph f).final ∈ SmoothForm.diffeomorphStabilizer σ.val) :
    (Φ.transDiffeomorph f).flux σ h =
      deRhamCohomology.map f.symm f.symm.contMDiff 1 (Φ.flux σ hΦ) := by
  have hpull : closedForms.mpullback f f.contMDiff 2 σ = σ :=
    Subtype.ext ((closedForms.coe_mpullback f f.contMDiff 2 σ).trans
      (SmoothForm.mem_diffeomorphStabilizer.1 hf))
  -- The flux only depends on the form, not on the proof that `Φ.final` preserves it.
  have key : ∀ (τ : closedForms J M 2) (h' : Φ.final ∈ SmoothForm.diffeomorphStabilizer τ.val),
      τ = σ → Φ.flux τ h' = Φ.flux σ hΦ := by
    rintro _ _ rfl
    rfl
  rw [Φ.flux_transDiffeomorph f σ (by rwa [hpull]), key _ _ hpull]

end Naturality

/-! ### Homotopy invariance -/

section Homotopy

variable {Ψ : Diffeotopy J ∞ M} {G : (M × unitInterval) × unitInterval → M}

/-- **Homotopy invariance of the flux form.** Let `G` be a smooth homotopy from the motion of a
diffeotopy `Φ` to the motion of a diffeotopy `Ψ` that fixes both time ends: `G (x, 0, s) = x` and
`G (x, 1, s) = φ₁ x` for every `s`. Then for a closed two-form `σ` the flux forms of `Φ` and `Ψ`
differ by an exact form. The intermediate maps of `G` need not be diffeomorphisms, and none of the
maps involved needs to preserve `σ`. -/
theorem fluxForm_sub_fluxForm_mem_exactForms {σ : SmoothForm J M ℝ 2}
    (hσ : SmoothForm.IsClosed σ) (hG : ContMDiff ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1)) J ∞ G)
    (hG₀ : ∀ p, G (p, 0) = Φ.cylinderMap p) (hG₁ : ∀ p, G (p, 1) = Ψ.cylinderMap p)
    (h₀ : ∀ x s, G ((x, 0), s) = x) (h₁ : ∀ x s, G ((x, 1), s) = Φ.final x) :
    Ψ.fluxForm σ - Φ.fluxForm σ ∈ exactForms J M 1 := by
  have : IsManifold J ((⊤ : ℕ∞) + 1 : WithTop ℕ∞) M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold (J.prod (𝓡∂ 1)) ((⊤ : ℕ∞) + 1 : WithTop ℕ∞) (M × unitInterval) :=
    IsManifold.of_le (n := ∞) (by simp)
  set τ := SmoothForm.mpullback G hG σ
  -- The slices `s = 0` and `s = 1` of `τ = G^* σ` are the pullbacks of `σ` along the motions.
  have hslice (s : unitInterval) : MDifferentiable (J.prod (𝓡∂ 1)) ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1))
      fun p : M × unitInterval ↦ (p, s) :=
    (contMDiff_id.prodMk contMDiff_const).mdifferentiable (n := 1) one_ne_zero
  have hG' : MDifferentiable ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1)) J G := hG.mdifferentiable (by simp)
  have hτ₀ : mpullback (J.prod (𝓡∂ 1)) ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1)) (fun p ↦ (p, 0)) τ.val =
      (SmoothForm.mpullback Φ.cylinderMap Φ.contMDiff_cylinderMap σ).val := by
    rw [SmoothForm.coe_mpullback, ← TauCeti.mpullback_comp (hslice 0) hG',
      show G ∘ (fun p ↦ (p, 0)) = Φ.cylinderMap from funext hG₀, SmoothForm.coe_mpullback]
  have hτ₁ : mpullback (J.prod (𝓡∂ 1)) ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1)) (fun p ↦ (p, 1)) τ.val =
      (SmoothForm.mpullback Ψ.cylinderMap Ψ.contMDiff_cylinderMap σ).val := by
    rw [SmoothForm.coe_mpullback, ← TauCeti.mpullback_comp (hslice 1) hG',
      show G ∘ (fun p ↦ (p, 1)) = Ψ.cylinderMap from funext hG₁, SmoothForm.coe_mpullback]
  -- Over both ends of the inner cylinder `G` is stationary in `s`, so `h_s τ` vanishes there.
  have hend {c : unitInterval} {g : M → M} (hc : ∀ x s, G ((x, c), s) = g x) :
      mpullback J (J.prod (𝓡∂ 1)) (fun x ↦ (x, c)) (homotopyOperator τ.val) = 0 :=
    funext fun x ↦ mpullback_apply_eq_zero <| by
      rw [SmoothForm.coe_mpullback]
      exact homotopyOperator_mpullback_apply_eq_zero (hc x) σ.val
  -- So the homotopy operators of the two slices of `τ` differ by `-d (h (h τ))`.
  have key := mextDeriv_homotopyOperator_homotopyOperator (I := J) (k := 0)
    (τ.isSmoothForm.of_le (by simp)) ((SmoothForm.isClosed_def _).mp (hσ.mpullback G hG))
  rw [hτ₀, hτ₁, hend h₀, hend h₁, sub_self, zero_sub] at key
  rw [exactForms_succ]
  refine ⟨-⟨homotopyOperator (homotopyOperator τ.val), (IsSmoothForm.homotopyOperator
    (IsSmoothForm.homotopyOperator τ.isSmoothForm)).mem_smoothBundleForms⟩,
    Subtype.ext ?_⟩
  -- The flux forms are `h (Ψ^* σ)` and `h (Φ^* σ)`.
  rw [map_neg, Submodule.coe_neg, mextDerivₗ_apply, Submodule.coe_sub, coe_fluxForm, coe_fluxForm]
  exact neg_eq_iff_eq_neg.mpr key

/-- **Homotopy invariance of the flux.** Diffeotopies whose motions are joined by a smooth homotopy
fixing both time ends have the same flux with respect to every closed two-form preserved by their
common final diffeomorphism. -/
theorem flux_eq_of_homotopy (σ : closedForms J M 2)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (hG : ContMDiff ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1)) J ∞ G)
    (hG₀ : ∀ p, G (p, 0) = Φ.cylinderMap p) (hG₁ : ∀ p, G (p, 1) = Ψ.cylinderMap p)
    (h₀ : ∀ x s, G ((x, 0), s) = x) (h₁ : ∀ x s, G ((x, 1), s) = Φ.final x) :
    Ψ.flux σ (Φ.final_eq_of_homotopy hG₁ h₁ ▸ hΦ) = Φ.flux σ hΦ := by
  rw [flux_def, flux_def, ← sub_eq_zero, ← map_sub, deRhamCohomology.mk_eq_zero_iff]
  exact Φ.fluxForm_sub_fluxForm_mem_exactForms
    ((SmoothForm.isClosed_def _).mpr ((mem_closedForms J σ.val).mp σ.property)) hG hG₀ hG₁ h₀ h₁

variable {Φ} in
/-- **Homotopic diffeotopies have the same flux** (`TauCeti.Diffeotopy.Homotopic`) with respect to
every closed two-form preserved by their common final diffeomorphism. -/
theorem Homotopic.flux_eq (σ : closedForms J M 2) (h : Φ.Homotopic Ψ)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (hΨ : Ψ.final ∈ SmoothForm.diffeomorphStabilizer σ.val) : Φ.flux σ hΦ = Ψ.flux σ hΨ := by
  obtain ⟨G, -, hG, hG₀, hG₁, h₀, h₁, -⟩ := homotopic_iff.mp h
  exact (Φ.flux_eq_of_homotopy σ hΦ hG hG₀ hG₁ h₀ h₁).symm

/-- A diffeotopy whose motion is homotopic, through a smooth homotopy fixing both time ends, to the
constant motion has zero flux with respect to every closed two-form. Its final diffeomorphism is
then the identity, so this applies to the loops of diffeomorphisms that are contractible relative
to their ends. -/
theorem flux_eq_zero_of_homotopy_refl (σ : closedForms J M 2)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.val)
    (hG : ContMDiff ((J.prod (𝓡∂ 1)).prod (𝓡∂ 1)) J ∞ G)
    (hG₀ : ∀ p, G (p, 0) = Φ.cylinderMap p) (hG₁ : ∀ p, G (p, 1) = p.1)
    (h₀ : ∀ x s, G ((x, 0), s) = x) (h₁ : ∀ x s, G ((x, 1), s) = x) :
    Φ.flux σ hΦ = 0 := by
  -- Running `G` backwards in `s` joins the constant motion to the motion of `Φ`.
  have hfinal : Φ.final = (refl J ∞ M).final :=
    (refl J ∞ M).final_eq_of_homotopy (G := fun q ↦ G (q.1, unitInterval.symm q.2))
      (fun p ↦ by rw [unitInterval.symm_one, hG₀]) fun x s ↦ by
        rw [h₁, final_refl, Diffeomorph.coe_refl, id_eq]
  rw [← Φ.flux_eq_of_homotopy σ hΦ hG hG₀ (fun p ↦ by rw [hG₁, cylinderMap_apply, refl_apply])
    h₀ fun x s ↦ by rw [h₁, hfinal, final_refl, Diffeomorph.coe_refl, id_eq], flux_refl]

end Homotopy

end Diffeotopy

end TauCeti
