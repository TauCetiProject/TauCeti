/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
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

For an exact form `σ = dθ` the flux depends only on the final diffeomorphism: it is the class of
the closed form `φ₁^* θ - θ` (`TauCeti.Diffeotopy.flux_mextDerivₗ`). In particular a
diffeotopy whose final diffeomorphism is the identity has zero flux for an exact form
(`TauCeti.Diffeotopy.flux_eq_zero_of_final_eq_refl`).

Conjugating a diffeotopy by a diffeomorphism `f` transports its flux along `f`
(`TauCeti.Diffeotopy.flux_transDiffeomorph`); the corresponding naturality of the homotopy
operator is `TauCeti.homotopyOperator_mpullback_prodMap_id`.

## Main definitions

* `TauCeti.Diffeotopy.fluxForm`: the one-form `∫₀¹ φ_t^* (ι_{X_t} σ) dt` of a smooth diffeotopy.
* `TauCeti.Diffeotopy.flux`: its class in `H¹_dR(M)`, when `φ₁^* σ = σ` for a closed `σ`.

## Main results

* `TauCeti.Diffeotopy.fluxForm_apply`: the integral formula for the flux form.
* `TauCeti.Diffeotopy.mextDerivₗ_fluxForm`: `d (Flux φ) = φ₁^* σ - σ` for closed `σ`.
* `TauCeti.Diffeotopy.flux_refl`: the constant diffeotopy has zero flux.
* `TauCeti.Diffeotopy.flux_mextDerivₗ`: for `σ = dθ`, the flux is the class of `φ₁^* θ - θ`.
* `TauCeti.Diffeotopy.flux_eq_of_final_eq`: for exact `σ`, diffeotopies with the same final
  diffeomorphism have the same flux.
* `TauCeti.Diffeotopy.flux_transDiffeomorph`: naturality of the flux under conjugation by a
  diffeomorphism.

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

/-- The motion of a diffeotopy read on the cylinder `M × [0, 1]`, with time as the second
coordinate: `(x, t) ↦ φ_t x`. This is the order used by `TauCeti.homotopyOperator`. -/
def cylinderMap : M × unitInterval → M :=
  fun p ↦ Φ (p.2, p.1)

@[simp]
theorem cylinderMap_apply (p : M × unitInterval) : Φ.cylinderMap p = Φ (p.2, p.1) :=
  (rfl)

theorem contMDiff_cylinderMap : ContMDiff (J.prod (𝓡∂ 1)) J ∞ Φ.cylinderMap :=
  Φ.contMDiff.comp (contMDiff_snd.prodMk contMDiff_fst)

/-- The cylinder map at time zero is the identity. -/
theorem cylinderMap_comp_zero : Φ.cylinderMap ∘ (fun x ↦ (x, (0 : unitInterval))) = id :=
  funext Φ.apply_zero

/-- The cylinder map at time one is the final diffeomorphism. -/
theorem cylinderMap_comp_one : Φ.cylinderMap ∘ (fun x ↦ (x, (1 : unitInterval))) = Φ.final :=
  funext fun x ↦ (Φ.final_apply x).symm

variable [IsManifold J ∞ M]

/-- The **flux form** of a smooth diffeotopy `φ_t` with respect to a two-form `σ`: the one-form
`x ↦ ∫₀¹ σ_{φ_t x}(∂ₜ φ_t x, dφ_t ·) dt`, the homotopy operator of the pullback of `σ` along
the motion `(x, t) ↦ φ_t x`. It is `∫₀¹ φ_t^* (ι_{X_t} σ) dt` for the velocity field `X_t` of the
diffeotopy. -/
def fluxForm (σ : SmoothForm J M ℝ 2) : SmoothForm J M ℝ 1 :=
  have : IsManifold J ((⊤ : ℕ∞) + 1 : WithTop ℕ∞) M := IsManifold.of_le (n := ∞) (by simp)
  ⟨homotopyOperator (SmoothForm.mpullback Φ.cylinderMap Φ.contMDiff_cylinderMap σ).1,
    (IsSmoothForm.homotopyOperator (SmoothForm.mpullback Φ.cylinderMap Φ.contMDiff_cylinderMap
      σ).isSmoothForm).mem_smoothBundleForms⟩

/-- The flux form is the homotopy operator of the pullback of `σ` to the cylinder. -/
theorem coe_fluxForm (σ : SmoothForm J M ℝ 2) :
    (Φ.fluxForm σ).1 =
      homotopyOperator (SmoothForm.mpullback Φ.cylinderMap Φ.contMDiff_cylinderMap σ).1 :=
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
    (Φ.fluxForm σ).1 x = intervalIntegral (E := E [⋀^Fin 1]→L[ℝ] ℝ) (fun t ↦
      (ContinuousAlternatingMap.curryLeft (E := E)
        (σ.1 (Φ.cylinderMap (x, projIcc 0 1 zero_le_one t)) : E [⋀^Fin 2]→L[ℝ] ℝ)
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

/-- Pulling a form back to the cylinder along the motion and then restricting to the two ends
gives the pullback by the final diffeomorphism and the form itself. -/
private theorem mpullback_slice_one_sub_mpullback_slice_zero {k : ℕ} (ψ : SmoothForm J M ℝ k)
    (x : M) :
    mpullback J (J.prod (𝓡∂ 1)) (fun y ↦ (y, 1))
        (SmoothForm.mpullback Φ.cylinderMap Φ.contMDiff_cylinderMap ψ).1 x -
      mpullback J (J.prod (𝓡∂ 1)) (fun y ↦ (y, 0))
        (SmoothForm.mpullback Φ.cylinderMap Φ.contMDiff_cylinderMap ψ).1 x =
      (SmoothForm.mpullback Φ.final Φ.final.contMDiff ψ).1 x - ψ.1 x := by
  have hcyl : MDifferentiable (J.prod (𝓡∂ 1)) J Φ.cylinderMap :=
    Φ.contMDiff_cylinderMap.mdifferentiable (by simp)
  have hslice (s : unitInterval) : MDifferentiable J (J.prod (𝓡∂ 1)) fun y : M ↦ (y, s) :=
    (contMDiff_id.prodMk contMDiff_const).mdifferentiable (n := 1) one_ne_zero
  rw [SmoothForm.coe_mpullback, ← TauCeti.mpullback_comp (hslice 1) hcyl,
    ← TauCeti.mpullback_comp (hslice 0) hcyl, cylinderMap_comp_one, cylinderMap_comp_zero,
    TauCeti.mpullback_id, SmoothForm.coe_mpullback]

/-- **The exterior derivative of the flux form.** For a closed two-form `σ`, the flux form of a
diffeotopy is a primitive of the difference between the pullback of `σ` by the final
diffeomorphism and `σ`: `d (Flux φ) = φ₁^* σ - σ`. -/
theorem mextDerivₗ_fluxForm {σ : SmoothForm J M ℝ 2} (hσ : SmoothForm.IsClosed σ) :
    mextDerivₗ J 1 (Φ.fluxForm σ) = SmoothForm.mpullback Φ.final Φ.final.contMDiff σ - σ := by
  set φ := SmoothForm.mpullback Φ.cylinderMap Φ.contMDiff_cylinderMap σ
  have hφ : IsSmoothForm (J.prod (𝓡∂ 1)) 1 φ.1 := φ.isSmoothForm.of_le (by simp)
  have hclosed : mextDeriv φ.1 = 0 :=
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
def flux (σ : closedForms J M 2) (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.1) :
    deRhamCohomology J M 1 :=
  deRhamCohomology.mk J 1
    ⟨Φ.fluxForm σ.1, Φ.fluxForm_mem_closedForms
      ((SmoothForm.isClosed_def _).mpr ((mem_closedForms J σ.1).mp σ.2)) hΦ⟩

/-- The flux is the de Rham class of the flux form. -/
theorem flux_def (σ : closedForms J M 2)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.1) :
    Φ.flux σ hΦ = deRhamCohomology.mk J 1
      ⟨Φ.fluxForm σ.1, Φ.fluxForm_mem_closedForms
      ((SmoothForm.isClosed_def _).mpr ((mem_closedForms J σ.1).mp σ.2)) hΦ⟩ :=
  (rfl)

/-! ### The constant diffeotopy -/

/-- The constant diffeotopy has zero flux form: its motion has no time derivative. -/
@[simp]
theorem fluxForm_refl (σ : SmoothForm J M ℝ 2) : (refl J ∞ M).fluxForm σ = 0 := by
  have hcyl : (refl J ∞ M).cylinderMap = Prod.fst := funext fun p ↦ by simp
  apply Subtype.ext
  funext x
  rw [coe_fluxForm, SmoothForm.coe_mpullback, hcyl,
    ← SmoothForm.coe_mpullback Prod.fst contMDiff_fst, homotopyOperator_apply, Submodule.coe_zero,
    Pi.zero_apply]
  refine (intervalIntegral.integral_congr (E := E [⋀^Fin 1]→L[ℝ] ℝ) (g := fun _ ↦ 0)
    fun t _ ↦ ?_).trans intervalIntegral.integral_zero
  ext v
  -- The motion of the constant diffeotopy is the projection to `M`, which kills the time vector.
  refine (SmoothForm.mpullback_fst_apply (I' := 𝓡∂ 1) (M' := unitInterval) σ
    (x, projIcc 0 1 zero_le_one t)
    (Fin.cons _ fun i ↦ ((v i : E), (0 : EuclideanSpace ℝ (Fin 1))))).trans ?_
  exact (σ.1 x).map_coord_zero 0 (by rw [Manifold.tangentSpaceProdEquiv_apply]; rfl)

/-- The constant diffeotopy has zero flux. -/
@[simp]
theorem flux_refl (σ : closedForms J M 2)
    (h : (refl J ∞ M).final ∈ SmoothForm.diffeomorphStabilizer σ.1) :
    (refl J ∞ M).flux σ h = 0 := by
  rw [flux_def, deRhamCohomology.mk_eq_zero_iff]
  change (refl J ∞ M).fluxForm σ.1 ∈ exactForms J M 1
  rw [fluxForm_refl]
  exact zero_mem _

/-! ### Exact forms -/

/-- For an exact two-form `dθ`, the flux form differs from `φ₁^* θ - θ` by an exact form, namely
`-d g` for the function `g x = ∫₀¹ θ(∂ₜ φ_t x) dt`. -/
theorem fluxForm_mextDerivₗ_sub_mem_exactForms (θ : SmoothForm J M ℝ 1) :
    Φ.fluxForm (mextDerivₗ J 1 θ) - (SmoothForm.mpullback Φ.final Φ.final.contMDiff θ - θ) ∈
      exactForms J M 1 := by
  have : IsManifold J ((⊤ : ℕ∞) + 1 : WithTop ℕ∞) M := IsManifold.of_le (n := ∞) (by simp)
  set φ := SmoothForm.mpullback Φ.cylinderMap Φ.contMDiff_cylinderMap θ
  have hφ : IsSmoothForm (J.prod (𝓡∂ 1)) 1 φ.1 := φ.isSmoothForm.of_le (by simp)
  have hd : mextDeriv φ.1 =
      (SmoothForm.mpullback Φ.cylinderMap Φ.contMDiff_cylinderMap (mextDerivₗ J 1 θ)).1 := by
    rw [← SmoothForm.mextDerivₗ_mpullback, mextDerivₗ_apply]
  rw [exactForms_succ]
  refine ⟨-⟨homotopyOperator φ.1,
    (IsSmoothForm.homotopyOperator φ.isSmoothForm).mem_smoothBundleForms⟩,
    Subtype.ext (funext fun x ↦ ?_)⟩
  -- The cochain-homotopy identity for `φ = Φ^* θ` on the cylinder, with `d φ = Φ^* (d θ)`.
  have key := mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv hφ x
  rw [hd, mpullback_slice_one_sub_mpullback_slice_zero] at key
  rw [map_neg, Submodule.coe_neg, Pi.neg_apply, mextDerivₗ_apply, Submodule.coe_sub, Pi.sub_apply,
    Submodule.coe_sub, Pi.sub_apply, ← key, coe_fluxForm]
  abel

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
    (hσ : σ.1 ∈ exactForms J M 2) (h : Φ.final = Ψ.final)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.1)
    (hΨ : Ψ.final ∈ SmoothForm.diffeomorphStabilizer σ.1) :
    Φ.flux σ hΦ = Ψ.flux σ hΨ := by
  obtain ⟨σ, hσc⟩ := σ
  rw [exactForms_succ] at hσ
  obtain ⟨θ, rfl⟩ := hσ
  rw [flux_mextDerivₗ, flux_mextDerivₗ]
  congr 2
  rw [h]

/-- For an exact two-form, a diffeotopy whose final diffeomorphism is the identity has zero
flux. -/
theorem flux_eq_zero_of_final_eq_refl (σ : closedForms J M 2) (hσ : σ.1 ∈ exactForms J M 2)
    (h : Φ.final = Diffeomorph.refl J M ∞)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.1) : Φ.flux σ hΦ = 0 := by
  have h' : Φ.final = (refl J ∞ M).final := h.trans final_refl.symm
  rw [Φ.flux_eq_of_final_eq σ hσ h' hΦ (h' ▸ hΦ), flux_refl]

/-! ### Naturality -/

section Naturality

variable {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold J ∞ P]

omit [IsManifold J ∞ M] [IsManifold J ∞ P] in
/-- The motion of a conjugated diffeotopy is the conjugated motion. -/
theorem cylinderMap_transDiffeomorph (f : M ≃ₘ⟮J, J⟯ P) :
    (Φ.transDiffeomorph f).cylinderMap = f ∘ Φ.cylinderMap ∘ Prod.map f.symm id :=
  funext fun p ↦ by simp

omit [IsManifold J ∞ M] [IsManifold J ∞ P] in
/-- The final diffeomorphism of a conjugated diffeotopy is the conjugated final diffeomorphism. -/
theorem final_transDiffeomorph (f : M ≃ₘ⟮J, J⟯ P) :
    (Φ.transDiffeomorph f).final = (f.symm.trans Φ.final).trans f :=
  Diffeomorph.ext fun x ↦ by simp

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
  have hf : MDifferentiable J J f := f.mdifferentiable (by simp)
  have hcyl : MDifferentiable (J.prod (𝓡∂ 1)) J Φ.cylinderMap :=
    Φ.contMDiff_cylinderMap.mdifferentiable (by simp)
  have hprod : MDifferentiable (J.prod (𝓡∂ 1)) (J.prod (𝓡∂ 1))
      (Prod.map f.symm (id : unitInterval → unitInterval)) :=
    (f.symm.contMDiff.prodMap contMDiff_id).mdifferentiable (by simp)
  apply Subtype.ext
  rw [coe_fluxForm, SmoothForm.coe_mpullback, cylinderMap_transDiffeomorph,
    TauCeti.mpullback_comp (hcyl.comp hprod) hf, TauCeti.mpullback_comp hprod hcyl,
    homotopyOperator_mpullback_prodMap_id (f.symm.mdifferentiable (by simp))
      fun _ ↦ f.symm.isInvertible_mfderiv (by simp),
    SmoothForm.coe_mpullback, coe_fluxForm, SmoothForm.coe_mpullback, SmoothForm.coe_mpullback]

/-- **Naturality of the flux.** The flux of a diffeotopy conjugated by a diffeomorphism `f` is
the pullback along `f⁻¹` of the flux of the original diffeotopy for `f^* σ`. -/
theorem flux_transDiffeomorph (f : M ≃ₘ⟮J, J⟯ P) (σ : closedForms J P 2)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer (closedForms.mpullback f f.contMDiff 2 σ).1) :
    (Φ.transDiffeomorph f).flux σ ((Φ.final_transDiffeomorph_mem_diffeomorphStabilizer_iff f σ.1).2
        (by rwa [← closedForms.coe_mpullback])) =
      deRhamCohomology.map f.symm f.symm.contMDiff 1
        (Φ.flux (closedForms.mpullback f f.contMDiff 2 σ) hΦ) := by
  rw [flux_def, flux_def, deRhamCohomology.map_mk]
  congr 1
  apply Subtype.ext
  simp only [closedForms.coe_mpullback]
  exact Φ.fluxForm_transDiffeomorph f σ.1

end Naturality

end Diffeotopy

end TauCeti
