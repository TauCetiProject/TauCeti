/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Flow
public import TauCeti.Geometry.Symplectic.Flux
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
import TauCeti.Geometry.Manifold.DifferentialForm.Squared
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz

/-!
# Hamiltonian isotopies have zero flux

Let `σ` be a two-form on a manifold `M` and let `φ_t`, `t ∈ [0, 1]`, be a smooth diffeotopy of
`M`, with velocity field `X_t = (∂ₜ φ_t) ∘ φ_t⁻¹`. A function `H : M × [0, 1] → ℝ` is a
**Hamiltonian** of the diffeotopy when every `X_t` is a Hamiltonian vector field of
`H_t = H(·, t)`, that is `ι_{X_t} σ = d H_t`. It is stated along the motion, as
`σ(∂ₜ φ_t x, ·) = d H_t` at `φ_t x` for every `(x, t)` (`TauCeti.Diffeotopy.HasHamiltonian`).
A diffeotopy with a smooth Hamiltonian is a **Hamiltonian isotopy**
(`TauCeti.Diffeotopy.IsHamiltonian`).

The flux form of a diffeotopy is `∫₀¹ φ_t^* (ι_{X_t} σ) dt`
(`TauCeti.Diffeotopy.fluxForm_apply`). For a Hamiltonian isotopy its integrand is
`φ_t^* (d H_t) = d (H_t ∘ φ_t)`, so the flux form is exact, with the explicit primitive

`Flux φ = d (∫₀¹ H_t ∘ φ_t dt)`

(`TauCeti.Diffeotopy.HasHamiltonian.fluxForm_eq`). Hence a Hamiltonian isotopy has zero flux
(`TauCeti.Diffeotopy.HasHamiltonian.flux_eq_zero`). Neither closedness nor nondegeneracy of `σ`
is needed for the exactness, and `M` need not be compact or boundaryless.

The primitive is obtained without differentiating under the integral sign. On the cylinder
`M × [0, 1]`, with time coordinate `t`, the one-form `τ = G dt`, where `G(x, t) = H_t (φ_t x)`, has
homotopy operator `h τ = ∫₀¹ G(·, t) dt` (`TauCeti.homotopyOperator`). Both slices of `τ` vanish,
because `dt` restricts to zero on them, so the cochain-homotopy identity
`d (h τ) + h (d τ) = ι₁^* τ - ι₀^* τ` gives `d (h τ) = -h (d τ)`. By the Leibniz rule
`d τ = dG ∧ dt`, whose contraction with the unit time vector `∂ₜ` is `-dG` on spatial vectors,
and this is minus the integrand of the flux form.

The time-dependent flow of a family of Hamiltonian vector fields `X_t` of functions `H_t` is a
Hamiltonian isotopy with Hamiltonian `H`
(`TauCeti.Diffeotopy.hasHamiltonian_timeDependentFlowDiffeotopy_iff`,
`TauCeti.Diffeotopy.isHamiltonian_timeDependentFlowDiffeotopy`), so its flux vanishes. The
constant diffeotopy is a Hamiltonian isotopy (`TauCeti.Diffeotopy.isHamiltonian_refl`).

## Main definitions

* `TauCeti.Diffeotopy.HasHamiltonian`: `H` is a Hamiltonian of the diffeotopy.
* `TauCeti.Diffeotopy.IsHamiltonian`: the diffeotopy is a Hamiltonian isotopy.

## Main results

* `TauCeti.Diffeotopy.HasHamiltonian.fluxForm_eq`: the flux form of a diffeotopy with a smooth
  Hamiltonian `H` is `d (∫₀¹ H_t ∘ φ_t dt)`.
* `TauCeti.Diffeotopy.HasHamiltonian.flux_eq_zero`, `TauCeti.Diffeotopy.IsHamiltonian.flux_eq_zero`:
  a Hamiltonian isotopy has zero flux.
* `TauCeti.Diffeotopy.hasHamiltonian_timeDependentFlowDiffeotopy_iff`: the time-dependent flow of
  a family of vector fields has Hamiltonian `H` exactly when each field is the Hamiltonian vector
  field of `H_t`.
* `TauCeti.Diffeotopy.isHamiltonian_timeDependentFlowDiffeotopy`: so the time-dependent flow of a
  smooth family of Hamiltonian vector fields is a Hamiltonian isotopy.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2 (the flux homomorphism vanishes on Hamiltonian isotopies).
* Augustin Banyaga, *The Structure of Classical Diffeomorphism Groups*, Kluwer, 1997,
  Chapter 3.
-/

public section

noncomputable section

open Set
open scoped ContDiff Manifold

namespace TauCeti

namespace Diffeotopy

variable {E HM : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {J : ModelWithCorners ℝ E HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold J ∞ M] (Φ : Diffeotopy J ∞ M)

/-! ### Hamiltonians of diffeotopies -/

/-- A function `H : M × [0, 1] → ℝ` is a **Hamiltonian** of the diffeotopy `φ` for the two-form
`σ` when, at every time `t`, the velocity of the motion is a Hamiltonian vector field of
`H_t = H(·, t)`: at every point `(x, t)` of the cylinder, the time derivative `∂ₜ φ_t x` of the
motion satisfies `σ(∂ₜ φ_t x, w) = d H_t (w)` at `φ_t x`. Since every `φ_t` is surjective, this says
that the velocity field `X_t = (∂ₜ φ_t) ∘ φ_t⁻¹` satisfies `ι_{X_t} σ = d H_t`. -/
def HasHamiltonian (σ : SmoothTwoForm J M) (H : M × unitInterval → ℝ) : Prop :=
  ∀ (p : M × unitInterval) (w : TangentSpace J (Φ.cylinderMap p)),
    SmoothBundleForm.eval₂ σ (Φ.cylinderMap p)
        (mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap p ((0 : E), (1 : TangentSpace (𝓡∂ 1) p.2)))
        w =
      mvfderiv J (fun y ↦ H (y, p.2)) (Φ.cylinderMap p) w

/-- A diffeotopy is a **Hamiltonian isotopy** for the two-form `σ` when it has a smooth
Hamiltonian. -/
def IsHamiltonian (σ : SmoothTwoForm J M) : Prop :=
  ∃ H : C^∞⟮J.prod (𝓡∂ 1), M × unitInterval; ℝ⟯, Φ.HasHamiltonian σ H

variable {Φ}

/-- The defining property of a Hamiltonian of a diffeotopy. -/
theorem hasHamiltonian_iff {σ : SmoothTwoForm J M} {H : M × unitInterval → ℝ} :
    Φ.HasHamiltonian σ H ↔ ∀ (p : M × unitInterval) (w : TangentSpace J (Φ.cylinderMap p)),
      SmoothBundleForm.eval₂ σ (Φ.cylinderMap p)
          (mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap p ((0 : E), (1 : TangentSpace (𝓡∂ 1) p.2)))
          w =
        mvfderiv J (fun y ↦ H (y, p.2)) (Φ.cylinderMap p) w :=
  Iff.rfl

/-- The defining property of a Hamiltonian isotopy. -/
theorem isHamiltonian_iff {σ : SmoothTwoForm J M} :
    Φ.IsHamiltonian σ ↔ ∃ H : C^∞⟮J.prod (𝓡∂ 1), M × unitInterval; ℝ⟯, Φ.HasHamiltonian σ H :=
  Iff.rfl

/-- The constant diffeotopy has the zero Hamiltonian: its motion has no time derivative. -/
theorem hasHamiltonian_refl (σ : SmoothTwoForm J M) :
    (refl J ∞ M).HasHamiltonian σ fun _ ↦ 0 := by
  have hcyl : (refl J ∞ M).cylinderMap = Prod.fst := funext fun p ↦ by simp
  refine hasHamiltonian_iff.2 fun p ↦ ?_
  rw [hcyl, mfderiv_fst]
  intro w
  -- The first vector `fst (0, 1)` is zero.
  refine (SmoothBundleForm.eval₂_apply _ _ _ _).trans (((σ.1 p.1).map_coord_zero 0 rfl).trans ?_)
  rw [mvfderiv_const, zero_apply]

/-- The constant diffeotopy is a Hamiltonian isotopy. -/
theorem isHamiltonian_refl (σ : SmoothTwoForm J M) : (refl J ∞ M).IsHamiltonian σ :=
  ⟨⟨fun _ ↦ 0, contMDiff_const⟩, hasHamiltonian_refl σ⟩

/-! ### The primitive of the flux form -/

variable (Φ)

/-- The function `G(x, t) = H_t (φ_t x)` on the cylinder. -/
private def hamiltonianAlongMotion (H : C^∞⟮J.prod (𝓡∂ 1), M × unitInterval; ℝ⟯) :
    C^∞⟮J.prod (𝓡∂ 1), M × unitInterval; ℝ⟯ :=
  ⟨fun p ↦ H (Φ.cylinderMap p, p.2),
    H.contMDiff.comp (Φ.contMDiff_cylinderMap.prodMk contMDiff_snd)⟩

/-- The one-form `τ = G dt` on the cylinder, whose homotopy operator is the primitive of the flux
form. -/
private def hamiltonianTimeForm (H : C^∞⟮J.prod (𝓡∂ 1), M × unitInterval; ℝ⟯) :
    SmoothForm (J.prod (𝓡∂ 1)) (M × unitInterval) ℝ 1 :=
  SmoothForm.funSMulₗ (Φ.hamiltonianAlongMotion H) (cylinderTimeForm J (M := M))

/-- The form `τ = G dt` is the pointwise product of `G` and `dt`. -/
private theorem coe_hamiltonianTimeForm (H : C^∞⟮J.prod (𝓡∂ 1), M × unitInterval; ℝ⟯) :
    (Φ.hamiltonianTimeForm H).1 =
      fun p ↦ Φ.hamiltonianAlongMotion H p • (cylinderTimeForm J (M := M)).1 p := by
  rw [hamiltonianTimeForm, SmoothForm.coe_funSMulₗ]

omit [IsManifold J ∞ M] in
/-- On a tangent vector `u` of the cylinder with zero time component, the derivative of
`G(x, t) = H_t (φ_t x)` is the derivative of `H_t` on the image of `u` under the motion. -/
private theorem mvfderiv_hamiltonianAlongMotion_apply
    (H : C^∞⟮J.prod (𝓡∂ 1), M × unitInterval; ℝ⟯) (p : M × unitInterval)
    (u : TangentSpace (J.prod (𝓡∂ 1)) p) (hu : u.2 = 0) :
    mvfderiv (J.prod (𝓡∂ 1)) (Φ.hamiltonianAlongMotion H) p u =
      mvfderiv J (fun y ↦ H (y, p.2)) (Φ.cylinderMap p)
        (mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap p u) := by
  have hcyl : MDifferentiableAt (J.prod (𝓡∂ 1)) J Φ.cylinderMap p :=
    Φ.contMDiff_cylinderMap.mdifferentiableAt (by simp)
  have hH : MDifferentiableAt (J.prod (𝓡∂ 1)) 𝓘(ℝ) H (Φ.cylinderMap p, p.2) :=
    H.contMDiff.mdifferentiableAt (by simp)
  have hcomp : (Φ.hamiltonianAlongMotion H : M × unitInterval → ℝ) =
      H ∘ fun q ↦ (Φ.cylinderMap q, q.2) := rfl
  rw [mvfderiv_apply_eq_mfderiv_apply, mvfderiv_apply_eq_mfderiv_apply, hcomp,
    mfderiv_comp p hH (hcyl.prodMk mdifferentiableAt_snd), ContinuousLinearMap.comp_apply,
    mfderiv_prodMk hcyl mdifferentiableAt_snd, mfderiv_snd]
  -- The moved vector has zero time component, so only the spatial derivative of `H` survives.
  refine (mfderiv_prod_eq_add_apply hH).trans ?_
  exact add_eq_left.2 ((congrArg _ hu).trans (map_zero _))

/-- Both end slices of `τ = G dt` vanish, since `dt` restricts to zero on every slice. -/
private theorem mpullback_slice_hamiltonianTimeForm (H : C^∞⟮J.prod (𝓡∂ 1), M × unitInterval; ℝ⟯)
    (s : unitInterval) (x : M) :
    mpullback J (J.prod (𝓡∂ 1)) (fun y ↦ (y, s)) (Φ.hamiltonianTimeForm H).1 x = 0 := by
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [mpullback_apply, coe_hamiltonianTimeForm, ContinuousAlternatingMap.smul_apply,
    cylinderTimeForm_apply, mfderiv_prod_left]
  -- The slice moves `v` to `(v, 0)`, whose time component is zero.
  exact (congrArg (_ • ·) (map_zero _)).trans (smul_zero _)

/-- **The integrand of `h (d τ)`.** Contracting `d τ = dG ∧ dt` with a tangent vector `T` of the
cylinder on which `dt` is `1`, such as the unit time vector `∂ₜ`, and evaluating on a tangent vector
`w 0` with zero time component gives `-dG (w 0)`. -/
private theorem mextDeriv_hamiltonianTimeForm_apply
    (H : C^∞⟮J.prod (𝓡∂ 1), M × unitInterval; ℝ⟯) (p : M × unitInterval)
    (T : TangentSpace (J.prod (𝓡∂ 1)) p) (w : Fin 1 → TangentSpace (J.prod (𝓡∂ 1)) p)
    (hT : (cylinderTimeForm J (M := M)).1 p ![T] = 1) (hw : (w 0).2 = 0) :
    mextDeriv (Φ.hamiltonianTimeForm H).1 p (Matrix.vecCons T w) =
      -mvfderiv J (fun y ↦ H (y, p.2)) (Φ.cylinderMap p)
        (mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap p (w 0)) := by
  have hdd : mextDeriv (cylinderTimeForm J (M := M)).1 p ![T, w 0] = 0 := by
    rw [cylinderTimeForm_def, mextDerivₗ_apply, SmoothForm.mextDeriv_mextDeriv]
    rfl
  have h0 : (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : unitInterval → ℝ) p.2 (w 0).2 : ℝ) = 0 := by
    rw [hw]
    exact map_zero _
  have hG : MDifferentiableAt (J.prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) (Φ.hamiltonianAlongMotion H) p :=
    (Φ.hamiltonianAlongMotion H).contMDiff.mdifferentiableAt (by simp)
  have hvec : Matrix.vecCons T w = ![T, w 0] := funext fun i ↦ by fin_cases i <;> rfl
  rw [hvec, coe_hamiltonianTimeForm,
    mextDeriv_fun_smul_apply hG ((cylinderTimeForm J (M := M)).mdifferentiableAt p), hdd, hT,
    cylinderTimeForm_apply, Matrix.cons_val_zero, h0,
    ← Φ.mvfderiv_hamiltonianAlongMotion_apply H p (w 0) hw]
  -- The values of `dt` and of `dG` are real numbers, read in the fibres of the trivial bundle.
  exact (fun a b c : ℝ ↦ (by ring : a * 0 - b * 1 + c * 0 = -b)) _ _ _

/-- The homotopy operator of `τ = G dt` is the `0`-form of the time average `∫₀¹ H_t ∘ φ_t dt`. -/
private theorem homotopyOperator_hamiltonianTimeForm
    (H : C^∞⟮J.prod (𝓡∂ 1), M × unitInterval; ℝ⟯) :
    homotopyOperator (Φ.hamiltonianTimeForm H).1 = RoughForm.ofFunction J fun x ↦
      ∫ t in (0 : ℝ)..1,
        H (Φ.cylinderMap (x, projIcc 0 1 zero_le_one t), projIcc 0 1 zero_le_one t) := by
  funext x
  rw [homotopyOperator_apply, RoughForm.ofFunction_apply_eq_constOfIsEmpty]
  -- The integrand is the constant alternating map of degree zero with value `G(x, t)`.
  refine (intervalIntegral.integral_congr (g := fun t ↦
    ContinuousAlternatingMap.constOfIsEmptyLIE ℝ E ℝ (Fin 0)
      (H (Φ.cylinderMap (x, projIcc 0 1 zero_le_one t), projIcc 0 1 zero_le_one t)))
    fun t _ ↦ ?_).trans ?_
  · refine ContinuousAlternatingMap.ext fun v ↦ ?_
    rw [curryLeft_compContinuousLinearMap_inl_apply, coe_hamiltonianTimeForm,
      ContinuousAlternatingMap.smul_apply, cylinderTimeForm_apply]
    -- The first vector is `∂ₜ`, on which `dt` is `1`.
    exact (congrArg (_ • ·) (mfderiv_subtypeVal_Icc_one _)).trans (mul_one _)
  · exact (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ E ℝ
      (Fin 0)).toLinearIsometry.intervalIntegral_comp_comm _

/-! ### The flux of a Hamiltonian isotopy -/

variable {Φ}

/-- **The flux form of a Hamiltonian isotopy is exact.** If a smooth function `H` is a
Hamiltonian of the diffeotopy `φ` for a two-form `σ`, then the flux form of `φ` is the
differential of the time average of the Hamiltonian along the motion:
`Flux φ = d (∫₀¹ H_t ∘ φ_t dt)`. Neither closedness nor nondegeneracy of `σ` is needed. -/
theorem HasHamiltonian.fluxForm_eq {σ : SmoothTwoForm J M}
    {H : C^∞⟮J.prod (𝓡∂ 1), M × unitInterval; ℝ⟯} (hH : Φ.HasHamiltonian σ H) :
    (Φ.fluxForm σ).1 = mextDeriv (RoughForm.ofFunction J fun x ↦
      ∫ t in (0 : ℝ)..1,
        H (Φ.cylinderMap (x, projIcc 0 1 zero_le_one t), projIcc 0 1 zero_le_one t)) := by
  have : IsManifold J 2 M := IsManifold.of_le (n := ∞) (by simp)
  funext x
  -- The cochain-homotopy identity for `τ = G dt`, whose end slices vanish.
  have key := mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv
    ((Φ.hamiltonianTimeForm H).isSmoothForm.of_le (by simp)) x
  rw [Φ.mpullback_slice_hamiltonianTimeForm, Φ.mpullback_slice_hamiltonianTimeForm, sub_zero,
    add_eq_zero_iff_eq_neg, homotopyOperator_hamiltonianTimeForm] at key
  have hneg : -homotopyOperator (mextDeriv (Φ.hamiltonianTimeForm H).1) =
      homotopyOperator ((-1 : ℝ) • mextDeriv (Φ.hamiltonianTimeForm H).1) := by
    rw [homotopyOperator_smul, neg_one_smul]
  rw [key, ← Pi.neg_apply, hneg, homotopyOperator_apply, fluxForm_apply]
  -- Pointwise in time, the integrand of the flux form is minus the integrand of `h (d τ)`.
  refine intervalIntegral.integral_congr (E := E [⋀^Fin 1]→L[ℝ] ℝ)
    fun t _ ↦ ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [curryLeft_mfderiv_cylinderMap_apply, curryLeft_compContinuousLinearMap_inl_apply]
  refine Eq.trans ?_ (neg_one_smul ℝ _).symm
  refine Eq.trans ?_ (congrArg Neg.neg (Φ.mextDeriv_hamiltonianTimeForm_apply H _ _ _
    (cylinderTimeForm_apply_time _) rfl)).symm
  refine Eq.trans ?_ (neg_neg _).symm
  have h := hasHamiltonian_iff.1 hH (x, projIcc 0 1 zero_le_one t)
    (mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap (x, projIcc 0 1 zero_le_one t)
      ((v 0 : E), (0 : EuclideanSpace ℝ (Fin 1))))
  rw [SmoothBundleForm.eval₂_apply] at h
  refine Eq.trans ?_ h
  exact congrArg (σ.1 _) (funext fun i ↦ by fin_cases i <;> rfl)

/-- The flux form of a diffeotopy with a smooth Hamiltonian is exact. -/
theorem HasHamiltonian.fluxForm_mem_exactForms {σ : SmoothTwoForm J M}
    {H : C^∞⟮J.prod (𝓡∂ 1), M × unitInterval; ℝ⟯} (hH : Φ.HasHamiltonian σ H) :
    Φ.fluxForm σ ∈ exactForms J M 1 := by
  have : IsManifold J ((⊤ : ℕ∞) + 1 : WithTop ℕ∞) M := IsManifold.of_le (n := ∞) (by simp)
  rw [exactForms_succ]
  refine ⟨⟨homotopyOperator (Φ.hamiltonianTimeForm H).1,
    (IsSmoothForm.homotopyOperator (Φ.hamiltonianTimeForm H).isSmoothForm).mem_smoothBundleForms⟩,
    Subtype.ext ?_⟩
  rw [mextDerivₗ_apply, hH.fluxForm_eq]
  exact congrArg mextDeriv (Φ.homotopyOperator_hamiltonianTimeForm H)

/-- **Hamiltonian isotopies have zero flux.** If a smooth function is a Hamiltonian of the
diffeotopy `φ` for a closed two-form `σ` preserved by the final diffeomorphism, then the flux of
`φ` vanishes. -/
theorem HasHamiltonian.flux_eq_zero {σ : closedForms J M 2}
    {H : C^∞⟮J.prod (𝓡∂ 1), M × unitInterval; ℝ⟯} (hH : Φ.HasHamiltonian σ.1 H)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.1) : Φ.flux σ hΦ = 0 := by
  rw [flux_def, deRhamCohomology.mk_eq_zero_iff]
  exact hH.fluxForm_mem_exactForms

/-- **Hamiltonian isotopies have zero flux.** A Hamiltonian isotopy for a closed two-form `σ`
whose final diffeomorphism preserves `σ` has zero flux. -/
theorem IsHamiltonian.flux_eq_zero {σ : closedForms J M 2} (hΦ' : Φ.IsHamiltonian σ.1)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.1) : Φ.flux σ hΦ = 0 :=
  hΦ'.elim fun _ hH ↦ hH.flux_eq_zero hΦ

/-! ### Time-dependent Hamiltonian flows -/

section TimeDependent

variable [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold J M]
  {X : ℝ → (x : M) → TangentSpace J x}
  (hX : ContMDiff (𝓘(ℝ, ℝ).prod J) J.tangent ∞
    (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle J M)))
  (hcomplete : IsCompleteVectorField (timeDependentSuspensionField X))

/-- **Time-dependent Hamiltonian flows.** The diffeotopy generated by a time-dependent vector field
`X` has Hamiltonian `H` exactly when, at every time `t ∈ [0, 1]`, the field `X t` is a
Hamiltonian vector field of `H_t = H(·, t)`. -/
theorem hasHamiltonian_timeDependentFlowDiffeotopy_iff {σ : SmoothTwoForm J M}
    {H : M × unitInterval → ℝ} :
    (timeDependentFlowDiffeotopy le_top hX hcomplete).HasHamiltonian σ H ↔
      ∀ t : unitInterval, σ.IsHamiltonianVectorField (fun y ↦ H (y, t)) (X t) := by
  simp only [hasHamiltonian_iff, SmoothTwoForm.isHamiltonianVectorField_iff,
    mfderiv_cylinderMap_timeDependentFlowDiffeotopy_time]
  refine ⟨fun h t y v ↦ ?_, fun h p w ↦ h p.2 _ w⟩
  -- Every point `y` is the image at time `t` of the point `φ_{t, 0} y`.
  have hy : (timeDependentFlowDiffeotopy le_top hX hcomplete).cylinderMap
      (timeDependentFlowOf X t 0 y, t) = y := by
    rw [cylinderMap_apply, timeDependentFlowDiffeotopy_apply,
      timeDependentFlowOf_trans hcomplete (hX.of_le (by simp)), timeDependentFlowOf_self]
  have := h (timeDependentFlowOf X t 0 y, t)
  rw [hy] at this
  exact this v

/-- **Time-dependent Hamiltonian flows are Hamiltonian isotopies.** If at every time `t ∈ [0, 1]`
the field `X t` is a Hamiltonian vector field of `H_t = H(·, t)` for a smooth `H`, then the
diffeotopy generated by `X` is a Hamiltonian isotopy; in particular its flux vanishes
(`TauCeti.Diffeotopy.IsHamiltonian.flux_eq_zero`). -/
theorem isHamiltonian_timeDependentFlowDiffeotopy {σ : SmoothTwoForm J M}
    {H : C^∞⟮J.prod (𝓡∂ 1), M × unitInterval; ℝ⟯}
    (hH : ∀ t : unitInterval, σ.IsHamiltonianVectorField (fun y ↦ H (y, t)) (X t)) :
    (timeDependentFlowDiffeotopy le_top hX hcomplete).IsHamiltonian σ :=
  ⟨H, (hasHamiltonian_timeDependentFlowDiffeotopy_iff hX hcomplete).2 hH⟩

end TimeDependent

end Diffeotopy

end TauCeti
