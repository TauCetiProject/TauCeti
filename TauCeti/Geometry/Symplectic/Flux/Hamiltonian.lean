/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Velocity
public import TauCeti.Geometry.Symplectic.Flux
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# Hamiltonian diffeotopies have zero flux

Let `σ` be a two-form on a manifold `M` and let `φ_t`, `t ∈ [0, 1]`, be a smooth diffeotopy of
`M`. It is **Hamiltonian**, with time-dependent Hamiltonian `H_t = H (t, ·)`
(`TauCeti.Diffeotopy.IsHamiltonian`), when at every time its Eulerian velocity field
`X_t = (∂ₜ φ_t) ∘ φ_t⁻¹` is a Hamiltonian vector field of `H_t`: `ι_{X_t} σ = d H_t`. Along the
motion this reads `σ(∂ₜ φ_t x, w) = d H_t (w)` at `φ_t x`
(`TauCeti.Diffeotopy.isHamiltonian_iff_forall_eval₂_velocity`).

For a jointly `C¹` Hamiltonian, the flux form `∫₀¹ φ_t^* (ι_{X_t} σ) dt` of a Hamiltonian
diffeotopy (`TauCeti.Diffeotopy.fluxForm`) is the differential of the time average of the
Hamiltonian along the motion (`TauCeti.Diffeotopy.IsHamiltonian.coe_fluxForm`):

`Flux φ = d (x ↦ ∫₀¹ H_t (φ_t x) dt)`.

For a smooth Hamiltonian this time average is smooth, so the flux form is exact and the flux of a
Hamiltonian diffeotopy vanishes in `H¹_dR(M)`
(`TauCeti.Diffeotopy.IsHamiltonian.flux_eq_zero`). This is one half of the characterization of
the kernel of the flux homomorphism by Hamiltonian isotopies. Neither closedness nor
nondegeneracy of `σ` is needed for the formula, and `M` may have boundary or corners.

The proof differentiates under the integral sign with the cochain-homotopy identity
`d (h β) + h (d β) = ι₁^* β - ι₀^* β` of the homotopy operator `h` on the cylinder `M × [0, 1]`
(`TauCeti.mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv`), applied to the one-form
`β = K dt` with `K (x, t) = H_t (φ_t x)`. Since `dt` restricts to zero on every slice `M × {s}`,
the right side vanishes, and `h β` is the time average of `K`. On the other hand `d β = dK ∧ dt`,
so `d β (∂ₜ, (u, 0)) = -dK (u, 0) = -d H_t (dφ_t u)`, which by the Hamiltonian equation is minus
the integrand `σ(∂ₜ φ_t x, dφ_t u)` of the flux form. Hence `Flux φ = -h (d β) = d (h β)`.

## Main definitions

* `TauCeti.Diffeotopy.IsHamiltonian`: a diffeotopy whose Eulerian velocity field is the Hamiltonian
  vector field of a time-dependent Hamiltonian.

## Main results

* `TauCeti.Diffeotopy.isHamiltonian_iff_forall_eval₂_velocity`: the Hamiltonian equation along the
  motion.
* `TauCeti.Diffeotopy.IsHamiltonian.coe_fluxForm`: the flux form of a Hamiltonian diffeotopy is
  `d (x ↦ ∫₀¹ H_t (φ_t x) dt)`.
* `TauCeti.Diffeotopy.IsHamiltonian.fluxForm_mem_exactForms`: the flux form is exact.
* `TauCeti.Diffeotopy.IsHamiltonian.flux_eq_zero`: Hamiltonian diffeotopies have zero flux.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2 (Hamiltonian isotopies have zero flux).
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

/-! ### Hamiltonian diffeotopies -/

section IsHamiltonian

variable [IsManifold J ∞ M] (Φ : Diffeotopy J ∞ M)

/-- A diffeotopy `φ_t` is **Hamiltonian** for the two-form `σ`, with time-dependent Hamiltonian
`H_t = H (t, ·)`, when at every time `t` its Eulerian velocity field `X_t = (∂ₜ φ_t) ∘ φ_t⁻¹` is a
Hamiltonian vector field of `H_t`: `ι_{X_t} σ = d H_t`. -/
def IsHamiltonian (σ : SmoothTwoForm J M) (H : unitInterval × M → ℝ) : Prop :=
  ∀ t, σ.IsHamiltonianVectorField (fun y ↦ H (t, y)) (Φ.eulerianField t)

variable {Φ} {σ : SmoothTwoForm J M} {H : unitInterval × M → ℝ}

/-- The defining property of a Hamiltonian diffeotopy: its Eulerian velocity field is a
Hamiltonian vector field of `H_t` at every time `t`. -/
theorem isHamiltonian_iff :
    Φ.IsHamiltonian σ H ↔ ∀ t, σ.IsHamiltonianVectorField (fun y ↦ H (t, y)) (Φ.eulerianField t) :=
  Iff.rfl

/-- **The Hamiltonian equation along the motion.** A diffeotopy is Hamiltonian exactly when
`σ(∂ₜ φ_t x, w) = d H_t (w)` at `φ_t x`, for every time `t`, point `x` and tangent vector `w`
at `φ_t x`. -/
theorem isHamiltonian_iff_forall_eval₂_velocity :
    Φ.IsHamiltonian σ H ↔ ∀ t x (w : TangentSpace J (Φ (t, x))),
      SmoothBundleForm.eval₂ σ (Φ (t, x)) (Φ.velocity t x) w =
        mvfderiv J (fun y ↦ H (t, y)) (Φ (t, x)) w := by
  simp only [isHamiltonian_iff, SmoothTwoForm.isHamiltonianVectorField_iff]
  refine ⟨fun hΦ t x w ↦ ?_, fun h t y w ↦ ?_⟩
  · have h := hΦ t (Φ (t, x)) w
    rwa [eulerianField_apply_apply] at h
  · obtain ⟨x, rfl⟩ : ∃ x, Φ (t, x) = y :=
      ⟨(Φ.timeSlice t).symm y, by rw [← timeSlice_apply, Diffeomorph.apply_symm_apply]⟩
    rw [eulerianField_apply_apply]
    exact h t x w

/-- Along the motion of a Hamiltonian diffeotopy, `σ(∂ₜ φ_t x, w) = d H_t (w)` at `φ_t x`. -/
theorem IsHamiltonian.eval₂_velocity (hΦ : Φ.IsHamiltonian σ H) (t : unitInterval) (x : M)
    (w : TangentSpace J (Φ (t, x))) :
    SmoothBundleForm.eval₂ σ (Φ (t, x)) (Φ.velocity t x) w =
      mvfderiv J (fun y ↦ H (t, y)) (Φ (t, x)) w :=
  isHamiltonian_iff_forall_eval₂_velocity.mp hΦ t x w

/-- The constant diffeotopy is Hamiltonian exactly for the Hamiltonians whose time slices all have
vanishing differential. -/
theorem isHamiltonian_refl_iff :
    (refl J ∞ M).IsHamiltonian σ H ↔ ∀ t y, mvfderiv J (fun y ↦ H (t, y)) y = 0 := by
  simp only [isHamiltonian_iff, eulerianField_refl, SmoothTwoForm.isHamiltonianVectorField_iff,
    Pi.zero_apply, SmoothBundleForm.eval₂_apply, ContinuousLinearMap.ext_iff, zero_apply]
  refine forall_congr' fun t ↦ forall_congr' fun y ↦ forall_congr' fun w ↦ ?_
  rw [(σ.1 y).map_coord_zero 0 rfl, eq_comm]

end IsHamiltonian

/-! ### The time form and the time average on the cylinder -/

section Cylinder

variable (Φ : Diffeotopy J ∞ M) (H : unitInterval × M → ℝ)

/-- The time coordinate `(x, t) ↦ t` of the cylinder `M × [0, 1]`. -/
private def timeCoord : M × unitInterval → ℝ := fun p ↦ (p.2 : ℝ)

private theorem contMDiff_timeCoord : ContMDiff (J.prod (𝓡∂ 1)) 𝓘(ℝ) ∞ (timeCoord (M := M)) :=
  contMDiff_subtypeVal_Icc.comp contMDiff_snd

/-- The differential of the time coordinate only sees the time component of a tangent vector. -/
private theorem mfderiv_timeCoord_apply (p : M × unitInterval)
    (w : TangentSpace (J.prod (𝓡∂ 1)) p) :
    mfderiv (J.prod (𝓡∂ 1)) 𝓘(ℝ) (timeCoord (M := M)) p w =
      mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : unitInterval → ℝ) p.2 w.2 := by
  rw [show (timeCoord (M := M)) = Subtype.val ∘ Prod.snd from rfl, mfderiv_comp_snd]
  rfl

/-- The Hamiltonian read along the motion, `K (x, t) = H_t (φ_t x)`. -/
private def motionHamiltonian : M × unitInterval → ℝ := fun p ↦ H (p.2, Φ (p.2, p.1))

private theorem contMDiff_motionHamiltonian {n : ℕ∞} (hH : ContMDiff ((𝓡∂ 1).prod J) 𝓘(ℝ) n H) :
    ContMDiff (J.prod (𝓡∂ 1)) 𝓘(ℝ) n (motionHamiltonian Φ H) :=
  (hH.comp (contMDiff_snd.prodMk (Φ.contMDiff_cylinderMap.of_le
    (WithTop.coe_le_coe.mpr le_top)))).congr fun p ↦ by
    rw [Function.comp_apply, cylinderMap_apply]; rfl

/-- The spatial derivative of `K (x, t) = H_t (φ_t x)` is `d H_t ∘ d φ_t`. -/
private theorem mfderiv_motionHamiltonian_inl (hH : ContMDiff ((𝓡∂ 1).prod J) 𝓘(ℝ) 1 H)
    (p : M × unitInterval) (u : E) :
    mfderiv (J.prod (𝓡∂ 1)) 𝓘(ℝ) (motionHamiltonian Φ H) p (u, 0) =
      mfderiv J 𝓘(ℝ) (fun y ↦ H (p.2, y)) (Φ.cylinderMap p)
        (mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap p (u, 0)) := by
  have hHd : MDifferentiable ((𝓡∂ 1).prod J) 𝓘(ℝ) H := hH.mdifferentiable one_ne_zero
  have hcyl : MDifferentiable (J.prod (𝓡∂ 1)) J Φ.cylinderMap :=
    Φ.contMDiff_cylinderMap.mdifferentiable (by simp)
  have hs : MDifferentiableAt J ((𝓡∂ 1).prod J) (fun y : M ↦ (p.2, y)) (Φ.cylinderMap p) :=
    mdifferentiableAt_const.prodMk mdifferentiableAt_id
  rw [show motionHamiltonian Φ H = H ∘ fun q ↦ (q.2, Φ.cylinderMap q) from
      funext fun q ↦ by rw [Function.comp_apply, cylinderMap_apply]; rfl,
    mfderiv_comp p (hHd _) (mdifferentiableAt_snd.prodMk (hcyl p)),
    show (fun y ↦ H (p.2, y)) = H ∘ fun y ↦ (p.2, y) from rfl, mfderiv_comp _ (hHd _) hs,
    mfderiv_prodMk mdifferentiableAt_snd (hcyl p),
    mfderiv_prodMk (f := fun _ : M ↦ p.2) (g := fun y : M ↦ y) mdifferentiableAt_const
      mdifferentiableAt_id, mfderiv_snd, mfderiv_const, show (fun y : M ↦ y) = id from rfl,
    mfderiv_id]
  -- Both sides apply `dH` at `(t, φ_t x)` to the pair `(0, dφ_t (u, 0))`.
  rfl

variable [IsManifold J ∞ M]

/-- The time form `dt` of the cylinder `M × [0, 1]`, as a smooth one-form. -/
private def cylinderTimeForm : SmoothForm (J.prod (𝓡∂ 1)) (M × unitInterval) ℝ 1 :=
  mextDerivₗ (J.prod (𝓡∂ 1)) 0 ⟨RoughForm.ofFunction (J.prod (𝓡∂ 1)) (timeCoord (M := M)),
    (isSmoothForm_ofFunction_iff.mpr contMDiff_timeCoord).mem_smoothBundleForms⟩

private theorem cylinderTimeForm_apply (p : M × unitInterval)
    (w : TangentSpace (J.prod (𝓡∂ 1)) p) :
    (cylinderTimeForm (J := J) (M := M)).1 p ![w] =
      mvfderiv (𝓡∂ 1) (Subtype.val : unitInterval → ℝ) p.2 w.2 := by
  rw [cylinderTimeForm, mextDerivₗ_apply, mextDeriv_ofFunction_apply, mfderiv_timeCoord_apply]
  -- `mvfderiv` is `mfderiv` followed by the identification of the tangent space of `ℝ` with `ℝ`.
  rfl

/-- The one-form `K dt` on the cylinder, for `K (x, t) = H_t (φ_t x)`. -/
private def hamiltonianTimeForm : RoughForm (J.prod (𝓡∂ 1)) (M × unitInterval) ℝ 1 :=
  fun p ↦ motionHamiltonian Φ H p • (cylinderTimeForm (J := J) (M := M)).1 p

private theorem isSmoothForm_hamiltonianTimeForm {n : ℕ∞}
    (hH : ContMDiff ((𝓡∂ 1).prod J) 𝓘(ℝ) n H) :
    IsSmoothForm (J.prod (𝓡∂ 1)) n (hamiltonianTimeForm Φ H) :=
  (cylinderTimeForm.isSmoothForm.of_le (WithTop.coe_le_coe.mpr le_top)).fun_smul
    (contMDiff_motionHamiltonian Φ H hH)

private theorem hamiltonianTimeForm_apply (p : M × unitInterval)
    (a : TangentSpace (J.prod (𝓡∂ 1)) p) :
    hamiltonianTimeForm Φ H p ![a] =
      motionHamiltonian Φ H p * mvfderiv (𝓡∂ 1) (Subtype.val : unitInterval → ℝ) p.2 a.2 := by
  unfold hamiltonianTimeForm
  rw [ContinuousAlternatingMap.smul_apply, cylinderTimeForm_apply, smul_eq_mul]

/-- `d (K dt) (a, w) = -dK (w)` when `dt (a) = 1` and `w` is spatial, since `dt` is closed. -/
private theorem mextDeriv_hamiltonianTimeForm_apply (hH : ContMDiff ((𝓡∂ 1).prod J) 𝓘(ℝ) 1 H)
    (p : M × unitInterval) (a w : TangentSpace (J.prod (𝓡∂ 1)) p)
    (ha : mvfderiv (𝓡∂ 1) (Subtype.val : unitInterval → ℝ) p.2 a.2 = 1) (hw : w.2 = 0) :
    mextDeriv (hamiltonianTimeForm Φ H) p ![a, w] =
      -mvfderiv (J.prod (𝓡∂ 1)) (motionHamiltonian Φ H) p w := by
  have hK := (contMDiff_motionHamiltonian Φ H hH p).mdifferentiableAt one_ne_zero
  have hτ := ((cylinderTimeForm (J := J) (M := M)).isSmoothForm.contMDiff p).mdifferentiableAt
    (n := ∞) (by simp)
  have hw' : mvfderiv (𝓡∂ 1) (Subtype.val : unitInterval → ℝ) p.2 w.2 = 0 := by
    rw [hw]
    exact map_zero _
  unfold hamiltonianTimeForm
  rw [mextDeriv_fun_smul_apply hK hτ, cylinderTimeForm_apply, cylinderTimeForm_apply, ha, hw',
    cylinderTimeForm, mextDerivₗ_apply, SmoothForm.mextDeriv_mextDeriv]
  simp only [Pi.zero_apply, ContinuousAlternatingMap.coe_zero, mul_zero, zero_sub, mul_one,
    add_zero]

/-- The one-form `K dt` vanishes on every time slice `M × {s}`, where `dt` restricts to zero. -/
private theorem mpullback_slice_hamiltonianTimeForm (s : unitInterval) :
    mpullback J (J.prod (𝓡∂ 1)) (fun y ↦ (y, s)) (hamiltonianTimeForm Φ H) = 0 := by
  have hι : MDifferentiable J (J.prod (𝓡∂ 1)) (fun y : M ↦ (y, s)) :=
    mdifferentiable_id.prodMk mdifferentiable_const
  unfold hamiltonianTimeForm
  rw [mpullback_fun_smul]
  funext x
  rw [cylinderTimeForm, mextDerivₗ_apply, mpullback_mextDeriv_ofFunction_apply (hι x)
    ((contMDiff_timeCoord (J := J) (M := M)).mdifferentiable (by simp) _),
    show timeCoord ∘ (fun y : M ↦ (y, s)) = fun _ ↦ (s : ℝ) from rfl, mextDeriv_ofFunction,
    mvfderiv_const]
  ext v
  simp

/-- Evaluating the contraction of a one-form with `a`, composed with `g`, on the empty tuple. -/
private theorem curryLeft_compContinuousLinearMap_apply_fin_zero {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : X [⋀^Fin 1]→L[ℝ] ℝ) (a : X) (g : Y →L[ℝ] X) (v : Fin 0 → Y) :
    ((f.curryLeft a).compContinuousLinearMap g) v = f ![a] := by
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.curryLeft_apply_apply]
  exact congrArg f (funext fun i ↦ by fin_cases i; rfl)

/-- Evaluating the contraction of a two-form with `a`, composed with `g`, on a single vector. -/
private theorem curryLeft_compContinuousLinearMap_apply_fin_one {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : X [⋀^Fin 2]→L[ℝ] ℝ) (a : X) (g : Y →L[ℝ] X) (v : Fin 1 → Y) :
    ((f.curryLeft a).compContinuousLinearMap g) v = f ![a, g (v 0)] := by
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.curryLeft_apply_apply]
  exact congrArg f (funext fun i ↦ by fin_cases i <;> rfl)

/-- The homotopy operator of `K dt` is the time average `x ↦ ∫₀¹ K (x, t) dt`. -/
private theorem homotopyOperator_hamiltonianTimeForm :
    homotopyOperator (hamiltonianTimeForm Φ H) = RoughForm.ofFunction J fun x ↦
      ∫ t in (0 : ℝ)..1, motionHamiltonian Φ H (x, projIcc 0 1 zero_le_one t) := by
  funext x
  rw [homotopyOperator_apply, RoughForm.ofFunction_apply_eq_constOfIsEmpty]
  -- The integrand at time `t` is the constant `0`-form `K (x, t) dt (∂ₜ) = K (x, t)`, and the
  -- integral commutes with the linear isometry `constOfIsEmptyLIE`.
  refine (intervalIntegral.integral_congr (g := fun t ↦
      ContinuousAlternatingMap.constOfIsEmptyLIE (𝕜 := ℝ) (E := E) ℝ (Fin 0)
        (motionHamiltonian Φ H (x, projIcc 0 1 zero_le_one t))) fun t _ ↦ ?_).trans
    ((ContinuousAlternatingMap.constOfIsEmptyLIE (𝕜 := ℝ) (E := E) ℝ
      (Fin 0)).toLinearIsometry.intervalIntegral_comp_comm _)
  ext w
  have ha : mvfderiv (𝓡∂ 1) (Subtype.val : unitInterval → ℝ) (projIcc 0 1 zero_le_one t)
      (1 : TangentSpace (𝓡∂ 1) (projIcc 0 1 zero_le_one t)) = 1 :=
    (mvfderiv_apply_eq_mfderiv_apply _ _ _).trans (mfderiv_subtypeVal_Icc_one _)
  refine (curryLeft_compContinuousLinearMap_apply_fin_zero _ _ _ w).trans
    ((hamiltonianTimeForm_apply Φ H _ _).trans ((congrArg (_ * ·) ha).trans ?_))
  simp

variable {Φ} {σ : SmoothTwoForm J M} {H}

/-- Along a Hamiltonian diffeotopy, the integrand `σ(∂ₜ φ_t x, dφ_t u)` of the flux form is
`-d (K dt) (∂ₜ, (u, 0))`. -/
private theorem eval₂_mfderiv_cylinderMap_eq_neg_mextDeriv (hΦ : Φ.IsHamiltonian σ H)
    (hH : ContMDiff ((𝓡∂ 1).prod J) 𝓘(ℝ) 1 H) (x : M) (s : unitInterval) (u : E) :
    σ.1 (Φ.cylinderMap (x, s))
        ![mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap (x, s) ((0 : E), (1 : TangentSpace (𝓡∂ 1) s)),
          mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap (x, s) (u, 0)] =
      -mextDeriv (hamiltonianTimeForm Φ H) (x, s)
        ![((0 : E), (1 : TangentSpace (𝓡∂ 1) s)), (u, (0 : EuclideanSpace ℝ (Fin 1)))] := by
  have ha : mvfderiv (𝓡∂ 1) (Subtype.val : unitInterval → ℝ) s (1 : TangentSpace (𝓡∂ 1) s) = 1 :=
    (mvfderiv_apply_eq_mfderiv_apply _ _ _).trans (mfderiv_subtypeVal_Icc_one s)
  have h₁ := mextDeriv_hamiltonianTimeForm_apply Φ H hH (x, s)
    ((0 : E), (1 : TangentSpace (𝓡∂ 1) s)) (u, 0) ha rfl
  have h₂ := hΦ.eval₂_velocity s x (mfderiv (J.prod (𝓡∂ 1)) J Φ.cylinderMap (x, s) (u, 0))
  have hc : Φ (s, x) = Φ.cylinderMap (x, s) := (Φ.cylinderMap_apply (x, s)).symm
  rw [velocity_def, hc, SmoothBundleForm.eval₂_apply] at h₂
  rw [h₁, neg_neg]
  -- `h₂` is the claim with `mvfderiv` for `mfderiv`, which agree by definition.
  exact h₂.trans (mfderiv_motionHamiltonian_inl Φ H hH (x, s) u).symm

/-- The flux form of a Hamiltonian diffeotopy is `d (h (K dt))`: apply the cochain-homotopy
identity `d (h β) + h (d β) = ι₁^* β - ι₀^* β` to `β = K dt`, whose slices vanish, and compare the
integrand of `h (d β)` with that of the flux form by the Hamiltonian equation. -/
private theorem fluxForm_apply_eq_mextDeriv_homotopyOperator (hΦ : Φ.IsHamiltonian σ H)
    (hH : ContMDiff ((𝓡∂ 1).prod J) 𝓘(ℝ) 1 H) (x : M) :
    (Φ.fluxForm σ).1 x = mextDeriv (homotopyOperator (hamiltonianTimeForm Φ H)) x := by
  have hid := mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv
    (isSmoothForm_hamiltonianTimeForm Φ H (n := 1) hH) x
  rw [mpullback_slice_hamiltonianTimeForm, mpullback_slice_hamiltonianTimeForm, sub_self,
    add_eq_zero_iff_eq_neg] at hid
  rw [hid, fluxForm_apply, homotopyOperator_apply]
  refine Eq.trans ?_ (intervalIntegral.integral_neg (E := E [⋀^Fin 1]→L[ℝ] ℝ))
  congr 1
  funext t
  ext v
  rw [ContinuousAlternatingMap.neg_apply]
  convert eval₂_mfderiv_cylinderMap_eq_neg_mextDeriv hΦ hH x (projIcc 0 1 zero_le_one t) (v 0)
    using 3 <;>
  exact curryLeft_compContinuousLinearMap_apply_fin_one _ _ _ v

end Cylinder

/-! ### The flux of a Hamiltonian diffeotopy -/

variable [IsManifold J ∞ M] {Φ : Diffeotopy J ∞ M} {σ : SmoothTwoForm J M}
  {H : unitInterval × M → ℝ}

/-- **The flux form of a Hamiltonian diffeotopy.** If the Eulerian velocity field of a diffeotopy
`φ_t` is the Hamiltonian vector field of a jointly `C¹` time-dependent Hamiltonian `H_t`, then its
flux form is the differential of the time average of the Hamiltonian along the motion:
`Flux φ = d (x ↦ ∫₀¹ H_t (φ_t x) dt)`. -/
theorem IsHamiltonian.coe_fluxForm (hΦ : Φ.IsHamiltonian σ H)
    (hH : ContMDiff ((𝓡∂ 1).prod J) 𝓘(ℝ) 1 H) :
    (Φ.fluxForm σ).1 = mextDeriv (RoughForm.ofFunction J fun x ↦
      ∫ t in (0 : ℝ)..1, H (projIcc 0 1 zero_le_one t, Φ (projIcc 0 1 zero_le_one t, x))) := by
  funext x
  rw [fluxForm_apply_eq_mextDeriv_homotopyOperator hΦ hH, homotopyOperator_hamiltonianTimeForm]
  -- `K (x, t) = H_t (φ_t x)` by definition.
  rfl

/-- **The flux form of a Hamiltonian diffeotopy is exact**, for a smooth Hamiltonian. -/
theorem IsHamiltonian.fluxForm_mem_exactForms (hΦ : Φ.IsHamiltonian σ H)
    (hH : ContMDiff ((𝓡∂ 1).prod J) 𝓘(ℝ) ∞ H) : Φ.fluxForm σ ∈ exactForms J M 1 := by
  have : IsManifold J ((⊤ : ℕ∞) + 1 : WithTop ℕ∞) M := IsManifold.of_le (n := ∞) (by simp)
  rw [exactForms_succ]
  refine ⟨⟨homotopyOperator (hamiltonianTimeForm Φ H),
    ((isSmoothForm_hamiltonianTimeForm Φ H (n := ⊤) hH).homotopyOperator).mem_smoothBundleForms⟩,
    Subtype.ext ?_⟩
  rw [mextDerivₗ_apply]
  exact funext fun x ↦
    (fluxForm_apply_eq_mextDeriv_homotopyOperator hΦ (hH.of_le (by simp)) x).symm

/-- **Hamiltonian diffeotopies have zero flux.** If the Eulerian velocity field of a diffeotopy is
the Hamiltonian vector field of a smooth time-dependent Hamiltonian for a closed two-form `σ`
preserved by its final diffeomorphism, then its flux in `H¹_dR(M)` vanishes. -/
theorem IsHamiltonian.flux_eq_zero {σ : closedForms J M 2} (hΦ : Φ.IsHamiltonian σ.1 H)
    (hH : ContMDiff ((𝓡∂ 1).prod J) 𝓘(ℝ) ∞ H)
    (hfin : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ.1) : Φ.flux σ hfin = 0 := by
  rw [flux_def, deRhamCohomology.mk_eq_zero_iff]
  exact hΦ.fluxForm_mem_exactForms hH

end Diffeotopy

end TauCeti
