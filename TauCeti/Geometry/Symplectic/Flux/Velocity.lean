/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Stabilizer
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Velocity
public import TauCeti.Geometry.Manifold.DeRham.Diffeotopy
public import TauCeti.Geometry.Manifold.Diffeomorph.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.SymplecticVectorField

/-!
# Velocity fields of symplectic isotopies modulo Hamiltonian vector fields

Let `σ` be a two-form on a manifold `M`. A vector field `X` is Hamiltonian for `σ` when
`ι_X σ = df` for a function `f` (`TauCeti.SmoothTwoForm.IsHamiltonianVectorField`). For a closed
`σ` and a symplectic vector field `X`, one whose contraction `ι_X σ` is closed, this says that the
de Rham class `[ι_X σ]` vanishes. This file computes velocity fields `X_t = (∂ₜ φ_t) ∘ φ_t⁻¹` of
diffeotopies (`TauCeti.Diffeotopy.velocity`) modulo such fields, the computations by which an
isotopy is corrected to a Hamiltonian isotopy in the proof that symplectic isotopies of zero flux
are homotopic to Hamiltonian isotopies.

* **Pushforward by a diffeomorphism isotopic to the identity.** If the final diffeomorphism `φ₁`
  of a smooth diffeotopy preserves `σ` and `Y` is a smooth symplectic vector field, then the
  pushforward `(φ₁)_* Y` differs from `Y` by a Hamiltonian vector field of a smooth function
  (`TauCeti.Diffeotopy.exists_eval₂_mfderiv_final_eq_add`). Indeed
  `ι_((φ₁)_* Y) σ = (φ₁⁻¹)^* ι_Y σ`, and pullback along `φ₁⁻¹`, the final diffeomorphism of the
  inverse diffeotopy, is the identity on de Rham cohomology
  (`TauCeti.Diffeotopy.mpullback_final_sub_mem_exactForms`).
* **Composites.** By the product velocity identity `X_(ψ φ) = X_ψ + (ψ_t)_* X_φ`
  (`TauCeti.Diffeotopy.velocity_trans`), if `ψ_t` preserves `σ`, `X_φ - Z` is Hamiltonian and
  `(ψ_t)_* Z - Z` is Hamiltonian, then so is `X_(ψ φ) - X_ψ - Z`
  (`TauCeti.Diffeotopy.isHamiltonianVectorField_velocity_trans_sub_sub`).
* **Corrections.** If `ψ_t` preserves `σ` and `X_φ - X_ψ` is Hamiltonian for `f`, then the
  velocity field of the corrected isotopy `ψ_t⁻¹ ∘ φ_t` is Hamiltonian for `f ∘ ψ_t`
  (`TauCeti.Diffeotopy.isHamiltonianVectorField_velocity_trans_symm`), since it is
  `(ψ_t⁻¹)_* (X_φ - X_ψ)`.

These statements are pointwise in the time `t`; nothing is claimed about the dependence of the
Hamiltonians on `t`.

## Main results

* `TauCeti.Diffeotopy.exists_eval₂_mfderiv_final_eq_add`: `(φ₁)_* Y - Y` is Hamiltonian.
* `TauCeti.Diffeotopy.isHamiltonianVectorField_velocity_trans_sub_sub`: velocity fields of
  composites modulo Hamiltonian vector fields.
* `TauCeti.Diffeotopy.isHamiltonianVectorField_velocity_trans_symm`: the velocity field of
  `ψ_t⁻¹ ∘ φ_t` is Hamiltonian when `X_φ - X_ψ` is.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2 (the proof of Theorem 10.2.5).
* Augustin Banyaga, *The Structure of Classical Diffeomorphism Groups*, Kluwer, 1997,
  Section 3.1.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

namespace Diffeotopy

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M}

/-- **Pushforward by a symplectomorphism isotopic to the identity.** If the final diffeomorphism
`φ₁` of a smooth diffeotopy preserves `σ` and `Y` is a smooth symplectic vector field, then the
pushforward `(φ₁)_* Y` differs from `Y` by the Hamiltonian vector field of a smooth function `f`:
`σ(dφ₁ (Y z), v) = σ(Y (φ₁ z), v) + df(v)` for every tangent vector `v` at `φ₁ z`. -/
theorem exists_eval₂_mfderiv_final_eq_add (Φ : Diffeotopy I ∞ M)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer σ)
    {Y : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯} (hY : Y ∈ σ.symplecticVectorFields) :
    ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ f ∧ ∀ (z : M) (v : TangentSpace I (Φ.final z)),
      SmoothBundleForm.eval₂ σ (Φ.final z) (mfderiv I I Φ.final z (Y z)) v =
        SmoothBundleForm.eval₂ σ (Φ.final z) (Y (Φ.final z)) v +
          mvfderiv I f (Φ.final z) v := by
  have hβ : σ.interiorₗ Y ∈ closedForms I M 1 := by
    rw [mem_closedForms, SmoothTwoForm.coe_interiorₗ]
    exact SmoothTwoForm.mem_symplecticVectorFields_iff.1 hY
  -- Pullback along `φ₁⁻¹`, the final map of the inverse diffeotopy, changes `ι_Y σ` by `df`.
  have hex := Φ.symm.mpullback_final_sub_mem_exactForms ⟨σ.interiorₗ Y, hβ⟩
  rw [final_symm] at hex
  obtain ⟨f, hf, hdf⟩ := exists_contMDiff_mextDeriv_eq_of_mem_exactForms I hex
  refine ⟨f, hf, fun z v ↦ ?_⟩
  -- Evaluating `df = (φ₁⁻¹)^* ι_Y σ - ι_Y σ` at `φ₁ z` on `v`.
  have h := congrArg (fun (β : RoughForm I M ℝ 1) ↦ β (Φ.final z) ![v]) hdf
  simp only [mextDeriv_ofFunction, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
    Submodule.coe_sub, Pi.sub_apply, ContinuousAlternatingMap.sub_apply,
    SmoothForm.coe_mpullback, mpullback_apply, SmoothTwoForm.coe_interiorₗ,
    RoughForm.interior_apply, Matrix.cons_val_zero] at h
  -- The pulled-back term is `σ(Y z, v')` at `φ₁⁻¹ (φ₁ z) = z`, for `v' = d(φ₁⁻¹) v`; pushing both
  -- vectors forward by `dφ₁`, which preserves `σ`, gives `σ(dφ₁ (Y z), v)`.
  set v' := mfderiv I I Φ.final.symm (Φ.final z) v
  have hvec : (fun i ↦ mfderiv I I Φ.final.symm (Φ.final z) (![v] i)) = ![v'] := by
    funext i
    fin_cases i
    rfl
  rw [hvec] at h
  have hpt : (σ : RoughForm I M ℝ 2) (Φ.final.symm (Φ.final z))
      ![Y (Φ.final.symm (Φ.final z)), v'] = SmoothBundleForm.eval₂ σ z (Y z) v' :=
    (congrArg (fun w : M ↦ (σ : RoughForm I M ℝ 2) w ![(Y w : E), (v' : E)])
      (Φ.final.symm_apply_apply z)).trans (SmoothBundleForm.eval₂_apply σ z (Y z) v').symm
  rw [SmoothForm.eval₂_mfderiv_left_of_mem_diffeomorphStabilizer hΦ z (Y z) v, ← hpt,
    SmoothBundleForm.eval₂_apply, h]
  ring

/-- **Velocity fields of composites modulo Hamiltonian vector fields.** Let `ψ_t` preserve `σ` at
time `t`, and let `Z` be a vector field whose pushforward `(ψ_t)_* Z` differs from `Z` by the
Hamiltonian vector field of `g`. If `X_φ - Z` is the Hamiltonian vector field of `f` at time `t`,
then `X_(ψ φ) - X_ψ - Z` is the Hamiltonian vector field of `f ∘ ψ_t⁻¹ + g` for the composite
diffeotopy `ψ_t ∘ φ_t`. -/
theorem isHamiltonianVectorField_velocity_trans_sub_sub (Φ Ψ : Diffeotopy I ∞ M) {t : unitInterval}
    (hΨ : Ψ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ) {Z : (x : M) → TangentSpace I x}
    {f g : M → ℝ} (hf : MDifferentiable I 𝓘(ℝ) f) (hg : MDifferentiable I 𝓘(ℝ) g)
    (hΦ : σ.IsHamiltonianVectorField f fun x ↦ Φ.velocity t x - Z x)
    (hZ : ∀ (z : M) (v : TangentSpace I (Ψ.timeSlice t z)),
      SmoothBundleForm.eval₂ σ (Ψ.timeSlice t z) (mfderiv I I (Ψ.timeSlice t) z (Z z)) v =
        SmoothBundleForm.eval₂ σ (Ψ.timeSlice t z) (Z (Ψ.timeSlice t z)) v +
          mvfderiv I g (Ψ.timeSlice t z) v) :
    σ.IsHamiltonianVectorField (fun x ↦ f ((Ψ.timeSlice t).symm x) + g x)
      fun x ↦ (Φ.trans Ψ).velocity t x - Ψ.velocity t x - Z x := by
  have hΨ' : (Ψ.timeSlice t).symm ∈ SmoothForm.diffeomorphStabilizer σ := by
    rw [← Diffeomorph.inv_def]
    exact (SmoothForm.diffeomorphStabilizer σ).inv_mem hΨ
  -- The pushforward `P = (ψ_t)_* (X_φ - Z)` of the Hamiltonian vector field of `f` is Hamiltonian
  -- for `f ∘ ψ_t⁻¹`.
  obtain ⟨P, hP⟩ : ∃ P : (x : M) → TangentSpace I x, P = fun x ↦
      mfderiv I I (Ψ.timeSlice t) ((Ψ.timeSlice t).symm x)
        (Φ.velocity t ((Ψ.timeSlice t).symm x) - Z ((Ψ.timeSlice t).symm x)) := ⟨_, rfl⟩
  have h₁ := hΦ.mpullback (X := P) (Ψ.timeSlice t).symm.contMDiff (fun _ ↦ hf _) fun x ↦ by
    rw [hP]
    exact (Ψ.timeSlice t).symm.mfderiv_apply_mfderiv_symm_apply (by simp) x _
  rw [SmoothForm.mem_diffeomorphStabilizer.1 hΨ'] at h₁
  have hPz : ∀ z, P (Ψ.timeSlice t z) =
      mfderiv I I (Ψ.timeSlice t) z (Φ.velocity t z - Z z) := fun z ↦ by
    subst hP
    exact congrArg (fun y ↦ (mfderiv I I (Ψ.timeSlice t) y (Φ.velocity t y - Z y) : E))
      ((Ψ.timeSlice t).symm_apply_apply z)
  -- By the product velocity identity, the remainder is `(ψ_t)_* Z - Z`, Hamiltonian for `g`.
  have hrest : ∀ z, ((fun x ↦ (Φ.trans Ψ).velocity t x - Ψ.velocity t x - Z x) - P)
      (Ψ.timeSlice t z) = mfderiv I I (Ψ.timeSlice t) z (Z z) - Z (Ψ.timeSlice t z) := fun z ↦ by
    rw [Pi.sub_apply, hPz, Φ.velocity_trans (by simp) Ψ t z, map_sub]
    abel
  have h₂ : σ.IsHamiltonianVectorField g
      ((fun x ↦ (Φ.trans Ψ).velocity t x - Ψ.velocity t x - Z x) - P) :=
    SmoothTwoForm.isHamiltonianVectorField_iff.2 fun x v ↦ by
      obtain ⟨z, rfl⟩ : ∃ z, Ψ.timeSlice t z = x :=
        ⟨(Ψ.timeSlice t).symm x, (Ψ.timeSlice t).apply_symm_apply x⟩
      rw [hrest, SmoothBundleForm.eval₂_sub_left, hZ z v, add_sub_cancel_left]
  have hsum := h₁.add h₂ (hf.comp ((Ψ.timeSlice t).symm.mdifferentiable (by simp))) hg
  rwa [add_sub_cancel] at hsum

/-- **The velocity field of a corrected isotopy.** If `ψ_t` preserves `σ` and the difference
`X_φ - X_ψ` of the velocity fields of two diffeotopies at time `t` is the Hamiltonian vector field
of a differentiable function `f`, then the velocity field of the corrected diffeotopy
`ψ_t⁻¹ ∘ φ_t` at time `t`, which is `(ψ_t⁻¹)_* (X_φ - X_ψ)`, is the Hamiltonian vector field of
`f ∘ ψ_t`. -/
theorem isHamiltonianVectorField_velocity_trans_symm (Φ Ψ : Diffeotopy I ∞ M) {t : unitInterval}
    (hΨ : Ψ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ) {f : M → ℝ}
    (hf : MDifferentiable I 𝓘(ℝ) f)
    (h : σ.IsHamiltonianVectorField f fun x ↦ Φ.velocity t x - Ψ.velocity t x) :
    σ.IsHamiltonianVectorField (f ∘ Ψ.timeSlice t) ((Φ.trans Ψ.symm).velocity t) := by
  have h' := h.mpullback (Ψ.timeSlice t).contMDiff (fun _ ↦ hf _)
    (Φ.mfderiv_timeSlice_velocity_trans_symm (by simp) Ψ t)
  rwa [SmoothForm.mem_diffeomorphStabilizer.1 hΨ] at h'

end Diffeotopy

end TauCeti
