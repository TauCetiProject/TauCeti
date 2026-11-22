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

/-- The value of a two-form at a point, on vectors of the model space, depends only on the point. -/
private theorem eval₂_congr_point {p q : M} (h : p = q) (a b : E) :
    SmoothBundleForm.eval₂ σ p a b = SmoothBundleForm.eval₂ σ q a b := by
  subst h
  rfl

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
  calc SmoothBundleForm.eval₂ σ (Φ.final z) (mfderiv I I Φ.final z (Y z)) v
      = SmoothBundleForm.eval₂ σ (Φ.final z) (mfderiv I I Φ.final z (Y z))
          (mfderiv I I Φ.final z v') :=
        congrArg _ (Φ.final.mfderiv_apply_mfderiv_symm_apply (by simp) z v).symm
    _ = SmoothBundleForm.eval₂ σ z (Y z) v' :=
        SmoothForm.eval₂_mfderiv_of_mem_diffeomorphStabilizer hΦ z (Y z) v'
    _ = _ := by
      rw [← hpt, SmoothBundleForm.eval₂_apply, h]
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
  refine SmoothTwoForm.isHamiltonianVectorField_iff.2 fun x v ↦ ?_
  obtain ⟨z, rfl⟩ : ∃ z, Ψ.timeSlice t z = x :=
    ⟨(Ψ.timeSlice t).symm x, (Ψ.timeSlice t).apply_symm_apply x⟩
  -- By the product velocity identity, the field at `ψ_t z` is `dψ_t (X_φ z) - Z (ψ_t z)`.
  have hvel : (Φ.trans Ψ).velocity t (Ψ.timeSlice t z) - Ψ.velocity t (Ψ.timeSlice t z) -
      Z (Ψ.timeSlice t z) =
        mfderiv I I (Ψ.timeSlice t) z (Φ.velocity t z) - Z (Ψ.timeSlice t z) := by
    rw [Φ.velocity_trans (by simp) Ψ t z, add_sub_cancel_left]
  -- Write `v = dψ_t v'`, so that both vectors at `ψ_t z` are pushed forward from `z`.
  set v' := mfderiv I I (Ψ.timeSlice t).symm (Ψ.timeSlice t z) v
  have hv : mfderiv I I (Ψ.timeSlice t) z v' = v :=
    (Ψ.timeSlice t).mfderiv_apply_mfderiv_symm_apply (by simp) z v
  -- The derivative of `f ∘ ψ_t⁻¹` at `ψ_t z` is `df_z ∘ d(ψ_t⁻¹)`.
  have hcomp : mvfderiv I (f ∘ (Ψ.timeSlice t).symm) (Ψ.timeSlice t z) v = mvfderiv I f z v' :=
    mvfderiv_comp_apply_of_eq (Ψ.timeSlice t z) (hf z)
      ((Ψ.timeSlice t).symm.mdifferentiable (by simp) _) ((Ψ.timeSlice t).symm_apply_apply z) v
  have hsum : mvfderiv I (fun x ↦ f ((Ψ.timeSlice t).symm x) + g x) (Ψ.timeSlice t z) v =
      mvfderiv I f z v' + mvfderiv I g (Ψ.timeSlice t z) v := by
    rw [← hcomp]
    exact congrArg (· v) (mvfderiv_add (g := f ∘ (Ψ.timeSlice t).symm) (g' := g)
      ((hf _).comp _ ((Ψ.timeSlice t).symm.mdifferentiable (by simp) _)) (hg _))
  -- `σ(X_φ z - Z z, v') = df(v')` at `z`, and `ψ_t` carries the values at `z` to `ψ_t z`.
  have hX := (SmoothBundleForm.eval₂_sub_left σ z _ _ _).symm.trans
    (SmoothTwoForm.isHamiltonianVectorField_iff.1 hΦ z v')
  have h₁ := SmoothForm.eval₂_mfderiv_of_mem_diffeomorphStabilizer hΨ z (Φ.velocity t z) v'
  have h₂ := SmoothForm.eval₂_mfderiv_of_mem_diffeomorphStabilizer hΨ z (Z z) v'
  rw [hv] at h₁ h₂
  rw [hvel, hsum, SmoothBundleForm.eval₂_sub_left, h₁]
  linarith [hZ z v]

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
  refine SmoothTwoForm.isHamiltonianVectorField_iff.2 fun x v ↦ ?_
  obtain ⟨w, rfl⟩ : ∃ w, Ψ.symm (t, w) = x := ⟨Ψ (t, x), Ψ.symm_apply_apply_mk t x⟩
  -- By the product velocity identity, the field at `ψ_t⁻¹ w` is `X_(ψ⁻¹) + (ψ_t⁻¹)_* X_φ`.
  have hvt := Φ.velocity_trans (by simp) Ψ.symm t w
  rw [timeSlice_apply] at hvt
  -- `dψ_t` sends `X_(ψ⁻¹)` to `-X_ψ w` and undoes `d(ψ_t⁻¹)`.
  have ha := Ψ.mfderiv_timeSlice_mfderiv_cylinderMap_symm (by simp) t w
  rw [← Ψ.symm.velocity_apply] at ha
  have hb : mfderiv I I (Ψ.timeSlice t) (Ψ.symm (t, w))
      (mfderiv I I (Ψ.symm.timeSlice t) w (Φ.velocity t w)) = Φ.velocity t w :=
    (congrArg (mfderiv I I (Ψ.timeSlice t) (Ψ.symm (t, w)))
      (Ψ.symm.mfderiv_cylinderMap_inl (by simp) (w, t) (Φ.velocity t w)).symm).trans
      (Ψ.mfderiv_timeSlice_mfderiv_cylinderMap_symm_inl (by simp) t w (Φ.velocity t w))
  have hpush : mfderiv I I (Ψ.timeSlice t) (Ψ.symm (t, w))
      ((Φ.trans Ψ.symm).velocity t (Ψ.symm (t, w))) = (Φ.velocity t w - Ψ.velocity t w : E) := by
    rw [hvt, map_add]
    exact (congrArg₂ (· + ·) ha hb).trans (neg_add_eq_sub _ _)
  have hy : Ψ.timeSlice t (Ψ.symm (t, w)) = w := by
    rw [timeSlice_apply]
    exact Ψ.apply_mk_symm_apply t w
  calc SmoothBundleForm.eval₂ σ (Ψ.symm (t, w)) ((Φ.trans Ψ.symm).velocity t (Ψ.symm (t, w))) v
      = SmoothBundleForm.eval₂ σ (Ψ.timeSlice t (Ψ.symm (t, w)))
          (mfderiv I I (Ψ.timeSlice t) (Ψ.symm (t, w))
            ((Φ.trans Ψ.symm).velocity t (Ψ.symm (t, w))))
          (mfderiv I I (Ψ.timeSlice t) (Ψ.symm (t, w)) v) :=
        (SmoothForm.eval₂_mfderiv_of_mem_diffeomorphStabilizer hΨ _ _ v).symm
    _ = SmoothBundleForm.eval₂ σ w (Φ.velocity t w - Ψ.velocity t w)
          (mfderiv I I (Ψ.timeSlice t) (Ψ.symm (t, w)) v) := by
        rw [hpush]
        exact eval₂_congr_point hy _ _
    _ = mvfderiv I f w (mfderiv I I (Ψ.timeSlice t) (Ψ.symm (t, w)) v) :=
        SmoothTwoForm.isHamiltonianVectorField_iff.1 h w _
    _ = mvfderiv I (f ∘ Ψ.timeSlice t) (Ψ.symm (t, w)) v :=
        (mvfderiv_comp_apply_of_eq _ (hf w) ((Ψ.timeSlice t).mdifferentiable (by simp) _) hy
          v).symm

end Diffeotopy

end TauCeti
