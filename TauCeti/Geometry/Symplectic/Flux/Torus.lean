/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Torus
public import TauCeti.Geometry.Manifold.DeRham.Torus
public import TauCeti.Geometry.Symplectic.Flux

/-!
# The flux of the translations of a torus

For a finite family of positive periods `p i`, let `Tⁿ = ∀ i, AddCircle (p i)` be the torus with
coordinate time forms `dt_i` (`TauCeti.torusTimeForm p i`), and let `φ_t (x) = x + [t v]` be the
translation diffeotopy along a real vector `v` (`TauCeti.torusTranslationDiffeotopy p v`). Its
velocity is the constant field `v` and each `φ_t` has derivative the identity. So for a two-form
`σ` with constant coefficients `β` in the product charts, each `φ_t` preserves `σ`, and the flux
form `∫₀¹ φ_t^* (ι_v σ) dt` is the constant one-form `ι_v β = β (v, ·)`
(`TauCeti.fluxForm_torusTranslationDiffeotopy_apply`).

On the two-torus with the area form `A dt_0 ∧ dt_1` this gives

`Flux(φ) = A (v 0 [dt_1] - v 1 [dt_0])` in `H¹_dR(T²)`

(`TauCeti.flux_torusTranslationDiffeotopy_smul_torusVolumeForm`). With unit periods,
coordinates `(x, y)` and `v = a ∂_x + b ∂_y`, this is `A (a [dy] - b [dx])`: the translation in the
`x`-direction has flux `A [dy]` and that in the `y`-direction has flux `-A [dx]`. The diffeotopy is
a loop exactly when `v` lies in the period lattice
(`TauCeti.final_torusTranslationDiffeotopy_eq_refl_iff`), and for `A ≠ 0` its flux vanishes only
when `v = 0`, since `[dt_0]` and `[dt_1]` are linearly independent. Integrated around the two
coordinate circles, the flux form has periods `-A v 1 p 0` and `A v 0 p 1`
(`TauCeti.pathIntegral_fluxForm_torusTranslationDiffeotopy_smul_torusVolumeForm_update`); for unit
periods and integer `v` these are integer multiples of `A`. So the fluxes of the translation loops
of the unit torus are exactly the classes `A (m [dx] + n [dy])` with `m, n ∈ ℤ`. For arbitrary
periods, every class `A (m p_1 [dt_0] + n p_0 [dt_1])` with `m, n ∈ ℤ` is the flux of a translation
loop all of whose maps preserve the area form
(`TauCeti.exists_final_eq_refl_and_flux_smul_torusVolumeForm_eq`). These classes are the total area
`A p_0 p_1` times the integer combinations of the classes `[dt_i / p_i]`, which integrate to `1`
around the `i`-th coordinate circle and to `0` around the other.

## Main results

* `TauCeti.fluxForm_torusTranslationDiffeotopy_apply`: for a constant-coefficient two-form `β`,
  the flux form of the translation along `v` is `β (v, ·)`.
* `TauCeti.timeSlice_torusTranslationDiffeotopy_mem_diffeomorphStabilizer`,
  `TauCeti.final_torusTranslationDiffeotopy_mem_diffeomorphStabilizer`: translations preserve
  constant-coefficient two-forms.
* `TauCeti.fluxForm_torusTranslationDiffeotopy_smul_torusVolumeForm`,
  `TauCeti.flux_torusTranslationDiffeotopy_smul_torusVolumeForm`: the flux form and the flux of a
  translation of the two-torus for the area form `A dt_0 ∧ dt_1`.
* `TauCeti.flux_torusTranslationDiffeotopy_smul_torusVolumeForm_eq_zero_iff`: this flux vanishes
  exactly when `A = 0` or `v = 0`.
* `TauCeti.pathIntegral_fluxForm_torusTranslationDiffeotopy_smul_torusVolumeForm_update`: its
  periods along the coordinate circles.
* `TauCeti.exists_final_eq_refl_and_flux_smul_torusVolumeForm_eq`: every class
  `A (m p_1 [dt_0] + n p_0 [dt_1])` with `m n : ℤ` is the flux of a loop of area-preserving
  diffeomorphisms based at the identity.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2 (the flux homomorphism, and the flux of the translations of
  the torus).
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti

variable {ι : Type*} [Fintype ι] (p : ι → ℝ) [∀ i, Fact (0 < p i)] (v : ι → ℝ)

section Constant

variable {σ : SmoothForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) ℝ 2}
  {β : (ι → ℝ) [⋀^Fin 2]→L[ℝ] ℝ}

/-- **The flux form of a translation.** For a two-form `σ` on the torus with constant coefficients
`β`, the flux form of the translation diffeotopy along `v` is the constant one-form `β (v, ·)`, the
contraction of `β` with `v`. -/
theorem fluxForm_torusTranslationDiffeotopy_apply
    (hσ : ∀ x, (σ.1 x : (ι → ℝ) [⋀^Fin 2]→L[ℝ] ℝ) = β) (x : ∀ i, AddCircle (p i)) :
    ((torusTranslationDiffeotopy p v).fluxForm σ).1 x = β.curryLeft v := by
  rw [Diffeotopy.fluxForm_apply]
  -- At every time the integrand is `β (v, ·)`: the velocity is `v`, the spatial derivative is the
  -- identity and `σ` has constant coefficients.
  simp only [mfderiv_cylinderMap_torusTranslationDiffeotopy_apply_one,
    mfderiv_cylinderMap_torusTranslationDiffeotopy_comp_inl, hσ]
  refine (intervalIntegral.integral_const (E := (ι → ℝ) [⋀^Fin 1]→L[ℝ] ℝ) (a := 0) (b := 1)
    ((β.curryLeft v).compContinuousLinearMap (ContinuousLinearMap.id ℝ (ι → ℝ)))).trans ?_
  rw [sub_zero, one_smul]
  -- Composing with the identity map changes nothing.
  ext w
  simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]

/-- Every time slice of a translation diffeotopy, a translation of the torus, preserves every
two-form with constant coefficients. -/
theorem timeSlice_torusTranslationDiffeotopy_mem_diffeomorphStabilizer
    (hσ : ∀ x, (σ.1 x : (ι → ℝ) [⋀^Fin 2]→L[ℝ] ℝ) = β) (t : unitInterval) :
    (torusTranslationDiffeotopy p v).timeSlice t ∈ SmoothForm.diffeomorphStabilizer σ := by
  have hslice : ⇑((torusTranslationDiffeotopy (n := ∞) p v).timeSlice t) =
      (· + fun i ↦ (((t : ℝ) * v i : ℝ) : AddCircle (p i))) :=
    funext fun x ↦ (Diffeotopy.timeSlice_apply _ t x).trans (torusTranslationDiffeotopy_apply p v _)
  refine SmoothForm.mem_diffeomorphStabilizer_iff_forall.2 fun x ↦
    ContinuousAlternatingMap.ext fun w ↦ ?_
  rw [TauCeti.mpullback_apply, hslice, AddCircle.mfderiv_pi_add_right]
  -- Both sides evaluate the constant coefficient `β` on `w`.
  exact (DFunLike.congr_fun (hσ _) _).trans (DFunLike.congr_fun (hσ x) w).symm

/-- The final diffeomorphism of a translation diffeotopy, a translation of the torus, preserves
every two-form with constant coefficients. -/
theorem final_torusTranslationDiffeotopy_mem_diffeomorphStabilizer
    (hσ : ∀ x, (σ.1 x : (ι → ℝ) [⋀^Fin 2]→L[ℝ] ℝ) = β) :
    (torusTranslationDiffeotopy p v).final ∈ SmoothForm.diffeomorphStabilizer σ := by
  rw [Diffeotopy.final_def]
  exact timeSlice_torusTranslationDiffeotopy_mem_diffeomorphStabilizer p v hσ 1

end Constant

section Area

variable (p : Fin 2 → ℝ) [∀ i, Fact (0 < p i)] (v : Fin 2 → ℝ) (A : ℝ)

/-- The area form `A dt_0 ∧ dt_1` of the two-torus has constant coefficients. -/
private theorem smul_torusVolumeForm_apply_eq (x : ∀ i, AddCircle (p i)) :
    ((A • torusVolumeForm p).1 x : (Fin 2 → ℝ) [⋀^Fin 2]→L[ℝ] ℝ) =
      (A • torusVolumeForm p).1 0 :=
  congrArg (A • ·) (torusVolumeForm_apply_eq_apply_zero p x)

/-- **The flux form of a translation of the two-torus.** For the area form `A dt_0 ∧ dt_1`, the
translation diffeotopy along `v` has the constant flux form `A (v 0 dt_1 - v 1 dt_0)`. -/
theorem fluxForm_torusTranslationDiffeotopy_smul_torusVolumeForm :
    (torusTranslationDiffeotopy p v).fluxForm (A • torusVolumeForm p) =
      A • (v 0 • torusTimeForm p 1 - v 1 • torusTimeForm p 0) := by
  refine Subtype.ext (funext fun x ↦ ?_)
  rw [fluxForm_torusTranslationDiffeotopy_apply p v (smul_torusVolumeForm_apply_eq p A) x]
  ext w
  refine (ContinuousAlternatingMap.curryLeft_apply_apply _ v w).trans ?_
  -- Both sides are `A` times a `2 × 2` determinant, read through the formulas for the volume form
  -- and for the coordinate time forms. These are instantiated at `w` explicitly, since the forms
  -- take values in tangent-space fibres where `simp` cannot apply them.
  have hL := congrArg (A • ·) (torusVolumeForm_apply p 0 (Matrix.vecCons v w))
  have hR := congrArg (A • ·) (congrArg₂ (fun a b : ℝ ↦ v 0 • a - v 1 • b)
    (torusTimeForm_apply p 1 x w) (torusTimeForm_apply p 0 x w))
  refine hL.trans (Eq.trans ?_ hR.symm)
  simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val, smul_eq_mul]
  ring

/-- The flux form `A (v 0 dt_1 - v 1 dt_0)` as a constant-coefficient combination of the coordinate
time forms. -/
private theorem smul_sub_eq_sum_smul_torusTimeForm :
    A • (v 0 • torusTimeForm p 1 - v 1 • torusTimeForm p 0) =
      ∑ j, ![-(A * v 1), A * v 0] j • torusTimeForm p j := by
  rw [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero]
  module

/-- **The periods of the flux form along the coordinate circles.** Along the `i`-th coordinate
circle through `x`, traversed from `[a]` to `[b]`, the flux form of the translation diffeotopy
along `v` for the area form `A dt_0 ∧ dt_1` integrates to `-A v 1 (b - a)` for `i = 0` and to
`A v 0 (b - a)` for `i = 1`. Over one circuit, `b - a = p i`. -/
theorem pathIntegral_fluxForm_torusTranslationDiffeotopy_smul_torusVolumeForm_update
    (x : ∀ i, AddCircle (p i)) (i : Fin 2) (a b : ℝ) :
    pathIntegral ((torusTranslationDiffeotopy p v).fluxForm (A • torusVolumeForm p)).1
        (fun t : ℝ ↦ Function.update x i (t : AddCircle (p i))) a b =
      ![-(A * v 1), A * v 0] i * (b - a) := by
  rw [fluxForm_torusTranslationDiffeotopy_smul_torusVolumeForm,
    smul_sub_eq_sum_smul_torusTimeForm, pathIntegral_sum_smul_torusTimeForm_update]

/-- **The flux of a translation of the two-torus.** For the area form `A dt_0 ∧ dt_1`, the
translation diffeotopy along `v` has flux `A (v 0 [dt_1] - v 1 [dt_0])` in `H¹_dR(T²)`. -/
theorem flux_torusTranslationDiffeotopy_smul_torusVolumeForm
    (h : (torusTranslationDiffeotopy p v).final ∈
      SmoothForm.diffeomorphStabilizer (A • torusVolumeForm p)) :
    (torusTranslationDiffeotopy p v).flux
        ⟨A • torusVolumeForm p, mem_closedForms_of_finrank_le _ (by simp) _⟩ h =
      A • (v 0 • deRhamCohomology.mk (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) 1
          (torusTimeClosedForm p 1) -
        v 1 • deRhamCohomology.mk (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) 1
          (torusTimeClosedForm p 0)) := by
  rw [Diffeotopy.flux_def, ← map_smul, ← map_smul, ← map_sub, ← map_smul]
  congr 1
  refine Subtype.ext ?_
  simp only [Submodule.coe_smul, Submodule.coe_sub, coe_torusTimeClosedForm]
  exact fluxForm_torusTranslationDiffeotopy_smul_torusVolumeForm p v A

/-- **Translations have nonzero flux.** For a nonzero area form `A dt_0 ∧ dt_1`, the translation
diffeotopy along `v` has zero flux only when `v = 0`: the classes `[dt_0]` and `[dt_1]` are
linearly independent. -/
theorem flux_torusTranslationDiffeotopy_smul_torusVolumeForm_eq_zero_iff
    (h : (torusTranslationDiffeotopy p v).final ∈
      SmoothForm.diffeomorphStabilizer (A • torusVolumeForm p)) :
    (torusTranslationDiffeotopy p v).flux
        ⟨A • torusVolumeForm p, mem_closedForms_of_finrank_le _ (by simp) _⟩ h = 0 ↔
      A = 0 ∨ v = 0 := by
  rw [Diffeotopy.flux_def, deRhamCohomology.mk_eq_zero_iff]
  simp only [fluxForm_torusTranslationDiffeotopy_smul_torusVolumeForm,
    smul_sub_eq_sum_smul_torusTimeForm, sum_smul_torusTimeForm_mem_exactForms_iff]
  constructor
  · intro h0
    have h₀ := congrFun h0 0
    have h₁ := congrFun h0 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, neg_eq_zero,
      mul_eq_zero] at h₀ h₁
    refine or_iff_not_imp_left.2 fun hA ↦ funext fun i ↦ ?_
    fin_cases i
    · exact h₁.resolve_left hA
    · exact h₀.resolve_left hA
  · rintro (rfl | rfl) <;> ext i <;> fin_cases i <;> simp

/-- **Integral translation loops realize the area lattice as fluxes.** On the two-torus with the
area form `A dt_0 ∧ dt_1`, for all integers `m` and `n` there is a loop of diffeomorphisms based at
the identity, all of whose maps preserve the area form, with flux `A (m p_1 [dt_0] + n p_0 [dt_1])`:
the translation diffeotopy along `(n p_0, -m p_1)`. These classes are the total area `A p_0 p_1`
times the integer combinations of the classes `[dt_i / p_i]` dual to the coordinate circles. -/
theorem exists_final_eq_refl_and_flux_smul_torusVolumeForm_eq (m n : ℤ) :
    ∃ (Φ : Diffeotopy (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) ∞ (∀ i, AddCircle (p i)))
      (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer (A • torusVolumeForm p)),
      (∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer (A • torusVolumeForm p)) ∧
      Φ.final = Diffeomorph.refl _ _ _ ∧
      Φ.flux ⟨A • torusVolumeForm p, mem_closedForms_of_finrank_le _ (by simp) _⟩ hΦ =
        A • ((m * p 1) • deRhamCohomology.mk (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) 1
            (torusTimeClosedForm p 0) +
          (n * p 0) • deRhamCohomology.mk (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) 1
            (torusTimeClosedForm p 1)) := by
  let v : Fin 2 → ℝ := ![n * p 0, -(m * p 1)]
  have hloop : ∀ i, v i ∈ AddSubgroup.zmultiples (p i) := by
    intro i
    fin_cases i
    · exact ⟨n, by simp [v]⟩
    · exact ⟨-m, by simp [v]⟩
  have hslice := timeSlice_torusTranslationDiffeotopy_mem_diffeomorphStabilizer p v
    (smul_torusVolumeForm_apply_eq p A)
  refine ⟨torusTranslationDiffeotopy p v, by rw [Diffeotopy.final_def]; exact hslice 1, hslice,
    (final_torusTranslationDiffeotopy_eq_refl_iff p v).2 hloop, ?_⟩
  rw [flux_torusTranslationDiffeotopy_smul_torusVolumeForm]
  simp only [v, Matrix.cons_val_zero, Matrix.cons_val_one, neg_smul, sub_neg_eq_add]
  rw [add_comm]

end Area

end TauCeti
