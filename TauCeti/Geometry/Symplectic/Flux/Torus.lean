/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Torus
public import TauCeti.Geometry.Manifold.DeRham.Torus
public import TauCeti.Geometry.Symplectic.Flux.Endpoint

/-!
# The flux of the translations and of the loops of a torus

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

Conversely, every loop of diffeomorphisms of the torus has the flux of a translation loop. A
diffeotopy `Φ` of `Tⁿ` whose final diffeomorphism is the identity has a common displacement `v` of
all points at time `1`, a vector of the period lattice, and its motion is homotopic with both time
ends fixed to that of the translation loop along `v`. By the homotopy invariance of the flux form,
the flux forms of `Φ` and of this translation loop differ by an exact form, for every closed
two-form
(`TauCeti.Diffeotopy.exists_fluxForm_torusTranslationDiffeotopy_sub_fluxForm_mem_exactForms`).
On the two-torus with the area form `A dt_0 ∧ dt_1` the flux of every loop is therefore
`A (m p_1 [dt_0] + n p_0 [dt_1])` for some integers `m` and `n`
(`TauCeti.Diffeotopy.exists_flux_smul_torusVolumeForm_eq`), whether or not its intermediate maps
preserve the area form. Together with the translation loops this determines the flux group
`Γ_σ` of the area form: it is exactly the lattice of these classes
(`TauCeti.mem_fluxGroup_smul_torusVolumeForm_iff`). For unit periods this lattice is
`A (ℤ [dt_0] + ℤ [dt_1])`, classically identified with `A H¹(T²; ℤ)`.

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
* `TauCeti.Diffeotopy.exists_fluxForm_torusTranslationDiffeotopy_sub_fluxForm_mem_exactForms`: a
  loop of the torus has the flux form of a translation loop up to an exact form.
* `TauCeti.Diffeotopy.exists_flux_smul_torusVolumeForm_eq`: the flux of a loop of the two-torus
  for the area form lies in the lattice above.
* `TauCeti.mem_fluxGroup_smul_torusVolumeForm_iff`: the flux group of the area form of the
  two-torus is that lattice.

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

section Loop

variable {p}

/-- **Loops of the torus have the flux forms of translation loops.** Let `Φ` be a diffeotopy of
the torus whose final diffeomorphism is the identity. Then there is a vector `v` of the period
lattice such that, for every closed two-form `σ`, the flux forms of `Φ` and of the translation
loop along `v` differ by an exact form. The vector `v` is the displacement of every point at time
`1`, and the motion of `Φ` is homotopic to that of the translation loop with both time ends
fixed. Neither diffeotopy needs to preserve `σ`. -/
theorem Diffeotopy.exists_fluxForm_torusTranslationDiffeotopy_sub_fluxForm_mem_exactForms
    (Φ : Diffeotopy (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) ∞ (∀ i, AddCircle (p i)))
    (hΦ : Φ.final = Diffeomorph.refl _ _ ∞) :
    ∃ v : ι → ℝ, (∀ i, v i ∈ AddSubgroup.zmultiples (p i)) ∧
      ∀ σ : SmoothForm (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) ℝ 2,
        σ.IsClosed → (torusTranslationDiffeotopy p v).fluxForm σ - Φ.fluxForm σ ∈
          exactForms (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) 1 := by
  obtain ⟨v, hv, G, hG, hG₀, hG₁, h₀, h₁⟩ :=
    Φ.exists_homotopy_cylinderMap_torusTranslationDiffeotopy hΦ
  refine ⟨v, hv, fun σ hσ ↦ Φ.fluxForm_sub_fluxForm_mem_exactForms hσ hG hG₀ hG₁ h₀ fun x s ↦ ?_⟩
  rw [h₁, hΦ, Diffeomorph.coe_refl, id]

end Loop

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

/-- **The flux of a loop of the two-torus is integral.** On the two-torus with the area form
`A dt_0 ∧ dt_1`, every diffeotopy whose final diffeomorphism is the identity has flux
`A (m p_1 [dt_0] + n p_0 [dt_1])` for some integers `m` and `n`: it is the flux of the translation
loop along its displacement at time `1`. The intermediate diffeomorphisms need not preserve the
area form. -/
theorem Diffeotopy.exists_flux_smul_torusVolumeForm_eq
    (Φ : Diffeotopy (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) ∞ (∀ i, AddCircle (p i)))
    (hΦ₁ : Φ.final = Diffeomorph.refl _ _ ∞)
    (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer (A • torusVolumeForm p)) :
    ∃ m n : ℤ, Φ.flux ⟨A • torusVolumeForm p, mem_closedForms_of_finrank_le _ (by simp) _⟩ hΦ =
      A • ((m * p 1) • deRhamCohomology.mk (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) 1
          (torusTimeClosedForm p 0) +
        (n * p 0) • deRhamCohomology.mk (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) 1
          (torusTimeClosedForm p 1)) := by
  obtain ⟨v, hv, hex⟩ :=
    Φ.exists_fluxForm_torusTranslationDiffeotopy_sub_fluxForm_mem_exactForms hΦ₁
  obtain ⟨k₀, hk₀⟩ := AddSubgroup.mem_zmultiples_iff.1 (hv 0)
  obtain ⟨k₁, hk₁⟩ := AddSubgroup.mem_zmultiples_iff.1 (hv 1)
  have hτ : (torusTranslationDiffeotopy p v).final ∈
      SmoothForm.diffeomorphStabilizer (A • torusVolumeForm p) :=
    final_torusTranslationDiffeotopy_mem_diffeomorphStabilizer p v
      (smul_torusVolumeForm_apply_eq p A)
  -- The two fluxes agree, since the flux forms differ by an exact form.
  have heq : Φ.flux ⟨A • torusVolumeForm p, mem_closedForms_of_finrank_le _ (by simp) _⟩ hΦ =
      (torusTranslationDiffeotopy p v).flux
        ⟨A • torusVolumeForm p, mem_closedForms_of_finrank_le _ (by simp) _⟩ hτ := by
    rw [← sub_eq_zero, Diffeotopy.flux_def, Diffeotopy.flux_def, ← map_sub,
      deRhamCohomology.mk_eq_zero_iff, Submodule.coe_sub, ← neg_mem_iff, neg_sub]
    exact hex _ ((SmoothForm.isClosed_def _).2 ((mem_closedForms _ _).1
      (mem_closedForms_of_finrank_le _ (by simp) _)))
  refine ⟨-k₁, k₀, ?_⟩
  rw [heq, flux_torusTranslationDiffeotopy_smul_torusVolumeForm, ← hk₀, ← hk₁]
  simp only [zsmul_eq_mul, Int.cast_neg, neg_mul, neg_smul]
  rw [add_comm, sub_eq_add_neg]

/-- **The flux group of the two-torus.** On the two-torus with the area form `A dt_0 ∧ dt_1`, the
flux group, the set of fluxes of loops of area-preserving diffeomorphisms based at the identity, is
the lattice of classes `A (m p_1 [dt_0] + n p_0 [dt_1])` with `m n : ℤ`. For unit periods this is
`A (ℤ [dt_0] + ℤ [dt_1])`, classically identified with `A H¹(T²; ℤ)`. -/
theorem mem_fluxGroup_smul_torusVolumeForm_iff
    {c : deRhamCohomology (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) 1} :
    c ∈ fluxGroup ⟨A • torusVolumeForm p, mem_closedForms_of_finrank_le _ (by simp) _⟩ ↔
      ∃ m n : ℤ, c =
        A • ((m * p 1) • deRhamCohomology.mk (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) 1
            (torusTimeClosedForm p 0) +
          (n * p 0) • deRhamCohomology.mk (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) 1
            (torusTimeClosedForm p 1)) := by
  rw [mem_fluxGroup]
  refine ⟨fun ⟨Φ, _, hΦ₁, hc⟩ ↦ hc ▸ Φ.exists_flux_smul_torusVolumeForm_eq p A hΦ₁ _,
    fun ⟨m, n, hc⟩ ↦ ?_⟩
  obtain ⟨Φ, _, hslice, hΦ₁, hflux⟩ :=
    exists_final_eq_refl_and_flux_smul_torusVolumeForm_eq p A m n
  exact ⟨Φ, hslice, hΦ₁, hflux.trans hc.symm⟩

end Area

end TauCeti
