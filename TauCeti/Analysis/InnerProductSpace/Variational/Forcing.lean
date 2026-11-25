/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Variational.EnergySpace
public import TauCeti.Analysis.InnerProductSpace.Variational.Spectrum

/-!
# Forcing maps of a coercive Hermitian form

Let `a` be a coercive Hermitian form on a Banach space `V` over `𝕜 = ℝ` or `ℂ`
(`TauCeti.CoerciveHermitianForm`), conjugate linear in its first argument. For every continuous
linear functional `ℓ` on `V` the weak equation `a(u, v) = ℓ(v)` for all `v` has exactly one
solution `u = F ℓ`, the Riesz representative of `ℓ` in the energy space of `a`. The **dual-forcing
map** `F : StrongDual 𝕜 V →L⋆[𝕜] V` (`TauCeti.CoerciveHermitianForm.dualForcing`) is conjugate
linear, since `a` is conjugate linear in the slot where the solution sits, and
`‖F ℓ‖ ≤ c⁻¹ ‖ℓ‖` for every coercivity constant `c`.

For a continuous linear map `j : V → H` to an inner product space, the **`H`-forcing map**
`S : H →L[𝕜] V` (`TauCeti.CoerciveHermitianForm.hForcing`) solves `a(S h, v) = ⟪h, j v⟫`. It is
`F` applied to the functional `⟪h, j ·⟫`, which is conjugate linear in `h`, so `S` is linear, with
`‖S h‖ ≤ c⁻¹ ‖j‖ ‖h‖`. For a compact form pair and a shift `α ≥ ω`, these are the solution maps
`S_α` and `F_α` of the shifted form, made coercive by
`TauCeti.CoerciveHermitianForm.ofSemibounded`. At `𝕜 = ℝ` the `H`-forcing map is the Lax–Milgram
solution map `IsCoercive.formSolutionMap`
(`TauCeti.CoerciveHermitianForm.hForcing_eq_formSolutionMap`).

## Main declarations

* `TauCeti.CoerciveHermitianForm.dualForcing`, with `form_dualForcing_apply`,
  `eq_dualForcing_iff` and `norm_dualForcing_le`.
* `TauCeti.CoerciveHermitianForm.hForcing`, with `form_hForcing_apply`,
  `hForcing_apply_eq_dualForcing`, `eq_hForcing_iff` and `norm_hForcing_le`.
* `TauCeti.CoerciveHermitianForm.hForcing_eq_formSolutionMap`: the comparison at `𝕜 = ℝ`.

## References

* TauCetiRoadmap, `VariationalMethods/README.md`, §2.3.
-/

public section

noncomputable section

open RCLike
open scoped InnerProductSpace

namespace TauCeti

namespace CoerciveHermitianForm

variable {𝕜 V H : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (a : CoerciveHermitianForm 𝕜 V)

/-! ### The dual-forcing map -/

/-- The **dual-forcing map** `F : StrongDual 𝕜 V →L⋆[𝕜] V` of a coercive Hermitian form `a`:
`F ℓ` is the unique solution `u` of `a(u, v) = ℓ(v)` for every `v`, the Riesz representative of
`ℓ` in the energy space of `a`. It is conjugate linear. -/
def dualForcing : StrongDual 𝕜 V →L⋆[𝕜] V :=
  (a.toEnergySpace.symm : a.EnergySpace →L[𝕜] V).comp
    (((InnerProductSpace.toDual 𝕜 a.EnergySpace).symm.toContinuousLinearEquiv :
        StrongDual 𝕜 a.EnergySpace →SL[starRingEnd 𝕜] a.EnergySpace).comp
      ((ContinuousLinearMap.compL 𝕜 a.EnergySpace V 𝕜).flip
        (a.toEnergySpace.symm : a.EnergySpace →L[𝕜] V)))

theorem toEnergySpace_dualForcing (ℓ : StrongDual 𝕜 V) :
    a.toEnergySpace (a.dualForcing ℓ) = (InnerProductSpace.toDual 𝕜 a.EnergySpace).symm
      (ℓ.comp (a.toEnergySpace.symm : a.EnergySpace →L[𝕜] V)) := by
  simp [dualForcing]

/-- **The weak equation solved by the dual-forcing map**: `a(F ℓ, v) = ℓ(v)`. -/
@[simp]
theorem form_dualForcing_apply (ℓ : StrongDual 𝕜 V) (v : V) :
    a.form (a.dualForcing ℓ) v = ℓ v :=
  (a.toEnergySpace_eq_toDual_symm_iff ℓ _).1 (a.toEnergySpace_dualForcing ℓ) v

/-- **Uniqueness of the solution of the weak equation**: `u` solves `a(u, v) = ℓ(v)` for every `v`
exactly when `u = F ℓ`. -/
theorem eq_dualForcing_iff {ℓ : StrongDual 𝕜 V} {u : V} :
    u = a.dualForcing ℓ ↔ ∀ v, a.form u v = ℓ v := by
  refine ⟨fun h v ↦ h ▸ a.form_dualForcing_apply ℓ v, fun h ↦ a.toEnergySpace.injective ?_⟩
  rw [a.toEnergySpace_dualForcing, (a.toEnergySpace_eq_toDual_symm_iff ℓ u).2 h]

/-- **The bound on the dual-forcing map**: `‖F ℓ‖ ≤ c⁻¹ ‖ℓ‖` for every coercivity constant `c`
of `a`. -/
theorem norm_dualForcing_le {c : ℝ} (hc : 0 < c) (hcoer : ∀ u, c * ‖u‖ ^ 2 ≤ re (a.form u u))
    (ℓ : StrongDual 𝕜 V) : ‖a.dualForcing ℓ‖ ≤ c⁻¹ * ‖ℓ‖ := by
  set u := a.dualForcing ℓ
  have h : c * ‖u‖ ^ 2 ≤ ‖ℓ‖ * ‖u‖ := by
    calc c * ‖u‖ ^ 2 ≤ re (a.form u u) := hcoer u
      _ = re (ℓ u) := by rw [a.form_dualForcing_apply]
      _ ≤ ‖ℓ u‖ := re_le_norm _
      _ ≤ ‖ℓ‖ * ‖u‖ := ℓ.le_opNorm u
  rcases (norm_nonneg u).eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  rw [inv_mul_eq_div, le_div_iff₀ hc]
  nlinarith

/-! ### The `H`-forcing map -/

/-- The **`H`-forcing map** `S : H →L[𝕜] V` of a coercive Hermitian form `a` along
`j : V →L[𝕜] H`: `S h` is the unique solution `u` of `a(u, v) = ⟪h, j v⟫` for every `v`. -/
def hForcing (j : V →L[𝕜] H) : H →L[𝕜] V :=
  a.dualForcing.comp (((ContinuousLinearMap.compL 𝕜 V H 𝕜).flip j).comp (innerSL 𝕜) :
    H →L⋆[𝕜] StrongDual 𝕜 V)

/-- The `H`-forcing map is the dual-forcing map applied to the functional `⟪h, j ·⟫`. -/
theorem hForcing_apply_eq_dualForcing (j : V →L[𝕜] H) (h : H) :
    a.hForcing j h = a.dualForcing ((innerSL 𝕜 h).comp j) := by
  simp [hForcing]

/-- **The weak equation solved by the `H`-forcing map**: `a(S h, v) = ⟪h, j v⟫`. -/
@[simp]
theorem form_hForcing_apply (j : V →L[𝕜] H) (h : H) (v : V) :
    a.form (a.hForcing j h) v = ⟪h, j v⟫_𝕜 := by
  simp [hForcing_apply_eq_dualForcing]

/-- `u` solves `a(u, v) = ⟪h, j v⟫` for every `v` exactly when `u = S h`. -/
theorem eq_hForcing_iff (j : V →L[𝕜] H) {h : H} {u : V} :
    u = a.hForcing j h ↔ ∀ v, a.form u v = ⟪h, j v⟫_𝕜 := by
  simp [hForcing_apply_eq_dualForcing, eq_dualForcing_iff]

/-- **The bound on the `H`-forcing map**: `‖S h‖ ≤ c⁻¹ ‖j‖ ‖h‖` for every coercivity constant `c`
of `a`. -/
theorem norm_hForcing_le {c : ℝ} (hc : 0 < c) (hcoer : ∀ u, c * ‖u‖ ^ 2 ≤ re (a.form u u))
    (j : V →L[𝕜] H) (h : H) : ‖a.hForcing j h‖ ≤ c⁻¹ * ‖j‖ * ‖h‖ := by
  rw [hForcing_apply_eq_dualForcing, mul_assoc]
  refine (a.norm_dualForcing_le hc hcoer _).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  calc ‖(innerSL 𝕜 h).comp j‖ ≤ ‖innerSL 𝕜 h‖ * ‖j‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖h‖ * ‖j‖ := by rw [innerSL_apply_norm]
    _ = ‖j‖ * ‖h‖ := mul_comm _ _

/-! ### Comparison with the real Lax–Milgram solution map -/

/-- At `𝕜 = ℝ`, the `H`-forcing map of a coercive Hermitian form agrees with the Lax–Milgram
solution map `IsCoercive.formSolutionMap` of any coercive bilinear form with the same values. -/
theorem hForcing_eq_formSolutionMap {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a : CoerciveHermitianForm ℝ V) {B : V →L[ℝ] V →L[ℝ] ℝ} (hB : IsCoercive B)
    (hBa : ∀ u v, B u v = a.form u v) (j : V →L[ℝ] H) :
    a.hForcing j = hB.formSolutionMap j :=
  ContinuousLinearMap.ext fun h ↦ hB.eq_formSolutionMap j fun v ↦ by
    rw [hBa, form_hForcing_apply]

end CoerciveHermitianForm

end TauCeti
