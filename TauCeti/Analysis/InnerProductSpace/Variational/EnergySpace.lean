/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LaxMilgram

/-!
# The energy space of a coercive Hermitian form

Let `a : V →L⋆[𝕜] V →L[𝕜] 𝕜` be a bounded sesquilinear form on a normed space `V` over
`𝕜 = ℝ` or `ℂ`, conjugate linear in its first argument, which is Hermitian,
`a u v = star (a v u)`, and coercive, `c * ‖u‖ ^ 2 ≤ re (a u u)` for some `c > 0`. Such a form
is an inner product on `V`. Its norm `√(re (a u u))` is equivalent to the norm of `V`, by

`c * ‖u‖ ^ 2 ≤ re (a u u) ≤ ‖a‖ * ‖u‖ ^ 2`.

The **energy space** of `a` is `V` equipped with this inner product. Variational spectral theory
works in it: the eigenvectors of a form are orthogonal for its energy inner product, and expansions
in them converge in the energy norm. Since the two norms are equivalent, the energy space has the
same topology as `V`, and it is complete when `V` is.

## Main declarations

* `TauCeti.CoerciveHermitianForm 𝕜 V`: a bounded Hermitian sesquilinear form on `V` with a
  positive coercivity constant. The constant is a proposition, so the structure is determined
  by its form (`TauCeti.CoerciveHermitianForm.ext`).
* `TauCeti.CoerciveHermitianForm.EnergySpace a`: a copy of `V` with the inner product `a`, a
  `NormedAddCommGroup` and an `InnerProductSpace 𝕜`, complete when `V` is.
* `TauCeti.CoerciveHermitianForm.toEnergySpace a : V ≃L[𝕜] a.EnergySpace`: the identity of `V`,
  with `⟪a.toEnergySpace u, a.toEnergySpace v⟫_𝕜 = a u v`
  (`TauCeti.CoerciveHermitianForm.inner_toEnergySpace`) and the two-sided norm bounds
  `TauCeti.CoerciveHermitianForm.sqrt_mul_norm_le_norm_toEnergySpace` and
  `TauCeti.CoerciveHermitianForm.norm_toEnergySpace_le`.
* `TauCeti.CoerciveHermitianForm.toEnergySpace_solutionOfFunctional`: when `V` is a Hilbert
  space, the Lax–Milgram solution of `a u v = ℓ v` is the Riesz representative of `ℓ` in the
  energy space.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Springer,
  2011, §5.3 (the Lax–Milgram theorem; for a symmetric form, `a` is an equivalent inner product
  and the theorem reduces to the Riesz–Fréchet representation).
* J. K. Hunter, *Notes on Partial Differential Equations*, Chapter 4, Theorem 4.20.
-/

public section

noncomputable section

open RCLike
open scoped InnerProductSpace

namespace TauCeti

/-- A **coercive Hermitian form** on a normed space `V` over `𝕜`: a bounded sesquilinear form
`form : V →L⋆[𝕜] V →L[𝕜] 𝕜`, conjugate linear in its first argument, with
`form u v = star (form v u)` and `c * ‖u‖ ^ 2 ≤ re (form u u)` for some `c > 0`. The coercivity
constant is only asserted to exist, so a coercive Hermitian form is determined by its form. -/
@[ext]
structure CoerciveHermitianForm (𝕜 V : Type*) [RCLike 𝕜] [NormedAddCommGroup V]
    [NormedSpace 𝕜 V] where
  /-- The underlying bounded sesquilinear form. -/
  form : V →L⋆[𝕜] V →L[𝕜] 𝕜
  /-- The form is Hermitian. -/
  form_apply_eq_star : ∀ u v, form u v = star (form v u)
  /-- The form is coercive, with some positive constant. -/
  exists_coercive : ∃ c > 0, ∀ u, c * ‖u‖ ^ 2 ≤ re (form u u)

namespace CoerciveHermitianForm

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  (a : CoerciveHermitianForm 𝕜 V)

/-- The diagonal real part of a coercive Hermitian form is nonnegative. -/
theorem re_form_apply_self_nonneg (u : V) : 0 ≤ re (a.form u u) := by
  obtain ⟨c, hc, hcoer⟩ := a.exists_coercive
  exact InnerProductSpace.re_apply_self_nonneg_of_coercive a.form hc.le hcoer u

/-- A coercive Hermitian form vanishes on the diagonal only at `0`. -/
@[simp]
theorem form_apply_self_eq_zero_iff {u : V} : a.form u u = 0 ↔ u = 0 := by
  refine ⟨fun hu ↦ ?_, fun hu ↦ by simp [hu]⟩
  obtain ⟨c, hc, hcoer⟩ := a.exists_coercive
  exact InnerProductSpace.eq_zero_of_re_apply_self_nonpos_of_coercive a.form hc hcoer
    (by simp [hu])

/-! ### The energy space -/

/-- The **energy space** of a coercive Hermitian form `a` on `V`: a copy of `V` whose inner
product is `a`. It is a `NormedAddCommGroup` and an `InnerProductSpace 𝕜`, complete when `V` is,
and `a.toEnergySpace` identifies it with `V`. -/
def EnergySpace (_a : CoerciveHermitianForm 𝕜 V) : Type _ := V

instance : AddCommGroup a.EnergySpace := inferInstanceAs (AddCommGroup V)

instance : Module 𝕜 a.EnergySpace := inferInstanceAs (Module 𝕜 V)

/-- The identity of `V`, as a linear equivalence onto the energy space. -/
private def toEnergySpaceₗ : V ≃ₗ[𝕜] a.EnergySpace := LinearEquiv.refl 𝕜 V

/-- The inner product core of the energy space: the form `a`, read on the underlying vectors of
`V`. -/
@[instance_reducible]
def innerProductCore : InnerProductSpace.Core 𝕜 a.EnergySpace where
  inner x y := a.form (a.toEnergySpaceₗ.symm x) (a.toEnergySpaceₗ.symm y)
  conj_inner_symm x y := by
    rw [starRingEnd_apply, ← a.form_apply_eq_star]
  re_inner_nonneg x := a.re_form_apply_self_nonneg _
  add_left x y z := by
    rw [map_add, map_add, add_apply]
  smul_left x y r := by
    rw [LinearEquiv.map_smul, map_smulₛₗ, smul_apply, smul_eq_mul]
  definite x hx := by
    simpa using hx

instance : NormedAddCommGroup a.EnergySpace := a.innerProductCore.toNormedAddCommGroup

instance : InnerProductSpace 𝕜 a.EnergySpace := InnerProductSpace.ofCore a.innerProductCore.toCore

/-- The inner product of the energy space is, by definition, the `inner` field of
`innerProductCore`. -/
private theorem inner_eq_form_toEnergySpaceₗ_symm (x y : a.EnergySpace) :
    ⟪x, y⟫_𝕜 = a.form (a.toEnergySpaceₗ.symm x) (a.toEnergySpaceₗ.symm y) :=
  (rfl)

private theorem inner_toEnergySpaceₗ (u v : V) :
    ⟪a.toEnergySpaceₗ u, a.toEnergySpaceₗ v⟫_𝕜 = a.form u v := by
  rw [inner_eq_form_toEnergySpaceₗ_symm, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply]

private theorem norm_toEnergySpaceₗ_sq (u : V) :
    ‖a.toEnergySpaceₗ u‖ ^ 2 = re (a.form u u) := by
  rw [@norm_sq_eq_re_inner 𝕜, inner_toEnergySpaceₗ]

private theorem norm_toEnergySpaceₗ_le (u : V) : ‖a.toEnergySpaceₗ u‖ ≤ √‖a.form‖ * ‖u‖ := by
  refine le_of_sq_le_sq ?_ (by positivity)
  rw [norm_toEnergySpaceₗ_sq, mul_pow, Real.sq_sqrt (norm_nonneg a.form)]
  calc re (a.form u u) ≤ ‖a.form u u‖ := re_le_norm _
    _ ≤ ‖a.form‖ * ‖u‖ * ‖u‖ := a.form.le_opNorm₂ u u
    _ = ‖a.form‖ * ‖u‖ ^ 2 := by ring

private theorem sqrt_mul_norm_le_norm_toEnergySpaceₗ {c : ℝ}
    (hcoer : ∀ u, c * ‖u‖ ^ 2 ≤ re (a.form u u)) (u : V) :
    √c * ‖u‖ ≤ ‖a.toEnergySpaceₗ u‖ := by
  rcases le_or_gt c 0 with hc | hc
  · rw [Real.sqrt_eq_zero'.mpr hc, zero_mul]
    exact norm_nonneg _
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  rw [norm_toEnergySpaceₗ_sq, mul_pow, Real.sq_sqrt hc.le]
  exact hcoer u

private theorem norm_toEnergySpaceₗ_symm_le {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ u, c * ‖u‖ ^ 2 ≤ re (a.form u u)) (x : a.EnergySpace) :
    ‖a.toEnergySpaceₗ.symm x‖ ≤ (√c)⁻¹ * ‖x‖ := by
  rw [le_inv_mul_iff₀ (Real.sqrt_pos.mpr hc)]
  simpa using a.sqrt_mul_norm_le_norm_toEnergySpaceₗ hcoer (a.toEnergySpaceₗ.symm x)

/-- The identity of `V`, as a continuous linear equivalence onto the energy space of `a`. It is
continuous in both directions because the energy norm is equivalent to the norm of `V`. -/
def toEnergySpace : V ≃L[𝕜] a.EnergySpace :=
  a.toEnergySpaceₗ.toContinuousLinearEquivOfBounds √‖a.form‖ (√a.exists_coercive.choose)⁻¹
    a.norm_toEnergySpaceₗ_le
    (a.norm_toEnergySpaceₗ_symm_le a.exists_coercive.choose_spec.1
      a.exists_coercive.choose_spec.2)

/-- The energy inner product of two vectors of `V` is the value of the form on them. -/
@[simp]
theorem inner_toEnergySpace (u v : V) :
    ⟪a.toEnergySpace u, a.toEnergySpace v⟫_𝕜 = a.form u v :=
  a.inner_toEnergySpaceₗ u v

/-- The inner product of the energy space, in terms of the underlying vectors of `V`. -/
theorem inner_eq_form (x y : a.EnergySpace) :
    ⟪x, y⟫_𝕜 = a.form (a.toEnergySpace.symm x) (a.toEnergySpace.symm y) := by
  rw [← inner_toEnergySpace, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply]

/-- The squared energy norm of `u` is the diagonal value `re (a u u)`. -/
theorem norm_toEnergySpace_sq (u : V) : ‖a.toEnergySpace u‖ ^ 2 = re (a.form u u) :=
  a.norm_toEnergySpaceₗ_sq u

/-- The energy norm of `u` is `√(re (a u u))`. -/
theorem norm_toEnergySpace (u : V) : ‖a.toEnergySpace u‖ = √(re (a.form u u)) := by
  rw [← norm_toEnergySpace_sq, Real.sqrt_sq (norm_nonneg _)]

/-- **Upper energy bound.** The energy norm is at most `√‖a‖` times the norm of `V`. -/
theorem norm_toEnergySpace_le (u : V) : ‖a.toEnergySpace u‖ ≤ √‖a.form‖ * ‖u‖ :=
  a.norm_toEnergySpaceₗ_le u

/-- **Lower energy bound.** If `c * ‖u‖ ^ 2 ≤ re (a u u)` for every `u`, then the energy norm is
at least `√c` times the norm of `V`. -/
theorem sqrt_mul_norm_le_norm_toEnergySpace {c : ℝ} (hcoer : ∀ u, c * ‖u‖ ^ 2 ≤ re (a.form u u))
    (u : V) : √c * ‖u‖ ≤ ‖a.toEnergySpace u‖ :=
  a.sqrt_mul_norm_le_norm_toEnergySpaceₗ hcoer u

/-- The operator norm of `a.toEnergySpace` is at most `√‖a‖`. -/
theorem opNorm_toEnergySpace_le : ‖(a.toEnergySpace : V →L[𝕜] a.EnergySpace)‖ ≤ √‖a.form‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) a.norm_toEnergySpace_le

/-- If `c * ‖u‖ ^ 2 ≤ re (a u u)` for every `u`, with `c > 0`, then the inverse of
`a.toEnergySpace` has operator norm at most `(√c)⁻¹`. -/
theorem opNorm_toEnergySpace_symm_le {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ u, c * ‖u‖ ^ 2 ≤ re (a.form u u)) :
    ‖(a.toEnergySpace.symm : a.EnergySpace →L[𝕜] V)‖ ≤ (√c)⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (a.norm_toEnergySpaceₗ_symm_le hc hcoer)

/-- The energy space of a coercive Hermitian form on a Banach space is a Hilbert space. -/
instance [CompleteSpace V] : CompleteSpace a.EnergySpace :=
  (completeSpace_congr (e := a.toEnergySpace.toEquiv) a.toEnergySpace.isUniformEmbedding).mp
    inferInstance

/-! ### Comparison with the Lax–Milgram solution map -/

section LaxMilgram

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
  (a : CoerciveHermitianForm 𝕜 V)

/-- The Fréchet–Riesz operator of a coercive Hermitian form on a Hilbert space is invertible. -/
theorem isUnit_continuousLinearMapOfBilin :
    IsUnit (InnerProductSpace.continuousLinearMapOfBilin a.form) :=
  have ⟨_, hc, hcoer⟩ := a.exists_coercive
  InnerProductSpace.isUnit_continuousLinearMapOfBilin_of_coercive a.form hc hcoer

/-- **The Lax–Milgram solution is a Riesz representative.** On a Hilbert space `V`, the solution
`u` of `a u v = ℓ v` for every `v` is, in the energy space, the Riesz representative of `ℓ`. -/
theorem toEnergySpace_solutionOfFunctional (ℓ : StrongDual 𝕜 V) :
    a.toEnergySpace
        (InnerProductSpace.solutionOfFunctional a.form a.isUnit_continuousLinearMapOfBilin ℓ) =
      (InnerProductSpace.toDual 𝕜 a.EnergySpace).symm
        (ℓ.comp (a.toEnergySpace.symm : a.EnergySpace →L[𝕜] V)) := by
  refine ext_inner_right 𝕜 fun x ↦ ?_
  rw [InnerProductSpace.toDual_symm_apply, ← a.toEnergySpace.apply_symm_apply x,
    inner_toEnergySpace, InnerProductSpace.apply_solutionOfFunctional_eq,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]

end LaxMilgram

end CoerciveHermitianForm

end TauCeti
