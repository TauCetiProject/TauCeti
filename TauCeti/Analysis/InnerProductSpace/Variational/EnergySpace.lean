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

The **energy space** of `a` is `V` equipped with this inner product. It is the setting in which
variational spectral theory proves, under additional spectral hypotheses, that eigenvectors are
orthogonal for the energy inner product and that expansions in them converge in the energy norm.
Since the two norms are equivalent, the energy space has the same topology as `V`, and it is
complete when `V` is.

Formally, the form supplies an `InnerProductSpace.Core` on the type synonym, and Mathlib's
`InnerProductSpace.Core.toNormedAddCommGroup` and `InnerProductSpace.ofCore` supply its normed
group and inner product space instances.

## Main declarations

In the formulas below, `a` is a bundled `TauCeti.CoerciveHermitianForm` and `a.form` is its
underlying sesquilinear form.

* `TauCeti.CoerciveHermitianForm 𝕜 V`: a bounded Hermitian sesquilinear form on `V` together with
  the existence of a positive coercivity constant. The existence is a proposition and no
  particular constant is stored, so the structure is determined by its form
  (`TauCeti.CoerciveHermitianForm.ext`).
* `TauCeti.CoerciveHermitianForm.EnergySpace a`: a copy of `V` with the inner product `a.form`, a
  `NormedAddCommGroup` and an `InnerProductSpace 𝕜`, complete when `V` is.
* `TauCeti.CoerciveHermitianForm.toEnergySpace a : V ≃L[𝕜] a.EnergySpace`: the identity of `V`,
  with `⟪a.toEnergySpace u, a.toEnergySpace v⟫_𝕜 = a.form u v`
  (`TauCeti.CoerciveHermitianForm.inner_toEnergySpace`) and the two-sided norm bounds
  `TauCeti.CoerciveHermitianForm.sqrt_mul_norm_le_norm_toEnergySpace` and
  `TauCeti.CoerciveHermitianForm.norm_toEnergySpace_le`.
* `TauCeti.CoerciveHermitianForm.sqrt_mul_norm_toEnergySpace_le`: the energy norms of two
  coercive Hermitian forms on the same space bound each other.
* `TauCeti.CoerciveHermitianForm.toEnergySpace_eq_toDual_symm_iff`: on a Banach space, `u` solves
  `a.form u v = ℓ v` for every `v` exactly when `a.toEnergySpace u` is the Riesz representative,
  in the energy space, of `ℓ` pulled back along `a.toEnergySpace.symm`.
* `TauCeti.CoerciveHermitianForm.isUnit_continuousLinearMapOfBilin`: when `V` is a Hilbert
  space, the Fréchet–Riesz operator of `a.form` is invertible, so the Lax–Milgram solution maps
  of `a.form` are defined.

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

/-- The inner product core of the energy space: the form `a.form`, read on the underlying vectors
of `V`. It only builds the instances below; use `inner_toEnergySpace` and `inner_eq_form` to
compute the resulting inner product. -/
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

/-- The energy norm on `a.EnergySpace`, `x ↦ √(re (a.form x x))`, built from the inner product
core by Mathlib's `InnerProductSpace.Core.toNormedAddCommGroup`. Under `a.toEnergySpace`, this
norm is equivalent to the original norm on `V` and can coincide with it. -/
instance : NormedAddCommGroup a.EnergySpace := a.innerProductCore.toNormedAddCommGroup

/-- The inner product of `a.EnergySpace` is the form `a.form`, transported to the type synonym,
built from the inner product core by Mathlib's `InnerProductSpace.ofCore`. -/
instance : InnerProductSpace 𝕜 a.EnergySpace := InnerProductSpace.ofCore a.innerProductCore.toCore

/-- The energy norm of the image of `u` is, by definition, `√(re (a.form u u))`. -/
private theorem norm_toEnergySpaceₗ (u : V) : ‖a.toEnergySpaceₗ u‖ = √(re (a.form u u)) :=
  (rfl)

private theorem norm_toEnergySpaceₗ_le (u : V) : ‖a.toEnergySpaceₗ u‖ ≤ √‖a.form‖ * ‖u‖ := by
  rw [norm_toEnergySpaceₗ, ← Real.sqrt_sq (norm_nonneg u), ← Real.sqrt_mul' _ (sq_nonneg _)]
  refine Real.sqrt_le_sqrt ?_
  calc re (a.form u u) ≤ ‖a.form u u‖ := re_le_norm _
    _ ≤ ‖a.form‖ * ‖u‖ * ‖u‖ := a.form.le_opNorm₂ u u
    _ = ‖a.form‖ * ‖u‖ ^ 2 := by ring

private theorem sqrt_mul_norm_le_norm_toEnergySpaceₗ {c : ℝ} (u : V)
    (h : c * ‖u‖ ^ 2 ≤ re (a.form u u)) : √c * ‖u‖ ≤ ‖a.toEnergySpaceₗ u‖ := by
  rw [norm_toEnergySpaceₗ, ← Real.sqrt_sq (norm_nonneg u), ← Real.sqrt_mul' _ (sq_nonneg _)]
  exact Real.sqrt_le_sqrt h

private theorem norm_toEnergySpaceₗ_symm_le {c : ℝ} (hc : 0 < c) (x : a.EnergySpace)
    (h : c * ‖a.toEnergySpaceₗ.symm x‖ ^ 2 ≤
      re (a.form (a.toEnergySpaceₗ.symm x) (a.toEnergySpaceₗ.symm x))) :
    ‖a.toEnergySpaceₗ.symm x‖ ≤ (√c)⁻¹ * ‖x‖ := by
  rw [le_inv_mul_iff₀ (Real.sqrt_pos.mpr hc)]
  simpa using a.sqrt_mul_norm_le_norm_toEnergySpaceₗ _ h

/-- The identity of `V`, as a continuous linear equivalence onto the energy space of `a`. It is
continuous in both directions because the energy norm is equivalent to the norm of `V`. -/
def toEnergySpace : V ≃L[𝕜] a.EnergySpace :=
  a.toEnergySpaceₗ.toContinuousLinearEquivOfBounds √‖a.form‖ (√a.exists_coercive.choose)⁻¹
    a.norm_toEnergySpaceₗ_le
    fun x ↦ a.norm_toEnergySpaceₗ_symm_le a.exists_coercive.choose_spec.1 x
      (a.exists_coercive.choose_spec.2 _)

/-- `a.toEnergySpace` applies `toEnergySpaceₗ`: `LinearEquiv.toContinuousLinearEquivOfBounds`
keeps the underlying linear equivalence. -/
private theorem coe_toEnergySpace : ⇑a.toEnergySpace = a.toEnergySpaceₗ := rfl

/-- The inverse of `a.toEnergySpace` applies the inverse of `toEnergySpaceₗ`. -/
private theorem coe_toEnergySpace_symm : ⇑a.toEnergySpace.symm = a.toEnergySpaceₗ.symm := rfl

/-- The inner product of the energy space, in terms of the underlying vectors of `V`. -/
theorem inner_eq_form (x y : a.EnergySpace) :
    ⟪x, y⟫_𝕜 = a.form (a.toEnergySpace.symm x) (a.toEnergySpace.symm y) := by
  rw [coe_toEnergySpace_symm]
  rfl

/-- The energy inner product of two vectors of `V` is the value of the form on them. -/
@[simp]
theorem inner_toEnergySpace (u v : V) :
    ⟪a.toEnergySpace u, a.toEnergySpace v⟫_𝕜 = a.form u v := by
  rw [inner_eq_form, ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- The squared energy norm of `u` is the diagonal value `re (a.form u u)`. -/
theorem norm_toEnergySpace_sq (u : V) : ‖a.toEnergySpace u‖ ^ 2 = re (a.form u u) := by
  rw [@norm_sq_eq_re_inner 𝕜, inner_toEnergySpace]

/-- The energy norm of `u` is `√(re (a.form u u))`. -/
theorem norm_toEnergySpace (u : V) : ‖a.toEnergySpace u‖ = √(re (a.form u u)) := by
  rw [coe_toEnergySpace]
  exact a.norm_toEnergySpaceₗ u

/-- **Upper energy bound.** The energy norm is at most `√‖a.form‖` times the norm of `V`. -/
theorem norm_toEnergySpace_le (u : V) : ‖a.toEnergySpace u‖ ≤ √‖a.form‖ * ‖u‖ := by
  rw [coe_toEnergySpace]
  exact a.norm_toEnergySpaceₗ_le u

/-- **Lower energy bound.** If `c * ‖u‖ ^ 2 ≤ re (a.form u u)`, then the energy norm of `u` is
at least `√c` times its norm in `V`. -/
theorem sqrt_mul_norm_le_norm_toEnergySpace {c : ℝ} (u : V)
    (h : c * ‖u‖ ^ 2 ≤ re (a.form u u)) : √c * ‖u‖ ≤ ‖a.toEnergySpace u‖ := by
  rw [coe_toEnergySpace]
  exact a.sqrt_mul_norm_le_norm_toEnergySpaceₗ u h

/-- **Comparison of two energy norms.** If `c * ‖u‖ ^ 2 ≤ re (a.form u u)`, then the energy norm
of `u` for another coercive Hermitian form `b` is controlled by its energy norm for `a`:
`√c * ‖u‖_b ≤ √‖b.form‖ * ‖u‖_a`. -/
theorem sqrt_mul_norm_toEnergySpace_le (b : CoerciveHermitianForm 𝕜 V) {c : ℝ} (u : V)
    (h : c * ‖u‖ ^ 2 ≤ re (a.form u u)) :
    √c * ‖b.toEnergySpace u‖ ≤ √‖b.form‖ * ‖a.toEnergySpace u‖ :=
  calc √c * ‖b.toEnergySpace u‖ ≤ √c * (√‖b.form‖ * ‖u‖) := by
        gcongr
        exact b.norm_toEnergySpace_le u
    _ = √‖b.form‖ * (√c * ‖u‖) := by ring
    _ ≤ √‖b.form‖ * ‖a.toEnergySpace u‖ := by
        gcongr
        exact a.sqrt_mul_norm_le_norm_toEnergySpace u h

/-- The operator norm of `a.toEnergySpace` is at most `√‖a.form‖`. -/
theorem opNorm_toEnergySpace_le : ‖(a.toEnergySpace : V →L[𝕜] a.EnergySpace)‖ ≤ √‖a.form‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) a.norm_toEnergySpace_le

/-- If `c * ‖u‖ ^ 2 ≤ re (a.form u u)` for every `u`, with `c > 0`, then the inverse of
`a.toEnergySpace` has operator norm at most `(√c)⁻¹`. -/
theorem opNorm_toEnergySpace_symm_le {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ u, c * ‖u‖ ^ 2 ≤ re (a.form u u)) :
    ‖(a.toEnergySpace.symm : a.EnergySpace →L[𝕜] V)‖ ≤ (√c)⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x ↦ by
    rw [ContinuousLinearEquiv.coe_coe, coe_toEnergySpace_symm]
    exact a.norm_toEnergySpaceₗ_symm_le hc x (hcoer _)

/-- The energy space of a coercive Hermitian form on a Banach space is a Hilbert space. -/
instance [CompleteSpace V] : CompleteSpace a.EnergySpace :=
  (completeSpace_congr (e := a.toEnergySpace.toEquiv) a.toEnergySpace.isUniformEmbedding).mp
    inferInstance

/-- **Variational equations through the Riesz map of the energy space.** On a Banach space `V`,
`u` solves `a.form u v = ℓ v` for every `v` if and only if `a.toEnergySpace u` is the Riesz
representative, in the energy space, of `ℓ` pulled back along `a.toEnergySpace.symm`. -/
theorem toEnergySpace_eq_toDual_symm_iff [CompleteSpace V] (ℓ : StrongDual 𝕜 V) (u : V) :
    a.toEnergySpace u = (InnerProductSpace.toDual 𝕜 a.EnergySpace).symm
        (ℓ.comp (a.toEnergySpace.symm : a.EnergySpace →L[𝕜] V)) ↔
      ∀ v, a.form u v = ℓ v := by
  refine ⟨fun h v ↦ ?_, fun h ↦ ext_inner_right 𝕜 fun x ↦ ?_⟩
  · simp [← inner_toEnergySpace, h, InnerProductSpace.toDual_symm_apply]
  · obtain ⟨v, rfl⟩ := a.toEnergySpace.surjective x
    simp [h, InnerProductSpace.toDual_symm_apply]

/-! ### Invertibility of the Fréchet–Riesz operator on a Hilbert space -/

section LaxMilgram

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
  (a : CoerciveHermitianForm 𝕜 V)

/-- The Fréchet–Riesz operator of a coercive Hermitian form on a Hilbert space is invertible. -/
theorem isUnit_continuousLinearMapOfBilin :
    IsUnit (InnerProductSpace.continuousLinearMapOfBilin a.form) :=
  have ⟨_, hc, hcoer⟩ := a.exists_coercive
  InnerProductSpace.isUnit_continuousLinearMapOfBilin_of_coercive a.form hc hcoer

end LaxMilgram

end CoerciveHermitianForm

end TauCeti
