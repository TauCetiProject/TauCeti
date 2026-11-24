/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.ClosedForm.Basic
public import TauCeti.Analysis.InnerProductSpace.Variational.EnergySpace
import TauCeti.Analysis.Real.Sqrt

/-!
# Closed semibounded forms on a subspace

Let `H` be an inner product space over `𝕜 = ℝ` or `ℂ`. A **semibounded form** on `H`
(`TauCeti.SemiboundedForm 𝕜 H`) is a Hermitian sesquilinear form `q` on a subspace `D` of `H`,
conjugate linear in its first slot, with some lower bound `γ` (`q.IsLowerBound γ`):
`γ * ‖u‖ ^ 2 ≤ re (q u u)` for `u ∈ D`. No continuity of `q` is assumed.

A shift `α` is admissible (`q.IsAdmissibleShift α`) when `α > -γ` for a lower bound `γ`. Then the
form `q_α(u, v) = q u v + α ⟪u, v⟫_𝕜` is an inner product on `D`, whose norm
`(re (q u u) + α * ‖u‖ ^ 2) ^ (1 / 2)` dominates the norm of `H`. The **form space**
`q.FormSpace α hα` is `D` with this inner product, and `q.inclusion hα` is its continuous
injective inclusion into `H`, with range `D`. The form is **closed** (`q.IsClosed`) when the form
spaces are complete. Different shifts give equivalent norms (`q.formSpaceEquiv`), so completeness
for one shift is completeness for all (`q.isClosed_iff_completeSpace`).

On the form space, `q` is a bounded sesquilinear form `q.formCLM hα` whose shift by `α` is the
inner product. So a closed form on a dense subspace of a Hilbert space is a model `(V, q, j)` of
`ContinuousLinearMap.closedFormOperator`, and it represents the operator `q.operator hd`, with
graph `{(u, h) | u ∈ D, ∀ v ∈ D, q u v = ⟪h, v⟫_𝕜}`, independent of the shift
(`q.operator_eq_closedFormOperator`). It is self-adjoint when `q` is closed
(`q.isSelfAdjoint_operator`) and keeps every lower bound `γ` of `q`.

Conversely, every model `(V, q, j)` of `ContinuousLinearMap.closedFormOperator` (a Banach space
`V`, a bounded Hermitian form `q` on `V`, a continuous injective `j : V →L[𝕜] H` and a shifted
coercivity bound `c * ‖u‖ ^ 2 ≤ re (q u u) + ω * ‖j u‖ ^ 2` with `c > 0`) arises this way: the
form transported to the range of `j` (`TauCeti.SemiboundedForm.ofModel`) is closed
(`TauCeti.SemiboundedForm.isClosed_ofModel`) and represents the same operator
(`TauCeti.SemiboundedForm.operator_ofModel`).

## Main declarations

* `TauCeti.SemiboundedForm`: a Hermitian sesquilinear form on a subspace, bounded below.
* `TauCeti.SemiboundedForm.IsLowerBound`, `TauCeti.SemiboundedForm.IsAdmissibleShift`: lower
  bounds of the form and the shifts they allow.
* `TauCeti.SemiboundedForm.FormSpace`: the subspace with the shifted inner product, with
  `TauCeti.SemiboundedForm.toFormSpace`, `TauCeti.SemiboundedForm.inner_toFormSpace` and
  `TauCeti.SemiboundedForm.norm_toFormSpace_sq`.
* `TauCeti.SemiboundedForm.inclusion`: the continuous injective inclusion of the form space into
  `H`, with dense range when the subspace is dense.
* `TauCeti.SemiboundedForm.formSpaceEquiv`: the identity between the form spaces of two shifts.
* `TauCeti.SemiboundedForm.IsClosed`: closedness, completeness of the form spaces, with
  `TauCeti.SemiboundedForm.isClosed_iff_completeSpace`.
* `TauCeti.SemiboundedForm.formCLM`: the form as a bounded form on the form space.
* `TauCeti.SemiboundedForm.operator`: the represented operator, with
  `TauCeti.SemiboundedForm.mem_graph_operator_iff`,
  `TauCeti.SemiboundedForm.mem_domain_operator_iff`,
  `TauCeti.SemiboundedForm.form_eq_inner_operator`,
  `TauCeti.SemiboundedForm.isSelfAdjoint_operator` and
  `TauCeti.SemiboundedForm.mul_norm_sq_le_re_inner_operator`.
* `TauCeti.SemiboundedForm.ofModel`: the closed form of a model `(V, q, j)`.

## References

* G. Teschl, *Mathematical Methods in Quantum Mechanics*, 2nd ed., AMS (2014), §2.3,
  Theorem 2.13.
-/

public section

noncomputable section

open RCLike
open scoped InnerProductSpace

namespace TauCeti

/-- A **semibounded form** on `H`: a sesquilinear form `form` on a subspace `domain` of `H`,
conjugate linear in its first slot, which is Hermitian and bounded below:
`γ * ‖u‖ ^ 2 ≤ re (form u u)` for some `γ`. The lower bound is only asserted to exist, so a
semibounded form is determined by its domain and its form. -/
@[ext]
structure SemiboundedForm (𝕜 H : Type*) [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] where
  /-- The form domain, a subspace of `H`. -/
  domain : Submodule 𝕜 H
  /-- The sesquilinear form, conjugate linear in its first slot. -/
  form : domain →ₗ⋆[𝕜] domain →ₗ[𝕜] 𝕜
  /-- The form is Hermitian. -/
  form_apply_eq_star : ∀ u v, form u v = star (form v u)
  /-- The form is bounded below, with some lower bound. -/
  exists_lowerBound : ∃ γ : ℝ, ∀ u : domain, γ * ‖(u : H)‖ ^ 2 ≤ re (form u u)

namespace SemiboundedForm

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  (q : SemiboundedForm 𝕜 H)

/-! ### Lower bounds and admissible shifts -/

/-- `γ` is a **lower bound** of `q`: `γ * ‖u‖ ^ 2 ≤ re (q u u)` on the form domain. -/
def IsLowerBound (γ : ℝ) : Prop :=
  ∀ u : q.domain, γ * ‖(u : H)‖ ^ 2 ≤ re (q.form u u)

/-- A shift `α` is **admissible** for `q` when `α > -γ` for some lower bound `γ` of `q`, so that
the shifted form `q u v + α ⟪u, v⟫_𝕜` is an inner product. -/
def IsAdmissibleShift (α : ℝ) : Prop :=
  ∃ γ, q.IsLowerBound γ ∧ -γ < α

/-- Unfolding `TauCeti.SemiboundedForm.IsLowerBound`. -/
theorem isLowerBound_iff {γ : ℝ} :
    q.IsLowerBound γ ↔ ∀ u : q.domain, γ * ‖(u : H)‖ ^ 2 ≤ re (q.form u u) :=
  Iff.rfl

/-- Unfolding `TauCeti.SemiboundedForm.IsAdmissibleShift`. -/
theorem isAdmissibleShift_iff {α : ℝ} : q.IsAdmissibleShift α ↔ ∃ γ, q.IsLowerBound γ ∧ -γ < α :=
  Iff.rfl

/-- Every semibounded form has a lower bound. -/
theorem exists_isLowerBound : ∃ γ, q.IsLowerBound γ :=
  q.exists_lowerBound

/-- Every semibounded form has an admissible shift. -/
theorem exists_isAdmissibleShift : ∃ α, q.IsAdmissibleShift α :=
  let ⟨γ, hγ⟩ := q.exists_isLowerBound
  ⟨1 - γ, γ, hγ, by linarith⟩

/-! ### The shifted inner product -/

/-- The shifted form `q_α(u, v) = q u v + α ⟪u, v⟫_𝕜` on the form domain. -/
def shiftedInner (α : ℝ) (u v : q.domain) : 𝕜 :=
  q.form u v + (α : 𝕜) * ⟪(u : H), (v : H)⟫_𝕜

/-- Unfolding `TauCeti.SemiboundedForm.shiftedInner`. -/
theorem shiftedInner_def (α : ℝ) (u v : q.domain) :
    q.shiftedInner α u v = q.form u v + (α : 𝕜) * ⟪(u : H), (v : H)⟫_𝕜 :=
  (rfl)

/-- The shifted form is Hermitian. -/
theorem star_shiftedInner (α : ℝ) (u v : q.domain) :
    star (q.shiftedInner α v u) = q.shiftedInner α u v := by
  rw [shiftedInner_def, shiftedInner_def, star_add, star_mul', ← q.form_apply_eq_star u v]
  simp only [RCLike.star_def, RCLike.conj_ofReal, inner_conj_symm]

/-- Diagonal real part of the shifted form. -/
theorem re_shiftedInner_self (α : ℝ) (u : q.domain) :
    re (q.shiftedInner α u u) = re (q.form u u) + α * ‖(u : H)‖ ^ 2 := by
  rw [shiftedInner_def, map_add, re_ofReal_mul, inner_self_eq_norm_sq]

/-- For a lower bound `γ`, the shifted form dominates `(γ + α) * ‖u‖ ^ 2` on the diagonal. -/
theorem add_mul_norm_sq_le_re_shiftedInner_self {γ : ℝ} (hγ : q.IsLowerBound γ) (α : ℝ)
    (u : q.domain) : (γ + α) * ‖(u : H)‖ ^ 2 ≤ re (q.shiftedInner α u u) := by
  rw [re_shiftedInner_self, add_mul]
  linarith [hγ u]

/-- Comparison of two shifts: for a lower bound `γ` and `α > -γ`, the diagonal of `q_β` is at
most `1 + |β - α| / (γ + α)` times that of `q_α`. -/
theorem re_shiftedInner_self_le {γ α : ℝ} (hγ : q.IsLowerBound γ) (hα : -γ < α) (β : ℝ)
    (u : q.domain) :
    re (q.shiftedInner β u u) ≤ (1 + |β - α| / (γ + α)) * re (q.shiftedInner α u u) := by
  have hpos : 0 < γ + α := by linarith
  have h1 := q.add_mul_norm_sq_le_re_shiftedInner_self hγ α u
  have h2 : |β - α| * ‖(u : H)‖ ^ 2 ≤ |β - α| / (γ + α) * re (q.shiftedInner α u u) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
    nlinarith [mul_le_mul_of_nonneg_left h1 (abs_nonneg (β - α))]
  have h3 : (β - α) * ‖(u : H)‖ ^ 2 ≤ |β - α| * ‖(u : H)‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
  rw [re_shiftedInner_self] at h1 h2
  rw [re_shiftedInner_self, re_shiftedInner_self]
  linarith

/-! ### The form space -/

/-- The **form space** of `q` for an admissible shift `α`: the form domain with the inner product
`q_α(u, v) = q u v + α ⟪u, v⟫_𝕜`. -/
def FormSpace (α : ℝ) (_hα : q.IsAdmissibleShift α) : Type _ := q.domain

variable {α : ℝ} (hα : q.IsAdmissibleShift α)

/-- The form space is additively the form domain. -/
instance instAddCommGroupFormSpace : AddCommGroup (q.FormSpace α hα) :=
  inferInstanceAs (AddCommGroup q.domain)

/-- The form space is the form domain as a module. -/
instance instModuleFormSpace : Module 𝕜 (q.FormSpace α hα) :=
  inferInstanceAs (Module 𝕜 q.domain)

/-- The identity of the form domain, as a linear equivalence onto the form space. -/
def toFormSpace : q.domain ≃ₗ[𝕜] q.FormSpace α hα := LinearEquiv.refl 𝕜 q.domain

/-- The inner product core of the form space: the shifted form `q_α`. It only builds the
instances below; use `TauCeti.SemiboundedForm.inner_toFormSpace` to compute the inner product. -/
@[instance_reducible]
def innerProductCore : InnerProductSpace.Core 𝕜 (q.FormSpace α hα) where
  inner x y := q.shiftedInner α ((q.toFormSpace hα).symm x) ((q.toFormSpace hα).symm y)
  conj_inner_symm x y := by
    rw [starRingEnd_apply, star_shiftedInner]
  re_inner_nonneg x := by
    obtain ⟨γ, hγ, hγα⟩ := id hα
    refine le_trans ?_ (q.add_mul_norm_sq_le_re_shiftedInner_self hγ α _)
    have : 0 < γ + α := by linarith
    positivity
  add_left x y z := by
    simp only [map_add, shiftedInner_def, LinearMap.add_apply, Submodule.coe_add, inner_add_left]
    ring
  smul_left x y r := by
    simp only [map_smul, shiftedInner_def, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, Submodule.coe_smul, inner_smul_left]
    ring
  definite x hx := by
    obtain ⟨γ, hγ, hγα⟩ := id hα
    have hpos : 0 < γ + α := by linarith
    have h := q.add_mul_norm_sq_le_re_shiftedInner_self hγ α ((q.toFormSpace hα).symm x)
    rw [hx, map_zero] at h
    have h0 := nonpos_of_mul_nonpos_right h hpos
    refine (q.toFormSpace hα).symm.map_eq_zero_iff.mp (Subtype.ext ?_)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm h0 (sq_nonneg _)))

/-- The form norm on the form space, `x ↦ (re (q x x) + α * ‖x‖ ^ 2) ^ (1 / 2)`. -/
instance instNormedAddCommGroupFormSpace : NormedAddCommGroup (q.FormSpace α hα) :=
  (q.innerProductCore hα).toNormedAddCommGroup

/-- The inner product of the form space is the shifted form. -/
instance instInnerProductSpaceFormSpace : InnerProductSpace 𝕜 (q.FormSpace α hα) :=
  InnerProductSpace.ofCore (q.innerProductCore hα).toCore

/-- The inner product of the form space is the shifted form `q_α`. -/
@[simp]
theorem inner_toFormSpace (u v : q.domain) :
    ⟪q.toFormSpace hα u, q.toFormSpace hα v⟫_𝕜 = q.shiftedInner α u v :=
  (rfl)

/-- The squared form norm is `re (q u u) + α * ‖u‖ ^ 2`. -/
theorem norm_toFormSpace_sq (u : q.domain) :
    ‖q.toFormSpace hα u‖ ^ 2 = re (q.form u u) + α * ‖(u : H)‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner 𝕜, inner_toFormSpace, re_shiftedInner_self]

/-- The squared form norm of `x` is the diagonal of the shifted form. -/
theorem norm_sq_eq_re_shiftedInner (x : q.FormSpace α hα) :
    ‖x‖ ^ 2 = re (q.shiftedInner α ((q.toFormSpace hα).symm x) ((q.toFormSpace hα).symm x)) := by
  obtain ⟨u, rfl⟩ := (q.toFormSpace hα).surjective x
  rw [@norm_sq_eq_re_inner 𝕜, inner_toFormSpace, LinearEquiv.symm_apply_apply]

/-! ### The inclusion into `H` -/

private theorem norm_coe_le {γ : ℝ} (hγ : q.IsLowerBound γ) (hγα : -γ < α)
    (x : q.FormSpace α hα) :
    ‖(((q.toFormSpace hα).symm x : q.domain) : H)‖ ≤ (√(γ + α))⁻¹ * ‖x‖ := by
  have hpos : 0 < γ + α := by linarith
  have h := q.add_mul_norm_sq_le_re_shiftedInner_self hγ α ((q.toFormSpace hα).symm x)
  rw [← norm_sq_eq_re_shiftedInner] at h
  rw [← Real.sqrt_inv]
  have hsq : ‖(((q.toFormSpace hα).symm x : q.domain) : H)‖ ^ 2 ≤ (γ + α)⁻¹ * ‖x‖ ^ 2 := by
    rw [inv_mul_eq_div, le_div_iff₀ hpos]
    linarith
  exact (Real.le_sqrt_of_sq_le hsq).trans_eq (by rw [Real.sqrt_mul_sq, abs_norm])

/-- The **inclusion of the form space into `H`**, continuous with norm at most
`(γ + α) ^ (-1 / 2)` for every lower bound `γ` with `-γ < α`. -/
def inclusion : q.FormSpace α hα →L[𝕜] H :=
  (q.domain.subtype ∘ₗ ((q.toFormSpace hα).symm : q.FormSpace α hα →ₗ[𝕜] q.domain))
    |>.mkContinuousOfExistsBound <|
    let ⟨_, hγ, hγα⟩ := hα
    ⟨_, q.norm_coe_le hα hγ hγα⟩

/-- The inclusion sends a vector of the form space to the underlying vector of the form
domain. -/
@[simp]
theorem inclusion_apply (x : q.FormSpace α hα) :
    q.inclusion hα x = ((q.toFormSpace hα).symm x : H) :=
  (rfl)

/-- The inclusion sends a vector of the form domain to itself. -/
theorem inclusion_toFormSpace (u : q.domain) : q.inclusion hα (q.toFormSpace hα u) = u :=
  (rfl)

/-- `√(γ + α) * ‖x‖_H ≤ ‖x‖` on the form space, for every lower bound `γ` with `-γ < α`. -/
theorem norm_inclusion_le {γ : ℝ} (hγ : q.IsLowerBound γ) (hγα : -γ < α)
    (x : q.FormSpace α hα) : ‖q.inclusion hα x‖ ≤ (√(γ + α))⁻¹ * ‖x‖ :=
  q.norm_coe_le hα hγ hγα x

/-- The inclusion of the form space into `H` is injective. -/
theorem inclusion_injective : Function.Injective (q.inclusion hα) := by
  intro x y h
  have : (q.toFormSpace hα).symm x = (q.toFormSpace hα).symm y := Subtype.ext h
  simpa using this

/-- The range of the inclusion is the form domain. -/
@[simp]
theorem range_inclusion : Set.range (q.inclusion hα) = q.domain := by
  ext x
  refine ⟨?_, fun hx ↦ ⟨q.toFormSpace hα ⟨x, hx⟩, rfl⟩⟩
  rintro ⟨y, rfl⟩
  exact ((q.toFormSpace hα).symm y).property

/-- The inclusion has dense range when the form domain is dense. -/
theorem denseRange_inclusion (hd : Dense (q.domain : Set H)) : DenseRange (q.inclusion hα) := by
  rw [DenseRange, range_inclusion]
  exact hd

/-! ### Independence of the shift -/

private theorem exists_norm_le_of_shift {β : ℝ} (hβ : q.IsAdmissibleShift β) :
    ∃ C, ∀ x : q.FormSpace α hα, ‖(q.toFormSpace hβ) ((q.toFormSpace hα).symm x)‖ ≤ C * ‖x‖ := by
  obtain ⟨γ, hγ, hγα⟩ := id hα
  refine ⟨√(1 + |β - α| / (γ + α)), fun x ↦ ?_⟩
  have hsq : ‖(q.toFormSpace hβ) ((q.toFormSpace hα).symm x)‖ ^ 2 ≤
      (1 + |β - α| / (γ + α)) * ‖x‖ ^ 2 := by
    rw [norm_sq_eq_re_shiftedInner, norm_sq_eq_re_shiftedInner, LinearEquiv.symm_apply_apply]
    exact q.re_shiftedInner_self_le hγ hγα β _
  exact (Real.le_sqrt_of_sq_le hsq).trans_eq (by rw [Real.sqrt_mul_sq, abs_norm])

/-- The form spaces of two shifts are the same space with equivalent norms: the identity of the
form domain is a continuous linear equivalence between them. -/
def formSpaceEquiv {β : ℝ} (hβ : q.IsAdmissibleShift β) :
    q.FormSpace α hα ≃L[𝕜] q.FormSpace β hβ :=
  ((q.toFormSpace hα).symm.trans (q.toFormSpace hβ)).toContinuousLinearEquivOfBounds
    (q.exists_norm_le_of_shift hα hβ).choose (q.exists_norm_le_of_shift hβ hα).choose
    (q.exists_norm_le_of_shift hα hβ).choose_spec (q.exists_norm_le_of_shift hβ hα).choose_spec

/-- `TauCeti.SemiboundedForm.formSpaceEquiv` is the identity of the form domain. -/
@[simp]
theorem formSpaceEquiv_toFormSpace {β : ℝ} (hβ : q.IsAdmissibleShift β) (u : q.domain) :
    q.formSpaceEquiv hα hβ (q.toFormSpace hα u) = q.toFormSpace hβ u :=
  (rfl)

/-- `TauCeti.SemiboundedForm.formSpaceEquiv` does not change the underlying vector of the form
domain. -/
@[simp]
theorem toFormSpace_symm_formSpaceEquiv {β : ℝ} (hβ : q.IsAdmissibleShift β)
    (x : q.FormSpace α hα) :
    (q.toFormSpace hβ).symm (q.formSpaceEquiv hα hβ x) = (q.toFormSpace hα).symm x :=
  (rfl)

/-- `TauCeti.SemiboundedForm.formSpaceEquiv` commutes with the inclusions into `H`. -/
theorem inclusion_formSpaceEquiv {β : ℝ} (hβ : q.IsAdmissibleShift β) (x : q.FormSpace α hα) :
    q.inclusion hβ (q.formSpaceEquiv hα hβ x) = q.inclusion hα x :=
  (rfl)

/-! ### Closed forms -/

/-- A semibounded form is **closed** when its form domain is complete for the form norm
`(re (q u u) + α * ‖u‖ ^ 2) ^ (1 / 2)` of every admissible shift `α`; by
`TauCeti.SemiboundedForm.isClosed_iff_completeSpace`, one shift suffices. -/
def IsClosed : Prop :=
  ∀ (α : ℝ) (hα : q.IsAdmissibleShift α), CompleteSpace (q.FormSpace α hα)

/-- **Closedness does not depend on the shift.** -/
theorem isClosed_iff_completeSpace : q.IsClosed ↔ CompleteSpace (q.FormSpace α hα) := by
  refine ⟨fun h ↦ h α hα, fun h β hβ ↦ ?_⟩
  exact (completeSpace_congr (e := (q.formSpaceEquiv hα hβ).toEquiv)
    (q.formSpaceEquiv hα hβ).isUniformEmbedding).mp h

/-! ### The form on the form space -/

/-- The form `q` as a bounded sesquilinear form on the form space: the inner product shifted back
by `-α`. -/
def formCLM : q.FormSpace α hα →L⋆[𝕜] q.FormSpace α hα →L[𝕜] 𝕜 :=
  ContinuousLinearMap.shiftedForm (q.inclusion hα) (innerSL 𝕜) (-α)

/-- `TauCeti.SemiboundedForm.formCLM` is the form `q` on the underlying vectors. -/
@[simp]
theorem formCLM_toFormSpace (u v : q.domain) :
    q.formCLM hα (q.toFormSpace hα u) (q.toFormSpace hα v) = q.form u v := by
  simp [formCLM, shiftedInner_def]

/-- `q.formCLM` shifted by `α` is the inner product of the form space. -/
theorem shiftedForm_formCLM :
    ContinuousLinearMap.shiftedForm (q.inclusion hα) (q.formCLM hα) α = innerSL 𝕜 := by
  simp [formCLM]

/-- `q.formCLM` is Hermitian. -/
theorem formCLM_apply_eq_star (x y : q.FormSpace α hα) :
    q.formCLM hα x y = star (q.formCLM hα y x) := by
  obtain ⟨u, rfl⟩ := (q.toFormSpace hα).surjective x
  obtain ⟨v, rfl⟩ := (q.toFormSpace hα).surjective y
  rw [formCLM_toFormSpace, formCLM_toFormSpace, q.form_apply_eq_star]

/-- The shifted coercivity bound of `q.formCLM`, with constant `1` and shift `α`. -/
theorem norm_sq_le_re_formCLM_add (x : q.FormSpace α hα) :
    1 * ‖x‖ ^ 2 ≤ re (q.formCLM hα x x) + α * ‖q.inclusion hα x‖ ^ 2 := by
  rw [← ContinuousLinearMap.re_shiftedForm_self, shiftedForm_formCLM, one_mul,
    innerSL_apply_apply, ← @norm_sq_eq_re_inner 𝕜]

/-! ### The represented operator -/

/-- The **operator represented by a semibounded form** `q` on a dense subspace: its graph consists
of the pairs `(u, h)` with `u` in the form domain and `q u v = ⟪h, v⟫_𝕜` for every `v` in the form
domain (`TauCeti.SemiboundedForm.mem_graph_operator_iff`). It is
`ContinuousLinearMap.closedFormOperator` for the form space of any admissible shift
(`TauCeti.SemiboundedForm.operator_eq_closedFormOperator`). -/
def operator (hd : Dense (q.domain : Set H)) : H →ₗ.[𝕜] H :=
  ContinuousLinearMap.closedFormOperator (q.inclusion q.exists_isAdmissibleShift.choose_spec)
    (q.inclusion_injective _) (q.denseRange_inclusion _ hd)
    (q.formCLM q.exists_isAdmissibleShift.choose_spec)

/-- The graph of `ContinuousLinearMap.closedFormOperator` for a model `(V, p, j)` identified with
`q` through a linear equivalence `e` of the form domain with `V`. -/
private theorem mem_graph_closedFormOperator_iff_of_linearEquiv {V : Type*}
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] {j : V →L[𝕜] H} (hj : Function.Injective j)
    (hdense : DenseRange j) {p : V →L⋆[𝕜] V →L[𝕜] 𝕜} (e : q.domain ≃ₗ[𝕜] V)
    (hje : ∀ u, j (e u) = u) (hpe : ∀ u v, p (e u) (e v) = q.form u v) {x h : H} :
    (x, h) ∈ (ContinuousLinearMap.closedFormOperator j hj hdense p).graph ↔
      ∃ u : q.domain, (u : H) = x ∧ ∀ v : q.domain, q.form u v = ⟪h, (v : H)⟫_𝕜 := by
  rw [ContinuousLinearMap.mem_graph_closedFormOperator_iff]
  constructor
  · rintro ⟨w, hw : j w = x, hwv : ∀ v, p w v = ⟪h, j v⟫_𝕜⟩
    obtain ⟨u, rfl⟩ := e.surjective w
    refine ⟨u, by rw [← hw, hje], fun v ↦ ?_⟩
    rw [← hpe, hwv, hje]
  · rintro ⟨u, hu, huv⟩
    refine ⟨e u, by rw [hje, hu], fun w ↦ ?_⟩
    obtain ⟨v, rfl⟩ := e.surjective w
    rw [hpe, huv, hje]

private theorem mem_graph_closedFormOperator_iff' (hd : Dense (q.domain : Set H)) {x h : H} :
    (x, h) ∈ (ContinuousLinearMap.closedFormOperator (q.inclusion hα) (q.inclusion_injective hα)
      (q.denseRange_inclusion hα hd) (q.formCLM hα)).graph ↔
      ∃ u : q.domain, (u : H) = x ∧ ∀ v : q.domain, q.form u v = ⟪h, (v : H)⟫_𝕜 :=
  q.mem_graph_closedFormOperator_iff_of_linearEquiv _ _ (q.toFormSpace hα)
    (q.inclusion_toFormSpace hα) (q.formCLM_toFormSpace hα)

/-- **Graph of the represented operator.** -/
theorem mem_graph_operator_iff (hd : Dense (q.domain : Set H)) {x h : H} :
    (x, h) ∈ (q.operator hd).graph ↔
      ∃ u : q.domain, (u : H) = x ∧ ∀ v : q.domain, q.form u v = ⟪h, (v : H)⟫_𝕜 :=
  q.mem_graph_closedFormOperator_iff' _ hd

/-- **Domain of the represented operator**: the vectors `u` of the form domain such that
`v ↦ q u v` is represented by a vector `h` of `H`. -/
theorem mem_domain_operator_iff (hd : Dense (q.domain : Set H)) {x : H} :
    x ∈ (q.operator hd).domain ↔
      ∃ u : q.domain, (u : H) = x ∧ ∃ h : H, ∀ v : q.domain, q.form u v = ⟪h, (v : H)⟫_𝕜 := by
  rw [LinearPMap.mem_domain_iff]
  simp only [mem_graph_operator_iff]
  exact ⟨fun ⟨h, u, hu, huv⟩ ↦ ⟨u, hu, h, huv⟩, fun ⟨u, hu, h, huv⟩ ↦ ⟨h, u, hu, huv⟩⟩

/-- **The represented operator does not depend on the shift**: it is the operator
`ContinuousLinearMap.closedFormOperator` of the form space of any admissible shift. -/
theorem operator_eq_closedFormOperator (hd : Dense (q.domain : Set H)) :
    q.operator hd = ContinuousLinearMap.closedFormOperator (q.inclusion hα)
      (q.inclusion_injective hα) (q.denseRange_inclusion hα hd) (q.formCLM hα) :=
  ContinuousLinearMap.eq_closedFormOperator_of_mem_graph_iff _ _ _ _ fun x h ↦ by
    rw [mem_graph_operator_iff, ← q.mem_graph_closedFormOperator_iff' hα hd,
      ContinuousLinearMap.mem_graph_closedFormOperator_iff]

/-- The domain of the represented operator lies in the form domain. -/
theorem domain_operator_le (hd : Dense (q.domain : Set H)) : (q.operator hd).domain ≤ q.domain := by
  intro x hx
  obtain ⟨u, hu, -⟩ := (q.mem_domain_operator_iff hd).mp hx
  exact hu ▸ u.property

/-- The form on a vector `x` of the domain of the represented operator is the inner product with
its image. -/
theorem form_eq_inner_operator (hd : Dense (q.domain : Set H)) (x : (q.operator hd).domain)
    (v : q.domain) :
    q.form ⟨x, q.domain_operator_le hd x.property⟩ v = ⟪q.operator hd x, (v : H)⟫_𝕜 := by
  obtain ⟨u, hu, huv⟩ := (q.mem_graph_operator_iff hd).mp (LinearPMap.mem_graph (q.operator hd) x)
  obtain rfl : u = ⟨x, q.domain_operator_le hd x.property⟩ := Subtype.ext hu
  exact huv v

/-- **The represented operator keeps every lower bound** `γ` of the form. -/
theorem mul_norm_sq_le_re_inner_operator (hd : Dense (q.domain : Set H)) {γ : ℝ}
    (hγ : q.IsLowerBound γ) (x : (q.operator hd).domain) :
    γ * ‖(x : H)‖ ^ 2 ≤ re ⟪q.operator hd x, (x : H)⟫_𝕜 := by
  exact (hγ _).trans_eq (congrArg re (q.form_eq_inner_operator hd x _))

/-- **First representation theorem for closed semibounded forms.** The operator represented by a
closed semibounded form on a dense subspace of a Hilbert space is self-adjoint. -/
theorem isSelfAdjoint_operator [CompleteSpace H] (hd : Dense (q.domain : Set H))
    (hq : q.IsClosed) : IsSelfAdjoint (q.operator hd) := by
  have := hq _ q.exists_isAdmissibleShift.choose_spec
  exact ContinuousLinearMap.isSelfAdjoint_closedFormOperator _ _ _ _
    (q.formCLM_apply_eq_star _)
    (ContinuousLinearMap.isUnit_continuousLinearMapOfBilin_shiftedForm _ one_pos le_rfl
      (q.norm_sq_le_re_formCLM_add _))

/-! ### Models of closed forms -/

section Model

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  (j : V →L[𝕜] H) (hj : Function.Injective j) (p : V →L⋆[𝕜] V →L[𝕜] 𝕜)
  (hp : ∀ u v, p u v = star (p v u)) (hb : ∃ γ : ℝ, ∀ u, γ * ‖j u‖ ^ 2 ≤ re (p u u))

/-- The identification of `V` with the range of `j`. -/
private def rangeEquiv : V ≃ₗ[𝕜] LinearMap.range (j : V →ₗ[𝕜] H) :=
  LinearEquiv.ofInjective (j : V →ₗ[𝕜] H) hj

/-- The semibounded form on the range of `j` transported from a model `(V, p, j)`: a bounded
Hermitian form `p` on `V` and a continuous injective `j : V →L[𝕜] H`, with
`γ * ‖j u‖ ^ 2 ≤ re (p u u)` for some `γ`. -/
def ofModel : SemiboundedForm 𝕜 H where
  domain := LinearMap.range (j : V →ₗ[𝕜] H)
  form := LinearMap.mk₂'ₛₗ (starRingEnd 𝕜) (RingHom.id 𝕜)
    (fun x y ↦ p ((rangeEquiv j hj).symm x) ((rangeEquiv j hj).symm y))
    (fun x y z ↦ by simp) (fun r x y ↦ by simp) (fun x y z ↦ by simp) (fun r x y ↦ by simp)
  form_apply_eq_star x y := hp _ _
  exists_lowerBound := by
    obtain ⟨γ, hγ⟩ := hb
    refine ⟨γ, fun x ↦ ?_⟩
    have h := hγ ((rangeEquiv j hj).symm x)
    have hx : j ((rangeEquiv j hj).symm x) = x :=
      congrArg Subtype.val ((rangeEquiv j hj).apply_symm_apply x)
    rwa [hx] at h

/-- The domain of `TauCeti.SemiboundedForm.ofModel` is the range of `j`. -/
@[simp]
theorem ofModel_domain :
    (ofModel j hj p hp hb).domain = LinearMap.range (j : V →ₗ[𝕜] H) :=
  (rfl)

/-- The identification of `V` with the domain of the transported form, `u ↦ j u`. -/
def toOfModel : V ≃ₗ[𝕜] (ofModel j hj p hp hb).domain :=
  rangeEquiv j hj

/-- `TauCeti.SemiboundedForm.toOfModel` sends `u` to `j u`. -/
@[simp]
theorem coe_toOfModel (u : V) : (toOfModel j hj p hp hb u : H) = j u :=
  (rfl)

/-- The transported form is `p` read through `TauCeti.SemiboundedForm.toOfModel`. -/
theorem ofModel_form_apply (x y : (ofModel j hj p hp hb).domain) :
    (ofModel j hj p hp hb).form x y =
      p ((toOfModel j hj p hp hb).symm x) ((toOfModel j hj p hp hb).symm y) :=
  (rfl)

/-- The transported form on `j u`, `j v` is `p u v`. -/
theorem ofModel_form_toOfModel (u v : V) :
    (ofModel j hj p hp hb).form (toOfModel j hj p hp hb u) (toOfModel j hj p hp hb v) = p u v := by
  rw [ofModel_form_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

/-- A lower bound of the model, `γ * ‖j u‖ ^ 2 ≤ re (p u u)`, is a lower bound of the transported
form. -/
theorem isLowerBound_ofModel {γ : ℝ} (hγ : ∀ u, γ * ‖j u‖ ^ 2 ≤ re (p u u)) :
    (ofModel j hj p hp hb).IsLowerBound γ := by
  intro x
  obtain ⟨u, rfl⟩ := (toOfModel j hj p hp hb).surjective x
  rw [ofModel_form_toOfModel, coe_toOfModel]
  exact hγ u

/-- A shifted coercivity bound `c * ‖u‖ ^ 2 ≤ re (p u u) + ω * ‖j u‖ ^ 2` with `c > 0` makes
`ω + 1` an admissible shift of the transported form. -/
private theorem isAdmissibleShift_ofModel {c ω : ℝ} (hc : 0 < c)
    (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ re (p u u) + ω * ‖j u‖ ^ 2) :
    (ofModel j hj p hp hb).IsAdmissibleShift (ω + 1) := by
  refine ⟨-ω, isLowerBound_ofModel j hj p hp hb fun u ↦ ?_, by linarith⟩
  nlinarith [hcoercive u, sq_nonneg ‖u‖]

/-- The form `p` shifted by `ω + 1` along `j`, coercive under a shifted coercivity bound. -/
private def shiftedCoerciveForm {c ω : ℝ} (hc : 0 < c)
    (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ re (p u u) + ω * ‖j u‖ ^ 2) : CoerciveHermitianForm 𝕜 V :=
  ⟨ContinuousLinearMap.shiftedForm j p (ω + 1), ContinuousLinearMap.shiftedForm_eq_star j hp _,
    c, hc, ContinuousLinearMap.mul_norm_sq_le_re_shiftedForm_self j (by linarith) hcoercive⟩

private theorem shiftedCoerciveForm_form {c ω : ℝ} (hc : 0 < c)
    (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ re (p u u) + ω * ‖j u‖ ^ 2) :
    (shiftedCoerciveForm j p hp hc hcoercive).form = ContinuousLinearMap.shiftedForm j p (ω + 1) :=
  rfl

/-- The energy space of the shifted model form is isometric to the form space of the transported
form for the shift `ω + 1`, through `u ↦ j u`. -/
private def energySpaceIsometryOfModel {c ω : ℝ} (hc : 0 < c)
    (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ re (p u u) + ω * ‖j u‖ ^ 2) :
    (shiftedCoerciveForm j p hp hc hcoercive).EnergySpace ≃ₗᵢ[𝕜]
      (ofModel j hj p hp hb).FormSpace (ω + 1)
        (isAdmissibleShift_ofModel j hj p hp hb hc hcoercive) where
  toLinearEquiv :=
    ((shiftedCoerciveForm j p hp hc hcoercive).toEnergySpace.symm.toLinearEquiv).trans
      ((toOfModel j hj p hp hb).trans ((ofModel j hj p hp hb).toFormSpace _))
  norm_map' x := by
    obtain ⟨u, rfl⟩ := (shiftedCoerciveForm j p hp hc hcoercive).toEnergySpace.surjective x
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
    simp [CoerciveHermitianForm.norm_toEnergySpace_sq, shiftedCoerciveForm_form,
      norm_toFormSpace_sq, ofModel_form_toOfModel]

/-- **A model of a closed form gives a closed form.** If `V` is complete and
`c * ‖u‖ ^ 2 ≤ re (p u u) + ω * ‖j u‖ ^ 2` with `c > 0`, the form transported to the range of `j`
is closed. -/
theorem isClosed_ofModel [CompleteSpace V] {c ω : ℝ} (hc : 0 < c)
    (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ re (p u u) + ω * ‖j u‖ ^ 2) :
    (ofModel j hj p hp hb).IsClosed :=
  (ofModel j hj p hp hb).isClosed_iff_completeSpace
    (isAdmissibleShift_ofModel j hj p hp hb hc hcoercive) |>.mpr <|
    (energySpaceIsometryOfModel j hj p hp hb hc hcoercive).toIsometryEquiv.completeSpace_iff.mp
      inferInstance

/-- The range of `j` is dense when `j` has dense range. -/
theorem dense_ofModel_domain (hdense : DenseRange j) :
    Dense ((ofModel j hj p hp hb).domain : Set H) := by
  rw [ofModel_domain, LinearMap.coe_range]
  exact hdense

/-- **The form of a model represents the operator of the model.** -/
theorem operator_ofModel (hdense : DenseRange j) :
    (ofModel j hj p hp hb).operator (dense_ofModel_domain j hj p hp hb hdense) =
      ContinuousLinearMap.closedFormOperator j hj hdense p :=
  ContinuousLinearMap.eq_closedFormOperator_of_mem_graph_iff _ _ _ _ fun x h ↦ by
    rw [mem_graph_operator_iff, ← mem_graph_closedFormOperator_iff_of_linearEquiv _ hj hdense
      (toOfModel j hj p hp hb).symm (fun u ↦ congrArg Subtype.val
        ((toOfModel j hj p hp hb).apply_symm_apply u)) fun u v ↦ (ofModel_form_apply ..).symm,
      ContinuousLinearMap.mem_graph_closedFormOperator_iff]

end Model

end SemiboundedForm

end TauCeti
