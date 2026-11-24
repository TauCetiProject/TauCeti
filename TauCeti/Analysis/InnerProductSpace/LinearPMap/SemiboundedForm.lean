/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.ClosedForm

/-!
# Closed semibounded forms on a subspace

Let `H` be an inner product space over `𝕜 = ℝ` or `ℂ`. A **semibounded form** on `H`
(`TauCeti.SemiboundedForm 𝕜 H`) is a Hermitian sesquilinear form `q` on a subspace `D` of `H`,
conjugate linear in its first slot, with a lower bound `γ`:
`γ * ‖u‖ ^ 2 ≤ re (q u u)` for `u ∈ D`. No continuity of `q` is assumed.

For every shift `α > -γ` the form `q_α(u, v) = q u v + α ⟪u, v⟫_𝕜` is an inner product on `D`,
whose norm `(re (q u u) + α * ‖u‖ ^ 2) ^ (1 / 2)` dominates the norm of `H`. The **form space**
`q.FormSpace α hα` is `D` with this inner product, and `q.inclusion α hα` is its continuous
injective inclusion into `H`, with range `D`. The form is **closed** (`q.IsClosed`) when the form
spaces are complete. Different shifts give equivalent norms (`q.formSpaceEquiv`), so completeness
for one shift is completeness for all (`q.isClosed_iff_completeSpace`).

On the form space, `q` is a bounded sesquilinear form `q.formCLM α hα` whose shift by `α` is the
inner product. So a closed form on a dense subspace of a Hilbert space is a model `(V, q, j)` of
`ContinuousLinearMap.closedFormOperator`, and it represents the operator `q.operator hd`, with
graph `{(u, h) | u ∈ D, ∀ v ∈ D, q u v = ⟪h, v⟫_𝕜}`, independent of the shift
(`q.operator_eq_closedFormOperator`). It is self-adjoint when `q` is closed
(`q.isSelfAdjoint_operator`) and keeps the lower bound `γ`.

Conversely, every model `(V, q, j)` of `ContinuousLinearMap.closedFormOperator` (a Hilbert space
`V`, a bounded Hermitian form `q` on `V`, a continuous injective `j : V →L[𝕜] H` and a shifted
coercivity bound `c * ‖u‖ ^ 2 ≤ re (q u u) + ω * ‖j u‖ ^ 2` with `c > 0`) arises this way: the
form transported to the range of `j` (`TauCeti.SemiboundedForm.ofModel`) is closed
(`TauCeti.SemiboundedForm.isClosed_ofModel`) and represents the same operator
(`TauCeti.SemiboundedForm.operator_ofModel`).

## Main declarations

* `TauCeti.SemiboundedForm`: a Hermitian sesquilinear form on a subspace, bounded below.
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
conjugate linear in its first slot, which is Hermitian and bounded below by `lowerBound`:
`lowerBound * ‖u‖ ^ 2 ≤ re (form u u)`. -/
structure SemiboundedForm (𝕜 H : Type*) [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] where
  /-- The form domain, a subspace of `H`. -/
  domain : Submodule 𝕜 H
  /-- The sesquilinear form, conjugate linear in its first slot. -/
  form : domain →ₗ⋆[𝕜] domain →ₗ[𝕜] 𝕜
  /-- The form is Hermitian. -/
  form_apply_eq_star : ∀ u v, form u v = star (form v u)
  /-- A lower bound of the form. -/
  lowerBound : ℝ
  /-- The form is bounded below by `lowerBound`. -/
  lowerBound_mul_norm_sq_le : ∀ u : domain, lowerBound * ‖(u : H)‖ ^ 2 ≤ re (form u u)

namespace SemiboundedForm

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  (q : SemiboundedForm 𝕜 H)

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

/-- The shifted form dominates `(γ + α) * ‖u‖ ^ 2` on the diagonal. -/
theorem add_mul_norm_sq_le_re_shiftedInner_self (α : ℝ) (u : q.domain) :
    (q.lowerBound + α) * ‖(u : H)‖ ^ 2 ≤ re (q.shiftedInner α u u) := by
  rw [re_shiftedInner_self, add_mul]
  linarith [q.lowerBound_mul_norm_sq_le u]

/-- Comparison of two shifts: for `α > -γ`, the diagonal of `q_β` is at most
`1 + |β - α| / (γ + α)` times that of `q_α`. -/
theorem re_shiftedInner_self_le {α : ℝ} (hα : -q.lowerBound < α) (β : ℝ) (u : q.domain) :
    re (q.shiftedInner β u u) ≤
      (1 + |β - α| / (q.lowerBound + α)) * re (q.shiftedInner α u u) := by
  have hpos : 0 < q.lowerBound + α := by linarith
  have h1 := q.add_mul_norm_sq_le_re_shiftedInner_self α u
  have h2 : |β - α| * ‖(u : H)‖ ^ 2 ≤
      |β - α| / (q.lowerBound + α) * re (q.shiftedInner α u u) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos, mul_assoc, mul_comm (‖(u : H)‖ ^ 2)]
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have h3 : (β - α) * ‖(u : H)‖ ^ 2 ≤ |β - α| * ‖(u : H)‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
  rw [re_shiftedInner_self] at h1 h2
  rw [re_shiftedInner_self, re_shiftedInner_self]
  linarith

/-! ### The form space -/

/-- The **form space** of `q` for a shift `α > -γ`: the form domain with the inner product
`q_α(u, v) = q u v + α ⟪u, v⟫_𝕜`. -/
def FormSpace (α : ℝ) (_hα : -q.lowerBound < α) : Type _ := q.domain

variable {α : ℝ} (hα : -q.lowerBound < α)

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
    refine le_trans ?_ (q.add_mul_norm_sq_le_re_shiftedInner_self α _)
    have : 0 < q.lowerBound + α := by linarith
    positivity
  add_left x y z := by
    simp only [map_add, shiftedInner_def, LinearMap.add_apply, Submodule.coe_add, inner_add_left]
    ring
  smul_left x y r := by
    simp only [map_smul, shiftedInner_def, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, Submodule.coe_smul, inner_smul_left]
    ring
  definite x hx := by
    have hpos : 0 < q.lowerBound + α := by linarith
    have h := q.add_mul_norm_sq_le_re_shiftedInner_self α ((q.toFormSpace hα).symm x)
    rw [hx, map_zero] at h
    have h0 : ‖(((q.toFormSpace hα).symm x : q.domain) : H)‖ ^ 2 ≤ 0 := by
      nlinarith [sq_nonneg ‖(((q.toFormSpace hα).symm x : q.domain) : H)‖, hpos]
    have : (q.toFormSpace hα).symm x = 0 := by
      ext
      simpa using pow_eq_zero_iff (n := 2) two_ne_zero |>.mp (le_antisymm h0 (sq_nonneg _))
    simpa using this

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
  rw [@norm_sq_eq_re_inner 𝕜]
  rfl

/-! ### The inclusion into `H` -/

private theorem norm_coe_le (x : q.FormSpace α hα) :
    ‖(((q.toFormSpace hα).symm x : q.domain) : H)‖ ≤ (√(q.lowerBound + α))⁻¹ * ‖x‖ := by
  have hpos : 0 < q.lowerBound + α := by linarith
  rw [le_inv_mul_iff₀ (Real.sqrt_pos.mpr hpos)]
  have h := q.add_mul_norm_sq_le_re_shiftedInner_self α ((q.toFormSpace hα).symm x)
  rw [← norm_sq_eq_re_shiftedInner] at h
  calc √(q.lowerBound + α) * ‖(((q.toFormSpace hα).symm x : q.domain) : H)‖
      = √((q.lowerBound + α) * ‖(((q.toFormSpace hα).symm x : q.domain) : H)‖ ^ 2) := by
        rw [Real.sqrt_mul hpos.le, Real.sqrt_sq (norm_nonneg _)]
    _ ≤ √(‖x‖ ^ 2) := Real.sqrt_le_sqrt h
    _ = ‖x‖ := Real.sqrt_sq (norm_nonneg _)

/-- The **inclusion of the form space into `H`**, continuous with norm at most
`(γ + α) ^ (-1 / 2)`. -/
def inclusion : q.FormSpace α hα →L[𝕜] H :=
  (q.domain.subtype ∘ₗ ((q.toFormSpace hα).symm : q.FormSpace α hα →ₗ[𝕜] q.domain)).mkContinuous
    (√(q.lowerBound + α))⁻¹ (q.norm_coe_le hα)

/-- The inclusion sends a vector of the form domain to itself. -/
@[simp]
theorem inclusion_toFormSpace (u : q.domain) : q.inclusion hα (q.toFormSpace hα u) = u :=
  (rfl)

/-- `√(γ + α) * ‖x‖_H ≤ ‖x‖` on the form space. -/
theorem norm_inclusion_le (x : q.FormSpace α hα) :
    ‖q.inclusion hα x‖ ≤ (√(q.lowerBound + α))⁻¹ * ‖x‖ :=
  q.norm_coe_le hα x

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

private theorem norm_le_of_shift {β : ℝ} (hβ : -q.lowerBound < β) (x : q.FormSpace α hα) :
    ‖(q.toFormSpace hβ) ((q.toFormSpace hα).symm x)‖ ≤
      √(1 + |β - α| / (q.lowerBound + α)) * ‖x‖ := by
  have hpos : 0 < q.lowerBound + α := by linarith
  rw [← Real.sqrt_sq (norm_nonneg ((q.toFormSpace hβ) _)), ← Real.sqrt_sq (norm_nonneg x),
    ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  rw [norm_sq_eq_re_shiftedInner, norm_sq_eq_re_shiftedInner, LinearEquiv.symm_apply_apply]
  exact q.re_shiftedInner_self_le hα β _

/-- The form spaces of two shifts are the same space with equivalent norms: the identity of the
form domain is a continuous linear equivalence between them. -/
def formSpaceEquiv {β : ℝ} (hβ : -q.lowerBound < β) : q.FormSpace α hα ≃L[𝕜] q.FormSpace β hβ :=
  ((q.toFormSpace hα).symm.trans (q.toFormSpace hβ)).toContinuousLinearEquivOfBounds
    √(1 + |β - α| / (q.lowerBound + α)) √(1 + |α - β| / (q.lowerBound + β))
    (q.norm_le_of_shift hα hβ) (q.norm_le_of_shift hβ hα)

/-- `TauCeti.SemiboundedForm.formSpaceEquiv` is the identity of the form domain. -/
@[simp]
theorem formSpaceEquiv_toFormSpace {β : ℝ} (hβ : -q.lowerBound < β) (u : q.domain) :
    q.formSpaceEquiv hα hβ (q.toFormSpace hα u) = q.toFormSpace hβ u :=
  (rfl)

/-- `TauCeti.SemiboundedForm.formSpaceEquiv` commutes with the inclusions into `H`. -/
@[simp]
theorem inclusion_formSpaceEquiv {β : ℝ} (hβ : -q.lowerBound < β) (x : q.FormSpace α hα) :
    q.inclusion hβ (q.formSpaceEquiv hα hβ x) = q.inclusion hα x :=
  (rfl)

/-! ### Closed forms -/

/-- A semibounded form is **closed** when its form domain is complete for the form norm
`(re (q u u) + α * ‖u‖ ^ 2) ^ (1 / 2)` of every shift `α > -γ`; by
`TauCeti.SemiboundedForm.isClosed_iff_completeSpace`, one shift suffices. -/
def IsClosed : Prop :=
  ∀ (α : ℝ) (hα : -q.lowerBound < α), CompleteSpace (q.FormSpace α hα)

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

/-- The canonical shift `1 - γ` used to define `TauCeti.SemiboundedForm.operator`. -/
theorem neg_lowerBound_lt_one_sub : -q.lowerBound < 1 - q.lowerBound := by linarith

/-- The **operator represented by a semibounded form** `q` on a dense subspace: its graph consists
of the pairs `(u, h)` with `u` in the form domain and `q u v = ⟪h, v⟫_𝕜` for every `v` in the form
domain (`TauCeti.SemiboundedForm.mem_graph_operator_iff`). It is
`ContinuousLinearMap.closedFormOperator` for the form space of any shift
(`TauCeti.SemiboundedForm.operator_eq_closedFormOperator`). -/
def operator (hd : Dense (q.domain : Set H)) : H →ₗ.[𝕜] H :=
  ContinuousLinearMap.closedFormOperator (q.inclusion q.neg_lowerBound_lt_one_sub)
    (q.inclusion_injective _) (q.denseRange_inclusion _ hd) (q.formCLM q.neg_lowerBound_lt_one_sub)

private theorem mem_graph_closedFormOperator_iff' (hd : Dense (q.domain : Set H)) {x h : H} :
    (x, h) ∈ (ContinuousLinearMap.closedFormOperator (q.inclusion hα) (q.inclusion_injective hα)
      (q.denseRange_inclusion hα hd) (q.formCLM hα)).graph ↔
      ∃ u : q.domain, (u : H) = x ∧ ∀ v : q.domain, q.form u v = ⟪h, (v : H)⟫_𝕜 := by
  rw [ContinuousLinearMap.mem_graph_closedFormOperator_iff]
  constructor
  · rintro ⟨y, hy, hyv⟩
    obtain ⟨u, rfl⟩ := (q.toFormSpace hα).surjective y
    refine ⟨u, by simpa using hy, fun v ↦ ?_⟩
    simpa using hyv (q.toFormSpace hα v)
  · rintro ⟨u, hu, huv⟩
    refine ⟨q.toFormSpace hα u, hu, fun y ↦ ?_⟩
    obtain ⟨v, rfl⟩ := (q.toFormSpace hα).surjective y
    rw [formCLM_toFormSpace, huv, inclusion_toFormSpace]

/-- **Graph of the represented operator.** -/
theorem mem_graph_operator_iff (hd : Dense (q.domain : Set H)) {x h : H} :
    (x, h) ∈ (q.operator hd).graph ↔
      ∃ u : q.domain, (u : H) = x ∧ ∀ v : q.domain, q.form u v = ⟪h, (v : H)⟫_𝕜 :=
  q.mem_graph_closedFormOperator_iff' _ hd

/-- **The represented operator does not depend on the shift**: it is the operator
`ContinuousLinearMap.closedFormOperator` of the form space of any shift `α > -γ`. -/
theorem operator_eq_closedFormOperator (hd : Dense (q.domain : Set H)) :
    q.operator hd = ContinuousLinearMap.closedFormOperator (q.inclusion hα)
      (q.inclusion_injective hα) (q.denseRange_inclusion hα hd) (q.formCLM hα) :=
  ContinuousLinearMap.eq_closedFormOperator_of_mem_graph_iff _ _ _ _ fun x h ↦ by
    rw [mem_graph_operator_iff, ← q.mem_graph_closedFormOperator_iff' hα hd,
      ContinuousLinearMap.mem_graph_closedFormOperator_iff]

/-- The domain of the represented operator lies in the form domain. -/
theorem domain_operator_le (hd : Dense (q.domain : Set H)) : (q.operator hd).domain ≤ q.domain := by
  intro x hx
  obtain ⟨u, hu, -⟩ := (q.mem_graph_operator_iff hd).mp (LinearPMap.mem_graph (q.operator hd)
    ⟨x, hx⟩)
  have hux : (u : H) = x := hu
  exact hux ▸ u.property

/-- **The represented operator keeps the lower bound** `γ` of the form. -/
theorem mul_norm_sq_le_re_inner_operator (hd : Dense (q.domain : Set H))
    (x : (q.operator hd).domain) :
    q.lowerBound * ‖(x : H)‖ ^ 2 ≤ re ⟪q.operator hd x, (x : H)⟫_𝕜 := by
  obtain ⟨u, hu, huv⟩ := (q.mem_graph_operator_iff hd).mp (LinearPMap.mem_graph (q.operator hd) x)
  have := huv u
  rw [← hu, ← this]
  exact q.lowerBound_mul_norm_sq_le u

/-- **First representation theorem for closed semibounded forms.** The operator represented by a
closed semibounded form on a dense subspace of a Hilbert space is self-adjoint. -/
theorem isSelfAdjoint_operator [CompleteSpace H] (hd : Dense (q.domain : Set H))
    (hq : q.IsClosed) : IsSelfAdjoint (q.operator hd) := by
  have := hq _ q.neg_lowerBound_lt_one_sub
  exact ContinuousLinearMap.isSelfAdjoint_closedFormOperator _ _ _ _
    (q.formCLM_apply_eq_star _)
    (ContinuousLinearMap.isUnit_continuousLinearMapOfBilin_shiftedForm _ one_pos le_rfl
      (q.norm_sq_le_re_formCLM_add _))

/-! ### Models of closed forms -/

section Model

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  (j : V →L[𝕜] H) (hj : Function.Injective j) (p : V →L⋆[𝕜] V →L[𝕜] 𝕜)
  (hp : ∀ u v, p u v = star (p v u)) {c ω : ℝ} (hc : 0 < c)
  (hcoercive : ∀ u, c * ‖u‖ ^ 2 ≤ re (p u u) + ω * ‖j u‖ ^ 2)

/-- The identification of `V` with the range of `j`. -/
private def rangeEquiv : V ≃ₗ[𝕜] LinearMap.range (j : V →ₗ[𝕜] H) :=
  LinearEquiv.ofInjective (j : V →ₗ[𝕜] H) hj

/-- The semibounded form on the range of `j` transported from a model `(V, p, j)`: a bounded
Hermitian form `p` on `V`, a continuous injective `j : V →L[𝕜] H` and a shifted coercivity bound
`c * ‖u‖ ^ 2 ≤ re (p u u) + ω * ‖j u‖ ^ 2`. Its lower bound is `-ω`. -/
def ofModel : SemiboundedForm 𝕜 H where
  domain := LinearMap.range (j : V →ₗ[𝕜] H)
  form := LinearMap.mk₂'ₛₗ (starRingEnd 𝕜) (RingHom.id 𝕜)
    (fun x y ↦ p ((rangeEquiv j hj).symm x) ((rangeEquiv j hj).symm y))
    (fun x y z ↦ by simp) (fun r x y ↦ by simp) (fun x y z ↦ by simp) (fun r x y ↦ by simp)
  form_apply_eq_star x y := hp _ _
  lowerBound := -ω
  lowerBound_mul_norm_sq_le x := by
    have h := hcoercive ((rangeEquiv j hj).symm x)
    have hx : j ((rangeEquiv j hj).symm x) = x :=
      congrArg Subtype.val ((rangeEquiv j hj).apply_symm_apply x)
    rw [hx] at h
    have : 0 ≤ c * ‖(rangeEquiv j hj).symm x‖ ^ 2 := by positivity
    simp only [LinearMap.mk₂'ₛₗ_apply]
    linarith

/-- The domain of `TauCeti.SemiboundedForm.ofModel` is the range of `j`. -/
@[simp]
theorem ofModel_domain :
    (ofModel j hj p hp hc hcoercive).domain = LinearMap.range (j : V →ₗ[𝕜] H) :=
  (rfl)

/-- The lower bound of `TauCeti.SemiboundedForm.ofModel` is `-ω`. -/
@[simp]
theorem ofModel_lowerBound : (ofModel j hj p hp hc hcoercive).lowerBound = -ω :=
  (rfl)

/-- The identification of `V` with the domain of the transported form, `u ↦ j u`. -/
def toOfModel : V ≃ₗ[𝕜] (ofModel j hj p hp hc hcoercive).domain :=
  rangeEquiv j hj

/-- `TauCeti.SemiboundedForm.toOfModel` sends `u` to `j u`. -/
@[simp]
theorem coe_toOfModel (u : V) : (toOfModel j hj p hp hc hcoercive u : H) = j u :=
  (rfl)

/-- The transported form on `j u`, `j v` is `p u v`. -/
theorem ofModel_form_toOfModel (u v : V) :
    (ofModel j hj p hp hc hcoercive).form (toOfModel j hj p hp hc hcoercive u)
      (toOfModel j hj p hp hc hcoercive v) = p u v := by
  change p ((rangeEquiv j hj).symm (rangeEquiv j hj u)) ((rangeEquiv j hj).symm
    (rangeEquiv j hj v)) = p u v
  simp

private theorem ofModel_shift : -(ofModel j hj p hp hc hcoercive).lowerBound < ω + 1 := by
  simp

private theorem norm_toFormSpace_ofModel_sq (u : V) :
    ‖(ofModel j hj p hp hc hcoercive).toFormSpace (ofModel_shift j hj p hp hc hcoercive)
      (toOfModel j hj p hp hc hcoercive u)‖ ^ 2 = re (p u u) + (ω + 1) * ‖j u‖ ^ 2 := by
  rw [norm_toFormSpace_sq, ofModel_form_toOfModel, coe_toOfModel]

/-- **A model of a closed form gives a closed form.** If `V` is complete, the form transported to
the range of `j` from a model `(V, p, j)` is closed. -/
theorem isClosed_ofModel [CompleteSpace V] : (ofModel j hj p hp hc hcoercive).IsClosed := by
  set q := ofModel j hj p hp hc hcoercive
  have hα := ofModel_shift j hj p hp hc hcoercive
  rw [q.isClosed_iff_completeSpace hα]
  have hupper (u : V) : ‖q.toFormSpace hα (toOfModel j hj p hp hc hcoercive u)‖ ≤
      √(‖p‖ + |ω + 1| * ‖j‖ ^ 2) * ‖u‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (q.toFormSpace hα _)), ← Real.sqrt_sq (norm_nonneg u),
      ← Real.sqrt_mul (by positivity), norm_toFormSpace_ofModel_sq]
    refine Real.sqrt_le_sqrt ?_
    have h1 : re (p u u) ≤ ‖p‖ * ‖u‖ ^ 2 :=
      (re_le_norm _).trans ((p.le_opNorm₂ u u).trans_eq (by ring))
    have h2 : (ω + 1) * ‖j u‖ ^ 2 ≤ |ω + 1| * (‖j‖ ^ 2 * ‖u‖ ^ 2) := by
      calc (ω + 1) * ‖j u‖ ^ 2 ≤ |ω + 1| * ‖j u‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
        _ ≤ |ω + 1| * (‖j‖ ^ 2 * ‖u‖ ^ 2) := by
          rw [← mul_pow]
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) (j.le_opNorm u) 2) (abs_nonneg _)
    nlinarith
  have hlower (u : V) : √c * ‖u‖ ≤ ‖q.toFormSpace hα (toOfModel j hj p hp hc hcoercive u)‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (q.toFormSpace hα _)), ← Real.sqrt_sq (norm_nonneg u),
      ← Real.sqrt_mul hc.le, norm_toFormSpace_ofModel_sq]
    refine Real.sqrt_le_sqrt ?_
    have := hcoercive u
    nlinarith [sq_nonneg ‖j u‖]
  let e₀ : V ≃ₗ[𝕜] q.FormSpace (ω + 1) hα :=
    (toOfModel j hj p hp hc hcoercive).trans (q.toFormSpace hα)
  let e : V ≃L[𝕜] q.FormSpace (ω + 1) hα :=
    e₀.toContinuousLinearEquivOfBounds _ (√c)⁻¹ hupper fun x ↦ by
      obtain ⟨u, rfl⟩ := e₀.surjective x
      rw [LinearEquiv.symm_apply_apply, le_inv_mul_iff₀ (Real.sqrt_pos.mpr hc)]
      exact hlower u
  exact (completeSpace_congr (e := e.toEquiv) e.isUniformEmbedding).mp inferInstance

/-- The range of `j` is dense when `j` has dense range. -/
theorem dense_ofModel_domain (hdense : DenseRange j) :
    Dense ((ofModel j hj p hp hc hcoercive).domain : Set H) := by
  rw [ofModel_domain, LinearMap.coe_range]
  exact hdense

/-- **The form of a model represents the operator of the model.** -/
theorem operator_ofModel (hdense : DenseRange j) :
    (ofModel j hj p hp hc hcoercive).operator (dense_ofModel_domain j hj p hp hc hcoercive hdense) =
      ContinuousLinearMap.closedFormOperator j hj hdense p :=
  ContinuousLinearMap.eq_closedFormOperator_of_mem_graph_iff _ _ _ _ fun x h ↦ by
    rw [mem_graph_operator_iff]
    constructor
    · rintro ⟨y, hu, huv⟩
      obtain ⟨w, rfl⟩ := (toOfModel j hj p hp hc hcoercive).surjective y
      refine ⟨w, hu, fun v ↦ ?_⟩
      have := huv (toOfModel j hj p hp hc hcoercive v)
      rwa [ofModel_form_toOfModel, coe_toOfModel] at this
    · rintro ⟨w, hu, huv⟩
      refine ⟨toOfModel j hj p hp hc hcoercive w, hu, fun y ↦ ?_⟩
      obtain ⟨v, rfl⟩ := (toOfModel j hj p hp hc hcoercive).surjective y
      rw [ofModel_form_toOfModel, coe_toOfModel]
      exact huv v

end Model

end SemiboundedForm

end TauCeti
