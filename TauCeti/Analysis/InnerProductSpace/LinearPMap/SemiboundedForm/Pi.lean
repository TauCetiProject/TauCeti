/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.SemiboundedForm
public import TauCeti.Analysis.Normed.Operator.LinearPMap.PiLp

/-!
# Finite orthogonal sums of semibounded forms

Let `q i` be semibounded forms on inner product spaces `H i`, for `i` in a finite type `ι`. Their
**orthogonal sum** `TauCeti.SemiboundedForm.pi q` is the semibounded form on the Hilbert direct
sum `PiLp 2 H` with domain the product of the domains and

`(pi q) u v = ∑ i, q i (u i) (v i)`.

A common lower bound of the `q i` is a lower bound of the sum
(`TauCeti.SemiboundedForm.isLowerBound_pi`), so the sum keeps `γ = min γᵢ`. The form space of the
sum for a common admissible shift is isometric to the Hilbert direct sum of the form spaces
(`TauCeti.SemiboundedForm.formSpacePiEquiv`), so the sum of closed forms is closed
(`TauCeti.SemiboundedForm.isClosed_pi`). The operator it represents is the direct sum of the
represented operators (`TauCeti.SemiboundedForm.operator_pi`), `LinearPMap.piLpMap`: testing the
form against vectors supported in one coordinate separates the coordinates.

## Main declarations

* `TauCeti.SemiboundedForm.pi`: the orthogonal sum of a finite family of semibounded forms.
* `TauCeti.SemiboundedForm.isLowerBound_pi`: common lower bounds pass to the sum.
* `TauCeti.SemiboundedForm.formSpacePiEquiv`: the form space of the sum is isometric to the
  Hilbert direct sum of the form spaces.
* `TauCeti.SemiboundedForm.isClosed_pi`: the sum of closed forms is closed.
* `TauCeti.SemiboundedForm.operator_pi`: the represented operator is the direct sum.

## References

* G. Teschl, *Mathematical Methods in Quantum Mechanics*, 2nd ed., AMS (2014), §2.3,
  Theorem 2.13.
-/

public section

noncomputable section

open RCLike Set
open Submodule (piLp piLpProj coe_piLpProj piLpEquiv piLpEquiv_apply)
open scoped InnerProductSpace

namespace TauCeti

namespace SemiboundedForm

variable {𝕜 ι : Type*} [RCLike 𝕜] {H : ι → Type*} [∀ i, NormedAddCommGroup (H i)]
  [∀ i, InnerProductSpace 𝕜 (H i)] (q : ∀ i, SemiboundedForm 𝕜 (H i))

/-- Finitely many semibounded forms have a common lower bound: the least of their lower bounds. -/
private theorem exists_common_lowerBound [Finite ι] : ∃ γ : ℝ, ∀ i, (q i).IsLowerBound γ := by
  choose γ hγ using fun i ↦ (q i).exists_isLowerBound
  obtain ⟨M, hM⟩ := Finite.exists_ge γ
  exact ⟨M, fun i ↦ (q i).isLowerBound_iff.2 fun u ↦
    (mul_le_mul_of_nonneg_right (hM i) (sq_nonneg _)).trans ((q i).isLowerBound_iff.1 (hγ i) u)⟩

variable [Fintype ι]

/-- The form of the orthogonal sum, `u, v ↦ ∑ i, q i (u i) (v i)`, on the vectors of `PiLp 2 H`
whose coordinates lie in the form domains. -/
private def piForm :
    piLp 2 (fun i ↦ (q i).domain) →ₗ⋆[𝕜]
      piLp 2 (fun i ↦ (q i).domain) →ₗ[𝕜] 𝕜 :=
  ∑ i, ((q i).form.comp (piLpProj 2 (fun i ↦ (q i).domain) i)).compl₂
    (piLpProj 2 (fun i ↦ (q i).domain) i)

private theorem piForm_apply (u v : piLp 2 fun i ↦ (q i).domain) :
    piForm q u v = ∑ i, (q i).form (piLpProj 2 (fun i ↦ (q i).domain) i u)
      (piLpProj 2 (fun i ↦ (q i).domain) i v) := by
  simp [piForm, LinearMap.sum_apply]

/-- A common lower bound of the `q i` is a lower bound of `piForm q`. -/
private theorem mul_norm_sq_le_re_piForm {γ : ℝ} (hγ : ∀ i, (q i).IsLowerBound γ)
    (u : piLp 2 fun i ↦ (q i).domain) :
    γ * ‖(u : PiLp 2 H)‖ ^ 2 ≤ re (piForm q u u) := by
  rw [piForm_apply, map_sum, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [← coe_piLpProj]
  exact (q i).isLowerBound_iff.1 (hγ i) _

/-- The **orthogonal sum** of a finite family of semibounded forms: the form
`u, v ↦ ∑ i, q i (u i) (v i)` on the vectors of the Hilbert direct sum `PiLp 2 H` whose
coordinates lie in the form domains. -/
def pi : SemiboundedForm 𝕜 (PiLp 2 H) where
  domain := piLp 2 fun i ↦ (q i).domain
  form := piForm q
  form_apply_eq_star u v := by
    simp only [piForm_apply, star_sum]
    exact Finset.sum_congr rfl fun i _ ↦ (q i).form_apply_eq_star _ _
  exists_lowerBound :=
    (exists_common_lowerBound q).imp fun _ hγ ↦ mul_norm_sq_le_re_piForm q hγ

/-- The domain of the orthogonal sum: the vectors of `PiLp 2 H` whose coordinates lie in the form
domains. -/
@[simp]
theorem pi_domain : (pi q).domain = piLp 2 fun i ↦ (q i).domain :=
  (rfl)

/-- The `i`-th coordinate of a vector of the domain of the orthogonal sum, as a vector of the
`i`-th form domain: `Submodule.piLpProj` read on `(pi q).domain`. -/
def piCoord (i : ι) : (pi q).domain →ₗ[𝕜] (q i).domain :=
  piLpProj 2 (fun i ↦ (q i).domain) i

/-- `TauCeti.SemiboundedForm.piCoord q i` reads off the `i`-th coordinate. -/
@[simp]
theorem coe_piCoord (i : ι) (u : (pi q).domain) : (piCoord q i u : H i) = (u : PiLp 2 H) i :=
  coe_piLpProj i u

/-- The orthogonal sum is the sum of the forms of the coordinates. -/
@[simp]
theorem pi_form_apply (u v : (pi q).domain) :
    (pi q).form u v = ∑ i, (q i).form (piCoord q i u) (piCoord q i v) :=
  piForm_apply q u v

/-- **Lower bounds of an orthogonal sum.** A common lower bound `γ` of the forms `q i`, for
instance `min γᵢ`, is a lower bound of their orthogonal sum. -/
theorem isLowerBound_pi {γ : ℝ} (hγ : ∀ i, (q i).IsLowerBound γ) : (pi q).IsLowerBound γ :=
  (isLowerBound_iff _).2 (mul_norm_sq_le_re_piForm q hγ)

/-- The orthogonal sum of densely defined forms is densely defined. -/
theorem dense_pi_domain (hd : ∀ i, Dense ((q i).domain : Set (H i))) :
    Dense ((pi q).domain : Set (PiLp 2 H)) :=
  Submodule.dense_piLp_iff.mpr hd

/-- A common lower bound of the `q i` gives a shift admissible for every `q i` and for their
orthogonal sum. -/
theorem exists_isAdmissibleShift_pi :
    ∃ α, (pi q).IsAdmissibleShift α ∧ ∀ i, (q i).IsAdmissibleShift α := by
  obtain ⟨γ, hγ⟩ := exists_common_lowerBound q
  exact ⟨1 - γ, (pi q).isAdmissibleShift_iff.2 ⟨_, isLowerBound_pi q hγ, by linarith⟩,
    fun i ↦ (q i).isAdmissibleShift_iff.2 ⟨_, hγ i, by linarith⟩⟩

/-- The linear equivalence underlying `TauCeti.SemiboundedForm.formSpacePiEquiv`. -/
private def formSpacePiLinearEquiv {α : ℝ} (hα : (pi q).IsAdmissibleShift α)
    (hαi : ∀ i, (q i).IsAdmissibleShift α) :
    (pi q).FormSpace α hα ≃ₗ[𝕜] PiLp 2 fun i ↦ (q i).FormSpace α (hαi i) :=
  -- `LinearEquiv.ofEq` along `pi_domain` retypes `(pi q).domain` as `piLp 2 _`, so that each
  -- step of the composite rewrites with its own simp lemma in `formSpacePiLinearEquiv_apply`.
  ((pi q).toFormSpace hα).symm ≪≫ₗ LinearEquiv.ofEq _ _ (pi_domain q) ≪≫ₗ
    piLpEquiv 2 (fun i ↦ (q i).domain) ≪≫ₗ
    LinearEquiv.piCongrRight (fun i ↦ (q i).toFormSpace (hαi i)) ≪≫ₗ
    (WithLp.linearEquiv 2 𝕜 (∀ i, (q i).FormSpace α (hαi i))).symm

private theorem formSpacePiLinearEquiv_apply {α : ℝ} (hα : (pi q).IsAdmissibleShift α)
    (hαi : ∀ i, (q i).IsAdmissibleShift α) (u : (pi q).domain) (i : ι) :
    formSpacePiLinearEquiv q hα hαi ((pi q).toFormSpace hα u) i =
      (q i).toFormSpace (hαi i) (piCoord q i u) := by
  simp only [formSpacePiLinearEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    WithLp.coe_symm_linearEquiv, WithLp.ofLp_toLp, LinearEquiv.piCongrRight_apply,
    piLpEquiv_apply]
  exact congrArg _ (Subtype.ext (by rw [coe_piLpProj, LinearEquiv.coe_ofEq_apply, coe_piCoord]))

private theorem inner_formSpacePiLinearEquiv {α : ℝ} (hα : (pi q).IsAdmissibleShift α)
    (hαi : ∀ i, (q i).IsAdmissibleShift α) (x y : (pi q).FormSpace α hα) :
    ⟪formSpacePiLinearEquiv q hα hαi x, formSpacePiLinearEquiv q hα hαi y⟫_𝕜 = ⟪x, y⟫_𝕜 := by
  obtain ⟨u, rfl⟩ := ((pi q).toFormSpace hα).surjective x
  obtain ⟨v, rfl⟩ := ((pi q).toFormSpace hα).surjective y
  rw [PiLp.inner_apply, inner_toFormSpace, shiftedInner_def, pi_form_apply, PiLp.inner_apply,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [formSpacePiLinearEquiv_apply, formSpacePiLinearEquiv_apply, inner_toFormSpace,
    shiftedInner_def, coe_piCoord, coe_piCoord]

/-- **Form space of an orthogonal sum.** For a common admissible shift `α`, the form space of the
orthogonal sum is isometric to the Hilbert direct sum of the form spaces of the `q i`, sending
`u` to its coordinates `u i` (`TauCeti.SemiboundedForm.formSpacePiEquiv_apply`). -/
def formSpacePiEquiv {α : ℝ} (hα : (pi q).IsAdmissibleShift α)
    (hαi : ∀ i, (q i).IsAdmissibleShift α) :
    (pi q).FormSpace α hα ≃ₗᵢ[𝕜] PiLp 2 fun i ↦ (q i).FormSpace α (hαi i) :=
  (formSpacePiLinearEquiv q hα hαi).isometryOfInner (inner_formSpacePiLinearEquiv q hα hαi)

/-- `TauCeti.SemiboundedForm.formSpacePiEquiv` sends a vector of the domain of the orthogonal sum
to its coordinates. -/
@[simp]
theorem formSpacePiEquiv_apply {α : ℝ} (hα : (pi q).IsAdmissibleShift α)
    (hαi : ∀ i, (q i).IsAdmissibleShift α) (u : (pi q).domain) (i : ι) :
    formSpacePiEquiv q hα hαi ((pi q).toFormSpace hα u) i =
      (q i).toFormSpace (hαi i) (piCoord q i u) :=
  formSpacePiLinearEquiv_apply q hα hαi u i

/-- **The orthogonal sum of closed forms is closed.** -/
theorem isClosed_pi (hq : ∀ i, (q i).IsClosed) : (pi q).IsClosed := by
  obtain ⟨α, hα, hαi⟩ := exists_isAdmissibleShift_pi q
  have := fun i ↦ ((q i).isClosed_iff_completeSpace (hαi i)).1 (hq i)
  let e := formSpacePiEquiv q hα hαi
  rw [(pi q).isClosed_iff_completeSpace hα]
  exact (completeSpace_congr (e := e.toEquiv) e.isometry.isUniformEmbedding).mpr inferInstance

/-- **The operator of an orthogonal sum is the direct sum of the operators.** For densely
defined forms `q i`, the operator represented by their orthogonal sum is the direct sum
`LinearPMap.piLpMap 2` of the operators they represent. -/
theorem operator_pi (hd : ∀ i, Dense ((q i).domain : Set (H i))) :
    (pi q).operator (dense_pi_domain q hd) =
      LinearPMap.piLpMap 2 fun i ↦ (q i).operator (hd i) := by
  classical
  refine LinearPMap.eq_of_eq_graph (Submodule.ext fun ⟨x, h⟩ ↦ ?_)
  rw [mem_graph_operator_iff, LinearPMap.mem_graph_piLpMap_iff]
  simp only [mem_graph_operator_iff]
  constructor
  · rintro ⟨u, rfl, huv⟩ i
    refine ⟨piCoord q i u, coe_piCoord q i u, fun w ↦ ?_⟩
    -- Test against the vector with `w` in the `i`-th coordinate and `0` elsewhere.
    have hw : PiLp.single 2 i (w : H i) ∈ (pi q).domain :=
      Submodule.single_mem_piLp w.property
    have hci : piCoord q i ⟨_, hw⟩ = w := Subtype.ext (by simp)
    have hcj (j : ι) (hj : j ≠ i) : piCoord q j ⟨_, hw⟩ = 0 :=
      Subtype.ext (by simp [Pi.single_eq_of_ne hj])
    have := huv ⟨_, hw⟩
    rw [pi_form_apply, PiLp.inner_apply, Fintype.sum_eq_single i
      fun j hj ↦ by rw [hcj j hj, map_zero], Fintype.sum_eq_single i
      fun j hj ↦ by simp [Pi.single_eq_of_ne hj], hci] at this
    simpa using this
  · intro hx
    choose u hu huv using hx
    obtain rfl : x = WithLp.toLp 2 fun i ↦ (u i : H i) := PiLp.ext fun i ↦ (hu i).symm
    let u' : (pi q).domain := ⟨_, Submodule.toLp_mem_piLp u⟩
    have hui (i : ι) : piCoord q i u' = u i := Subtype.ext (coe_piCoord q i u')
    refine ⟨u', rfl, fun v ↦ ?_⟩
    rw [pi_form_apply, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hui, huv i (piCoord q i v), coe_piCoord]

end SemiboundedForm

end TauCeti
