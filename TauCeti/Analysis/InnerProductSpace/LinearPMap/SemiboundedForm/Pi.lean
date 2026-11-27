/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.SemiboundedForm
public import TauCeti.Analysis.Normed.Operator.LinearPMap.PiLp
import TauCeti.Analysis.Normed.Lp.PiLp.Basic

/-!
# Finite orthogonal sums of semibounded forms

Let `q i` be semibounded forms on inner product spaces `H i`, for `i` in a finite type `ι`. Their
**orthogonal sum** `TauCeti.SemiboundedForm.pi q` is the semibounded form on the Hilbert direct
sum `PiLp 2 H` with domain the product of the domains and

`(pi q) u v = ∑ i, q i (u i) (v i)`.

A common lower bound of the `q i` is a lower bound of the sum
(`TauCeti.SemiboundedForm.isLowerBound_pi`), so the sum keeps `γ = min γᵢ`. The form space of the
sum for a common admissible shift is isometric to the Hilbert direct sum of the form spaces
(`TauCeti.SemiboundedForm.piFormSpaceEquiv`), so the sum is closed exactly when every `q i` is
(`TauCeti.SemiboundedForm.isClosed_pi_iff`). The operator it represents is the direct sum of the
represented operators (`TauCeti.SemiboundedForm.operator_pi`), `LinearPMap.piLpMap`: testing the
form against vectors supported in one coordinate separates the coordinates.

## Main declarations

* `TauCeti.SemiboundedForm.pi`: the orthogonal sum of a finite family of semibounded forms.
* `TauCeti.SemiboundedForm.mem_pi_domain`: `x` lies in the domain of the sum exactly when each
  coordinate `x i` lies in the domain of `q i`.
* `TauCeti.SemiboundedForm.isLowerBound_pi`: common lower bounds pass to the sum.
* `TauCeti.SemiboundedForm.piFormSpaceEquiv`: the form space of the sum is isometric to the
  Hilbert direct sum of the form spaces.
* `TauCeti.SemiboundedForm.isClosed_pi_iff`: the sum is closed if and only if every `q i` is.
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
theorem pi_domain : (pi q).domain = piLp 2 fun i ↦ (q i).domain :=
  (rfl)

variable {q} in
/-- A vector lies in the domain of the orthogonal sum exactly when each coordinate `x i` lies in
the domain of `q i`. -/
@[simp]
theorem mem_pi_domain {x : PiLp 2 H} : x ∈ (pi q).domain ↔ ∀ i, x i ∈ (q i).domain :=
  Submodule.mem_piLp

/-- A family of vectors `u i` of the form domains gives a vector of the domain of the orthogonal
sum. -/
theorem toLp_mem_pi_domain (u : ∀ i, (q i).domain) :
    WithLp.toLp 2 (fun i ↦ (u i : H i)) ∈ (pi q).domain :=
  Submodule.toLp_mem_piLp u

variable {q} in
/-- A vector of the `i`-th form domain placed in the `i`-th coordinate, with `0` elsewhere, lies in
the domain of the orthogonal sum. -/
theorem single_mem_pi_domain [DecidableEq ι] {i : ι} {w : H i} (hw : w ∈ (q i).domain) :
    PiLp.single 2 i w ∈ (pi q).domain :=
  Submodule.single_mem_piLp hw

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

/-- The orthogonal sum is densely defined if and only if every `q i` is densely defined. -/
theorem dense_pi_domain_iff :
    Dense ((pi q).domain : Set (PiLp 2 H)) ↔ ∀ i, Dense ((q i).domain : Set (H i)) :=
  Submodule.dense_piLp_iff

/-- The orthogonal sum of densely defined forms is densely defined. -/
theorem dense_pi_domain (hd : ∀ i, Dense ((q i).domain : Set (H i))) :
    Dense ((pi q).domain : Set (PiLp 2 H)) :=
  (dense_pi_domain_iff q).mpr hd

/-- Pairing the orthogonal sum with a vector `w` placed in the `i`-th coordinate, and `0`
elsewhere, gives the `i`-th form. -/
theorem pi_form_single [DecidableEq ι] (u : (pi q).domain) (i : ι) (w : (q i).domain) :
    (pi q).form u ⟨PiLp.single 2 i (w : H i), single_mem_pi_domain w.property⟩ =
      (q i).form (piCoord q i u) w := by
  rw [pi_form_apply, Fintype.sum_eq_single i fun j hj ↦ ?_]
  · exact congrArg _ (Subtype.ext (by simp))
  · refine (congrArg ((q j).form (piCoord q j u)) (Subtype.ext ?_)).trans (map_zero _)
    simp [Pi.single_eq_of_ne hj]

/-- There is a shift admissible for every `q i` and for their orthogonal sum. -/
theorem exists_isAdmissibleShift_pi :
    ∃ α, (pi q).IsAdmissibleShift α ∧ ∀ i, (q i).IsAdmissibleShift α := by
  obtain ⟨γ, hγ⟩ := exists_common_lowerBound q
  exact ⟨1 - γ, (pi q).isAdmissibleShift_iff.2 ⟨_, isLowerBound_pi q hγ, by linarith⟩,
    fun i ↦ (q i).isAdmissibleShift_iff.2 ⟨_, hγ i, by linarith⟩⟩

/-- The linear equivalence underlying `TauCeti.SemiboundedForm.piFormSpaceEquiv`. -/
private def piFormSpaceLinearEquiv {α : ℝ} (hα : (pi q).IsAdmissibleShift α)
    (hαi : ∀ i, (q i).IsAdmissibleShift α) :
    (pi q).FormSpace α hα ≃ₗ[𝕜] PiLp 2 fun i ↦ (q i).FormSpace α (hαi i) :=
  -- `LinearEquiv.ofEq` along `pi_domain` retypes `(pi q).domain` as `piLp 2 _`, so that each
  -- step of the composite rewrites with its own simp lemma in
  -- `piFormSpaceLinearEquiv_toFormSpace`.
  ((pi q).toFormSpace hα).symm ≪≫ₗ LinearEquiv.ofEq _ _ (pi_domain q) ≪≫ₗ
    piLpEquiv 2 (fun i ↦ (q i).domain) ≪≫ₗ
    LinearEquiv.piCongrRight (fun i ↦ (q i).toFormSpace (hαi i)) ≪≫ₗ
    (WithLp.linearEquiv 2 𝕜 (∀ i, (q i).FormSpace α (hαi i))).symm

private theorem piFormSpaceLinearEquiv_toFormSpace {α : ℝ} (hα : (pi q).IsAdmissibleShift α)
    (hαi : ∀ i, (q i).IsAdmissibleShift α) (u : (pi q).domain) (i : ι) :
    piFormSpaceLinearEquiv q hα hαi ((pi q).toFormSpace hα u) i =
      (q i).toFormSpace (hαi i) (piCoord q i u) := by
  simp only [piFormSpaceLinearEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    WithLp.coe_symm_linearEquiv, WithLp.ofLp_toLp, LinearEquiv.piCongrRight_apply,
    piLpEquiv_apply]
  exact congrArg _ (Subtype.ext (by rw [coe_piLpProj, LinearEquiv.coe_ofEq_apply, coe_piCoord]))

private theorem inner_piFormSpaceLinearEquiv {α : ℝ} (hα : (pi q).IsAdmissibleShift α)
    (hαi : ∀ i, (q i).IsAdmissibleShift α) (x y : (pi q).FormSpace α hα) :
    ⟪piFormSpaceLinearEquiv q hα hαi x, piFormSpaceLinearEquiv q hα hαi y⟫_𝕜 = ⟪x, y⟫_𝕜 := by
  obtain ⟨u, rfl⟩ := ((pi q).toFormSpace hα).surjective x
  obtain ⟨v, rfl⟩ := ((pi q).toFormSpace hα).surjective y
  simp [PiLp.inner_apply, shiftedInner_def, Finset.mul_sum, Finset.sum_add_distrib,
    piFormSpaceLinearEquiv_toFormSpace]

/-- **Form space of an orthogonal sum.** For a common admissible shift `α`, the form space of the
orthogonal sum is isometric to the Hilbert direct sum of the form spaces of the `q i`, sending
`u` to its coordinates `u i` (`TauCeti.SemiboundedForm.piFormSpaceEquiv_toFormSpace`). -/
def piFormSpaceEquiv {α : ℝ} (hα : (pi q).IsAdmissibleShift α)
    (hαi : ∀ i, (q i).IsAdmissibleShift α) :
    (pi q).FormSpace α hα ≃ₗᵢ[𝕜] PiLp 2 fun i ↦ (q i).FormSpace α (hαi i) :=
  (piFormSpaceLinearEquiv q hα hαi).isometryOfInner (inner_piFormSpaceLinearEquiv q hα hαi)

section FormSpace

variable {α : ℝ} (hα : (pi q).IsAdmissibleShift α) (hαi : ∀ i, (q i).IsAdmissibleShift α)

/-- `TauCeti.SemiboundedForm.piFormSpaceEquiv` sends a vector of the domain of the orthogonal sum
to its coordinates. -/
@[simp]
theorem piFormSpaceEquiv_toFormSpace (u : (pi q).domain) (i : ι) :
    piFormSpaceEquiv q hα hαi ((pi q).toFormSpace hα u) i =
      (q i).toFormSpace (hαi i) (piCoord q i u) :=
  piFormSpaceLinearEquiv_toFormSpace q hα hαi u i

/-- The inverse of `TauCeti.SemiboundedForm.piFormSpaceEquiv` assembles a family of vectors
`u i` of the form domains into the vector of the domain of the orthogonal sum with coordinates
`u i`. -/
@[simp]
theorem piFormSpaceEquiv_symm_toLp (u : ∀ i, (q i).domain) :
    (piFormSpaceEquiv q hα hαi).symm (WithLp.toLp 2 fun i ↦ (q i).toFormSpace (hαi i) (u i)) =
      (pi q).toFormSpace hα ⟨WithLp.toLp 2 fun i ↦ (u i : H i), toLp_mem_pi_domain q u⟩ := by
  rw [LinearIsometryEquiv.symm_apply_eq]
  ext i
  rw [piFormSpaceEquiv_toFormSpace]
  exact congrArg _ (Subtype.ext (by simp))

/-- `TauCeti.SemiboundedForm.piFormSpaceEquiv` commutes with the inclusions into `H i` and
`PiLp 2 H`. -/
theorem inclusion_piFormSpaceEquiv (x : (pi q).FormSpace α hα) (i : ι) :
    (q i).inclusion (hαi i) (piFormSpaceEquiv q hα hαi x i) = (pi q).inclusion hα x i := by
  obtain ⟨u, rfl⟩ := ((pi q).toFormSpace hα).surjective x
  rw [piFormSpaceEquiv_toFormSpace, inclusion_toFormSpace, inclusion_toFormSpace, coe_piCoord]

end FormSpace

/-- **Closed orthogonal sums.** The orthogonal sum is closed if and only if every `q i` is
closed. -/
theorem isClosed_pi_iff : (pi q).IsClosed ↔ ∀ i, (q i).IsClosed := by
  obtain ⟨α, hα, hαi⟩ := exists_isAdmissibleShift_pi q
  let e := piFormSpaceEquiv q hα hαi
  rw [(pi q).isClosed_iff_completeSpace hα,
    completeSpace_congr (e := e.toEquiv) e.isometry.isUniformEmbedding, PiLp.completeSpace_iff]
  exact forall_congr' fun i ↦ ((q i).isClosed_iff_completeSpace (hαi i)).symm

/-- **The orthogonal sum of closed forms is closed.** -/
theorem isClosed_pi (hq : ∀ i, (q i).IsClosed) : (pi q).IsClosed :=
  (isClosed_pi_iff q).mpr hq

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
    -- Test against the vector with `w` in the `i`-th coordinate and `0` elsewhere.
    refine ⟨piCoord q i u, coe_piCoord q i u, fun w ↦ ?_⟩
    rw [← pi_form_single, huv, PiLp.inner_apply, Fintype.sum_eq_single i fun j hj ↦ by
      simp [Pi.single_eq_of_ne hj]]
    simp
  · intro hx
    choose u hu huv using hx
    obtain rfl : x = WithLp.toLp 2 fun i ↦ (u i : H i) := PiLp.ext fun i ↦ (hu i).symm
    let u' : (pi q).domain := ⟨_, toLp_mem_pi_domain q u⟩
    have hui (i : ι) : piCoord q i u' = u i := Subtype.ext (coe_piCoord q i u')
    refine ⟨u', rfl, fun v ↦ ?_⟩
    rw [pi_form_apply, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hui, huv i (piCoord q i v), coe_piCoord]

end SemiboundedForm

end TauCeti
