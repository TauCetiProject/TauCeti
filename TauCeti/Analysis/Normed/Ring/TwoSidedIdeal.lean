/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Quotient
public import TauCeti.RingTheory.TwoSidedIdeal.Quotient

/-!
# Quotient norms on two-sided ring quotients

We equip the quotient `A ⧸ I` of a possibly nonunital, possibly noncommutative seminormed ring `A`
by a two-sided ideal `I : TwoSidedIdeal A` with its quotient seminorm, proving submultiplicativity
`‖x * y‖ ≤ ‖x‖ * ‖y‖`, completeness when `A` is complete, and definiteness when `I` is closed
(adapting the continuity-of-multiplication argument from `Ideal.Quotient.semiNormedCommRing` in
`Mathlib/Analysis/Normed/Group/Quotient.lean` to `TwoSidedIdeal`). When `A` is unital, we also
provide the resulting `SeminormedRing`, `NormedRing`, and `NormedAlgebra` instances on `A ⧸ I`.

## Main results

* `TwoSidedIdeal.Quotient.nonUnitalSeminormedRing` and
  `TwoSidedIdeal.Quotient.nonUnitalNormedRing`: quotient seminormed and normed ring structures on
  `A ⧸ I` for `I : TwoSidedIdeal A`.
* `TwoSidedIdeal.Quotient.seminormedRing`, `TwoSidedIdeal.Quotient.normedRing`, and
  `TwoSidedIdeal.Quotient.normedAlgebra`: unital and algebra counterparts on `R ⧸ I`.
-/

public section

namespace TwoSidedIdeal.Quotient

section NonUnital

variable {A : Type*} [NonUnitalSeminormedRing A] (I : TwoSidedIdeal A)

instance isClosed_toAddSubgroup [hI : IsClosed (I : Set A)] :
    IsClosed (I.toAddSubgroup : Set A) :=
  hI

noncomputable instance seminormedAddCommGroup : SeminormedAddCommGroup (A ⧸ I) :=
  inferInstanceAs <| SeminormedAddCommGroup (A ⧸ I.toAddSubgroup)

noncomputable instance normedAddCommGroup [IsClosed (I : Set A)] :
    NormedAddCommGroup (A ⧸ I) :=
  inferInstanceAs <| NormedAddCommGroup (A ⧸ I.toAddSubgroup)

instance completeSpace [CompleteSpace A] : CompleteSpace (A ⧸ I) :=
  QuotientAddGroup.completeSpace_left A I.toAddSubgroup

/-- The quotient projection `mk I : A →ₙ+* A ⧸ I` is contractive. -/
theorem norm_mk_le (a : A) : ‖mk I a‖ ≤ ‖a‖ := by
  rw [← quotientAddGroupMk_eq_mk]
  exact QuotientAddGroup.norm_mk_le_norm (S := I.toAddSubgroup)

/-- Every class in `A ⧸ I` has a representative of norm within `ε` of its quotient norm. -/
theorem exists_norm_mk_lt {I : TwoSidedIdeal A} (x : A ⧸ I) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, mk I a = x ∧ ‖a‖ < ‖x‖ + ε := by
  obtain ⟨a, ha, hlt⟩ := QuotientAddGroup.exists_norm_mk_lt (S := I.toAddSubgroup) x hε
  exact ⟨a, (quotientAddGroupMk_eq_mk I a).symm.trans ha, hlt⟩

/-- The quotient norm of `mk I a` is the infimum of `‖a + y‖` over `y ∈ I`. -/
theorem norm_mk_eq (a : A) : ‖mk I a‖ = sInf ((‖a + ·‖) '' (I : Set A)) := by
  have hmk : (QuotientAddGroup.mk' I.toAddSubgroup a : A ⧸ I) = mk I a := by
    rw [QuotientAddGroup.mk'_apply, quotientAddGroupMk_eq_mk]
  rw [← hmk, ← coe_toAddSubgroup]
  exact quotient_norm_mk_eq I.toAddSubgroup a

/-- The quotient projection `mk I` is continuous. -/
@[fun_prop]
theorem continuous_mk : Continuous (mk I) := by
  have hmk : (mk I : A → A ⧸ I) = (QuotientAddGroup.mk : A → A ⧸ I.toAddSubgroup) := by
    ext a
    exact (quotientAddGroupMk_eq_mk I a).symm
  rw [hmk]
  exact QuotientAddGroup.continuous_mk

noncomputable instance nonUnitalSeminormedRing : NonUnitalSeminormedRing (A ⧸ I) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le x y := le_of_forall_pos_le_add fun ε hε => by
    have h := ((Metric.nhds_basis_ball.prod_nhds Metric.nhds_basis_ball).tendsto_iff
      Metric.nhds_basis_ball).mp (continuous_mul.tendsto (‖x‖, ‖y‖)) ε hε
    simp only [Set.mem_prod, Metric.mem_ball, and_imp, Prod.forall, Prod.exists] at h
    rcases h with ⟨ε₁, ε₂, ⟨h₁, h₂⟩, h⟩
    obtain ⟨⟨a, rfl, ha⟩, ⟨b, rfl, hb⟩⟩ := exists_norm_mk_lt x h₁, exists_norm_mk_lt y h₂
    simp only [Real.dist_eq, abs_sub_lt_iff] at h
    specialize h ‖a‖ ‖b‖ ⟨by linarith, by linarith [norm_mk_le I a]⟩
      ⟨by linarith, by linarith [norm_mk_le I b]⟩
    calc
      ‖mk I a * mk I b‖ = ‖mk I (a * b)‖ := by rw [map_mul]
      _ ≤ ‖a‖ * ‖b‖ := (norm_mk_le I (a * b)).trans (norm_mul_le a b)
      _ ≤ ‖mk I a‖ * ‖mk I b‖ + ε := (sub_lt_iff_lt_add'.mp h.1).le

noncomputable instance nonUnitalNormedRing [IsClosed (I : Set A)] :
    NonUnitalNormedRing (A ⧸ I) :=
  { nonUnitalSeminormedRing I, normedAddCommGroup I with }

noncomputable instance nonUnitalSeminormedCommRing {A : Type*}
    [NonUnitalSeminormedCommRing A] (I : TwoSidedIdeal A) :
    NonUnitalSeminormedCommRing (A ⧸ I) where
  mul_comm := _root_.mul_comm

noncomputable instance nonUnitalNormedCommRing {A : Type*}
    [NonUnitalSeminormedCommRing A] (I : TwoSidedIdeal A) [IsClosed (I : Set A)] :
    NonUnitalNormedCommRing (A ⧸ I) where
  mul_comm := _root_.mul_comm

end NonUnital

section Unital

variable {R : Type*} [SeminormedRing R] (I : TwoSidedIdeal R)

noncomputable instance seminormedRing : SeminormedRing (R ⧸ I) where
  __ := ring I
  __ := nonUnitalSeminormedRing I

noncomputable instance normedRing [IsClosed (I : Set R)] : NormedRing (R ⧸ I) :=
  { seminormedRing I, normedAddCommGroup I with }

noncomputable instance seminormedCommRing {R : Type*} [SeminormedCommRing R]
    (I : TwoSidedIdeal R) : SeminormedCommRing (R ⧸ I) where
  mul_comm := _root_.mul_comm

noncomputable instance normedCommRing {R : Type*} [SeminormedCommRing R]
    (I : TwoSidedIdeal R) [IsClosed (I : Set R)] : NormedCommRing (R ⧸ I) where
  mul_comm := _root_.mul_comm

noncomputable instance normedAlgebra {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra 𝕜 R] :
    NormedAlgebra 𝕜 (R ⧸ I) :=
  { Submodule.Quotient.normedSpace I.asIdeal 𝕜, algebra I with }

end Unital

end TwoSidedIdeal.Quotient
