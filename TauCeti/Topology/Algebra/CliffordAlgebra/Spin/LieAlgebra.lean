/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Units
public import TauCeti.LinearAlgebra.CliffordAlgebra.Quadratic.Lie.Characterization
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Star
public import TauCeti.Topology.Algebra.CliffordAlgebra.Normed
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Closed
import TauCeti.Geometry.Lie.Adjoint.InvariantSubmodule
import TauCeti.Geometry.Lie.Exponential.Unitary

/-!
# The Lie algebras of the real and complex Spin groups

For a real Clifford algebra of any signature, a one-parameter exponential family stays in the real
Spin group exactly when its generator is even, is negated by reversal, and preserves the
generating-vector subspace under commutators. These are precisely the intrinsic conditions that
characterize quadratic Clifford elements.

Consequently, the canonical coordinates on the Lie algebra of the ambient unit group identify the
Lie algebra of the closed real Spin subgroup with the quadratic Lie subalgebra.

The same holds for the Spin group of a nondegenerate quadratic form on a complex coordinate space
`ℂⁿ`, viewed as a closed subgroup of the units of the finite-dimensional real normed algebra
`CliffordAlgebra Q`. The exponential lines are still real, `t ↦ exp (t • x)` with `t : ℝ`, but
the Lie algebra they cut out is the complex quadratic Lie subalgebra. In particular it is stable
under complex scalars, so the real Lie algebra of the complex Spin group is the underlying real Lie
algebra of a complex one. (Every finite-dimensional nondegenerate complex quadratic space is
isometric to such a coordinate space; this remark is not formalized here.)

## Main results

* `CliffordAlgebra.forall_expUnit_smul_mem_realCliffordSpinGroup_iff_mem_quadraticLieSubalgebra`
  characterizes the exponential lines contained in a real Spin subgroup.
* `unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_mem_quadraticLieSubalgebra`
  identifies its closed-subgroup Lie algebra in Clifford-algebra coordinates.
* `CliffordAlgebra.forall_expUnit_smul_mem_complexSpinGroup_iff_mem_quadraticLieSubalgebra` and
  `unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_mem_quadraticLieSubalgebra_complex`
  are the same two statements for a nondegenerate quadratic form on `ℂⁿ`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.
-/

public section

noncomputable section

open Manifold NormedSpace
open scoped Manifold

namespace CliffordAlgebra

open TauCeti

attribute [local instance] TauCeti.normedAlgebraRatOfReal

attribute [local instance] starModule_of_trivialStar

/-! ### The shared exponential-line arguments -/

section Abstract

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- For a homomorphism from a trivial group into the units, an exponential line lies in its range
exactly when its generator vanishes. -/
private theorem forall_expUnit_smul_mem_range_iff_eq_zero {G : Type*} [Group G] [Subsingleton G]
    (f : G →* Aˣ) (x : A) : (∀ t : ℝ, TauCeti.expUnit (t • x) ∈ f.range) ↔ x = 0 := by
  refine ⟨fun h ↦ TauCeti.eq_of_forall_exp_smul_eq fun t ↦ ?_, by rintro rfl t; exact ⟨1, by simp⟩⟩
  obtain ⟨s, hs⟩ := h t
  rw [Subsingleton.elim s 1, map_one] at hs
  simpa only [TauCeti.expUnit_coe, Units.val_one, smul_zero, exp_zero] using
    (congrArg Units.val hs).symm

variable [StarRing A] [ContinuousStar A] [StarModule ℝ A]

/-- An exponential line consists of unitaries lying in a closed subalgebra `E` whose conjugation
preserves a closed subspace `V` exactly when its generator lies in `E`, is skew-adjoint, and
brackets `V` into itself. -/
private theorem forall_exp_smul_mem_unitary_and_mem_and_conj_mem_iff {E : Subalgebra ℝ A}
    (hE : IsClosed (E : Set A)) {V : Submodule ℝ A} (hV : IsClosed (V : Set A)) (x : A) :
    (∀ t : ℝ, exp (t • x) ∈ unitary A ∧ exp (t • x) ∈ E ∧
        ∀ y ∈ V, exp (t • x) * y * star (exp (t • x)) ∈ V) ↔
      x ∈ E ∧ star x = -x ∧ ∀ y ∈ V, x * y - y * x ∈ V := by
  constructor
  · intro h
    refine ⟨TauCeti.mem_of_forall_exp_smul_mem (S := Subalgebra.toSubmodule E) hE
        fun t ↦ (h t).2.1,
      skewAdjoint.mem_iff.mp <|
        (TauCeti.forall_exp_smul_mem_unitary_iff_mem_skewAdjoint x).mp fun t ↦ (h t).1,
      (TauCeti.Lie.forall_exp_smul_mul_mem_iff_forall_commutator_mem x hV).mp fun t y hy ↦ ?_⟩
    simpa only [TauCeti.star_exp_eq_exp_neg_of_exp_mem_unitary (h t).1] using (h t).2.2 y hy
  · rintro ⟨hxE, hstar, hcomm⟩ t
    have hunitary : exp (t • x) ∈ unitary A :=
      (TauCeti.forall_exp_smul_mem_unitary_iff_mem_skewAdjoint x).mpr
        (skewAdjoint.mem_iff.mpr hstar) t
    refine ⟨hunitary, NormedSpace.exp_mem hE (E.smul_mem hxE t), fun y hy ↦ ?_⟩
    rw [TauCeti.star_exp_eq_exp_neg_of_exp_mem_unitary hunitary]
    exact (TauCeti.Lie.forall_exp_smul_mul_mem_iff_forall_commutator_mem x hV).mpr hcomm t y hy

end Abstract

section Algebraic

/-- On even elements reversal is Clifford conjugation, so the conditions of
`forall_exp_smul_mem_unitary_and_mem_and_conj_mem_iff` are the intrinsic quadratic conditions. -/
private theorem mem_even_and_star_eq_neg_and_commutator_mem_iff {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (Q : QuadraticForm R M) (x : CliffordAlgebra Q) :
    (x ∈ even Q ∧ star x = -x ∧
        ∀ y ∈ LinearMap.range (ι Q), x * y - y * x ∈ LinearMap.range (ι Q)) ↔
      x ∈ even Q ∧ reverse x = -x ∧ ∀ v, x * ι Q v - ι Q v * x ∈ LinearMap.range (ι Q) := by
  refine and_congr_right fun he ↦ and_congr ?_
    ⟨fun h v ↦ h _ ⟨v, rfl⟩, fun h ↦ by rintro _ ⟨v, rfl⟩; exact h v⟩
  rw [reverse_eq_star_of_mem_even ⟨x, he⟩]

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Invertible (2 : K)] (Q : QuadraticForm K V)

/-- For a nondegenerate form with an anisotropic vector, membership in the Spin group is
unitarity, evenness and preservation of the generating vectors under conjugation. -/
private theorem mem_spinGroup_iff_unitary_and_mem_even_and_conj_mem (hQ : Q.Nondegenerate)
    (hv : ∃ v, IsUnit (Q v)) (e : CliffordAlgebra Q) :
    e ∈ spinGroup Q ↔ e ∈ unitary (CliffordAlgebra Q) ∧ e ∈ even Q ∧
      ∀ y ∈ LinearMap.range (ι Q), e * y * star e ∈ LinearMap.range (ι Q) := by
  rw [mem_spinGroup_iff_unitary_even_and_involute_act_ι_mem_range_ι Q hQ hv]
  refine and_congr_right fun _ ↦ and_congr_right fun he ↦ ?_
  rw [involute_eq_of_mem_even (by rw [← even_toSubmodule Q]; exact he)]
  exact ⟨fun h ↦ by rintro _ ⟨m, rfl⟩; exact h m, fun h m ↦ h _ ⟨m, rfl⟩⟩

attribute [local instance 100] LieRing.ofAssociativeRing in
/-- Over the zero space the quadratic conditions force `x = 0`. -/
private theorem mem_even_and_reverse_eq_neg_and_commutator_mem_iff_eq_zero [Subsingleton V]
    (hQ : Q.Nondegenerate) (x : CliffordAlgebra Q) :
    (x ∈ even Q ∧ reverse x = -x ∧ ∀ v, x * ι Q v - ι Q v * x ∈ LinearMap.range (ι Q)) ↔
      x = 0 := by
  refine ⟨fun hx ↦ ?_, by rintro rfl; simp⟩
  have hxq : x ∈ quadraticLieSubalgebra Q :=
    (mem_quadraticLieSubalgebra_iff_mem_even_and_reverse_eq_neg_and_lie_ι_mem_range_ι Q
      hQ).mpr (by simpa only [Ring.lie_def] using hx)
  have hle : (quadraticLieSubalgebra Q).toSubmodule ≤ ⊥ :=
    quadraticLieSubalgebra_toSubmodule_le_of_bivector_mem Q fun a b ↦ by
      simp [Subsingleton.elim a 0, Subsingleton.elim b 0]
  exact (Submodule.mem_bot K).mp (hle hxq)

end Algebraic

attribute [local instance 100] LieRing.ofAssociativeRing

/-- An exponential line in a real Clifford algebra stays in its Spin group exactly when its
generator is even, is negated by reversal, and brackets every generating vector back into the
generating-vector subspace. -/
theorem
forall_expUnit_smul_mem_realCliffordSpinGroup_iff_mem_even_and_reverse_eq_neg_and_lie_ι_mem_range_ι
    (p q : ℕ) (x : CliffordAlgebra (realCliffordForm p q)) :
    (∀ t : ℝ, TauCeti.expUnit (t • x) ∈
        (spinGroup.toUnits (Q := realCliffordForm p q)).range) ↔
      x ∈ even (realCliffordForm p q) ∧
        reverse x = -x ∧
        ∀ v : Fin (p + q) → ℝ, x * ι (realCliffordForm p q) v -
          ι (realCliffordForm p q) v * x ∈
            LinearMap.range (ι (realCliffordForm p q)) := by
  have hQ := nondegenerate_realCliffordForm p q
  rcases subsingleton_or_nontrivial (Fin (p + q) → ℝ) with _ | _
  · exact (forall_expUnit_smul_mem_range_iff_eq_zero _ x).trans
      (mem_even_and_reverse_eq_neg_and_commutator_mem_iff_eq_zero _ hQ x).symm
  · simp only [mem_spinGroup_toUnits_range_iff, TauCeti.expUnit_coe,
      mem_spinGroup_iff_unitary_and_mem_even_and_conj_mem _ hQ hQ.exists_isUnit]
    exact (forall_exp_smul_mem_unitary_and_mem_and_conj_mem_iff
      (Submodule.isClosed_of_isModuleTopology (even (realCliffordForm p q)).toSubmodule)
      (Submodule.isClosed_of_isModuleTopology (LinearMap.range (ι (realCliffordForm p q)))) x).trans
        (mem_even_and_star_eq_neg_and_commutator_mem_iff _ x)

/-- An exponential line lies in a real Spin group exactly when its generator is a
quadratic Clifford element. -/
-- Normalize the whole exponential-line predicate before range membership expands.
@[simp↓]
theorem forall_expUnit_smul_mem_realCliffordSpinGroup_iff_mem_quadraticLieSubalgebra
    (p q : ℕ) (x : CliffordAlgebra (realCliffordForm p q)) :
    (∀ t : ℝ, TauCeti.expUnit (t • x) ∈
        (spinGroup.toUnits (Q := realCliffordForm p q)).range) ↔
      x ∈ quadraticLieSubalgebra (realCliffordForm p q) := by
  rw [
forall_expUnit_smul_mem_realCliffordSpinGroup_iff_mem_even_and_reverse_eq_neg_and_lie_ι_mem_range_ι,
    mem_quadraticLieSubalgebra_iff_mem_even_and_reverse_eq_neg_and_lie_ι_mem_range_ι
      (realCliffordForm p q) (nondegenerate_realCliffordForm p q)]
  simp only [Ring.lie_def]

/-- In canonical units coordinates, the Lie algebra of a closed real Spin subgroup is the
quadratic Lie subalgebra of its Clifford algebra. -/
@[simp↓]
theorem
    unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_mem_quadraticLieSubalgebra
    (p q : ℕ) (x : CliffordAlgebra (realCliffordForm p q)) :
    (TauCeti.Lie.unitsLieAlgebraLieEquiv
        (R := CliffordAlgebra (realCliffordForm p q))).symm x ∈
        TauCeti.Lie.lieSubalgebraOfSubgroup
          (I := 𝓘(ℝ, CliffordAlgebra (realCliffordForm p q)))
          (spinGroup.toUnits (Q := realCliffordForm p q)).range ↔
      x ∈ quadraticLieSubalgebra (realCliffordForm p q) := by
  rw [TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff
    (by simpa only [MonoidHom.coe_range] using
      (isClosed_range_spinGroup_toUnits (realCliffordForm p q)
        (nondegenerate_realCliffordForm p q))),
    forall_expUnit_smul_mem_realCliffordSpinGroup_iff_mem_quadraticLieSubalgebra]

/-! ### Complex coordinate spaces -/

section Complex

variable {n : ℕ} (Q : QuadraticForm ℂ (Fin n → ℂ))

/-- An exponential line in the Clifford algebra of a nondegenerate quadratic form on `ℂⁿ` stays in
its Spin group exactly when its generator is even, is negated by reversal, and brackets every
generating vector back into the generating-vector subspace. The exponential line is real:
`t` ranges over `ℝ`. -/
theorem
forall_expUnit_smul_mem_complexSpinGroup_iff_mem_even_and_reverse_eq_neg_and_lie_ι_mem_range_ι
    (hQ : Q.Nondegenerate) (x : CliffordAlgebra Q) :
    (∀ t : ℝ, TauCeti.expUnit (t • x) ∈ (spinGroup.toUnits (Q := Q)).range) ↔
      x ∈ even Q ∧ reverse x = -x ∧ ∀ v : Fin n → ℂ, ⁅x, ι Q v⁆ ∈ LinearMap.range (ι Q) := by
  simp only [Ring.lie_def]
  rcases subsingleton_or_nontrivial (Fin n → ℂ) with _ | _
  · exact (forall_expUnit_smul_mem_range_iff_eq_zero _ x).trans
      (mem_even_and_reverse_eq_neg_and_commutator_mem_iff_eq_zero Q hQ x).symm
  · simp only [mem_spinGroup_toUnits_range_iff, TauCeti.expUnit_coe,
      mem_spinGroup_iff_unitary_and_mem_even_and_conj_mem Q hQ hQ.exists_isUnit]
    exact (forall_exp_smul_mem_unitary_and_mem_and_conj_mem_iff (E := (even Q).restrictScalars ℝ)
      (Submodule.isClosed_of_isModuleTopology (even Q).toSubmodule)
      (V := (LinearMap.range (ι Q)).restrictScalars ℝ)
      (Submodule.isClosed_of_isModuleTopology (LinearMap.range (ι Q))) x).trans
        (mem_even_and_star_eq_neg_and_commutator_mem_iff Q x)

/-- An exponential line lies in the Spin group of a nondegenerate quadratic form on `ℂⁿ` exactly
when its generator is a quadratic Clifford element. -/
-- Normalize the whole exponential-line predicate before range membership expands.
@[simp↓]
theorem forall_expUnit_smul_mem_complexSpinGroup_iff_mem_quadraticLieSubalgebra
    (hQ : Q.Nondegenerate) (x : CliffordAlgebra Q) :
    (∀ t : ℝ, TauCeti.expUnit (t • x) ∈ (spinGroup.toUnits (Q := Q)).range) ↔
      x ∈ quadraticLieSubalgebra Q := by
  rw [
forall_expUnit_smul_mem_complexSpinGroup_iff_mem_even_and_reverse_eq_neg_and_lie_ι_mem_range_ι
      Q hQ, mem_quadraticLieSubalgebra_iff_mem_even_and_reverse_eq_neg_and_lie_ι_mem_range_ι Q hQ]

/-- In canonical units coordinates, the real Lie algebra of the closed Spin subgroup of a
nondegenerate quadratic form on `ℂⁿ` is the complex quadratic Lie subalgebra of its Clifford
algebra. In particular it is stable under complex scalars. -/
@[simp↓]
theorem
    unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_mem_quadraticLieSubalgebra_complex
    (hQ : Q.Nondegenerate) (x : CliffordAlgebra Q) :
    (TauCeti.Lie.unitsLieAlgebraLieEquiv (R := CliffordAlgebra Q)).symm x ∈
        TauCeti.Lie.lieSubalgebraOfSubgroup (I := 𝓘(ℝ, CliffordAlgebra Q))
          (spinGroup.toUnits (Q := Q)).range ↔
      x ∈ quadraticLieSubalgebra Q := by
  rw [TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff
    (by simpa only [MonoidHom.coe_range] using isClosed_range_spinGroup_toUnits Q hQ),
    forall_expUnit_smul_mem_complexSpinGroup_iff_mem_quadraticLieSubalgebra Q hQ]

end Complex

end CliffordAlgebra
