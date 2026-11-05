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
  · exact (TauCeti.forall_expUnit_smul_mem_range_iff_eq_zero _ x).trans
      (mem_even_and_reverse_eq_neg_and_commutator_mem_iff_eq_zero _ hQ x).symm
  · simp only [mem_spinGroup_toUnits_range_iff, TauCeti.expUnit_coe,
      mem_spinGroup_iff_unitary_and_mem_even_and_conj_mem _ hQ hQ.exists_isUnit]
    exact (TauCeti.Lie.forall_exp_smul_mem_unitary_and_mem_and_conj_mem_iff
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
  · exact (TauCeti.forall_expUnit_smul_mem_range_iff_eq_zero _ x).trans
      (mem_even_and_reverse_eq_neg_and_commutator_mem_iff_eq_zero Q hQ x).symm
  · simp only [mem_spinGroup_toUnits_range_iff, TauCeti.expUnit_coe,
      mem_spinGroup_iff_unitary_and_mem_even_and_conj_mem Q hQ hQ.exists_isUnit]
    exact (TauCeti.Lie.forall_exp_smul_mem_unitary_and_mem_and_conj_mem_iff
      (E := (even Q).restrictScalars ℝ)
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
