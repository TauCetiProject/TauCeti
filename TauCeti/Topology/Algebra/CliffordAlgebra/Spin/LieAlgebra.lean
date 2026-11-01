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
algebra of a complex one. Every nondegenerate complex quadratic space is isometric to such a
coordinate space.

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

private theorem forall_expUnit_smul_mem_realCliffordSpinGroup_iff_of_neZero
    (p q : ℕ) [NeZero (p + q)] (x : CliffordAlgebra (realCliffordForm p q)) :
    (∀ t : ℝ, TauCeti.expUnit (t • x) ∈
        (spinGroup.toUnits (Q := realCliffordForm p q)).range) ↔
      x ∈ even (realCliffordForm p q) ∧
        reverse x = -x ∧
        ∀ v : Fin (p + q) → ℝ, x * ι (realCliffordForm p q) v -
          ι (realCliffordForm p q) v * x ∈
            LinearMap.range (ι (realCliffordForm p q)) := by
  let Q := realCliffordForm p q
  have hQ : Q.Nondegenerate := nondegenerate_realCliffordForm p q
  constructor
  · intro hline
    have hspin (t : ℝ) : exp (t • x) ∈ spinGroup Q := by
      have hu := (mem_spinGroup_toUnits_range_iff
        (TauCeti.expUnit (t • x))).mp (hline t)
      simpa only [Q, TauCeti.expUnit_coe] using hu
    have hcarrier (t : ℝ) :
        exp (t • x) ∈ unitary (CliffordAlgebra Q) ∧
          exp (t • x) ∈ even Q ∧
          ∀ v, involute (Q := Q) (exp (t • x)) * ι Q v * star (exp (t • x)) ∈
            LinearMap.range (ι Q) :=
      (mem_spinGroup_iff_unitary_even_and_involute_act_ι_mem_range_ι Q hQ
        hQ.exists_isUnit).mp (hspin t)
    have heven : x ∈ even Q :=
      TauCeti.mem_of_forall_exp_smul_mem (S := (even Q).toSubmodule)
        (Submodule.isClosed_of_isModuleTopology _) fun t ↦ (hcarrier t).2.1
    have hstar : star x = -x :=
      skewAdjoint.mem_iff.mp <|
        (TauCeti.forall_exp_smul_mem_unitary_iff_mem_skewAdjoint x).mp fun t ↦ (hcarrier t).1
    have hreverse : reverse x = -x := by
      rw [reverse_eq_star_of_mem_even ⟨x, heven⟩]
      exact hstar
    refine ⟨heven, hreverse, ?_⟩
    have hflow : ∀ (t : ℝ) (y : CliffordAlgebra Q), y ∈ LinearMap.range (ι Q) →
        exp (t • x) * y * exp (-(t • x)) ∈ LinearMap.range (ι Q) := by
      intro t y hy
      obtain ⟨w, rfl⟩ := hy
      have hact := (hcarrier t).2.2 w
      have hexpEven : exp (t • x) ∈ even Q := (hcarrier t).2.1
      have hscaled : star (t • x) = -(t • x) := by
        rw [CliffordAlgebra.star_smul, hstar, smul_neg]
      have hinvolute : involute (Q := Q) (exp (t • x)) = exp (t • x) :=
        involute_eq_of_mem_even (by
          rw [← even_toSubmodule Q]
          exact hexpEven)
      rw [hinvolute, star_exp, hscaled] at hact
      exact hact
    have hcomm := (TauCeti.Lie.forall_exp_smul_mul_mem_iff_forall_commutator_mem x
      (Submodule.isClosed_of_isModuleTopology (LinearMap.range (ι Q)))).mp hflow
    intro v
    simpa only [Q] using hcomm (ι Q v) ⟨v, rfl⟩
  · rintro ⟨heven, hreverse, hcomm⟩ t
    rw [mem_spinGroup_toUnits_range_iff, TauCeti.expUnit_coe]
    rw [mem_spinGroup_iff_unitary_even_and_involute_act_ι_mem_range_ι Q hQ hQ.exists_isUnit]
    have hstar : star x = -x := by
      rw [← reverse_eq_star_of_mem_even ⟨x, heven⟩]
      exact hreverse
    have hexpEven : exp (t • x) ∈ even Q := by
      apply NormedSpace.exp_mem (s := even Q)
        (Submodule.isClosed_of_isModuleTopology (even Q).toSubmodule)
      exact (even Q).toSubmodule.smul_mem t heven
    have hunitary : exp (t • x) ∈ unitary (CliffordAlgebra Q) :=
      (TauCeti.forall_exp_smul_mem_unitary_iff_mem_skewAdjoint x).mpr
        (skewAdjoint.mem_iff.mpr hstar) t
    refine ⟨hunitary, hexpEven, ?_⟩
    intro v
    have hflow := (TauCeti.Lie.forall_exp_smul_mul_mem_iff_forall_commutator_mem x
      (Submodule.isClosed_of_isModuleTopology (LinearMap.range (ι Q)))).mpr
        (fun y hy ↦ by
          obtain ⟨w, rfl⟩ := hy
          simpa only [Q] using hcomm w) t (ι Q v) ⟨v, rfl⟩
    have hscaled : star (t • x) = -(t • x) := by
      rw [CliffordAlgebra.star_smul, hstar, smul_neg]
    have hinvolute : involute (Q := Q) (exp (t • x)) = exp (t • x) :=
      involute_eq_of_mem_even (by
        rw [← even_toSubmodule Q]
        exact hexpEven)
    simpa only [TauCeti.expUnit_coe, hinvolute, star_exp, hscaled] using hflow

/-! ### Complex coordinate spaces: the two dimension cases -/

section Complex

variable {n : ℕ} (Q : QuadraticForm ℂ (Fin n → ℂ))

/-- The nontrivial case: here `Q` has an anisotropic vector, so membership in the Spin group is
unitarity, evenness and preservation of the generating vectors under twisted conjugation. -/
private theorem forall_expUnit_smul_mem_complexSpinGroup_iff_of_nontrivial
    [Nontrivial (Fin n → ℂ)] (hQ : Q.Nondegenerate) (x : CliffordAlgebra Q) :
    (∀ t : ℝ, TauCeti.expUnit (t • x) ∈ (spinGroup.toUnits (Q := Q)).range) ↔
      x ∈ even Q ∧ reverse x = -x ∧
        ∀ v : Fin n → ℂ, x * ι Q v - ι Q v * x ∈ LinearMap.range (ι Q) := by
  have hι : IsClosed ((LinearMap.range (ι Q)).restrictScalars ℝ : Set (CliffordAlgebra Q)) :=
    Submodule.isClosed_of_isModuleTopology (LinearMap.range (ι Q))
  have hinvolute {t : ℝ} (h : exp (t • x) ∈ even Q) :
      involute (Q := Q) (exp (t • x)) = exp (t • x) :=
    involute_eq_of_mem_even (by rw [← even_toSubmodule Q]; exact h)
  constructor
  · intro hline
    have hcarrier (t : ℝ) :
        exp (t • x) ∈ unitary (CliffordAlgebra Q) ∧ exp (t • x) ∈ even Q ∧
          ∀ v, involute (Q := Q) (exp (t • x)) * ι Q v * star (exp (t • x)) ∈
            LinearMap.range (ι Q) := by
      refine (mem_spinGroup_iff_unitary_even_and_involute_act_ι_mem_range_ι Q hQ
        hQ.exists_isUnit).mp ?_
      simpa only [TauCeti.expUnit_coe] using
        (mem_spinGroup_toUnits_range_iff (TauCeti.expUnit (t • x))).mp (hline t)
    have heven : x ∈ even Q :=
      TauCeti.mem_of_forall_exp_smul_mem (S := (even Q).toSubmodule.restrictScalars ℝ)
        (Submodule.isClosed_of_isModuleTopology (even Q).toSubmodule) fun t ↦ (hcarrier t).2.1
    have hstar : star x = -x :=
      skewAdjoint.mem_iff.mp <|
        (TauCeti.forall_exp_smul_mem_unitary_iff_mem_skewAdjoint x).mp fun t ↦ (hcarrier t).1
    refine ⟨heven, by rw [reverse_eq_star_of_mem_even ⟨x, heven⟩, hstar], ?_⟩
    have hflow : ∀ (t : ℝ) (y : CliffordAlgebra Q),
        y ∈ (LinearMap.range (ι Q)).restrictScalars ℝ →
          exp (t • x) * y * exp (-(t • x)) ∈ (LinearMap.range (ι Q)).restrictScalars ℝ := by
      rintro t _ ⟨w, rfl⟩
      have hact := (hcarrier t).2.2 w
      rwa [hinvolute (hcarrier t).2.1,
        TauCeti.star_exp_eq_exp_neg_of_exp_mem_unitary (hcarrier t).1] at hact
    intro v
    exact (TauCeti.Lie.forall_exp_smul_mul_mem_iff_forall_commutator_mem x hι).mp hflow
      (ι Q v) ⟨v, rfl⟩
  · rintro ⟨heven, hreverse, hcomm⟩ t
    rw [mem_spinGroup_toUnits_range_iff, TauCeti.expUnit_coe,
      mem_spinGroup_iff_unitary_even_and_involute_act_ι_mem_range_ι Q hQ hQ.exists_isUnit]
    have hstar : star x = -x := by
      rw [← reverse_eq_star_of_mem_even ⟨x, heven⟩, hreverse]
    have hexpEven : exp (t • x) ∈ even Q :=
      (Subalgebra.mem_restrictScalars ℝ).mp <| NormedSpace.exp_mem (R := ℝ)
        (s := (even Q).restrictScalars ℝ)
        (Submodule.isClosed_of_isModuleTopology (even Q).toSubmodule)
        (((even Q).restrictScalars ℝ).smul_mem heven t)
    have hunitary : exp (t • x) ∈ unitary (CliffordAlgebra Q) :=
      (TauCeti.forall_exp_smul_mem_unitary_iff_mem_skewAdjoint x).mpr
        (skewAdjoint.mem_iff.mpr hstar) t
    refine ⟨hunitary, hexpEven, fun v ↦ ?_⟩
    have hflow := (TauCeti.Lie.forall_exp_smul_mul_mem_iff_forall_commutator_mem x hι).mpr
      (by rintro _ ⟨w, rfl⟩; exact hcomm w) t (ι Q v) ⟨v, rfl⟩
    rwa [hinvolute hexpEven, TauCeti.star_exp_eq_exp_neg_of_exp_mem_unitary hunitary]

attribute [local instance 100] LieRing.ofAssociativeRing in
/-- The zero-dimensional case: the Spin group is trivial and the conditions force `x = 0`. -/
private theorem forall_expUnit_smul_mem_complexSpinGroup_iff_of_subsingleton
    [Subsingleton (Fin n → ℂ)] (hQ : Q.Nondegenerate) (x : CliffordAlgebra Q) :
    (∀ t : ℝ, TauCeti.expUnit (t • x) ∈ (spinGroup.toUnits (Q := Q)).range) ↔
      x ∈ even Q ∧ reverse x = -x ∧
        ∀ v : Fin n → ℂ, x * ι Q v - ι Q v * x ∈ LinearMap.range (ι Q) := by
  constructor
  · intro hline
    have hx : x = 0 := TauCeti.eq_of_forall_exp_smul_eq fun t ↦ by
      obtain ⟨s, hs⟩ := hline t
      rw [Subsingleton.elim s 1, map_one] at hs
      simpa only [TauCeti.expUnit_coe, Units.val_one, smul_zero, exp_zero] using
        (congrArg (fun u : (CliffordAlgebra Q)ˣ ↦ (u : CliffordAlgebra Q)) hs).symm
    subst x
    simp
  · intro hx
    have hxq : x ∈ quadraticLieSubalgebra Q :=
      (mem_quadraticLieSubalgebra_iff_mem_even_and_reverse_eq_neg_and_lie_ι_mem_range_ι Q
        hQ).mpr (by simpa only [Ring.lie_def] using hx)
    have hle : (quadraticLieSubalgebra Q).toSubmodule ≤ ⊥ :=
      quadraticLieSubalgebra_toSubmodule_le_of_bivector_mem Q fun a b ↦ by
        simp [Subsingleton.elim a 0, Subsingleton.elim b 0]
    rw [(Submodule.mem_bot ℂ).mp (hle hxq)]
    exact fun t ↦ ⟨1, by simp⟩

end Complex

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
  rcases p with _ | p
  · rcases q with _ | q
    · let Q := realCliffordForm 0 0
      let _ : Subsingleton (Fin 0 → ℝ) :=
        ⟨fun a b ↦ funext fun i ↦ Fin.elim0 i⟩
      constructor
      · intro hline
        have hexp (t : ℝ) : exp (t • x) = 1 := by
          obtain ⟨s, hs⟩ := hline t
          have hs_one : s = 1 := Subsingleton.elim _ _
          subst s
          have hs' := congrArg
            (fun u : (CliffordAlgebra Q)ˣ ↦ (u : CliffordAlgebra Q)) hs
          simpa only [TauCeti.expUnit_coe, map_one, Units.val_one] using hs'.symm
        have hderiv : HasDerivAt (fun t : ℝ ↦ exp (t • x)) x 0 := by
          simpa using hasDerivAt_exp_smul_const x (0 : ℝ)
        have hderiv_zero : HasDerivAt (fun t : ℝ ↦ exp (t • x)) 0 0 := by
          simpa only [hexp] using
            (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : CliffordAlgebra Q)))
        have hx : x = 0 := hderiv.unique hderiv_zero
        subst x
        simp
      · intro hx
        have hxq : x ∈ quadraticLieSubalgebra Q :=
          (mem_quadraticLieSubalgebra_iff_mem_even_and_reverse_eq_neg_and_lie_ι_mem_range_ι
            Q (nondegenerate_realCliffordForm 0 0)).mpr (by
              simpa only [Q, Ring.lie_def, Nat.add_zero] using hx)
        have hle : (quadraticLieSubalgebra Q).toSubmodule ≤ ⊥ :=
          quadraticLieSubalgebra_toSubmodule_le_of_bivector_mem Q fun a b ↦ by
            have ha : a = 0 := funext fun i ↦ Fin.elim0 i
            have hb : b = 0 := funext fun i ↦ Fin.elim0 i
            subst a
            subst b
            simp
        have hx_zero : x = 0 := (Submodule.mem_bot ℝ).mp (hle hxq)
        subst x
        intro t
        exact ⟨1, by simp⟩
    · let _ : NeZero (0 + (q + 1)) := ⟨by simp⟩
      exact forall_expUnit_smul_mem_realCliffordSpinGroup_iff_of_neZero 0 (q + 1) x
  · let _ : NeZero ((p + 1) + q) := ⟨by simp⟩
    exact forall_expUnit_smul_mem_realCliffordSpinGroup_iff_of_neZero (p + 1) q x

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
  · exact forall_expUnit_smul_mem_complexSpinGroup_iff_of_subsingleton Q hQ x
  · exact forall_expUnit_smul_mem_complexSpinGroup_iff_of_nontrivial Q hQ x

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
