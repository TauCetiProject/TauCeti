/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.CAR.WeightSpectrum
public import TauCeti.Algebra.Lie.GeneralLinear.Isotypic
import TauCeti.Algebra.Lie.GeneralLinear.CAR.Casimir
import TauCeti.Algebra.Lie.GeneralLinear.CAR.WeightUniqueness
import TauCeti.Algebra.Lie.GeneralLinear.Existence
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension

/-!
# Isotypy of the left-regular CAR module

Over an algebraically closed field of characteristic zero, the left-regular Clifford algebra of
the trace form is an isotypic `gl_N`-module. Its simple type has the half-shifted staircase highest
weight

`(N - 1/2, N - 3/2, ..., 1/2)`.

To identify the weight, write its coordinates as natural occupation counts shifted by `1/2`.
Highest-weight dominance makes the counts antitone, while the CAR cut identities bound their
proper prefix sums and fix their total. The trace-form Casimir scalar supplies the remaining
quadratic equality. The staircase majorization criterion then identifies every coordinate.

## Main results

* `TauCeti.IsGlHighestWeightVector.eq_glHalfStaircase`: every CAR highest-weight vector has the
  half-shifted staircase weight.
* `TauCeti.exists_isGlHighestWeightVector_glHalfStaircase_car`: every nonzero CAR submodule
  contains a highest-weight vector of that weight.
* `TauCeti.isIsotypicOfType_glIrreducible_car`: the left-regular CAR module is isotypic of the
  simple module with that highest weight.

## References

* D. Panyushev, *The exterior algebra and "spin" of an orthogonal g-module*, Transformation Groups
  6 (2001), 371–396, Proposition 2.4 and Example 2.5(1).
* D. Shlyakhtenko, *Failure of Strong Convergence of Matrices with Fermionic Entries*,
  arXiv:2606.28648, Section 2.3.
-/

public section

open scoped BigOperators TauCeti

namespace TauCeti

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

namespace IsGlHighestWeightVector

variable {K : Type*} [Field K] [CharZero K] {N : ℕ}

/-- Every highest-weight vector in the left-regular CAR module has the half-shifted staircase
weight `(N - 1/2, N - 3/2, ..., 1/2)`.

The result is uniform in the rank, including ranks zero and one. -/
theorem eq_glHalfStaircase {μ : Fin N → K}
    {v : CliffordAlgebra (traceQuadraticForm K (Fin N))}
    (hv : IsGlHighestWeightVector μ v) : μ = glHalfStaircase K N := by
  let a : Fin N → ℕ := fun i => (hv.exists_weight_apply_eq_natCast_add_inv_two i).choose
  have hμ (i : Fin N) : μ i = (a i : K) + (2 : K)⁻¹ :=
    (hv.exists_weight_apply_eq_natCast_add_inv_two i).choose_spec.2
  have ha : Antitone a :=
    hv.isGlDominantIntegral.antitone_of_eq_natCast_add_const (funext hμ)
  have haeq := eq_finRev_of_antitone_of_prefix_sum_le_of_sum_eq_of_casimir_eq
    a ha (prefix_sum_le_rev hv hμ) (sum_eq_rev hv hμ) (casimir_sum_eq_rev hv hμ)
  funext i
  rw [hμ i, congrFun haeq i]
  simpa only [one_div] using
    (Fin.natCast_rev_add_one_div_two_eq_glHalfStaircase (F := K) i)

end IsGlHighestWeightVector

/-- Every nonzero Lie submodule of the left-regular CAR module contains a highest-weight vector
of half-shifted staircase weight.

In particular, this identifies the highest weight occurring in every simple CAR submodule. -/
theorem exists_isGlHighestWeightVector_glHalfStaircase_car
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] (N : ℕ)
    (S : LieSubmodule K (Matrix (Fin N) (Fin N) K)
      (CliffordAlgebra (traceQuadraticForm K (Fin N)))) (hS : S ≠ ⊥) :
    ∃ v : S, IsGlHighestWeightVector (glHalfStaircase K N) v :=
  LieSubmodule.exists_isGlHighestWeightVector_of_forall
    (M := CliffordAlgebra (traceQuadraticForm K (Fin N)))
    (mu := glHalfStaircase K N)
    S hS (fun _μ _v hv => (isGlHighestWeightVector_coe_iff.mpr hv).eq_glHalfStaircase)

/-- Over an algebraically closed field of characteristic zero, the left-regular CAR module is
isotypic of the simple `gl_N`-module with half-shifted staircase highest weight. -/
theorem isIsotypicOfType_glIrreducible_car
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] (N : ℕ) :
    _root_.LieModule.IsIsotypicOfType K (Matrix (Fin N) (Fin N) K)
      (CliffordAlgebra (traceQuadraticForm K (Fin N)))
      (glIrreducible N (glHalfStaircase K N)) := by
  apply isIsotypicOfType_glIrreducible_of_forall_isGlHighestWeightVector
  intro μ v hv
  exact hv.eq_glHalfStaircase

end

end TauCeti
