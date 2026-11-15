/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Generation.HilleYosida.Generation
public import TauCeti.Analysis.Semigroups.Generation.LumerPhillips

/-!
# The Hille--Yosida theorem for contraction and quasi-contraction semigroups

When the constant in the growth bound is `M = 1`, the Hille--Yosida resolvent-power estimates
`‖R(lambda, A) ^ n‖ ≤ 1 / (lambda - omega) ^ n` for all `n ≥ 1` are implied by the single
estimate `‖R(lambda, A)‖ ≤ 1 / (lambda - omega)`, by submultiplicativity of the operator norm.
This gives the classical form of the generation theorem, in which only the first power of the
resolvent is controlled:

* a densely defined operator `A` on a real Banach space generates a C₀-semigroup with
  `‖S(t)‖ ≤ e^{omega t}` exactly when `(omega, ∞)` lies in its resolvent set and
  `‖R(lambda, A)‖ ≤ 1 / (lambda - omega)` for `lambda > omega`;
* in particular `A` generates a contraction semigroup exactly when `(0, ∞)` lies in its
  resolvent set and `‖R(lambda, A)‖ ≤ 1 / lambda` for `lambda > 0`.

The contraction form is obtained through the Lumer--Phillips characterization, using that these
resolvent conditions are equivalent to m-dissipativity.

## Main results

* `TauCeti.Semigroups.exists_generator_eq_and_hasGrowthBound_one_iff_forall_norm_resolvent_le`:
  the Hille--Yosida characterization of quasi-contraction semigroups.
* `TauCeti.Semigroups.exists_contractionSemigroup_generator_eq_iff_forall_norm_resolvent_le`:
  the Hille--Yosida characterization of contraction semigroups.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Theorem II.3.5 and Corollary II.3.6.
* A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
  Chapter 1, Theorem 3.1 and Corollary 3.8.
-/

public section

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- **Hille--Yosida for quasi-contraction semigroups.** An unbounded operator `A` on a real
Banach space generates a strongly continuous semigroup with `‖S(t)‖ ≤ e^{omega t}` if and only if
its domain is dense, the half-line `(omega, ∞)` lies in its resolvent set, and
`‖R(lambda, A)‖ ≤ 1 / (lambda - omega)` for every `lambda > omega`. -/
theorem exists_generator_eq_and_hasGrowthBound_one_iff_forall_norm_resolvent_le
    (A : X →ₗ.[ℝ] X) (omega : ℝ) :
    (∃ S : StronglyContinuousSemigroup X, S.generator = A ∧ S.HasGrowthBound omega 1) ↔
      Dense (A.domain : Set X) ∧
        (∀ lambda : ℝ, omega < lambda → lambda ∈ LinearPMap.resolventSet A) ∧
        ∀ lambda : ℝ, omega < lambda →
          ‖LinearPMap.resolvent A lambda‖ ≤ (lambda - omega)⁻¹ := by
  rw [hilleYosida_generation_iff]
  refine ⟨fun ⟨_, hdense, hres, hpow⟩ => ⟨hdense, hres, fun lambda hlambda => ?_⟩,
    fun ⟨hdense, hres, hnorm⟩ => ⟨le_rfl, hdense, hres, fun n hn lambda hlambda => ?_⟩⟩
  · simpa using hpow 1 le_rfl lambda hlambda
  · calc ‖LinearPMap.resolvent A lambda ^ n‖ ≤ ‖LinearPMap.resolvent A lambda‖ ^ n :=
          norm_pow_le' _ (by omega)
      _ ≤ (lambda - omega)⁻¹ ^ n := by gcongr; exact hnorm lambda hlambda
      _ = 1 / (lambda - omega) ^ n := by rw [inv_pow, one_div]

/-- **Hille--Yosida for contraction semigroups.** An unbounded operator `A` on a real Banach
space generates a strongly continuous contraction semigroup if and only if its domain is dense,
every `lambda > 0` lies in its resolvent set, and `‖R(lambda, A)‖ ≤ 1 / lambda` for every
`lambda > 0`. -/
theorem exists_contractionSemigroup_generator_eq_iff_forall_norm_resolvent_le
    (A : X →ₗ.[ℝ] X) :
    (∃ S : ContractionSemigroup X, S.toStronglyContinuousSemigroup.generator = A) ↔
      Dense (A.domain : Set X) ∧
        (∀ lambda : ℝ, 0 < lambda → lambda ∈ LinearPMap.resolventSet A) ∧
        ∀ lambda : ℝ, 0 < lambda → ‖LinearPMap.resolvent A lambda‖ ≤ lambda⁻¹ := by
  rw [exists_contractionSemigroup_generator_eq_iff,
    isMDissipative_iff_forall_mem_resolventSet_and_norm_resolvent_le]

end TauCeti.Semigroups

end
