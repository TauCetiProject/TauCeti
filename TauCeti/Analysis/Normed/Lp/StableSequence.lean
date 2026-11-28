/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Analysis.Normed.Lp.C0Ideal
public import TauCeti.Analysis.Normed.Operator.StableSequence

/-!
# Stable sequences in bounded products of normed rings

For an `ℕ`-indexed family of normed rings `A n`, the cofinite filter on `ℕ` is `Filter.atTop`, so
invertibility in the `c₀` quotient `lp A ∞ ⧸ lp.c0Ideal A` is precisely sequence stability
(`TauCeti.IsStableSequence`). In particular, for bounded families of operators on nontrivial
finite-dimensional normed spaces over a complete nontrivially normed field, quotient invertibility
is equivalent to an eventual uniform lower bound `‖x‖ ≤ M * ‖A n x‖`.

## Main results

* `lp.isUnit_mk_c0Ideal_iff_isStableSequence`: a bounded sequence in normed rings with `‖1‖ = 1`
  and summable geometric series is invertible modulo `lp.c0Ideal` if and only if it is stable.
* `lp.isStableSequence_iff_of_sub_mem_c0Ideal`: stability of bounded sequences is invariant modulo
  `lp.c0Ideal`.
* `lp.exists_conditionNumber_le_of_isUnit_mk_c0Ideal`: a unit modulo `lp.c0Ideal` has eventually
  bounded coordinate condition numbers.
* `lp.isUnit_mk_c0Ideal_iff_exists_forall_norm_le`: for bounded operator families on nontrivial
  finite-dimensional spaces, quotient invertibility is an eventual uniform lower bound.

## References

* A. Böttcher, *C\*-Algebras in Numerical Analysis*, Irish Math. Soc. Bull. 45 (2000), 57–101,
  Section 7.
* R. Hagen, S. Roch and B. Silbermann, *C\*-Algebras and Numerical Analysis*, Section 1.2.
-/

public section

open Filter Topology
open scoped ENNReal

namespace lp

section Ring

variable {A : ℕ → Type*} [∀ n, NormedRing (A n)]

/-- Two bounded sequences whose difference lies in `lp.c0Ideal` are simultaneously stable or
unstable. -/
theorem isStableSequence_iff_of_sub_mem_c0Ideal [∀ n, HasSummableGeomSeries (A n)]
    {a b : lp A ∞} (h : a - b ∈ c0Ideal A) :
    TauCeti.IsStableSequence (a : ∀ n, A n) ↔ TauCeti.IsStableSequence (b : ∀ n, A n) := by
  have ht : Tendsto (fun n ↦ ‖a n - b n‖) atTop (𝓝 0) := by
    simpa only [Nat.cofinite_eq_atTop, lp.coeFn_sub, Pi.sub_apply] using mem_c0Ideal.mp h
  exact TauCeti.isStableSequence_iff_of_tendsto_sub_zero ht

variable [∀ n, NormOneClass (A n)]

/-- A stable bounded sequence projects to a unit in `lp A ∞ ⧸ lp.c0Ideal A`. -/
theorem isUnit_mk_c0Ideal_of_isStableSequence {a : lp A ∞}
    (ha : TauCeti.IsStableSequence (a : ∀ n, A n)) :
    IsUnit (TwoSidedIdeal.Quotient.mk (c0Ideal A) a) := by
  rw [TauCeti.isStableSequence_def, ← Nat.cofinite_eq_atTop] at ha
  exact isUnit_mk_c0Ideal_of_eventually ha

/-- **Quotient characterization of stability.** In normed rings with `‖1‖ = 1` and summable
geometric series, the class of `a : lp A ∞` in `lp A ∞ ⧸ lp.c0Ideal A` is a unit if and only if
`a` is a stable sequence. -/
theorem isUnit_mk_c0Ideal_iff_isStableSequence [∀ n, HasSummableGeomSeries (A n)] {a : lp A ∞} :
    IsUnit (TwoSidedIdeal.Quotient.mk (c0Ideal A) a) ↔
      TauCeti.IsStableSequence (a : ∀ n, A n) := by
  rw [isUnit_mk_c0Ideal_iff, Nat.cofinite_eq_atTop, ← TauCeti.isStableSequence_def]

/-- A bounded sequence whose class modulo `lp.c0Ideal` is invertible has eventually bounded
coordinate condition numbers. -/
theorem exists_conditionNumber_le_of_isUnit_mk_c0Ideal [∀ n, HasSummableGeomSeries (A n)]
    {a : lp A ∞} (ha : IsUnit (TwoSidedIdeal.Quotient.mk (c0Ideal A) a)) :
    ∃ K : ℝ, ∀ᶠ n in atTop, TauCeti.conditionNumber (a n) ≤ K :=
  (isUnit_mk_c0Ideal_iff_isStableSequence.mp ha).exists_conditionNumber_le
    (Eventually.of_forall fun n ↦ norm_apply_le_norm ENNReal.top_ne_zero a n)

end Ring

section FiniteDimensional

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace 𝕜 (E n)]
  [∀ n, FiniteDimensional 𝕜 (E n)] [∀ n, Nontrivial (E n)]

/-- For a bounded sequence of operators on nontrivial finite-dimensional normed spaces over a
complete nontrivially normed field, invertibility modulo `lp.c0Ideal` is equivalent to an eventual
uniform lower bound. -/
theorem isUnit_mk_c0Ideal_iff_exists_forall_norm_le
    {A : lp (fun n ↦ E n →L[𝕜] E n) ∞} :
    IsUnit (TwoSidedIdeal.Quotient.mk (c0Ideal (fun n ↦ E n →L[𝕜] E n)) A) ↔
      ∃ M : ℝ, ∀ᶠ n in atTop, ∀ x, ‖x‖ ≤ M * ‖A n x‖ := by
  have (n : ℕ) : CompleteSpace (E n) := FiniteDimensional.completeSpace 𝕜 (E n)
  rw [isUnit_mk_c0Ideal_iff_isStableSequence, TauCeti.isStableSequence_iff_exists_forall_norm_le]

end FiniteDimensional

end lp
