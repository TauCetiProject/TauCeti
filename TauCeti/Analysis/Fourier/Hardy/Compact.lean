/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Hardy.Hankel
public import TauCeti.Analysis.Normed.Operator.Compact.FiniteRank

/-!
# Compact Hankel operators and Toeplitz semicommutators of continuous symbols

The Hankel operator `H_a = (1 - P) M_a |H²` of a continuous symbol `a` on the unit circle is
compact. Consequently, for an essentially bounded symbol `a` and a continuous symbol `b`, the
Toeplitz semicommutator `T_a T_b - T_(ab)` is compact. This is the compactness input to the
symbol calculus of Toeplitz operators modulo compact operators, from which their Fredholm theory
is built.

## Main results

* `TauCeti.hasFiniteRange_hankel_fourierLp`: the Hankel operator of a Fourier monomial has
  finite rank.
* `TauCeti.isCompactOperator_hankel_toLp`: the Hankel operator of a continuous symbol is compact.
* `TauCeti.isCompactOperator_toeplitz_comp_sub_toeplitz_toLp`: if the right symbol is continuous,
  the Toeplitz semicommutator is compact.

## Implementation notes

The Hankel operator of the monomial `e_n` sends the Hardy basis vector `e_k` to the nonnegative
mode `e_(n+k)` when `n + k ≥ 0`, which projection discards, so it vanishes on all but finitely
many basis vectors. Trigonometric polynomials are uniformly dense in the continuous symbols by
Mathlib's `span_fourier_closure_eq_top`, the Hankel symbol map is continuous for the sup norm, and
the compact operators form a closed subspace, so compactness passes from the monomials to every
continuous symbol.

## References

* J. B. Conway, *A Course in Functional Analysis*, second edition.
* E. Park, *Toeplitz operators*.
* A. Böttcher and B. Silbermann, *Analysis of Toeplitz Operators*, second edition, chapter 2.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

/-- The Hankel operator of the monomial `e_n` kills each Hardy basis vector `e_k` with
`n + k ≥ 0`, since the product `e_(n+k)` already lies in Hardy space. -/
private theorem hankel_fourierLp_hardyBasis {n : ℤ} {k : ℕ} (h : 0 ≤ n + k) :
    hankel (fourierLp (T := 1) ∞ n) (hardyBasis k) = 0 := by
  apply Subtype.ext
  rw [coe_hankel_apply, coe_hardyBasis, Submodule.coe_zero, sub_eq_zero, eq_comm,
    Submodule.starProjection_eq_self_iff, mem_hardySubmodule_iff]
  intro m hm
  rw [fourierCoeff_smul_fourierBasis, fourierCoeff_congr_ae (coeFn_fourierLp ∞ n),
    fourierCoeff_fourier, Pi.single_apply, ite_eq_right (by omega)]

/-- The Hankel operator of a Fourier monomial has finite rank. -/
theorem hasFiniteRange_hankel_fourierLp (n : ℤ) :
    (hankel (fourierLp (T := 1) ∞ n) : HardySpace →ₗ[ℂ] ↥hardySubmoduleᗮ).HasFiniteRange :=
  hardyBasis.hasFiniteRange_of_apply_eq_zero _ (Finset.range (-n).toNat) fun k hk ↦
    hankel_fourierLp_hardyBasis (by simp only [Finset.mem_range, not_lt] at hk; omega)

/-- **Compactness of continuous-symbol Hankel operators.** The Hankel operator of a continuous
symbol on the unit circle is compact. -/
theorem isCompactOperator_hankel_toLp (f : C(UnitAddCircle, ℂ)) :
    IsCompactOperator
      (hankel (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ f)) := by
  -- The continuous symbols whose Hankel operator is compact form a closed subspace.
  let Φ := hankel ∘L ContinuousMap.toLp (E := ℂ) ∞ (AddCircle.haarAddCircle (T := 1)) ℂ
  let K : Submodule ℂ C(UnitAddCircle, ℂ) :=
    (compactOperator (RingHom.id ℂ) HardySpace ↥hardySubmoduleᗮ).comap
      (Φ : C(UnitAddCircle, ℂ) →ₗ[ℂ] HardySpace →L[ℂ] ↥hardySubmoduleᗮ)
  have hK : IsClosed (K : Set C(UnitAddCircle, ℂ)) :=
    isClosed_setOfPred_isCompactOperator.preimage Φ.continuous
  -- It contains every Fourier monomial, hence every trigonometric polynomial.
  have hspan : Submodule.span ℂ (Set.range (fourier (T := 1))) ≤ K := by
    rw [Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    exact (hasFiniteRange_hankel_fourierLp n).isCompactOperator
  have hf : f ∈ (Submodule.span ℂ (Set.range (fourier (T := 1)))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    exact Submodule.mem_top
  exact Submodule.topologicalClosure_minimal _ hspan hK hf

/-- **Compactness of Toeplitz semicommutators.** For an essentially bounded symbol `a` and a
continuous symbol `b` on the unit circle, the semicommutator `T_a T_b - T_(ab)` is compact. -/
theorem isCompactOperator_toeplitz_comp_sub_toeplitz_toLp
    (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) (b : C(UnitAddCircle, ℂ)) :
    IsCompactOperator (toeplitz a ∘L
        toeplitz (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ b) -
      toeplitz (a • ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ b :
        Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1)))) := by
  rw [toeplitz_comp_sub_toeplitz, FunLike.coe_neg, ContinuousLinearMap.coe_comp]
  exact ((isCompactOperator_hankel_toLp b).clm_comp _).neg

end TauCeti
