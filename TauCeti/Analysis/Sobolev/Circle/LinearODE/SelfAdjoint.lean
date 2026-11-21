/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.CommonDomain
public import TauCeti.Analysis.Sobolev.Circle.LinearODE.Eigenbasis
import TauCeti.Topology.Algebra.Module.ComplexSmulI

/-!
# The asymptotic operator of a loop as a self-adjoint operator

Let `F` be a finite-dimensional complex inner product space and `S` a continuous loop of
infinitesimally symplectic real-linear maps of `F`. The asymptotic operator
`A ζ = J₀ (ζ' - S_t ζ)` of Floer theory is the bounded operator `I • loopOperator T S` from
`H¹(F)` to `H⁰(F)`. Read through the inclusion `ι : H¹(F) → H⁰(F)` it is an unbounded operator on
the real Hilbert space `H⁰(F)` with domain `H¹(F)`,
`ι.domainOperator (I • loopOperator T S)` (`ContinuousLinearMap.domainOperator`).

When the loop is nondegenerate, that is, `ζ' = S_t ζ` has no nonzero periodic solution, this
operator is self-adjoint (`TauCeti.CircleSobolev.isSelfAdjoint_domainOperator_I_smul_loopOperator`):
it is symmetric by `TauCeti.CircleSobolev.real_inner_I_smul_loopOperator_comm` and invertible.
It has compact resolvent
(`TauCeti.CircleSobolev.hasCompactResolvent_domainOperator_I_smul_loopOperator`), by Rellich's
theorem for the inclusion `H¹ → H⁰` (`TauCeti.CircleSobolev.isCompactOperator_inclusion`). These
are the self-adjoint operators with compact resolvent on the fixed Hilbert space `H⁰(F)` and the
common domain `H¹(F)` along which the spectral flow of a path of loops is taken.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2 (the self-adjoint operator `J₀ ∂_t + S` on `W^{1,2}(S¹)`).
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc. 27
  (1995), 1–33, Section 4.
-/

public section

noncomputable section

open Complex

namespace TauCeti.CircleSobolev

variable (T : ℝ) [Fact (0 < T)] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F] {S : C(AddCircle T, F →L[ℝ] F)}

private local instance : CompleteSpace F := FiniteDimensional.completeSpace ℂ F

/-- **The asymptotic operator of a nondegenerate loop is self-adjoint.** If every `S_t` is
infinitesimally symplectic and `ζ' = S_t ζ` has no nonzero periodic solution, the operator
`J₀ (d/dt - S_t)` on `H⁰(F)` with domain `H¹(F)` is self-adjoint. -/
theorem isSelfAdjoint_domainOperator_I_smul_loopOperator
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (hL : (loopOperator T S).IsInvertible) :
    IsSelfAdjoint (((inclusion (E := F) zero_le_one).restrictScalars ℝ).domainOperator
      (I • loopOperator T S) (inclusion_injective zero_le_one)) :=
  ContinuousLinearMap.isSelfAdjoint_domainOperator_of_isInvertible
    (real_inner_I_smul_loopOperator_comm T S hS)
    ((ContinuousLinearMap.isInvertible_I_smul_iff _).2 hL)

/-- **The asymptotic operator of a nondegenerate loop has compact resolvent.** If `ζ' = S_t ζ`
has no nonzero periodic solution, the operator `J₀ (d/dt - S_t)` on `H⁰(F)` with domain `H¹(F)`
has compact resolvent. -/
theorem hasCompactResolvent_domainOperator_I_smul_loopOperator
    (hL : (loopOperator T S).IsInvertible) :
    (((inclusion (E := F) zero_le_one).restrictScalars ℝ).domainOperator
      (I • loopOperator T S) (inclusion_injective zero_le_one)).HasCompactResolvent :=
  ContinuousLinearMap.hasCompactResolvent_domainOperator (c := 0)
    (isCompactOperator_inclusion (E := F) zero_lt_one)
    (ContinuousLinearMap.isInvertible_zero_smul_sub_iff.2
      ((ContinuousLinearMap.isInvertible_I_smul_iff _).2 hL))

end TauCeti.CircleSobolev
