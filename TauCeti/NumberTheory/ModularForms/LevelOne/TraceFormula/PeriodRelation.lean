/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.UpperTriangularSum

/-!
# The Popa–Zagier period relation

Popa and Zagier's proof of the Eichler–Selberg trace formula starts from an element `T̃ₙ` of the
group ring `ℛₙ = ℚ[ℳₙ]` satisfying the *period relation*
`(A)  (1 - S)·T̃ₙ - Tₙ^∞·(1 - S) ∈ (1 - T)·ℛₙ`,
where `S = (0 -1; 1 0)` and `T = (1 1; 0 1)` act on `ℳₙ` by left and right multiplication and
`Tₙ^∞` is the formal sum of the upper-triangular representatives of `Γ \ ℳₙ`. This file defines
the predicate `TauCeti.TraceFormulaMatrixModule.PeriodRelation k n ξ` expressing (A) for `ξ ∈ ℛₙ`
and proves that it has a solution for every `n`.

As in Popa–Zagier, who say that solutions exist "as in [CZ]", existence is proved abstractly rather
than by exhibiting a solution. It is a coinvariance statement. The right translate `Tₙ^∞·S` is the
formal sum of another set of representatives of `Γ \ ℳₙ`, so `Tₙ^∞·(1 - S)` has vanishing sums along
every orbit of `SL(2, ℤ)`, that is, it lies in the coinvariant kernel of the left action. As `S` and
`T` generate `SL(2, ℤ)`, this kernel is `(1 - S)·ℛₙ + (1 - T)·ℛₙ`, which gives a solution. The
explicit solution of Popa–Zagier's eq. (15) is not constructed here: they deduce (A) for it from the
relations (B) and the coset identity `⟨T̃ₙ, K⟩ = -1`, and it is deferred to milestone (vi) of the
`ModularForms` roadmap (Layer 11).

Membership in `(1 - T)·ℛₙ` is decided by the criterion of Popa–Zagier §3: an element of `ℛₙ` lies in
`(1 - T)·ℛₙ` if and only if its coefficients sum to zero along every orbit of `Γ_∞ = ⟨T⟩` on `ℳₙ`.

## Main definitions

* `TauCeti.TraceFormulaMatrixModule.PeriodRelation k n ξ`: the element `ξ ∈ ℛₙ` satisfies the
  period relation (A).

## Main results

* `TauCeti.TraceFormulaMatrixModule.mem_range_one_sub_T_iff`: an element of `k[ℳₙ]` lies in
  `(1 - T)·k[ℳₙ]` if and only if its coefficient sums along the `⟨T⟩`-orbits vanish.
* `TauCeti.TraceFormulaMatrixModule.PeriodRelation.add` and
  `TauCeti.TraceFormulaMatrixModule.PeriodRelation.sub_mem`: solutions of (A) are determined up to
  elements `η` with `(1 - S)·η ∈ (1 - T)·ℛₙ`.
* `TauCeti.TraceFormulaMatrixModule.exists_periodRelation`: the period relation (A) has a solution
  for every `n`.

## Implementation notes

The products in (A) are permutation representations on `ℛₙ`. The left products are the
representation of `SL(2, ℤ)`: `S·ξ` is `Representation.ofMulAction ℚ SL(2, ℤ) ℳₙ S ξ`, and
similarly for `T`. This is the simp-normal form of the left representation of `PSL(2, ℤ)` at the
classes of `S` and `T` (by `TauCeti.TraceFormulaMatrixModule.ofMulAction_coe`), and since `S` and
`T` generate `SL(2, ℤ)`, the coinvariant kernel of this representation is the sum of the ranges of
`S - 1` and `T - 1`. The right product `ξ·S` is
`Representation.ofMulAction ℚ PSL(2, ℤ)ᵐᵒᵖ ℳₙ (MulOpposite.op S) ξ`, the right representation of
`PSL(2, ℤ)` from `TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.PermutationModule`, with
`S` viewed in `PSL(2, ℤ)`. The matrices `S` and `T` are Mathlib's `ModularGroup.S` and
`ModularGroup.T`; they are Popa–Zagier's `S` and `T`.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327. The period relation (A) is stated
  in §1; the criterion for membership in `(1 - T)·ℛₙ` is in §3, which also notes that solutions of
  (A) exist "as in [CZ]".
* [CZ] Y. J. Choie and D. Zagier, *Rational period functions for PSL(2, ℤ)*,
  Contemp. Math. **143** (1993), 89–108.
-/

public section

open MonoidAlgebra Representation ModularGroup
open scoped MatrixGroups

namespace TauCeti.TraceFormulaMatrixModule

variable {k : Type*} [CommRing k] {n : ℤ}

variable (k n) in
/-- **Popa–Zagier's period relation (A)** for `ξ ∈ k[ℳₙ]` (Popa–Zagier take `k = ℚ`, `ℛₙ = ℚ[ℳₙ]`):
`(1 - S)·ξ - Tₙ^∞·(1 - S) ∈ (1 - T)·ℛₙ`, where `(1 - S)·` and `(1 - T)·` are left multiplications
and `·(1 - S)` is right multiplication. -/
def PeriodRelation (ξ : k[TraceFormulaMatrixModule n]) : Prop :=
  (1 - ofMulAction k SL(2, ℤ) (TraceFormulaMatrixModule n) S) ξ -
      (1 - ofMulAction k PSL(2, ℤ)ᵐᵒᵖ (TraceFormulaMatrixModule n) (.op (S : PSL(2, ℤ))))
        (upperTriangularSum k n) ∈
    LinearMap.range (1 - ofMulAction k SL(2, ℤ) (TraceFormulaMatrixModule n) T)

/-- Unfolding `PeriodRelation`. -/
theorem periodRelation_iff {ξ : k[TraceFormulaMatrixModule n]} : PeriodRelation k n ξ ↔
    (1 - ofMulAction k SL(2, ℤ) (TraceFormulaMatrixModule n) S) ξ -
        (1 - ofMulAction k PSL(2, ℤ)ᵐᵒᵖ (TraceFormulaMatrixModule n) (.op (S : PSL(2, ℤ))))
          (upperTriangularSum k n) ∈
      LinearMap.range (1 - ofMulAction k SL(2, ℤ) (TraceFormulaMatrixModule n) T) :=
  Iff.rfl

/-- **Popa–Zagier's criterion for `(1 - T)·ℛₙ`.** An element of `k[ℳₙ]` lies in the range of left
multiplication by `1 - T` if and only if its coefficients sum to zero along every orbit of
`Γ_∞ = ⟨T⟩`. -/
theorem mem_range_one_sub_T_iff {ζ : k[TraceFormulaMatrixModule n]} :
    ζ ∈ LinearMap.range (1 - ofMulAction k SL(2, ℤ) (TraceFormulaMatrixModule n) T) ↔
      mapDomainLinearMap k k (Quotient.mk (MulAction.orbitRel (Subgroup.zpowers T) _)) ζ = 0 := by
  rw [← neg_sub, LinearMap.range_neg, Module.End.one_eq_id, mem_range_ofMulAction_sub_id_iff]

/-- Adding to a solution of the period relation an element `η` with `(1 - S)·η ∈ (1 - T)·ℛₙ` gives
another solution. -/
theorem PeriodRelation.add {ξ η : k[TraceFormulaMatrixModule n]} (h : PeriodRelation k n ξ)
    (hη : (1 - ofMulAction k SL(2, ℤ) (TraceFormulaMatrixModule n) S) η ∈
      LinearMap.range (1 - ofMulAction k SL(2, ℤ) (TraceFormulaMatrixModule n) T)) :
    PeriodRelation k n (ξ + η) := by
  rw [periodRelation_iff, map_add, add_sub_right_comm]
  exact add_mem h hη

/-- Two solutions of the period relation differ by an element `η` with `(1 - S)·η ∈ (1 - T)·ℛₙ`. -/
theorem PeriodRelation.sub_mem {ξ ξ' : k[TraceFormulaMatrixModule n]} (h : PeriodRelation k n ξ)
    (h' : PeriodRelation k n ξ') :
    (1 - ofMulAction k SL(2, ℤ) (TraceFormulaMatrixModule n) S) (ξ - ξ') ∈
      LinearMap.range (1 - ofMulAction k SL(2, ℤ) (TraceFormulaMatrixModule n) T) := by
  simpa only [map_sub, sub_sub_sub_cancel_right] using _root_.sub_mem h h'

variable (k) in
/-- **Existence of a solution of the period relation (A)** (Popa–Zagier, "as in [CZ]"): for every
`n` there is `ξ ∈ ℛₙ` with `(1 - S)·ξ - Tₙ^∞·(1 - S) ∈ (1 - T)·ℛₙ`. -/
theorem exists_periodRelation (n : ℤ) : ∃ ξ, PeriodRelation k n ξ := by
  -- `Tₙ^∞·(1 - S) = (S - 1)·x + (T - 1)·y`, since `S` and `T` generate `SL(2, ℤ)`
  obtain ⟨_, ⟨x, rfl⟩, _, ⟨y, rfl⟩, hxy⟩ := Submodule.mem_sup.1 <|
    ((coinvariantsKer_eq_iSup_range _ SpecialLinearGroup.SL2Z_generators).trans iSup_pair).le
      (one_sub_ofMulAction_op_upperTriangularSum_mem (k := k) (n := n) (S : PSL(2, ℤ)))
  refine ⟨-x, periodRelation_iff.2 ⟨y, ?_⟩⟩
  rw [← hxy]
  simp only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.id_apply, map_neg]
  abel

end TauCeti.TraceFormulaMatrixModule
