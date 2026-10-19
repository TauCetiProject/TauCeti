/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlbertAlgebra.Basic
public import TauCeti.Algebra.Lie.Derivation.Basic
import Mathlib.Tactic.LinearCombination
import TauCeti.Data.Fin.Basic

/-!
# Derivations of the split Albert algebra

`F₄` is the derivation algebra of the split Albert algebra `J = H₃(𝕆)`, and over a field its
`26`-dimensional fundamental representation is supposed to be the trace-zero subspace `J₀`. Neither
statement can be made until one knows that a derivation of `J` lands in `J₀`; that is what this file
proves.

Write `Fⱼ(a)` for the Hermitian matrix whose only nonzero entry is the octonion `a` in position
`(j + 1, j + 2)` (`TauCeti.AlbertAlgebra.offDiagSingle`). Together with the diagonal frame
`E₀, E₁, E₂` of `TauCeti/Algebra/AlbertAlgebra/Basic.lean` the slots span `J`
(`TauCeti.AlbertAlgebra.eq_sum_smul_diagIdempotent_add_sum_offDiagSingle`), and the trace of a
derivation is killed on each kind of generator separately; on a diagonal idempotent more is true,
`D Eᵢ` has no diagonal at all
(`TauCeti.AlbertAlgebra.derivation_apply_diagIdempotent_diag_eq_zero`). Only the Peirce calculus of
the frame enters, so no Jordan identity is needed — which is just as well, since `J` is not yet
known here to satisfy one.

The trace-zero subspace is therefore a Lie submodule
(`TauCeti.AlbertAlgebra.traceZeroLieSubmodule`), the candidate fundamental representation, of
dimension `26` over a base satisfying `StrongRankCondition`
(`TauCeti.AlbertAlgebra.finrank_traceZeroLieSubmodule`); `Der J` acts faithfully on it
(`TauCeti.AlbertAlgebra.isFaithful_traceZeroLieSubmodule`).

## Main definitions

* `TauCeti.AlbertAlgebra.traceZeroLieSubmodule`: the trace-zero subspace `J₀` as a Lie submodule of
  `J` over `Der J`, so that `J₀` is a representation of `Der J`, with
  `TauCeti.AlbertAlgebra.finrank_traceZeroLieSubmodule` its dimension `26` over a base satisfying
  `StrongRankCondition`.

## Main results

* `TauCeti.AlbertAlgebra.derivation_apply_diagIdempotent_diag_eq_zero`: the value of a derivation at
  a diagonal idempotent has vanishing diagonal.
* `TauCeti.AlbertAlgebra.trace_derivation_apply_eq_zero`: **a derivation of `J` has values of trace
  `0`**, with `TauCeti.AlbertAlgebra.derivation_apply_mem_traceZero` its membership form.
* `TauCeti.AlbertAlgebra.isFaithful_traceZeroLieSubmodule`: `Der J` acts faithfully on `J₀`;
  `TauCeti.AlbertAlgebra.instIsFaithfulTraceZeroLieSubmodule` is its instance form.

## Implementation notes

Everything is stated over a commutative ring in which `2` is invertible, the hypothesis the
symmetrized product already carries; the base is a field nowhere. Faithfulness also holds in
characteristic `3`, where the identity belongs to `J₀`: the trace-zero diagonal differences and
their squares determine the action on the diagonal frame.

Derivations are taken in the bundled form `D : TauCeti.derivationLieAlgebra R (AlbertAlgebra R)` of
`TauCeti/Algebra/Lie/Derivation/Basic.lean`, and are applied through the coercion
`(D : Module.End R (AlbertAlgebra R))`.

## References

* `TauCeti/Algebra/Octonion/Derivation.lean`, the `G₂ = Der(𝕆)` counterpart of this file, from which
  the packaging of the invariant subspace is adapted: `TauCeti.Octonion.imaginaryLieSubmodule`,
  `TauCeti.Octonion.isFaithful_imaginaryLieSubmodule` and
  `TauCeti.Octonion.instIsFaithfulImaginaryLieSubmodule` — the imaginary octonions as a Lie
  submodule over `Der 𝕆`, faithful over every commutative ring — are the
  models for
  `TauCeti.AlbertAlgebra.traceZeroLieSubmodule`,
  `TauCeti.AlbertAlgebra.isFaithful_traceZeroLieSubmodule` and
  `TauCeti.AlbertAlgebra.instIsFaithfulTraceZeroLieSubmodule` here. The trace computation itself is
  not adapted from it: there the argument is the skewness of a derivation for the norm form, here it
  is the Peirce calculus of the diagonal frame.
* T. A. Springer and F. D. Veldkamp, *Octonions, Jordan Algebras and Exceptional Groups*, §5.
* N. Jacobson, *Structure and Representations of Jordan Algebras*, Ch. IX, where the Peirce calculus
  of a complete orthogonal frame of idempotents is developed.
-/

public section

namespace TauCeti

namespace AlbertAlgebra

variable {R : Type*}

/-! ### A derivation has trace-zero values -/

section Derivation

variable [CommRing R] [Invertible (2 : R)] (D : derivationLieAlgebra R (AlbertAlgebra R))

/-- **The value of a derivation at a diagonal idempotent has no diagonal**: every scalar entry of
`D Eᵢ` vanishes, so in particular `D Eᵢ` has trace `0`. -/
theorem derivation_apply_diagIdempotent_diag_eq_zero (i : Fin 3) :
    ((D : Module.End R (AlbertAlgebra R)) (diagIdempotent R i)).diag = 0 := by
  have hEE : diagIdempotent R i * diagIdempotent R i = diagIdempotent R i := by simp
  have h := derivationLieAlgebra.leibniz D (diagIdempotent R i) (diagIdempotent R i)
  rw [hEE, mul_comm ((D : Module.End R (AlbertAlgebra R)) (diagIdempotent R i))
    (diagIdempotent R i)] at h
  funext m
  simp only [Pi.zero_apply]
  have hm := congrArg (fun X : AlbertAlgebra R => X.diag m) h
  simp only [add_diag, mul_diag, diagIdempotent_diag, diagIdempotent_offDiag, Pi.add_apply,
    Pi.zero_apply, map_zero, LinearMap.zero_apply, add_zero] at hm
  rcases eq_or_ne m i with rfl | hmi
  · rw [Pi.single_eq_same, one_mul] at hm
    linear_combination -hm
  · rw [Pi.single_eq_of_ne hmi, zero_mul, add_zero] at hm
    exact hm

/-- A derivation kills the trace of a diagonal idempotent. -/
theorem trace_derivation_apply_diagIdempotent (i : Fin 3) :
    trace ((D : Module.End R (AlbertAlgebra R)) (diagIdempotent R i)) = 0 := by
  simp [derivation_apply_diagIdempotent_diag_eq_zero D i]

/-- **A derivation kills the trace of an off-diagonal slot.** -/
theorem trace_derivation_apply_offDiagSingle (j : Fin 3) (a : Octonion R) :
    trace ((D : Module.End R (AlbertAlgebra R)) (offDiagSingle j a)) = 0 := by
  have h1 : j + 1 ≠ j := add_one_ne_self (by omega) j
  have hne : j + 2 ≠ j := by
    rw [← add_one_add_one_fin_three j]; exact add_one_add_one_ne_self le_rfl j
  have h21 : j + 2 ≠ j + 1 := by
    rw [← add_one_add_one_fin_three j]; exact add_one_ne_self (by omega) (j + 1)
  have hE : diagIdempotent R (j + 1) * offDiagSingle j a = ⅟(2 : R) • offDiagSingle j a := by
    rw [diagIdempotent_mul_offDiagSingle, ite_eq_right h1]
  have h := derivationLieAlgebra.leibniz D (diagIdempotent R (j + 1)) (offDiagSingle j a)
  rw [hE, map_smul] at h
  set U := (D : Module.End R (AlbertAlgebra R)) (diagIdempotent R (j + 1))
  set W := (D : Module.End R (AlbertAlgebra R)) (offDiagSingle j a)
  have e0 : ⅟(2 : R) * W.diag j = 0 := by
    have hj := congrArg (fun X : AlbertAlgebra R => X.diag j) h
    simpa only [smul_diag, Pi.smul_apply, smul_eq_mul, add_diag, Pi.add_apply, mul_diag,
      offDiagSingle_diag, offDiagSingle_offDiag, diagIdempotent_diag, diagIdempotent_offDiag,
      Pi.zero_apply, Pi.single_eq_of_ne h1, Pi.single_eq_of_ne hne,
      Pi.single_eq_of_ne (Ne.symm h1), mul_zero, zero_mul, map_zero,
      LinearMap.zero_apply, add_zero] using hj
  have e1 : ⅟(2 : R) * W.diag (j + 1) =
      QuadraticMap.associated (Octonion.normQuadraticForm R) (U.offDiag j) a + W.diag (j + 1) := by
    have hj := congrArg (fun X : AlbertAlgebra R => X.diag (j + 1)) h
    simpa only [smul_diag, Pi.smul_apply, smul_eq_mul, add_diag, Pi.add_apply, mul_diag,
      offDiagSingle_diag, offDiagSingle_offDiag, diagIdempotent_diag, diagIdempotent_offDiag,
      add_one_add_one_fin_three j, add_one_add_two_fin_three j, Pi.zero_apply,
      Pi.single_eq_of_ne hne,
      Pi.single_eq_same, mul_zero, one_mul, map_zero, LinearMap.zero_apply, add_zero,
      zero_add] using hj
  have e2 : ⅟(2 : R) * W.diag (j + 2) =
      QuadraticMap.associated (Octonion.normQuadraticForm R) (U.offDiag j) a := by
    have hj := congrArg (fun X : AlbertAlgebra R => X.diag (j + 2)) h
    simpa only [smul_diag, Pi.smul_apply, smul_eq_mul, add_diag, Pi.add_apply, mul_diag,
      offDiagSingle_diag, offDiagSingle_offDiag, diagIdempotent_diag, diagIdempotent_offDiag,
      add_two_add_one_fin_three j, add_two_add_two_fin_three j, Pi.zero_apply,
      Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h21,
      Pi.single_eq_same, mul_zero, zero_mul, map_zero, LinearMap.zero_apply, add_zero,
      zero_add] using hj
  have h2 : ⅟(2 : R) * 2 = 1 := invOf_mul_self' 2
  rw [trace_apply, sum_fin_three_rotate _ j]
  linear_combination (2 : R) * e0 - (2 : R) * e1 + (2 : R) * e2 +
    (W.diag (j + 1) - W.diag (j + 2) - W.diag j) * h2

/-- **A derivation of the split Albert algebra has values of trace `0`.** -/
theorem trace_derivation_apply_eq_zero (A : AlbertAlgebra R) :
    trace ((D : Module.End R (AlbertAlgebra R)) A) = 0 := by
  rw [eq_sum_smul_diagIdempotent_add_sum_offDiagSingle A]
  simp only [Fin.sum_univ_three, map_add, map_smul, smul_eq_mul,
    trace_derivation_apply_diagIdempotent, trace_derivation_apply_offDiagSingle, mul_zero,
    add_zero]

/-- **A derivation maps `H₃(𝕆)` into its trace-zero subspace**, the membership form of
`TauCeti.AlbertAlgebra.trace_derivation_apply_eq_zero`. -/
theorem derivation_apply_mem_traceZero (A : AlbertAlgebra R) :
    (D : Module.End R (AlbertAlgebra R)) A ∈ traceZero R :=
  mem_traceZero.2 (trace_derivation_apply_eq_zero D A)

end Derivation

/-! ### The trace-zero subspace as a representation of the derivation algebra -/

/-- **The trace-zero subspace `J₀` as a Lie submodule of `H₃(𝕆)` over `Der H₃(𝕆)`**, so that `J₀` is
a representation of the derivation algebra. This is the candidate fundamental representation of
`F₄`; over a base satisfying `StrongRankCondition` its dimension is `26`
(`TauCeti.AlbertAlgebra.finrank_traceZeroLieSubmodule`). -/
def traceZeroLieSubmodule (R : Type*) [CommRing R] [Invertible (2 : R)] :
    LieSubmodule R (derivationLieAlgebra R (AlbertAlgebra R)) (AlbertAlgebra R) where
  __ := traceZero R
  lie_mem {D _} _ := derivation_apply_mem_traceZero D _

@[simp]
theorem toSubmodule_traceZeroLieSubmodule (R : Type*) [CommRing R] [Invertible (2 : R)] :
    (traceZeroLieSubmodule R).toSubmodule = traceZero R :=
  (rfl)

@[simp]
theorem mem_traceZeroLieSubmodule [CommRing R] [Invertible (2 : R)] {A : AlbertAlgebra R} :
    A ∈ traceZeroLieSubmodule R ↔ trace A = 0 := by
  rw [← LieSubmodule.mem_toSubmodule, toSubmodule_traceZeroLieSubmodule, mem_traceZero]

/-- **The trace-zero subspace is `26`-dimensional**, over a base satisfying
`StrongRankCondition`. -/
theorem finrank_traceZeroLieSubmodule (R : Type*) [CommRing R] [Invertible (2 : R)]
    [StrongRankCondition R] : Module.finrank R (traceZeroLieSubmodule R) = 26 :=
  finrank_traceZero R

section Faithful

variable [CommRing R] [Invertible (2 : R)]

/-- **`Der H₃(𝕆)` acts faithfully on the trace-zero subspace**, so no information is lost by
restricting the derivation algebra to its candidate fundamental representation, including in
characteristic `3`. -/
theorem isFaithful_traceZeroLieSubmodule :
    LieModule.IsFaithful R (derivationLieAlgebra R (AlbertAlgebra R))
      (traceZeroLieSubmodule R) := by
  rw [LieModule.isFaithful_iff']
  intro D hD
  have hzero (A : AlbertAlgebra R) (hA : trace A = 0) :
      (D : Module.End R (AlbertAlgebra R)) A = 0 := by
    have h := congrArg Subtype.val (hD ⟨A, mem_traceZeroLieSubmodule.mpr hA⟩)
    simpa only [LieSubmodule.coe_bracket, LieSubalgebra.coe_bracket_of_module,
      Module.End.lie_apply, ZeroMemClass.coe_zero] using h
  -- The difference and its square recover twice the first diagonal idempotent.
  have hdiff := hzero (diagIdempotent R 0 - diagIdempotent R 1)
    (by simp only [map_sub, trace_diagIdempotent, sub_self])
  have hsquare : (diagIdempotent R 0 - diagIdempotent R 1) *
      (diagIdempotent R 0 - diagIdempotent R 1) =
      diagIdempotent R 0 + diagIdempotent R 1 := by
    simp [sub_mul, mul_sub]
  have hsum := derivationLieAlgebra.apply_mul_eq_zero hdiff hdiff
  rw [hsquare, map_add] at hsum
  rw [map_sub, sub_eq_zero] at hdiff
  have htwo : (2 : R) • (D : Module.End R (AlbertAlgebra R)) (diagIdempotent R 0) = 0 := by
    simpa only [two_smul R, hdiff] using hsum
  have hdiag : (D : Module.End R (AlbertAlgebra R)) (diagIdempotent R 0) = 0 := by
    simpa using congrArg (⅟(2 : R) • ·) htwo
  refine derivationLieAlgebra.ext fun A => ?_
  have h := hzero (A - trace A • diagIdempotent R 0)
    (by simp only [map_sub, map_smul, trace_diagIdempotent, smul_eq_mul, mul_one, sub_self])
  simpa [hdiag] using h

/-- **`Der H₃(𝕆)` acts faithfully on the trace-zero subspace**, the typeclass form of
`TauCeti.AlbertAlgebra.isFaithful_traceZeroLieSubmodule`. -/
instance instIsFaithfulTraceZeroLieSubmodule :
    LieModule.IsFaithful R (derivationLieAlgebra R (AlbertAlgebra R))
      (traceZeroLieSubmodule R) :=
  isFaithful_traceZeroLieSubmodule

end Faithful

end AlbertAlgebra

end TauCeti
