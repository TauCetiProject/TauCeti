/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Regular
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

The argument is the Peirce calculus of the diagonal frame `E₀, E₁, E₂` of
`TauCeti/Algebra/AlbertAlgebra/Basic.lean`, and it needs no Jordan identity — which is just as well,
since `J` is not yet known here to satisfy one. Write `Fᵢ(a)` for the Hermitian matrix whose only
nonzero entry is the octonion `a` in position `(i + 1, i + 2)`
(`TauCeti.AlbertAlgebra.offDiagSingle`). The frame and the three slots span `J`
(`TauCeti.AlbertAlgebra.eq_sum_smul_diagIdempotent_add_sum_offDiagSingle`), so it is enough to
annihilate the trace on each of them, and each case is one application of the Leibniz rule to a
Peirce relation.

* On `Eᵢ`: from `Eᵢ ∘ Eᵢ = Eᵢ` the value `D Eᵢ` satisfies `D Eᵢ = 2 (Eᵢ ∘ D Eᵢ)`, whose `m`-th
  diagonal entry is `2 δ_{m i}` times the `m`-th diagonal entry of `D Eᵢ`. Off `i` that forces the
  entry to vanish, and at `i` it forces `x = 2 x`. So **`D Eᵢ` has no diagonal at all**
  (`TauCeti.AlbertAlgebra.derivation_apply_diagIdempotent_diag_eq_zero`), and in particular
  trace `0`.
* On `Fⱼ(a)`: the single relation `E_{j+1} ∘ Fⱼ(a) = ½ Fⱼ(a)`
  (`TauCeti.AlbertAlgebra.diagIdempotent_mul_offDiagSingle`) differentiates to
  `½ W = U ∘ Fⱼ(a) + E_{j+1} ∘ W` with `W = D Fⱼ(a)` and `U = D E_{j+1}`. Its three diagonal
  entries read `½ W_j = 0`, `½ W_{j+1} = t + W_{j+1}` and `½ W_{j+2} = t` for the single scalar
  `t = ⟨U_j, a⟩` that the off-diagonal slots contribute. The first gives `W_j = 0`, and the other
  two give `W_{j+1} + W_{j+2} = 0`, so the three entries sum to zero.

So `D` maps all of `J` into the trace-zero subspace, that subspace is a Lie submodule
(`TauCeti.AlbertAlgebra.traceZeroLieSubmodule`) — this is the candidate fundamental representation,
of dimension `26` over a base satisfying `StrongRankCondition`
(`TauCeti.AlbertAlgebra.finrank_traceZeroLieSubmodule`) — and, when scalar multiplication by `3`
on `J` is regular, `Der J` acts faithfully on it: a derivation kills `1`, so it sends the trace-zero
element `3 • A - (tr A) • 1` to `3 • D A`, and regularity cancels that `3`.

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
* `TauCeti.AlbertAlgebra.isFaithful_traceZeroLieSubmodule`: when scalar multiplication by `3` on `J`
  is regular, `Der J` acts faithfully on `J₀`;
  `TauCeti.AlbertAlgebra.instIsFaithfulTraceZeroLieSubmodule` is the instance form of that, under
  `[NoZeroSMulDivisors R (AlbertAlgebra R)]` and `[NeZero (3 : R)]`.

## Implementation notes

Everything is stated over a commutative ring in which `2` is invertible, the hypothesis the
symmetrized product already carries; the base is a field nowhere. The faithfulness result is stated
for the exact hypothesis its proof uses, `IsSMulRegular (AlbertAlgebra R) (3 : R)`, which is not a
class; the instance form of it therefore asks for the two classes
`[NoZeroSMulDivisors R (AlbertAlgebra R)]` and `[NeZero (3 : R)]`, which imply it but are strictly
stronger. Some such hypothesis is necessary for this argument: in characteristic `3` the trace-zero
element `3 • A - (tr A) • 1` degenerates to `-(tr A) • 1`, which retains no information about `A`.

The index arithmetic of `Fin 3` — that `j`, `j + 1` and `j + 2` are distinct and that shifting twice
more returns to them — is discharged by `decide` in a block of private lemmas, so that no proof
below argues about `Fin 3` while it is computing in `J`; the one case already available in general,
`j + 2 ≠ j`, is `TauCeti.add_one_add_one_ne_self`.

Derivations are taken in the bundled form `D : TauCeti.derivationLieAlgebra R (AlbertAlgebra R)` of
`TauCeti/Algebra/Lie/Derivation/Basic.lean`, and are applied through the coercion
`(D : Module.End R (AlbertAlgebra R))`, which is the simp-normal form of their action there.

## References

* `TauCeti/Algebra/Octonion/Derivation.lean`, the `G₂ = Der(𝕆)` counterpart of this file, from which
  the packaging of the invariant subspace is adapted: `TauCeti.Octonion.imaginaryLieSubmodule`,
  `TauCeti.Octonion.isFaithful_imaginaryLieSubmodule` and
  `TauCeti.Octonion.instIsFaithfulImaginaryLieSubmodule` — the imaginary octonions as a Lie
  submodule over `Der 𝕆`, faithful once multiplication by the scalar `2` is regular — are the
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

/-! ### The index arithmetic of `Fin 3` -/

private theorem add_one_ne_self (j : Fin 3) : j + 1 ≠ j := by revert j; decide

private theorem add_two_ne_add_one (j : Fin 3) : j + 2 ≠ j + 1 := by revert j; decide

private theorem add_one_add_two (j : Fin 3) : j + 1 + 2 = j := by revert j; decide

private theorem add_one_add_one (j : Fin 3) : j + 1 + 1 = j + 2 := by revert j; decide

private theorem add_two_add_one (j : Fin 3) : j + 2 + 1 = j := by revert j; decide

private theorem add_two_add_two (j : Fin 3) : j + 2 + 2 = j + 1 := by revert j; decide

/-- A sum over `Fin 3` read off starting from an arbitrary index. -/
private theorem sum_fin_three_rotate {M : Type*} [AddCommMonoid M] (f : Fin 3 → M) (j : Fin 3) :
    ∑ m, f m = f j + f (j + 1) + f (j + 2) := by
  have h : ∑ m : Fin 3, f (j + m) = ∑ m : Fin 3, f m :=
    Fintype.sum_equiv (Equiv.addLeft j) _ _ fun _ => rfl
  rw [← h, Fin.sum_univ_three, add_zero]

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
  have hne : j + 2 ≠ j := by
    rw [← add_one_add_one j]
    exact add_one_add_one_ne_self le_rfl j
  have hE : diagIdempotent R (j + 1) * offDiagSingle j a = ⅟(2 : R) • offDiagSingle j a := by
    rw [diagIdempotent_mul_offDiagSingle, ite_eq_right (add_one_ne_self j)]
  have h := derivationLieAlgebra.leibniz D (diagIdempotent R (j + 1)) (offDiagSingle j a)
  rw [hE, map_smul] at h
  set U := (D : Module.End R (AlbertAlgebra R)) (diagIdempotent R (j + 1))
  set W := (D : Module.End R (AlbertAlgebra R)) (offDiagSingle j a)
  have e0 : ⅟(2 : R) * W.diag j = 0 := by
    have hj := congrArg (fun X : AlbertAlgebra R => X.diag j) h
    simpa only [smul_diag, Pi.smul_apply, smul_eq_mul, add_diag, Pi.add_apply, mul_diag,
      offDiagSingle_diag, offDiagSingle_offDiag, diagIdempotent_diag, diagIdempotent_offDiag,
      Pi.zero_apply, Pi.single_eq_of_ne (add_one_ne_self j), Pi.single_eq_of_ne hne,
      Pi.single_eq_of_ne (Ne.symm (add_one_ne_self j)), mul_zero, zero_mul, map_zero,
      LinearMap.zero_apply, add_zero] using hj
  have e1 : ⅟(2 : R) * W.diag (j + 1) =
      QuadraticMap.associated (Octonion.normQuadraticForm R) (U.offDiag j) a + W.diag (j + 1) := by
    have hj := congrArg (fun X : AlbertAlgebra R => X.diag (j + 1)) h
    simpa only [smul_diag, Pi.smul_apply, smul_eq_mul, add_diag, Pi.add_apply, mul_diag,
      offDiagSingle_diag, offDiagSingle_offDiag, diagIdempotent_diag, diagIdempotent_offDiag,
      add_one_add_one j, add_one_add_two j, Pi.zero_apply, Pi.single_eq_of_ne hne,
      Pi.single_eq_same, mul_zero, one_mul, map_zero, LinearMap.zero_apply, add_zero,
      zero_add] using hj
  have e2 : ⅟(2 : R) * W.diag (j + 2) =
      QuadraticMap.associated (Octonion.normQuadraticForm R) (U.offDiag j) a := by
    have hj := congrArg (fun X : AlbertAlgebra R => X.diag (j + 2)) h
    simpa only [smul_diag, Pi.smul_apply, smul_eq_mul, add_diag, Pi.add_apply, mul_diag,
      offDiagSingle_diag, offDiagSingle_offDiag, diagIdempotent_diag, diagIdempotent_offDiag,
      add_two_add_one j, add_two_add_two j, Pi.zero_apply,
      Pi.single_eq_of_ne (add_one_ne_self j), Pi.single_eq_of_ne (add_two_ne_add_one j),
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

/-- **The trace-zero subspace is `26`-dimensional**, over a base satisfying `StrongRankCondition`.
The carrier of `TauCeti.AlbertAlgebra.traceZeroLieSubmodule` is the submodule
`TauCeti.AlbertAlgebra.traceZero` itself — `TauCeti.AlbertAlgebra.toSubmodule_traceZeroLieSubmodule`
holds by `rfl` — so this is `TauCeti.AlbertAlgebra.finrank_traceZero` read along that
identification. -/
theorem finrank_traceZeroLieSubmodule (R : Type*) [CommRing R] [Invertible (2 : R)]
    [StrongRankCondition R] : Module.finrank R (traceZeroLieSubmodule R) = 26 :=
  finrank_traceZero R

section Faithful

variable [CommRing R] [Invertible (2 : R)]

/-- **`Der H₃(𝕆)` acts faithfully on the trace-zero subspace** as soon as scalar multiplication by
`3` on `H₃(𝕆)` is regular, so no information is lost by restricting the derivation algebra to its
candidate fundamental representation. Some hypothesis on `3` is needed; the instance
`TauCeti.AlbertAlgebra.instIsFaithfulTraceZeroLieSubmodule` supplies this one from typeclasses. -/
theorem isFaithful_traceZeroLieSubmodule (h3 : IsSMulRegular (AlbertAlgebra R) (3 : R)) :
    LieModule.IsFaithful R (derivationLieAlgebra R (AlbertAlgebra R))
      (traceZeroLieSubmodule R) := by
  rw [LieModule.isFaithful_iff']
  intro D hD
  refine derivationLieAlgebra.ext fun A => ?_
  have hA : (3 : R) • A - trace A • (1 : AlbertAlgebra R) ∈ traceZeroLieSubmodule R := by
    rw [mem_traceZeroLieSubmodule, map_sub, map_smul, map_smul, trace_one]
    simp [mul_comm]
  have h := congrArg (Subtype.val) (hD ⟨_, hA⟩)
  rw [LieSubmodule.coe_bracket] at h
  simp only [LieSubalgebra.coe_bracket_of_module, Module.End.lie_apply, map_sub, map_smul,
    derivationLieAlgebra.apply_one_eq_zero, smul_zero, sub_zero, ZeroMemClass.coe_zero] at h
  simp [h3.right_eq_zero_of_smul h]

/-- **`Der H₃(𝕆)` acts faithfully on the trace-zero subspace** over a base for which `3` is a
nonzero scalar acting without zero divisors, the typeclass form of
`TauCeti.AlbertAlgebra.isFaithful_traceZeroLieSubmodule`. -/
instance instIsFaithfulTraceZeroLieSubmodule [NoZeroSMulDivisors R (AlbertAlgebra R)]
    [NeZero (3 : R)] :
    LieModule.IsFaithful R (derivationLieAlgebra R (AlbertAlgebra R))
      (traceZeroLieSubmodule R) :=
  isFaithful_traceZeroLieSubmodule <| IsSMulRegular.of_right_eq_zero_of_smul fun _ h =>
    (eq_zero_or_eq_zero_of_smul_eq_zero h).resolve_left (NeZero.ne (3 : R))

end Faithful

end AlbertAlgebra

end TauCeti
