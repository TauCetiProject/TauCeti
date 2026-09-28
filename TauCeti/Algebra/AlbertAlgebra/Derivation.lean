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

`F₄` is the derivation algebra of the split Albert algebra `J = H₃(𝕆)`, and its `26`-dimensional
fundamental representation is supposed to be the trace-zero subspace `J₀`. Neither statement can be
made until one knows that a derivation of `J` lands in `J₀`; that is what this file proves.

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
(`TauCeti.AlbertAlgebra.traceZeroLieSubmodule`) — this is the candidate `26`-dimensional
fundamental representation — and, when scalar multiplication by `3` on `J` is regular, `Der J` acts
faithfully on it: a derivation kills `1`, so it sends the trace-zero element `3 • A - (tr A) • 1` to
`3 • D A`, and regularity cancels that `3`.

## Main definitions

* `TauCeti.AlbertAlgebra.offDiagSingle`: the Hermitian matrix with a single octonion entry, in
  position `(j + 1, j + 2)`.
* `TauCeti.AlbertAlgebra.traceZeroLieSubmodule`: the trace-zero subspace `J₀` as a Lie submodule of
  `J` over `Der J`, so that `J₀` is a representation of `Der J`.

## Main results

* `TauCeti.AlbertAlgebra.diagIdempotent_mul_offDiagSingle`: the **Peirce relation** between the
  diagonal frame and the off-diagonal slots: `Eᵢ` annihilates its opposite slot and halves the other
  two.
* `TauCeti.AlbertAlgebra.eq_sum_smul_diagIdempotent_add_sum_offDiagSingle`: the frame and the slots
  span `J`.
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

`TauCeti.AlbertAlgebra.offDiagSingle` is placed here rather than beside
`TauCeti.AlbertAlgebra.diagIdempotent`: its only purpose is to state the Peirce relation and the
spanning statement that the trace computation below runs on, and all three arrive together.

The index arithmetic of `Fin 3` — that `j`, `j + 1` and `j + 2` are distinct and that shifting twice
more returns to them — is discharged by `decide` in a block of private lemmas, so that no proof
below argues about `Fin 3` while it is computing in `J`; the one case already available in general,
`j + 2 ≠ j`, is `TauCeti.add_one_add_one_ne_self`.

Derivations are taken in the bundled form `D : TauCeti.derivationLieAlgebra R (AlbertAlgebra R)` of
`TauCeti/Algebra/Lie/Derivation/Basic.lean`, and are applied through the coercion
`(D : Module.End R (AlbertAlgebra R))`, which is the simp-normal form of their action there.

## References

This is the first step of the `F₄ = Der(H₃(𝕆))` target of Layer 8 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md` ("build
`derivationLieAlgebra (AlbertAlgebra K)`, prove `finrank = 52` and Killing-simplicity of type
`F₄`", "with its `26`-dimensional fundamental representation the trace-zero elements
`J₀ = ker(albertTrace)`"). The count `finrank (Der J) = 52`, the type-`F₄` Killing-simplicity, the
Jordan identity and the identification with `LieAlgebra.f₄` are not proved here.

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

private theorem eq_add_one_or_eq_add_two {i j : Fin 3} (h : i ≠ j) : i = j + 1 ∨ i = j + 2 := by
  revert h; revert i j; decide

/-- A sum over `Fin 3` read off starting from an arbitrary index. -/
private theorem sum_fin_three_rotate {M : Type*} [AddCommMonoid M] (f : Fin 3 → M) (j : Fin 3) :
    ∑ m, f m = f j + f (j + 1) + f (j + 2) := by
  have h : ∑ m : Fin 3, f (j + m) = ∑ m : Fin 3, f m :=
    Fintype.sum_equiv (Equiv.addLeft j) _ _ fun _ => rfl
  rw [← h, Fin.sum_univ_three, add_zero]

/-! ### The off-diagonal slots -/

/-- The Hermitian octonion matrix whose only nonzero entry is the octonion `a`, in position
`(j + 1, j + 2)`: the `j`-th **off-diagonal slot** of `H₃(𝕆)`. Together with the diagonal frame
`TauCeti.AlbertAlgebra.diagIdempotent` these span the algebra. -/
def offDiagSingle [Zero R] (j : Fin 3) (a : Octonion R) : AlbertAlgebra R := ⟨0, Pi.single j a⟩

@[simp] theorem offDiagSingle_diag [Zero R] (j : Fin 3) (a : Octonion R) :
    (offDiagSingle j a).diag = 0 := (rfl)

@[simp] theorem offDiagSingle_offDiag [Zero R] (j : Fin 3) (a : Octonion R) :
    (offDiagSingle j a).offDiag = Pi.single j a := (rfl)

/-- An off-diagonal slot has trace `0`: it has no diagonal entries. Not a `simp` lemma, for the
reason `TauCeti.AlbertAlgebra.trace_diagIdempotent` is not: `TauCeti.AlbertAlgebra.trace_apply`
already takes its left-hand side apart, and `simp` proves it outright. -/
theorem trace_offDiagSingle [Semiring R] (j : Fin 3) (a : Octonion R) :
    trace (offDiagSingle j a) = 0 := by
  simp

section Peirce

variable [CommRing R] [Invertible (2 : R)]

/-- **The Peirce relation between the diagonal frame and the off-diagonal slots**: the `j`-th slot
sits in position `(j + 1, j + 2)`, so `Eⱼ` — whose only entry is in position `(j, j)` — annihilates
it, while the two other idempotents halve it. -/
theorem diagIdempotent_mul_offDiagSingle (i j : Fin 3) (a : Octonion R) :
    diagIdempotent R i * offDiagSingle j a =
      if i = j then 0 else ⅟(2 : R) • offDiagSingle j a := by
  rcases eq_or_ne i j with rfl | h
  · refine AlbertAlgebra.ext (funext fun m => ?_) (funext fun m => ?_)
    · simp
    · rcases eq_or_ne m i with rfl | hm
      · simp
      · simp [Pi.single_eq_of_ne hm]
  · refine AlbertAlgebra.ext (funext fun m => ?_) (funext fun m => ?_)
    · simp [h]
    · rcases eq_or_ne m j with rfl | hm
      · rcases eq_add_one_or_eq_add_two h with rfl | rfl
        · simp [h]
        · simp [h]
      · simp [h, Pi.single_eq_of_ne hm]

end Peirce

section Span

variable [CommRing R]

/-- **The diagonal frame and the off-diagonal slots span `H₃(𝕆)`**: a Hermitian octonion matrix is
the combination of the diagonal idempotents read off its diagonal, plus its three off-diagonal
slots. -/
theorem eq_sum_smul_diagIdempotent_add_sum_offDiagSingle (A : AlbertAlgebra R) :
    A = (∑ i, A.diag i • diagIdempotent R i) + ∑ i, offDiagSingle i (A.offDiag i) := by
  refine AlbertAlgebra.ext (funext fun m => ?_) (funext fun m => ?_) <;>
    simp only [Fin.sum_univ_three, add_diag, add_offDiag, smul_diag, smul_offDiag,
      diagIdempotent_diag, diagIdempotent_offDiag, offDiagSingle_diag, offDiagSingle_offDiag,
      Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_zero, add_zero, zero_add] <;>
    fin_cases m <;> simp

end Span

/-! ### A derivation has trace-zero values -/

section Derivation

variable [CommRing R] [Invertible (2 : R)] (D : derivationLieAlgebra R (AlbertAlgebra R))

/-- **The value of a derivation at a diagonal idempotent has no diagonal.** Differentiating
`Eᵢ ∘ Eᵢ = Eᵢ` gives `D Eᵢ = 2 (Eᵢ ∘ D Eᵢ)`; taking the `m`-th diagonal entry multiplies that entry
by `2 δ_{m i}`, which kills it off `i` and forces `x = 2 x` at `i`. -/
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

/-- **A derivation kills the trace of an off-diagonal slot.** Differentiating the single Peirce
relation `E_{j+1} ∘ Fⱼ(a) = ½ Fⱼ(a)` gives `½ W = U ∘ Fⱼ(a) + E_{j+1} ∘ W` for `W = D Fⱼ(a)` and
`U = D E_{j+1}`, and the octonion slots of `U` enter the three diagonal entries of that equation
through the single scalar `t = ⟨Uⱼ, a⟩`: the entries read `½ Wⱼ = 0`, `½ W_{j+1} = t + W_{j+1}` and
`½ W_{j+2} = t`. The first kills `Wⱼ`, and eliminating `t` between the other two gives
`W_{j+1} + W_{j+2} = 0`. -/
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
    simpa [Pi.single_eq_of_ne (add_one_ne_self j), Pi.single_eq_of_ne hne,
      Pi.single_eq_of_ne (Ne.symm (add_one_ne_self j))] using hj
  have e1 : ⅟(2 : R) * W.diag (j + 1) =
      QuadraticMap.associated (Octonion.normQuadraticForm R) (U.offDiag j) a + W.diag (j + 1) := by
    have hj := congrArg (fun X : AlbertAlgebra R => X.diag (j + 1)) h
    simpa [add_one_add_one j, add_one_add_two j, Pi.single_eq_of_ne hne] using hj
  have e2 : ⅟(2 : R) * W.diag (j + 2) =
      QuadraticMap.associated (Octonion.normQuadraticForm R) (U.offDiag j) a := by
    have hj := congrArg (fun X : AlbertAlgebra R => X.diag (j + 2)) h
    simpa [add_two_add_one j, add_two_add_two j, Pi.single_eq_of_ne (add_one_ne_self j),
      Pi.single_eq_of_ne (add_two_ne_add_one j)] using hj
  have h2 : ⅟(2 : R) * 2 = 1 := invOf_mul_self' 2
  rw [trace_apply, sum_fin_three_rotate _ j]
  linear_combination (2 : R) * e0 - (2 : R) * e1 + (2 : R) * e2 +
    (W.diag (j + 1) - W.diag (j + 2) - W.diag j) * h2

/-- **A derivation of the split Albert algebra has values of trace `0`.** The diagonal frame and the
off-diagonal slots span, and the trace of a derivation vanishes on each of them. -/
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
a representation of the derivation algebra. This is the candidate `26`-dimensional fundamental
representation of `F₄`; its dimension is `TauCeti.AlbertAlgebra.finrank_traceZero`. -/
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
    A ∈ traceZeroLieSubmodule R ↔ trace A = 0 :=
  mem_traceZero

section Faithful

variable [CommRing R] [Invertible (2 : R)]

/-- **`Der H₃(𝕆)` acts faithfully on the trace-zero subspace**, so no information is lost by
restricting the derivation algebra to its candidate fundamental representation.

A derivation kills `1`, and `3 · A - (tr A) · 1` has trace `0` with
`D (3 · A - (tr A) · 1) = 3 · D A`, so a derivation vanishing on `J₀` vanishes outright as soon as
scalar multiplication by `3` on `J` is regular. That regularity is the exact hypothesis the proof
uses; the instance `TauCeti.AlbertAlgebra.instIsFaithfulTraceZeroLieSubmodule` supplies it from
typeclasses. -/
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
