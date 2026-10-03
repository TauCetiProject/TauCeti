/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import TauCeti.NumberTheory.ModularForms.BinaryForms
import TauCeti.LinearAlgebra.End.OrderTwoThree
import TauCeti.RingTheory.MvPolynomial.Finrank

/-!
# The space of period polynomials

Fix a commutative ring `R` and a natural number `w` (the weight `k = w + 2`). Let `V_w` be the
`R`-module of binary forms of degree `w`, modelled as `homogeneousSubmodule (Fin 2) R w` with
`X = X 0` and `Y = X 1`. Integral `2 × 2` matrices act on it on the right,
`(P ∣ M)(X, Y) = P(aX + bY, cX + dY)` for `M = !![a, b; c, d]`, so that `P ∣ (M * N) =
(P ∣ M) ∣ N`; this is `TauCeti.binaryFormRep`, defined in
`TauCeti.NumberTheory.ModularForms.BinaryForms`. The **period-polynomial space** is
`W_w = ker(1 + S) ∩ ker(1 + U + U²)`, where `S = !![0, -1; 1, 0]` and `U = T S = !![1, -1; 1, 0]`
are the standard generators of order `2` and `3` of `PSL(2, ℤ)`. It is the space in which
the period polynomial `r_f(X, Y) = ∫₀^{i∞} f(τ) (X - τY)^w dτ` of a cusp form `f` of weight
`w + 2` lives, and the target of the Eichler–Shimura period maps. Popa and Zagier compute the
trace of Hecke operators on `S_k(SL(2, ℤ))` by computing it on `W_w`.

The parity involution is `ε = !![-1, 0; 0, 1]`, acting by `P(X, Y) ↦ P(-X, Y)`. For even `w` it
preserves `W_w` (because `εSε = -S` and `εUε = SU²S`), and the **even** and **odd** period
polynomials `W_w^±` are its `±1`-eigenspaces in `W_w`. When `2` is invertible they span `W_w`.
For odd `w` the central element `S² = -1` acts by `-1`, so `W_w = 0` whenever multiplication by
`2` is injective on `R`; under this condition only even `w`, that is even weight, carries period
polynomials.

The Eisenstein polynomial `X^w - Y^w` is an even period polynomial for every even `w`. For
positive even `w`, over `ℂ`, it is up to a nonzero scalar the extended even period polynomial of
the Eisenstein series of weight `w + 2`; at `w = 0` it is zero.

Over a field of characteristic zero and for positive even `w`, the two kernels
`A = ker(1 + S)` and `B = ker(1 + U + U²)` cutting out `W_w` together span `V_w`. Popa and Zagier
use this to reduce the trace of an operator exchanging `A` and `B` on `W_w` to its trace on `V_w`.

## Main definitions

* `TauCeti.periodPolynomials R w`: the period-polynomial space `W_w`.
* `TauCeti.evenPeriodPolynomials R w`, `TauCeti.oddPeriodPolynomials R w`: its even and odd
  parts `W_w^±`.
* `TauCeti.eisensteinPeriodPolynomial R w`: the binary form `X^w - Y^w`.

## Main results

* `TauCeti.binaryFormRep_parity_involutive`: the parity action is an involution.
* `TauCeti.mem_periodPolynomials_binaryFormRep_parity`: for even `w`, the parity involution
  preserves `W_w`.
* `TauCeti.evenPeriodPolynomials_sup_oddPeriodPolynomials` and
  `TauCeti.disjoint_evenPeriodPolynomials_oddPeriodPolynomials`: `W_w = W_w^+ ⊕ W_w^-` when
  `2` is invertible (spanning) and multiplication by `2` is injective (disjointness).
* `TauCeti.periodPolynomials_eq_bot_of_odd`: `W_w = 0` for odd `w` when multiplication by `2`
  is injective.
* `TauCeti.mem_evenPeriodPolynomials_eisensteinPeriodPolynomial`: `X^w - Y^w ∈ W_w^+` for even
  `w`.
* `TauCeti.evenPeriodPolynomials_ne_bot`, `TauCeti.periodPolynomials_ne_bot`: `W_w^+` and `W_w`
  are nonzero for positive even `w` over a nontrivial ring, witnessed by `X^w - Y^w`.
* `TauCeti.binaryFormRep_S_sq_of_even`, `TauCeti.binaryFormRep_U_pow_three_of_even`: for even
  `w`, `S` and `U` act on `V_w` with orders dividing `2` and `3`, since `-1` acts trivially.
* `TauCeti.codisjoint_ker_one_add_S_ker_one_add_U_add_U_sq`: over a field of characteristic
  zero, `ker(1 + S) + ker(1 + U + U²) = V_w` for positive even `w`.

## Implementation notes

Popa and Zagier prove `ker(1 + S) + ker(1 + U + U²) = V_w` with a nondegenerate `SL(2, ℤ)`-invariant
pairing on `V_w`. Here it is proved directly. For even `w`, `S² = 1` and `U³ = 1` on `V_w`, so
`P - P ∣ S` lies in `ker(1 + S)` and `P - P ∣ U` lies in `ker(1 + U + U²)`
(`TauCeti.End.range_one_sub_le_ker_one_add`, `TauCeti.End.range_one_sub_le_ker_one_add_add_sq`),
and `P - P ∣ T` lies in their sum, as `T = -U S`. The
substitution `T : X ↦ X + Y` is unitriangular on the monomials `X^a Y^b`, so induction on `a`
puts every `X^a Y^b` with `a < w` in the sum, and then `X^w = Y^w - (Y^w - Y^w ∣ S)` as well.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327.
* W. Kohnen and D. Zagier, *Modular forms with rational periods*, in *Modular Forms*
  (R. A. Rankin, ed.), Ellis Horwood, 1984, 197–249, §1.
-/

public section

open Matrix MulOpposite MvPolynomial ModularGroup
open scoped MatrixGroups

namespace TauCeti

variable (R : Type*) [CommRing R] (w : ℕ)

/-- The **period-polynomial space** `W_w = ker(1 + S) ∩ ker(1 + U + U²)` inside the binary forms
of degree `w`, where `S = !![0, -1; 1, 0]` and `U = T S = !![1, -1; 1, 0]`. -/
noncomputable def periodPolynomials : Submodule R (homogeneousSubmodule (Fin 2) R w) :=
  LinearMap.ker (1 + binaryFormRep R w (op (S : Matrix (Fin 2) (Fin 2) ℤ))) ⊓
    LinearMap.ker (1 + binaryFormRep R w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) +
      binaryFormRep R w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) ^ 2)

variable {R w}

/-- Definition of the period-polynomial space. -/
theorem periodPolynomials_def :
    periodPolynomials R w =
      LinearMap.ker (1 + binaryFormRep R w (op (S : Matrix (Fin 2) (Fin 2) ℤ))) ⊓
        LinearMap.ker (1 + binaryFormRep R w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) +
          binaryFormRep R w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) ^ 2) := by
  rw [periodPolynomials]

/-- A binary form `P` of degree `w` is a period polynomial iff `P + P ∣ S = 0` and
`P + P ∣ U + P ∣ U² = 0`. -/
@[simp]
theorem mem_periodPolynomials_iff {P : homogeneousSubmodule (Fin 2) R w} :
    P ∈ periodPolynomials R w ↔
      P + binaryFormRep R w (op (S : Matrix (Fin 2) (Fin 2) ℤ)) P = 0 ∧
        P + binaryFormRep R w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) P +
          binaryFormRep R w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
            (binaryFormRep R w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) P) = 0 := by
  simp [periodPolynomials, pow_two]

variable (R w)

/-- The **even period polynomials** `W_w^+`: the period polynomials fixed by the parity
involution `P(X, Y) ↦ P(-X, Y)`. -/
noncomputable def evenPeriodPolynomials : Submodule R (homogeneousSubmodule (Fin 2) R w) :=
  periodPolynomials R w ⊓ LinearMap.ker (binaryFormRep R w (op !![-1, 0; 0, 1]) - 1)

/-- Definition of the even period-polynomial space. -/
theorem evenPeriodPolynomials_def :
    evenPeriodPolynomials R w =
      periodPolynomials R w ⊓ LinearMap.ker (binaryFormRep R w (op !![-1, 0; 0, 1]) - 1) := by
  rw [evenPeriodPolynomials]

/-- The **odd period polynomials** `W_w^-`: the period polynomials negated by the parity
involution `P(X, Y) ↦ P(-X, Y)`. -/
noncomputable def oddPeriodPolynomials : Submodule R (homogeneousSubmodule (Fin 2) R w) :=
  periodPolynomials R w ⊓ LinearMap.ker (binaryFormRep R w (op !![-1, 0; 0, 1]) + 1)

/-- Definition of the odd period-polynomial space. -/
theorem oddPeriodPolynomials_def :
    oddPeriodPolynomials R w =
      periodPolynomials R w ⊓ LinearMap.ker (binaryFormRep R w (op !![-1, 0; 0, 1]) + 1) := by
  rw [oddPeriodPolynomials]

variable {R w}

@[simp]
theorem mem_evenPeriodPolynomials_iff {P : homogeneousSubmodule (Fin 2) R w} :
    P ∈ evenPeriodPolynomials R w ↔
      P ∈ periodPolynomials R w ∧ binaryFormRep R w (op !![-1, 0; 0, 1]) P = P := by
  simp [evenPeriodPolynomials, sub_eq_zero]

@[simp]
theorem mem_oddPeriodPolynomials_iff {P : homogeneousSubmodule (Fin 2) R w} :
    P ∈ oddPeriodPolynomials R w ↔
      P ∈ periodPolynomials R w ∧ binaryFormRep R w (op !![-1, 0; 0, 1]) P = -P := by
  simp [oddPeriodPolynomials, add_eq_zero_iff_eq_neg]

/-! ### The parity involution preserves the period polynomials -/

/-- `εSε = -S`, in the form `ε S = -(S ε)`. -/
private lemma parity_mul_S :
    !![-1, 0; 0, 1] * (S : Matrix (Fin 2) (Fin 2) ℤ) = -((S : Matrix (Fin 2) (Fin 2) ℤ) *
      !![-1, 0; 0, 1]) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- `εUε = SU²S`, in the form `ε U = S U² S ε`. -/
private lemma parity_mul_U :
    !![-1, 0; 0, 1] * ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (S : Matrix (Fin 2) (Fin 2) ℤ) * ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
        ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (S : Matrix (Fin 2) (Fin 2) ℤ) *
          !![-1, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- `εU²ε = SUS`, in the form `ε U² = S U S ε`. -/
private lemma parity_mul_U_sq :
    !![-1, 0; 0, 1] * ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
        ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      (S : Matrix (Fin 2) (Fin 2) ℤ) * ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
        (S : Matrix (Fin 2) (Fin 2) ℤ) * !![-1, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The parity involution squares to the identity. -/
private lemma parity_mul_parity :
    !![-1, 0; 0, 1] * !![-1, 0; 0, 1] = (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The parity action `P(X, Y) ↦ P(-X, Y)` is an involution. -/
theorem binaryFormRep_parity_involutive :
    Function.Involutive (binaryFormRep R w (op !![-1, 0; 0, 1])) := fun P ↦ by
  rw [← binaryFormRep_op_mul_apply, parity_mul_parity, op_one, map_one, Module.End.one_apply]

/-- For even `w`, the parity involution `P(X, Y) ↦ P(-X, Y)` preserves the period
polynomials. -/
theorem mem_periodPolynomials_binaryFormRep_parity (hw : Even w)
    {P : homogeneousSubmodule (Fin 2) R w} (hP : P ∈ periodPolynomials R w) :
    binaryFormRep R w (op !![-1, 0; 0, 1]) P ∈ periodPolynomials R w := by
  obtain ⟨hS, hU⟩ := mem_periodPolynomials_iff.1 hP
  refine mem_periodPolynomials_iff.2 ⟨?_, ?_⟩
  · -- `(P ∣ ε) ∣ S = P ∣ (εS) = P ∣ (-Sε) = (P ∣ S) ∣ ε = -(P ∣ ε)`.
    rw [← binaryFormRep_op_mul_apply, parity_mul_S, binaryFormRep_op_neg_of_even hw,
      binaryFormRep_op_mul_apply, eq_neg_of_add_eq_zero_right hS, map_neg, add_neg_cancel]
  · -- Move `ε` to the right through `εU² = SUSε` and `εU = SU²Sε`, then use `P ∣ S = -P` and
    -- the relation `P + P ∣ U + P ∣ U² = 0`.
    have hU' : binaryFormRep R w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
        (binaryFormRep R w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) P) +
        binaryFormRep R w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) P = -P :=
      eq_neg_of_add_eq_zero_left (by rw [← hU]; abel)
    have key : binaryFormRep R w (op !![-1, 0; 0, 1])
        (binaryFormRep R w (op (S : Matrix (Fin 2) (Fin 2) ℤ))
          (binaryFormRep R w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
            (binaryFormRep R w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) P))) +
        binaryFormRep R w (op !![-1, 0; 0, 1])
          (binaryFormRep R w (op (S : Matrix (Fin 2) (Fin 2) ℤ))
            (binaryFormRep R w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) P)) =
        binaryFormRep R w (op !![-1, 0; 0, 1]) P := by
      rw [← map_add, ← map_add, hU', map_neg, eq_neg_of_add_eq_zero_right hS, neg_neg]
    rw [← binaryFormRep_op_mul_apply, ← binaryFormRep_op_mul_apply, parity_mul_U_sq,
      parity_mul_U]
    simp only [binaryFormRep_op_mul_apply, eq_neg_of_add_eq_zero_right hS, map_neg]
    rw [add_assoc, ← neg_add, key, add_neg_cancel]

/-! ### The even and odd parts -/

private theorem evenPeriodPolynomials_sup_oddPeriodPolynomials_of_even
    [Invertible (2 : R)] (hw : Even w) :
    evenPeriodPolynomials R w ⊔ oddPeriodPolynomials R w = periodPolynomials R w := by
  refine le_antisymm (sup_le inf_le_left inf_le_left) fun P hP ↦ ?_
  have hεP := mem_periodPolynomials_binaryFormRep_parity hw hP
  refine Submodule.mem_sup.2 ⟨⅟(2 : R) • (P + binaryFormRep R w (op !![-1, 0; 0, 1]) P), ?_,
    ⅟(2 : R) • (P - binaryFormRep R w (op !![-1, 0; 0, 1]) P), ?_, ?_⟩
  · refine mem_evenPeriodPolynomials_iff.2
      ⟨Submodule.smul_mem _ _ (Submodule.add_mem _ hP hεP), ?_⟩
    rw [map_smul, map_add, binaryFormRep_parity_involutive, add_comm]
  · refine mem_oddPeriodPolynomials_iff.2
      ⟨Submodule.smul_mem _ _ (Submodule.sub_mem _ hP hεP), ?_⟩
    rw [map_smul, map_sub, binaryFormRep_parity_involutive, ← neg_sub, smul_neg]
  · rw [← smul_add, add_add_sub_cancel, ← two_smul R P, smul_smul, invOf_mul_self, one_smul]

/-- A period polynomial cannot be both even and odd when multiplication by `2` is injective. -/
theorem disjoint_evenPeriodPolynomials_oddPeriodPolynomials
    (h2 : Function.Injective fun r : R ↦ 2 * r) :
    Disjoint (evenPeriodPolynomials R w) (oddPeriodPolynomials R w) :=
  Submodule.disjoint_def.2 fun _ hP hP' ↦ Subtype.ext <|
    MvPolynomial.eq_zero_of_add_self_eq_zero h2 <| congrArg Subtype.val <|
      eq_neg_iff_add_eq_zero.1
        ((mem_evenPeriodPolynomials_iff.1 hP).2.symm.trans (mem_oddPeriodPolynomials_iff.1 hP').2)

/-- For odd `w`, applying `S` twice negates every degree-`w` binary form. -/
private lemma binaryFormRep_S_sq_of_odd (hw : Odd w) (P : homogeneousSubmodule (Fin 2) R w) :
    binaryFormRep R w (op (S : Matrix (Fin 2) (Fin 2) ℤ))
      (binaryFormRep R w (op (S : Matrix (Fin 2) (Fin 2) ℤ)) P) = -P := by
  rw [← binaryFormRep_op_mul_apply, S_mul_S_eq, binaryFormRep_op_neg, hw.neg_one_pow, op_one,
    map_one, LinearMap.smul_apply, Module.End.one_apply, neg_one_smul]

/-- For odd `w` there are no nonzero period polynomials when multiplication by `2` is injective:
the central element `S² = -1` acts by `-1` but fixes every `P` with `P ∣ S = -P`. -/
theorem periodPolynomials_eq_bot_of_odd
    (h2 : Function.Injective fun r : R ↦ 2 * r) (hw : Odd w) :
    periodPolynomials R w = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun P hP ↦ ?_
  apply Subtype.ext
  apply MvPolynomial.eq_zero_of_add_self_eq_zero h2
  suffices P + P = 0 by
    simpa using congrArg
      (fun Q : homogeneousSubmodule (Fin 2) R w ↦ (Q : MvPolynomial (Fin 2) R)) this
  have hSP := eq_neg_of_add_eq_zero_right (mem_periodPolynomials_iff.1 hP).1
  have hSS := binaryFormRep_S_sq_of_odd hw P
  rw [hSP, map_neg, hSP, neg_neg] at hSS
  exact eq_neg_iff_add_eq_zero.1 hSS

/-- When `2` is invertible, the even and odd period polynomials span `W_w`. -/
theorem evenPeriodPolynomials_sup_oddPeriodPolynomials [Invertible (2 : R)] :
    evenPeriodPolynomials R w ⊔ oddPeriodPolynomials R w = periodPolynomials R w := by
  rcases Nat.even_or_odd w with hw | hw
  · exact evenPeriodPolynomials_sup_oddPeriodPolynomials_of_even hw
  · have h2 : Function.Injective fun r : R ↦ 2 * r :=
      (isUnit_of_invertible (2 : R)).mul_right_injective
    have hle : evenPeriodPolynomials R w ⊔ oddPeriodPolynomials R w ≤
        periodPolynomials R w := sup_le inf_le_left inf_le_left
    rw [periodPolynomials_eq_bot_of_odd h2 hw] at hle
    rw [periodPolynomials_eq_bot_of_odd h2 hw]
    exact bot_unique hle

/-! ### The Eisenstein polynomial -/

variable (R w)

/-- The binary form `X^w - Y^w`. For even `w` it is an even period polynomial. For positive even
`w`, over `ℂ`, it is up to a nonzero scalar the extended even period polynomial of the Eisenstein
series of weight `w + 2`; at `w = 0` it is zero. -/
noncomputable def eisensteinPeriodPolynomial : homogeneousSubmodule (Fin 2) R w :=
  ⟨X 0 ^ w - X 1 ^ w, (isHomogeneous_X_pow 0 w).sub (isHomogeneous_X_pow 1 w)⟩

variable {R w}

@[simp]
theorem coe_eisensteinPeriodPolynomial :
    (eisensteinPeriodPolynomial R w : MvPolynomial (Fin 2) R) = X 0 ^ w - X 1 ^ w :=
  (rfl)

/-- For even `w`, the Eisenstein polynomial `X^w - Y^w` is an even period polynomial. -/
theorem mem_evenPeriodPolynomials_eisensteinPeriodPolynomial (hw : Even w) :
    eisensteinPeriodPolynomial R w ∈ evenPeriodPolynomials R w := by
  refine mem_evenPeriodPolynomials_iff.2 ⟨mem_periodPolynomials_iff.2 ⟨?_, ?_⟩, ?_⟩ <;>
    refine Subtype.ext ?_ <;>
    simp [Fin.sum_univ_two, hw.neg_pow]

/-- For positive `w`, the Eisenstein polynomial `X^w - Y^w` is nonzero. -/
theorem eisensteinPeriodPolynomial_ne_zero [Nontrivial R] (hw : w ≠ 0) :
    eisensteinPeriodPolynomial R w ≠ 0 := by
  intro h
  have h' := congrArg Subtype.val h
  rw [coe_eisensteinPeriodPolynomial, ZeroMemClass.coe_zero, sub_eq_zero, X_pow_eq_monomial,
    X_pow_eq_monomial, (monomial_left_injective one_ne_zero).eq_iff,
    Finsupp.single_left_inj hw] at h'
  exact zero_ne_one h'

/-- For positive even `w` over a nontrivial ring, the even period polynomials are nonzero. -/
theorem evenPeriodPolynomials_ne_bot [Nontrivial R] (hw : Even w) (hw₀ : w ≠ 0) :
    evenPeriodPolynomials R w ≠ ⊥ :=
  (Submodule.ne_bot_iff _).2 ⟨_, mem_evenPeriodPolynomials_eisensteinPeriodPolynomial hw,
    eisensteinPeriodPolynomial_ne_zero hw₀⟩

/-- For positive even `w` over a nontrivial ring, the period polynomials are nonzero. -/
theorem periodPolynomials_ne_bot [Nontrivial R] (hw : Even w) (hw₀ : w ≠ 0) :
    periodPolynomials R w ≠ ⊥ :=
  ne_bot_of_le_ne_bot (evenPeriodPolynomials_ne_bot hw hw₀) inf_le_left

/-! ### The kernels of `1 + S` and `1 + U + U²` span `V_w` -/

/-- `U³ = -1`, for `U = T S`. -/
private lemma U_mul_U_mul_U_eq_neg_one :
    ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
        (((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
          ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- `U S = -T`, for `U = T S`. -/
private lemma U_mul_S_eq_neg_T :
    ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (S : Matrix (Fin 2) (Fin 2) ℤ) =
      -(T : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- For even `w`, `S` acts on `V_w` as an involution, since `S² = -1` acts trivially. -/
theorem binaryFormRep_S_sq_of_even (hw : Even w) :
    binaryFormRep R w (op (S : Matrix (Fin 2) (Fin 2) ℤ)) ^ 2 = 1 := by
  rw [← map_pow, ← op_pow, sq, S_mul_S_eq, binaryFormRep_op_neg_of_even hw, op_one, map_one]

/-- For even `w`, `U = T S` acts on `V_w` with cube `1`, since `U³ = -1` acts trivially. -/
theorem binaryFormRep_U_pow_three_of_even (hw : Even w) :
    binaryFormRep R w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) ^ 3 = 1 := by
  rw [← map_pow, ← op_pow, pow_three, U_mul_U_mul_U_eq_neg_one, binaryFormRep_op_neg_of_even hw,
    op_one, map_one]

/-- For even `w`, `P - P ∣ T` lies in `ker (1 + S) + ker (1 + U + U²)`, where `U = T S`. -/
private lemma sub_binaryFormRep_T_mem_sup (hw : Even w) (P : homogeneousSubmodule (Fin 2) R w) :
    P - binaryFormRep R w (op (T : Matrix (Fin 2) (Fin 2) ℤ)) P ∈
      LinearMap.ker (1 + binaryFormRep R w (op (S : Matrix (Fin 2) (Fin 2) ℤ))) ⊔
        LinearMap.ker (1 + binaryFormRep R w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) +
          binaryFormRep R w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) ^ 2) := by
  have hT : binaryFormRep R w (op (T : Matrix (Fin 2) (Fin 2) ℤ)) P =
      binaryFormRep R w (op (S : Matrix (Fin 2) (Fin 2) ℤ))
        (binaryFormRep R w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) P) := by
    rw [← binaryFormRep_op_mul_apply, U_mul_S_eq_neg_T, binaryFormRep_op_neg_of_even hw]
  -- `P - P ∣ T = (1 - S) (P ∣ U) + (1 - U) P`; for `S² = 1` and `U³ = 1`, `1 + S` kills the range
  -- of `1 - S` and `1 + U + U²` kills the range of `1 - U`
  have h : P - binaryFormRep R w (op (T : Matrix (Fin 2) (Fin 2) ℤ)) P =
      (1 - binaryFormRep R w (op (S : Matrix (Fin 2) (Fin 2) ℤ)))
          (binaryFormRep R w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) P) +
        (1 - binaryFormRep R w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))) P := by
    rw [LinearMap.sub_apply, LinearMap.sub_apply, Module.End.one_apply, Module.End.one_apply, hT]
    abel
  rw [h]
  exact Submodule.add_mem_sup
    (End.range_one_sub_le_ker_one_add (binaryFormRep_S_sq_of_even hw)
      (LinearMap.mem_range_self _ _))
    (End.range_one_sub_le_ker_one_add_add_sq (binaryFormRep_U_pow_three_of_even hw)
      (LinearMap.mem_range_self _ _))

section Field

variable {K : Type*} [Field K]

/-- The substitution `T : X ↦ X + Y` is unitriangular on monomials: it sends `X^(i+1) Y^k` to
itself plus `(i + 1) X^i Y^(k+1)` plus multiples of the monomials `X^m Y^(i+1-m+k)` with
`m < i`. -/
private lemma linearSubst_T_X_pow_succ_mul_X_pow (i k : ℕ) :
    linearSubst ((T : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → K)) (X 0 ^ (i + 1) * X 1 ^ k) =
      X 0 ^ (i + 1) * X 1 ^ k + (i + 1) • (X 0 ^ i * X 1 ^ (k + 1)) +
        ∑ m ∈ Finset.range i, (i + 1).choose m • (X 0 ^ m * X 1 ^ (i + 1 - m + k)) := by
  have hT : linearSubst ((T : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → K))
      (X 0 ^ (i + 1) * X 1 ^ k) = (X 0 + X 1) ^ (i + 1) * X 1 ^ k := by
    simp [Fin.sum_univ_two, coe_T]
  have hsum : ∑ m ∈ Finset.range i, X 0 ^ m * X 1 ^ (i + 1 - m) *
      ((i + 1).choose m : MvPolynomial (Fin 2) K) * X 1 ^ k =
      ∑ m ∈ Finset.range i, (i + 1).choose m • (X 0 ^ m * X 1 ^ (i + 1 - m + k)) :=
    Finset.sum_congr rfl fun m _ ↦ by rw [nsmul_eq_mul, pow_add]; ring
  rw [hT, add_pow, Finset.sum_range_succ, Finset.sum_range_succ, add_mul, add_mul, Finset.sum_mul,
    hsum, Nat.choose_succ_self_right, Nat.choose_self, add_tsub_cancel_left, tsub_self,
    Nat.cast_succ]
  ring

/-- Over a field of characteristic zero, a subspace `W` of `V_w` containing `P - P ∣ T` for
every `P` contains every monomial `X^a Y^b` of degree `w` with `a < w`. -/
private lemma X_pow_mul_X_pow_mem_of_lt [CharZero K]
    {W : Submodule K (homogeneousSubmodule (Fin 2) K w)}
    (hT : ∀ P, P - binaryFormRep K w (op (T : Matrix (Fin 2) (Fin 2) ℤ)) P ∈ W) {a b : ℕ}
    (hab : a + b = w) (ha : a < w) :
    X 0 ^ a * X 1 ^ b ∈ W.map (homogeneousSubmodule (Fin 2) K w).subtype := by
  induction a using Nat.strong_induction_on generalizing b with
  | _ i ih =>
    obtain ⟨k, rfl⟩ : ∃ k, w = i + 1 + k := ⟨w - (i + 1), by omega⟩
    obtain rfl : b = k + 1 := by omega
    have h1 := Submodule.mem_map_of_mem (f := (homogeneousSubmodule (Fin 2) K _).subtype)
      (hT ⟨_, (isHomogeneous_X_pow 0 (i + 1)).mul (isHomogeneous_X_pow 1 k)⟩)
    rw [Submodule.subtype_apply, Submodule.coe_sub, coe_binaryFormRep_apply,
      linearSubst_T_X_pow_succ_mul_X_pow] at h1
    have h2 : ∑ m ∈ Finset.range i, (i + 1).choose m • (X 0 ^ m * X 1 ^ (i + 1 - m + k)) ∈
        W.map (homogeneousSubmodule (Fin 2) K _).subtype :=
      Submodule.sum_mem _ fun m hm ↦ by
        have hm := Finset.mem_range.1 hm
        exact Submodule.smul_of_tower_mem _ _ (ih m hm (by omega) (by omega))
    have h3 : ((i + 1 : ℕ) : K) • (X 0 ^ i * X 1 ^ (k + 1)) ∈
        W.map (homogeneousSubmodule (Fin 2) K _).subtype := by
      rw [Nat.cast_smul_eq_nsmul]
      convert sub_mem (neg_mem h1) h2 using 1
      abel
    exact (Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 i.succ_ne_zero)).1 h3

/-- Over a field of characteristic zero and for `w ≠ 0`, a subspace `W` of `V_w` containing
`P - P ∣ T` and `P - P ∣ S` for every `P` contains every monomial `X^a Y^b` of degree `w`. -/
private lemma X_pow_mul_X_pow_mem [CharZero K] (hw₀ : w ≠ 0)
    {W : Submodule K (homogeneousSubmodule (Fin 2) K w)}
    (hT : ∀ P, P - binaryFormRep K w (op (T : Matrix (Fin 2) (Fin 2) ℤ)) P ∈ W)
    (hS : ∀ P, P - binaryFormRep K w (op (S : Matrix (Fin 2) (Fin 2) ℤ)) P ∈ W) {a b : ℕ}
    (hab : a + b = w) :
    X 0 ^ a * X 1 ^ b ∈ W.map (homogeneousSubmodule (Fin 2) K w).subtype := by
  rcases (Nat.le.intro hab).lt_or_eq with ha | ha
  · exact X_pow_mul_X_pow_mem_of_lt hT hab ha
  obtain ⟨rfl, rfl⟩ : w = a ∧ b = 0 := ⟨ha.symm, by omega⟩
  -- `X^w = Y^w - (Y^w - Y^w ∣ S)`
  have h := Submodule.mem_map_of_mem (f := (homogeneousSubmodule (Fin 2) K w).subtype)
    (hS ⟨X 1 ^ w, isHomogeneous_X_pow 1 w⟩)
  have hSY : linearSubst ((S : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → K)) (X 1 ^ w) =
      X 0 ^ w := by
    simp [Fin.sum_univ_two, coe_S]
  rw [Submodule.subtype_apply, Submodule.coe_sub, coe_binaryFormRep_apply, hSY] at h
  simpa using sub_mem (X_pow_mul_X_pow_mem_of_lt hT (zero_add w) (Nat.pos_of_ne_zero hw₀)) h

/-- Over a field of characteristic zero and for `w ≠ 0`, the only subspace of `V_w` containing
`P - P ∣ T` and `P - P ∣ S` for every `P` is `V_w`. -/
private lemma eq_top_of_sub_binaryFormRep_mem [CharZero K] (hw₀ : w ≠ 0)
    {W : Submodule K (homogeneousSubmodule (Fin 2) K w)}
    (hT : ∀ P, P - binaryFormRep K w (op (T : Matrix (Fin 2) (Fin 2) ℤ)) P ∈ W)
    (hS : ∀ P, P - binaryFormRep K w (op (S : Matrix (Fin 2) (Fin 2) ℤ)) P ∈ W) : W = ⊤ := by
  rw [eq_top_iff, ← (homogeneousMonomialBasis (R := K) w).span_eq, Submodule.span_le]
  rintro _ ⟨s, rfl⟩
  rw [SetLike.mem_coe, ← Submodule.comap_map_eq_of_injective
    (homogeneousSubmodule (Fin 2) K w).injective_subtype W, Submodule.mem_comap,
    Submodule.subtype_apply, coe_homogeneousMonomialBasis, monomial_eq,
    Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two, C_1, one_mul]
  exact X_pow_mul_X_pow_mem hw₀ hT hS <| by
    simpa [Finsupp.degree_eq_sum, Fin.sum_univ_two] using s.2

/-- **The kernels of `1 + S` and `1 + U + U²` span `V_w`** (Popa–Zagier, §2, proof of
Proposition 3): over a field of characteristic zero and for even `w ≠ 0`, every binary form of
degree `w` is the sum of one killed by `1 + S` and one killed by `1 + U + U²`, where `U = T S`.
Both hypotheses on `w` are needed: for `w = 0` or odd `w` both kernels are zero. -/
theorem codisjoint_ker_one_add_S_ker_one_add_U_add_U_sq [CharZero K] (hw : Even w)
    (hw₀ : w ≠ 0) :
    Codisjoint (LinearMap.ker (1 + binaryFormRep K w (op (S : Matrix (Fin 2) (Fin 2) ℤ))))
      (LinearMap.ker (1 + binaryFormRep K w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) +
        binaryFormRep K w (op ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) ^ 2)) :=
  codisjoint_iff.2 <| eq_top_of_sub_binaryFormRep_mem hw₀ (sub_binaryFormRep_T_mem_sup hw)
    fun P ↦ Submodule.mem_sup_left <| by
      -- `P - P ∣ S = (1 - S) P`, and `1 + S` kills the range of `1 - S` as `S² = 1`
      simpa only [LinearMap.sub_apply, Module.End.one_apply] using
        End.range_one_sub_le_ker_one_add (binaryFormRep_S_sq_of_even hw)
          (LinearMap.mem_range_self _ P)

end Field

end TauCeti
