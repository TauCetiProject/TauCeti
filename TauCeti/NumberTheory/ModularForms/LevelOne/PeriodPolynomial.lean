/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import TauCeti.RingTheory.MvPolynomial.LinearSubst

/-!
# The space of period polynomials

Fix a commutative ring `R` and a natural number `w` (the weight `k = w + 2`). Let `V_w` be the
`R`-module of binary forms of degree `w`, modelled as `homogeneousSubmodule (Fin 2) R w` with
`X = X 0` and `Y = X 1`. Integral `2 × 2` matrices act on it on the right,
`(P ∣ M)(X, Y) = P(aX + bY, cX + dY)` for `M = !![a, b; c, d]`, so that `P ∣ (M * N) =
(P ∣ M) ∣ N`; this is `TauCeti.binaryFormRep`. The **period-polynomial space** is
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

## Main definitions

* `TauCeti.binaryFormRep R w`: the right action of integral matrices on binary forms of degree
  `w`, as a representation of `(Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ`.
* `TauCeti.periodPolynomials R w`: the period-polynomial space `W_w`.
* `TauCeti.evenPeriodPolynomials R w`, `TauCeti.oddPeriodPolynomials R w`: its even and odd
  parts `W_w^±`.
* `TauCeti.eisensteinPeriodPolynomial R w`: the binary form `X^w - Y^w`.

## Main results

* `TauCeti.mem_periodPolynomials_binaryFormRep_parity`: for even `w`, the parity involution
  preserves `W_w`.
* `TauCeti.evenPeriodPolynomials_sup_oddPeriodPolynomials` and
  `TauCeti.disjoint_evenPeriodPolynomials_oddPeriodPolynomials`: `W_w = W_w^+ ⊕ W_w^-` when
  `2` is invertible (spanning) and multiplication by `2` is injective (disjointness).
* `TauCeti.periodPolynomials_eq_bot_of_odd`: `W_w = 0` for odd `w` when multiplication by `2`
  is injective.
* `TauCeti.mem_evenPeriodPolynomials_eisensteinPeriodPolynomial`: `X^w - Y^w ∈ W_w^+` for even
  `w`.

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

/-- The right action `P ↦ P ∣ M` of integral `2 × 2` matrices on binary forms of degree `w`,
`(P ∣ M)(X, Y) = P(aX + bY, cX + dY)` for `M = !![a, b; c, d]`, as a representation of the
opposite matrix monoid. -/
noncomputable def binaryFormRep :
    Representation R (Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ (homogeneousSubmodule (Fin 2) R w) :=
  (linearSubstRep (Fin 2) R w).comp
    (MonoidHom.op (Int.castRingHom R).mapMatrix.toMonoidHom)

variable {R w}

@[simp]
theorem coe_binaryFormRep_apply (M : Matrix (Fin 2) (Fin 2) ℤ)
    (P : homogeneousSubmodule (Fin 2) R w) :
    (binaryFormRep R w (op M) P : MvPolynomial (Fin 2) R) =
      linearSubst (M.map (Int.cast : ℤ → R)) P := by
  simp [binaryFormRep]

/-- The action is on the right: `P ∣ (M * N) = (P ∣ M) ∣ N`. -/
theorem binaryFormRep_op_mul_apply (M N : Matrix (Fin 2) (Fin 2) ℤ)
    (P : homogeneousSubmodule (Fin 2) R w) :
    binaryFormRep R w (op (M * N)) P = binaryFormRep R w (op N) (binaryFormRep R w (op M) P) := by
  rw [op_mul, map_mul, Module.End.mul_apply]

/-- Negating the matrix multiplies a form of degree `w` by `(-1)ʷ`. -/
theorem binaryFormRep_op_neg (M : Matrix (Fin 2) (Fin 2) ℤ) :
    binaryFormRep R w (op (-M)) = (-1 : R) ^ w • binaryFormRep R w (op M) := by
  refine LinearMap.ext fun P ↦ Subtype.ext ?_
  simp only [coe_binaryFormRep_apply, LinearMap.smul_apply, Submodule.coe_smul]
  rw [Matrix.map_neg _ Int.cast_neg, P.2.linearSubst_neg]

/-- For even `w`, a matrix and its negative act in the same way. -/
theorem binaryFormRep_op_neg_of_even (hw : Even w) (M : Matrix (Fin 2) (Fin 2) ℤ) :
    binaryFormRep R w (op (-M)) = binaryFormRep R w (op M) := by
  rw [binaryFormRep_op_neg, hw.neg_one_pow, one_smul]

variable (R w)

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
  have hεε : ∀ Q, binaryFormRep R w (op !![-1, 0; 0, 1]) (binaryFormRep R w (op !![-1, 0; 0, 1]) Q)
      = Q := fun Q ↦ by
    rw [← binaryFormRep_op_mul_apply, parity_mul_parity, op_one, map_one, Module.End.one_apply]
  have hεP := mem_periodPolynomials_binaryFormRep_parity hw hP
  refine Submodule.mem_sup.2 ⟨⅟(2 : R) • (P + binaryFormRep R w (op !![-1, 0; 0, 1]) P), ?_,
    ⅟(2 : R) • (P - binaryFormRep R w (op !![-1, 0; 0, 1]) P), ?_, ?_⟩
  · refine mem_evenPeriodPolynomials_iff.2
      ⟨Submodule.smul_mem _ _ (Submodule.add_mem _ hP hεP), ?_⟩
    rw [map_smul, map_add, hεε, add_comm]
  · refine mem_oddPeriodPolynomials_iff.2
      ⟨Submodule.smul_mem _ _ (Submodule.sub_mem _ hP hεP), ?_⟩
    rw [map_smul, map_sub, hεε, ← neg_sub, smul_neg]
  · rw [← smul_add, add_add_sub_cancel, ← two_smul R P, smul_smul, invOf_mul_self, one_smul]

private lemma eq_zero_of_add_self_eq_zero
    (h2 : Function.Injective fun r : R ↦ 2 * r)
    {P : homogeneousSubmodule (Fin 2) R w} (h : P + P = 0) : P = 0 := by
  refine Subtype.ext (MvPolynomial.ext _ _ fun m ↦ ?_)
  have hm : (P : MvPolynomial (Fin 2) R).coeff m + (P : MvPolynomial (Fin 2) R).coeff m = 0 := by
    simpa using congrArg (fun Q : homogeneousSubmodule (Fin 2) R w ↦
      (Q : MvPolynomial (Fin 2) R).coeff m) h
  apply h2
  simpa [two_mul] using hm

/-- A period polynomial cannot be both even and odd when multiplication by `2` is injective. -/
theorem disjoint_evenPeriodPolynomials_oddPeriodPolynomials
    (h2 : Function.Injective fun r : R ↦ 2 * r) :
    Disjoint (evenPeriodPolynomials R w) (oddPeriodPolynomials R w) :=
  Submodule.disjoint_def.2 fun _ hP hP' ↦ eq_zero_of_add_self_eq_zero h2 <| eq_neg_iff_add_eq_zero.1
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
  refine (Submodule.eq_bot_iff _).2 fun P hP ↦ eq_zero_of_add_self_eq_zero h2 ?_
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

end TauCeti
