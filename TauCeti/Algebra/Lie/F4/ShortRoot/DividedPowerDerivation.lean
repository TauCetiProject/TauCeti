/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Derivation

/-!
# Divided-power exponentials of a derivation of the type-F4 multiplication

A divided-power exponential `1 + t N + t² P` of a nilpotent integral matrix `N` with divided
square `P` is multiplicative for the invariant multiplication of the twenty-six-dimensional module
of type `F₄` as soon as `N` differentiates that multiplication. Expanding the multiplicativity
equation in the parameter produces four coefficient conditions, one for each of the degrees one to
four; this file shows that the first of them, which is exactly the derivation property of `N`,
implies the other three, and then assembles the expansion.

The three implications are formal consequences of the derivation property together with the
divided-power relations `N² = 2 P`, `N P = P N = 0` and `P² = 0`, obtained by iterating the
adjoint action of `N` on an operator of multiplication by a vector. Iterating it twice identifies
the divided adjoint `Z ↦ P Z - N Z N + Z P` on those operators; iterating it three times, where
the cube of `N` vanishes, gives the commutation `N Z P = P Z N` from which the two top-degree
conditions follow. Each step divides an identity by a nonzero integer, which is legitimate because
the integer matrices are torsion free, and this is where the divided powers are used.

Nothing below verifies the derivation property for any particular matrix.

## Main results

* `TauCeti.F4ShortRoot.multiplicationBy_mulVec_dividedSquare`: the divided adjoint of an operator
  of multiplication by a vector.
* `TauCeti.F4ShortRoot.preservesMultiplication_one_add_smul_add_smul`: **a divided-power
  exponential of a derivation is multiplicative**, over every commutative ring.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Yale (1967), §2.
* B. Kostant, *Groups over `ℤ`*, Proc. Sympos. Pure Math. **IX** (1966), for the divided powers.
-/

public section

open Matrix

namespace TauCeti.F4ShortRoot

universe u

variable {R : Type u} [CommRing R] {N P : Matrix (Fin 26) (Fin 26) ℤ}

/-- Entrywise integer casts turn a matrix sum into the sum of the casts. -/
private theorem map_intCast_add (M M' : Matrix (Fin 26) (Fin 26) ℤ) :
    (M + M').map (Int.cast : ℤ → R) =
      M.map (Int.cast : ℤ → R) + M'.map (Int.cast : ℤ → R) := by
  ext a b
  rw [Matrix.map_apply, Matrix.add_apply, Matrix.add_apply, Int.cast_add, Matrix.map_apply,
    Matrix.map_apply]

/-- Entrywise integer casts turn a matrix difference into the difference of the casts. -/
private theorem map_intCast_sub (M M' : Matrix (Fin 26) (Fin 26) ℤ) :
    (M - M').map (Int.cast : ℤ → R) =
      M.map (Int.cast : ℤ → R) - M'.map (Int.cast : ℤ → R) := by
  ext a b
  rw [Matrix.map_apply, Matrix.sub_apply, Matrix.sub_apply, Int.cast_sub, Matrix.map_apply,
    Matrix.map_apply]

/-- Entrywise integer casts turn a matrix product into the product of the casts. -/
private theorem map_intCast_mul' (M M' : Matrix (Fin 26) (Fin 26) ℤ) :
    (M * M').map (Int.cast : ℤ → R) =
      M.map (Int.cast : ℤ → R) * M'.map (Int.cast : ℤ → R) :=
  Matrix.map_mul (f := (Int.castRingHom R))

/-- Entrywise integer casts send the zero matrix to the zero matrix. -/
private theorem map_intCast_zero :
    (0 : Matrix (Fin 26) (Fin 26) ℤ).map (Int.cast : ℤ → R) = 0 := by
  ext a b
  rw [Matrix.map_apply, Matrix.zero_apply, Matrix.zero_apply, Int.cast_zero]

/-- Integer matrices are torsion free. -/
private theorem smul_cancel {c : ℤ} (hc : c ≠ 0) {A B : Matrix (Fin 26) (Fin 26) ℤ}
    (h : c • A = c • B) : A = B := by
  ext a b
  have hab := congrFun (congrFun h a) b
  rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul] at hab
  exact mul_left_cancel₀ hc hab

variable (hN : IsDerivation N) (hNN : N * N = (2 : ℤ) • P)

include hN hNN

/-- **The divided adjoint of an operator of multiplication by a vector.** Applying the adjoint
action of a derivation twice and halving identifies the divided adjoint of the operator of
multiplication by a vector with the operator of multiplication by the divided square of that
vector. -/
theorem multiplicationBy_mulVec_dividedSquare (v : Fin 26 → ℤ) :
    P * multiplicationBy v - N * multiplicationBy v * N + multiplicationBy v * P =
      multiplicationBy (P *ᵥ v) := by
  have hone : ∀ w : Fin 26 → ℤ, N * multiplicationBy w - multiplicationBy w * N =
      multiplicationBy (N *ᵥ w) := hN.mulVec
  have hvec : N *ᵥ (N *ᵥ v) = (2 : ℤ) • (P *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, hNN, Matrix.smul_mulVec]
  have hright : multiplicationBy (N *ᵥ (N *ᵥ v)) = (2 : ℤ) • multiplicationBy (P *ᵥ v) := by
    rw [hvec, multiplicationBy_smul]
  have hleft : N * multiplicationBy (N *ᵥ v) - multiplicationBy (N *ᵥ v) * N =
      (2 : ℤ) • (P * multiplicationBy v - N * multiplicationBy v * N + multiplicationBy v * P) := by
    rw [← hone v]
    have hexpand : N * (N * multiplicationBy v - multiplicationBy v * N) -
        (N * multiplicationBy v - multiplicationBy v * N) * N =
          N * N * multiplicationBy v - (2 : ℤ) • (N * multiplicationBy v * N) +
            multiplicationBy v * (N * N) := by
      rw [two_smul]
      noncomm_ring
    rw [hexpand, hNN, Matrix.smul_mul, Matrix.mul_smul]
    module
  exact smul_cancel two_ne_zero (hleft.symm.trans (hone (N *ᵥ v) ▸ hright))

/-- The second coefficient condition: the divided square of a derivation commutes with an operator
of multiplication by a vector up to the operators of the transformed vectors. -/
theorem multiplicationBy_dividedSquare_commutator (v : Fin 26 → ℤ) :
    P * multiplicationBy v - multiplicationBy v * P =
      multiplicationBy (P *ᵥ v) + multiplicationBy (N *ᵥ v) * N := by
  have hone : N * multiplicationBy v - multiplicationBy v * N = multiplicationBy (N *ᵥ v) :=
    hN.mulVec v
  have hdiv := multiplicationBy_mulVec_dividedSquare hN hNN v
  have hsq : N * multiplicationBy v * N =
      multiplicationBy (N *ᵥ v) * N + multiplicationBy v * ((2 : ℤ) • P) := by
    rw [← hNN, ← hone]
    noncomm_ring
  rw [← hdiv, hsq, Matrix.mul_smul, two_smul]
  abel

variable (hPN : P * N = 0)

include hPN

/-- The commutation of a derivation and its divided square across an operator of multiplication by
a vector, from the vanishing of the cube of the derivation. -/
theorem multiplicationBy_comm_dividedSquare (v : Fin 26 → ℤ) :
    N * multiplicationBy v * P = P * multiplicationBy v * N := by
  have hone : ∀ w : Fin 26 → ℤ, N * multiplicationBy w - multiplicationBy w * N =
      multiplicationBy (N *ᵥ w) := hN.mulVec
  have hcube : N * N * N = 0 := by rw [hNN, Matrix.smul_mul, hPN, smul_zero]
  have hthird : N * (N * (N * multiplicationBy v - multiplicationBy v * N) -
      (N * multiplicationBy v - multiplicationBy v * N) * N) -
      (N * (N * multiplicationBy v - multiplicationBy v * N) -
        (N * multiplicationBy v - multiplicationBy v * N) * N) * N =
      multiplicationBy (N *ᵥ (N *ᵥ (N *ᵥ v))) := by
    rw [hone v, hone (N *ᵥ v), hone (N *ᵥ (N *ᵥ v))]
  have hzero : multiplicationBy (N *ᵥ (N *ᵥ (N *ᵥ v))) = 0 := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcube, Matrix.zero_mulVec]
    rw [multiplicationBy_def]
    exact Finset.sum_eq_zero fun a _ => by rw [Pi.zero_apply, zero_smul]
  rw [hzero] at hthird
  have hexpand : N * (N * (N * multiplicationBy v - multiplicationBy v * N) -
      (N * multiplicationBy v - multiplicationBy v * N) * N) -
      (N * (N * multiplicationBy v - multiplicationBy v * N) -
        (N * multiplicationBy v - multiplicationBy v * N) * N) * N =
      N * N * N * multiplicationBy v - (3 : ℤ) • (N * N * multiplicationBy v * N) +
        (3 : ℤ) • (N * multiplicationBy v * (N * N)) - multiplicationBy v * (N * N * N) := by
    rw [show (3 : ℤ) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul]
    noncomm_ring
  rw [hexpand, hcube, hNN] at hthird
  have hsimp : (0 : Matrix (Fin 26) (Fin 26) ℤ) * multiplicationBy v -
      (3 : ℤ) • ((2 : ℤ) • P * multiplicationBy v * N) +
      (3 : ℤ) • (N * multiplicationBy v * ((2 : ℤ) • P)) - multiplicationBy v * 0 =
      (6 : ℤ) • (N * multiplicationBy v * P - P * multiplicationBy v * N) := by
    rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul, smul_sub]
    norm_num
    noncomm_ring
  rw [hsimp] at hthird
  have := smul_cancel (c := (6 : ℤ)) (by norm_num) (hthird.trans (by rw [smul_zero]))
  rw [sub_eq_zero] at this
  exact this

variable (hNP : N * P = 0) (hPP : P * P = 0)

include hNP

/-- The third coefficient condition: the two top operators of multiplication by transformed
vectors annihilate the derivation and its divided square. -/
theorem multiplicationBy_mulVec_dividedSquare_mul (v : Fin 26 → ℤ) :
    multiplicationBy (P *ᵥ v) * N + multiplicationBy (N *ᵥ v) * P = 0 := by
  have hone : N * multiplicationBy v - multiplicationBy v * N = multiplicationBy (N *ᵥ v) :=
    hN.mulVec v
  have hdiv := multiplicationBy_mulVec_dividedSquare hN hNN v
  have hcomm := multiplicationBy_comm_dividedSquare hN hNN hPN v
  have hleft : multiplicationBy (P *ᵥ v) * N =
      P * multiplicationBy v * N - N * multiplicationBy v * (N * N) +
        multiplicationBy v * (P * N) := by
    rw [← hdiv]
    noncomm_ring
  have hright : multiplicationBy (N *ᵥ v) * P =
      N * multiplicationBy v * P - multiplicationBy v * (N * P) := by
    rw [← hone]
    noncomm_ring
  rw [hleft, hright, hNN, hPN, hNP, Matrix.mul_smul, hcomm]
  module

include hPP

/-- The fourth coefficient condition: the operator of multiplication by the divided square of a
vector annihilates the divided square of the derivation. -/
theorem multiplicationBy_mulVec_dividedSquare_mul_dividedSquare (v : Fin 26 → ℤ) :
    multiplicationBy (P *ᵥ v) * P = 0 := by
  have hdiv := multiplicationBy_mulVec_dividedSquare hN hNN v
  have hcomm := multiplicationBy_comm_dividedSquare hN hNN hPN v
  have hstep : multiplicationBy (P *ᵥ v) * P = P * multiplicationBy v * P := by
    rw [← hdiv]
    have hexp : (P * multiplicationBy v - N * multiplicationBy v * N +
        multiplicationBy v * P) * P = P * multiplicationBy v * P -
          N * multiplicationBy v * (N * P) + multiplicationBy v * (P * P) := by noncomm_ring
    rw [hexp, hNP, hPP, mul_zero, mul_zero]
    abel
  have hkey : (2 : ℤ) • (P * multiplicationBy v * P) = 0 := by
    have h : N * (N * multiplicationBy v * P) = N * (P * multiplicationBy v * N) := by
      rw [hcomm]
    have hl : N * (N * multiplicationBy v * P) = N * N * multiplicationBy v * P := by noncomm_ring
    have hr : N * (P * multiplicationBy v * N) = (N * P) * multiplicationBy v * N := by noncomm_ring
    rw [hl, hr, hNP, hNN, Matrix.smul_mul, Matrix.smul_mul] at h
    rw [h, Matrix.zero_mul, Matrix.zero_mul]
  rw [hstep]
  exact smul_cancel (c := (2 : ℤ)) two_ne_zero (by rw [hkey, smul_zero])

/-! ## The coefficient conditions on the columns -/

omit hNN hPN hNP hPP in
/-- The derivation equation on the `k`th column. -/
theorem multiplicationOperator_column_derivation (k : Fin 26) :
    N * multiplicationOperator k - multiplicationOperator k * N =
      multiplicationBy fun a => N a k := by
  rw [multiplicationBy_int]
  exact (isDerivation_int_iff N).mp hN k

omit hPN hNP hPP in
/-- The second coefficient condition on the `k`th column. -/
theorem multiplicationOperator_column_dividedSquare (k : Fin 26) :
    P * multiplicationOperator k - multiplicationOperator k * P =
      multiplicationBy (fun a => P a k) + multiplicationBy (fun a => N a k) * N := by
  have h := multiplicationBy_dividedSquare_commutator hN hNN
    (fun a => if a = k then (1 : ℤ) else 0)
  rwa [multiplicationBy_single_int, mulVec_single, mulVec_single] at h

omit hPP in
/-- The third coefficient condition on the `k`th column. -/
theorem multiplicationOperator_column_mul (k : Fin 26) :
    multiplicationBy (fun a => P a k) * N + multiplicationBy (fun a => N a k) * P = 0 := by
  have h := multiplicationBy_mulVec_dividedSquare_mul hN hNN hPN hNP
    (fun a => if a = k then (1 : ℤ) else 0)
  rwa [mulVec_single, mulVec_single] at h

/-- The fourth coefficient condition on the `k`th column. -/
theorem multiplicationOperator_column_mul_dividedSquare (k : Fin 26) :
    multiplicationBy (fun a => P a k) * P = 0 := by
  have h := multiplicationBy_mulVec_dividedSquare_mul_dividedSquare hN hNN hPN hNP hPP
    (fun a => if a = k then (1 : ℤ) else 0)
  rwa [mulVec_single] at h

/-! ## The divided-power exponential -/

/-- **A divided-power exponential of a derivation preserves the multiplication**, over every
commutative ring. The hypotheses are the derivation property of `N`, and the divided-power
relations between `N` and its divided square `P`. -/
theorem preservesMultiplication_one_add_smul_add_smul (t : R) :
    PreservesMultiplication
      (1 + t • N.map (Int.cast : ℤ → R) + t ^ 2 • P.map (Int.cast : ℤ → R)) := by
  rw [preservesMultiplication_def]
  intro k
  have hcast : ∀ M M' : Matrix (Fin 26) (Fin 26) ℤ, M = M' →
      M.map (Int.cast : ℤ → R) = M'.map (Int.cast : ℤ → R) := fun M M' h => by rw [h]
  have f1 : N.map (Int.cast : ℤ → R) * (multiplicationOperator k).map (Int.cast : ℤ → R) =
      multiplicationBy (fun a => ((N a k : ℤ) : R)) +
        (multiplicationOperator k).map (Int.cast : ℤ → R) * N.map (Int.cast : ℤ → R) := by
    have h := hcast _ _ (multiplicationOperator_column_derivation hN k)
    rw [map_intCast_sub, map_intCast_mul', map_intCast_mul', map_multiplicationBy,
      sub_eq_iff_eq_add'] at h
    rw [h]
    abel
  have f2 : P.map (Int.cast : ℤ → R) * (multiplicationOperator k).map (Int.cast : ℤ → R) =
      multiplicationBy (fun a => ((P a k : ℤ) : R)) +
        multiplicationBy (fun a => ((N a k : ℤ) : R)) * N.map (Int.cast : ℤ → R) +
        (multiplicationOperator k).map (Int.cast : ℤ → R) * P.map (Int.cast : ℤ → R) := by
    have h := hcast _ _ (multiplicationOperator_column_dividedSquare hN hNN k)
    rw [map_intCast_sub, map_intCast_mul', map_intCast_mul', map_intCast_add, map_intCast_mul',
      map_multiplicationBy, map_multiplicationBy, sub_eq_iff_eq_add'] at h
    rw [h]
    abel
  have f3 : multiplicationBy (fun a => ((P a k : ℤ) : R)) * N.map (Int.cast : ℤ → R) +
      multiplicationBy (fun a => ((N a k : ℤ) : R)) * P.map (Int.cast : ℤ → R) = 0 := by
    have h := hcast _ _ (multiplicationOperator_column_mul hN hNN hPN hNP k)
    rwa [map_intCast_add, map_intCast_mul', map_intCast_mul', map_multiplicationBy,
      map_multiplicationBy, map_intCast_zero] at h
  have f4 : multiplicationBy (fun a => ((P a k : ℤ) : R)) * P.map (Int.cast : ℤ → R) = 0 := by
    have h := hcast _ _ (multiplicationOperator_column_mul_dividedSquare hN hNN hPN hNP hPP k)
    rwa [map_intCast_mul', map_multiplicationBy, map_intCast_zero] at h
  have hcol : (fun a => (1 + t • N.map (Int.cast : ℤ → R) +
        t ^ 2 • P.map (Int.cast : ℤ → R)) a k) =
      (fun a => if a = k then (1 : R) else 0) + t • (fun a => ((N a k : ℤ) : R)) +
        t ^ 2 • fun a => ((P a k : ℤ) : R) := by
    funext a
    simp [Matrix.one_apply, Matrix.map_apply]
  rw [hcol, multiplicationBy_add, multiplicationBy_add, multiplicationBy_smul,
    multiplicationBy_smul, multiplicationBy_single]
  rw [Matrix.add_mul, Matrix.add_mul, one_mul, Matrix.smul_mul, Matrix.smul_mul]
  have expandR : ((multiplicationOperator k).map (Int.cast : ℤ → R) +
        t • multiplicationBy (fun a => ((N a k : ℤ) : R)) +
        t ^ 2 • multiplicationBy (fun a => ((P a k : ℤ) : R))) *
      (1 + t • N.map (Int.cast : ℤ → R) + t ^ 2 • P.map (Int.cast : ℤ → R)) =
      (multiplicationOperator k).map (Int.cast : ℤ → R) +
        t • (multiplicationBy (fun a => ((N a k : ℤ) : R)) +
          (multiplicationOperator k).map (Int.cast : ℤ → R) * N.map (Int.cast : ℤ → R)) +
        t ^ 2 • (multiplicationBy (fun a => ((P a k : ℤ) : R)) +
          multiplicationBy (fun a => ((N a k : ℤ) : R)) * N.map (Int.cast : ℤ → R) +
          (multiplicationOperator k).map (Int.cast : ℤ → R) * P.map (Int.cast : ℤ → R)) +
        t ^ 3 • (multiplicationBy (fun a => ((P a k : ℤ) : R)) * N.map (Int.cast : ℤ → R) +
          multiplicationBy (fun a => ((N a k : ℤ) : R)) * P.map (Int.cast : ℤ → R)) +
        t ^ 4 • (multiplicationBy (fun a => ((P a k : ℤ) : R)) * P.map (Int.cast : ℤ → R)) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, mul_one,
      smul_smul, smul_add]
    module
  rw [expandR, f1, f2, f3, f4, smul_zero, smul_zero, add_zero, add_zero]

end TauCeti.F4ShortRoot
