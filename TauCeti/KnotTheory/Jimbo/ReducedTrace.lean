/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Jimbo.Enhancement.Laurent
public import TauCeti.KnotTheory.Jimbo.Normalization
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import TauCeti.KnotTheory.Markov.Skein

/-!
# The reduced Jimbo trace

The writhe-normalized Jimbo trace assigns the quantum dimension to the unknot.
Over a field, dividing by that dimension gives the reduced `sl_N` specialization
of HOMFLY, `MarkovBraid.jimboReducedTrace`, with unknot value one whenever the
quantum dimension is nonzero. It retains Markov invariance and the skein relation
with `a = q ^ N` and `z = q - q⁻¹`. The field quotient uses total division, so at
a zero quantum dimension it vanishes rather than giving an unknot-normalized
invariant.

For positive `N`, the writhe-normalized trace at the generic Laurent unit `T` of
`ℤ[T, T⁻¹]` is divisible in `ℤ[T, T⁻¹]` by the nonzero generic quantum dimension
(`[N]_T ≠ 0`, `KnotTheory.jimboWeight_sum_genericUnit_ne_zero`). Its Laurent
polynomial quotient `MarkovBraid.jimboReducedLaurent` evaluates along
`LaurentPolynomial.eval₂ (Int.castRingHom R) q` at every unit `q : Rˣ` of every
commutative ring `R`: over a field with nonzero quantum dimension it agrees with
`MarkovBraid.jimboReducedTrace`, while at any zero-factor specialization `(q : R) - ↑q⁻¹ = 0` it
remains regular (`MarkovBraid.eval₂_jimboReducedLaurent_of_sub_inv_eq_zero`), evaluating at `q = 1`
to `N ^ (β.componentCount - 1)` and at `q = -1` to `((-1) ^ (N - 1) * N) ^ (β.componentCount - 1)`.

## References

* V. G. Turaev, *The Yang-Baxter equation and invariants of links*, Invent. Math.
  92 (1988), 527–553 (the normalization of enhanced braid traces).
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388.

The construction uses `MarkovBraid.jimboTrace`, and the calculations use its
skein relation, `jimboWeight_sum`, and `MarkovBraid.eq_of_skein`.
-/

public section

namespace TauCeti

open KnotTheory
open scoped BigOperators

variable {K : Type*} [Field K] {N n : ℕ}

namespace MarkovBraid

/-- Divide the writhe-normalized Jimbo trace by its unknot value. This gives the
reduced `sl_N` specialization when the quantum dimension is nonzero. -/
noncomputable def jimboReducedTrace (β : MarkovBraid) (q : Kˣ) : K :=
  β.jimboTrace (N := N) q / ∑ a : Fin N, jimboWeight q a

/-- The reduced trace is the normalized trace divided by the quantum dimension. -/
theorem jimboReducedTrace_def (β : MarkovBraid) (q : Kˣ) :
    β.jimboReducedTrace (N := N) q =
      β.jimboTrace (N := N) q / ∑ a : Fin N, jimboWeight q a := (rfl)

/-- Conjugation preserves the reduced trace. -/
@[simp]
theorem jimboReducedTrace_conj (q : Kˣ) (b c : BraidGroup (n + 1)) :
    jimboReducedTrace (N := N) ⟨n, c * b * c⁻¹⟩ q =
      jimboReducedTrace (N := N) ⟨n, b⟩ q := by
  simp only [jimboReducedTrace_def, jimboTrace_conj]

/-- Positive Markov stabilization preserves the reduced trace. -/
@[simp]
theorem jimboReducedTrace_stabilize (q : Kˣ) (b : BraidGroup (n + 1)) :
    jimboReducedTrace (N := N)
        ⟨n + 1, BraidGroup.strandIncl b * BraidGroup.sigma (Fin.last n)⟩ q =
      jimboReducedTrace (N := N) ⟨n, b⟩ q := by
  simp only [jimboReducedTrace_def, jimboTrace_stabilize]

/-- Negative Markov stabilization preserves the reduced trace. -/
@[simp]
theorem jimboReducedTrace_stabilizeInv (q : Kˣ) (b : BraidGroup (n + 1)) :
    jimboReducedTrace (N := N)
        ⟨n + 1, BraidGroup.strandIncl b * (BraidGroup.sigma (Fin.last n))⁻¹⟩ q =
      jimboReducedTrace (N := N) ⟨n, b⟩ q := by
  simp only [jimboReducedTrace_def, jimboTrace_stabilizeInv]

/-- Multiplying the reduced trace by the nonzero quantum dimension recovers the
writhe-normalized trace. -/
@[simp]
theorem jimboReducedTrace_mul_sum (β : MarkovBraid) (q : Kˣ)
    (hδ : (∑ a : Fin N, jimboWeight q a) ≠ 0) :
    β.jimboReducedTrace (N := N) q * (∑ a : Fin N, jimboWeight q a) =
      β.jimboTrace (N := N) q := by
  rw [jimboReducedTrace_def, div_mul_cancel₀ _ hδ]

/-- The `(n + 1)`-component unlink has reduced trace equal to the `n`-th power
of the quantum dimension. In particular the one-strand unknot has value one. -/
@[simp]
theorem jimboReducedTrace_one (q : Kˣ)
    (hδ : (∑ a : Fin N, jimboWeight q a) ≠ 0) :
    jimboReducedTrace (N := N) ⟨n, 1⟩ q = (∑ a : Fin N, jimboWeight q a) ^ n := by
  rw [jimboReducedTrace_def, jimboTrace_one, pow_succ, mul_div_cancel_right₀ _ hδ]

/-- The reduced trace satisfies the oriented HOMFLY skein relation in any braid context. -/
theorem jimboReducedTrace_skein (q : Kˣ) (b c : BraidGroup (n + 1)) (i : Fin n) :
    ↑(q ^ N) * jimboReducedTrace (N := N)
        ⟨n, b * BraidGroup.sigma (n := n + 1) i * c⟩ q -
      ↑((q⁻¹) ^ N) * jimboReducedTrace (N := N)
        ⟨n, b * (BraidGroup.sigma (n := n + 1) i)⁻¹ * c⟩ q =
      ((q : K) - ↑(q⁻¹)) * jimboReducedTrace (N := N) ⟨n, b * c⟩ q := by
  simp only [jimboReducedTrace_def, ← mul_div_assoc, ← sub_div]
  rw [jimboTrace_skein]

end MarkovBraid

/-- Markov-equivalent braids have the same reduced Jimbo trace. -/
theorem MarkovEquiv.jimboReducedTrace_eq {β γ : MarkovBraid} (h : MarkovEquiv β γ)
    (q : Kˣ) : β.jimboReducedTrace (N := N) q = γ.jimboReducedTrace (N := N) q := by
  rw [MarkovBraid.jimboReducedTrace_def, MarkovBraid.jimboReducedTrace_def,
    h.jimboTrace_eq q]

namespace MarkovBraid

/-- The closure of the positive two-strand braid `σ₀ ^ 3` has the reduced
trefoil value `a⁻² (z² + 2) - a⁻⁴`, where `a = q ^ N` and `z = q - q⁻¹`. -/
theorem jimboReducedTrace_trefoil (q : Kˣ)
    (hδ : (∑ a : Fin N, jimboWeight q a) ≠ 0) :
    jimboReducedTrace (N := N) ⟨1, BraidGroup.sigma (n := 2) 0 ^ 3⟩ q =
      (↑((q⁻¹) ^ N) : K) ^ 2 * (((q : K) - ↑(q⁻¹)) ^ 2 + 2) -
        (↑((q⁻¹) ^ N) : K) ^ 4 := by
  let s : BraidGroup 2 := BraidGroup.sigma 0
  have hs : jimboReducedTrace (N := N) ⟨1, s⟩ q = 1 := by
    simpa [s, Fin.last, hδ] using
      (markovEquiv_sigma_last_one_one.jimboReducedTrace_eq (N := N) q)
  have h₂ := jimboReducedTrace_skein (N := N) q s 1 (0 : Fin 1)
  have h₃ := jimboReducedTrace_skein (N := N) q (s ^ 2) 1 (0 : Fin 1)
  have hsig : BraidGroup.sigma (n := 2) 0 = s := rfl
  rw [hsig] at h₂ h₃
  -- Normalize the braid products to powers before using the two skein equations.
  simp only [mul_one] at h₂
  rw [← pow_two, mul_inv_cancel] at h₂
  simp only [jimboReducedTrace_one q hδ, pow_one, hs, mul_one] at h₂
  have hcancel : s ^ 2 * s⁻¹ = s := by group
  simp only [mul_one, ← pow_succ, hcancel, hs, mul_one] at h₃
  have hdim := jimboWeight_sum (N := N) q
  have ha : (↑(q ^ N) : K) * ↑((q⁻¹) ^ N) = 1 := by
    rw [inv_pow]
    exact Units.mul_inv _
  -- Eliminate the two-crossing value and the quantum dimension from the skein equations.
  linear_combination
    (↑((q⁻¹) ^ N) : K) ^ 2 * ↑(q ^ N) * h₃ +
    (↑((q⁻¹) ^ N) : K) ^ 2 * ((q : K) - ↑(q⁻¹)) * h₂ +
    (↑((q⁻¹) ^ N) : K) ^ 3 * hdim -
    (jimboReducedTrace (N := N) ⟨1, s ^ 3⟩ q *
      (↑(q ^ N) * ↑((q⁻¹) ^ N) + 1) - 2 * (↑((q⁻¹) ^ N) : K) ^ 2) * ha

/-- With two colours the trefoil value is `q⁻² + q⁻⁶ - q⁻⁸`, the Jones value
`t + t³ - t⁴` after the substitution `t = q⁻²`. -/
theorem jimboReducedTrace_trefoil_two (q : Kˣ)
    (hδ : (∑ a : Fin 2, jimboWeight q a) ≠ 0) :
    jimboReducedTrace (N := 2) ⟨1, BraidGroup.sigma (n := 2) 0 ^ 3⟩ q =
      (↑(q⁻¹) : K) ^ 2 + (↑(q⁻¹) : K) ^ 6 - (↑(q⁻¹) : K) ^ 8 := by
  rw [jimboReducedTrace_trefoil q hδ]
  simp only [Units.val_pow_eq_pow_val]
  have ha : (q : K) * ↑(q⁻¹) = 1 := Units.mul_inv _
  linear_combination
    ((↑(q⁻¹) : K) ^ 2 * ((q : K) * ↑(q⁻¹) + 1) - 2 * (↑(q⁻¹) : K) ^ 4) * ha

end MarkovBraid

/-! ### Universal Laurent polynomial quotient and specializations -/

namespace MarkovBraid

/-- The universal reduced `N`-colour Jimbo invariant of a braid closure in `ℤ[T;T⁻¹]`, chosen as
a Laurent polynomial quotient of `jimboTrace` at `T` by `[N]_T` (unique when `N ≠ 0`, see
`jimboReducedLaurent_eq_iff`). Evaluating at any unit `q : Rˣ` of a commutative ring specializes
the reduced invariant without dividing by `[N]_q`, so zero-factor specializations such as `q = ±1`
and quantum roots of unity remain regular. -/
noncomputable def jimboReducedLaurent (β : MarkovBraid) (N : ℕ) :
    LaurentPolynomial ℤ :=
  (β.sum_jimboWeight_dvd_jimboTrace (N := N) (LaurentPolynomial.genericUnit ℤ)).choose

/-- Multiplying `jimboReducedLaurent` by the generic quantum dimension recovers `jimboTrace` at
`LaurentPolynomial.genericUnit ℤ`. -/
@[simp]
theorem jimboReducedLaurent_mul_sum (β : MarkovBraid) (N : ℕ) :
    β.jimboReducedLaurent N *
        (∑ a : Fin N, jimboWeight (LaurentPolynomial.genericUnit ℤ) a) =
      β.jimboTrace (N := N) (LaurentPolynomial.genericUnit ℤ) :=
  (mul_comm _ _).trans
    (β.sum_jimboWeight_dvd_jimboTrace (N := N) (LaurentPolynomial.genericUnit ℤ)).choose_spec.symm

/-- A Laurent polynomial equals `β.jimboReducedLaurent N` if and only if its product with the
generic quantum dimension is `β.jimboTrace` at `LaurentPolynomial.genericUnit ℤ`. -/
theorem jimboReducedLaurent_eq_iff (β : MarkovBraid) (N : ℕ) [NeZero N]
    {P : LaurentPolynomial ℤ} :
    β.jimboReducedLaurent N = P ↔
      P * (∑ a : Fin N, jimboWeight (LaurentPolynomial.genericUnit ℤ) a) =
        β.jimboTrace (N := N) (LaurentPolynomial.genericUnit ℤ) := by
  rw [← jimboReducedLaurent_mul_sum β N,
    mul_left_inj' (jimboWeight_sum_genericUnit_ne_zero ℤ N), eq_comm]

end MarkovBraid

/-- Markov-equivalent braids have the same universal reduced Jimbo Laurent polynomial. -/
theorem MarkovEquiv.jimboReducedLaurent_eq {β γ : MarkovBraid} (h : MarkovEquiv β γ)
    (N : ℕ) [NeZero N] : β.jimboReducedLaurent N = γ.jimboReducedLaurent N := by
  rw [MarkovBraid.jimboReducedLaurent_eq_iff, MarkovBraid.jimboReducedLaurent_mul_sum,
    h.jimboTrace_eq]

namespace MarkovBraid

/-- The `(n + 1)`-component unlink has universal reduced Jimbo Laurent polynomial equal to the
`n`-th power of the generic quantum dimension. -/
@[simp]
theorem jimboReducedLaurent_one (n N : ℕ) [NeZero N] :
    jimboReducedLaurent ⟨n, 1⟩ N =
      (∑ a : Fin N, jimboWeight (LaurentPolynomial.genericUnit ℤ) a) ^ n := by
  rw [jimboReducedLaurent_eq_iff, jimboTrace_one, ← pow_succ]

/-- Adding an uncrossed strand multiplies `jimboReducedLaurent` by the generic quantum dimension. -/
@[simp]
theorem jimboReducedLaurent_strandIncl {n : ℕ} (b : BraidGroup (n + 1)) (N : ℕ) [NeZero N] :
    jimboReducedLaurent ⟨n + 1, BraidGroup.strandIncl b⟩ N =
      (∑ a : Fin N, jimboWeight (LaurentPolynomial.genericUnit ℤ) a) *
        jimboReducedLaurent ⟨n, b⟩ N := by
  rw [jimboReducedLaurent_eq_iff, jimboTrace_strandIncl, mul_assoc, jimboReducedLaurent_mul_sum]

/-- The universal reduced Jimbo Laurent polynomial satisfies the oriented HOMFLY skein relation
with `a = T ^ N` and `z = T - T⁻¹` in every braid context. -/
theorem jimboReducedLaurent_skein {n : ℕ} (N : ℕ) [NeZero N]
    (b c : BraidGroup (n + 1)) (i : Fin n) :
    LaurentPolynomial.T (N : ℤ) *
        jimboReducedLaurent ⟨n, b * BraidGroup.sigma (n := n + 1) i * c⟩ N -
      LaurentPolynomial.T (-(N : ℤ)) *
        jimboReducedLaurent ⟨n, b * (BraidGroup.sigma (n := n + 1) i)⁻¹ * c⟩ N =
      (LaurentPolynomial.T 1 - LaurentPolynomial.T (-1)) *
        jimboReducedLaurent ⟨n, b * c⟩ N := by
  apply mul_right_cancel₀ (jimboWeight_sum_genericUnit_ne_zero ℤ N)
  have hs := jimboTrace_skein (N := N) (LaurentPolynomial.genericUnit ℤ) b c i
  rw [← zpow_natCast, inv_pow, ← zpow_natCast, ← zpow_neg,
    LaurentPolynomial.genericUnit_zpow_val, LaurentPolynomial.genericUnit_zpow_val,
    LaurentPolynomial.genericUnit_val, LaurentPolynomial.genericUnit_inv] at hs
  simpa only [sub_mul, mul_assoc, jimboReducedLaurent_mul_sum] using hs

/-- Evaluating `jimboReducedLaurent` at any unit `q : Rˣ` satisfies the oriented HOMFLY skein
relation with `a = q ^ N` and `z = q - q⁻¹` in every braid context. -/
theorem eval₂_jimboReducedLaurent_skein {R : Type*} [CommRing R] {n : ℕ} (N : ℕ) [NeZero N]
    (q : Rˣ) (b c : BraidGroup (n + 1)) (i : Fin n) :
    ↑(q ^ N) * LaurentPolynomial.eval₂ (Int.castRingHom R) q
        (jimboReducedLaurent ⟨n, b * BraidGroup.sigma (n := n + 1) i * c⟩ N) -
      ↑((q ^ N)⁻¹) * LaurentPolynomial.eval₂ (Int.castRingHom R) q
        (jimboReducedLaurent ⟨n, b * (BraidGroup.sigma (n := n + 1) i)⁻¹ * c⟩ N) =
      ((q : R) - ↑q⁻¹) * LaurentPolynomial.eval₂ (Int.castRingHom R) q
        (jimboReducedLaurent ⟨n, b * c⟩ N) := by
  have hs := congrArg (laurentEval (R := ℤ) q) (jimboReducedLaurent_skein N b c i)
  simp only [map_sub, map_mul, laurentEval_T, zpow_natCast, zpow_neg, zpow_one] at hs
  simpa only [laurentEval_eq_eval₂, RingHom.eq_intCast' (algebraMap ℤ R)] using hs

/-- Evaluating `jimboReducedLaurent` at any unit `q : Rˣ` and multiplying by `[N]_q` recovers the
writhe-normalized Jimbo trace `β.jimboTrace q` over any commutative ring `R`. -/
theorem eval₂_jimboReducedLaurent_mul_sum {R : Type*} [CommRing R] (β : MarkovBraid)
    (N : ℕ) (q : Rˣ) :
    LaurentPolynomial.eval₂ (Int.castRingHom R) q (β.jimboReducedLaurent N) *
        (∑ a : Fin N, jimboWeight q a) =
      β.jimboTrace (N := N) q := by
  have h := congrArg (laurentEval (R := ℤ) q).toRingHom (β.jimboReducedLaurent_mul_sum N)
  have hcoe : ((laurentEval (R := ℤ) q).toRingHom : LaurentPolynomial ℤ →* R) =
      (laurentEval (R := ℤ) q : LaurentPolynomial ℤ →* R) := by
    ext x
    simp
  have hmap : Units.map ((laurentEval (R := ℤ) q).toRingHom : LaurentPolynomial ℤ →* R)
      (LaurentPolynomial.genericUnit ℤ) = q := by
    rw [hcoe, LaurentPolynomial.map_genericUnit, laurentEvalEquiv_symm_laurentEval]
  rw [map_mul, β.map_jimboTrace, hmap] at h
  simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, laurentEval_eq_eval₂,
    RingHom.eq_intCast' (algebraMap ℤ R), eval₂_sum_jimboWeight_genericUnit] using h

/-- Over a field with nonzero quantum dimension `[N]_q ≠ 0`, evaluating `jimboReducedLaurent` at
`q` agrees with the field quotient `β.jimboReducedTrace q`. -/
theorem eval₂_jimboReducedLaurent_eq_jimboReducedTrace (β : MarkovBraid) (N : ℕ)
    (q : Kˣ) (hδ : (∑ a : Fin N, jimboWeight q a) ≠ 0) :
    LaurentPolynomial.eval₂ (Int.castRingHom K) q (β.jimboReducedLaurent N) =
      β.jimboReducedTrace (N := N) q := by
  apply mul_right_cancel₀ hδ
  rw [eval₂_jimboReducedLaurent_mul_sum, jimboReducedTrace_mul_sum β q hδ]

/-- At any unit `q : Rˣ` satisfying `(q : R) - ↑q⁻¹ = 0` (so `q⁻¹ = q`, including `q = ±1`),
evaluating `β.jimboReducedLaurent N` at `q` gives
`(∑ a : Fin N, jimboWeight q a) ^ (β.componentCount - 1)`. -/
theorem eval₂_jimboReducedLaurent_of_sub_inv_eq_zero {R : Type*} [CommRing R] (β : MarkovBraid)
    (N : ℕ) [NeZero N] {q : Rˣ} (hq : (q : R) - ↑q⁻¹ = 0) :
    LaurentPolynomial.eval₂ (Int.castRingHom R) q (β.jimboReducedLaurent N) =
      (∑ a : Fin N, jimboWeight q a) ^ (β.componentCount - 1) := by
  have hqinv : q⁻¹ = q := Units.ext (sub_eq_zero.mp hq).symm
  have hε : ((q ^ N)⁻¹ : Rˣ) = q ^ N := by rw [← inv_pow, hqinv]
  refine congrFun (eq_of_skein (q ^ N) (0 : R) (∑ a : Fin N, jimboWeight q a)
    (F := fun γ ↦ LaurentPolynomial.eval₂ (Int.castRingHom R) q (γ.jimboReducedLaurent N))
    (G := fun γ ↦ (∑ a : Fin N, jimboWeight q a) ^ (γ.componentCount - 1))
    (fun _ _ h ↦ congrArg _ (h.jimboReducedLaurent_eq N))
    (fun _ _ h ↦ by rw [h.componentCount_eq]) ?_ ?_ ?_ ?_ ?_) β
  · intro m c i
    simpa only [one_mul, smul_eq_mul, hq, zero_mul] using
      eval₂_jimboReducedLaurent_skein N q 1 c i
  · intro m c i
    have hc := componentCount_mul_sigma_inv_mul 1 c i
    simp only [one_mul] at hc
    simp [hc, hε]
  · intro m b
    rw [jimboReducedLaurent_strandIncl, map_mul, eval₂_sum_jimboWeight_genericUnit, smul_eq_mul]
  · intro m b
    have hpos : 1 ≤ componentCount ⟨m, b⟩ := componentCount_pos ⟨m, b⟩
    have he : componentCount ⟨m, b⟩ + 1 - 1 = (componentCount ⟨m, b⟩ - 1) + 1 := by omega
    rw [componentCount_strandIncl, he, pow_succ', smul_eq_mul]
  · simp

/-- Specializing `jimboReducedLaurent` at the zero-factor parameter `q = 1` gives
`N ^ (β.componentCount - 1)` over any commutative ring, even though `q - q⁻¹ = 0`. -/
@[simp]
theorem eval₂_jimboReducedLaurent_one {R : Type*} [CommRing R] (β : MarkovBraid)
    (N : ℕ) [NeZero N] :
    LaurentPolynomial.eval₂ (Int.castRingHom R) (1 : Rˣ) (β.jimboReducedLaurent N) =
      (N : R) ^ (β.componentCount - 1) := by
  simpa using β.eval₂_jimboReducedLaurent_of_sub_inv_eq_zero (q := (1 : Rˣ)) N (by simp)

/-- Specializing `jimboReducedLaurent` at the zero-factor parameter `q = -1` gives
`((-1) ^ (N - 1) * N) ^ (β.componentCount - 1)` over any commutative ring. -/
@[simp]
theorem eval₂_jimboReducedLaurent_neg_one {R : Type*} [CommRing R] (β : MarkovBraid)
    (N : ℕ) [NeZero N] :
    LaurentPolynomial.eval₂ (Int.castRingHom R) (-1 : Rˣ) (β.jimboReducedLaurent N) =
      ((-1 : R) ^ (N - 1) * (N : R)) ^ (β.componentCount - 1) := by
  simpa [mul_comm (N : R)] using
    β.eval₂_jimboReducedLaurent_of_sub_inv_eq_zero (q := (-1 : Rˣ)) N (by simp)

end MarkovBraid

end TauCeti
