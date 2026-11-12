/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Infinite

/-!
# Jucys–Murphy elements of the type-A Hecke algebra

Write `Q = q²` and `gᵢ = q • T i`, so that `(gᵢ + 1) * (gᵢ - Q) = 0`. The normalized
Jucys–Murphy elements of the infinite type-A Hecke algebra are defined by
`J₀ = 1` and `Jₖ₊₁ = Q⁻¹ gₖ Jₖ gₖ = T k * Jₖ * T k`, and the rescaled (additive) ones by
`L₀ = 0` and `Lₖ₊₁ = Q⁻¹ gₖ Lₖ gₖ + Q⁻¹ gₖ = T k * Lₖ * T k + q⁻¹ • T k`. Strands are counted
from `0`, so `Jₖ` is the element attached to strand `k`, written `J_(k+1)` in one-based notation.

The rescaled elements are defined by their own recursion, over every commutative ring and every
unit `q`, rather than by dividing by `Q - 1`. They are related to the normalized elements by
`Jₖ = 1 + (Q - 1) • Lₖ`
(`TauCeti.InfiniteTypeAHeckeAlgebra.jucysMurphy_eq_one_add_smul_additiveJucysMurphy`). For
`Q = 1` the normalized elements are all `1`, while the rescaled ones satisfy the additive
recursion `Lₖ₊₁ = gₖ Lₖ gₖ + gₖ` of the Jucys–Murphy elements of the symmetric group, where now
`gₖ * gₖ = 1`. For `Q - 1` a unit, `Lₖ = (Q - 1)⁻¹ • (Jₖ - 1)`.

The element `Jₖ` lies in the stage of the first `k + 1` strands and commutes with the stage of
the first `k` strands. Hence the Jucys–Murphy elements commute pairwise, and `T i` commutes with
`Jₖ` unless `i + 1 = k` or `i = k`. The generator `T k` commutes with the elementary symmetric
expressions `Jₖ + Jₖ₊₁` and `Jₖ * Jₖ₊₁` in the two Jucys–Murphy elements it moves. On the
index and sign characters, which are the one-dimensional representations of the one-row and
one-column partitions, `Jₖ` acts by `Q ^ k` and `Q⁻¹ ^ k` and `Lₖ` by the quantum integer
`[k]_Q = 1 + Q + ⋯ + Q ^ (k - 1)` and by `[-k]_Q`: the contents of the box added at strand `k`.

## Main definitions

* `TauCeti.InfiniteTypeAHeckeAlgebra.jucysMurphy`: the normalized Jucys–Murphy elements `Jₖ`.
* `TauCeti.InfiniteTypeAHeckeAlgebra.additiveJucysMurphy`: the rescaled Jucys–Murphy elements
  `Lₖ`.

## Main results

* `TauCeti.InfiniteTypeAHeckeAlgebra.jucysMurphy_eq_one_add_smul_additiveJucysMurphy`:
  `Jₖ = 1 + (Q - 1) • Lₖ`.
* `TauCeti.InfiniteTypeAHeckeAlgebra.commute_jucysMurphy_of_mem_stage` and
  `TauCeti.InfiniteTypeAHeckeAlgebra.commute_additiveJucysMurphy_of_mem_stage`: the elements
  attached to strand `k` commute with the stage of the first `k` strands.
* `TauCeti.InfiniteTypeAHeckeAlgebra.commute_jucysMurphy` and
  `TauCeti.InfiniteTypeAHeckeAlgebra.commute_additiveJucysMurphy`: the Jucys–Murphy elements
  commute pairwise.
* `TauCeti.InfiniteTypeAHeckeAlgebra.commute_T_jucysMurphy_add` and
  `TauCeti.InfiniteTypeAHeckeAlgebra.commute_T_jucysMurphy_mul`: `T k` commutes with
  `Jₖ + Jₖ₊₁` and `Jₖ * Jₖ₊₁`.

## References

* G. E. Murphy, *On the representation theory of the symmetric groups and associated Hecke
  algebras*, J. Algebra 152 (1992), 492–513.
* A. Mathas, *Iwahori–Hecke algebras and Schur algebras of the symmetric group*, University
  Lecture Series 15, AMS (1999).
-/

public section

namespace TauCeti

namespace InfiniteTypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {q : Rˣ}

/-! ### Two relations among three generators -/

/-- `T i` commutes with a conjugate `T (i + 1) * T i * x * T i * T (i + 1)` whenever `x`
commutes with `T (i + 1)`, by two applications of the braid relation. -/
private theorem commute_T_braid_conj (i : ℕ) {x : InfiniteTypeAHeckeAlgebra R q}
    (hx : Commute (T q (i + 1)) x) :
    Commute (T q i) (T q (i + 1) * T q i * x * T q i * T q (i + 1)) := by
  have hb : ∀ y : InfiniteTypeAHeckeAlgebra R q,
      T q i * (T q (i + 1) * (T q i * y)) = T q (i + 1) * (T q i * (T q (i + 1) * y)) :=
    fun y ↦ by simp only [← mul_assoc, T_braid]
  have hb' : T q (i + 1) * (T q i * T q (i + 1)) = T q i * (T q (i + 1) * T q i) := by
    simp only [← mul_assoc, T_braid]
  rw [commute_iff_eq]
  simp only [mul_assoc]
  rw [hb, ← mul_assoc (T q (i + 1)) x, hx.eq, mul_assoc x, hb']

/-- `T i` commutes with `T (i + 1) * T i * T (i + 1) + T (i + 1)`; this uses the quadratic
relation as well as the braid relation. -/
private theorem commute_T_braid_add (i : ℕ) :
    Commute (T q i) (T q (i + 1) * T q i * T q (i + 1) + T q (i + 1)) := by
  rw [commute_iff_eq, ← T_braid]
  have h₁ : T q i * (T q i * T q (i + 1) * T q i) = (T q i * T q i) * T q (i + 1) * T q i := by
    simp only [mul_assoc]
  have h₂ : T q i * T q (i + 1) * T q i * T q i = T q i * T q (i + 1) * (T q i * T q i) := by
    simp only [mul_assoc]
  rw [mul_add, add_mul, h₁, h₂, T_mul_self]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, mul_assoc]
  abel

/-! ### The normalized Jucys–Murphy elements -/

variable (q) in
/-- The normalized Jucys–Murphy element `Jₖ` attached to strand `k` (counted from `0`), defined
by `J₀ = 1` and `Jₖ₊₁ = T k * Jₖ * T k`. With `Q = q²` and `gₖ = q • T k` this is the recursion
`Jₖ₊₁ = Q⁻¹ gₖ Jₖ gₖ` (`TauCeti.InfiniteTypeAHeckeAlgebra.jucysMurphy_succ_eq_smul`). -/
def jucysMurphy : ℕ → InfiniteTypeAHeckeAlgebra R q
  | 0 => 1
  | k + 1 => T q k * jucysMurphy k * T q k

/-- The Jucys–Murphy element of the first strand is `1`. -/
@[simp]
theorem jucysMurphy_zero : jucysMurphy q 0 = 1 := (rfl)

/-- The recursion `Jₖ₊₁ = T k * Jₖ * T k` for the Jucys–Murphy elements. -/
theorem jucysMurphy_succ (k : ℕ) :
    jucysMurphy q (k + 1) = T q k * jucysMurphy q k * T q k := (rfl)

/-- The recursion `Jₖ₊₁ = Q⁻¹ gₖ Jₖ gₖ` of the Jucys–Murphy elements in the normalization
`gₖ = q • T k`, `Q = q²`, where `(gₖ + 1) * (gₖ - Q) = 0`. -/
theorem jucysMurphy_succ_eq_smul (k : ℕ) :
    jucysMurphy q (k + 1) =
      ((↑q⁻¹ : R) ^ 2) • (((q : R) • T q k) * jucysMurphy q k * ((q : R) • T q k)) := by
  rw [jucysMurphy_succ, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, smul_smul]
  simp [sq]

/-- The Jucys–Murphy element of strand `k` lies in the stage of the first `k + 1` strands. -/
theorem jucysMurphy_mem_stage (k : ℕ) : jucysMurphy q k ∈ stage R q (k + 1) := by
  induction k with
  | zero => exact one_mem _
  | succ k ih =>
    have hT : T q k ∈ stage R q (k + 2) := T_mem_stage (by omega)
    exact mul_mem (mul_mem hT (stage_mono (by omega) ih)) hT

/-- Each Jucys–Murphy element is a unit, being a product of generators. -/
theorem isUnit_jucysMurphy (k : ℕ) : IsUnit (jucysMurphy q k) := by
  induction k with
  | zero => exact isUnit_one
  | succ k ih => exact ((isUnit_T k).mul ih).mul (isUnit_T k)

/-! ### The rescaled Jucys–Murphy elements -/

variable (q) in
/-- The rescaled (additive) Jucys–Murphy element `Lₖ` attached to strand `k` (counted from `0`),
defined by `L₀ = 0` and `Lₖ₊₁ = T k * Lₖ * T k + q⁻¹ • T k`. With `Q = q²` and `gₖ = q • T k`
this is the recursion `Lₖ₊₁ = Q⁻¹ gₖ Lₖ gₖ + Q⁻¹ gₖ`, and `Jₖ = 1 + (Q - 1) • Lₖ`
(`TauCeti.InfiniteTypeAHeckeAlgebra.jucysMurphy_eq_one_add_smul_additiveJucysMurphy`). For
`Q = 1` it is the additive recursion `Lₖ₊₁ = gₖ Lₖ gₖ + gₖ` of the Jucys–Murphy elements of the
symmetric group, where `gₖ * gₖ = 1`. -/
def additiveJucysMurphy : ℕ → InfiniteTypeAHeckeAlgebra R q
  | 0 => 0
  | k + 1 => T q k * additiveJucysMurphy k * T q k + (↑q⁻¹ : R) • T q k

/-- The rescaled Jucys–Murphy element of the first strand is `0`. -/
@[simp]
theorem additiveJucysMurphy_zero : additiveJucysMurphy q 0 = 0 := (rfl)

/-- The recursion `Lₖ₊₁ = T k * Lₖ * T k + q⁻¹ • T k` for the rescaled Jucys–Murphy elements. -/
theorem additiveJucysMurphy_succ (k : ℕ) :
    additiveJucysMurphy q (k + 1) =
      T q k * additiveJucysMurphy q k * T q k + (↑q⁻¹ : R) • T q k := (rfl)

/-- The recursion `Lₖ₊₁ = Q⁻¹ gₖ Lₖ gₖ + Q⁻¹ gₖ` of the rescaled Jucys–Murphy elements in the
normalization `gₖ = q • T k`, `Q = q²`. -/
theorem additiveJucysMurphy_succ_eq_smul (k : ℕ) :
    additiveJucysMurphy q (k + 1) =
      ((↑q⁻¹ : R) ^ 2) • (((q : R) • T q k) * additiveJucysMurphy q k * ((q : R) • T q k)) +
        ((↑q⁻¹ : R) ^ 2) • ((q : R) • T q k) := by
  rw [additiveJucysMurphy_succ, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul,
    smul_smul, smul_smul]
  simp [sq, mul_assoc]

/-- The normalized and rescaled Jucys–Murphy elements are related by `Jₖ = 1 + (Q - 1) • Lₖ`,
where `Q = q²`. -/
theorem jucysMurphy_eq_one_add_smul_additiveJucysMurphy (k : ℕ) :
    jucysMurphy q k = 1 + ((q : R) ^ 2 - 1) • additiveJucysMurphy q k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hq : ((q : R) ^ 2 - 1) * ↑q⁻¹ = q - ↑q⁻¹ := by
      rw [sub_mul, sq, mul_assoc, Units.mul_inv, mul_one, one_mul]
    rw [jucysMurphy_succ, additiveJucysMurphy_succ, ih, smul_add, smul_smul, hq, mul_add,
      add_mul, mul_one, T_mul_self, mul_smul_comm, smul_mul_assoc]
    abel

/-- When `Q - 1 = q² - 1` is a unit, the rescaled Jucys–Murphy element is
`Lₖ = (Q - 1)⁻¹ • (Jₖ - 1)`. -/
theorem additiveJucysMurphy_eq_smul_of_isUnit (h : IsUnit ((q : R) ^ 2 - 1)) (k : ℕ) :
    additiveJucysMurphy q k = (↑h.unit⁻¹ : R) • (jucysMurphy q k - 1) := by
  rw [jucysMurphy_eq_one_add_smul_additiveJucysMurphy, add_sub_cancel_left, smul_smul,
    h.val_inv_mul, one_smul]

/-- The rescaled Jucys–Murphy element of strand `k` lies in the stage of the first `k + 1`
strands. -/
theorem additiveJucysMurphy_mem_stage (k : ℕ) : additiveJucysMurphy q k ∈ stage R q (k + 1) := by
  induction k with
  | zero => exact zero_mem _
  | succ k ih =>
    have hT : T q k ∈ stage R q (k + 2) := T_mem_stage (by omega)
    exact add_mem (mul_mem (mul_mem hT (stage_mono (by omega) ih)) hT)
      (Subalgebra.smul_mem _ hT _)

/-! ### Commutation -/

/-- **The rescaled Jucys–Murphy element of strand `k` centralizes the first `k` strands**: it
commutes with every element of the stage of the first `k` strands. -/
theorem commute_additiveJucysMurphy_of_mem_stage {k : ℕ} {x : InfiniteTypeAHeckeAlgebra R q}
    (hx : x ∈ stage R q k) : Commute (additiveJucysMurphy q k) x := by
  induction k generalizing x with
  | zero => exact Commute.zero_left x
  | succ k ih =>
    suffices hle : stage R q (k + 1) ≤
        Subalgebra.centralizer R {additiveJucysMurphy q (k + 1)} from
      (Subalgebra.mem_centralizer_iff R).1 (hle hx) _ rfl
    refine stage_le_iff.2 fun i hi ↦ (Subalgebra.mem_centralizer_iff R).2 ?_
    rintro _ rfl
    refine Commute.eq (Commute.symm ?_)
    rw [additiveJucysMurphy_succ]
    rcases (show i + 1 < k ∨ i + 1 = k by omega) with hik | rfl
    · -- `T i` crosses two of the first `k` strands, so it commutes with `T k` and `Lₖ`.
      have hTk : Commute (T q i) (T q k) := commute_T (Or.inl (by omega))
      exact ((hTk.mul_right (ih (T_mem_stage hik)).symm).mul_right hTk).add_right
        (hTk.smul_right _)
    · -- `T i` with `k = i + 1`: expand `Lᵢ₊₁` once more and use the braid relations.
      have hL : Commute (T q (i + 1)) (additiveJucysMurphy q i) :=
        commute_T_of_mem_stage le_rfl (additiveJucysMurphy_mem_stage i)
      have heq : T q (i + 1) * additiveJucysMurphy q (i + 1) * T q (i + 1) +
          (↑q⁻¹ : R) • T q (i + 1) =
          T q (i + 1) * T q i * additiveJucysMurphy q i * T q i * T q (i + 1) +
            (↑q⁻¹ : R) • (T q (i + 1) * T q i * T q (i + 1) + T q (i + 1)) := by
        rw [additiveJucysMurphy_succ, mul_add, add_mul, smul_add, mul_smul_comm, smul_mul_assoc,
          add_assoc]
        simp only [mul_assoc]
      rw [heq]
      exact (commute_T_braid_conj i hL).add_right ((commute_T_braid_add i).smul_right _)

/-- **The Jucys–Murphy element of strand `k` centralizes the first `k` strands**: it commutes
with every element of the stage of the first `k` strands. -/
theorem commute_jucysMurphy_of_mem_stage {k : ℕ} {x : InfiniteTypeAHeckeAlgebra R q}
    (hx : x ∈ stage R q k) : Commute (jucysMurphy q k) x := by
  rw [jucysMurphy_eq_one_add_smul_additiveJucysMurphy]
  exact (Commute.one_left x).add_left
    ((commute_additiveJucysMurphy_of_mem_stage hx).smul_left _)

/-- The rescaled Jucys–Murphy elements commute pairwise. -/
theorem commute_additiveJucysMurphy (i j : ℕ) :
    Commute (additiveJucysMurphy q i) (additiveJucysMurphy q j) := by
  rcases lt_trichotomy i j with h | rfl | h
  · exact (commute_additiveJucysMurphy_of_mem_stage
      (stage_mono (by omega) (additiveJucysMurphy_mem_stage i))).symm
  · exact Commute.refl _
  · exact commute_additiveJucysMurphy_of_mem_stage
      (stage_mono (by omega) (additiveJucysMurphy_mem_stage j))

/-- The Jucys–Murphy elements commute pairwise. -/
theorem commute_jucysMurphy (i j : ℕ) : Commute (jucysMurphy q i) (jucysMurphy q j) := by
  simp only [jucysMurphy_eq_one_add_smul_additiveJucysMurphy]
  exact (Commute.one_left _).add_left <| (Commute.one_right _).add_right <|
    ((commute_additiveJucysMurphy i j).smul_left _).smul_right _

/-- The generator `T i` commutes with the rescaled Jucys–Murphy element of strand `k` unless it
crosses strand `k`, that is unless `i + 1 = k` or `i = k`. -/
theorem commute_T_additiveJucysMurphy {i k : ℕ} (h : i + 1 < k ∨ k < i) :
    Commute (T q i) (additiveJucysMurphy q k) := by
  rcases h with h | h
  · exact (commute_additiveJucysMurphy_of_mem_stage (T_mem_stage h)).symm
  · exact commute_T_of_mem_stage h (additiveJucysMurphy_mem_stage k)

/-- The generator `T i` commutes with the Jucys–Murphy element of strand `k` unless it crosses
strand `k`, that is unless `i + 1 = k` or `i = k`. -/
theorem commute_T_jucysMurphy {i k : ℕ} (h : i + 1 < k ∨ k < i) :
    Commute (T q i) (jucysMurphy q k) := by
  rcases h with h | h
  · exact (commute_jucysMurphy_of_mem_stage (T_mem_stage h)).symm
  · exact commute_T_of_mem_stage h (jucysMurphy_mem_stage k)

/-- The generator `T k` commutes with the sum `Lₖ + Lₖ₊₁` of the two rescaled Jucys–Murphy
elements of the strands it crosses. -/
theorem commute_T_additiveJucysMurphy_add (k : ℕ) :
    Commute (T q k) (additiveJucysMurphy q k + additiveJucysMurphy q (k + 1)) := by
  rw [commute_iff_eq, additiveJucysMurphy_succ]
  have h₁ : T q k * (T q k * additiveJucysMurphy q k * T q k) =
      (T q k * T q k) * additiveJucysMurphy q k * T q k := by
    simp only [mul_assoc]
  have h₂ : T q k * additiveJucysMurphy q k * T q k * T q k =
      T q k * additiveJucysMurphy q k * (T q k * T q k) := by
    simp only [mul_assoc]
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  rw [h₁, h₂, T_mul_self]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, mul_assoc]
  abel

/-- The generator `T k` commutes with the sum `Jₖ + Jₖ₊₁` of the two Jucys–Murphy elements of
the strands it crosses. -/
theorem commute_T_jucysMurphy_add (k : ℕ) :
    Commute (T q k) (jucysMurphy q k + jucysMurphy q (k + 1)) := by
  have heq : jucysMurphy q k + jucysMurphy q (k + 1) = 1 + 1 +
      ((q : R) ^ 2 - 1) • (additiveJucysMurphy q k + additiveJucysMurphy q (k + 1)) := by
    rw [jucysMurphy_eq_one_add_smul_additiveJucysMurphy,
      jucysMurphy_eq_one_add_smul_additiveJucysMurphy, smul_add]
    abel
  rw [heq]
  exact ((Commute.one_right _).add_right (Commute.one_right _)).add_right
    ((commute_T_additiveJucysMurphy_add k).smul_right _)

/-- The generator `T k` commutes with the product `Jₖ * Jₖ₊₁` of the two Jucys–Murphy elements
of the strands it crosses. -/
theorem commute_T_jucysMurphy_mul (k : ℕ) :
    Commute (T q k) (jucysMurphy q k * jucysMurphy q (k + 1)) := by
  rw [commute_iff_eq]
  conv_rhs => rw [(commute_jucysMurphy k (k + 1)).eq]
  rw [jucysMurphy_succ]
  simp only [mul_assoc]

/-! ### The characters -/

/-- The index character, the one-dimensional representation of the one-row partition, sends the
Jucys–Murphy element of strand `k` to `Q ^ k`, where `Q = q²`. -/
@[simp]
theorem indexCharacter_jucysMurphy (k : ℕ) :
    indexCharacter R q (jucysMurphy q k) = ((q : R) ^ 2) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [jucysMurphy_succ, map_mul, map_mul, ih, indexCharacter_T]; ring

/-- The sign character, the one-dimensional representation of the one-column partition, sends
the Jucys–Murphy element of strand `k` to `Q⁻¹ ^ k`, where `Q = q²`. -/
@[simp]
theorem signCharacter_jucysMurphy (k : ℕ) :
    signCharacter R q (jucysMurphy q k) = ((↑q⁻¹ : R) ^ 2) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [jucysMurphy_succ, map_mul, map_mul, ih, signCharacter_T]; ring

/-- The index character sends the rescaled Jucys–Murphy element of strand `k` to the quantum
integer `[k]_Q = 1 + Q + ⋯ + Q ^ (k - 1)`, where `Q = q²`. -/
@[simp]
theorem indexCharacter_additiveJucysMurphy (k : ℕ) :
    indexCharacter R q (additiveJucysMurphy q k) = ∑ i ∈ Finset.range k, ((q : R) ^ 2) ^ i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [additiveJucysMurphy_succ, map_add, map_mul, map_mul, map_smul, ih, indexCharacter_T,
      smul_eq_mul, Units.inv_mul, Finset.sum_range_succ', pow_zero,
      Finset.sum_congr rfl fun i _ ↦ pow_succ ((q : R) ^ 2) i, ← Finset.sum_mul]
    ring

/-- The sign character sends the rescaled Jucys–Murphy element of strand `k` to the quantum
integer `[-k]_Q = -(Q⁻¹ + Q⁻¹ ^ 2 + ⋯ + Q⁻¹ ^ k)`, where `Q = q²`. -/
@[simp]
theorem signCharacter_additiveJucysMurphy (k : ℕ) :
    signCharacter R q (additiveJucysMurphy q k) =
      -∑ i ∈ Finset.range k, ((↑q⁻¹ : R) ^ 2) ^ (i + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [additiveJucysMurphy_succ, map_add, map_mul, map_mul, map_smul, ih, signCharacter_T,
      smul_eq_mul, Finset.sum_range_succ',
      Finset.sum_congr rfl fun i _ ↦ pow_succ ((↑q⁻¹ : R) ^ 2) (i + 1), ← Finset.sum_mul]
    ring

end InfiniteTypeAHeckeAlgebra

end TauCeti
