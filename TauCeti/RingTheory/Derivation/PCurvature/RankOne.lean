/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.Basic
public import TauCeti.RingTheory.Derivation.PPow
import Mathlib.Data.Nat.Factorial.NatCast
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.Lie.Restricted.Jacobson
import TauCeti.Data.Nat.Factorial.NatCast
import TauCeti.RingTheory.Derivation.Basic
import TauCeti.RingTheory.Derivation.FirstOrder

/-!
# The `p`-curvature of a rank-one connection

Let `A` be a commutative `R`-algebra of prime characteristic `p` and `D` an `R`-derivation of `A`.
A rank-one connection on `A` acts on `A` through the operators `D + a`, with `a : A` the value of
its connection form on `D`. Its `p`-curvature `(∇_D)^p - ∇_{D^[p]}` is a multiplication operator:
in `Module.End R A`,

`(D + a) ^ p = D^[p] + (a ^ p + D^[p - 1] a)`,

which is Jacobson's formula for the pair `D`, `a`, whose iterated commutators are the
multiplications by the derivatives `D^[k] a` (`Derivation.add_mulLeft_pow_char`). Hence the
`p`-curvature of the connection with `∇_D = D + a` and `∇_{D^[p]} = D^[p] + b` is multiplication
by `a ^ p + D^[p - 1] a - b` (`Derivation.rankOne_pCurvature_eq`), and it vanishes when the
connection has a horizontal unit (`Derivation.pow_add_iterate_eq_of_unit`).

In one variable the converse holds without any smoothness hypothesis. If `A` is a local ring,
`D^[p] = 0` and `D x = 1` for some `x : A`, then `D + a` kills a unit of `A` if and only if
`a ^ p + D^[p - 1] a = 0` (`Derivation.exists_unit_horizontal_iff`). This applies to `κ(x)`, to
`κ⟦x⟧` and to the local rings of `κ[x]` with `D = d/dx`. For instance, on `𝔽_p[x]_(x)` the
operator `d/dx + 1` kills no unit, since `1 ^ p + 0 = 1`.

## Main statements

* `Derivation.add_mulLeft_pow_char`: `(D + a) ^ p = D^[p] + (a ^ p + D^[p - 1] a)`.
* `Derivation.rankOne_pCurvature_eq`: the `p`-curvature of a rank-one connection.
* `Derivation.pow_add_iterate_eq_of_unit`: a rank-one connection with a horizontal unit has
  vanishing `p`-curvature.
* `Derivation.exists_unit_horizontal_iff`: over a local ring with a coordinate `x`, `D x = 1`,
  and `D^[p] = 0`, the operator `D + a` has a horizontal unit if and only if
  `a ^ p + D^[p - 1] a = 0`.

## Implementation notes

The converse direction of `Derivation.exists_unit_horizontal_iff` uses Katz's projector in one
variable. Write `∇ = D + a`, so that `∇ ^ p = 0`, and let
`P m = ∑_{k < p} (-x) ^ k / k! * ∇ ^ k m`. Then `∇ (P m) = 0`, because `D (x ^ k / k!)` is
`x ^ (k - 1) / (k - 1)!` and the sum telescopes, and Taylor's formula
`∑_{j < p} x ^ j / j! * P (∇ ^ j m) = m` holds because `∑_{i + k = n} (-1) ^ k / (i! k!)` vanishes
for `0 < n < p`. For `m = 1`, one of the summands is a unit since `A` is local, so one of the
horizontal elements `P (∇ ^ j 1)` is a unit.

## References

* N. M. Katz, *Nilpotent connections and the monodromy theorem: applications of a result of
  Turrittin*, Publ. Math. IHÉS **39** (1970), 175--232, §5 and (5.1.2)--(5.1.6).
* N. Jacobson, *Abstract derivation and Lie algebras*, Trans. Amer. Math. Soc. **42** (1937),
  206--224.
-/

public section

open Finset

namespace Derivation

section Jacobson

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R A : Type*} [CommSemiring R] [CommRing A] [Algebra R A]

/-- The coefficients of Jacobson's polynomial at `D` and multiplication by `a`: the only nonzero
iterated commutator of length `k + 1` is `⁅D, … ⁅D, ⁅a, D⁆⁆ …⁆`, with `k` copies of `D` outside
`⁅a, D⁆`, namely `-D^[k + 1] a`. -/
private theorem jacobsonCoeff_toLinearMap_mulLeft (D : Derivation R A A) (a : A) (k j : ℕ) :
    TauCeti.LieAlgebra.jacobsonCoeff D.toLinearMap (LinearMap.mulLeft R a) (k + 1) j =
      if j = k then -LinearMap.mulLeft R (D^[k + 1] a) else 0 := by
  -- Multiplication operators commute.
  have lie_mulLeft_mulLeft (b c : A) : ⁅LinearMap.mulLeft R b, LinearMap.mulLeft R c⁆ = 0 := by
    ext
    simp [Ring.lie_def, mul_left_comm]
  induction k generalizing j with
  | zero =>
    rcases j with _ | _ | j
    · simp [← lie_skew (LinearMap.mulLeft R a)]
    · simp
    · simp
  | succ k ih =>
    rcases j with _ | j
    · rw [TauCeti.LieAlgebra.jacobsonCoeff_succ_zero, ih]
      simp only [(Nat.succ_ne_zero k).symm, ↓reduceIte]
      split_ifs
      · rw [lie_neg, lie_mulLeft_mulLeft, neg_zero]
      · rw [lie_zero]
    · rw [TauCeti.LieAlgebra.jacobsonCoeff_succ_succ, ih, ih]
      by_cases hj : j = k
      · subst hj
        simp [Function.iterate_succ_apply']
      · split_ifs <;> simp_all

variable (p : ℕ) [Fact p.Prime] [CharP A p]

/-- **Jacobson's formula in rank one.** In characteristic `p`, for a derivation `D` of `A` and
`a : A`, `(D + a) ^ p = D^[p] + (a ^ p + D^[p - 1] a)` in `Module.End R A`, where `a` stands for
multiplication by `a`. -/
theorem add_mulLeft_pow_char (D : Derivation R A A) (a : A) :
    (D.toLinearMap + LinearMap.mulLeft R a) ^ p =
      (D.pPow p).toLinearMap + LinearMap.mulLeft R (a ^ p + D^[p - 1] a) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by have := (Fact.out : p.Prime).two_le; omega⟩
  have : CharP (Module.End R A) (q + 2) :=
    (expChar_prime_iff (R := Module.End R A) Fact.out).mp inferInstance
  -- The weight of the only nonzero word is the representative `q + 1` of `(p - 1)⁻¹ = -1`.
  have hinv : (((q : ZMod (q + 2)) + 1)⁻¹).val = q + 1 := by
    have : ((q : ZMod (q + 2)) + 1) = -1 := by
      rw [eq_neg_iff_add_eq_zero, add_assoc, one_add_one_eq_two]
      exact_mod_cast ZMod.natCast_self (q + 2)
    rw [this, ZMod.inv_neg_one]
    exact ZMod.val_neg_one (q + 1)
  have hq : (q : A) + 2 = 0 := by exact_mod_cast CharP.cast_eq_zero A (q + 2)
  have hq1 : q + 2 - 1 = q + 1 := by omega
  -- Jacobson's sum collapses to its only nonzero term, indexed by `j = q`.
  have hcollapse : TauCeti.LieAlgebra.jacobson (q + 2) D.toLinearMap (LinearMap.mulLeft R a) =
      (q + 1) • -LinearMap.mulLeft R (D^[q + 1] a) := by
    rw [TauCeti.LieAlgebra.jacobson_def, hq1,
      sum_eq_single_of_mem q (by simp) fun j _ hj ↦ by
        simp [jacobsonCoeff_toLinearMap_mulLeft, hj],
      jacobsonCoeff_toLinearMap_mulLeft, hinv]
    simp only [↓reduceIte]
  rw [TauCeti.LieAlgebra.add_pow_eq_jacobson, LinearMap.pow_mulLeft, ← toLinearMap_pPow,
    hcollapse, add_assoc, hq1]
  congr 1
  ext b
  simp only [LinearMap.add_apply, LinearMap.mulLeft_apply, LinearMap.smul_apply,
    LinearMap.neg_apply]
  rw [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  linear_combination (-(D^[q + 1] a * b)) * hq

/-- **The `p`-curvature of a rank-one connection.** If a connection on `A` acts as `D + a` along
`D` and as `D^[p] + b` along `D^[p]`, its `p`-curvature `(D + a) ^ p - (D^[p] + b)` at `D` is
multiplication by `a ^ p + D^[p - 1] a - b`. -/
theorem rankOne_pCurvature_eq (D : Derivation R A A) (a b : A) :
    (D.toLinearMap + LinearMap.mulLeft R a) ^ p -
        ((D.pPow p).toLinearMap + LinearMap.mulLeft R b) =
      LinearMap.mulLeft R (a ^ p + D^[p - 1] a - b) := by
  rw [add_mulLeft_pow_char]
  ext c
  simp
  ring

/-- **A horizontal unit forces zero `p`-curvature.** If a unit `u` is killed by both `D + a` and
`D^[p] + b`, the rank-one connection acting by these operators has vanishing `p`-curvature:
`a ^ p + D^[p - 1] a = b`. -/
theorem pow_add_iterate_eq_of_unit (D : Derivation R A A) {a b : A} (u : Aˣ)
    (ha : D u + a * u = 0) (hb : D.pPow p u + b * u = 0) : a ^ p + D^[p - 1] a = b := by
  have key : (D.toLinearMap + LinearMap.mulLeft R a) ^ p =
      (D.pPow p).toLinearMap + LinearMap.mulLeft R b := by
    have ha' : a = -(↑u⁻¹ * D u) := by linear_combination (↑u⁻¹ : A) * ha - a * u.inv_mul
    have hb' : b = -(↑u⁻¹ * D.pPow p u) := by
      linear_combination (↑u⁻¹ : A) * hb - b * u.inv_mul
    convert sub_mulLeft_inv_mul_pow_expChar (R := R) p D u using 2 <;>
      ext c <;> simp [ha', hb', sub_eq_add_neg, mul_assoc]
  rw [add_mulLeft_pow_char, add_right_inj] at key
  simpa using congr($key 1)

end Jacobson

/-! ### Katz's projector in one variable -/

section Projector

open scoped Nat

variable {R A : Type*} [CommSemiring R] [CommRing A] [Algebra R A]

/-- Katz's projector truncated at `n`: with `∇ = D + a`, the element
`∑_{k < n} (-x) ^ k / k! * ∇ ^ k m`. For `n = p` it is the projector `P` of the implementation
notes. -/
private noncomputable def projector (D : Derivation R A A) (x a : A) (n : ℕ) (m : A) : A :=
  ∑ k ∈ range n, (-1) ^ k * (Ring.inverse (k ! : A) * x ^ k) *
    ((D.toLinearMap + LinearMap.mulLeft R a) ^ k) m

/-- The partial sums of Katz's projector: with `∇ = D + a` and `D x = 1`, the element
`∑_{k ≤ n} (-1) ^ k x ^ k / k! * ∇ ^ k m` is killed by `∇` up to the boundary term
`(-1) ^ n x ^ n / n! * ∇ ^ (n + 1) m`. -/
private theorem add_mulLeft_apply_projector (D : Derivation R A A) {x : A} (hx : D x = 1)
    (a m : A) {n : ℕ} (hn : IsUnit (n ! : A)) :
    (D.toLinearMap + LinearMap.mulLeft R a) (projector D x a (n + 1) m) =
      (-1) ^ n * (Ring.inverse (n ! : A) * x ^ n) *
        ((D.toLinearMap + LinearMap.mulLeft R a) ^ (n + 1)) m := by
  unfold projector
  set N := D.toLinearMap + LinearMap.mulLeft R a
  -- The Leibniz rule for `N`: `N (f * y) = D f * y + f * N y`.
  have hN (f y : A) : N (f * y) = D f * y + f * N y := by
    simp only [N, LinearMap.add_apply, coeFn_coe, leibniz, smul_eq_mul, LinearMap.mulLeft_apply]
    ring
  induction n with
  | zero => simp
  | succ n ih =>
    have hn' : IsUnit (n ! : A) := hn.natCast_factorial_of_le n.le_succ
    have hd : D ((-1) ^ (n + 1) * (Ring.inverse ((n + 1)! : A) * x ^ (n + 1))) =
        (-1) ^ (n + 1) * (Ring.inverse (n ! : A) * x ^ n) := by
      -- `leibniz_ringInverse_factorial_mul_pow_succ` is stated over a commutative ring of
      -- scalars, so apply it to `D` viewed as a `ℤ`-derivation.
      have h := (D.restrictScalars ℤ).leibniz_ringInverse_factorial_mul_pow_succ
        (by rwa [restrictScalars_apply]) hn
      rw [restrictScalars_apply] at h
      rw [leibniz, h]
      simp [leibniz_pow]
    have hsucc (k : ℕ) : (N ^ (k + 1)) m = N ((N ^ k) m) := by
      rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply]
    rw [sum_range_succ, map_add, ih hn', hN, hd, ← hsucc]
    ring

/-- **Taylor's formula.** If `D x = 1` and `∇ = D + a` satisfies `∇ ^ p = 0` with `(p - 1)!` a
unit, every `m` is recovered from the values of Katz's projector
`P m = ∑_{k < p} (-x) ^ k / k! * ∇ ^ k m` as `m = ∑_{j < p} x ^ j / j! * P (∇ ^ j m)`. -/
private theorem sum_projector_eq (D : Derivation R A A) (x a m : A) {p : ℕ}
    (hp : IsUnit ((p - 1)! : A))
    (hN : (D.toLinearMap + LinearMap.mulLeft R a) ^ p = 0) :
    ∑ j ∈ range p, Ring.inverse (j ! : A) * x ^ j *
        projector D x a p (((D.toLinearMap + LinearMap.mulLeft R a) ^ j) m) = m := by
  set N := D.toLinearMap + LinearMap.mulLeft R a
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · -- For `p = 0`, `∇ ^ 0 = 1 = 0`, so `m = 0`.
    simpa [eq_comm] using congr($hN m)
  have hpow (k j : ℕ) : (N ^ k) ((N ^ j) m) = (N ^ (j + k)) m := by
    rw [add_comm, pow_add, Module.End.mul_eq_comp, LinearMap.comp_apply]
  have hzero {n : ℕ} (hn : p ≤ n) : (N ^ n) m = 0 := by
    rw [← Nat.add_sub_cancel' hn, pow_add, hN, zero_mul, LinearMap.zero_apply]
  -- The summand indexed by `(j, k)` only depends on `n = j + k`, and vanishes once `p ≤ n`.
  let F (j k : ℕ) : A :=
    (-1) ^ k * (Ring.inverse (j ! : A) * Ring.inverse (k ! : A)) * (x ^ (j + k) * (N ^ (j + k)) m)
  have hF : ∀ j ∈ range p, Ring.inverse (j ! : A) * x ^ j * projector D x a p ((N ^ j) m) =
      ∑ k ∈ range (p - j), F j k := by
    intro j _
    rw [projector, mul_sum, ← sum_subset (range_subset_range.mpr (Nat.sub_le p j))]
    · refine sum_congr rfl fun k _ ↦ ?_
      simp only [F]
      rw [hpow, pow_add x]
      ring
    · intro k _ hk
      simp only [mem_range, not_lt] at hk
      rw [hpow, hzero (by omega)]
      simp
  rw [sum_congr rfl hF, ← sum_range_diag_flip]
  -- Grouping by `n = j + k`, the coefficient of `x ^ n * ∇ ^ n m` is `1` for `n = 0`, else `0`.
  have hdiag : ∀ n ∈ range p, ∑ i ∈ range (n + 1), F i (n - i) =
      if n = 0 then m else 0 := by
    intro n hn
    have hcoef := TauCeti.sum_range_neg_one_pow_mul_ringInverse_factorial
      (hp.natCast_factorial_of_lt (mem_range.mp hn))
    calc ∑ i ∈ range (n + 1), F i (n - i)
        = (∑ i ∈ range (n + 1), (-1) ^ (n - i) *
            (Ring.inverse (i ! : A) * Ring.inverse ((n - i)! : A))) * (x ^ n * (N ^ n) m) := by
          rw [sum_mul]
          refine sum_congr rfl fun i hi ↦ ?_
          simp only [F]
          rw [Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (mem_range.mp hi))]
      _ = if n = 0 then m else 0 := by
          rw [hcoef]
          split_ifs with h
          · simp [h]
          · simp
  rw [sum_congr rfl hdiag, sum_ite_eq']
  simp [hp0]

/-- **Horizontal units in one variable.** Let `A` be a local ring of characteristic `p`, `D` a
derivation of `A` with `D^[p] = 0`, and `x : A` with `D x = 1`. Then `D + a` kills a unit of `A`
if and only if `a ^ p + D^[p - 1] a = 0`, that is, if and only if the rank-one connection acting
as `D + a` along `D` and as `D^[p]` along `D^[p] = 0` has vanishing `p`-curvature. -/
theorem exists_unit_horizontal_iff (p : ℕ) [Fact p.Prime] [CharP A p] [IsLocalRing A]
    (D : Derivation R A A) (hD : D.pPow p = 0) {x : A} (hx : D x = 1) (a : A) :
    (∃ u : Aˣ, D u + a * u = 0) ↔ a ^ p + D^[p - 1] a = 0 := by
  constructor
  · rintro ⟨u, hu⟩
    exact pow_add_iterate_eq_of_unit p D u hu (by simp [hD])
  intro h
  set N := D.toLinearMap + LinearMap.mulLeft R a
  have hN : N ^ p = 0 := by
    rw [add_mulLeft_pow_char, h, hD]
    ext
    simp
  have hp := (Fact.out : p.Prime)
  have hfac : IsUnit ((p - 1)! : A) :=
    (IsUnit.natCast_factorial_iff_of_charP p).mpr (Nat.sub_lt hp.pos one_pos)
  -- By Taylor's formula at `m = 1`, a sum of `p` multiples of horizontal elements is `1`; since
  -- `A` is local, one of them is a unit.
  obtain ⟨j, -, hj⟩ : ∃ j ∈ range p,
      IsUnit (Ring.inverse (j ! : A) * x ^ j * projector D x a p ((N ^ j) 1)) := by
    by_contra! H
    have hmem := Ideal.sum_mem (IsLocalRing.maximalIdeal A) fun j hj ↦
      (IsLocalRing.mem_maximalIdeal _).mpr (H j hj)
    rw [sum_projector_eq D x a 1 hfac hN] at hmem
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem isUnit_one
  refine ⟨(isUnit_of_mul_isUnit_right hj).unit, ?_⟩
  have hproj := add_mulLeft_apply_projector D hx a ((N ^ j) 1) hfac
  rw [Nat.sub_add_cancel hp.pos, hN, LinearMap.zero_apply, mul_zero] at hproj
  rw [IsUnit.unit_spec]
  simpa only [N, LinearMap.add_apply, coeFn_coe, LinearMap.mulLeft_apply] using hproj

end Projector

end Derivation
