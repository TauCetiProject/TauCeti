/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Ring.Ultra
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Defs
import TauCeti.Algebra.Group.ForwardDiff
import TauCeti.Algebra.Polynomial.Eval.Nonarchimedean
import TauCeti.Analysis.Normed.Ring.Basic

/-!
# The closed unit ball and products of elements close to one in ultrametric normed rings

An ultrametric seminormed ring is a nonarchimedean topological ring: its open balls about zero
are open additive subgroups. In an ultrametric seminormed ring with `‖1‖ = 1`, the closed unit
ball is an open subring. In an ultrametric seminormed ring, the product of two elements each
within `B` of `1` (`0 ≤ B ≤ 1`) or strictly within `ε` of `1` (`0 < ε ≤ 1`) satisfies the same
bound, and over a commutative ultrametric seminormed ring the same bound holds for finite
`Finset.prod` products (see `TauCeti.Analysis.Normed.Ring.InfiniteProd.Ultra` for infinite
products). A series `∑_{n ≥ 1} f(qⁿ w)` of terms bounded by their arguments is bounded by its
first argument `q w`, and it depends on `w` in a `‖q‖`-Lipschitz way when its terms are
`1`-Lipschitz. The rational functions `t / (1 - t)²`, `t / (1 - t)³` and `t² / (1 - t)³` are
Lipschitz on the open unit ball of an ultrametric field.

Integer casts have norm at most `‖1‖`, without requiring the seminorm to be normalized. For a
power-multiplicative seminorm, every element integral over `ℤ` has norm at most one. When
`‖1‖ = 1`, arbitrarily large natural numbers have norm exactly one, and if `‖n‖ < 1` then
multiplying by a natural number coprime to `n` does not change norms; in particular every natural
number coprime to `n` has norm one. For a prime `p` with `‖p‖ < 1`, the binomial coefficient
`(p ^ (k + 1)).choose (p ^ k)`, exactly divisible by `p`, thus has the norm of `p`. Since the
forward differences of a monomial are divisible by `k!`, their norms carry the factor `‖k!‖`.

## Main results

* `IsUltrametricDist.norm_le_one_of_isIntegral`: algebraic integers lie in the closed unit ball of
  an ultrametric seminormed ring whose seminorm is power-multiplicative.
* `IsUltrametricDist.exists_lt_norm_natCast_eq_one`: arbitrarily large natural numbers have norm
  one in an ultrametric seminormed ring with `‖1‖ = 1`.
* `IsUltrametricDist.norm_mul_natCast_eq_of_coprime`: if `‖n‖ < 1` with `‖1‖ = 1`, then
  `‖x * m‖ = ‖x‖` for every `x` and every natural number `m` coprime to `n`.
* `IsUltrametricDist.norm_natCast_eq_one_of_coprime`: if `‖n‖ < 1` with `‖1‖ = 1`, every natural
  number coprime to `n` has norm one.
* `IsUltrametricDist.norm_choose_prime_pow_succ`: if a prime `p` has `‖p‖ < 1`, the binomial
  coefficient `(p ^ (k + 1)).choose (p ^ k)` has the norm of `p`.
* `IsUltrametricDist.nonarchimedeanRing`: an ultrametric seminormed ring is a nonarchimedean
  ring.
* `Subring.unitClosedBall`: the closed unit ball of an ultrametric seminormed ring with
  `‖1‖ = 1`, an open subring.
* `TauCeti.norm_one_sub_of_norm_lt_one`: subtracting an element of norm less than one from one
  leaves the norm equal to one; `TauCeti.norm_eq_one_of_norm_one_sub_lt_one`: an element within
  less than one of one has norm one; `TauCeti.norm_div_one_sub_pow`: dividing by a power of such
  a `1 - w` does not change norms.
* `TauCeti.norm_div_one_sub_cube_sub_div_one_sub_cube_le` and
  `TauCeti.norm_sq_div_one_sub_cube_sub_sq_div_one_sub_cube_le_max_mul`: on the open unit ball,
  `t ↦ t / (1 - t)³` is `1`-Lipschitz and `t ↦ t² / (1 - t)³` is Lipschitz with constant the
  larger of the two norms.
* `TauCeti.norm_tsum_le_norm_mul`: a one-sided series `∑_{n ≥ 1} f(qⁿ w)` whose terms are bounded
  by their arguments has norm at most `‖q w‖`; `TauCeti.norm_tsum_sub_tsum_le_norm_mul`: if the
  terms are `1`-Lipschitz, two such series differ by at most `‖q (w - w')‖`;
  `TauCeti.norm_tsum_sub_tsum_add_tsum_sub_tsum_le`: a series at `u` and a series at `u⁻¹` of
  `1`-Lipschitz terms together depend on `u` in a `‖q‖`-Lipschitz way on the unit circle.
* `TauCeti.norm_div_one_sub_sq_sub_div_one_sub_sq_le`: the map `t ↦ t / (1 - t)²` is
  `1`-Lipschitz on the open unit ball of an ultrametric field;
  `TauCeti.norm_sub_le_of_eq_mul_div` is the estimate behind it.
* `TauCeti.norm_one_sub_cube_div_sub_one_sub_cube_div_le`: the map `v ↦ (1 - v)³ / v` is
  `1`-Lipschitz on the unit circle of an ultrametric field.
* `TauCeti.one_le_norm_one_sub_of_norm_ne_one`: subtracting an element whose norm is not one
  from one gives norm at least one.
* `TauCeti.norm_mul_sub_one_le` and `TauCeti.norm_mul_sub_one_lt`: binary multiplication bounds
  near `1` (closed for `0 ≤ B ≤ 1`, strict for `0 < ε ≤ 1`) over any ultrametric seminormed ring
  (without commutativity).
* `TauCeti.norm_prod_sub_one_le` and `TauCeti.norm_prod_sub_one_lt`: over a commutative
  ultrametric seminormed ring, unordered `Finset.prod` products of elements within `B` of `1`
  (`0 ≤ B ≤ 1`) or strictly within `ε` of `1` (`0 < ε ≤ 1`) satisfy the same bound.
* `TauCeti.norm_add_add_mul_le`: the group law `a + b + a b` keeps the closed ball of radius
  `ε ≤ 1` about `0`.
* `TauCeti.norm_inv_sub_one_eq`: inversion preserves distance less than one from `1`.
* `TauCeti.norm_pow_sub_one_le_norm_sub_one`: a power of an element `x` of norm at most one is
  no farther from `1` than `x`.
* `TauCeti.norm_prod_sub_prod_le`: a uniform perturbation bound for finite products.
* `TauCeti.norm_prod_pow_sub_prod_pow_le`: monomials in two close families lying in a
  norm-bounded subring differ by a bound independent of their degree.
* `TauCeti.norm_fwdDiff_iter_pow_mul_pow_le`: for `‖x‖, ‖h‖ ≤ c`, the `k`-th forward difference
  of `y ↦ yᵐ` with step `h` at `x` satisfies `‖Δₕᵏ (y ↦ yᵐ)(x)‖ cᵏ ≤ ‖k!‖ ‖h‖ᵏ cᵐ`.
-/

public section

/-- Integer casts in an ultrametric seminormed ring have norm at most the norm of one. -/
theorem IsUltrametricDist.norm_intCast_le_norm_one {R : Type*} [SeminormedRing R]
    [IsUltrametricDist R] (z : ℤ) : ‖(z : R)‖ ≤ ‖(1 : R)‖ := by
  simpa using IsUltrametricDist.norm_zsmul_le (1 : R) z

/-- In a seminormed ring whose seminorm is power-multiplicative and ultrametric, every element
integral over `ℤ` has norm at most `1`. This is the norm analogue of
`IsNonarchimedean.apply_le_one_of_isIntegral_int`, and like it a case of
`IsNonarchimedean.apply_le_one_of_isIntegral_of_isPowMul`. -/
theorem IsUltrametricDist.norm_le_one_of_isIntegral {R : Type*} [SeminormedRing R]
    [IsUltrametricDist R] (hR : IsPowMul (‖·‖ : R → ℝ)) {x : R} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 :=
  isNonarchimedean_norm.apply_le_one_of_isIntegral_of_isPowMul norm_nonneg norm_mul_le hR
    (fun z ↦ eq_intCast (algebraMap ℤ R) z ▸ (norm_intCast_le_norm_one z).trans hR.map_one_le_one)
    hx

/-- In an ultrametric seminormed ring with `‖1‖ = 1`, arbitrarily large natural numbers have norm
one: of two consecutive natural numbers, one has norm one, since their difference does. -/
theorem IsUltrametricDist.exists_lt_norm_natCast_eq_one (R : Type*) [SeminormedRing R]
    [NormOneClass R] [IsUltrametricDist R] (N : ℕ) : ∃ m, N < m ∧ ‖(m : R)‖ = 1 := by
  by_contra! h
  have h1 := (IsUltrametricDist.norm_natCast_le_one R (N + 1)).lt_of_ne (h _ (by omega))
  have h2 := (IsUltrametricDist.norm_natCast_le_one R (N + 2)).lt_of_ne (h _ (by omega))
  have h3 := IsUltrametricDist.norm_add_le_max ((N + 2 : ℕ) : R) (-((N + 1 : ℕ) : R))
  have hsum : ((N + 2 : ℕ) : R) + -((N + 1 : ℕ) : R) = 1 := by
    push_cast
    abel_nf
    norm_num
  rw [norm_neg, hsum, norm_one] at h3
  exact (h3.trans_lt (max_lt h2 h1)).false

/-- In an ultrametric seminormed ring with `‖1‖ = 1` in which a natural number `n` has norm less
than one, multiplying any element on the right by a natural number coprime to `n` does not change
its norm. -/
theorem IsUltrametricDist.norm_mul_natCast_eq_of_coprime {R : Type*} [SeminormedRing R]
    [NormOneClass R] [IsUltrametricDist R] {n m : ℕ} (hnR : ‖(n : R)‖ < 1) (hnm : n.Coprime m)
    (x : R) : ‖x * (m : R)‖ = ‖x‖ := by
  refine ((norm_mul_le _ _).trans ?_).antisymm (not_lt.mp fun hlt ↦ ?_)
  · exact mul_le_of_le_one_right (norm_nonneg _) (norm_natCast_le_one R m)
  -- Bézout: `n * a + m * b = 1`, hence `x = x * (n * a) + (x * m) * b`.
  have hsum : x = x * (n * (n.gcdA m : R)) + x * m * (n.gcdB m : R) := by
    have h : (n : ℤ) * n.gcdA m + m * n.gcdB m = 1 := by
      rw [← Nat.gcd_eq_gcd_ab, hnm.gcd_eq_one, Nat.cast_one]
    have h' : (n : R) * (n.gcdA m : R) + (m : R) * (n.gcdB m : R) = 1 := by
      exact_mod_cast congrArg (Int.cast (R := R)) h
    calc x = x * (n * (n.gcdA m : R) + m * (n.gcdB m : R)) := by rw [h', mul_one]
      _ = _ := by rw [mul_add, mul_assoc]
  have h1 : ‖x * (n * (n.gcdA m : R))‖ < ‖x‖ := by
    have hx0 : 0 < ‖x‖ := (norm_nonneg _).trans_lt hlt
    calc ‖x * (n * (n.gcdA m : R))‖ ≤ ‖x‖ * (‖(n : R)‖ * 1) := by
          refine (norm_mul_le _ _).trans ?_
          gcongr
          exact (norm_mul_le _ _).trans (by gcongr; exact norm_intCast_le_one R _)
      _ < ‖x‖ * 1 := by gcongr; rwa [mul_one]
      _ = ‖x‖ := mul_one _
  have h2 : ‖x * m * (n.gcdB m : R)‖ < ‖x‖ := by
    calc ‖x * m * (n.gcdB m : R)‖ ≤ ‖x * m‖ * 1 :=
          (norm_mul_le _ _).trans (by gcongr; exact norm_intCast_le_one R _)
      _ < ‖x‖ := by rwa [mul_one]
  have h := IsUltrametricDist.norm_add_le_max (x * (n * (n.gcdA m : R))) (x * m * (n.gcdB m : R))
  rw [← hsum] at h
  exact (h.trans_lt (max_lt h1 h2)).false

/-- In an ultrametric seminormed ring with `‖1‖ = 1` in which a natural number `n` has norm less
than one, every natural number coprime to `n` has norm one. -/
theorem IsUltrametricDist.norm_natCast_eq_one_of_coprime {R : Type*} [SeminormedRing R]
    [NormOneClass R] [IsUltrametricDist R] {n m : ℕ} (hnR : ‖(n : R)‖ < 1) (hnm : n.Coprime m) :
    ‖(m : R)‖ = 1 := by
  simpa using norm_mul_natCast_eq_of_coprime hnR hnm (1 : R)

/-- In an ultrametric seminormed ring with `‖1‖ = 1` in which a prime `p` has norm less than one,
the binomial coefficient `(p ^ (k + 1)).choose (p ^ k)`, which is exactly divisible by `p`, has the
norm of `p`. -/
theorem IsUltrametricDist.norm_choose_prime_pow_succ {R : Type*} [SeminormedRing R]
    [NormOneClass R] [IsUltrametricDist R] {p : ℕ} (hp : p.Prime)
    (hpR : ‖(p : R)‖ < 1) (k : ℕ) : ‖((p ^ (k + 1)).choose (p ^ k) : R)‖ = ‖(p : R)‖ := by
  have hc : (p ^ (k + 1)).choose (p ^ k) ≠ 0 :=
    (Nat.choose_pos (Nat.pow_le_pow_right hp.pos (Nat.le_succ k))).ne'
  have hfact : ((p ^ (k + 1)).choose (p ^ k)).factorization p = 1 := by
    rw [Nat.factorization_choose_prime_pow hp (Nat.pow_le_pow_right hp.pos (Nat.le_succ k))
      (pow_ne_zero _ hp.ne_zero), Nat.factorization_pow_self hp]
    omega
  have h := Nat.ordProj_mul_ordCompl_eq_self ((p ^ (k + 1)).choose (p ^ k)) p
  have hu := Nat.not_dvd_ordCompl hp hc
  rw [hfact, pow_one] at h hu
  rw [← h, Nat.cast_mul, norm_mul_natCast_eq_of_coprime hpR (hp.coprime_iff_not_dvd.mpr hu)]

/-- **An ultrametric seminormed ring is a nonarchimedean ring.** This is the ring form of
Mathlib's `IsUltrametricDist.nonarchimedeanAddGroup`: every neighbourhood of zero contains an open
additive subgroup, namely a small open ball. -/
instance IsUltrametricDist.nonarchimedeanRing {R : Type*} [SeminormedRing R]
    [IsUltrametricDist R] : NonarchimedeanRing R where
  is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean

section UnitClosedBall

variable (R : Type*) [SeminormedRing R] [IsUltrametricDist R] [NormOneClass R]

/-- **The closed unit ball of an ultrametric seminormed ring with `‖1‖ = 1` is a subring**: it is
the submonoid `Submonoid.unitClosedBall` and the open additive subgroup
`IsUltrametricDist.closedBall_openAddSubgroup`. -/
def Subring.unitClosedBall : Subring R :=
  { Submonoid.unitClosedBall R,
    (IsUltrametricDist.closedBall_openAddSubgroup R one_pos : AddSubgroup R) with }

variable {R} in
/-- An element lies in the closed unit ball exactly when its norm is at most one. -/
@[simp]
theorem Subring.mem_unitClosedBall {x : R} : x ∈ Subring.unitClosedBall R ↔ ‖x‖ ≤ 1 :=
  Submonoid.mem_unitClosedBall R

/-- The carrier of `Subring.unitClosedBall R` is `Metric.closedBall 0 1`. -/
@[simp]
theorem Subring.coe_unitClosedBall :
    (Subring.unitClosedBall R : Set R) = Metric.closedBall 0 1 := by
  ext
  simp

/-- The closed unit ball of an ultrametric seminormed ring is open. -/
theorem Subring.isOpen_unitClosedBall : IsOpen (Subring.unitClosedBall R : Set R) :=
  (IsUltrametricDist.closedBall_openAddSubgroup R one_pos).isOpen'

end UnitClosedBall

namespace TauCeti

/-- An element strictly smaller than one does not change the norm of one when subtracted. -/
@[simp]
theorem norm_one_sub_of_norm_lt_one {R : Type*} [SeminormedRing R] [NormOneClass R]
    [IsUltrametricDist R] {x : R} (hx : ‖x‖ < 1) : ‖1 - x‖ = 1 := by
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm]
  · simp [hx.le]
  · exact ne_of_gt (by simpa using hx)

/-- In an ultrametric seminormed ring, multiplication by a perturbation `1 + a` of one with
`‖a‖ < 1` preserves norms. -/
@[simp]
theorem norm_one_add_mul_of_norm_lt_one {A : Type*} [SeminormedRing A] [IsUltrametricDist A]
    {a : A} (ha : ‖a‖ < 1) (x : A) : ‖(1 + a) * x‖ = ‖x‖ := by
  rw [add_mul, one_mul]
  have hax : ‖a * x‖ ≤ ‖a‖ * ‖x‖ := norm_mul_le _ _
  rcases (norm_nonneg x).eq_or_lt with hx | hx
  · have h0 : ‖a * x‖ = 0 := le_antisymm (by simpa [← hx] using hax) (norm_nonneg _)
    rw [← hx]
    refine le_antisymm ?_ (norm_nonneg _)
    simpa [← hx, h0] using IsUltrametricDist.norm_add_le_max x (a * x)
  · have hlt : ‖a * x‖ < ‖x‖ := hax.trans_lt (by simpa using mul_lt_mul_of_pos_right ha hx)
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le]

/-- An element at distance less than one from one has norm one. -/
theorem norm_eq_one_of_norm_one_sub_lt_one {R : Type*} [SeminormedRing R] [NormOneClass R]
    [IsUltrametricDist R] {x : R} (hx : ‖1 - x‖ < 1) : ‖x‖ = 1 := by
  simpa using norm_one_sub_of_norm_lt_one hx

/-- Subtracting an element whose norm is not one from one gives norm at least one. -/
theorem one_le_norm_one_sub_of_norm_ne_one {R : Type*} [SeminormedRing R] [NormOneClass R]
    [IsUltrametricDist R] {x : R} (hx : ‖x‖ ≠ 1) : 1 ≤ ‖1 - x‖ := by
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by simpa using hx.symm)]
  simp

/-- Dividing by a power of `1 - w` with `‖w‖ < 1` does not change norms in an ultrametric normed
division ring. -/
theorem norm_div_one_sub_pow {K : Type*} [NormedDivisionRing K] [IsUltrametricDist K] (z : K)
    {w : K} (hw : ‖w‖ < 1) (k : ℕ) : ‖z / (1 - w) ^ k‖ = ‖z‖ := by
  rw [norm_div, norm_pow, norm_one_sub_of_norm_lt_one hw, one_pow, div_one]

/-- The map `t ↦ t / (1 - t)³` is `1`-Lipschitz on the open unit ball of an ultrametric field. -/
theorem norm_div_one_sub_cube_sub_div_one_sub_cube_le {K : Type*} [NormedField K]
    [IsUltrametricDist K] {t t' : K} (ht : ‖t‖ < 1) (ht' : ‖t'‖ < 1) :
    ‖t / (1 - t) ^ 3 - t' / (1 - t') ^ 3‖ ≤ ‖t - t'‖ := by
  have h₁ : 1 - t ≠ 0 := norm_ne_zero_iff.mp (by simp [ht])
  have h₂ : 1 - t' ≠ 0 := norm_ne_zero_iff.mp (by simp [ht'])
  have e : t / (1 - t) ^ 3 - t' / (1 - t') ^ 3 =
      (t - t') * (1 - t * t' - t * t' - t * t' + t * t' * (t + t')) /
        ((1 - t) ^ 3 * (1 - t') ^ 3) := by
    field_simp
    ring
  have hP : 1 - t * t' - t * t' - t * t' + t * t' * (t + t') ∈ Subring.unitClosedBall K := by
    have h₃ : t ∈ Subring.unitClosedBall K := Subring.mem_unitClosedBall.mpr ht.le
    have h₄ : t' ∈ Subring.unitClosedBall K := Subring.mem_unitClosedBall.mpr ht'.le
    apply_rules [add_mem, sub_mem, mul_mem, one_mem]
  rw [e, norm_div, norm_mul, norm_mul, norm_pow, norm_pow, norm_one_sub_of_norm_lt_one ht,
    norm_one_sub_of_norm_lt_one ht', one_pow, mul_one, div_one]
  exact mul_le_of_le_one_right (norm_nonneg _) (Subring.mem_unitClosedBall.mp hP)

/-- On the open unit ball of an ultrametric field, the map `t ↦ t² / (1 - t)³` is Lipschitz with
constant `max ‖t‖ ‖t'‖` between `t` and `t'`, so it contracts near zero. -/
theorem norm_sq_div_one_sub_cube_sub_sq_div_one_sub_cube_le_max_mul {K : Type*} [NormedField K]
    [IsUltrametricDist K] {t t' : K} (ht : ‖t‖ < 1) (ht' : ‖t'‖ < 1) :
    ‖t ^ 2 / (1 - t) ^ 3 - t' ^ 2 / (1 - t') ^ 3‖ ≤ max ‖t‖ ‖t'‖ * ‖t - t'‖ := by
  have h₁ : 1 - t ≠ 0 := norm_ne_zero_iff.mp (by simp [ht])
  have h₂ : 1 - t' ≠ 0 := norm_ne_zero_iff.mp (by simp [ht'])
  set A := 1 - t' - t' - t' + t * t' ^ 2
  have e : t ^ 2 / (1 - t) ^ 3 - t' ^ 2 / (1 - t') ^ 3 =
      (t - t') * (t * A + t') / ((1 - t) ^ 3 * (1 - t') ^ 3) := by
    field_simp
    ring
  have hA : ‖A‖ ≤ 1 := by
    have h₃ : t ∈ Subring.unitClosedBall K := Subring.mem_unitClosedBall.mpr ht.le
    have h₄ : t' ∈ Subring.unitClosedBall K := Subring.mem_unitClosedBall.mpr ht'.le
    refine Subring.mem_unitClosedBall.mp ?_
    apply_rules [add_mem, sub_mem, mul_mem, pow_mem, one_mem]
  have hQ : ‖t * A + t'‖ ≤ max ‖t‖ ‖t'‖ := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ le_rfl)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hA
  rw [e, norm_div, norm_mul, norm_mul, norm_pow, norm_pow, norm_one_sub_of_norm_lt_one ht,
    norm_one_sub_of_norm_lt_one ht', one_pow, mul_one, div_one, mul_comm]
  exact mul_le_mul_of_nonneg_right hQ (norm_nonneg _)

/-- A one-sided series `∑_{n ≥ 1} f(qⁿ w)` with values in an ultrametric group, whose terms are
bounded by their arguments, has norm at most `‖q w‖` when `‖q‖ ≤ 1` and `‖q w‖ < 1`. -/
theorem norm_tsum_le_norm_mul {R E : Type*} [SeminormedRing R]
    [SeminormedAddCommGroup E] [IsUltrametricDist E] (f : R → E)
    (hf : ∀ w : R, ‖w‖ < 1 → ‖f w‖ ≤ ‖w‖) {q w : R} (hq : ‖q‖ ≤ 1) (hw : ‖q * w‖ < 1) :
    ‖∑' n : ℕ, f (q ^ (n + 1) * w)‖ ≤ ‖q * w‖ := by
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg _) fun n ↦ ?_
  have h := norm_pow_succ_mul_le hq w n
  exact (hf _ (h.trans_lt hw)).trans h

/-- Two convergent one-sided series `∑_{n ≥ 1} f(qⁿ w)` and `∑_{n ≥ 1} f(qⁿ w')` with values in
an ultrametric group, whose terms are `1`-Lipschitz on the open unit ball, differ by at most
`‖q (w - w')‖` when `‖q‖ ≤ 1` and `‖q w‖, ‖q w'‖ < 1`. -/
theorem norm_tsum_sub_tsum_le_norm_mul {R E : Type*} [SeminormedRing R]
    [NormedAddCommGroup E] [IsUltrametricDist E] (f : R → E)
    (hf : ∀ t t' : R, ‖t‖ < 1 → ‖t'‖ < 1 → ‖f t - f t'‖ ≤ ‖t - t'‖) {q w w' : R}
    (hq : ‖q‖ ≤ 1) (hw : ‖q * w‖ < 1) (hw' : ‖q * w'‖ < 1)
    (hs : Summable fun n : ℕ ↦ f (q ^ (n + 1) * w))
    (hs' : Summable fun n : ℕ ↦ f (q ^ (n + 1) * w')) :
    ‖∑' n : ℕ, f (q ^ (n + 1) * w) - ∑' n : ℕ, f (q ^ (n + 1) * w')‖ ≤ ‖q * (w - w')‖ := by
  rw [← hs.tsum_sub hs']
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg _) fun n ↦ ?_
  refine (hf _ _ ((norm_pow_succ_mul_le hq w n).trans_lt hw)
    ((norm_pow_succ_mul_le hq w' n).trans_lt hw')).trans ?_
  rw [← mul_sub]
  exact norm_pow_succ_mul_le hq _ n

/-- A one-sided series `∑_{n ≥ 1} f(qⁿ u)` at `u` and one `∑_{n ≥ 1} g(qⁿ u⁻¹)` at `u⁻¹`, with
values in an ultrametric group, together depend on `u` in a `‖q‖`-Lipschitz way on the unit
circle when their terms are `1`-Lipschitz on the open unit ball and `‖q‖ < 1`. Only the values
need to be ultrametric. -/
theorem norm_tsum_sub_tsum_add_tsum_sub_tsum_le {K E : Type*} [NormedField K]
    [NormedAddCommGroup E] [IsUltrametricDist E] {q u u' : K} (hq : ‖q‖ < 1) (hu : ‖u‖ = 1)
    (hu' : ‖u'‖ = 1) (f g : K → E) (hf : ∀ t t' : K, ‖t‖ < 1 → ‖t'‖ < 1 → ‖f t - f t'‖ ≤ ‖t - t'‖)
    (hg : ∀ t t' : K, ‖t‖ < 1 → ‖t'‖ < 1 → ‖g t - g t'‖ ≤ ‖t - t'‖)
    (hfs : Summable fun n : ℕ ↦ f (q ^ (n + 1) * u))
    (hfs' : Summable fun n : ℕ ↦ f (q ^ (n + 1) * u'))
    (hgs : Summable fun n : ℕ ↦ g (q ^ (n + 1) * u⁻¹))
    (hgs' : Summable fun n : ℕ ↦ g (q ^ (n + 1) * u'⁻¹)) :
    ‖(∑' n : ℕ, f (q ^ (n + 1) * u) - ∑' n : ℕ, f (q ^ (n + 1) * u')) +
        (∑' n : ℕ, g (q ^ (n + 1) * u⁻¹) - ∑' n : ℕ, g (q ^ (n + 1) * u'⁻¹))‖ ≤
      ‖q‖ * ‖u - u'‖ := by
  have hqw (w : K) (hw : ‖w‖ = 1) : ‖q * w‖ < 1 := by rwa [norm_mul, hw, mul_one]
  have hinv : ‖q * (u⁻¹ - u'⁻¹)‖ = ‖q‖ * ‖u - u'‖ := by
    have h₀ : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hu]; exact one_ne_zero)
    have h₀' : u' ≠ 0 := norm_ne_zero_iff.mp (by rw [hu']; exact one_ne_zero)
    rw [norm_mul, ← dist_eq_norm, dist_inv_inv₀ h₀ h₀', hu, hu', mul_one, div_one, dist_eq_norm]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [← norm_mul]
    exact norm_tsum_sub_tsum_le_norm_mul f hf hq.le (hqw _ hu) (hqw _ hu') hfs hfs'
  · rw [← hinv]
    exact norm_tsum_sub_tsum_le_norm_mul g hg hq.le (hqw _ (by rw [norm_inv, hu, inv_one]))
      (hqw _ (by rw [norm_inv, hu', inv_one])) hgs hgs'

section Field

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- A difference of the form `(t - t') P / ((1 - t)ᵏ (1 - t')ᵏ)` with `‖t‖, ‖t'‖ < 1` and
`‖P‖ ≤ 1` has norm at most `‖t - t'‖`. -/
theorem norm_sub_le_of_eq_mul_div {t t' a a' P : K} (ht : ‖t‖ < 1) (ht' : ‖t'‖ < 1)
    {k : ℕ} (h : a - a' = (t - t') * P / ((1 - t) ^ k * (1 - t') ^ k)) (hP : ‖P‖ ≤ 1) :
    ‖a - a'‖ ≤ ‖t - t'‖ := by
  rw [h, norm_div, norm_mul, norm_mul, norm_pow, norm_pow, norm_one_sub_of_norm_lt_one ht,
    norm_one_sub_of_norm_lt_one ht', one_pow, mul_one, div_one]
  exact mul_le_of_le_one_right (norm_nonneg _) hP

/-- The map `t ↦ t / (1 - t)²` is `1`-Lipschitz on the open unit ball of an ultrametric
field. -/
theorem norm_div_one_sub_sq_sub_div_one_sub_sq_le {t t' : K} (ht : ‖t‖ < 1) (ht' : ‖t'‖ < 1) :
    ‖t / (1 - t) ^ 2 - t' / (1 - t') ^ 2‖ ≤ ‖t - t'‖ := by
  have h₁ : 1 - t ≠ 0 := norm_ne_zero_iff.mp (by simp [ht])
  have h₂ : 1 - t' ≠ 0 := norm_ne_zero_iff.mp (by simp [ht'])
  refine norm_sub_le_of_eq_mul_div ht ht' (P := 1 - t * t') (k := 2) (by field_simp; ring)
    (Subring.mem_unitClosedBall.mp ?_)
  have h₃ : t ∈ Subring.unitClosedBall K := Subring.mem_unitClosedBall.mpr ht.le
  have h₄ : t' ∈ Subring.unitClosedBall K := Subring.mem_unitClosedBall.mpr ht'.le
  apply_rules [sub_mem, mul_mem, one_mem]

/-- The map `v ↦ (1 - v)³ / v` is `1`-Lipschitz on the unit circle of an ultrametric field. -/
theorem norm_one_sub_cube_div_sub_one_sub_cube_div_le {v w : K} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ‖(1 - v) ^ 3 / v - (1 - w) ^ 3 / w‖ ≤ ‖v - w‖ := by
  have h₀ : v ≠ 0 := norm_ne_zero_iff.mp (by rw [hv]; exact one_ne_zero)
  have h₀' : w ≠ 0 := norm_ne_zero_iff.mp (by rw [hw]; exact one_ne_zero)
  have e : (1 - v) ^ 3 / v - (1 - w) ^ 3 / w =
      (w - v) * (1 - v * w - v * w - v * w + v * w * (v + w)) / (v * w) := by
    field_simp
    ring
  have h₃ : v ∈ Subring.unitClosedBall K := Subring.mem_unitClosedBall.mpr hv.le
  have h₄ : w ∈ Subring.unitClosedBall K := Subring.mem_unitClosedBall.mpr hw.le
  have hP : 1 - v * w - v * w - v * w + v * w * (v + w) ∈ Subring.unitClosedBall K := by
    apply_rules [add_mem, sub_mem, mul_mem, one_mem]
  rw [e, norm_div, norm_mul, norm_mul, hv, hw, mul_one, div_one, norm_sub_rev]
  exact mul_le_of_le_one_right (norm_nonneg _) (Subring.mem_unitClosedBall.mp hP)

end Field

/-- In an ultrametric seminormed ring, if `a` and `b` are within `B ≤ 1` of `1`, so is `a * b`. -/
theorem norm_mul_sub_one_le {R : Type*} [SeminormedRing R] [IsUltrametricDist R] {a b : R}
    {B : ℝ} (hB : B ≤ 1) (ha : ‖a - 1‖ ≤ B) (hb : ‖b - 1‖ ≤ B) : ‖a * b - 1‖ ≤ B := by
  calc ‖a * b - 1‖ = ‖(a - 1) * (b - 1) + (a - 1) + (b - 1)‖ := by
        congr 1
        simp only [mul_sub, sub_mul, mul_one, one_mul]
        abel
    _ ≤ max (max ‖(a - 1) * (b - 1)‖ ‖a - 1‖) ‖b - 1‖ :=
      (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le_max (IsUltrametricDist.norm_add_le_max _ _) le_rfl)
    _ ≤ B := max_le (max_le ((norm_mul_le _ _).trans
      ((mul_le_of_le_one_right (norm_nonneg _) (hb.trans hB)).trans ha)) ha) hb

/-- In an ultrametric seminormed ring, if `a` and `b` are both strictly within `ε ≤ 1` of `1`,
so is `a * b`. -/
theorem norm_mul_sub_one_lt {R : Type*} [SeminormedRing R] [IsUltrametricDist R] {a b : R}
    {ε : ℝ} (hε : ε ≤ 1) (ha : ‖a - 1‖ < ε) (hb : ‖b - 1‖ < ε) : ‖a * b - 1‖ < ε :=
  (norm_mul_sub_one_le ((max_le ha.le hb.le).trans hε) (le_max_left _ _)
    (le_max_right _ _)).trans_lt (max_lt ha hb)

/-- In an ultrametric normed ring, the group law `a ⊕ b = a + b + a b` keeps the closed ball of
radius `ε ≤ 1` about `0`, since `a ⊕ b = (1 + a) (1 + b) - 1`. -/
theorem norm_add_add_mul_le {R : Type*} [SeminormedRing R] [IsUltrametricDist R] {a b : R}
    {ε : ℝ} (hε : ε ≤ 1) (ha : ‖a‖ ≤ ε) (hb : ‖b‖ ≤ ε) : ‖a + b + a * b‖ ≤ ε := by
  have h := norm_mul_sub_one_le hε (a := 1 + a) (b := 1 + b) (by simpa using ha)
    (by simpa using hb)
  convert h using 2
  simp only [add_mul, mul_add, one_mul, mul_one]
  abel

/-- In an ultrametric normed division ring, an element `x` within distance less than one of `1`
has an inverse at the same distance from `1`: `‖x⁻¹ - 1‖ = ‖x - 1‖`. Unlike the Neumann estimate
`TauCeti.norm_inverse_one_sub_sub_one`, this needs no convergent geometric series, so it applies
over incomplete fields such as an algebraic closure of `ℚ_[p]`. -/
theorem norm_inv_sub_one_eq {K : Type*} [NormedDivisionRing K] [IsUltrametricDist K] {x : K}
    (hx : ‖x - 1‖ < 1) : ‖x⁻¹ - 1‖ = ‖x - 1‖ := by
  have hx₁ : ‖x‖ = 1 := norm_eq_one_of_norm_one_sub_lt_one ((norm_sub_rev _ _).trans_lt hx)
  have hx₀ : x ≠ 0 := norm_ne_zero_iff.1 (hx₁.symm ▸ one_ne_zero)
  calc ‖x⁻¹ - 1‖ = ‖x⁻¹ * (1 - x)‖ := by rw [mul_sub, mul_one, inv_mul_cancel₀ hx₀]
    _ = ‖x - 1‖ := by simp [hx₁, norm_sub_rev]

/-- In an ultrametric seminormed ring, a power of an element `x` of norm at most
one is no farther from `1` than `x` is: `‖x ^ n - 1‖ ≤ ‖x - 1‖`. -/
theorem norm_pow_sub_one_le_norm_sub_one {R : Type*} [SeminormedRing R] [IsUltrametricDist R]
    {x : R} (hx : ‖x‖ ≤ 1) (n : ℕ) : ‖x ^ n - 1‖ ≤ ‖x - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc ‖x ^ (n + 1) - 1‖ = ‖x * (x ^ n - 1) + (x - 1)‖ := by
          rw [mul_sub, mul_one, pow_succ', sub_add_sub_cancel]
      _ ≤ max ‖x * (x ^ n - 1)‖ ‖x - 1‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ ‖x - 1‖ := max_le ((norm_mul_le _ _).trans
        ((mul_le_of_le_one_left (norm_nonneg _) hx).trans ih)) le_rfl

/-- In an ultrametric seminormed commutative ring, a finite product of elements within `B ≤ 1` of
`1` is again within `B` of `1` (for `0 ≤ B`). -/
theorem norm_prod_sub_one_le {ι R : Type*} [SeminormedCommRing R] [IsUltrametricDist R]
    (s : Finset ι) (f : ι → R) {B : ℝ} (hB0 : 0 ≤ B) (hB1 : B ≤ 1)
    (hf : ∀ i ∈ s, ‖f i - 1‖ ≤ B) : ‖∏ i ∈ s, f i - 1‖ ≤ B := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hB0
  | insert j s hj ih =>
    rw [Finset.prod_insert hj]
    exact norm_mul_sub_one_le hB1 (hf j (Finset.mem_insert_self j s))
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-- In an ultrametric seminormed commutative ring, a finite product of elements each strictly within
`ε ≤ 1` of `1` is again strictly within `ε` of `1` (for `0 < ε`). -/
theorem norm_prod_sub_one_lt {ι R : Type*} [SeminormedCommRing R] [IsUltrametricDist R]
    (s : Finset ι) (f : ι → R) {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1)
    (hf : ∀ i ∈ s, ‖f i - 1‖ < ε) : ‖∏ i ∈ s, f i - 1‖ < ε := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hε0
  | insert j s hj ih =>
    rw [Finset.prod_insert hj]
    exact norm_mul_sub_one_lt hε (hf j (Finset.mem_insert_self j s))
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-- If two finite families are bounded by `M` and differ by at most `ε` in each coordinate,
their products differ by at most `ε * M ^ (s.card - 1)`. The exponent uses natural subtraction,
so the statement includes the empty product and `M = 0`. -/
theorem norm_prod_sub_prod_le {ι R : Type*} [SeminormedCommRing R]
    [IsUltrametricDist R] {s : Finset ι} {f g : ι → R} {M ε : ℝ} (hε : 0 ≤ ε)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ M) (hg : ∀ i ∈ s, ‖g i‖ ≤ M)
    (hfg : ∀ i ∈ s, ‖f i - g i‖ ≤ ε) :
    ‖∏ i ∈ s, f i - ∏ i ∈ s, g i‖ ≤ ε * M ^ (s.card - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hε]
  | insert a s ha ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simpa using hfg a (by simp)
    have hprod : ‖∏ i ∈ s, f i‖ ≤ M ^ s.card := by
      calc ‖∏ i ∈ s, f i‖ ≤ ∏ i ∈ s, ‖f i‖ := TauCeti.norm_prod_le_prod_norm_of_nonempty hs f
        _ ≤ ∏ _i ∈ s, M := Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
          fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
        _ = M ^ s.card := Finset.prod_const _
    have htail := ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
      (fun i hi ↦ hg i (Finset.mem_insert_of_mem hi))
      (fun i hi ↦ hfg i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha,
      Nat.add_sub_cancel]
    calc ‖f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i‖ =
          ‖(f a - g a) * ∏ i ∈ s, f i + g a * (∏ i ∈ s, f i - ∏ i ∈ s, g i)‖ := by
            congr 1
            ring
      _ ≤ max (‖f a - g a‖ * ‖∏ i ∈ s, f i‖)
          (‖g a‖ * ‖∏ i ∈ s, f i - ∏ i ∈ s, g i‖) :=
        (IsUltrametricDist.norm_add_le_max _ _).trans
          (max_le_max (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ max (ε * M ^ s.card) (M * (ε * M ^ (s.card - 1))) :=
        max_le_max (mul_le_mul (hfg a (by simp)) hprod (norm_nonneg _) hε)
          (mul_le_mul (hg a (by simp)) htail (norm_nonneg _)
            ((norm_nonneg _).trans (hg a (by simp))))
      _ = ε * M ^ s.card := by
        have hcard : s.card - 1 + 1 = s.card := Nat.sub_add_cancel (Finset.card_pos.mpr hs)
        rw [mul_left_comm M ε, ← pow_succ', hcard, max_self]

/-- **Monomials in close families of a bounded subring are close.** In an ultrametric seminormed
commutative ring, let `b` and `y` be families whose members indexed by a finset `s` lie in a
subring `R₀` with elements of norm at most `N`, and satisfy `‖bᵢ - yᵢ‖ ≤ δ`. Then the monomials
`∏ bᵢ ^ dᵢ` and `∏ yᵢ ^ dᵢ` over `s` differ by at most `N * δ`, whatever the degree: their
difference lies in the ideal of `R₀` generated by the `bᵢ - yᵢ`. Compare
`norm_prod_sub_prod_le`, whose bound grows with the number of factors. -/
theorem norm_prod_pow_sub_prod_pow_le {ι R : Type*} [SeminormedCommRing R] [IsUltrametricDist R]
    {R₀ : Subring R} {N δ : ℝ} (hN : ∀ x ∈ R₀, ‖x‖ ≤ N) (hδ : 0 ≤ δ) (s : Finset ι)
    {b y : ι → R} (hb : ∀ i ∈ s, b i ∈ R₀) (hy : ∀ i ∈ s, y i ∈ R₀)
    (hby : ∀ i ∈ s, ‖b i - y i‖ ≤ δ) (d : ι → ℕ) :
    ‖∏ i ∈ s, b i ^ d i - ∏ i ∈ s, y i ^ d i‖ ≤ N * δ := by
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0 R₀.zero_mem)
  -- work in `R₀`, indexing by the finite type `s`
  let x : s → R₀ := fun i ↦ ⟨b i, hb i i.property⟩
  let z : s → R₀ := fun i ↦ ⟨y i, hy i i.property⟩
  have hmem : ∏ i, x i ^ d i - ∏ i, z i ^ d i ∈ Ideal.span (Set.range fun i ↦ x i - z i) := by
    rw [← Ideal.Quotient.eq, map_prod, map_prod]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    have hi : Ideal.Quotient.mk (Ideal.span (Set.range fun i ↦ x i - z i)) (x i) =
        Ideal.Quotient.mk _ (z i) :=
      Ideal.Quotient.eq.mpr (Ideal.subset_span (Set.mem_range_self i))
    rw [map_pow, map_pow, hi]
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  have hsum : ∏ i ∈ s, b i ^ d i - ∏ i ∈ s, y i ^ d i = ∑ i, (c i : R) * (b i - y i) := by
    rw [← Finset.prod_coe_sort s, ← Finset.prod_coe_sort s fun i ↦ y i ^ d i]
    simpa [x, z] using congrArg (R₀.subtype) hc.symm
  rw [hsum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hN0 hδ) fun i _ ↦ ?_
  calc ‖(c i : R) * (b i - y i)‖ ≤ ‖(c i : R)‖ * ‖b i - y i‖ := norm_mul_le _ _
    _ ≤ N * δ := mul_le_mul (hN _ (c i).property) (hby i i.property) (norm_nonneg _) hN0

section FwdDiff

open Finset
open scoped fwdDiff

variable {A : Type*} [SeminormedCommRing A] [NormOneClass A] [IsUltrametricDist A] {c : ℝ}
  {h x : A}

/-- **Forward differences of powers.** In an ultrametric seminormed commutative ring with
`‖1‖ = 1`,
for a point `x` and a step `h` with `‖x‖ ≤ c` and `‖h‖ ≤ c`,
`‖Δₕᵏ (y ↦ yᵐ)(x)‖ cᵏ ≤ ‖k!‖ ‖h‖ᵏ cᵐ`. -/
theorem norm_fwdDiff_iter_pow_mul_pow_le (hh : ‖h‖ ≤ c) (hx : ‖x‖ ≤ c) (k m : ℕ) :
    ‖Δ_[h]^[k] (fun y : A ↦ y ^ m) x‖ * c ^ k ≤ ‖(k.factorial : A)‖ * ‖h‖ ^ k * c ^ m := by
  have hc : 0 ≤ c := (norm_nonneg h).trans hh
  rw [fwdDiff_iter_pow_eq_sum]
  rcases lt_or_ge m k with hmk | hkm
  · rw [sum_eq_zero fun l hl ↦ by
      rw [Nat.stirlingSecond_eq_zero_of_lt (by grind), Nat.cast_zero, mul_zero, mul_zero]]
    simp only [norm_zero, zero_mul]
    positivity
  rw [← pow_sub_mul_pow c hkm, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right
    (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun l hl ↦ ?_)
    (by positivity)
  rcases lt_or_ge l k with hlk | hkl
  · rw [Nat.stirlingSecond_eq_zero_of_lt hlk, Nat.cast_zero, mul_zero, mul_zero, norm_zero]
    positivity
  have hlm : l ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hl)
  calc ‖x ^ (m - l) * h ^ l * (m.choose l : A) * ((k.factorial : A) * l.stirlingSecond k)‖
      ≤ ‖x‖ ^ (m - l) * ‖h‖ ^ l * 1 * (‖(k.factorial : A)‖ * 1) := by
        refine (norm_mul_le _ _).trans (mul_le_mul ?_ ((norm_mul_le _ _).trans ?_)
          (norm_nonneg _) (by positivity))
        · refine (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans ?_)
            (IsUltrametricDist.norm_natCast_le_one A _) (norm_nonneg _) (by positivity))
          exact mul_le_mul (norm_pow_le _ _) (norm_pow_le _ _) (norm_nonneg _) (by positivity)
        · exact mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_natCast_le_one A _)
            (norm_nonneg _)
    _ ≤ c ^ (m - l) * (‖h‖ ^ k * c ^ (l - k)) * 1 * (‖(k.factorial : A)‖ * 1) := by
        rw [← pow_mul_pow_sub ‖h‖ hkl]
        gcongr
    _ = ‖(k.factorial : A)‖ * ‖h‖ ^ k * c ^ (m - k) := by
        rw [← Nat.sub_add_sub_cancel hlm hkl, pow_add]
        ring

end FwdDiff

end TauCeti
