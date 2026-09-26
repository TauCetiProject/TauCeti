/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.Basic

/-!
# Power and bracket in degree zero of the lower `p`-series

Away from degree zero the power operator `π` on the graded pieces of the lower `p`-series
commutes with the bracket (`TauCeti.gradedPow_gradedBracket_left`,
`TauCeti.gradedPow_gradedBracket_right`). This file treats the remaining case, where the powered
input has degree zero. The binomial collection formula for `⁅a ^ n, b⁆` and `⁅a, b ^ n⁆` produces
a correction term: for `x` of degree zero,

  `[π x, y] = π [x, y] + (p choose 2) • [x, [x, y]]`,

and symmetrically `[x, π y] = π [x, y] + (p choose 2) • [y, [x, y]]` for `y` of degree zero. For
odd `p` the correction vanishes, so `π` commutes with the bracket in every degree; for `p = 2` it
is the iterated bracket `[[x, y], x]`, resp. `[[x, y], y]`. These are the counterparts for the
bracket of the degree-zero additivity defect `π (x + y) = π x + π y + (p choose 2) • [y, x]`
(`TauCeti.gradedPow_add_zero`), and together with the results away from degree zero they describe
`π` on the whole graded Lie algebra.

## Main results

* `TauCeti.mk_commutatorElement_pow_left`, `TauCeti.mk_commutatorElement_pow_right`: the
  collection formulas for `⁅a ^ n, b⁆` and `⁅a, b ^ n⁆` modulo `λ_{k+3}` when the unpowered input
  lies in `λ_k`.
* `TauCeti.gradedBracket_gradedPow_zero_left`, `TauCeti.gradedBracket_gradedPow_zero_right`: the
  degree-zero corrections `(p choose 2) • [x, [x, y]]` and `(p choose 2) • [y, [x, y]]`.
* `TauCeti.gradedPow_gradedBracket_left_of_odd`, `TauCeti.gradedPow_gradedBracket_right_of_odd`:
  for odd `p`, `π [x, y] = [π x, y] = [x, π y]` in every degree.
* `TauCeti.gradedBracket_gradedPow_zero_left_of_two`,
  `TauCeti.gradedBracket_gradedPow_zero_right_of_two`: for `p = 2`,
  `[π x, y] = π [x, y] + [[x, y], x]` and `[x, π y] = π [x, y] + [[x, y], y]`.

## References

* J. Labute, *Classification of Demushkin groups*, Canadian J. Math. 19 (1967), §1,
  Propositions 1 and 2.
-/

public section

open Subgroup
open scoped commutatorElement

namespace TauCeti

universe u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Collection of a powered commutator modulo `λ_{k+3}`. The iterated commutator lies in
`λ_{k+2}`, so its image is central and the binomial formula applies. -/
theorem mk_commutatorElement_pow_left {k : ℕ} {a b : G}
    (hb : b ∈ pLowerCentralSeries p G k) (n : ℕ) :
    ((⁅a ^ n, b⁆ : G) : G ⧸ pLowerCentralSeries p G (k + 2 + 1)) =
      ((⁅a, b⁆ ^ n * ⁅a, ⁅a, b⁆⁆ ^ n.choose 2 : G) : G ⧸ _) := by
  have ha : a ∈ pLowerCentralSeries p G 0 := by simp
  have hd : ⁅a, ⁅a, b⁆⁆ ∈ pLowerCentralSeries p G (k + 2) := by
    simpa only [zero_add, Nat.add_assoc] using
      commutator_mem_pLowerCentralSeries ha (commutator_mem_pLowerCentralSeries ha hb)
  simp only [← QuotientGroup.mk'_apply, map_commutatorElement, map_pow, map_mul]
  refine commutatorElement_pow_left_of_commute ?_ ?_ n
  · simpa only [← QuotientGroup.mk'_apply, map_commutatorElement] using
      commute_mk_of_mem_pLowerCentralSeries hd a
  · simpa only [← QuotientGroup.mk'_apply, map_commutatorElement] using
      commute_mk_of_mem_pLowerCentralSeries hd ⁅a, b⁆

/-- Collection in the right input modulo `λ_{j+3}`. The correction involves
`⁅b, ⁅a, b⁆⁆`; reversing the outer commutator would change its sign. -/
theorem mk_commutatorElement_pow_right {j : ℕ} {a b : G}
    (ha : a ∈ pLowerCentralSeries p G j) (n : ℕ) :
    ((⁅a, b ^ n⁆ : G) : G ⧸ pLowerCentralSeries p G (j + 2 + 1)) =
      ((⁅a, b⁆ ^ n * ⁅b, ⁅a, b⁆⁆ ^ n.choose 2 : G) : G ⧸ _) := by
  have hb : b ∈ pLowerCentralSeries p G 0 := by simp
  have hd : ⁅b, ⁅a, b⁆⁆ ∈ pLowerCentralSeries p G (j + 2) := by
    simpa only [zero_add, add_zero, Nat.add_assoc] using
      commutator_mem_pLowerCentralSeries hb (commutator_mem_pLowerCentralSeries ha hb)
  simp only [← QuotientGroup.mk'_apply, map_commutatorElement, map_pow, map_mul]
  refine commutatorElement_pow_right_of_commute ?_ ?_ n
  · simpa only [← QuotientGroup.mk'_apply, map_commutatorElement] using
      commute_mk_of_mem_pLowerCentralSeries hd b
  · simpa only [← QuotientGroup.mk'_apply, map_commutatorElement] using
      commute_mk_of_mem_pLowerCentralSeries hd ⁅a, b⁆

/-- The correction to `[π x, y] = π [x, y]` when `x` has degree zero is
`(p choose 2) • [x, [x, y]]`, transported to the degree of `π [x, y]`. -/
theorem gradedBracket_gradedPow_zero_left {k : ℕ} (x : gradedPiece p G 0)
    (y : gradedPiece p G k) :
    gradedCast p G (by omega) (gradedBracket p G 1 k (gradedPow p G 0 x) y) =
      gradedPow p G (0 + k + 1) (gradedBracket p G 0 k x y) +
        p.choose 2 • gradedCast p G (by omega)
          (gradedBracket p G 0 (0 + k + 1) x (gradedBracket p G 0 k x y)) := by
  obtain ⟨x, rfl⟩ := gradedMk_surjective 0 x
  obtain ⟨y, rfl⟩ := gradedMk_surjective k y
  simp only [gradedPow_gradedMk, gradedBracket_gradedMk, gradedCast_gradedMk,
    ← gradedMk_pow, ← gradedMk_mul, gradedMk_eq_gradedMk_iff, coe_mul, coe_pow]
  have hdegree : k + 2 + 1 = 0 + k + 1 + 1 + 1 := by omega
  exact hdegree ▸ mk_commutatorElement_pow_left (a := (x : G)) y.2 p

/-- The correction to `[x, π y] = π [x, y]` when `y` has degree zero is
`(p choose 2) • [y, [x, y]]`, with the inner bracket in this order. -/
theorem gradedBracket_gradedPow_zero_right {j : ℕ} (x : gradedPiece p G j)
    (y : gradedPiece p G 0) :
    gradedCast p G (by omega) (gradedBracket p G j 1 x (gradedPow p G 0 y)) =
      gradedPow p G (j + 0 + 1) (gradedBracket p G j 0 x y) +
        p.choose 2 • gradedCast p G (by omega)
          (gradedBracket p G 0 (j + 0 + 1) y (gradedBracket p G j 0 x y)) := by
  obtain ⟨x, rfl⟩ := gradedMk_surjective j x
  obtain ⟨y, rfl⟩ := gradedMk_surjective 0 y
  simp only [gradedPow_gradedMk, gradedBracket_gradedMk, gradedCast_gradedMk,
    ← gradedMk_pow, ← gradedMk_mul, gradedMk_eq_gradedMk_iff, coe_mul, coe_pow]
  simpa only [add_zero, Nat.add_assoc] using
    mk_commutatorElement_pow_right (b := (y : G)) x.2 p

/-- For odd `p`, the power operator commutes with the bracket on the left in every degree,
including degree zero. No primality assumption is needed. -/
theorem gradedPow_gradedBracket_left_of_odd (hp : Odd p) {j k : ℕ}
    (x : gradedPiece p G j) (y : gradedPiece p G k) :
    gradedPow p G (j + k + 1) (gradedBracket p G j k x y) =
      gradedCast p G (by omega) (gradedBracket p G (j + 1) k (gradedPow p G j x) y) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have h := gradedBracket_gradedPow_zero_left x y
    rw [Nat.choose_two_right, Nat.mul_div_assoc _ (Nat.Odd.sub_odd hp odd_one).two_dvd,
      mul_nsmul, nsmul_gradedPiece_eq_zero, nsmul_zero] at h
    simpa only [add_zero] using h.symm
  · exact gradedPow_gradedBracket_left hj x y

/-- For odd `p`, the power operator commutes with the bracket on the right in every degree,
including degree zero. No primality assumption is needed. -/
theorem gradedPow_gradedBracket_right_of_odd (hp : Odd p) {j k : ℕ}
    (x : gradedPiece p G j) (y : gradedPiece p G k) :
    gradedPow p G (j + k + 1) (gradedBracket p G j k x y) =
      gradedCast p G (by omega) (gradedBracket p G j (k + 1) x (gradedPow p G k y)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h := gradedBracket_gradedPow_zero_right x y
    rw [Nat.choose_two_right, Nat.mul_div_assoc _ (Nat.Odd.sub_odd hp odd_one).two_dvd,
      mul_nsmul, nsmul_gradedPiece_eq_zero, nsmul_zero] at h
    simpa only [add_zero] using h.symm
  · exact gradedPow_gradedBracket_right hk x y

private theorem neg_gradedPiece_two {k : ℕ} (x : gradedPiece 2 G k) : -x = x := by
  rw [neg_eq_iff_add_eq_zero]
  exact (two_nsmul _).symm.trans (nsmul_gradedPiece_eq_zero _)

private theorem gradedCast_trans {i j k : ℕ} (hij : i = j) (hjk : j = k)
    (x : gradedPiece p G i) :
    gradedCast p G hjk (gradedCast p G hij x) = gradedCast p G (hij.trans hjk) x := by
  subst hij
  subst hjk
  simp only [gradedCast_rfl]

/-- For `p = 2` and `x` of degree zero, `[π x, y] = π [x, y] + [[x, y], x]`.
The last term has this orientation because every graded piece is killed by `2`. -/
theorem gradedBracket_gradedPow_zero_left_of_two (hp : p = 2) {k : ℕ}
    (x : gradedPiece p G 0) (y : gradedPiece p G k) :
    gradedCast p G (by omega) (gradedBracket p G 1 k (gradedPow p G 0 x) y) =
      gradedPow p G (0 + k + 1) (gradedBracket p G 0 k x y) +
        gradedCast p G (by omega)
          (gradedBracket p G (0 + k + 1) 0 (gradedBracket p G 0 k x y) x) := by
  subst hp
  rw [gradedBracket_gradedPow_zero_left, Nat.choose_self, one_nsmul]
  congr 1
  -- Skew-symmetry reverses the outer bracket up to a sign, which is trivial for `p = 2`.
  rw [← neg_gradedPiece_two (gradedBracket 2 G 0 (0 + k + 1) x (gradedBracket 2 G 0 k x y)),
    ← gradedCast_gradedBracket_swap, gradedCast_trans]

/-- For `p = 2` and `y` of degree zero, `[x, π y] = π [x, y] + [[x, y], y]`.
The inner bracket retains the order `[x, y]`. -/
theorem gradedBracket_gradedPow_zero_right_of_two (hp : p = 2) {j : ℕ}
    (x : gradedPiece p G j) (y : gradedPiece p G 0) :
    gradedCast p G (by omega) (gradedBracket p G j 1 x (gradedPow p G 0 y)) =
      gradedPow p G (j + 0 + 1) (gradedBracket p G j 0 x y) +
        gradedCast p G (by omega)
          (gradedBracket p G (j + 0 + 1) 0 (gradedBracket p G j 0 x y) y) := by
  subst hp
  rw [gradedBracket_gradedPow_zero_right, Nat.choose_self, one_nsmul]
  congr 1
  -- Skew-symmetry reverses the outer bracket up to a sign, which is trivial for `p = 2`.
  rw [← neg_gradedPiece_two (gradedBracket 2 G 0 (j + 0 + 1) y (gradedBracket 2 G j 0 x y)),
    ← gradedCast_gradedBracket_swap, gradedCast_trans]

end TauCeti
