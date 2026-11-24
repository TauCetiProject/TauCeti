/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.Algebra.Field.CrossRatio
public import TauCeti.Topology.Compactification.OnePoint.CrossRatio.Basic

/-!
# Scalar-valued cross-ratio on the projective line

Extending the finite cross-ratio `TauCeti.crossRatio a b c d = (a - c) * (b - d) / ((a - d) *
(b - c))` to the projective line `OnePoint K` by the four one-infinity cancellation formulas and
assigning `0` when at least two entries are `∞` defines
`OnePoint.crossRatioSphere : OnePoint K → OnePoint K → OnePoint K → OnePoint K → K`.

Unlike `OnePoint.crossRatio`, which takes values in `OnePoint K` and is normalized by
`OnePoint.crossRatio 0 1 ∞ z = z`, `OnePoint.crossRatioSphere` takes values directly in `K`, is
normalized by `crossRatioSphere ∞ 0 1 z = z`, and totalises poles and multi-infinity degeneracies
to `0 : K`. On non-degenerate quadruples the two conventions are related by permuting the first
three entries: `(crossRatioSphere a b c d : OnePoint K) = OnePoint.crossRatio b c a d`. The
bracket `[a, b, c, d]` normalized by `[∞, 1, 0, x] = x` equals `1 - crossRatioSphere a b c d`.

## Main definitions

* `OnePoint.crossRatioSphere`: the scalar-valued extension of `TauCeti.crossRatio` to `OnePoint K`,
  given by the four one-infinity cancellation formulas and `0` when two or more arguments equal
  `∞`.

## Main results

* `OnePoint.crossRatioSphere_eq_zero_iff` and `OnePoint.crossRatioSphere_eq_one_iff`: exact
  characterizations of when `crossRatioSphere` takes the values `0` and `1`, together with
  `OnePoint.crossRatioSphere_ne_zero`, `OnePoint.crossRatioSphere_ne_one`, and their
  `*_of_injective` specializations.
* `OnePoint.crossRatioSphere_swap_first_second` and its five transposition companions: the
  anharmonic transformations `r ↦ r⁻¹`, `r ↦ 1 - r`, and `r ↦ r / (r - 1)` under sharp
  non-degeneracy hypotheses, together with `*_of_injective` specializations.
* `OnePoint.crossRatioSphere_eq_det_div` and `OnePoint.one_sub_crossRatioSphere_eq_det_div`:
  expression of `crossRatioSphere` and the bracket `1 - crossRatioSphere` as quotients of `2 × 2`
  homogeneous determinants via `OnePoint.equivProjectivization`.
* `OnePoint.crossRatioSphere_gl_smul`, `OnePoint.crossRatioSphere_pgl_smul`, and
  `OnePoint.crossRatioSphere_psl_smul`: Möbius invariance under `GL (Fin 2) K`, `PGL(2, K)`, and
  `PSL(2, K)` whenever `a ≠ b` and `c ≠ d`.
* `OnePoint.coe_crossRatioSphere_eq_crossRatio`: comparison with `OnePoint.crossRatio` whenever
  `a, b, c` are pairwise distinct, `a ≠ d`, and `c, d` are not both `∞`.
* `OnePoint.exists_gl_smul_eq_infty_zero_one_crossRatioSphere`,
  `OnePoint.exists_pgl_smul_eq_infty_zero_one_crossRatioSphere`, and
  `OnePoint.exists_gl_smul_eq_infty_zero_one_coe_coe`: normalization of five pairwise distinct
  points of `OnePoint K` to `![∞, 0, 1, x, y]` under `GL (Fin 2) K` and `PGL(2, K)` (built from
  `OnePoint.exists_smul_zero_one_infty_eq`), together with the omitted-point cross-ratio formulas
  on `![∞, 0, 1, x, y]`.
* `OnePoint.crossRatioSphere_cyclic_five_bracket`: the cyclic algebraic relation
  `1 - bᵢ = -bᵢ / (bᵢ₊₂ * bᵢ₊₃)` for `bᵢ = 1 - crossRatioSphere (s i) (s (i + 1)) (s (i + 2))
  (s (i + 3))` on five pairwise distinct points of `OnePoint K`.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993), §4.1.
* Don Zagier, *The dilogarithm function*, in *Frontiers in Number Theory, Physics, and Geometry II*,
  Springer (2007), Part I, §3 (the projective cross-ratio normalization and five-point coordinates).
* Alexander Goncharov and Daniil Rudenko, *Motivic correlators, cluster varieties and Zagier's
  conjecture on `ζ_F(4)`*, arXiv:1803.08585, §1.1 (the bracket `1 - r` and cyclic five-bracket
  relation).
-/

public section

open Function Matrix
open scoped LinearAlgebra.Projectivization MatrixGroups

namespace OnePoint

/-! ### Definition, basic identities, and anharmonic symmetries -/

section Basic

variable {K : Type*} [Field K]

/-- The field-valued cross-ratio on the projective line `OnePoint K`, defined on finite points by
`(a - c) * (b - d) / ((a - d) * (b - c))`, on quadruples with a single `∞` by the four cancellation
formulas, and equal to `0` when at least two entries equal `∞`. Normalized by
`crossRatioSphere ∞ 0 1 z = z`. -/
def crossRatioSphere : OnePoint K → OnePoint K → OnePoint K → OnePoint K → K
  | .some a, .some b, .some c, .some d => TauCeti.crossRatio a b c d
  | .infty, .some b, .some c, .some d => (b - d) / (b - c)
  | .some a, .infty, .some c, .some d => (a - c) / (a - d)
  | .some a, .some b, .infty, .some d => (b - d) / (a - d)
  | .some a, .some b, .some c, .infty => (a - c) / (b - c)
  | _, _, _, _ => 0

/-- On four finite points, `crossRatioSphere` restricts to `TauCeti.crossRatio`. -/
@[simp]
theorem crossRatioSphere_coe (a b c d : K) :
    crossRatioSphere (a : OnePoint K) b c d = TauCeti.crossRatio a b c d :=
  (rfl)

/-- Cancellation formula for `crossRatioSphere` when only the first entry is `∞`. -/
@[simp]
theorem crossRatioSphere_infty_coe_coe_coe (b c d : K) :
    crossRatioSphere ∞ (b : OnePoint K) c d = (b - d) / (b - c) :=
  (rfl)

/-- Cancellation formula for `crossRatioSphere` when only the second entry is `∞`. -/
@[simp]
theorem crossRatioSphere_coe_infty_coe_coe (a c d : K) :
    crossRatioSphere (a : OnePoint K) ∞ c d = (a - c) / (a - d) :=
  (rfl)

/-- Cancellation formula for `crossRatioSphere` when only the third entry is `∞`. -/
@[simp]
theorem crossRatioSphere_coe_coe_infty_coe (a b d : K) :
    crossRatioSphere (a : OnePoint K) b ∞ d = (b - d) / (a - d) :=
  (rfl)

/-- Cancellation formula for `crossRatioSphere` when only the fourth entry is `∞`. -/
@[simp]
theorem crossRatioSphere_coe_coe_coe_infty (a b c : K) :
    crossRatioSphere (a : OnePoint K) b c ∞ = (a - c) / (b - c) :=
  (rfl)

/-- `crossRatioSphere` vanishes when the first and third entries coincide (including at `∞`). -/
@[simp]
theorem crossRatioSphere_self_first_third (a b d : OnePoint K) :
    crossRatioSphere a b a d = 0 := by
  cases a <;> cases b <;> cases d <;> simp [crossRatioSphere]

/-- `crossRatioSphere` vanishes when the second and fourth entries coincide (including at `∞`). -/
@[simp]
theorem crossRatioSphere_self_second_fourth (a b c : OnePoint K) :
    crossRatioSphere a b c b = 0 := by
  cases a <;> cases b <;> cases c <;> simp [crossRatioSphere]

/-- `crossRatioSphere` vanishes when the first and fourth entries coincide (including at `∞`). -/
@[simp]
theorem crossRatioSphere_self_first_fourth (a b c : OnePoint K) :
    crossRatioSphere a b c a = 0 := by
  cases a <;> cases b <;> cases c <;> simp [crossRatioSphere]

/-- `crossRatioSphere` vanishes when the second and third entries coincide (including at `∞`). -/
@[simp]
theorem crossRatioSphere_self_second_third (a b d : OnePoint K) :
    crossRatioSphere a b b d = 0 := by
  cases a <;> cases b <;> cases d <;> simp [crossRatioSphere]

/-- `crossRatioSphere` vanishes when the first two entries are `∞`. -/
@[simp]
theorem crossRatioSphere_infty_infty (c d : OnePoint K) :
    crossRatioSphere ∞ ∞ c d = 0 := by
  cases c <;> cases d <;> rfl

/-- `crossRatioSphere` vanishes when the last two entries are `∞`. -/
@[simp]
theorem crossRatioSphere_infty_infty_right (a b : OnePoint K) :
    crossRatioSphere a b ∞ ∞ = 0 := by
  cases a <;> cases b <;> rfl

/-- `crossRatioSphere` vanishes whenever two distinct entries of the quadruple equal `∞`. -/
theorem crossRatioSphere_eq_zero_of_ne_of_eq_infty_of_eq_infty {s : Fin 4 → OnePoint K}
    {i j : Fin 4} (hij : i ≠ j) (hi : s i = ∞) (hj : s j = ∞) :
    crossRatioSphere (s 0) (s 1) (s 2) (s 3) = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all

/-- Swapping both `(a, b)` and `(c, d)` leaves `crossRatioSphere` unchanged on all quadruples. -/
theorem crossRatioSphere_swap_within_pairs (a b c d : OnePoint K) :
    crossRatioSphere b a d c = crossRatioSphere a b c d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    first | rfl | exact TauCeti.crossRatio_swap_within_pairs _ _ _ _

/-- Exchanging `(a, b)` with `(c, d)` leaves `crossRatioSphere` unchanged on all quadruples. -/
theorem crossRatioSphere_swap_pairs (a b c d : OnePoint K) :
    crossRatioSphere c d a b = crossRatioSphere a b c d := by
  have hneg (x y z : K) : (x - z) / (y - z) = (z - x) / (z - y) := by
    rw [← neg_sub z x, ← neg_sub z y, neg_div_neg_eq]
  cases a <;> cases b <;> cases c <;> cases d <;>
    first
    | rfl
    | exact TauCeti.crossRatio_swap_pairs _ _ _ _
    | exact hneg _ _ _
    | exact (hneg _ _ _).symm

/-- Reversing the order of all four points leaves `crossRatioSphere` unchanged. -/
theorem crossRatioSphere_reverse (a b c d : OnePoint K) :
    crossRatioSphere d c b a = crossRatioSphere a b c d := by
  rw [crossRatioSphere_swap_pairs, crossRatioSphere_swap_within_pairs]

/-- Exchanging the first two entries inverts `crossRatioSphere` unconditionally (with `0⁻¹ = 0`). -/
theorem crossRatioSphere_swap_first_second (a b c d : OnePoint K) :
    crossRatioSphere b a c d = (crossRatioSphere a b c d)⁻¹ := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    first | exact TauCeti.crossRatio_swap_first_second _ _ _ _ | simp [inv_div]

/-- Exchanging the last two entries inverts `crossRatioSphere` unconditionally (with `0⁻¹ = 0`). -/
theorem crossRatioSphere_swap_third_fourth (a b c d : OnePoint K) :
    crossRatioSphere a b d c = (crossRatioSphere a b c d)⁻¹ := by
  rw [← crossRatioSphere_swap_within_pairs, crossRatioSphere_swap_first_second]

/-- When a finite first entry is repeated, distinct from `c` and `d`, and `c, d` are not both `∞`,
`crossRatioSphere a a c d = 1`. -/
@[simp]
theorem crossRatioSphere_self_first_second {a c d : OnePoint K} (ha : a ≠ ∞) (hac : a ≠ c)
    (had : a ≠ d) (hcd : ¬(c = ∞ ∧ d = ∞)) :
    crossRatioSphere a a c d = 1 := by
  cases a with
  | infty => exact (ha rfl).elim
  | coe x =>
    cases c with
    | infty =>
      cases d with
      | infty => exact (hcd ⟨rfl, rfl⟩).elim
      | coe w =>
        rw [crossRatioSphere_coe_coe_infty_coe]
        exact div_self (sub_ne_zero.mpr (by simpa using had))
    | coe y =>
      cases d with
      | infty =>
        rw [crossRatioSphere_coe_coe_coe_infty]
        exact div_self (sub_ne_zero.mpr (by simpa using hac))
      | coe w =>
        rw [crossRatioSphere_coe]
        exact TauCeti.crossRatio_self_first_second (by simpa using had) (by simpa using hac)

/-- When a finite last entry is repeated, distinct from `a` and `b`, and `a, b` are not both `∞`,
`crossRatioSphere a b c c = 1`. -/
@[simp]
theorem crossRatioSphere_self_third_fourth {a b c : OnePoint K} (hc : c ≠ ∞) (hac : a ≠ c)
    (hbc : b ≠ c) (hab : ¬(a = ∞ ∧ b = ∞)) :
    crossRatioSphere a b c c = 1 := by
  rw [← crossRatioSphere_swap_pairs]
  exact crossRatioSphere_self_first_second hc hac.symm hbc.symm hab

/-- `crossRatioSphere a b c d` vanishes precisely when a pair of opposite or adjacent entries in
the numerator/denominator coincide (`a = c`, `b = d`, `a = d`, `b = c`) or both entries of the
first or second pair equal `∞`. -/
@[simp]
theorem crossRatioSphere_eq_zero_iff (a b c d : OnePoint K) :
    crossRatioSphere a b c d = 0 ↔
      a = c ∨ b = d ∨ a = d ∨ b = c ∨ (a = ∞ ∧ b = ∞) ∨ (c = ∞ ∧ d = ∞) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp [sub_eq_zero]

/-- `crossRatioSphere a b c d` equals `1` precisely when `a ≠ d`, `b ≠ c`, neither `(a, b)` nor
`(c, d)` is `(∞, ∞)`, and either `a = b` or `c = d`. -/
@[simp]
theorem crossRatioSphere_eq_one_iff (a b c d : OnePoint K) :
    crossRatioSphere a b c d = 1 ↔
      a ≠ d ∧ b ≠ c ∧ ¬(a = ∞ ∧ b = ∞) ∧ ¬(c = ∞ ∧ d = ∞) ∧ (a = b ∨ c = d) := by
  have hdiv₁ (x y z : K) : (x - y) / (x - z) = 1 ↔ x ≠ z ∧ z = y := by
    by_cases hxz : x = z
    · simp [hxz]
    · rw [div_eq_one_iff_eq (sub_ne_zero.mpr hxz)]
      exact ⟨fun h ↦ ⟨hxz, (sub_right_inj.mp h).symm⟩, fun ⟨_, hzy⟩ ↦ by rw [hzy]⟩
  have hdiv₂ (x y z : K) : (x - z) / (y - z) = 1 ↔ y ≠ z ∧ x = y := by
    by_cases hyz : y = z
    · simp [hyz]
    · rw [div_eq_one_iff_eq (sub_ne_zero.mpr hyz)]
      exact ⟨fun h ↦ ⟨hyz, sub_left_inj.mp h⟩, fun ⟨_, hxy⟩ ↦ by rw [hxy]⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    first
    | (simp [hdiv₁, hdiv₂]; done)
    | simp [hdiv₁, hdiv₂, eq_comm]

/-- `crossRatioSphere a b c d` is nonzero whenever `a ≠ c`, `b ≠ d`, `a ≠ d`, `b ≠ c`, and neither
`(a, b)` nor `(c, d)` is `(∞, ∞)`. -/
theorem crossRatioSphere_ne_zero {a b c d : OnePoint K} (hac : a ≠ c) (hbd : b ≠ d)
    (had : a ≠ d) (hbc : b ≠ c) (hab : ¬(a = ∞ ∧ b = ∞)) (hcd : ¬(c = ∞ ∧ d = ∞)) :
    crossRatioSphere a b c d ≠ 0 := by
  simp [hac, hbd, had, hbc, hab, hcd]

/-- On four pairwise distinct points of `OnePoint K`, `crossRatioSphere` is nonzero. -/
theorem crossRatioSphere_ne_zero_of_injective {s : Fin 4 → OnePoint K} (hs : Injective s) :
    crossRatioSphere (s 0) (s 1) (s 2) (s 3) ≠ 0 :=
  crossRatioSphere_ne_zero (hs.ne (by decide)) (hs.ne (by decide)) (hs.ne (by decide))
    (hs.ne (by decide))
    (fun ⟨h0, h1⟩ ↦ hs.ne (by decide : (0 : Fin 4) ≠ 1) (h0.trans h1.symm))
    (fun ⟨h2, h3⟩ ↦ hs.ne (by decide : (2 : Fin 4) ≠ 3) (h2.trans h3.symm))

/-- `crossRatioSphere a b c d` is not equal to `1` whenever `a ≠ b` and `c ≠ d`. -/
theorem crossRatioSphere_ne_one {a b c d : OnePoint K} (hab : a ≠ b) (hcd : c ≠ d) :
    crossRatioSphere a b c d ≠ 1 := by
  simp [hab, hcd]

/-- On four pairwise distinct points of `OnePoint K`, `crossRatioSphere` is not equal to `1`. -/
theorem crossRatioSphere_ne_one_of_injective {s : Fin 4 → OnePoint K} (hs : Injective s) :
    crossRatioSphere (s 0) (s 1) (s 2) (s 3) ≠ 1 :=
  crossRatioSphere_ne_one (hs.ne (by decide)) (hs.ne (by decide))

/-- Exchanging the middle two entries replaces `crossRatioSphere` by `1 - r` whenever `a ≠ d`,
`b ≠ c`, and at most one of `a, b, c, d` equals `∞` (so the Goncharov–Rudenko bracket
`1 - r(a, b, c, d)` equals `r(a, c, b, d)`). -/
theorem crossRatioSphere_swap_second_third {a b c d : OnePoint K} (had : a ≠ d) (hbc : b ≠ c)
    (hab : ¬(a = ∞ ∧ b = ∞)) (hac : ¬(a = ∞ ∧ c = ∞)) (hbd : ¬(b = ∞ ∧ d = ∞))
    (hcd : ¬(c = ∞ ∧ d = ∞)) :
    crossRatioSphere a c b d = 1 - crossRatioSphere a b c d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    first
    | exact TauCeti.crossRatio_swap_second_third (by simpa using had) (by simpa using hbc)
    | (simp only [crossRatioSphere_coe_infty_coe_coe, crossRatioSphere_coe_coe_infty_coe]
       rw [one_sub_div (sub_ne_zero.mpr (by simpa using had))]
       congr 1; ring)
    | (simp only [crossRatioSphere_infty_coe_coe_coe, crossRatioSphere_coe_coe_coe_infty]
       rw [one_sub_div (sub_ne_zero.mpr (by simpa using hbc)), ← neg_div_neg_eq]
       exact congr_arg₂ (· / ·) (by ring) (by ring))
    | simp_all

/-- Exchanging the middle two entries of an injective quadruple replaces `crossRatioSphere` by
`1 - r`. -/
theorem crossRatioSphere_swap_second_third_of_injective {s : Fin 4 → OnePoint K}
    (hs : Injective s) :
    crossRatioSphere (s 0) (s 2) (s 1) (s 3) = 1 - crossRatioSphere (s 0) (s 1) (s 2) (s 3) :=
  crossRatioSphere_swap_second_third (hs.ne (by decide)) (hs.ne (by decide))
    (fun ⟨h0, h1⟩ ↦ hs.ne (by decide : (0 : Fin 4) ≠ 1) (h0.trans h1.symm))
    (fun ⟨h0, h2⟩ ↦ hs.ne (by decide : (0 : Fin 4) ≠ 2) (h0.trans h2.symm))
    (fun ⟨h1, h3⟩ ↦ hs.ne (by decide : (1 : Fin 4) ≠ 3) (h1.trans h3.symm))
    (fun ⟨h2, h3⟩ ↦ hs.ne (by decide : (2 : Fin 4) ≠ 3) (h2.trans h3.symm))

/-- Exchanging the first and fourth entries replaces `crossRatioSphere` by `1 - r` whenever
`a ≠ d`, `b ≠ c`, and at most one of `a, b, c, d` equals `∞`. -/
theorem crossRatioSphere_swap_first_fourth {a b c d : OnePoint K} (had : a ≠ d) (hbc : b ≠ c)
    (hab : ¬(a = ∞ ∧ b = ∞)) (hac : ¬(a = ∞ ∧ c = ∞)) (hbd : ¬(b = ∞ ∧ d = ∞))
    (hcd : ¬(c = ∞ ∧ d = ∞)) :
    crossRatioSphere d b c a = 1 - crossRatioSphere a b c d := by
  rw [← crossRatioSphere_reverse, crossRatioSphere_swap_second_third had hbc hab hac hbd hcd]

/-- Exchanging the first and fourth entries of an injective quadruple replaces `crossRatioSphere`
by `1 - r`. -/
theorem crossRatioSphere_swap_first_fourth_of_injective {s : Fin 4 → OnePoint K}
    (hs : Injective s) :
    crossRatioSphere (s 3) (s 1) (s 2) (s 0) = 1 - crossRatioSphere (s 0) (s 1) (s 2) (s 3) := by
  rw [← crossRatioSphere_reverse, crossRatioSphere_swap_second_third_of_injective hs]

/-- Exchanging the first and third entries sends `r = crossRatioSphere a b c d` to `r / (r - 1)`
whenever `a ≠ d` and `b ≠ c` (including at numerator-zero and multi-infinity tuples). -/
theorem crossRatioSphere_swap_first_third {a b c d : OnePoint K} (had : a ≠ d) (hbc : b ≠ c) :
    crossRatioSphere c b a d =
      crossRatioSphere a b c d / (crossRatioSphere a b c d - 1) := by
  have hdiv (u v : K) (hv : v ≠ 0) : (u / v) / (u / v - 1) = u / (u - v) := by
    rcases eq_or_ne u v with rfl | huv
    · simp [hv]
    · field_simp [hv, sub_ne_zero.mpr huv]
  cases a <;> cases b <;> cases c <;> cases d <;>
    first
    | exact TauCeti.crossRatio_swap_first_third (by simpa using had) (by simpa using hbc)
    | (simp only [crossRatioSphere_infty_coe_coe_coe, crossRatioSphere_coe_coe_infty_coe]
       rw [hdiv _ _ (sub_ne_zero.mpr (by simpa using had))]
       exact congr_arg₂ (· / ·) rfl (by ring))
    | (simp only [crossRatioSphere_coe_infty_coe_coe]
       rw [hdiv _ _ (sub_ne_zero.mpr (by simpa using had)), ← neg_div_neg_eq]
       exact congr_arg₂ (· / ·) (by ring) (by ring))
    | (simp only [crossRatioSphere_infty_coe_coe_coe, crossRatioSphere_coe_coe_infty_coe]
       rw [hdiv _ _ (sub_ne_zero.mpr (by simpa using hbc))]
       exact congr_arg₂ (· / ·) rfl (by ring))
    | (simp only [crossRatioSphere_coe_coe_coe_infty]
       rw [hdiv _ _ (sub_ne_zero.mpr (by simpa using hbc)), ← neg_div_neg_eq]
       exact congr_arg₂ (· / ·) (by ring) (by ring))
    | simp

/-- Exchanging the first and third entries of an injective quadruple sends
`r = crossRatioSphere (s 0) (s 1) (s 2) (s 3)` to `r / (r - 1)`. -/
theorem crossRatioSphere_swap_first_third_of_injective {s : Fin 4 → OnePoint K}
    (hs : Injective s) :
    crossRatioSphere (s 2) (s 1) (s 0) (s 3) =
      crossRatioSphere (s 0) (s 1) (s 2) (s 3) /
        (crossRatioSphere (s 0) (s 1) (s 2) (s 3) - 1) :=
  crossRatioSphere_swap_first_third (hs.ne (by decide)) (hs.ne (by decide))

/-- Exchanging the second and fourth entries sends `r = crossRatioSphere a b c d` to
`r / (r - 1)` whenever `a ≠ d` and `b ≠ c`. -/
theorem crossRatioSphere_swap_second_fourth {a b c d : OnePoint K} (had : a ≠ d) (hbc : b ≠ c) :
    crossRatioSphere a d c b =
      crossRatioSphere a b c d / (crossRatioSphere a b c d - 1) := by
  rw [← crossRatioSphere_swap_within_pairs, crossRatioSphere_swap_first_third hbc had,
    crossRatioSphere_swap_within_pairs]

/-- Exchanging the second and fourth entries of an injective quadruple sends
`r = crossRatioSphere (s 0) (s 1) (s 2) (s 3)` to `r / (r - 1)`. -/
theorem crossRatioSphere_swap_second_fourth_of_injective {s : Fin 4 → OnePoint K}
    (hs : Injective s) :
    crossRatioSphere (s 0) (s 3) (s 2) (s 1) =
      crossRatioSphere (s 0) (s 1) (s 2) (s 3) /
        (crossRatioSphere (s 0) (s 1) (s 2) (s 3) - 1) :=
  crossRatioSphere_swap_second_fourth (hs.ne (by decide)) (hs.ne (by decide))

/-- **Defining normalization of `crossRatioSphere`**: `crossRatioSphere ∞ 0 1 z = z`. -/
theorem crossRatioSphere_infty_zero_one_coe (z : K) :
    crossRatioSphere ∞ ((0 : K) : OnePoint K) ((1 : K) : OnePoint K) z = z := by
  simp

/-- On `(0, ∞, 1, z)`, `crossRatioSphere` evaluates to `z⁻¹`. -/
theorem crossRatioSphere_zero_infty_one_coe (z : K) :
    crossRatioSphere ((0 : K) : OnePoint K) ∞ ((1 : K) : OnePoint K) z = z⁻¹ := by
  simp

/-- On `(∞, 1, 0, z)`, `crossRatioSphere` evaluates to `1 - z`, so the bracket
`1 - crossRatioSphere` satisfies `[∞, 1, 0, z] = z`. -/
theorem crossRatioSphere_infty_one_zero_coe (z : K) :
    crossRatioSphere ∞ ((1 : K) : OnePoint K) ((0 : K) : OnePoint K) z = 1 - z := by
  simp

end Basic

/-! ### Homogeneous determinants, Möbius invariance, and five-point normalization -/

section Projective

/-! `[DecidableEq K]` is part of the statements in this section because Mathlib's
`OnePoint.equivProjectivization` and `OnePoint.instGLAction` carry `[DecidableEq K]` in their type
signatures. -/

variable {K : Type*} [Field K] [DecidableEq K]

/-- **Homogeneous determinant formula for `crossRatioSphere`.** Whenever `(p₀, p₁)` are not both
`∞` and `(p₂, p₃)` are not both `∞`, for any nonzero homogeneous representatives `v₀, v₁, v₂, v₃`
of `p₀, p₁, p₂, p₃` under `OnePoint.equivProjectivization K`, `crossRatioSphere p₀ p₁ p₂ p₃` equals
`det ![v₀, v₂] * det ![v₁, v₃] / (det ![v₀, v₃] * det ![v₁, v₂])`, independent of independent
rescalings of the four representatives. -/
theorem crossRatioSphere_eq_det_div {p₀ p₁ p₂ p₃ : OnePoint K} (h01 : ¬(p₀ = ∞ ∧ p₁ = ∞))
    (h23 : ¬(p₂ = ∞ ∧ p₃ = ∞)) {v₀ v₁ v₂ v₃ : Fin 2 → K} (hv₀ : v₀ ≠ 0) (hv₁ : v₁ ≠ 0)
    (hv₂ : v₂ ≠ 0) (hv₃ : v₃ ≠ 0)
    (hp₀ : Projectivization.mk K v₀ hv₀ = equivProjectivization K p₀)
    (hp₁ : Projectivization.mk K v₁ hv₁ = equivProjectivization K p₁)
    (hp₂ : Projectivization.mk K v₂ hv₂ = equivProjectivization K p₂)
    (hp₃ : Projectivization.mk K v₃ hv₃ = equivProjectivization K p₃) :
    crossRatioSphere p₀ p₁ p₂ p₃ =
      (Matrix.of ![v₀, v₂]).det * (Matrix.of ![v₁, v₃]).det /
        ((Matrix.of ![v₀, v₃]).det * (Matrix.of ![v₁, v₂]).det) := by
  let u (p : OnePoint K) : Fin 2 → K := p.elim ![1, 0] fun t ↦ ![t, 1]
  have hu (p : OnePoint K) : u p ≠ 0 := by cases p <;> simp [u]
  have hmk (p : OnePoint K) : equivProjectivization K p = Projectivization.mk K (u p) (hu p) := by
    cases p <;> simp [u]
  obtain ⟨a₀, rfl⟩ :=
    (Projectivization.mk_eq_mk_iff K v₀ (u p₀) hv₀ (hu p₀)).mp (hp₀.trans (hmk p₀))
  obtain ⟨a₁, rfl⟩ :=
    (Projectivization.mk_eq_mk_iff K v₁ (u p₁) hv₁ (hu p₁)).mp (hp₁.trans (hmk p₁))
  obtain ⟨a₂, rfl⟩ :=
    (Projectivization.mk_eq_mk_iff K v₂ (u p₂) hv₂ (hu p₂)).mp (hp₂.trans (hmk p₂))
  obtain ⟨a₃, rfl⟩ :=
    (Projectivization.mk_eq_mk_iff K v₃ (u p₃) hv₃ (hu p₃)).mp (hp₃.trans (hmk p₃))
  have hscale (a b : Kˣ) (v w : Fin 2 → K) :
      (Matrix.of ![a • v, b • w]).det = (a : K) * (b : K) * (Matrix.of ![v, w]).det := by
    simp [Matrix.det_fin_two, Units.smul_def]
    ring
  have hunit : ((a₀ : K) * a₁ * a₂ * a₃) ≠ 0 := by simp
  rw [hscale, hscale, hscale, hscale]
  have hnum : (a₀ : K) * a₂ * (Matrix.of ![u p₀, u p₂]).det *
      ((a₁ : K) * a₃ * (Matrix.of ![u p₁, u p₃]).det) =
      ((a₀ : K) * a₁ * a₂ * a₃) *
        ((Matrix.of ![u p₀, u p₂]).det * (Matrix.of ![u p₁, u p₃]).det) := by ring
  have hden : (a₀ : K) * a₃ * (Matrix.of ![u p₀, u p₃]).det *
      ((a₁ : K) * a₂ * (Matrix.of ![u p₁, u p₂]).det) =
      ((a₀ : K) * a₁ * a₂ * a₃) *
        ((Matrix.of ![u p₀, u p₃]).det * (Matrix.of ![u p₁, u p₂]).det) := by ring
  rw [hnum, hden, mul_div_mul_left _ _ hunit]
  cases p₀ <;> cases p₁ <;> cases p₂ <;> cases p₃ <;>
    simp_all [u, TauCeti.crossRatio_def, Matrix.det_fin_two, -neg_sub]

/-- Homogeneous determinant formula for `crossRatioSphere` on an injective quadruple. -/
theorem crossRatioSphere_eq_det_div_of_injective {s : Fin 4 → OnePoint K} (hs : Injective s)
    {v : Fin 4 → Fin 2 → K} (hv : ∀ i, v i ≠ 0)
    (hrep : ∀ i, Projectivization.mk K (v i) (hv i) = equivProjectivization K (s i)) :
    crossRatioSphere (s 0) (s 1) (s 2) (s 3) =
      (Matrix.of ![v 0, v 2]).det * (Matrix.of ![v 1, v 3]).det /
        ((Matrix.of ![v 0, v 3]).det * (Matrix.of ![v 1, v 2]).det) :=
  crossRatioSphere_eq_det_div
    (fun ⟨h0, h1⟩ ↦ hs.ne (by decide : (0 : Fin 4) ≠ 1) (h0.trans h1.symm))
    (fun ⟨h2, h3⟩ ↦ hs.ne (by decide : (2 : Fin 4) ≠ 3) (h2.trans h3.symm))
    (hv 0) (hv 1) (hv 2) (hv 3) (hrep 0) (hrep 1) (hrep 2) (hrep 3)

/-- **Homogeneous bracket comparison.** Whenever `p₀ ≠ p₃`, `p₁ ≠ p₂`, and at most one of
`p₀, p₁, p₂, p₃` is `∞`, for any nonzero homogeneous representatives `vᵢ`, the determinant
quotient `det ![v₀, v₁] * det ![v₂, v₃] / (det ![v₀, v₃] * det ![v₂, v₁])` equals
`1 - crossRatioSphere p₀ p₁ p₂ p₃`. -/
theorem one_sub_crossRatioSphere_eq_det_div {p₀ p₁ p₂ p₃ : OnePoint K} (h03 : p₀ ≠ p₃)
    (h12 : p₁ ≠ p₂) (h01 : ¬(p₀ = ∞ ∧ p₁ = ∞)) (h02 : ¬(p₀ = ∞ ∧ p₂ = ∞))
    (h13 : ¬(p₁ = ∞ ∧ p₃ = ∞)) (h23 : ¬(p₂ = ∞ ∧ p₃ = ∞)) {v₀ v₁ v₂ v₃ : Fin 2 → K}
    (hv₀ : v₀ ≠ 0) (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hv₃ : v₃ ≠ 0)
    (hp₀ : Projectivization.mk K v₀ hv₀ = equivProjectivization K p₀)
    (hp₁ : Projectivization.mk K v₁ hv₁ = equivProjectivization K p₁)
    (hp₂ : Projectivization.mk K v₂ hv₂ = equivProjectivization K p₂)
    (hp₃ : Projectivization.mk K v₃ hv₃ = equivProjectivization K p₃) :
    1 - crossRatioSphere p₀ p₁ p₂ p₃ =
      (Matrix.of ![v₀, v₁]).det * (Matrix.of ![v₂, v₃]).det /
        ((Matrix.of ![v₀, v₃]).det * (Matrix.of ![v₂, v₁]).det) := by
  rw [← crossRatioSphere_swap_second_third h03 h12 h01 h02 h13 h23]
  exact crossRatioSphere_eq_det_div h02 h13 hv₀ hv₂ hv₁ hv₃ hp₀ hp₂ hp₁ hp₃

/-- Homogeneous bracket comparison for `1 - crossRatioSphere` on an injective quadruple. -/
theorem one_sub_crossRatioSphere_eq_det_div_of_injective {s : Fin 4 → OnePoint K}
    (hs : Injective s) {v : Fin 4 → Fin 2 → K} (hv : ∀ i, v i ≠ 0)
    (hrep : ∀ i, Projectivization.mk K (v i) (hv i) = equivProjectivization K (s i)) :
    1 - crossRatioSphere (s 0) (s 1) (s 2) (s 3) =
      (Matrix.of ![v 0, v 1]).det * (Matrix.of ![v 2, v 3]).det /
        ((Matrix.of ![v 0, v 3]).det * (Matrix.of ![v 2, v 1]).det) :=
  one_sub_crossRatioSphere_eq_det_div (hs.ne (by decide)) (hs.ne (by decide))
    (fun ⟨h0, h1⟩ ↦ hs.ne (by decide : (0 : Fin 4) ≠ 1) (h0.trans h1.symm))
    (fun ⟨h0, h2⟩ ↦ hs.ne (by decide : (0 : Fin 4) ≠ 2) (h0.trans h2.symm))
    (fun ⟨h1, h3⟩ ↦ hs.ne (by decide : (1 : Fin 4) ≠ 3) (h1.trans h3.symm))
    (fun ⟨h2, h3⟩ ↦ hs.ne (by decide : (2 : Fin 4) ≠ 3) (h2.trans h3.symm))
    (hv 0) (hv 1) (hv 2) (hv 3) (hrep 0) (hrep 1) (hrep 2) (hrep 3)

/-- **Möbius invariance of `crossRatioSphere` under `GL (Fin 2) K`.** Every invertible `2 × 2`
matrix preserves `crossRatioSphere a b c d` whenever `a ≠ b` and `c ≠ d`. -/
@[simp]
theorem crossRatioSphere_gl_smul (g : GL (Fin 2) K) {a b c d : OnePoint K} (hab : a ≠ b)
    (hcd : c ≠ d) :
    crossRatioSphere (g • a) (g • b) (g • c) (g • d) = crossRatioSphere a b c d := by
  let u (p : OnePoint K) : Fin 2 → K := (equivProjectivization K p).rep
  have hu (p : OnePoint K) : u p ≠ 0 := (equivProjectivization K p).rep_ne_zero
  have hgu (p : OnePoint K) : g • u p ≠ 0 := (smul_ne_zero_iff_ne g).mpr (hu p)
  have hmk (p : OnePoint K) : Projectivization.mk K (u p) (hu p) = equivProjectivization K p :=
    (equivProjectivization K p).mk_rep
  have hgmk (p : OnePoint K) :
      Projectivization.mk K (g • u p) (hgu p) = equivProjectivization K (g • p) := by
    rw [equivProjectivization_smul, ← hmk p, Projectivization.smul_mk]
  have h01 : ¬(a = ∞ ∧ b = ∞) := fun ⟨ha, hb⟩ ↦ hab (ha.trans hb.symm)
  have h23 : ¬(c = ∞ ∧ d = ∞) := fun ⟨hc, hd⟩ ↦ hcd (hc.trans hd.symm)
  have hg01 : ¬(g • a = ∞ ∧ g • b = ∞) :=
    fun ⟨ha, hb⟩ ↦ (MulAction.injective g).ne hab (ha.trans hb.symm)
  have hg23 : ¬(g • c = ∞ ∧ g • d = ∞) :=
    fun ⟨hc, hd⟩ ↦ (MulAction.injective g).ne hcd (hc.trans hd.symm)
  rw [crossRatioSphere_eq_det_div hg01 hg23 (hgu a) (hgu b) (hgu c) (hgu d)
      (hgmk a) (hgmk b) (hgmk c) (hgmk d),
    crossRatioSphere_eq_det_div h01 h23 (hu a) (hu b) (hu c) (hu d)
      (hmk a) (hmk b) (hmk c) (hmk d)]
  have hcov (v w : Fin 2 → K) :
      (Matrix.of ![g • v, g • w]).det =
        (g : Matrix (Fin 2) (Fin 2) K).det * (Matrix.of ![v, w]).det := by
    simp [Matrix.det_fin_two]
    ring
  rw [hcov, hcov, hcov, hcov]
  have hdet2 : (g : Matrix (Fin 2) (Fin 2) K).det * (g : Matrix (Fin 2) (Fin 2) K).det ≠ 0 :=
    mul_ne_zero g.det_ne_zero g.det_ne_zero
  have hnum : (g : Matrix (Fin 2) (Fin 2) K).det * (Matrix.of ![u a, u c]).det *
      ((g : Matrix (Fin 2) (Fin 2) K).det * (Matrix.of ![u b, u d]).det) =
      ((g : Matrix (Fin 2) (Fin 2) K).det * (g : Matrix (Fin 2) (Fin 2) K).det) *
        ((Matrix.of ![u a, u c]).det * (Matrix.of ![u b, u d]).det) := by ring
  have hden : (g : Matrix (Fin 2) (Fin 2) K).det * (Matrix.of ![u a, u d]).det *
      ((g : Matrix (Fin 2) (Fin 2) K).det * (Matrix.of ![u b, u c]).det) =
      ((g : Matrix (Fin 2) (Fin 2) K).det * (g : Matrix (Fin 2) (Fin 2) K).det) *
        ((Matrix.of ![u a, u d]).det * (Matrix.of ![u b, u c]).det) := by ring
  rw [hnum, hden, mul_div_mul_left _ _ hdet2]

/-- Möbius invariance of `crossRatioSphere` on an injective quadruple under `GL (Fin 2) K`. -/
theorem crossRatioSphere_gl_smul_of_injective (g : GL (Fin 2) K) {s : Fin 4 → OnePoint K}
    (hs : Injective s) :
    crossRatioSphere (g • s 0) (g • s 1) (g • s 2) (g • s 3) =
      crossRatioSphere (s 0) (s 1) (s 2) (s 3) :=
  crossRatioSphere_gl_smul g (hs.ne (by decide)) (hs.ne (by decide))

/-- Möbius invariance of `crossRatioSphere` under `PGL(2, K)` whenever `a ≠ b` and `c ≠ d`. -/
@[simp]
theorem crossRatioSphere_pgl_smul (g : PGL(2, K)) {a b c d : OnePoint K} (hab : a ≠ b)
    (hcd : c ≠ d) :
    crossRatioSphere (g • a) (g • b) (g • c) (g • d) = crossRatioSphere a b c d := by
  obtain ⟨h, rfl⟩ := ProjGenLinGroup.mk_surjective g
  simpa using crossRatioSphere_gl_smul h hab hcd

/-- Möbius invariance of `crossRatioSphere` under `PSL(2, K)` whenever `a ≠ b` and `c ≠ d`. -/
@[simp]
theorem crossRatioSphere_psl_smul (g : PSL(2, K)) {a b c d : OnePoint K} (hab : a ≠ b)
    (hcd : c ≠ d) :
    crossRatioSphere (g • a) (g • b) (g • c) (g • d) = crossRatioSphere a b c d := by
  simpa [ProjectiveSpecialLinearGroup.toPGL_smul] using
    crossRatioSphere_pgl_smul (ProjectiveSpecialLinearGroup.toPGL g) hab hcd

/-- **Comparison with `OnePoint.crossRatio`.** When `a, b, c` are pairwise distinct, `a ≠ d`, and
`c, d` are not both `∞`, coercing `crossRatioSphere a b c d` to `OnePoint K` agrees with
`OnePoint.crossRatio b c a d`. -/
theorem coe_crossRatioSphere_eq_crossRatio {a b c d : OnePoint K} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (had : a ≠ d) (hcd : ¬(c = ∞ ∧ d = ∞)) :
    ↑(crossRatioSphere a b c d) = OnePoint.crossRatio b c a d := by
  by_cases hcd' : c = d
  · subst hcd'
    have hc : c ≠ ∞ := fun h ↦ hcd ⟨h, h⟩
    have hab' : ¬(a = ∞ ∧ b = ∞) := fun ⟨ha, hb⟩ ↦ hab (ha.trans hb.symm)
    rw [crossRatioSphere_self_third_fourth hc hac hbc hab',
      OnePoint.crossRatio_fourth_eq_second hbc hab.symm hac.symm]
  · obtain ⟨g, hb, hc, ha⟩ := exists_pgl_smul_eq_zero_one_infty hbc hab.symm hac.symm
    have hgd : g • d ≠ ∞ := by
      rw [← ha]
      exact (MulAction.injective g).ne had.symm
    obtain ⟨z, hz⟩ : ∃ z : K, g • d = z := by
      cases h : g • d with
      | infty => exact (hgd h).elim
      | coe z => exact ⟨z, rfl⟩
    rw [OnePoint.crossRatio_eq_smul d hb hc ha, ← crossRatioSphere_pgl_smul g hab hcd',
      ha, hb, hc, hz, crossRatioSphere_infty_zero_one_coe]

/-- On an injective quadruple, `↑(crossRatioSphere (s 0) (s 1) (s 2) (s 3))` equals
`OnePoint.crossRatio (s 1) (s 2) (s 0) (s 3)`. -/
theorem coe_crossRatioSphere_eq_crossRatio_of_injective {s : Fin 4 → OnePoint K}
    (hs : Injective s) :
    ↑(crossRatioSphere (s 0) (s 1) (s 2) (s 3)) =
      OnePoint.crossRatio (s 1) (s 2) (s 0) (s 3) :=
  coe_crossRatioSphere_eq_crossRatio (hs.ne (by decide)) (hs.ne (by decide))
    (hs.ne (by decide)) (hs.ne (by decide))
    (fun ⟨h2, h3⟩ ↦ hs.ne (by decide : (2 : Fin 4) ≠ 3) (h2.trans h3.symm))

/-- **Normalization of five distinct points on `OnePoint K` with explicit cross-ratio coordinates.**
Every injective five-tuple `s : Fin 5 → OnePoint K` is carried by an element of `GL (Fin 2) K` to
`![∞, 0, 1, x, y]`, where `x = crossRatioSphere (s 0) (s 1) (s 2) (s 3)` and
`y = crossRatioSphere (s 0) (s 1) (s 2) (s 4)`. -/
theorem exists_gl_smul_eq_infty_zero_one_crossRatioSphere {s : Fin 5 → OnePoint K}
    (hs : Injective s) :
    ∃ g : GL (Fin 2) K,
      g • s = ![∞, (0 : K), (1 : K),
        ↑(crossRatioSphere (s 0) (s 1) (s 2) (s 3)),
        ↑(crossRatioSphere (s 0) (s 1) (s 2) (s 4))] := by
  obtain ⟨h, h1', h2', h0'⟩ := exists_smul_zero_one_infty_eq
    (hs.ne (by decide : (1 : Fin 5) ≠ 2))
    (hs.ne (by decide : (1 : Fin 5) ≠ 0))
    (hs.ne (by decide : (2 : Fin 5) ≠ 0))
  let g : GL (Fin 2) K := h⁻¹
  have h0 : g • s 0 = ∞ := by rw [← h0', inv_smul_smul]
  have h1 : g • s 1 = (0 : K) := by rw [← h1', inv_smul_smul]
  have h2 : g • s 2 = (1 : K) := by rw [← h2', inv_smul_smul]
  have hfin (j : Fin 5) (hj0 : j ≠ 0) (hj2 : j ≠ 2) :
      g • s j = ↑(crossRatioSphere (s 0) (s 1) (s 2) (s j)) := by
    rw [coe_crossRatioSphere_eq_crossRatio (hs.ne (by decide)) (hs.ne (by decide))
        (hs.ne (by decide)) (hs.ne hj0.symm)
        (fun ⟨h2j, hjj⟩ ↦ hs.ne hj2.symm (h2j.trans hjj.symm)),
      OnePoint.crossRatio_eq_gl_smul (s j) h1 h2 h0]
  refine ⟨g, funext fun i ↦ ?_⟩
  fin_cases i <;>
    simp [Pi.smul_apply, h0, h1, h2, hfin 3 (by decide) (by decide),
      hfin 4 (by decide) (by decide)]

/-- Projective `PGL(2, K)` form of `exists_gl_smul_eq_infty_zero_one_crossRatioSphere`: every
injective five-tuple `s : Fin 5 → OnePoint K` is carried by `PGL(2, K)` to `![∞, 0, 1, x, y]` with
`x = crossRatioSphere (s 0) (s 1) (s 2) (s 3)` and
`y = crossRatioSphere (s 0) (s 1) (s 2) (s 4)`. -/
theorem exists_pgl_smul_eq_infty_zero_one_crossRatioSphere {s : Fin 5 → OnePoint K}
    (hs : Injective s) :
    ∃ g : PGL(2, K),
      g • s = ![∞, (0 : K), (1 : K),
        ↑(crossRatioSphere (s 0) (s 1) (s 2) (s 3)),
        ↑(crossRatioSphere (s 0) (s 1) (s 2) (s 4))] := by
  obtain ⟨g, hg⟩ := exists_gl_smul_eq_infty_zero_one_crossRatioSphere hs
  exact ⟨ProjGenLinGroup.mk g, funext fun i ↦ by simpa [Pi.smul_apply] using congrFun hg i⟩

/-- **Normalization of five distinct points on `OnePoint K`.** For every injective
`s : Fin 5 → OnePoint K` there exist `g : GL (Fin 2) K` and `x, y : K` with `x ≠ 0`, `x ≠ 1`,
`y ≠ 0`, `y ≠ 1`, `x ≠ y`, and `g • s = ![∞, 0, 1, x, y]`. -/
theorem exists_gl_smul_eq_infty_zero_one_coe_coe {s : Fin 5 → OnePoint K} (hs : Injective s) :
    ∃ (g : GL (Fin 2) K) (x y : K),
      x ≠ 0 ∧ x ≠ 1 ∧ y ≠ 0 ∧ y ≠ 1 ∧ x ≠ y ∧
        g • s = ![∞, (0 : K), (1 : K), (x : K), (y : K)] := by
  obtain ⟨g, hg⟩ := exists_gl_smul_eq_infty_zero_one_crossRatioSphere hs
  have hgs : Injective (g • s) := (MulAction.injective g).comp hs
  rw [hg] at hgs
  refine ⟨g, crossRatioSphere (s 0) (s 1) (s 2) (s 3),
    crossRatioSphere (s 0) (s 1) (s 2) (s 4), ?_, ?_, ?_, ?_, ?_, hg⟩
  · exact fun h ↦ hgs.ne (by decide : (3 : Fin 5) ≠ 1) (by simp [h])
  · exact fun h ↦ hgs.ne (by decide : (3 : Fin 5) ≠ 2) (by simp [h])
  · exact fun h ↦ hgs.ne (by decide : (4 : Fin 5) ≠ 1) (by simp [h])
  · exact fun h ↦ hgs.ne (by decide : (4 : Fin 5) ≠ 2) (by simp [h])
  · exact fun h ↦ hgs.ne (by decide : (3 : Fin 5) ≠ 4) (by simp [h])

end Projective

/-! ### Five-point coordinates and cyclic brackets -/

section FivePoint

variable {K : Type*} [Field K]

/-- On the normalized five-tuple `![∞, 0, 1, x, y]`, omitting `∞` gives
`crossRatioSphere 0 1 x y = ((1 - x⁻¹) / (1 - y⁻¹))⁻¹` for all nonzero `x` and `y`. -/
theorem crossRatioSphere_zero_one_coe_coe {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    crossRatioSphere ((0 : K) : OnePoint K) ((1 : K) : OnePoint K) x y =
      ((1 - x⁻¹) / (1 - y⁻¹))⁻¹ := by
  rw [crossRatioSphere_coe, TauCeti.crossRatio_def, inv_div]
  rcases eq_or_ne x 1 with rfl | hx1
  · simp
  rcases eq_or_ne y 1 with rfl | hy1
  · simp
  field_simp [hx, hy, sub_ne_zero.mpr hx1, sub_ne_zero.mpr hx1.symm,
    sub_ne_zero.mpr hy1, sub_ne_zero.mpr hy1.symm]
  ring

/-- On the normalized five-tuple `![∞, 0, 1, x, y]`, omitting `0` gives
`crossRatioSphere ∞ 1 x y = ((1 - x) / (1 - y))⁻¹` for all `x, y : K`. -/
theorem crossRatioSphere_infty_one_coe_coe (x y : K) :
    crossRatioSphere ∞ ((1 : K) : OnePoint K) x y = ((1 - x) / (1 - y))⁻¹ := by
  rw [crossRatioSphere_infty_coe_coe_coe, inv_div]

/-- On the normalized five-tuple `![∞, 0, 1, x, y]`, omitting `1` gives
`crossRatioSphere ∞ 0 x y = y / x` for all `x, y : K`. -/
theorem crossRatioSphere_infty_zero_coe_coe (x y : K) :
    crossRatioSphere ∞ ((0 : K) : OnePoint K) x y = y / x := by
  simp [neg_div_neg_eq]

/-- **Cyclic five-bracket algebraic relation** (Goncharov–Rudenko). For five pairwise distinct
points `s : Fin 5 → OnePoint K` and the cyclic brackets
`b j = 1 - crossRatioSphere (s j) (s (j + 1)) (s (j + 2)) (s (j + 3))`, every index `i : Fin 5`
satisfies `1 - b i = -b i / (b (i + 2) * b (i + 3))`. -/
theorem crossRatioSphere_cyclic_five_bracket {s : Fin 5 → OnePoint K} (hs : Injective s)
    (i : Fin 5) :
    let b (j : Fin 5) : K := 1 - crossRatioSphere (s j) (s (j + 1)) (s (j + 2)) (s (j + 3))
    1 - b i = -b i / (b (i + 2) * b (i + 3)) := by
  classical
  dsimp only
  -- Reindex `s` by translating `i` to `0`, then normalize the shifted tuple to `![∞, 0, 1, x, y]`.
  let t : Fin 5 → OnePoint K := fun j ↦ s (i + j)
  have ht : Injective t := hs.comp (add_right_injective i)
  obtain ⟨g, x, y, hx0, hx1, _, _, hxy, hgt⟩ := exists_gl_smul_eq_infty_zero_one_coe_coe ht
  have hcr (j : Fin 5) :
      crossRatioSphere (s (i + j)) (s (i + j + 1)) (s (i + j + 2)) (s (i + j + 3)) =
        crossRatioSphere ((g • t) j) ((g • t) (j + 1)) ((g • t) (j + 2)) ((g • t) (j + 3)) := by
    simp only [t, add_assoc, Pi.smul_apply]
    exact (crossRatioSphere_gl_smul g
      (hs.ne fun h ↦ by simpa using add_left_cancel h)
      (hs.ne fun h ↦ by simpa using add_left_cancel h)).symm
  have hb0 : crossRatioSphere (s i) (s (i + 1)) (s (i + 2)) (s (i + 3)) = x := by
    simpa using (hcr 0).trans (by rw [hgt]; simp)
  have hb2 : crossRatioSphere (s (i + 2)) (s (i + 2 + 1)) (s (i + 2 + 2)) (s (i + 2 + 3)) =
      (1 - y) / (x - y) := by
    rw [hcr 2, hgt]
    simp [Fin.add_def]
  have hb3 : crossRatioSphere (s (i + 3)) (s (i + 3 + 1)) (s (i + 3 + 2)) (s (i + 3 + 3)) =
      y / x := by
    rw [hcr 3, hgt]
    simp [Fin.add_def]
  have hb2' :
      1 - crossRatioSphere (s (i + 2)) (s (i + 2 + 1)) (s (i + 2 + 2)) (s (i + 2 + 3)) =
        (x - 1) / (x - y) := by
    rw [hb2, one_sub_div (sub_ne_zero.mpr hxy)]
    ring
  have hb3' :
      1 - crossRatioSphere (s (i + 3)) (s (i + 3 + 1)) (s (i + 3 + 2)) (s (i + 3 + 3)) =
        (x - y) / x := by
    rw [hb3, one_sub_div hx0]
  rw [hb0, hb2', hb3']
  field_simp [hx0, sub_ne_zero.mpr hx1, sub_ne_zero.mpr hxy]
  ring

end FivePoint

/-! ### Checks and sharpness witnesses -/

section Checks

-- Paired cancellation check over `ℚ`: `r(∞, 0, 1, 3) = 3` and `r(0, ∞, 1, 3) = 1 / 3`.
example :
    crossRatioSphere ∞ ((0 : ℚ) : OnePoint ℚ) ((1 : ℚ) : OnePoint ℚ) ((3 : ℚ) : OnePoint ℚ) = 3 ∧
    crossRatioSphere ((0 : ℚ) : OnePoint ℚ) ∞ ((1 : ℚ) : OnePoint ℚ) ((3 : ℚ) : OnePoint ℚ) =
      1 / 3 := by
  simp

-- Rescaled homogeneous representatives `(2, 0), (0, 3), (5, 5), (21, 7)` of `(∞, 0, 1, 3)`
-- evaluate to `3`.
example :
    (Matrix.of ![![2, (0 : ℚ)], ![5, 5]]).det *
      (Matrix.of ![![0, (3 : ℚ)], ![21, 7]]).det /
      ((Matrix.of ![![2, (0 : ℚ)], ![21, 7]]).det *
        (Matrix.of ![![0, (3 : ℚ)], ![5, 5]]).det) =
      crossRatioSphere ∞ ((0 : ℚ) : OnePoint ℚ) ((1 : ℚ) : OnePoint ℚ) ((3 : ℚ) : OnePoint ℚ) := by
  simp [Matrix.det_fin_two]
  norm_num

-- Coordinate swap `!![0, 1; 1, 0]` sends `(∞, 0, 1, z)` to `(0, ∞, 1, z⁻¹)` and fails to preserve
-- `crossRatioSphere` on `(0, 0, 1, 2)` (`0 ≠ 1`), witnessing sharpness of `a ≠ b`.
example :
    let g : GL (Fin 2) ℚ :=
      GeneralLinearGroup.mkOfDetNeZero !![(0 : ℚ), 1; 1, 0] (by simp [det_fin_two_of])
    crossRatioSphere (g • ((0 : ℚ) : OnePoint ℚ)) (g • ((0 : ℚ) : OnePoint ℚ))
      (g • ((1 : ℚ) : OnePoint ℚ)) (g • ((2 : ℚ) : OnePoint ℚ)) ≠
      crossRatioSphere ((0 : ℚ) : OnePoint ℚ) ((0 : ℚ) : OnePoint ℚ)
        ((1 : ℚ) : OnePoint ℚ) ((2 : ℚ) : OnePoint ℚ) := by
  intro g
  have hg0 : g • ((0 : ℚ) : OnePoint ℚ) = ∞ := by simp [g]
  rw [hg0, crossRatioSphere_infty_infty, crossRatioSphere_coe,
    TauCeti.crossRatio_self_first_second (by norm_num) (by norm_num)]
  norm_num

-- Sharpness of `a ≠ d` in the bracket relation: on `(0, 1, 2, 0)`, `1 - r = 1 ≠ 0`.
example :
    crossRatioSphere ((0 : ℚ) : OnePoint ℚ) ((2 : ℚ) : OnePoint ℚ)
      ((1 : ℚ) : OnePoint ℚ) ((0 : ℚ) : OnePoint ℚ) ≠
      1 - crossRatioSphere ((0 : ℚ) : OnePoint ℚ) ((1 : ℚ) : OnePoint ℚ)
        ((2 : ℚ) : OnePoint ℚ) ((0 : ℚ) : OnePoint ℚ) := by
  simp

end Checks

end OnePoint
