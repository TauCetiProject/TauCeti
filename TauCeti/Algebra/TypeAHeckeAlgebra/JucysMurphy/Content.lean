/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.JucysMurphy.Basic
public import TauCeti.Combinatorics.Young.Addable
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.LinearCombination

/-!
# Additive quantum contents

The additive content `[c]_Q` is the Laurent polynomial extending
`(Q ^ c - 1) / (Q - 1)` to `Q = 1`, where its value is the ordinary integer
content `c`. Negative contents use negative powers of `Q`. These are the scalar
values associated with the rescaled Jucys–Murphy elements, in the convention
`g_i = q T_i` and `Q = q²`.

For positive real `Q`, additive contents are strictly increasing in `c`, including
at `Q = 1`. Consequently they separate the addable boxes of each fixed Young
diagram, and the inverse differences used in Lagrange interpolation are continuous
on the entire positive half-line. This supplies the scalar denominators for
continuous path projectors without dividing by `Q - 1`. No tableau eigenvalue
theorem is assumed or asserted here. The one-row and one-column values are
identified with the existing scalar characters of the actual Hecke algebra.

## References

* A. Mathas, *Iwahori–Hecke algebras and Schur algebras of the symmetric group*,
  University Lecture Series 15, AMS (1999), Chapter 3.
-/

public section

namespace TauCeti.TypeAHeckeAlgebra

variable {R : Type*} [Field R]

/-- The additive quantum content `[c]_Q`, defined by finite geometric sums so
that it is regular at `Q = 1`. The parameter must be nonzero when negative
contents are used. -/
def additiveContent (Q : R) : ℤ → R
  | .ofNat n => ∑ i ∈ Finset.range n, Q ^ i
  | .negSucc n => -∑ i ∈ Finset.range (n + 1), (Q⁻¹) ^ (i + 1)

/-- A nonnegative additive content is a geometric sum. -/
theorem additiveContent_natCast (Q : R) (n : ℕ) :
    additiveContent Q (n : ℤ) = ∑ i ∈ Finset.range n, Q ^ i := (rfl)

/-- A negative additive content is a negative geometric sum of inverse powers. -/
theorem additiveContent_neg_natCast (Q : R) (n : ℕ) :
    additiveContent Q (-(n : ℤ)) = -∑ i ∈ Finset.range n, (Q⁻¹) ^ (i + 1) := by
  cases n with
  | zero => simp [additiveContent]
  | succ n => rfl

/-- The content zero has value zero. -/
@[simp]
theorem additiveContent_zero (Q : R) : additiveContent Q 0 = 0 := by
  simp [additiveContent]

/-- At `Q = 1` the additive content is the ordinary integer content. -/
@[simp]
theorem additiveContent_one (c : ℤ) : additiveContent (1 : R) c = c := by
  cases c <;> simp [additiveContent, Int.cast_negSucc]

/-- Consecutive additive contents differ by `Q ^ c`. This identity also holds
at `Q = 1`, unlike a computation using division by `Q - 1`. -/
theorem additiveContent_add_one (Q : R) (c : ℤ) :
    additiveContent Q (c + 1) = additiveContent Q c + Q ^ c := by
  cases c with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast]
    rw [← Int.natCast_add_one]
    simp [additiveContent, Finset.sum_range_succ]
  | negSucc n =>
    cases n with
    | zero => simp [additiveContent]
    | succ n =>
      have hi : Int.negSucc (n + 1) + 1 = Int.negSucc n := by omega
      rw [hi]
      simp only [additiveContent, Finset.sum_range_succ, zpow_negSucc, inv_pow]
      abel

/-- The Laurent-polynomial identity relating additive and multiplicative contents. -/
theorem sub_one_mul_additiveContent {Q : R} (hQ : Q ≠ 0) (c : ℤ) :
    (Q - 1) * additiveContent Q c = Q ^ c - 1 := by
  induction c using Int.induction_on with
  | zero => simp
  | succ c ih =>
    rw [additiveContent_add_one, mul_add, ih, zpow_add₀ hQ]
    simp only [zpow_one]
    ring
  | pred c ih =>
    have hrec := additiveContent_add_one Q (-(c : ℤ) - 1)
    have hpow : Q ^ (-(c : ℤ)) = Q ^ (-(c : ℤ) - 1) * Q := by
      rw [← zpow_add_one₀ hQ, sub_add_cancel]
    rw [sub_add_cancel] at hrec
    rw [hrec, mul_add, hpow] at ih
    linear_combination ih

/-- Away from `Q = 1`, the additive content is the usual quotient. -/
theorem additiveContent_eq_div {Q : R} (hQ : Q ≠ 0) (hQ1 : Q ≠ 1) (c : ℤ) :
    additiveContent Q c = (Q ^ c - 1) / (Q - 1) := by
  apply (eq_div_iff (sub_ne_zero.mpr hQ1)).mpr
  simpa only [mul_comm] using sub_one_mul_additiveContent hQ c

/-- Each additive content varies continuously on the nonzero parameters; in
particular `Q = 1` is not removed from its domain. -/
@[fun_prop]
theorem continuousOn_additiveContent [TopologicalSpace R] [IsTopologicalDivisionRing R]
    (c : ℤ) : ContinuousOn (fun Q : R => additiveContent Q c) {Q | Q ≠ 0} := by
  cases c with
  | ofNat n =>
    exact (continuous_finsetSum _ fun i _ => continuous_id.pow i).continuousOn
  | negSucc n =>
    simp only [additiveContent]
    exact (continuousOn_finsetSum _ fun i _ =>
      (continuousOn_id.inv₀ fun _ h => h).pow (i + 1)).neg

/-- On a positive parameter, additive contents increase strictly with the integer
content. This includes the ordinary symmetric-group parameter `Q = 1`. -/
theorem strictMono_additiveContent [LinearOrder R] [IsStrictOrderedRing R]
    {Q : R} (hQ : 0 < Q) : StrictMono (additiveContent Q) := by
  apply strictMono_int_of_lt_succ
  intro c
  rw [additiveContent_add_one]
  exact lt_add_of_pos_right _ (zpow_pos hQ c)

/-- The positive-real additive content family is continuous through `Q = 1`. -/
@[fun_prop]
theorem continuousOn_additiveContent_pos (c : ℤ) :
    ContinuousOn (fun Q : ℝ => additiveContent Q c) (Set.Ioi 0) :=
  (continuousOn_additiveContent c).mono fun _ h => ne_of_gt h

end TauCeti.TypeAHeckeAlgebra

namespace YoungDiagram

open TauCeti.TypeAHeckeAlgebra

/-- Additive contents separate the addable cells of a fixed diagram at every
positive parameter, including `Q = 1`. No bound on the diagram size is needed. -/
theorem injOn_additiveContent_cellContent (μ : YoungDiagram) {R : Type*} [Field R]
    [LinearOrder R] [IsStrictOrderedRing R] {Q : R} (hQ : 0 < Q) :
    Set.InjOn (fun c => additiveContent Q (cellContent c)) {c | IsAddable μ c} :=
  (strictMono_additiveContent hQ).injective.comp_injOn μ.injOn_cellContent

/-- The inverse content differences appearing in one-box Lagrange interpolation
are continuous across the entire positive-real parameter family, including at `1`. -/
@[fun_prop]
theorem continuousOn_inv_sub_additiveContent_cellContent {μ : YoungDiagram}
    {c d : ℕ × ℕ} (hc : IsAddable μ c) (hd : IsAddable μ d) (hne : c ≠ d) :
    ContinuousOn (fun Q : ℝ =>
      (additiveContent Q (cellContent c) - additiveContent Q (cellContent d))⁻¹)
      (Set.Ioi 0) := by
  refine ((continuousOn_additiveContent_pos _).sub
    (continuousOn_additiveContent_pos _)).inv₀ ?_
  intro Q hQ
  exact sub_ne_zero.mpr fun h =>
    hne (injOn_additiveContent_cellContent μ hQ hc hd h)

end YoungDiagram

namespace TauCeti.InfiniteTypeAHeckeAlgebra

open TypeAHeckeAlgebra

/-- The one-row scalar character evaluates the additive Jucys–Murphy element
at the additive content of its new box. -/
theorem indexCharacter_additiveJucysMurphy_eq_additiveContent {R : Type*} [Field R]
    (q : Rˣ) (k : ℕ) :
    indexCharacter R q (additiveJucysMurphy q k) = additiveContent ((q : R) ^ 2) (k : ℤ) := by
  rw [indexCharacter_additiveJucysMurphy, additiveContent_natCast]

/-- The one-column scalar character evaluates the additive Jucys–Murphy element
at the negative content of its new box. -/
theorem signCharacter_additiveJucysMurphy_eq_additiveContent {R : Type*} [Field R]
    (q : Rˣ) (k : ℕ) :
    signCharacter R q (additiveJucysMurphy q k) =
      additiveContent ((q : R) ^ 2) (-(k : ℤ)) := by
  simp only [signCharacter_additiveJucysMurphy, additiveContent_neg_natCast,
    inv_pow, Units.val_inv_eq_inv_val]

end TauCeti.InfiniteTypeAHeckeAlgebra
