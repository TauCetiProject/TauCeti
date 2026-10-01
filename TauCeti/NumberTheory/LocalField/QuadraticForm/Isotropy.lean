/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.LowRank
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Binary
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Realization
import TauCeti.Algebra.Ring.Int.Units

/-!
# Isotropy of quadratic forms over a local field, rank by rank

Let `K` be a nonarchimedean local field in which `2` is invertible. Whether a regular quadratic
form over `K` is isotropic is decided by its rank `n`, its plain discriminant `d ∈ Kˣ/(Kˣ)²` and
its local Hasse invariant `s = ∏_{i<j} (aᵢ, aⱼ)_K`:

* `n = 1`: never isotropic, and `n = 2`: isotropic exactly when `d = [-1]`; these two hold over
  every field (`TauCeti.RegularFormClass.anisotropic_of_rank_le_one`,
  `TauCeti.RegularFormClass.not_anisotropic_iff_discr_eq_neg_one_of_rank_eq_two`);
* `n = 3`: isotropic exactly when `s = (-1, -d)_K`;
* `n = 4`: isotropic exactly when `d ≠ [1]`, or `d = [1]` and `s = (-1, -1)_K`;
* `n ≥ 5`: always isotropic.

In particular the `u`-invariant of `K` is four: every regular form of rank at least five is
isotropic, and there is an anisotropic form of rank four, namely any form with invariants
`(4, [1], -(-1, -1)_K)`.

The ternary and quaternary criteria reduce to the binary one, which says that a regular binary
form `⟨a, b⟩` represents a unit `c` exactly when `(c, -ab)_K = (a, b)_K`. A ternary form
`⟨a, b, c⟩` is isotropic exactly when `⟨a, b⟩` represents `-c`. A quaternary form
`⟨a, b⟩ ⊥ ⟨c, d⟩` is isotropic exactly when `⟨a, b⟩` and `⟨-c, -d⟩` have a common nonzero value,
which is a question about the two characters `(·, -ab)_K` and `(·, -cd)_K` of `Kˣ`: they are
distinct when `abcd` is a nonsquare, and two distinct nontrivial characters of a group of exponent
two take every pair of values. A form of rank five contains a binary form, whose values fill two
square classes, and a ternary form, which represents every unit outside one square class.

## Main results

* `TauCeti.RegularFormClass.not_anisotropic_iff_localHasse_eq_of_rank_eq_three`: the ternary
  criterion `s = (-1, -d)_K`.
* `TauCeti.RegularFormClass.not_anisotropic_iff_discr_ne_zero_or_localHasse_eq_of_rank_eq_four`:
  the quaternary criterion `d ≠ [1] ∨ s = (-1, -1)_K`.
* `TauCeti.RegularFormClass.not_anisotropic_of_five_le_rank`: every class of rank at least five
  is isotropic.
* `TauCeti.RegularFormClass.exists_rank_eq_four_and_anisotropic`: there is an anisotropic class of
  rank four, so `u(K) = 4`.
* `TauCeti.neg_mem_unitValueSet_presentedForm_three_of_not_isSquare`: a ternary diagonal form
  represents every unit outside one square class.
* `QuadraticForm.not_anisotropic_iff_localHasse_eq_of_finrank_eq_three`,
  `QuadraticForm.not_anisotropic_iff_discr_ne_zero_or_localHasse_eq_of_finrank_eq_four`,
  `QuadraticForm.not_anisotropic_of_five_le_finrank`: the same criteria for regular forms on
  finite-dimensional spaces.
* `QuadraticForm.exists_nondegenerate_and_anisotropic_fin_four`: an anisotropic regular form on
  `Fin 4 → K`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter IV, §2.2, Theorem 6.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §63:17–63:19.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter VI, §2.
-/

public section

open Finset QuadraticMap

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Invertible (2 : K)]

/-! ### Diagonal forms of rank three, four and five -/

/-- **Ternary isotropy** (Serre IV Thm 6 (ii)). A diagonal form `⟨a, b, c⟩` over `K` is
isotropic exactly when its local Hasse invariant `(a, b)(a, c)(b, c)` is `(-1, -abc)_K`. -/
theorem not_anisotropic_presentedForm_three_iff (w : Fin 3 → Kˣ) :
    ¬(presentedForm ⟨3, w⟩).Anisotropic ↔
      hilbertSymbol (w 0) (w 1) * hilbertSymbol (w 0) (w 2) * hilbertSymbol (w 1) (w 2) =
        hilbertSymbol (-1) (-(w 0 * w 1 * w 2)) := by
  have h2 : (2 : K) ≠ 0 := Invertible.ne_zero 2
  -- `⟨w₀, w₁, w₂⟩` is isotropic exactly when `⟨w₁, w₂⟩` represents `-w₀`, that is, when
  -- `(-w₀, -w₁w₂)_K = (w₁, w₂)_K`.
  have htail : presentedForm ⟨2, fun i : Fin 2 => w i.succ⟩ =
      weightedSumSquares K ![(w 1 : K), (w 2 : K)] := presentedForm_two _
  refine (not_anisotropic_presentedForm_succ_iff w).trans ?_
  rw [htail, mem_unitValueSet_binary_iff_hilbertSymbol_eq]
  -- Both products expand to the same seven symbols.
  have key : hilbertSymbol (-w 0) (-(w 1 * w 2)) * hilbertSymbol (w 1) (w 2) =
      hilbertSymbol (w 0) (w 1) * hilbertSymbol (w 0) (w 2) * hilbertSymbol (w 1) (w 2) *
        hilbertSymbol (-1) (-(w 0 * w 1 * w 2)) := by
    rw [neg_eq_neg_one_mul (w 0), neg_eq_neg_one_mul (w 1 * w 2),
      neg_eq_neg_one_mul (w 0 * w 1 * w 2)]
    simp only [hilbertSymbol_mul_left h2, hilbertSymbol_mul_right h2]
    rw [hilbertSymbol_comm (w 0) (-1)]
    simp only [mul_comm, mul_left_comm, mul_assoc]
  exact Int.units_eq_iff_eq_of_mul_eq_mul key

/-- If `abcd` is a nonsquare, the binary forms `⟨a, b⟩` and `⟨c, d⟩` have unit values `x` and
`-x` that are negatives of each other, so that `⟨a, b⟩ ⊥ ⟨c, d⟩` is isotropic. -/
private theorem exists_mem_unitValueSet_binary_and_neg_mem_of_not_isSquare (a b c d : Kˣ)
    (h : ¬IsSquare (a * b * c * d)) :
    ∃ x : Kˣ, x ∈ unitValueSet (weightedSumSquares K ![(a : K), (b : K)]) ∧
      -x ∈ unitValueSet (weightedSumSquares K ![(c : K), (d : K)]) := by
  have h2 : (2 : K) ≠ 0 := Invertible.ne_zero 2
  have hab : hilbertSymbol a (-(a * b)) = hilbertSymbol a b := hilbertSymbol_neg_self_mul h2 a b
  have hcd : hilbertSymbol c (-(c * d)) = hilbertSymbol c d := hilbertSymbol_neg_self_mul h2 c d
  simp only [mem_unitValueSet_binary_iff_hilbertSymbol_eq]
  by_cases hab' : IsSquare (-(a * b))
  · -- `⟨a, b⟩` is a hyperbolic plane and represents every unit, in particular `-c`.
    refine ⟨-c, ?_, ?_⟩
    · rw [hilbertSymbol_eq_one_of_isSquare_right _ hab', ← hab,
        hilbertSymbol_eq_one_of_isSquare_right _ hab']
    · rw [neg_neg, hcd]
  by_cases hcd' : IsSquare (-(c * d))
  · -- `⟨c, d⟩` is a hyperbolic plane and represents every unit, in particular `-a`.
    refine ⟨a, hab, ?_⟩
    rw [hilbertSymbol_eq_one_of_isSquare_right _ hcd', ← hcd,
      hilbertSymbol_eq_one_of_isSquare_right _ hcd']
  -- Otherwise `(·, -ab)_K` and `(·, -cd)_K` are distinct nontrivial characters.
  have hprod : ¬IsSquare (-(a * b) * -(c * d)) := by rwa [neg_mul_neg, ← mul_assoc]
  obtain ⟨x, hx₁, hx₂⟩ := exists_hilbertSymbol_eq_and_hilbertSymbol_eq h2 hab' hcd' hprod
    (hilbertSymbol a b) (hilbertSymbol (-1) (-(c * d)) * hilbertSymbol c d)
  refine ⟨x, hx₁, ?_⟩
  rw [neg_eq_neg_one_mul x, hilbertSymbol_mul_left h2, hx₂, ← mul_assoc, Int.units_mul_self,
    one_mul]

/-- **Quaternary isotropy, nonsquare discriminant** (Serre IV Thm 6 (iii)). A diagonal form
`⟨a, b, c, d⟩` over `K` whose discriminant `abcd` is a nonsquare is isotropic. -/
theorem not_anisotropic_presentedForm_four_of_not_isSquare (w : Fin 4 → Kˣ)
    (h : ¬IsSquare (w 0 * w 1 * w 2 * w 3)) : ¬(presentedForm ⟨4, w⟩).Anisotropic := by
  have hlast : presentedForm ⟨2, fun i => w (Fin.natAdd 2 i)⟩ =
      weightedSumSquares K ![(w 2 : K), (w 3 : K)] := presentedForm_two _
  rw [not_anisotropic_presentedForm_two_add_iff (n := 2) w, hlast]
  exact exists_mem_unitValueSet_binary_and_neg_mem_of_not_isSquare (w 0) (w 1) (w 2) (w 3) h

/-- **Quaternary isotropy, square discriminant** (Serre IV Thm 6 (iii)). A diagonal form
`⟨a, b, c, d⟩` over `K` whose discriminant `abcd` is a square is isotropic exactly when its local
Hasse invariant `∏_{i<j} (aᵢ, aⱼ)_K` is `(-1, -1)_K`. -/
theorem not_anisotropic_presentedForm_four_iff_of_isSquare (w : Fin 4 → Kˣ)
    (h : IsSquare (w 0 * w 1 * w 2 * w 3)) :
    ¬(presentedForm ⟨4, w⟩).Anisotropic ↔
      hilbertSymbol (w 0) (w 1) * hilbertSymbol (w 0) (w 2) * hilbertSymbol (w 0) (w 3) *
        hilbertSymbol (w 1) (w 2) * hilbertSymbol (w 1) (w 3) * hilbertSymbol (w 2) (w 3) =
          hilbertSymbol (-1 : Kˣ) (-1) := by
  have h2 : (2 : K) ≠ 0 := Invertible.ne_zero 2
  have hlast : presentedForm ⟨2, fun i => w (Fin.natAdd 2 i)⟩ =
      weightedSumSquares K ![(w 2 : K), (w 3 : K)] := presentedForm_two _
  have hab : hilbertSymbol (w 0) (-(w 0 * w 1)) = hilbertSymbol (w 0) (w 1) :=
    hilbertSymbol_neg_self_mul h2 (w 0) (w 1)
  -- `⟨w₀, w₁⟩ ⊥ ⟨w₂, w₃⟩` is isotropic exactly when `⟨w₀, w₁⟩` has a unit value `x` with `-x` a
  -- value of `⟨w₂, w₃⟩`. Since `-w₀w₁` and `-w₂w₃` lie in the same square class, the two
  -- characters `(·, -w₀w₁)_K` and `(·, -w₂w₃)_K` agree, and `w₀` itself is a value of
  -- `⟨w₀, w₁⟩`; so the condition is `(-1, -w₀w₁)_K (w₀, w₁)_K = (w₂, w₃)_K`.
  have hcong (x : Kˣ) : hilbertSymbol x (-(w 2 * w 3)) = hilbertSymbol x (-(w 0 * w 1)) :=
    hilbertSymbol_congr_sq x x _ _ ⟨x, rfl⟩
      (by rwa [neg_mul_neg, mul_comm (w 2 * w 3), ← mul_assoc])
  have hneg (x : Kˣ) : hilbertSymbol (-x) (-(w 0 * w 1)) =
      hilbertSymbol (-1) (-(w 0 * w 1)) * hilbertSymbol x (-(w 0 * w 1)) := by
    rw [neg_eq_neg_one_mul x, hilbertSymbol_mul_left h2]
  rw [not_anisotropic_presentedForm_two_add_iff (n := 2) w, hlast]
  simp only [mem_unitValueSet_binary_iff_hilbertSymbol_eq, hcong]
  -- The common value `x` is forced to have `(x, -w₀w₁)_K = (w₀, w₁)_K`, and `w₀` is one such
  -- value, so the existential collapses to the single sign equation.
  have hex : (∃ x : Kˣ, hilbertSymbol x (-(w 0 * w 1)) = hilbertSymbol (w 0) (w 1) ∧
      hilbertSymbol (-x) (-(w 0 * w 1)) = hilbertSymbol (w 2) (w 3)) ↔
      hilbertSymbol (-1) (-(w 0 * w 1)) * hilbertSymbol (w 0) (w 1) =
        hilbertSymbol (w 2) (w 3) := by
    constructor
    · rintro ⟨x, hx₁, hx₂⟩
      rwa [hneg x, hx₁] at hx₂
    · intro h
      exact ⟨w 0, hab, by rw [hneg (w 0), hab, h]⟩
  rw [hex]
  -- The two products expand to the same symbols, once `(w₀w₁, w₂w₃)_K = (-1, w₀w₁)_K` is used.
  have key : hilbertSymbol (-1) (-(w 0 * w 1)) * hilbertSymbol (w 0) (w 1) *
      hilbertSymbol (w 2) (w 3) =
      hilbertSymbol (w 0) (w 1) * hilbertSymbol (w 0) (w 2) * hilbertSymbol (w 0) (w 3) *
        hilbertSymbol (w 1) (w 2) * hilbertSymbol (w 1) (w 3) * hilbertSymbol (w 2) (w 3) *
          hilbertSymbol (-1 : Kˣ) (-1) := by
    have habcd : hilbertSymbol (w 0 * w 1) (w 2 * w 3) = hilbertSymbol (-1 : Kˣ) (w 0 * w 1) := by
      rw [hilbertSymbol_congr_sq (w 0 * w 1) (w 0 * w 1) (w 2 * w 3) (w 0 * w 1) ⟨w 0 * w 1, rfl⟩
        (by rwa [mul_comm (w 2 * w 3), ← mul_assoc]), hilbertSymbol_self, hilbertSymbol_comm]
    rw [neg_eq_neg_one_mul (w 0 * w 1), hilbertSymbol_mul_right h2, ← habcd]
    simp only [hilbertSymbol_mul_left h2, hilbertSymbol_mul_right h2]
    simp only [mul_comm, mul_left_comm, mul_assoc]
  exact Int.units_eq_iff_eq_of_mul_eq_mul key

/-- **Ternary representation.** A diagonal form `⟨a, b, c⟩` over `K` represents `-x` for every
unit `x` such that `xabc` is a nonsquare: a ternary form represents every unit outside one square
class. -/
theorem neg_mem_unitValueSet_presentedForm_three_of_not_isSquare (w : Fin 3 → Kˣ) (x : Kˣ)
    (hx : ¬IsSquare (x * (w 0 * w 1 * w 2))) : -x ∈ unitValueSet (presentedForm ⟨3, w⟩) := by
  -- `⟨x, a, b, c⟩` has nonsquare discriminant, so it is isotropic, so `⟨a, b, c⟩` represents `-x`.
  have h4 := (not_anisotropic_presentedForm_succ_iff ![x, w 0, w 1, w 2]).mp
    (not_anisotropic_presentedForm_four_of_not_isSquare ![x, w 0, w 1, w 2]
      (by simpa [mul_assoc] using hx))
  -- The tail of `⟨x, a, b, c⟩` is `⟨a, b, c⟩`; the rewrite goes through the dependent rank index,
  -- which `simp` cannot do.
  have htail : (fun i : Fin 3 => ![x, w 0, w 1, w 2] i.succ) = w :=
    funext fun i => by fin_cases i <;> rfl
  rw [htail] at h4
  simpa using h4

/-- **Isotropy in rank five** (Serre IV Thm 6 (iv)). Every diagonal form of rank five over `K`
is isotropic. -/
theorem not_anisotropic_presentedForm_five (w : Fin 5 → Kˣ) :
    ¬(presentedForm ⟨5, w⟩).Anisotropic := by
  have h2 : (2 : K) ≠ 0 := Invertible.ne_zero 2
  have hlast : (fun i : Fin 3 => w (Fin.natAdd 2 i)) = ![w 2, w 3, w 4] :=
    funext fun i => by fin_cases i <;> rfl
  -- `⟨w₀, …, w₄⟩` is isotropic as soon as a unit value `x` of `⟨w₀, w₁⟩` has `-x` a value of
  -- `⟨w₂, w₃, w₄⟩`.
  rw [not_anisotropic_presentedForm_two_add_iff (n := 3) w, hlast]
  -- The values `w₀` and `w₀ n` of `⟨w₀, w₁⟩`, with `n` a nonsquare norm from `K(√(-w₀w₁))`, lie
  -- in distinct square classes, so one of them has a nonsquare product with `w₂w₃w₄`.
  have hw0 := mem_unitValueSet_binary_left (w 0) (w 1 : K)
  obtain ⟨n, hn, hn'⟩ := exists_not_isSquare_hilbertSymbol_eq_one h2 (-(w 0 * w 1))
  have hw0n : w 0 * n ∈ unitValueSet (weightedSumSquares K ![(w 0 : K), (w 1 : K)]) := by
    rw [mem_unitValueSet_binary_iff_hilbertSymbol_eq, hilbertSymbol_mul_left h2, hn', mul_one]
    exact (mem_unitValueSet_binary_iff_hilbertSymbol_eq _ _ _).mp hw0
  by_cases hsq : IsSquare (w 0 * (w 2 * w 3 * w 4))
  · refine ⟨_, hw0n,
      neg_mem_unitValueSet_presentedForm_three_of_not_isSquare ![w 2, w 3, w 4] _ fun h => hn ?_⟩
    have hcancel : w 0 * n * (w 2 * w 3 * w 4) * (w 0 * (w 2 * w 3 * w 4))⁻¹ = n := by
      rw [mul_right_comm (w 0) n, mul_comm (w 0 * (w 2 * w 3 * w 4)) n, mul_inv_cancel_right]
    exact hcancel ▸ h.mul hsq.inv
  · exact ⟨_, hw0, neg_mem_unitValueSet_presentedForm_three_of_not_isSquare ![w 2, w 3, w 4] _ hsq⟩

/-- **Isotropy in rank at least five.** Every diagonal form of rank at least five over `K` is
isotropic. -/
theorem not_anisotropic_presentedForm_of_five_le {n : ℕ} (hn : 5 ≤ n) (w : Fin n → Kˣ) :
    ¬(presentedForm ⟨n, w⟩).Anisotropic := by
  induction n, hn using Nat.le_induction with
  | base => exact not_anisotropic_presentedForm_five w
  | succ n _ ih => exact (presentedForm_tail_isRepresentedBy w).not_anisotropic (ih _)

/-! ### The isotropy list on isometry classes -/

namespace RegularFormClass

/-- **Ternary isotropy** (Serre IV Thm 6 (ii)). A regular-form class of rank three over `K` is
isotropic exactly when its local Hasse invariant is `(-1, -d)_K`, where `d` is its
discriminant. -/
theorem not_anisotropic_iff_localHasse_eq_of_rank_eq_three {x : RegularFormClass K}
    (hx : x.rank = 3) :
    ¬x.Anisotropic ↔ localHasse x =
      hilbertSymbolOnSquareClasses (squareClass (-1 : Kˣ)) (squareClass (-1 : Kˣ) + discr x) := by
  induction x using Quotient.inductionOn with
  | h p =>
    obtain ⟨n, w⟩ := p
    rw [rank_mk] at hx
    subst hx
    rw [anisotropic_mk, not_anisotropic_presentedForm_three_iff, localHasse_mk,
      prod_prod_Ioi_three, discr_mk, Fin.prod_univ_three, ← squareClass_mul,
      hilbertSymbolOnSquareClasses_squareClass, neg_one_mul]

/-- **Quaternary isotropy** (Serre IV Thm 6 (iii)). A regular-form class of rank four over `K` is
isotropic exactly when its discriminant is not the class of `1`, or its discriminant is the class
of `1` and its local Hasse invariant is `(-1, -1)_K`. -/
theorem not_anisotropic_iff_discr_ne_zero_or_localHasse_eq_of_rank_eq_four
    {x : RegularFormClass K} (hx : x.rank = 4) :
    ¬x.Anisotropic ↔ discr x ≠ 0 ∨ localHasse x = hilbertSymbol (-1 : Kˣ) (-1) := by
  induction x using Quotient.inductionOn with
  | h p =>
    obtain ⟨n, w⟩ := p
    rw [rank_mk] at hx
    subst hx
    rw [anisotropic_mk, discr_mk, Fin.prod_univ_four, ne_eq, squareClass_eq_zero_iff,
      localHasse_mk, prod_prod_Ioi_four]
    dsimp only
    by_cases h : IsSquare (w 0 * w 1 * w 2 * w 3)
    · rw [not_anisotropic_presentedForm_four_iff_of_isSquare w h]
      simp only [h, not_true_eq_false, false_or]
    · simp only [h, not_false_eq_true, true_or, iff_true]
      exact not_anisotropic_presentedForm_four_of_not_isSquare w h

/-- **Isotropy in rank at least five** (Serre IV Thm 6 (iv)). Every regular-form class of rank at
least five over `K` is isotropic. -/
theorem not_anisotropic_of_five_le_rank {x : RegularFormClass K} (hx : 5 ≤ x.rank) :
    ¬x.Anisotropic := by
  induction x using Quotient.inductionOn with
  | h p =>
    rw [rank_mk] at hx
    rw [anisotropic_mk]
    exact not_anisotropic_presentedForm_of_five_le hx p.2

/-- **`u(K) = 4`** (O'Meara 63:19). There is an anisotropic regular-form class of rank four over
`K`: any class with trivial discriminant and local Hasse invariant `-(-1, -1)_K`. -/
theorem exists_rank_eq_four_and_anisotropic :
    ∃ x : RegularFormClass K, x.rank = 4 ∧ x.Anisotropic := by
  obtain ⟨x, hx, hd, hs⟩ := exists_of_realization (K := K) (n := 4) (by norm_num) 0
    (-hilbertSymbol (-1 : Kˣ) (-1)) (fun h => by omega) (fun h => by omega)
  refine ⟨x, hx, not_not.mp fun h => ?_⟩
  rcases (not_anisotropic_iff_discr_ne_zero_or_localHasse_eq_of_rank_eq_four hx).mp h with
    hd' | hs'
  · exact hd' hd
  · exact Int.units_ne_iff_eq_neg.mpr rfl (hs.symm.trans hs')

end RegularFormClass

end TauCeti

/-! ### The isotropy list on quadratic forms -/

namespace QuadraticForm

open TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **Ternary isotropy** (Serre IV Thm 6 (ii)). A regular quadratic form on a space of dimension
three over `K` is isotropic exactly when its local Hasse invariant is `(-1, -d)_K`, where `d` is
its discriminant. -/
theorem not_anisotropic_iff_localHasse_eq_of_finrank_eq_three (Q : QuadraticForm K V)
    (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) :
    ¬Q.Anisotropic ↔ RegularFormClass.localHasse (formClass Q hQ) =
      hilbertSymbolOnSquareClasses (squareClass (-1 : Kˣ))
        (squareClass (-1 : Kˣ) + RegularFormClass.discr (formClass Q hQ)) := by
  rw [← anisotropic_formClass Q hQ]
  exact RegularFormClass.not_anisotropic_iff_localHasse_eq_of_rank_eq_three
    (by rwa [rank_formClass])

/-- **Quaternary isotropy** (Serre IV Thm 6 (iii)). A regular quadratic form on a space of
dimension four over `K` is isotropic exactly when its discriminant is not the class of `1`, or its
discriminant is the class of `1` and its local Hasse invariant is `(-1, -1)_K`. -/
theorem not_anisotropic_iff_discr_ne_zero_or_localHasse_eq_of_finrank_eq_four
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 4) :
    ¬Q.Anisotropic ↔ RegularFormClass.discr (formClass Q hQ) ≠ 0 ∨
      RegularFormClass.localHasse (formClass Q hQ) = hilbertSymbol (-1 : Kˣ) (-1) := by
  rw [← anisotropic_formClass Q hQ]
  exact RegularFormClass.not_anisotropic_iff_discr_ne_zero_or_localHasse_eq_of_rank_eq_four
    (by rwa [rank_formClass])

/-- **Isotropy in dimension at least five** (Serre IV Thm 6 (iv)). Every regular quadratic form on
a space of dimension at least five over `K` is isotropic. -/
theorem not_anisotropic_of_five_le_finrank (Q : QuadraticForm K V) (hQ : Q.Nondegenerate)
    (hV : 5 ≤ Module.finrank K V) : ¬Q.Anisotropic := by
  rw [← anisotropic_formClass Q hQ]
  exact RegularFormClass.not_anisotropic_of_five_le_rank (by rwa [rank_formClass])

/-- **`u(K) = 4`** (O'Meara 63:19). There is an anisotropic regular quadratic form on the
four-dimensional space `Fin 4 → K`. -/
theorem exists_nondegenerate_and_anisotropic_fin_four :
    ∃ Q : QuadraticForm K (Fin 4 → K), Q.Nondegenerate ∧ Q.Anisotropic := by
  obtain ⟨x, hx, hani⟩ := RegularFormClass.exists_rank_eq_four_and_anisotropic (K := K)
  induction x using Quotient.inductionOn with
  | h p =>
    obtain ⟨n, w⟩ := p
    rw [RegularFormClass.rank_mk] at hx
    subst hx
    exact ⟨presentedForm ⟨4, w⟩, nondegenerate_presentedForm ⟨4, w⟩,
      (RegularFormClass.anisotropic_mk _).mp hani⟩

end QuadraticForm
