/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumericalSemigroup.Apery
public import Mathlib.Data.Nat.Nth
import Mathlib.Tactic.IntervalCases

/-!
# Symmetric numerical semigroups

Write `C` for the conductor of a numerical semigroup `S`, so that `F = C - 1` is its Frobenius
number. The reflection `x ↦ C - 1 - x` of `{0, …, C - 1}` sends every element of `S` below `C`
to a gap, which gives the inequality `C ≤ 2 g` of
`AddSubmonoid.numericalConductor_le_two_mul_numericalGenus`, where `g` is the genus.

`S` is *symmetric* when the reflection also sends every gap into `S`, that is when for every
integer `x ∉ S` (negative integers included) one has `F - x ∈ S`. Symmetric semigroups are
exactly those with `2 g = C`, so their Frobenius number is odd. With respect to any
`0 < n ∈ S`, symmetry is read off the Apéry set `Ap(S, n)`, whose largest element is `C + n - 1`:
`S` is symmetric exactly when `w ↦ C + n - 1 - w` maps `Ap(S, n)` to itself, that is when the
elements `a₀ < a₁ < ⋯ < a_{n - 1}` of `Ap(S, n)` satisfy `a_i + a_{n - 1 - i} = a_{n - 1}`.

## Main definitions

* `AddSubmonoid.IsSymmetricNumericalSemigroup S`: `S` is a numerical semigroup and
  `C - 1 - x ∈ S` for every gap `x`.

## Main results

* `AddSubmonoid.isSymmetricNumericalSemigroup_iff_forall_int`: the symmetry condition stated
  for all integers `x ∉ S`, with the integer-valued Frobenius number.
* `AddSubmonoid.IsNumericalSemigroup.isSymmetricNumericalSemigroup_iff_two_mul_numericalGenus_eq`:
  a numerical semigroup is symmetric if and only if `2 g = F + 1`.
* `AddSubmonoid.IsSymmetricNumericalSemigroup.odd_numericalFrobenius`: a symmetric numerical
  semigroup has odd Frobenius number.
* `AddSubmonoid.IsNumericalSemigroup.isSymmetricNumericalSemigroup_iff_forall_mem_aperySet` and
  `AddSubmonoid.IsNumericalSemigroup.isSymmetricNumericalSemigroup_iff_nth_add_nth`: the
  Apéry-set criterion for symmetry.

## References

* A. Assi and P. A. García-Sánchez, *Numerical semigroups and applications* (2014),
  §2, Proposition 43(i), Corollary 44(i) and Proposition 47.
-/

public section

namespace AddSubmonoid

variable {S : AddSubmonoid ℕ} {n : ℕ}

/-! ### Symmetric numerical semigroups -/

variable (S) in
/-- A numerical semigroup `S` with conductor `C` is **symmetric** if `C - 1 - x ∈ S` for every
gap `x`. Since `C - 1` is the Frobenius number `F`, this says that exactly one of `x` and
`F - x` lies in `S` whenever `0 ≤ x ≤ F`; `isSymmetricNumericalSemigroup_iff_forall_int` states
it as `F - x ∈ S` for every integer `x ∉ S`, the condition of Assi–García-Sánchez. -/
def IsSymmetricNumericalSemigroup : Prop :=
  S.IsNumericalSemigroup ∧ ∀ x ∉ S, S.numericalConductor - 1 - x ∈ S

variable (S) in
/-- The defining condition of a symmetric numerical semigroup. -/
theorem isSymmetricNumericalSemigroup_def :
    S.IsSymmetricNumericalSemigroup ↔
      S.IsNumericalSemigroup ∧ ∀ x ∉ S, S.numericalConductor - 1 - x ∈ S :=
  Iff.rfl

/-- A symmetric numerical semigroup is a numerical semigroup. -/
theorem IsSymmetricNumericalSemigroup.isNumericalSemigroup
    (h : S.IsSymmetricNumericalSemigroup) : S.IsNumericalSemigroup :=
  h.1

/-- In a symmetric numerical semigroup with conductor `C`, the reflection `C - 1 - x` of a gap
`x` lies in the semigroup. -/
theorem IsSymmetricNumericalSemigroup.numericalConductor_sub_one_sub_mem
    (h : S.IsSymmetricNumericalSemigroup) {x : ℕ} (hx : x ∉ S) :
    S.numericalConductor - 1 - x ∈ S :=
  h.2 x hx

/-- `ℕ` is a symmetric numerical semigroup. -/
@[simp]
theorem isSymmetricNumericalSemigroup_top : (⊤ : AddSubmonoid ℕ).IsSymmetricNumericalSemigroup :=
  ⟨isNumericalSemigroup_top, fun x hx ↦ (hx (mem_top x)).elim⟩

/-- A numerical semigroup with conductor `C` is symmetric if and only if, for every `x < C`,
exactly one of `x` and `C - 1 - x` lies in it. -/
theorem IsNumericalSemigroup.isSymmetricNumericalSemigroup_iff_mem_iff_notMem
    (h : S.IsNumericalSemigroup) :
    S.IsSymmetricNumericalSemigroup ↔
      ∀ x < S.numericalConductor, (x ∈ S ↔ S.numericalConductor - 1 - x ∉ S) := by
  refine ⟨fun hS x hx ↦ ⟨fun hmem ↦ numericalConductor_sub_one_sub_notMem hmem hx,
    fun hnot ↦ by_contra fun hxS ↦ hnot (hS.2 x hxS)⟩, fun H ↦ ⟨h, fun x hx ↦ ?_⟩⟩
  have hlt := h.lt_numericalConductor_of_notMem hx
  have := H (S.numericalConductor - 1 - x) (by omega)
  rw [Nat.sub_sub_self (by omega)] at this
  exact this.mpr hx

/-- The symmetry condition of Assi–García-Sánchez: `S` is a symmetric numerical semigroup if and
only if `F(S) - x ∈ S` for every integer `x ∉ S`, where `F(S)` is the integer-valued Frobenius
number. No separate hypothesis that `S` is a numerical semigroup is needed. -/
theorem isSymmetricNumericalSemigroup_iff_forall_int :
    S.IsSymmetricNumericalSemigroup ↔
      ∀ x : ℤ, x ∉ ((↑) : ℕ → ℤ) '' S → S.numericalFrobenius - x ∈ ((↑) : ℕ → ℤ) '' S := by
  have hF := S.numericalFrobenius_add_one
  constructor
  · intro hS x hx
    rcases lt_or_ge x 0 with hneg | hnonneg
    · refine ⟨(S.numericalFrobenius - x).toNat,
        mem_of_numericalConductor_le hS.1 (by omega), by omega⟩
    · lift x to ℕ using hnonneg
      have hxS : x ∉ S := fun hmem ↦ hx ⟨x, hmem, rfl⟩
      have hlt := hS.1.lt_numericalConductor_of_notMem hxS
      exact ⟨_, hS.2 x hxS, by omega⟩
  · intro H
    have hgap {x : ℕ} (hx : x ∉ S) : ∃ m ∈ S, (m : ℤ) = S.numericalFrobenius - x := by
      obtain ⟨m, hm, hmx⟩ := H x fun ⟨y, hy, hyx⟩ ↦ hx (Nat.cast_injective hyx ▸ hy)
      exact ⟨m, hm, hmx⟩
    have hnum : S.IsNumericalSemigroup := by
      by_contra hnum
      obtain ⟨x, hx⟩ := Set.Infinite.nonempty (mt (isNumericalSemigroup_def S).mpr hnum)
      obtain ⟨m, -, hm⟩ := hgap hx
      exact hnum (isNumericalSemigroup_of_numericalConductor_ne_zero (by omega))
    refine ⟨hnum, fun x hx ↦ ?_⟩
    obtain ⟨m, hm, hmx⟩ := hgap hx
    rwa [show S.numericalConductor - 1 - x = m by omega]

/-- **Symmetric semigroups are those of least genus**: a numerical semigroup `S` is symmetric
if and only if `2 g(S) = C(S)`, that is `2 g(S) = F(S) + 1`. -/
theorem IsNumericalSemigroup.isSymmetricNumericalSemigroup_iff_two_mul_numericalGenus_eq
    (h : S.IsNumericalSemigroup) :
    S.IsSymmetricNumericalSemigroup ↔ 2 * S.numericalGenus = S.numericalConductor := by
  have hsum := S.ncard_inter_Iio_add_numericalGenus
  have hle := S.ncard_inter_Iio_le_numericalGenus
  have hfin : ((S : Set ℕ) ∩ Set.Iio S.numericalConductor).Finite :=
    (Set.finite_Iio _).inter_of_right _
  constructor
  · intro hS
    -- The reflection also sends the gaps injectively into `S` below the conductor.
    have : S.numericalGenus ≤ ((S : Set ℕ) ∩ Set.Iio S.numericalConductor).ncard := by
      rw [numericalGenus_def]
      have hgaps : S.numericalGaps ⊆ Set.Iio S.numericalConductor := fun x hx ↦
        h.lt_numericalConductor_of_notMem ((mem_numericalGaps S).mp hx)
      refine Set.ncard_le_ncard_of_injOn (S.numericalConductor - 1 - ·)
        (fun x hx ↦ ⟨hS.2 x ((mem_numericalGaps S).mp hx), Set.mem_Iio.mpr ?_⟩)
        (fun a ha b hb ↦ tsub_inj_right (Nat.le_sub_one_of_lt (hgaps ha))
          (Nat.le_sub_one_of_lt (hgaps hb))) hfin
      have := Set.mem_Iio.mp (hgaps hx)
      omega
    omega
  · intro h2
    -- Equal cardinalities make the reflection a bijection onto the gaps.
    have hinj : Set.InjOn (S.numericalConductor - 1 - ·)
        ((S : Set ℕ) ∩ Set.Iio S.numericalConductor) :=
      fun a ha b hb ↦ tsub_inj_right (Nat.le_sub_one_of_lt ha.2) (Nat.le_sub_one_of_lt hb.2)
    have himage : (S.numericalConductor - 1 - ·) '' ((S : Set ℕ) ∩ Set.Iio S.numericalConductor) =
        S.numericalGaps :=
      Set.eq_of_subset_of_ncard_le
        (Set.image_subset_iff.mpr fun _ hs ↦
          (mem_numericalGaps S).mpr (numericalConductor_sub_one_sub_notMem hs.1 hs.2))
        (by rw [hinj.ncard_image, ← numericalGenus_def]; omega) h.finite_numericalGaps
    refine ⟨h, fun x hx ↦ ?_⟩
    obtain ⟨s, hs, rfl⟩ : x ∈ (S.numericalConductor - 1 - ·) ''
        ((S : Set ℕ) ∩ Set.Iio S.numericalConductor) := himage ▸ (mem_numericalGaps S).mpr hx
    rw [Nat.sub_sub_self (by have := Set.mem_Iio.mp hs.2; omega)]
    exact hs.1

/-- A symmetric numerical semigroup satisfies `2 g(S) = C(S)`, that is `2 g(S) = F(S) + 1`. -/
theorem IsSymmetricNumericalSemigroup.two_mul_numericalGenus_eq
    (h : S.IsSymmetricNumericalSemigroup) : 2 * S.numericalGenus = S.numericalConductor :=
  (h.1.isSymmetricNumericalSemigroup_iff_two_mul_numericalGenus_eq).mp h

/-- The Frobenius number of a symmetric numerical semigroup is odd. This includes `ℕ`, whose
Frobenius number is `-1`. -/
theorem IsSymmetricNumericalSemigroup.odd_numericalFrobenius
    (h : S.IsSymmetricNumericalSemigroup) : Odd S.numericalFrobenius := by
  have h2 := congrArg (Nat.cast : ℕ → ℤ) h.two_mul_numericalGenus_eq
  push_cast at h2
  have hF := S.numericalFrobenius_add_one
  exact ⟨(S.numericalGenus : ℤ) - 1, by omega⟩

/-! ### The Apéry-set criterion -/

/-- **Apéry-set criterion for symmetry**: for a numerical semigroup `S` with conductor `C` and
`0 < n ∈ S`, the semigroup is symmetric if and only if `w ↦ C + n - 1 - w` maps the Apéry set
`Ap(S, n)` to itself. Here `C + n - 1` is the largest element of `Ap(S, n)`. -/
theorem IsNumericalSemigroup.isSymmetricNumericalSemigroup_iff_forall_mem_aperySet
    (h : S.IsNumericalSemigroup) (hn : n ∈ S) (hpos : n ≠ 0) :
    S.IsSymmetricNumericalSemigroup ↔
      ∀ w ∈ S.aperySet n, S.numericalConductor + n - 1 - w ∈ S.aperySet n := by
  have hmax := h.isGreatest_aperySet hpos
  constructor
  · intro hS w hw
    have hwle : w ≤ S.numericalConductor + n - 1 := hmax.2 hw
    have hmem : S.numericalConductor + n - 1 - w ∈ S := by
      by_cases hnw : n ≤ w
      · have := hS.2 _ ((mem_aperySet_iff_sub_notMem.mp hw).2 hnw)
        rwa [show S.numericalConductor - 1 - (w - n) = S.numericalConductor + n - 1 - w by
          omega] at this
      · exact mem_of_numericalConductor_le h (by omega)
    exact mem_aperySet_of_add_mem_aperySet_left hmem (aperySet_subset hw)
      (by rw [Nat.sub_add_cancel hwle]; exact hmax.1)
  · intro H
    refine ⟨h, fun x hx ↦ ?_⟩
    -- Write the gap `x` as `w - (k + 1) n` with `w ∈ Ap(S, n)`.
    obtain ⟨w, hw, hmod⟩ := h.exists_mem_aperySet_modEq hpos x
    have hxw : x < w :=
      lt_of_not_ge fun hle ↦ hx (mem_of_le_of_modEq hn (aperySet_subset hw) hle hmod)
    obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hxw.le).mp hmod.symm
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (n := k) (by rintro rfl; omega)
    have hlt := h.lt_numericalConductor_of_notMem hx
    have hwle : w ≤ S.numericalConductor + n - 1 := hmax.2 hw
    rw [Nat.mul_add_one] at hk
    rw [show S.numericalConductor - 1 - x = S.numericalConductor + n - 1 - w + k • n by
      rw [smul_eq_mul, Nat.mul_comm]; omega]
    exact S.add_mem (aperySet_subset (H w hw)) (S.nsmul_mem hn k)

/-- **Apéry-set criterion for symmetry**, with the elements `a₀ < a₁ < ⋯ < a_{n - 1}` of the
Apéry set `Ap(S, n)` listed in increasing order by `Nat.nth`: for a numerical semigroup `S` and
`0 < n ∈ S`, the semigroup is symmetric if and only if `a_i + a_{n - 1 - i} = a_{n - 1}` for all
`i < n`. -/
theorem IsNumericalSemigroup.isSymmetricNumericalSemigroup_iff_nth_add_nth
    (h : S.IsNumericalSemigroup) (hn : n ∈ S) (hpos : n ≠ 0) :
    S.IsSymmetricNumericalSemigroup ↔
      ∀ i < n, Nat.nth (· ∈ S.aperySet n) i + Nat.nth (· ∈ S.aperySet n) (n - 1 - i) =
        Nat.nth (· ∈ S.aperySet n) (n - 1) := by
  rw [h.isSymmetricNumericalSemigroup_iff_forall_mem_aperySet hn hpos]
  have hmax := h.isGreatest_aperySet hpos
  set M := S.numericalConductor + n - 1
  set p : ℕ → Prop := (· ∈ S.aperySet n)
  have hf : (Set.ofPred p).Finite := AddSubmonoid.finite_aperySet hn
  have hk : hf.toFinset.card = n := by
    rw [← Set.ncard_eq_toFinset_card _ hf]
    exact h.ncard_aperySet hn
  have hmem (i : ℕ) (hi : i < n) : p (Nat.nth p i) := Nat.nth_mem_of_lt_card hf (hk ▸ hi)
  have hle (i : ℕ) (hi : i < n) : Nat.nth p i ≤ M := hmax.2 (hmem i hi)
  have hlast : Nat.nth p (n - 1) = M := by
    refine IsGreatest.unique ⟨hmem _ (by omega), fun w hw ↦ ?_⟩ hmax
    obtain ⟨i, hi, rfl⟩ := Nat.exists_lt_card_finite_nth_eq hf hw
    exact Nat.nth_le_nth_of_lt_card hf (by omega) (by omega)
  rw [hlast]
  constructor
  · intro H i hi
    -- `j ↦ M - a_{n - 1 - j}` is an increasing enumeration of `Ap(S, n)`, so it is `j ↦ a_j`.
    have key := Finset.orderEmbOfFin_unique (s := hf.toFinset) rfl
      (f := fun j ↦ M - Nat.nth p (hf.toFinset.card - 1 - j))
      (fun j ↦ hf.mem_toFinset.mpr (H _ (hmem _ (by omega))))
      (fun j j' hjj' ↦ by
        have hlt := Nat.nth_lt_nth_of_lt_card hf
          (show hf.toFinset.card - 1 - j' < hf.toFinset.card - 1 - j by
            have := j'.isLt
            have : (j : ℕ) < j' := hjj'
            omega)
          (by omega)
        have := hle (hf.toFinset.card - 1 - j) (by omega)
        dsimp only
        omega)
    have hi' := congrFun key ⟨i, by omega⟩
    rw [← Nat.nth_eq_orderEmbOfFin hf] at hi'
    simp only [hk] at hi'
    have := hle (n - 1 - i) (by omega)
    omega
  · intro H w hw
    obtain ⟨i, hi, rfl⟩ := Nat.exists_lt_card_finite_nth_eq hf hw
    rw [hk] at hi
    rw [← H i hi, Nat.add_sub_cancel_left]
    exact hmem _ (by omega)

/-- The semigroup generated by `3` and `5` is symmetric. -/
example : (closure ({3, 5} : Set ℕ)).IsSymmetricNumericalSemigroup := by
  have hf := frobeniusNumber_iff.mp (frobeniusNumber_pair (m := 3) (n := 5)
    (by decide) (by decide) (by decide))
  have hF : (closure ({3, 5} : Set ℕ)).numericalFrobenius = 7 :=
    (numericalFrobenius_eq_natCast_iff _ 7).mpr (by simpa using hf)
  have hC := (closure ({3, 5} : Set ℕ)).numericalFrobenius_add_one
  rw [hF] at hC
  refine ⟨(isNumericalSemigroup_closure_pair_iff 3 5).mpr (by decide), fun x hx ↦ ?_⟩
  rw [show (closure ({3, 5} : Set ℕ)).numericalConductor = 8 by omega]
  have hx7 : x ≤ 7 := not_lt.mp fun h7 ↦ hx (hf.2 x h7)
  simp only [mem_closure_pair, smul_eq_mul, not_exists] at hx ⊢
  interval_cases x
  all_goals first
    | exact ⟨2, 0, rfl⟩
    | exact ⟨0, 1, rfl⟩
    | exact ⟨1, 0, rfl⟩
    | exact ⟨0, 0, rfl⟩
    | exact (hx 0 0 rfl).elim
    | exact (hx 1 0 rfl).elim
    | exact (hx 0 1 rfl).elim
    | exact (hx 2 0 rfl).elim

/-- The semigroup generated by `3`, `4` and `5` has gaps `{1, 2}` and is not symmetric: its
Frobenius number `2` is even. -/
example : ¬ (closure ({3, 4, 5} : Set ℕ)).IsSymmetricNumericalSemigroup := by
  have hT (x : ℕ) (hx : x ∈ closure ({3, 4, 5} : Set ℕ)) : x = 0 ∨ 3 ≤ x := by
    induction hx using closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      omega
    | zero => exact Or.inl rfl
    | add x y _ _ hx hy => omega
  have hmem : ∀ k, 3 ≤ k → k ∈ closure ({3, 4, 5} : Set ℕ) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      by_cases hk6 : k < 6
      · interval_cases k <;> exact subset_closure (by simp)
      · rw [show k = (k - 3) + 3 by omega]
        exact add_mem (ih _ (by omega) (by omega)) (subset_closure (by simp))
  have hF : (closure ({3, 4, 5} : Set ℕ)).numericalFrobenius = 2 := by
    refine (numericalFrobenius_eq_natCast_iff _ 2).mpr ⟨fun h2 ↦ ?_, fun k hk ↦ hmem k hk⟩
    have := hT 2 h2
    omega
  intro hS
  have := hS.odd_numericalFrobenius
  rw [hF] at this
  exact absurd this (by decide)

end AddSubmonoid
