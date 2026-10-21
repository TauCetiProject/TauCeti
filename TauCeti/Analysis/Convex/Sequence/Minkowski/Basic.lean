/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Tropical.BigOperators
public import Mathlib.RingTheory.PowerSeries.Basic
public import TauCeti.Analysis.Convex.Sequence.Face

/-!
# Minkowski sums of height sequences

The Minkowski sum of two one-sided height sequences is their min-convolution
`minkowskiSum h g n = min_{i + j = n} (h i + g j)`. For convex sequences it is the height
function of the Minkowski sum of the two polygons. This is the geometric operation that
describes Newton polygons of products of polynomials and power series.

Under tropicalisation `trop : WithTop ℝ → MinTropical (WithTop ℝ)`, min-convolution is the
Cauchy product of power series over the tropical semiring. This identifies the algebraic laws
(symmetry, associativity, the singleton at `(0, 0)` as identity and the empty polygon as
absorbing element) with those of multiplication of power series.

## Main results

* `mk_trop_minkowskiSum`: tropicalisation turns `minkowskiSum` into multiplication of
  power series over `MinTropical (WithTop ℝ)`.
* `minkowskiSum_comm`, `minkowskiSum_assoc`, `minkowskiSum_ite_eq_zero`, `minkowskiSum_top`:
  the algebraic laws; `minkowskiSum_ite_eq` describes the sum with a single point, which
  translates the other sequence.
* `ordConnected_minkowskiSum`: order-connected finite domains have an order-connected sum.
* `minkowskiSum_add_eq_of_forall_lt`, `minkowskiSum_add_eq_of_forall_gt`: first points add,
  and so do last points when both finite domains are bounded above.
* `IsConvexSeq.minkowskiSum`: the Minkowski sum of convex height sequences is convex.
* `supportingValue_minkowskiSum`, `supportingValue_minkowskiSum_of_ne_bot`: supporting values add
  in `EReal` for nonempty sequences, or when neither supporting value is `⊥`.
* `minkowskiSum_add_eq_add_iff`: a split `n = i + j` of convex sequences is minimising exactly
  when `i` and `j` lie on supporting faces of `h` and `g` with a common slope.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §3.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1, Proposition 1.
-/

public section

open Finset MinTropical

namespace TauCeti

/-- The Minkowski sum of two height sequences, given by the min-convolution
`n ↦ min_{i + j = n} (h i + g j)`. A split with an infinite height contributes `⊤`. -/
noncomputable def minkowskiSum (h g : ℕ → WithTop ℝ) (n : ℕ) : WithTop ℝ :=
  (antidiagonal n).inf fun p => h p.1 + g p.2

variable {h g h' g' : ℕ → WithTop ℝ}

/-- The Minkowski sum is the infimum over the antidiagonal of sums of heights. -/
theorem minkowskiSum_def (h g : ℕ → WithTop ℝ) (n : ℕ) :
    minkowskiSum h g n = (antidiagonal n).inf fun p => h p.1 + g p.2 := (rfl)

/-- Every split of an index bounds the Minkowski sum from above. -/
theorem minkowskiSum_add_le (h g : ℕ → WithTop ℝ) (i j : ℕ) :
    minkowskiSum h g (i + j) ≤ h i + g j :=
  Finset.inf_le (f := fun p : ℕ × ℕ => h p.1 + g p.2) (b := (i, j)) (mem_antidiagonal.mpr rfl)

/-- Every split `n = i + j` bounds the Minkowski sum at `n` from above. -/
theorem minkowskiSum_le_add_of_add_eq {i j n : ℕ} (hij : i + j = n) :
    minkowskiSum h g n ≤ h i + g j :=
  hij ▸ minkowskiSum_add_le h g i j

/-- A lower bound for the Minkowski sum is a lower bound for every split. -/
theorem le_minkowskiSum_iff {n : ℕ} {r : WithTop ℝ} :
    r ≤ minkowskiSum h g n ↔ ∀ i j, i + j = n → r ≤ h i + g j := by
  simp [minkowskiSum, Finset.le_inf_iff]

/-- The Minkowski sum is attained by some split. -/
theorem exists_minkowskiSum_eq (h g : ℕ → WithTop ℝ) (n : ℕ) :
    ∃ i j, i + j = n ∧ minkowskiSum h g n = h i + g j := by
  obtain ⟨p, hp, he⟩ := exists_mem_eq_inf (antidiagonal n) ⟨(0, n), by simp⟩
    fun p : ℕ × ℕ => h p.1 + g p.2
  exact ⟨p.1, p.2, mem_antidiagonal.mp hp, he⟩

/-- The Minkowski sum is finite exactly at sums of finite indices. -/
theorem minkowskiSum_ne_top_iff {n : ℕ} :
    minkowskiSum h g n ≠ ⊤ ↔ ∃ i j, i + j = n ∧ h i ≠ ⊤ ∧ g j ≠ ⊤ := by
  simp [minkowskiSum, Finset.inf_eq_top_iff]

/-- The Minkowski sum is infinite exactly when every split meets an infinite height. -/
theorem minkowskiSum_eq_top_iff {n : ℕ} :
    minkowskiSum h g n = ⊤ ↔ ∀ i j, i + j = n → h i = ⊤ ∨ g j = ⊤ := by
  simp [minkowskiSum, Finset.inf_eq_top_iff]

/-- The Minkowski sum is monotone in both height sequences. -/
@[gcongr]
theorem minkowskiSum_mono (hh : h ≤ h') (hg : g ≤ g') :
    minkowskiSum h g ≤ minkowskiSum h' g' := fun _ =>
  Finset.inf_mono_fun fun p _ => add_le_add (hh p.1) (hg p.2)

/-! ### Tropicalisation and the algebraic laws -/

/-- Tropicalisation turns the Minkowski sum of height sequences into the product of the
corresponding power series over the tropical semiring `MinTropical (WithTop ℝ)`. -/
theorem mk_trop_minkowskiSum (h g : ℕ → WithTop ℝ) :
    PowerSeries.mk (fun n => trop (minkowskiSum h g n)) =
      PowerSeries.mk (fun n => trop (h n)) * PowerSeries.mk (fun n => trop (g n)) := by
  ext n
  simp [PowerSeries.coeff_mul, minkowskiSum, Finset.trop_inf, trop_add]

/-- Height sequences are determined by their tropicalised power series. -/
private theorem eq_of_mk_trop_eq {a b : ℕ → WithTop ℝ}
    (hab : PowerSeries.mk (fun n => trop (a n)) = PowerSeries.mk (fun n => trop (b n))) :
    a = b :=
  funext fun n => by simpa using congr_arg (PowerSeries.coeff n) hab

/-- The Minkowski sum is symmetric. -/
theorem minkowskiSum_comm (h g : ℕ → WithTop ℝ) : minkowskiSum h g = minkowskiSum g h :=
  eq_of_mk_trop_eq <| by rw [mk_trop_minkowskiSum, mk_trop_minkowskiSum, mul_comm]

/-- The Minkowski sum is associative. -/
theorem minkowskiSum_assoc (h g k : ℕ → WithTop ℝ) :
    minkowskiSum (minkowskiSum h g) k = minkowskiSum h (minkowskiSum g k) :=
  eq_of_mk_trop_eq <| by simp only [mk_trop_minkowskiSum, mul_assoc]

/-- Adding a single point at `(k, c)` shifts the indices by `k` and the heights by `c`. -/
theorem minkowskiSum_ite_eq (h : ℕ → WithTop ℝ) (k : ℕ) (c : WithTop ℝ) (n : ℕ) :
    minkowskiSum h (fun m => if m = k then c else ⊤) n =
      if k ≤ n then h (n - k) + c else ⊤ := by
  split_ifs with hkn
  · refine le_antisymm ?_ (le_minkowskiSum_iff.mpr fun i j hij => ?_)
    · simpa [Nat.sub_add_cancel hkn] using minkowskiSum_add_le h (fun m => if m = k then c else ⊤)
        (n - k) k
    · by_cases hj : j = k
      · subst hj
        simp [← hij]
      · simp [hj]
  · refine minkowskiSum_eq_top_iff.mpr fun i j hij => .inr ?_
    simp only [ite_eq_right_iff]
    omega

/-- The singleton at `(0, 0)` is an identity for the Minkowski sum. -/
@[simp]
theorem minkowskiSum_ite_eq_zero (h : ℕ → WithTop ℝ) :
    minkowskiSum h (fun m => if m = 0 then 0 else ⊤) = h := by
  funext n
  simp [minkowskiSum_ite_eq]

/-- The singleton at `(0, 0)` is an identity for the Minkowski sum. -/
@[simp]
theorem ite_eq_zero_minkowskiSum (h : ℕ → WithTop ℝ) :
    minkowskiSum (fun m => if m = 0 then 0 else ⊤) h = h := by
  rw [minkowskiSum_comm, minkowskiSum_ite_eq_zero]

/-- The empty polygon is absorbing for the Minkowski sum. -/
@[simp]
theorem minkowskiSum_top (h : ℕ → WithTop ℝ) : minkowskiSum h ⊤ = ⊤ := by
  funext n
  exact minkowskiSum_eq_top_iff.mpr fun _ _ _ => .inr rfl

/-- The empty polygon is absorbing for the Minkowski sum. -/
@[simp]
theorem top_minkowskiSum (g : ℕ → WithTop ℝ) : minkowskiSum ⊤ g = ⊤ := by
  rw [minkowskiSum_comm, minkowskiSum_top]

/-! ### First and last points -/

section Endpoints

variable {i j n : ℕ}

/-- Before the sum of the first finite indices, the Minkowski sum is infinite. -/
theorem minkowskiSum_eq_top_of_lt_add (hi : ∀ k < i, h k = ⊤) (hj : ∀ k < j, g k = ⊤)
    (hn : n < i + j) : minkowskiSum h g n = ⊤ :=
  minkowskiSum_eq_top_iff.mpr fun p q hpq => by
    by_cases hp : p < i
    · exact .inl (hi p hp)
    · exact .inr (hj q (by omega))

/-- First points add: if `h` and `g` are infinite before `i` and `j`, the Minkowski sum
at `i + j` is `h i + g j`. -/
theorem minkowskiSum_add_eq_of_forall_lt (hi : ∀ k < i, h k = ⊤) (hj : ∀ k < j, g k = ⊤) :
    minkowskiSum h g (i + j) = h i + g j := by
  refine le_antisymm (minkowskiSum_add_le h g i j) (le_minkowskiSum_iff.mpr fun p q hpq => ?_)
  rcases lt_trichotomy p i with hp | rfl | hp
  · simp [hi p hp]
  · obtain rfl : q = j := by omega
    exact le_rfl
  · simp [hj q (by omega)]

/-- After the sum of the last finite indices, the Minkowski sum is infinite. -/
theorem minkowskiSum_eq_top_of_add_lt (hi : ∀ k, i < k → h k = ⊤)
    (hj : ∀ k, j < k → g k = ⊤) (hn : i + j < n) : minkowskiSum h g n = ⊤ :=
  minkowskiSum_eq_top_iff.mpr fun p q hpq => by
    by_cases hp : i < p
    · exact .inl (hi p hp)
    · exact .inr (hj q (by omega))

/-- Last points add: if `h` and `g` are infinite after `i` and `j`, the Minkowski sum
at `i + j` is `h i + g j`. -/
theorem minkowskiSum_add_eq_of_forall_gt (hi : ∀ k, i < k → h k = ⊤)
    (hj : ∀ k, j < k → g k = ⊤) : minkowskiSum h g (i + j) = h i + g j := by
  refine le_antisymm (minkowskiSum_add_le h g i j) (le_minkowskiSum_iff.mpr fun p q hpq => ?_)
  rcases lt_trichotomy i p with hp | rfl | hp
  · simp [hi p hp]
  · obtain rfl : q = j := by omega
    exact le_rfl
  · simp [hj q (by omega)]

end Endpoints

/-! ### Convexity -/

/-- The finite domain of a Minkowski sum of sequences with order-connected finite domains
is order connected. -/
theorem ordConnected_minkowskiSum (hh : {n | h n ≠ ⊤}.OrdConnected)
    (hg : {n | g n ≠ ⊤}.OrdConnected) : {n | minkowskiSum h g n ≠ ⊤}.OrdConnected := by
  refine ⟨fun n hn k hk t ht => ?_⟩
  obtain ⟨i, j, rfl, hi, hj⟩ := minkowskiSum_ne_top_iff.mp hn
  obtain ⟨i', j', rfl, hi', hj'⟩ := minkowskiSum_ne_top_iff.mp hk
  obtain ⟨htl, htr⟩ := ht
  refine minkowskiSum_ne_top_iff.mpr ?_
  -- Move from the split `(i, j)` to the split `(i', j')` one coordinate at a time.
  rcases le_total i i' with hii' | hii'
  · by_cases hti : t ≤ i' + j
    · exact ⟨t - j, j, by omega, hh.out hi hi' ⟨by omega, by omega⟩, hj⟩
    · exact ⟨i', t - i', by omega, hi', hg.out hj hj' ⟨by omega, by omega⟩⟩
  · by_cases htj : t ≤ i + j'
    · exact ⟨i, t - i, by omega, hi, hg.out hj hj' ⟨by omega, by omega⟩⟩
    · exact ⟨t - j', j', by omega, hh.out hi' hi ⟨by omega, by omega⟩, hj'⟩

/-- The exchange step for the second-difference inequality: if the first coordinate of a split
of `n + 2` exceeds that of a split of `n` by at least two, convexity of `h` moves both splits one
step towards each other. -/
private theorem minkowskiSum_succ_add_succ_le_of_add_two_le (hh : IsConvexSeq h)
    {i j i' j' : ℕ} (hi : i + 2 ≤ i') (hij' : i' + j' = i + j + 2) :
    minkowskiSum h g (i + j + 1) + minkowskiSum h g (i + j + 1) ≤
      (h i + g j) + (h i' + g j') := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hi
  calc _ ≤ (h (i + 1) + g j) + (h (i + t + 1) + g j') :=
        add_le_add (minkowskiSum_le_add_of_add_eq (by omega))
          (minkowskiSum_le_add_of_add_eq (by omega))
    _ = (h (i + 1) + h (i + t + 1)) + (g j + g j') := add_add_add_comm _ _ _ _
    _ ≤ (h i + h (i + t + 2)) + (g j + g j') :=
        add_le_add_left (hh.succ_add_succ_le_add (Nat.le_add_right i t)) _
    _ = _ := by rw [add_add_add_comm, show i + 2 + t = i + t + 2 by omega]

/-- The second-difference inequality for the Minkowski sum of convex sequences, in
`WithTop ℝ`. -/
theorem minkowskiSum_succ_add_succ_le (hh : IsConvexSeq h) (hg : IsConvexSeq g) (n : ℕ) :
    minkowskiSum h g (n + 1) + minkowskiSum h g (n + 1) ≤
      minkowskiSum h g n + minkowskiSum h g (n + 2) := by
  obtain ⟨i, j, rfl, hn⟩ := exists_minkowskiSum_eq h g n
  obtain ⟨i', j', hij', hn'⟩ := exists_minkowskiSum_eq h g (i + j + 2)
  rw [hn, hn']
  -- Either one coordinate of the optimal split moves by at least two, and convexity of that
  -- sequence lets both splits move one step towards each other, or both coordinates move by
  -- one and the two intermediate splits use exactly the same heights.
  by_cases hi : i + 2 ≤ i'
  · exact minkowskiSum_succ_add_succ_le_of_add_two_le hh hi hij'
  by_cases hj : j + 2 ≤ j'
  · have := minkowskiSum_succ_add_succ_le_of_add_two_le hg (g := h) hj
      (show j' + i' = j + i + 2 by omega)
    rwa [minkowskiSum_comm, add_comm j i, add_comm (g j), add_comm (g j')] at this
  obtain ⟨rfl, rfl⟩ : i' = i + 1 ∧ j' = j + 1 := by omega
  calc _ ≤ (h (i + 1) + g j) + (h i + g (j + 1)) :=
        add_le_add (minkowskiSum_le_add_of_add_eq (by omega))
          (minkowskiSum_le_add_of_add_eq (by omega))
    _ = _ := by abel

/-- The Minkowski sum of convex height sequences is convex. -/
theorem IsConvexSeq.minkowskiSum (hh : IsConvexSeq h) (hg : IsConvexSeq g) :
    IsConvexSeq (minkowskiSum h g) := by
  refine isConvexSeq_iff_two_mul_le.mpr
    ⟨ordConnected_minkowskiSum hh.ordConnected hg.ordConnected, fun n hn hn₂ => ?_⟩
  have hle := minkowskiSum_succ_add_succ_le hh hg n
  rw [← WithTop.coe_untop₀_of_ne_top hn, ← WithTop.coe_untop₀_of_ne_top hn₂,
    ← WithTop.coe_add] at hle
  have hn₁ : TauCeti.minkowskiSum h g (n + 1) ≠ ⊤ := fun h₁ => by simp [h₁] at hle
  rw [← WithTop.coe_untop₀_of_ne_top hn₁, ← WithTop.coe_add, WithTop.coe_le_coe] at hle
  linarith

/-! ### Supporting values -/

/-- For nonempty height sequences, the supporting values of their Minkowski sum are the sums
of their supporting values. The nonemptiness hypotheses are needed: if `h = ⊤` and the
supporting value of `g` is `⊥`, the left side is `⊤` while `⊤ + ⊥ = ⊥` in `EReal`. -/
theorem supportingValue_minkowskiSum (hh : h ≠ ⊤) (hg : g ≠ ⊤) (σ : ℝ) :
    supportingValue (minkowskiSum h g) σ = supportingValue h σ + supportingValue g σ := by
  refine le_antisymm (EReal.le_add_of_forall_gt (.inr ?_) (.inl ?_) fun a ha b hb => ?_) ?_
  · simpa using hg
  · simpa using hh
  · obtain ⟨i, hi⟩ := iInf_lt_iff.mp (by rwa [supportingValue_def] at ha)
    obtain ⟨j, hj⟩ := iInf_lt_iff.mp (by rwa [supportingValue_def] at hb)
    calc supportingValue (minkowskiSum h g) σ
        ≤ (minkowskiSum h g (i + j)).toEReal - ((σ * ↑(i + j) : ℝ) : EReal) :=
          supportingValue_le _ σ (i + j)
      _ ≤ (h i + g j).toEReal - ((σ * ↑(i + j) : ℝ) : EReal) :=
          EReal.sub_le_sub (WithTop.toEReal_le_toEReal_iff.mpr (minkowskiSum_add_le h g i j))
            le_rfl
      _ = _ := by rw [Nat.cast_add, mul_add, WithTop.toEReal_add_sub_coe_add]
      _ ≤ a + b := add_le_add hi.le hj.le
  · refine le_supportingValue_iff.mpr fun n => ?_
    obtain ⟨i, j, rfl, hn⟩ := exists_minkowskiSum_eq h g n
    rw [hn, Nat.cast_add, mul_add, WithTop.toEReal_add_sub_coe_add]
    exact add_le_add (supportingValue_le h σ i) (supportingValue_le g σ j)

/-- Supporting values of a Minkowski sum add in `EReal` whenever neither summand has
supporting value `⊥`. Compared with `supportingValue_minkowskiSum`, this allows either sequence
to be empty: then both sides are `⊤`. -/
theorem supportingValue_minkowskiSum_of_ne_bot {σ : ℝ} (hh : supportingValue h σ ≠ ⊥)
    (hg : supportingValue g σ ≠ ⊥) :
    supportingValue (minkowskiSum h g) σ = supportingValue h σ + supportingValue g σ := by
  obtain rfl | hh' := eq_or_ne h ⊤
  · rw [top_minkowskiSum, supportingValue_top, EReal.top_add_of_ne_bot hg]
  obtain rfl | hg' := eq_or_ne g ⊤
  · rw [minkowskiSum_top, supportingValue_top, EReal.add_top_of_ne_bot hh]
  exact supportingValue_minkowskiSum hh' hg' σ

/-! ### Minimising splits -/

/-- A split `n = i + j` at which `h` and `g` touch supporting lines of a common slope
attains the Minkowski sum. -/
theorem minkowskiSum_add_eq_of_mem_supportingFace {σ c d : ℝ} {i j : ℕ}
    (hc : IsSupportingLine h σ c) (hi : i ∈ supportingFace h σ c)
    (hd : IsSupportingLine g σ d) (hj : j ∈ supportingFace g σ d) :
    minkowskiSum h g (i + j) = h i + g j := by
  refine le_antisymm (minkowskiSum_add_le h g i j) (le_minkowskiSum_iff.mpr fun p q hpq => ?_)
  rw [mem_supportingFace] at hi hj
  have hpq' : (p : ℝ) + q = i + j := by exact_mod_cast hpq
  calc h i + g j = (((c + σ * p) + (d + σ * q) : ℝ) : WithTop ℝ) := by
        have hσ : σ * p + σ * q = σ * i + σ * j := by rw [← mul_add, ← mul_add, hpq']
        rw [hi, hj, ← WithTop.coe_add, WithTop.coe_eq_coe]
        linarith
    _ ≤ h p + g q := by
        rw [WithTop.coe_add]
        exact add_le_add (isSupportingLine_iff_forall.mp hc p) (isSupportingLine_iff_forall.mp hd q)

/-- An affine minorant of the Minkowski sum that is tight at a finite split `i + j` restricts
to a supporting line of `h` through `i`. -/
private theorem isSupportingLine_of_affine_minorant_minkowskiSum {e σ : ℝ} {i j : ℕ}
    (hline : ∀ n : ℕ, ((e + σ * n : ℝ) : WithTop ℝ) ≤ minkowskiSum h g n) (hj : g j ≠ ⊤)
    (he : e + σ * ↑(i + j) = (h i).untop₀ + (g j).untop₀) :
    IsSupportingLine h σ ((h i).untop₀ - σ * i) := by
  refine isSupportingLine_iff_forall.mpr fun p => ?_
  by_cases hp : h p = ⊤
  · simp [hp]
  have hle := (hline (p + j)).trans (minkowskiSum_add_le h g p j)
  rw [← WithTop.coe_untop₀_of_ne_top hp, ← WithTop.coe_untop₀_of_ne_top hj,
    ← WithTop.coe_add, WithTop.coe_le_coe] at hle
  rw [← WithTop.coe_untop₀_of_ne_top hp, WithTop.coe_le_coe]
  push_cast at hle he
  linarith

/-- For convex sequences with finite heights at `i` and `j`, the split `i + j` attains the
Minkowski sum exactly when `i` and `j` lie on supporting faces of `h` and `g` of a common
slope. -/
theorem minkowskiSum_add_eq_add_iff (hh : IsConvexSeq h) (hg : IsConvexSeq g) {i j : ℕ}
    (hi : h i ≠ ⊤) (hj : g j ≠ ⊤) :
    minkowskiSum h g (i + j) = h i + g j ↔
      ∃ σ c d : ℝ, IsSupportingLine h σ c ∧ i ∈ supportingFace h σ c ∧
        IsSupportingLine g σ d ∧ j ∈ supportingFace g σ d := by
  refine ⟨fun heq => ?_, fun ⟨σ, c, d, hc, hi', hd, hj'⟩ =>
    minkowskiSum_add_eq_of_mem_supportingFace hc hi' hd hj'⟩
  have hn : minkowskiSum h g (i + j) ≠ ⊤ := by
    rw [heq]
    exact WithTop.add_ne_top.mpr ⟨hi, hj⟩
  -- A supporting line of the Minkowski sum through `i + j` splits into supporting lines of
  -- `h` through `i` and of `g` through `j`.
  obtain ⟨e, σ, hline, he⟩ := (hh.minkowskiSum hg).exists_affine_minorant_eq hn
  rw [heq, ← WithTop.coe_untop₀_of_ne_top hi, ← WithTop.coe_untop₀_of_ne_top hj,
    ← WithTop.coe_add, WithTop.untop₀_coe] at he
  have he' : e + σ * ↑(j + i) = (g j).untop₀ + (h i).untop₀ := by
    push_cast at he ⊢
    linarith
  refine ⟨σ, _, _, isSupportingLine_of_affine_minorant_minkowskiSum hline hj he, ?_,
    isSupportingLine_of_affine_minorant_minkowskiSum (fun n => minkowskiSum_comm h g ▸ hline n)
      hi he', ?_⟩
  · rw [mem_supportingFace, sub_add_cancel, WithTop.coe_untop₀_of_ne_top hi]
  · rw [mem_supportingFace, sub_add_cancel, WithTop.coe_untop₀_of_ne_top hj]

end TauCeti
