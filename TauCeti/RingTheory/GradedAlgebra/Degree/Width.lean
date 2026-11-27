/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.Algebra.DirectSum.Internal

/-!
# Extremal homogeneous parts and degree width in graded rings

Let `A` be an additive commutative monoid with an internal direct-sum decomposition `𝒜 : ι → σ`
indexed by a linearly ordered type `ι` with `0`. Every nonzero element `x : A` has a nonempty
finite support of homogeneous degrees, giving a least degree `minDeg 𝒜 x`, a greatest degree
`maxDeg 𝒜 x` (both `0` when `x = 0`), and the extremal homogeneous components
`minHomogPart 𝒜 x ∈ 𝒜 (minDeg 𝒜 x)` and `maxHomogPart 𝒜 x ∈ 𝒜 (maxDeg 𝒜 x)`. An element is
homogeneous if and only if its greatest and least degrees coincide
(`exists_mem_iff_maxDeg_eq_minDeg`).

When `A` is a (not necessarily commutative) semiring graded by `𝒜` over a linearly ordered
additive monoid `ι` with strictly monotone addition on both sides, the component of a product
`x * y` (`x ≠ 0`, `y ≠ 0`) in degree `minDeg 𝒜 x + minDeg 𝒜 y` is the single product
`minHomogPart 𝒜 x * minHomogPart 𝒜 y`, and all components of strictly smaller degree vanish; the
symmetric statement holds for `maxDeg` and `maxHomogPart`.

## Main definitions

* `TauCeti.GradedAlgebra.minDeg`, `TauCeti.GradedAlgebra.maxDeg`: the least and greatest degrees in
  the homogeneous support of `x` (`0` when `x = 0`).
* `TauCeti.GradedAlgebra.minHomogPart`, `TauCeti.GradedAlgebra.maxHomogPart`,
  `TauCeti.GradedAlgebra.minHomogPartHom`, `TauCeti.GradedAlgebra.maxHomogPartHom`: the extremal
  homogeneous components and, in the absence of zero divisors, the bundled `MonoidWithZeroHom`s
  `A →*₀ A`.
* `TauCeti.GradedAlgebra.degWidth`: for an ordered commutative additive group `ι`, the degree width
  `maxDeg 𝒜 x - minDeg 𝒜 x`.

## Main results

* `TauCeti.GradedAlgebra.noZeroDivisors_of_graded`: if nonzero homogeneous elements have no zero
  divisors between them, then `A` has no zero divisors.
* `TauCeti.GradedAlgebra.minDeg_mul`, `TauCeti.GradedAlgebra.maxDeg_mul`: when `A` has no zero
  divisors, `minDeg` and `maxDeg` are additive on nonzero products.
* `TauCeti.GradedAlgebra.mem_minDeg_of_mul_mem`, `TauCeti.GradedAlgebra.exists_mem_of_dvd_of_mem`,
  `TauCeti.GradedAlgebra.exists_mem_of_isUnit`: factors of nonzero homogeneous elements, and all
  units, are homogeneous.
* `TauCeti.GradedAlgebra.degWidth_eq_zero_iff`, `TauCeti.GradedAlgebra.degWidth_mul`,
  `TauCeti.GradedAlgebra.degWidth_le_of_dvd`: degree width is nonnegative, vanishes precisely on
  homogeneous elements, is additive on nonzero products, and is monotone under divisibility.
-/

public section

namespace TauCeti.GradedAlgebra

open _root_.DirectSum

section Decomposition

variable {ι A σ : Type*} [DecidableEq ι] [Zero ι] [LinearOrder ι]
  [AddCommMonoid A] [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [Decomposition 𝒜]

open Classical in
/-- The least degree in the homogeneous support of `x`, or `0` when `x = 0`. -/
noncomputable def minDeg (x : A) : ι :=
  if h : (decompose 𝒜 x).support.Nonempty then (decompose 𝒜 x).support.min' h else 0

open Classical in
/-- The greatest degree in the homogeneous support of `x`, or `0` when `x = 0`. -/
noncomputable def maxDeg (x : A) : ι :=
  if h : (decompose 𝒜 x).support.Nonempty then (decompose 𝒜 x).support.max' h else 0

/-- The homogeneous component of `x` of least degree (`0` when `x = 0`). -/
noncomputable def minHomogPart (x : A) : A :=
  (decompose 𝒜 x (minDeg 𝒜 x) : A)

/-- The homogeneous component of `x` of greatest degree (`0` when `x = 0`). -/
noncomputable def maxHomogPart (x : A) : A :=
  (decompose 𝒜 x (maxDeg 𝒜 x) : A)

theorem minHomogPart_def (x : A) : minHomogPart 𝒜 x = (decompose 𝒜 x (minDeg 𝒜 x) : A) :=
  (rfl)

theorem maxHomogPart_def (x : A) : maxHomogPart 𝒜 x = (decompose 𝒜 x (maxDeg 𝒜 x) : A) :=
  (rfl)

@[simp]
theorem minDeg_zero : minDeg 𝒜 (0 : A) = 0 := by
  classical simp [minDeg]

@[simp]
theorem maxDeg_zero : maxDeg 𝒜 (0 : A) = 0 := by
  classical simp [maxDeg]

@[simp]
theorem minHomogPart_zero : minHomogPart 𝒜 (0 : A) = 0 := by
  simp [minHomogPart]

@[simp]
theorem maxHomogPart_zero : maxHomogPart 𝒜 (0 : A) = 0 := by
  simp [maxHomogPart]

theorem minHomogPart_mem (x : A) : minHomogPart 𝒜 x ∈ 𝒜 (minDeg 𝒜 x) :=
  (decompose 𝒜 x (minDeg 𝒜 x)).property

theorem maxHomogPart_mem (x : A) : maxHomogPart 𝒜 x ∈ 𝒜 (maxDeg 𝒜 x) :=
  (decompose 𝒜 x (maxDeg 𝒜 x)).property

theorem minHomogPart_ne_zero {x : A} (hx : x ≠ 0) : minHomogPart 𝒜 x ≠ 0 := by
  classical
  have hne : (decompose 𝒜 x).support.Nonempty := (support_decompose_nonempty_iff 𝒜).mpr hx
  have hmem : minDeg 𝒜 x ∈ (decompose 𝒜 x).support := by
    simpa only [minDeg, hne, ↓reduceDIte] using Finset.min'_mem _ hne
  exact (mem_support_decompose_iff 𝒜).mp hmem

theorem maxHomogPart_ne_zero {x : A} (hx : x ≠ 0) : maxHomogPart 𝒜 x ≠ 0 := by
  classical
  have hne : (decompose 𝒜 x).support.Nonempty := (support_decompose_nonempty_iff 𝒜).mpr hx
  have hmem : maxDeg 𝒜 x ∈ (decompose 𝒜 x).support := by
    simpa only [maxDeg, hne, ↓reduceDIte] using Finset.max'_mem _ hne
  exact (mem_support_decompose_iff 𝒜).mp hmem

@[simp]
theorem minHomogPart_eq_zero {x : A} : minHomogPart 𝒜 x = 0 ↔ x = 0 :=
  ⟨fun h ↦ by_contra fun hx ↦ minHomogPart_ne_zero 𝒜 hx h, fun h ↦ h ▸ minHomogPart_zero 𝒜⟩

@[simp]
theorem maxHomogPart_eq_zero {x : A} : maxHomogPart 𝒜 x = 0 ↔ x = 0 :=
  ⟨fun h ↦ by_contra fun hx ↦ maxHomogPart_ne_zero 𝒜 hx h, fun h ↦ h ▸ maxHomogPart_zero 𝒜⟩

/-- Every nonzero homogeneous component of `x` has degree at least `minDeg 𝒜 x`. -/
theorem minDeg_le_of_decompose_ne_zero {x : A} {i : ι} (hi : (decompose 𝒜 x i : A) ≠ 0) :
    minDeg 𝒜 x ≤ i := by
  classical
  have hmem : i ∈ (decompose 𝒜 x).support := (mem_support_decompose_iff 𝒜).mpr hi
  have hne : (decompose 𝒜 x).support.Nonempty := ⟨i, hmem⟩
  simpa only [minDeg, hne, ↓reduceDIte] using Finset.min'_le _ i hmem

/-- Every nonzero homogeneous component of `x` has degree at most `maxDeg 𝒜 x`. -/
theorem le_maxDeg_of_decompose_ne_zero {x : A} {i : ι} (hi : (decompose 𝒜 x i : A) ≠ 0) :
    i ≤ maxDeg 𝒜 x := by
  classical
  have hmem : i ∈ (decompose 𝒜 x).support := (mem_support_decompose_iff 𝒜).mpr hi
  have hne : (decompose 𝒜 x).support.Nonempty := ⟨i, hmem⟩
  simpa only [maxDeg, hne, ↓reduceDIte] using Finset.le_max' _ i hmem

theorem coe_decompose_eq_zero_of_lt_minDeg {x : A} {i : ι} (hi : i < minDeg 𝒜 x) :
    (decompose 𝒜 x i : A) = 0 :=
  by_contra fun h ↦ (minDeg_le_of_decompose_ne_zero 𝒜 h).not_gt hi

theorem coe_decompose_eq_zero_of_maxDeg_lt {x : A} {i : ι} (hi : maxDeg 𝒜 x < i) :
    (decompose 𝒜 x i : A) = 0 :=
  by_contra fun h ↦ (le_maxDeg_of_decompose_ne_zero 𝒜 h).not_gt hi

theorem minDeg_le_maxDeg (x : A) : minDeg 𝒜 x ≤ maxDeg 𝒜 x := by
  by_cases hx : x = 0
  · simp [hx]
  · exact le_maxDeg_of_decompose_ne_zero 𝒜 (minHomogPart_ne_zero 𝒜 hx)

/-- Characterization of `minDeg 𝒜 x` for a nonzero element `x` by nonvanishing in degree `d` and
vanishing in all strictly smaller degrees. -/
theorem minDeg_eq_iff {x : A} (hx : x ≠ 0) {d : ι} :
    minDeg 𝒜 x = d ↔ (decompose 𝒜 x d : A) ≠ 0 ∧ ∀ i < d, (decompose 𝒜 x i : A) = 0 := by
  refine ⟨?_, fun ⟨hd, hlt⟩ ↦ le_antisymm (minDeg_le_of_decompose_ne_zero 𝒜 hd) ?_⟩
  · rintro rfl
    exact ⟨minHomogPart_ne_zero 𝒜 hx, fun _ hi ↦ coe_decompose_eq_zero_of_lt_minDeg 𝒜 hi⟩
  · exact le_of_not_gt fun h ↦ minHomogPart_ne_zero 𝒜 hx (hlt _ h)

/-- Characterization of `maxDeg 𝒜 x` for a nonzero element `x` by nonvanishing in degree `d` and
vanishing in all strictly larger degrees. -/
theorem maxDeg_eq_iff {x : A} (hx : x ≠ 0) {d : ι} :
    maxDeg 𝒜 x = d ↔ (decompose 𝒜 x d : A) ≠ 0 ∧ ∀ i, d < i → (decompose 𝒜 x i : A) = 0 := by
  refine ⟨?_, fun ⟨hd, hgt⟩ ↦ le_antisymm ?_ (le_maxDeg_of_decompose_ne_zero 𝒜 hd)⟩
  · rintro rfl
    exact ⟨maxHomogPart_ne_zero 𝒜 hx, fun _ hi ↦ coe_decompose_eq_zero_of_maxDeg_lt 𝒜 hi⟩
  · exact le_of_not_gt fun h ↦ maxHomogPart_ne_zero 𝒜 hx (hgt _ h)

theorem minDeg_of_mem_ne_zero {x : A} {d : ι} (hx : x ∈ 𝒜 d) (hx0 : x ≠ 0) :
    minDeg 𝒜 x = d :=
  (minDeg_eq_iff 𝒜 hx0).mpr
    ⟨by rwa [decompose_of_mem_same 𝒜 hx], fun _ hi ↦ decompose_of_mem_ne 𝒜 hx hi.ne'⟩

theorem maxDeg_of_mem_ne_zero {x : A} {d : ι} (hx : x ∈ 𝒜 d) (hx0 : x ≠ 0) :
    maxDeg 𝒜 x = d :=
  (maxDeg_eq_iff 𝒜 hx0).mpr
    ⟨by rwa [decompose_of_mem_same 𝒜 hx], fun _ hi ↦ decompose_of_mem_ne 𝒜 hx hi.ne⟩

theorem minHomogPart_of_mem {x : A} {d : ι} (hx : x ∈ 𝒜 d) : minHomogPart 𝒜 x = x := by
  by_cases hx0 : x = 0
  · simp [hx0]
  · rw [minHomogPart, minDeg_of_mem_ne_zero 𝒜 hx hx0, decompose_of_mem_same 𝒜 hx]

theorem maxHomogPart_of_mem {x : A} {d : ι} (hx : x ∈ 𝒜 d) : maxHomogPart 𝒜 x = x := by
  by_cases hx0 : x = 0
  · simp [hx0]
  · rw [maxHomogPart, maxDeg_of_mem_ne_zero 𝒜 hx hx0, decompose_of_mem_same 𝒜 hx]

/-- An element `x` lies in `𝒜 (minDeg 𝒜 x)` if and only if `maxDeg 𝒜 x = minDeg 𝒜 x`. -/
theorem mem_minDeg_iff_maxDeg_eq_minDeg {x : A} :
    x ∈ 𝒜 (minDeg 𝒜 x) ↔ maxDeg 𝒜 x = minDeg 𝒜 x := by
  by_cases hx0 : x = 0
  · simp [hx0, zero_mem]
  refine ⟨fun hx ↦ maxDeg_of_mem_ne_zero 𝒜 hx hx0, fun heq ↦ ?_⟩
  classical
  have hex : x = minHomogPart 𝒜 x := by
    conv_lhs => rw [← sum_support_decompose 𝒜 x]
    refine Finset.sum_eq_single (minDeg 𝒜 x) (fun i _ hi ↦ ?_) (fun hnot ↦ ?_)
    · rcases lt_or_gt_of_ne hi with hlt | hgt
      · exact coe_decompose_eq_zero_of_lt_minDeg 𝒜 hlt
      · exact coe_decompose_eq_zero_of_maxDeg_lt 𝒜 (heq.symm ▸ hgt)
    · exact absurd ((mem_support_decompose_iff 𝒜).mpr (minHomogPart_ne_zero 𝒜 hx0)) hnot
  have hmem := minHomogPart_mem 𝒜 x
  rwa [← hex] at hmem

/-- An element is homogeneous if and only if its greatest and least degrees agree. -/
theorem exists_mem_iff_maxDeg_eq_minDeg {x : A} :
    (∃ d, x ∈ 𝒜 d) ↔ maxDeg 𝒜 x = minDeg 𝒜 x := by
  by_cases hx0 : x = 0
  · exact ⟨fun _ ↦ by simp [hx0], fun _ ↦ ⟨0, hx0 ▸ zero_mem _⟩⟩
  refine ⟨fun ⟨d, hd⟩ ↦ ?_, fun h ↦ ⟨minDeg 𝒜 x, (mem_minDeg_iff_maxDeg_eq_minDeg 𝒜).mpr h⟩⟩
  rw [minDeg_of_mem_ne_zero 𝒜 hd hx0, maxDeg_of_mem_ne_zero 𝒜 hd hx0]

/-- When two nonzero elements have strictly ordered least degrees, the sum inherits the smaller
least degree. -/
theorem minDeg_add_eq_left {x y : A} (hx : x ≠ 0) (h : minDeg 𝒜 x < minDeg 𝒜 y) :
    minDeg 𝒜 (x + y) = minDeg 𝒜 x := by
  have hcomp : (decompose 𝒜 (x + y) (minDeg 𝒜 x) : A) = minHomogPart 𝒜 x := by
    rw [decompose_add, _root_.DirectSum.add_apply, AddMemClass.coe_add,
      coe_decompose_eq_zero_of_lt_minDeg 𝒜 h, add_zero, minHomogPart]
  have hxy : x + y ≠ 0 := fun h0 ↦ minHomogPart_ne_zero 𝒜 hx (by simpa [h0] using hcomp.symm)
  refine (minDeg_eq_iff 𝒜 hxy).mpr ⟨hcomp ▸ minHomogPart_ne_zero 𝒜 hx, fun i hi ↦ ?_⟩
  rw [decompose_add, _root_.DirectSum.add_apply, AddMemClass.coe_add,
    coe_decompose_eq_zero_of_lt_minDeg 𝒜 hi,
    coe_decompose_eq_zero_of_lt_minDeg 𝒜 (hi.trans h), add_zero]

/-- When two nonzero elements have strictly ordered greatest degrees, the sum inherits the larger
greatest degree. -/
theorem maxDeg_add_eq_left {x y : A} (hx : x ≠ 0) (h : maxDeg 𝒜 y < maxDeg 𝒜 x) :
    maxDeg 𝒜 (x + y) = maxDeg 𝒜 x := by
  have hcomp : (decompose 𝒜 (x + y) (maxDeg 𝒜 x) : A) = maxHomogPart 𝒜 x := by
    rw [decompose_add, _root_.DirectSum.add_apply, AddMemClass.coe_add,
      coe_decompose_eq_zero_of_maxDeg_lt 𝒜 h, add_zero, maxHomogPart]
  have hxy : x + y ≠ 0 := fun h0 ↦ maxHomogPart_ne_zero 𝒜 hx (by simpa [h0] using hcomp.symm)
  refine (maxDeg_eq_iff 𝒜 hxy).mpr ⟨hcomp ▸ maxHomogPart_ne_zero 𝒜 hx, fun i hi ↦ ?_⟩
  rw [decompose_add, _root_.DirectSum.add_apply, AddMemClass.coe_add,
    coe_decompose_eq_zero_of_maxDeg_lt 𝒜 hi,
    coe_decompose_eq_zero_of_maxDeg_lt 𝒜 (h.trans hi), add_zero]

end Decomposition

section Neg

variable {ι G σ : Type*} [DecidableEq ι] [Zero ι] [LinearOrder ι]
  [AddCommGroup G] [SetLike σ G] [AddSubgroupClass σ G] (𝒜 : ι → σ) [Decomposition 𝒜]

@[simp]
theorem minDeg_neg (x : G) : minDeg 𝒜 (-x) = minDeg 𝒜 x := by
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨hd, hlt⟩ := (minDeg_eq_iff 𝒜 hx).mp rfl
  refine (minDeg_eq_iff 𝒜 (neg_ne_zero.mpr hx)).mpr ⟨?_, fun i hi ↦ ?_⟩
  · rwa [decompose_neg, DFinsupp.neg_apply, NegMemClass.coe_neg, neg_ne_zero]
  · rw [decompose_neg, DFinsupp.neg_apply, NegMemClass.coe_neg, neg_eq_zero]
    exact hlt i hi

@[simp]
theorem maxDeg_neg (x : G) : maxDeg 𝒜 (-x) = maxDeg 𝒜 x := by
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨hd, hgt⟩ := (maxDeg_eq_iff 𝒜 hx).mp rfl
  refine (maxDeg_eq_iff 𝒜 (neg_ne_zero.mpr hx)).mpr ⟨?_, fun i hi ↦ ?_⟩
  · rwa [decompose_neg, DFinsupp.neg_apply, NegMemClass.coe_neg, neg_ne_zero]
  · rw [decompose_neg, DFinsupp.neg_apply, NegMemClass.coe_neg, neg_eq_zero]
    exact hgt i hi

@[simp]
theorem minHomogPart_neg (x : G) : minHomogPart 𝒜 (-x) = -minHomogPart 𝒜 x := by
  rw [minHomogPart, minDeg_neg, decompose_neg, DFinsupp.neg_apply, NegMemClass.coe_neg,
    minHomogPart]

@[simp]
theorem maxHomogPart_neg (x : G) : maxHomogPart 𝒜 (-x) = -maxHomogPart 𝒜 x := by
  rw [maxHomogPart, maxDeg_neg, decompose_neg, DFinsupp.neg_apply, NegMemClass.coe_neg,
    maxHomogPart]

end Neg

section GradedRing

variable {ι A σ : Type*} [DecidableEq ι] [AddMonoid ι] [LinearOrder ι]
  [Semiring A] [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]

@[simp]
theorem minDeg_one : minDeg 𝒜 (1 : A) = 0 := by
  by_cases h : (1 : A) = 0
  · simp [h]
  · exact minDeg_of_mem_ne_zero 𝒜 (SetLike.one_mem_graded 𝒜) h

@[simp]
theorem maxDeg_one : maxDeg 𝒜 (1 : A) = 0 := by
  by_cases h : (1 : A) = 0
  · simp [h]
  · exact maxDeg_of_mem_ne_zero 𝒜 (SetLike.one_mem_graded 𝒜) h

@[simp]
theorem minHomogPart_one : minHomogPart 𝒜 (1 : A) = 1 :=
  minHomogPart_of_mem 𝒜 (SetLike.one_mem_graded 𝒜)

@[simp]
theorem maxHomogPart_one : maxHomogPart 𝒜 (1 : A) = 1 :=
  maxHomogPart_of_mem 𝒜 (SetLike.one_mem_graded 𝒜)

section StrictMono

variable [AddLeftStrictMono ι] [AddRightStrictMono ι]

attribute [local instance] addLeftMono_of_addLeftStrictMono addRightMono_of_addRightStrictMono

/-- Below `minDeg 𝒜 x + minDeg 𝒜 y`, every homogeneous component of `x * y` vanishes. -/
theorem coe_decompose_mul_eq_zero_of_lt {x y : A} {k : ι} (hk : k < minDeg 𝒜 x + minDeg 𝒜 y) :
    (decompose 𝒜 (x * y) k : A) = 0 := by
  classical
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [decompose_mul, _root_.DirectSum.coe_mul_apply]
  refine Finset.sum_eq_zero fun ij hij ↦ ?_
  rw [Finset.mem_filter, Finset.mem_product] at hij
  have hi : minDeg 𝒜 x ≤ ij.1 :=
    minDeg_le_of_decompose_ne_zero 𝒜 ((mem_support_decompose_iff 𝒜).mp hij.1.1)
  have hj : minDeg 𝒜 y ≤ ij.2 :=
    minDeg_le_of_decompose_ne_zero 𝒜 ((mem_support_decompose_iff 𝒜).mp hij.1.2)
  exact absurd (hij.2 ▸ add_le_add hi hj) hk.not_ge

/-- Above `maxDeg 𝒜 x + maxDeg 𝒜 y`, every homogeneous component of `x * y` vanishes. -/
theorem coe_decompose_mul_eq_zero_of_gt {x y : A} {k : ι} (hk : maxDeg 𝒜 x + maxDeg 𝒜 y < k) :
    (decompose 𝒜 (x * y) k : A) = 0 := by
  classical
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [decompose_mul, _root_.DirectSum.coe_mul_apply]
  refine Finset.sum_eq_zero fun ij hij ↦ ?_
  rw [Finset.mem_filter, Finset.mem_product] at hij
  have hi : ij.1 ≤ maxDeg 𝒜 x :=
    le_maxDeg_of_decompose_ne_zero 𝒜 ((mem_support_decompose_iff 𝒜).mp hij.1.1)
  have hj : ij.2 ≤ maxDeg 𝒜 y :=
    le_maxDeg_of_decompose_ne_zero 𝒜 ((mem_support_decompose_iff 𝒜).mp hij.1.2)
  exact absurd (hij.2 ▸ add_le_add hi hj) hk.not_ge

/-- **Extremal lower convolution identity.** For nonzero `x` and `y`, the homogeneous component of
`x * y` in degree `minDeg 𝒜 x + minDeg 𝒜 y` is the single product
`minHomogPart 𝒜 x * minHomogPart 𝒜 y`. -/
theorem coe_decompose_mul_minDeg_add {x y : A} (hx : x ≠ 0) (hy : y ≠ 0) :
    (decompose 𝒜 (x * y) (minDeg 𝒜 x + minDeg 𝒜 y) : A) =
      minHomogPart 𝒜 x * minHomogPart 𝒜 y := by
  classical
  rw [decompose_mul, _root_.DirectSum.coe_mul_apply]
  refine Finset.sum_eq_single (minDeg 𝒜 x, minDeg 𝒜 y) (fun ij hij hne ↦ ?_) (fun hnot ↦ ?_)
  · rw [Finset.mem_filter, Finset.mem_product] at hij
    have hi : minDeg 𝒜 x ≤ ij.1 :=
      minDeg_le_of_decompose_ne_zero 𝒜 ((mem_support_decompose_iff 𝒜).mp hij.1.1)
    have hj : minDeg 𝒜 y ≤ ij.2 :=
      minDeg_le_of_decompose_ne_zero 𝒜 ((mem_support_decompose_iff 𝒜).mp hij.1.2)
    rcases hi.lt_or_eq with hlt | heq
    · exact absurd hij.2 (add_lt_add_of_lt_of_le hlt hj).ne'
    · have hjlt : minDeg 𝒜 y < ij.2 := hj.lt_of_ne fun hj' ↦ hne (Prod.ext heq.symm hj'.symm)
      exact absurd hij.2 (add_lt_add_of_le_of_lt hi hjlt).ne'
  · exfalso
    apply hnot
    rw [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨(mem_support_decompose_iff 𝒜).mpr (minHomogPart_ne_zero 𝒜 hx),
      (mem_support_decompose_iff 𝒜).mpr (minHomogPart_ne_zero 𝒜 hy)⟩, rfl⟩

/-- **Extremal upper convolution identity.** For nonzero `x` and `y`, the homogeneous component of
`x * y` in degree `maxDeg 𝒜 x + maxDeg 𝒜 y` is the single product
`maxHomogPart 𝒜 x * maxHomogPart 𝒜 y`. -/
theorem coe_decompose_mul_maxDeg_add {x y : A} (hx : x ≠ 0) (hy : y ≠ 0) :
    (decompose 𝒜 (x * y) (maxDeg 𝒜 x + maxDeg 𝒜 y) : A) =
      maxHomogPart 𝒜 x * maxHomogPart 𝒜 y := by
  classical
  rw [decompose_mul, _root_.DirectSum.coe_mul_apply]
  refine Finset.sum_eq_single (maxDeg 𝒜 x, maxDeg 𝒜 y) (fun ij hij hne ↦ ?_) (fun hnot ↦ ?_)
  · rw [Finset.mem_filter, Finset.mem_product] at hij
    have hi : ij.1 ≤ maxDeg 𝒜 x :=
      le_maxDeg_of_decompose_ne_zero 𝒜 ((mem_support_decompose_iff 𝒜).mp hij.1.1)
    have hj : ij.2 ≤ maxDeg 𝒜 y :=
      le_maxDeg_of_decompose_ne_zero 𝒜 ((mem_support_decompose_iff 𝒜).mp hij.1.2)
    rcases hi.lt_or_eq with hlt | heq
    · exact absurd hij.2 (add_lt_add_of_lt_of_le hlt hj).ne
    · have hjlt : ij.2 < maxDeg 𝒜 y := hj.lt_of_ne fun hj' ↦ hne (Prod.ext heq hj')
      exact absurd hij.2 (add_lt_add_of_le_of_lt hi hjlt).ne
  · exfalso
    apply hnot
    rw [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨(mem_support_decompose_iff 𝒜).mpr (maxHomogPart_ne_zero 𝒜 hx),
      (mem_support_decompose_iff 𝒜).mpr (maxHomogPart_ne_zero 𝒜 hy)⟩, rfl⟩

/-- **A ring graded by an ordered cancellative monoid has no zero divisors as soon as its
homogeneous elements have none.** -/
theorem noZeroDivisors_of_graded
    (h : ∀ {i j : ι} {a b : A}, a ∈ 𝒜 i → b ∈ 𝒜 j → a * b = 0 → a = 0 ∨ b = 0) :
    NoZeroDivisors A :=
  ⟨fun {x y} hxy ↦ by
    by_contra! hne
    refine (h (minHomogPart_mem 𝒜 x) (minHomogPart_mem 𝒜 y) ?_).elim
      (minHomogPart_ne_zero 𝒜 hne.1) (minHomogPart_ne_zero 𝒜 hne.2)
    rw [← coe_decompose_mul_minDeg_add 𝒜 hne.1 hne.2, hxy]
    simp⟩

/-- Whenever the product of least homogeneous parts is nonzero, `minDeg` adds on the product. -/
theorem minDeg_mul_of_mul_ne_zero {x y : A} (h : minHomogPart 𝒜 x * minHomogPart 𝒜 y ≠ 0) :
    minDeg 𝒜 (x * y) = minDeg 𝒜 x + minDeg 𝒜 y := by
  have hx : x ≠ 0 := fun hx0 ↦ h (by simp [hx0])
  have hy : y ≠ 0 := fun hy0 ↦ h (by simp [hy0])
  have hcomp : (decompose 𝒜 (x * y) (minDeg 𝒜 x + minDeg 𝒜 y) : A) ≠ 0 := by
    rwa [coe_decompose_mul_minDeg_add 𝒜 hx hy]
  have hxy : x * y ≠ 0 := fun h0 ↦ hcomp (by simp [h0])
  exact (minDeg_eq_iff 𝒜 hxy).mpr ⟨hcomp, fun _ hk ↦ coe_decompose_mul_eq_zero_of_lt 𝒜 hk⟩

/-- Whenever the product of greatest homogeneous parts is nonzero, `maxDeg` adds on the product. -/
theorem maxDeg_mul_of_mul_ne_zero {x y : A} (h : maxHomogPart 𝒜 x * maxHomogPart 𝒜 y ≠ 0) :
    maxDeg 𝒜 (x * y) = maxDeg 𝒜 x + maxDeg 𝒜 y := by
  have hx : x ≠ 0 := fun hx0 ↦ h (by simp [hx0])
  have hy : y ≠ 0 := fun hy0 ↦ h (by simp [hy0])
  have hcomp : (decompose 𝒜 (x * y) (maxDeg 𝒜 x + maxDeg 𝒜 y) : A) ≠ 0 := by
    rwa [coe_decompose_mul_maxDeg_add 𝒜 hx hy]
  have hxy : x * y ≠ 0 := fun h0 ↦ hcomp (by simp [h0])
  exact (maxDeg_eq_iff 𝒜 hxy).mpr ⟨hcomp, fun _ hk ↦ coe_decompose_mul_eq_zero_of_gt 𝒜 hk⟩

section NoZeroDivisors

variable [NoZeroDivisors A]

theorem minDeg_mul {x y : A} (hx : x ≠ 0) (hy : y ≠ 0) :
    minDeg 𝒜 (x * y) = minDeg 𝒜 x + minDeg 𝒜 y :=
  minDeg_mul_of_mul_ne_zero 𝒜 (mul_ne_zero (minHomogPart_ne_zero 𝒜 hx) (minHomogPart_ne_zero 𝒜 hy))

theorem maxDeg_mul {x y : A} (hx : x ≠ 0) (hy : y ≠ 0) :
    maxDeg 𝒜 (x * y) = maxDeg 𝒜 x + maxDeg 𝒜 y :=
  maxDeg_mul_of_mul_ne_zero 𝒜 (mul_ne_zero (maxHomogPart_ne_zero 𝒜 hx) (maxHomogPart_ne_zero 𝒜 hy))

@[simp]
theorem minHomogPart_mul (x y : A) :
    minHomogPart 𝒜 (x * y) = minHomogPart 𝒜 x * minHomogPart 𝒜 y := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [minHomogPart, minDeg_mul 𝒜 hx hy, coe_decompose_mul_minDeg_add 𝒜 hx hy]

@[simp]
theorem maxHomogPart_mul (x y : A) :
    maxHomogPart 𝒜 (x * y) = maxHomogPart 𝒜 x * maxHomogPart 𝒜 y := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [maxHomogPart, maxDeg_mul 𝒜 hx hy, coe_decompose_mul_maxDeg_add 𝒜 hx hy]

/-- The least homogeneous part as a multiplicative homomorphism with zero. -/
noncomputable def minHomogPartHom : A →*₀ A where
  toFun := minHomogPart 𝒜
  map_zero' := minHomogPart_zero 𝒜
  map_one' := minHomogPart_one 𝒜
  map_mul' := minHomogPart_mul 𝒜

/-- The greatest homogeneous part as a multiplicative homomorphism with zero. -/
noncomputable def maxHomogPartHom : A →*₀ A where
  toFun := maxHomogPart 𝒜
  map_zero' := maxHomogPart_zero 𝒜
  map_one' := maxHomogPart_one 𝒜
  map_mul' := maxHomogPart_mul 𝒜

@[simp]
theorem minHomogPartHom_apply (x : A) : minHomogPartHom 𝒜 x = minHomogPart 𝒜 x :=
  (rfl)

@[simp]
theorem maxHomogPartHom_apply (x : A) : maxHomogPartHom 𝒜 x = maxHomogPart 𝒜 x :=
  (rfl)

@[simp]
theorem minHomogPart_pow (x : A) (n : ℕ) : minHomogPart 𝒜 (x ^ n) = minHomogPart 𝒜 x ^ n :=
  map_pow (minHomogPartHom 𝒜) x n

@[simp]
theorem maxHomogPart_pow (x : A) (n : ℕ) : maxHomogPart 𝒜 (x ^ n) = maxHomogPart 𝒜 x ^ n :=
  map_pow (maxHomogPartHom 𝒜) x n

theorem minDeg_pow {x : A} (hx : x ≠ 0) (n : ℕ) : minDeg 𝒜 (x ^ n) = n • minDeg 𝒜 x := by
  rcases subsingleton_or_nontrivial A with _ | _
  · exact absurd (Subsingleton.elim x 0) hx
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', minDeg_mul 𝒜 hx (pow_ne_zero n hx), ih, succ_nsmul']

theorem maxDeg_pow {x : A} (hx : x ≠ 0) (n : ℕ) : maxDeg 𝒜 (x ^ n) = n • maxDeg 𝒜 x := by
  rcases subsingleton_or_nontrivial A with _ | _
  · exact absurd (Subsingleton.elim x 0) hx
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', maxDeg_mul 𝒜 hx (pow_ne_zero n hx), ih, succ_nsmul']

/-- **Factors of a nonzero homogeneous product are homogeneous.** -/
theorem mem_minDeg_of_mul_mem {a b : A} {d : ι} (hab : a * b ∈ 𝒜 d) (hne : a * b ≠ 0) :
    a ∈ 𝒜 (minDeg 𝒜 a) ∧ b ∈ 𝒜 (minDeg 𝒜 b) := by
  have ha : a ≠ 0 := left_ne_zero_of_mul hne
  have hb : b ≠ 0 := right_ne_zero_of_mul hne
  have heq : minDeg 𝒜 a + minDeg 𝒜 b = maxDeg 𝒜 a + maxDeg 𝒜 b := by
    rw [← minDeg_mul 𝒜 ha hb, ← maxDeg_mul 𝒜 ha hb,
      minDeg_of_mem_ne_zero 𝒜 hab hne, maxDeg_of_mem_ne_zero 𝒜 hab hne]
  have hle_a := minDeg_le_maxDeg 𝒜 a
  have hle_b := minDeg_le_maxDeg 𝒜 b
  refine ⟨(mem_minDeg_iff_maxDeg_eq_minDeg 𝒜).mpr ?_,
    (mem_minDeg_iff_maxDeg_eq_minDeg 𝒜).mpr ?_⟩
  · exact (hle_a.eq_of_not_lt fun hlt ↦ (add_lt_add_of_lt_of_le hlt hle_b).ne heq).symm
  · exact (hle_b.eq_of_not_lt fun hlt ↦ (add_lt_add_of_le_of_lt hle_a hlt).ne heq).symm

/-- Every divisor of a nonzero homogeneous element lies in `𝒜 (minDeg 𝒜 a)`. -/
theorem mem_minDeg_of_dvd_of_mem {a b : A} {d : ι} (hdvd : a ∣ b) (hb : b ∈ 𝒜 d) (hb0 : b ≠ 0) :
    a ∈ 𝒜 (minDeg 𝒜 a) := by
  obtain ⟨c, rfl⟩ := hdvd
  exact (mem_minDeg_of_mul_mem 𝒜 hb hb0).1

/-- Every divisor of a nonzero homogeneous element is homogeneous. -/
theorem exists_mem_of_dvd_of_mem {a b : A} {d : ι} (hdvd : a ∣ b) (hb : b ∈ 𝒜 d) (hb0 : b ≠ 0) :
    ∃ i, a ∈ 𝒜 i :=
  ⟨minDeg 𝒜 a, mem_minDeg_of_dvd_of_mem 𝒜 hdvd hb hb0⟩

/-- **Every unit of a graded ring without zero divisors lies in `𝒜 (minDeg 𝒜 u)`.** -/
theorem mem_minDeg_of_isUnit {u : A} (hu : IsUnit u) : u ∈ 𝒜 (minDeg 𝒜 u) := by
  by_cases h1 : (1 : A) = 0
  · have hu0 : u = 0 := by rw [← mul_one u, h1, mul_zero]
    simp [hu0, zero_mem]
  · obtain ⟨v, huv, -⟩ := isUnit_iff_exists.mp hu
    exact (mem_minDeg_of_mul_mem 𝒜 (huv ▸ SetLike.one_mem_graded 𝒜) (huv ▸ h1)).1

/-- Every unit of a graded ring without zero divisors is homogeneous. -/
theorem exists_mem_of_isUnit {u : A} (hu : IsUnit u) : ∃ d, u ∈ 𝒜 d :=
  ⟨minDeg 𝒜 u, mem_minDeg_of_isUnit 𝒜 hu⟩

end NoZeroDivisors

end StrictMono

end GradedRing

section CommGradedRing

variable {ι A σ : Type*} [DecidableEq ι] [AddCommMonoid ι] [LinearOrder ι]
  [IsOrderedCancelAddMonoid ι] [CommSemiring A] [NoZeroDivisors A]
  [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]

theorem minDeg_prod {κ : Type*} {s : Finset κ} {f : κ → A} (hf : ∀ i ∈ s, f i ≠ 0) :
    minDeg 𝒜 (∏ i ∈ s, f i) = ∑ i ∈ s, minDeg 𝒜 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.forall_mem_insert] at hf
    rcases subsingleton_or_nontrivial A with _ | _
    · exact absurd (Subsingleton.elim (f a) 0) hf.1
    · have hprod : ∏ i ∈ s, f i ≠ 0 := Finset.prod_ne_zero_iff.mpr hf.2
      rw [Finset.prod_insert ha, minDeg_mul 𝒜 hf.1 hprod, Finset.sum_insert ha, ih hf.2]

theorem maxDeg_prod {κ : Type*} {s : Finset κ} {f : κ → A} (hf : ∀ i ∈ s, f i ≠ 0) :
    maxDeg 𝒜 (∏ i ∈ s, f i) = ∑ i ∈ s, maxDeg 𝒜 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.forall_mem_insert] at hf
    rcases subsingleton_or_nontrivial A with _ | _
    · exact absurd (Subsingleton.elim (f a) 0) hf.1
    · have hprod : ∏ i ∈ s, f i ≠ 0 := Finset.prod_ne_zero_iff.mpr hf.2
      rw [Finset.prod_insert ha, maxDeg_mul 𝒜 hf.1 hprod, Finset.sum_insert ha, ih hf.2]

end CommGradedRing

section Width

variable {ι : Type*} [DecidableEq ι] [AddCommGroup ι] [LinearOrder ι]

section Decomposition

variable {A σ : Type*} [AddCommMonoid A] [SetLike σ A] [AddSubmonoidClass σ A]
  (𝒜 : ι → σ) [Decomposition 𝒜]

/-- The **degree width** of `x` in an internally decomposed module indexed by an ordered additive
group: the difference `maxDeg 𝒜 x - minDeg 𝒜 x`. -/
noncomputable def degWidth (x : A) : ι :=
  maxDeg 𝒜 x - minDeg 𝒜 x

theorem degWidth_def (x : A) : degWidth 𝒜 x = maxDeg 𝒜 x - minDeg 𝒜 x :=
  (rfl)

@[simp]
theorem degWidth_zero : degWidth 𝒜 (0 : A) = 0 := by
  simp [degWidth]

theorem degWidth_nonneg [IsOrderedAddMonoid ι] (x : A) : 0 ≤ degWidth 𝒜 x :=
  sub_nonneg.mpr (minDeg_le_maxDeg 𝒜 x)

/-- **The degree width of `x` vanishes if and only if `x` is homogeneous.** -/
@[simp]
theorem degWidth_eq_zero_iff {x : A} : degWidth 𝒜 x = 0 ↔ ∃ d, x ∈ 𝒜 d := by
  rw [degWidth, sub_eq_zero, exists_mem_iff_maxDeg_eq_minDeg]

theorem degWidth_of_mem {x : A} {d : ι} (hx : x ∈ 𝒜 d) : degWidth 𝒜 x = 0 :=
  (degWidth_eq_zero_iff 𝒜).mpr ⟨d, hx⟩

end Decomposition

section Neg

variable {G σ : Type*} [AddCommGroup G] [SetLike σ G] [AddSubgroupClass σ G]
  (𝒜 : ι → σ) [Decomposition 𝒜]

@[simp]
theorem degWidth_neg (x : G) : degWidth 𝒜 (-x) = degWidth 𝒜 x := by
  simp [degWidth]

end Neg

section GradedRing

variable {A σ : Type*} [Semiring A] [SetLike σ A] [AddSubmonoidClass σ A]
  (𝒜 : ι → σ) [GradedRing 𝒜]

@[simp]
theorem degWidth_one : degWidth 𝒜 (1 : A) = 0 := by
  simp [degWidth]

/-- Multiplying on the left by a homogeneous unit preserves the degree width without any
zero-divisor hypothesis on `A`. -/
theorem degWidth_mul_of_isUnit_of_mem_left [IsOrderedAddMonoid ι] {u : A} {d : ι}
    (hu : IsUnit u) (hud : u ∈ 𝒜 d) (x : A) :
    degWidth 𝒜 (u * x) = degWidth 𝒜 x := by
  rcases subsingleton_or_nontrivial A with _ | _
  · simp [Subsingleton.elim (u * x) x]
  by_cases hx : x = 0
  · simp [hx]
  have hmin : minDeg 𝒜 (u * x) = d + minDeg 𝒜 x := by
    rw [minDeg_mul_of_mul_ne_zero 𝒜, minDeg_of_mem_ne_zero 𝒜 hud hu.ne_zero]
    simpa [minHomogPart_of_mem 𝒜 hud] using mt hu.mul_right_eq_zero.mp (minHomogPart_ne_zero 𝒜 hx)
  have hmax : maxDeg 𝒜 (u * x) = d + maxDeg 𝒜 x := by
    rw [maxDeg_mul_of_mul_ne_zero 𝒜, maxDeg_of_mem_ne_zero 𝒜 hud hu.ne_zero]
    simpa [maxHomogPart_of_mem 𝒜 hud] using mt hu.mul_right_eq_zero.mp (maxHomogPart_ne_zero 𝒜 hx)
  rw [degWidth, hmax, hmin, add_sub_add_left_eq_sub, ← degWidth]

/-- Multiplying on the right by a homogeneous unit preserves the degree width without any
zero-divisor hypothesis on `A`. -/
theorem degWidth_mul_of_isUnit_of_mem_right [IsOrderedAddMonoid ι] {u : A} {d : ι}
    (hu : IsUnit u) (hud : u ∈ 𝒜 d) (x : A) :
    degWidth 𝒜 (x * u) = degWidth 𝒜 x := by
  rcases subsingleton_or_nontrivial A with _ | _
  · simp [Subsingleton.elim (x * u) x]
  by_cases hx : x = 0
  · simp [hx]
  have hmin : minDeg 𝒜 (x * u) = minDeg 𝒜 x + d := by
    rw [minDeg_mul_of_mul_ne_zero 𝒜, minDeg_of_mem_ne_zero 𝒜 hud hu.ne_zero]
    simpa [minHomogPart_of_mem 𝒜 hud] using mt hu.mul_left_eq_zero.mp (minHomogPart_ne_zero 𝒜 hx)
  have hmax : maxDeg 𝒜 (x * u) = maxDeg 𝒜 x + d := by
    rw [maxDeg_mul_of_mul_ne_zero 𝒜, maxDeg_of_mem_ne_zero 𝒜 hud hu.ne_zero]
    simpa [maxHomogPart_of_mem 𝒜 hud] using mt hu.mul_left_eq_zero.mp (maxHomogPart_ne_zero 𝒜 hx)
  rw [degWidth, hmax, hmin, add_sub_add_right_eq_sub, ← degWidth]

section NoZeroDivisors

variable [IsOrderedAddMonoid ι] [NoZeroDivisors A]

/-- **Degree width is additive on nonzero products** in a graded ring without zero divisors. -/
theorem degWidth_mul {x y : A} (hx : x ≠ 0) (hy : y ≠ 0) :
    degWidth 𝒜 (x * y) = degWidth 𝒜 x + degWidth 𝒜 y := by
  simp only [degWidth, minDeg_mul 𝒜 hx hy, maxDeg_mul 𝒜 hx hy]
  abel

@[simp]
theorem degWidth_of_isUnit {u : A} (hu : IsUnit u) : degWidth 𝒜 u = 0 :=
  degWidth_of_mem 𝒜 (mem_minDeg_of_isUnit 𝒜 hu)

/-- Multiplying on the left by a unit leaves the degree width unchanged. -/
theorem degWidth_mul_of_isUnit_left {u : A} (hu : IsUnit u) (x : A) :
    degWidth 𝒜 (u * x) = degWidth 𝒜 x :=
  degWidth_mul_of_isUnit_of_mem_left 𝒜 hu (mem_minDeg_of_isUnit 𝒜 hu) x

/-- Multiplying on the right by a unit leaves the degree width unchanged. -/
theorem degWidth_mul_of_isUnit_right {u : A} (hu : IsUnit u) (x : A) :
    degWidth 𝒜 (x * u) = degWidth 𝒜 x :=
  degWidth_mul_of_isUnit_of_mem_right 𝒜 hu (mem_minDeg_of_isUnit 𝒜 hu) x

theorem degWidth_pow (x : A) (n : ℕ) : degWidth 𝒜 (x ^ n) = n • degWidth 𝒜 x := by
  rcases subsingleton_or_nontrivial A with _ | _
  · rw [Subsingleton.elim (x ^ n) 0, Subsingleton.elim x 0, degWidth_zero, smul_zero]
  by_cases hx : x = 0
  · rcases n with _ | n <;> simp [hx]
  · simp [degWidth, maxDeg_pow 𝒜 hx n, minDeg_pow 𝒜 hx n, nsmul_sub]

/-- Any divisor of a nonzero element has degree width at most that of the dividend. -/
theorem degWidth_le_of_dvd {a b : A} (hab : a ∣ b) (hb : b ≠ 0) :
    degWidth 𝒜 a ≤ degWidth 𝒜 b := by
  obtain ⟨c, rfl⟩ := hab
  rw [degWidth_mul 𝒜 (left_ne_zero_of_mul hb) (right_ne_zero_of_mul hb)]
  exact le_add_of_nonneg_right (degWidth_nonneg 𝒜 c)

end NoZeroDivisors

end GradedRing

section CommGradedRing

variable [IsOrderedAddMonoid ι] {A σ : Type*} [CommSemiring A] [NoZeroDivisors A]
  [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]

theorem degWidth_prod {κ : Type*} {s : Finset κ} {f : κ → A} (hf : ∀ i ∈ s, f i ≠ 0) :
    degWidth 𝒜 (∏ i ∈ s, f i) = ∑ i ∈ s, degWidth 𝒜 (f i) := by
  simp only [degWidth, maxDeg_prod 𝒜 hf, minDeg_prod 𝒜 hf, Finset.sum_sub_distrib]

end CommGradedRing

end Width

end TauCeti.GradedAlgebra
