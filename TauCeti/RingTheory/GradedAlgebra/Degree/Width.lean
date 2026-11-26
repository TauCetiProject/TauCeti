/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Degree
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Algebra.Order.Monoid.WithTop
import TauCeti.Algebra.DirectSum.Laurent

/-!
# Least and greatest degrees, homogeneous parts, and width in `ℤ`-graded rings

Every element `x` of a ring `A` with an internal `ℤ`-decomposition `𝒜` is a finite sum of
homogeneous components `DirectSum.decompose 𝒜 x i ∈ 𝒜 i`. When `x ≠ 0`, the support of these
components has a greatest integer `maxDegree 𝒜 x` and a least integer `minDegree 𝒜 x` (both set to
`0` at `0`), with corresponding nonzero homogeneous components `leadingPart 𝒜 x` and
`trailingPart 𝒜 x`. Their difference `width 𝒜 x = maxDegree 𝒜 x - minDegree 𝒜 x` is nonnegative and
vanishes if and only if `x` is homogeneous.

When `𝒜` is a `GradedRing` and `A` has no zero divisors (commutativity is not assumed), both
extreme homogeneous parts are multiplicative (`leadingPartHom`, `trailingPartHom`), so
`maxDegree 𝒜`, `minDegree 𝒜`, and `width 𝒜` are additive on nonzero products. In particular,
divisors of a nonzero element have smaller or equal width, and every unit of a `ℤ`-graded domain is
homogeneous.

## Main definitions

* `TauCeti.GradedAlgebra.maxDegree 𝒜 x`: greatest degree of a nonzero homogeneous component of `x`,
  or `0` when `x = 0`.
* `TauCeti.GradedAlgebra.minDegree 𝒜 x`: least degree of a nonzero homogeneous component of `x`,
  or `0` when `x = 0`.
* `TauCeti.GradedAlgebra.width 𝒜 x`: the degree spread `maxDegree 𝒜 x - minDegree 𝒜 x`.
* `TauCeti.GradedAlgebra.leadingPart 𝒜 x`, `TauCeti.GradedAlgebra.trailingPart 𝒜 x`: the
  homogeneous components of `x` at `maxDegree 𝒜 x` and `minDegree 𝒜 x`, bundled as
  `MonoidWithZeroHom`s `leadingPartHom` and `trailingPartHom` when `A` has no zero divisors.

## Main results

* `TauCeti.GradedAlgebra.width_eq_zero_iff`: `width 𝒜 x = 0 ↔ SetLike.IsHomogeneousElem 𝒜 x`.
* `TauCeti.GradedAlgebra.leadingPart_mul`, `TauCeti.GradedAlgebra.trailingPart_mul`: the greatest
  and least homogeneous parts are multiplicative over a semiring without zero divisors.
* `TauCeti.GradedAlgebra.maxDegree_mul`, `TauCeti.GradedAlgebra.minDegree_mul`,
  `TauCeti.GradedAlgebra.width_mul`: additivity of extreme degrees and width on nonzero products.
* `TauCeti.GradedAlgebra.width_le_of_dvd`, `TauCeti.GradedAlgebra.isHomogeneousElem_of_isUnit`:
  divisibility bounds width, forcing every unit of a `ℤ`-graded domain to be homogeneous.

## Implementation notes

Via `TauCeti.decomposeLaurent`, an internal `ℤ`-decomposition embeds additively (and
multiplicatively for a `GradedRing`) into `A[T;T⁻¹]`. Reading `maxDegree` through the order
embedding `(↑) : ℤ → WithBot ℤ` and `minDegree` through `n ↦ (↑(-n) : WithBot ℤ)` reuses
`AddMonoidAlgebra.supDegree` and `AddMonoidAlgebra.leadingCoeff` uniformly for both ends without
requiring decidable equality on `A`.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras I: Foundations*, J. Amer. Math. Soc. 15 (2002),
  §3.
* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Adv. Math. 195 (2005), §4.
-/

public section

open DirectSum

namespace TauCeti.GradedAlgebra

noncomputable section

section Decomposition

variable {A σ : Type*} [Semiring A] [SetLike σ A] [AddSubmonoidClass σ A]
  (𝒜 : ℤ → σ) [Decomposition 𝒜]

private abbrev posDeg : ℤ → WithBot ℤ := WithBot.some
private abbrev negDeg : ℤ → WithBot ℤ := fun n ↦ WithBot.some (-n)

private theorem posDeg_injective : Function.Injective posDeg := WithBot.coe_injective

private theorem negDeg_injective : Function.Injective negDeg :=
  WithBot.coe_injective.comp neg_injective

private theorem posDeg_add (a b : ℤ) : posDeg (a + b) = posDeg a + posDeg b := rfl

private theorem negDeg_add (a b : ℤ) : negDeg (a + b) = negDeg a + negDeg b := by
  rw [negDeg, neg_add_rev, WithBot.coe_add, add_comm]

/-- The greatest integer degree in which `x` has a nonzero homogeneous component, or `0` if
`x = 0`. -/
def maxDegree (x : A) : ℤ :=
  ((decomposeLaurent 𝒜 x).supDegree posDeg).unbotD 0

/-- The least integer degree in which `x` has a nonzero homogeneous component, or `0` if
`x = 0`. -/
def minDegree (x : A) : ℤ :=
  -((decomposeLaurent 𝒜 x).supDegree negDeg).unbotD 0

/-- The degree spread `maxDegree 𝒜 x - minDegree 𝒜 x` of an element in a `ℤ`-decomposed ring. -/
def width (x : A) : ℤ :=
  maxDegree 𝒜 x - minDegree 𝒜 x

/-- The homogeneous component of `x` of greatest degree `maxDegree 𝒜 x` (zero when `x = 0`). -/
def leadingPart (x : A) : A :=
  decompose 𝒜 x (maxDegree 𝒜 x)

/-- The homogeneous component of `x` of least degree `minDegree 𝒜 x` (zero when `x = 0`). -/
def trailingPart (x : A) : A :=
  decompose 𝒜 x (minDegree 𝒜 x)

theorem width_def (x : A) : width 𝒜 x = maxDegree 𝒜 x - minDegree 𝒜 x :=
  (rfl)

theorem leadingPart_def (x : A) : leadingPart 𝒜 x = decompose 𝒜 x (maxDegree 𝒜 x) :=
  (rfl)

theorem trailingPart_def (x : A) : trailingPart 𝒜 x = decompose 𝒜 x (minDegree 𝒜 x) :=
  (rfl)

@[simp]
theorem maxDegree_zero : maxDegree 𝒜 (0 : A) = 0 := by
  simp [maxDegree]

@[simp]
theorem minDegree_zero : minDegree 𝒜 (0 : A) = 0 := by
  simp [minDegree]

@[simp]
theorem width_zero : width 𝒜 (0 : A) = 0 := by
  simp [width]

@[simp]
theorem leadingPart_zero : leadingPart 𝒜 (0 : A) = 0 := by
  simp [leadingPart]

@[simp]
theorem trailingPart_zero : trailingPart 𝒜 (0 : A) = 0 := by
  simp [trailingPart]

/-- The greatest homogeneous part of `x` lies in `𝒜 (maxDegree 𝒜 x)`. -/
theorem leadingPart_mem (x : A) : leadingPart 𝒜 x ∈ 𝒜 (maxDegree 𝒜 x) :=
  (decompose 𝒜 x (maxDegree 𝒜 x)).property

/-- The least homogeneous part of `x` lies in `𝒜 (minDegree 𝒜 x)`. -/
theorem trailingPart_mem (x : A) : trailingPart 𝒜 x ∈ 𝒜 (minDegree 𝒜 x) :=
  (decompose 𝒜 x (minDegree 𝒜 x)).property

private theorem supDegree_posDeg_eq {x : A} (hx : x ≠ 0) :
    (decomposeLaurent 𝒜 x).supDegree posDeg = posDeg (maxDegree 𝒜 x) := by
  have hx' : decomposeLaurent 𝒜 x ≠ 0 := (decomposeLaurent_eq_zero 𝒜).not.mpr hx
  obtain ⟨a, -, ha⟩ := AddMonoidAlgebra.exists_supDegree_mem_support posDeg hx'
  simp [maxDegree, ha, posDeg]

private theorem supDegree_negDeg_eq {x : A} (hx : x ≠ 0) :
    (decomposeLaurent 𝒜 x).supDegree negDeg = negDeg (minDegree 𝒜 x) := by
  have hx' : decomposeLaurent 𝒜 x ≠ 0 := (decomposeLaurent_eq_zero 𝒜).not.mpr hx
  obtain ⟨a, -, ha⟩ := AddMonoidAlgebra.exists_supDegree_mem_support negDeg hx'
  simp [minDegree, ha, negDeg]

private theorem leadingPart_eq_leadingCoeff (x : A) :
    leadingPart 𝒜 x = (decomposeLaurent 𝒜 x).leadingCoeff posDeg := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [AddMonoidAlgebra.leadingCoeff, supDegree_posDeg_eq 𝒜 hx,
      Function.leftInverse_invFun posDeg_injective, coeff_decomposeLaurent, leadingPart_def]

private theorem trailingPart_eq_leadingCoeff (x : A) :
    trailingPart 𝒜 x = (decomposeLaurent 𝒜 x).leadingCoeff negDeg := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [AddMonoidAlgebra.leadingCoeff, supDegree_negDeg_eq 𝒜 hx,
      Function.leftInverse_invFun negDeg_injective, coeff_decomposeLaurent, trailingPart_def]

@[simp]
theorem leadingPart_eq_zero {x : A} : leadingPart 𝒜 x = 0 ↔ x = 0 := by
  rw [leadingPart_eq_leadingCoeff, AddMonoidAlgebra.leadingCoeff_eq_zero posDeg_injective,
    decomposeLaurent_eq_zero]

theorem leadingPart_ne_zero {x : A} : leadingPart 𝒜 x ≠ 0 ↔ x ≠ 0 :=
  (leadingPart_eq_zero 𝒜).not

@[simp]
theorem trailingPart_eq_zero {x : A} : trailingPart 𝒜 x = 0 ↔ x = 0 := by
  rw [trailingPart_eq_leadingCoeff, AddMonoidAlgebra.leadingCoeff_eq_zero negDeg_injective,
    decomposeLaurent_eq_zero]

theorem trailingPart_ne_zero {x : A} : trailingPart 𝒜 x ≠ 0 ↔ x ≠ 0 :=
  (trailingPart_eq_zero 𝒜).not

/-- Every nonzero homogeneous component of `x` has degree at most `maxDegree 𝒜 x`. -/
theorem le_maxDegree_of_decompose_ne_zero {x : A} {i : ℤ}
    (hi : (decompose 𝒜 x i : A) ≠ 0) : i ≤ maxDegree 𝒜 x := by
  have hx : x ≠ 0 := by
    rintro rfl
    exact hi (by simp)
  have hmem : i ∈ (decomposeLaurent 𝒜 x).coeff.support := by
    rwa [Finsupp.mem_support_iff, coeff_decomposeLaurent]
  have hle : posDeg i ≤ (decomposeLaurent 𝒜 x).supDegree posDeg := Finset.le_sup hmem
  rwa [supDegree_posDeg_eq 𝒜 hx, posDeg, WithBot.coe_le_coe] at hle

/-- Every nonzero homogeneous component of `x` has degree at least `minDegree 𝒜 x`. -/
theorem minDegree_le_of_decompose_ne_zero {x : A} {i : ℤ}
    (hi : (decompose 𝒜 x i : A) ≠ 0) : minDegree 𝒜 x ≤ i := by
  have hx : x ≠ 0 := by
    rintro rfl
    exact hi (by simp)
  have hmem : i ∈ (decomposeLaurent 𝒜 x).coeff.support := by
    rwa [Finsupp.mem_support_iff, coeff_decomposeLaurent]
  have hle : negDeg i ≤ (decomposeLaurent 𝒜 x).supDegree negDeg := Finset.le_sup hmem
  rw [supDegree_negDeg_eq 𝒜 hx, negDeg, WithBot.coe_le_coe, neg_le_neg_iff] at hle
  exact hle

/-- Homogeneous components strictly above `maxDegree 𝒜 x` vanish. -/
theorem coe_decompose_eq_zero_of_maxDegree_lt {x : A} {i : ℤ} (h : maxDegree 𝒜 x < i) :
    (decompose 𝒜 x i : A) = 0 := by
  by_contra hi
  exact h.not_ge (le_maxDegree_of_decompose_ne_zero 𝒜 hi)

theorem decompose_eq_zero_of_maxDegree_lt {x : A} {i : ℤ} (h : maxDegree 𝒜 x < i) :
    decompose 𝒜 x i = 0 :=
  Subtype.ext (coe_decompose_eq_zero_of_maxDegree_lt 𝒜 h)

/-- Homogeneous components strictly below `minDegree 𝒜 x` vanish. -/
theorem coe_decompose_eq_zero_of_lt_minDegree {x : A} {i : ℤ} (h : i < minDegree 𝒜 x) :
    (decompose 𝒜 x i : A) = 0 := by
  by_contra hi
  exact h.not_ge (minDegree_le_of_decompose_ne_zero 𝒜 hi)

theorem decompose_eq_zero_of_lt_minDegree {x : A} {i : ℤ} (h : i < minDegree 𝒜 x) :
    decompose 𝒜 x i = 0 :=
  Subtype.ext (coe_decompose_eq_zero_of_lt_minDegree 𝒜 h)

/-- Characterization of `maxDegree 𝒜 x` on nonzero elements. -/
theorem maxDegree_eq_iff {x : A} (hx : x ≠ 0) {d : ℤ} :
    maxDegree 𝒜 x = d ↔
      (decompose 𝒜 x d : A) ≠ 0 ∧ ∀ i, (decompose 𝒜 x i : A) ≠ 0 → i ≤ d := by
  refine ⟨?_, fun ⟨hd, hle⟩ ↦ ?_⟩
  · rintro rfl
    exact ⟨(leadingPart_ne_zero 𝒜).mpr hx, fun _ ↦ le_maxDegree_of_decompose_ne_zero 𝒜⟩
  · exact le_antisymm
      (hle _ ((leadingPart_ne_zero 𝒜).mpr hx))
      (le_maxDegree_of_decompose_ne_zero 𝒜 hd)

/-- Characterization of `minDegree 𝒜 x` on nonzero elements. -/
theorem minDegree_eq_iff {x : A} (hx : x ≠ 0) {d : ℤ} :
    minDegree 𝒜 x = d ↔
      (decompose 𝒜 x d : A) ≠ 0 ∧ ∀ i, (decompose 𝒜 x i : A) ≠ 0 → d ≤ i := by
  refine ⟨?_, fun ⟨hd, hle⟩ ↦ ?_⟩
  · rintro rfl
    exact ⟨(trailingPart_ne_zero 𝒜).mpr hx, fun _ ↦ minDegree_le_of_decompose_ne_zero 𝒜⟩
  · exact le_antisymm
      (minDegree_le_of_decompose_ne_zero 𝒜 hd)
      (hle _ ((trailingPart_ne_zero 𝒜).mpr hx))

/-- The least degree never exceeds the greatest degree. -/
theorem minDegree_le_maxDegree (x : A) : minDegree 𝒜 x ≤ maxDegree 𝒜 x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact minDegree_le_of_decompose_ne_zero 𝒜 ((leadingPart_ne_zero 𝒜).mpr hx)

/-- The degree width is always nonnegative. -/
theorem width_nonneg (x : A) : 0 ≤ width 𝒜 x :=
  sub_nonneg.mpr (minDegree_le_maxDegree 𝒜 x)

/-- A nonzero homogeneous element of degree `i` has `maxDegree` equal to `i`. -/
theorem maxDegree_of_mem {x : A} {i : ℤ} (hx : x ∈ 𝒜 i) (hx0 : x ≠ 0) :
    maxDegree 𝒜 x = i := by
  rw [maxDegree_eq_iff 𝒜 hx0]
  refine ⟨by rwa [decompose_of_mem_same 𝒜 hx], fun j hj ↦ ?_⟩
  by_contra hji
  exact hj (decompose_of_mem_ne 𝒜 hx (Ne.symm (ne_of_gt (lt_of_not_ge hji))))

/-- A nonzero homogeneous element of degree `i` has `minDegree` equal to `i`. -/
theorem minDegree_of_mem {x : A} {i : ℤ} (hx : x ∈ 𝒜 i) (hx0 : x ≠ 0) :
    minDegree 𝒜 x = i := by
  rw [minDegree_eq_iff 𝒜 hx0]
  refine ⟨by rwa [decompose_of_mem_same 𝒜 hx], fun j hj ↦ ?_⟩
  by_contra hji
  exact hj (decompose_of_mem_ne 𝒜 hx (ne_of_gt (lt_of_not_ge hji)))

/-- A homogeneous element coincides with its greatest homogeneous part. -/
theorem leadingPart_of_mem {x : A} {i : ℤ} (hx : x ∈ 𝒜 i) : leadingPart 𝒜 x = x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  · rw [leadingPart_def, maxDegree_of_mem 𝒜 hx hx0, decompose_of_mem_same 𝒜 hx]

/-- A homogeneous element coincides with its least homogeneous part. -/
theorem trailingPart_of_mem {x : A} {i : ℤ} (hx : x ∈ 𝒜 i) : trailingPart 𝒜 x = x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  · rw [trailingPart_def, minDegree_of_mem 𝒜 hx hx0, decompose_of_mem_same 𝒜 hx]

/-- Any homogeneous element has width zero. -/
theorem width_eq_zero_of_mem {x : A} {i : ℤ} (hx : x ∈ 𝒜 i) : width 𝒜 x = 0 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  · rw [width_def, maxDegree_of_mem 𝒜 hx hx0, minDegree_of_mem 𝒜 hx hx0, sub_self]

/-- An element of width zero lies in the graded piece of its greatest degree. -/
theorem mem_grade_maxDegree_of_width_eq_zero {x : A} (h : width 𝒜 x = 0) :
    x ∈ 𝒜 (maxDegree 𝒜 x) := by
  have hmin : minDegree 𝒜 x = maxDegree 𝒜 x := (sub_eq_zero.mp h).symm
  set y := decompose 𝒜 x (maxDegree 𝒜 x) with hy
  have hdec : decompose 𝒜 x = DirectSum.of (fun i ↦ 𝒜 i) (maxDegree 𝒜 x) y := by
    ext i : 1
    rcases lt_trichotomy i (maxDegree 𝒜 x) with hlt | rfl | hgt
    · rw [decompose_eq_zero_of_lt_minDegree 𝒜 (hmin.symm ▸ hlt),
        DirectSum.of_eq_of_ne _ _ _ hlt.ne]
    · rw [DirectSum.of_eq_same, ← hy]
    · rw [decompose_eq_zero_of_maxDegree_lt 𝒜 hgt, DirectSum.of_eq_of_ne _ _ _ hgt.ne']
  have hx : x = (y : A) := by
    calc x = (decompose 𝒜).symm (decompose 𝒜 x) := ((decompose 𝒜).symm_apply_apply x).symm
      _ = (y : A) := by rw [hdec, decompose_symm_of]
  have hy_mem : (y : A) ∈ 𝒜 (maxDegree 𝒜 x) := y.property
  rwa [← hx] at hy_mem

/-- **Width-zero characterization of homogeneity.** An element has width zero if and only if it is
homogeneous. -/
@[simp]
theorem width_eq_zero_iff {x : A} : width 𝒜 x = 0 ↔ SetLike.IsHomogeneousElem 𝒜 x :=
  ⟨fun h ↦ ⟨maxDegree 𝒜 x, mem_grade_maxDegree_of_width_eq_zero 𝒜 h⟩,
    fun ⟨_, hi⟩ ↦ width_eq_zero_of_mem 𝒜 hi⟩

/-- An element equals its greatest homogeneous part if and only if it is homogeneous. -/
theorem leadingPart_eq_self_iff {x : A} :
    leadingPart 𝒜 x = x ↔ SetLike.IsHomogeneousElem 𝒜 x :=
  ⟨fun h ↦ ⟨maxDegree 𝒜 x, by have hm := leadingPart_mem 𝒜 x; rwa [h] at hm⟩,
    fun ⟨_, hi⟩ ↦ leadingPart_of_mem 𝒜 hi⟩

/-- An element equals its least homogeneous part if and only if it is homogeneous. -/
theorem trailingPart_eq_self_iff {x : A} :
    trailingPart 𝒜 x = x ↔ SetLike.IsHomogeneousElem 𝒜 x :=
  ⟨fun h ↦ ⟨minDegree 𝒜 x, by have hm := trailingPart_mem 𝒜 x; rwa [h] at hm⟩,
    fun ⟨_, hi⟩ ↦ trailingPart_of_mem 𝒜 hi⟩

/-- Ultrametric upper bound for `maxDegree` on nonzero sums. -/
theorem maxDegree_add_le {x y : A} (hxy : x + y ≠ 0) :
    maxDegree 𝒜 (x + y) ≤ max (maxDegree 𝒜 x) (maxDegree 𝒜 y) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hle : (decomposeLaurent 𝒜 (x + y)).supDegree posDeg ≤
      (decomposeLaurent 𝒜 x).supDegree posDeg ⊔ (decomposeLaurent 𝒜 y).supDegree posDeg := by
    rw [map_add]
    exact AddMonoidAlgebra.supDegree_add_le
  rwa [supDegree_posDeg_eq 𝒜 hxy, supDegree_posDeg_eq 𝒜 hx, supDegree_posDeg_eq 𝒜 hy,
    posDeg, ← WithBot.coe_max, WithBot.coe_le_coe] at hle

/-- Ultrametric lower bound for `minDegree` on nonzero sums. -/
theorem le_minDegree_add {x y : A} (hxy : x + y ≠ 0) :
    min (minDegree 𝒜 x) (minDegree 𝒜 y) ≤ minDegree 𝒜 (x + y) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hle : (decomposeLaurent 𝒜 (x + y)).supDegree negDeg ≤
      (decomposeLaurent 𝒜 x).supDegree negDeg ⊔ (decomposeLaurent 𝒜 y).supDegree negDeg := by
    rw [map_add]
    exact AddMonoidAlgebra.supDegree_add_le
  rw [supDegree_negDeg_eq 𝒜 hxy, supDegree_negDeg_eq 𝒜 hx, supDegree_negDeg_eq 𝒜 hy,
    negDeg, ← WithBot.coe_max, WithBot.coe_le_coe] at hle
  omega

/-- Strict inequality of greatest degrees determines `maxDegree` of a sum. -/
theorem maxDegree_add_eq_left {x y : A} (hx : x ≠ 0)
    (h : maxDegree 𝒜 y < maxDegree 𝒜 x) : maxDegree 𝒜 (x + y) = maxDegree 𝒜 x := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [add_zero]
  have hlt : (decomposeLaurent 𝒜 y).supDegree posDeg <
      (decomposeLaurent 𝒜 x).supDegree posDeg := by
    rwa [supDegree_posDeg_eq 𝒜 hy, supDegree_posDeg_eq 𝒜 hx, posDeg, WithBot.coe_lt_coe]
  have heq : (decomposeLaurent 𝒜 (x + y)).supDegree posDeg =
      (decomposeLaurent 𝒜 x).supDegree posDeg := by
    rw [map_add]
    exact AddMonoidAlgebra.supDegree_add_eq_left hlt
  rw [maxDegree, maxDegree, heq]

/-- Strict inequality of greatest degrees determines `maxDegree` of a sum. -/
theorem maxDegree_add_eq_right {x y : A} (hy : y ≠ 0)
    (h : maxDegree 𝒜 x < maxDegree 𝒜 y) : maxDegree 𝒜 (x + y) = maxDegree 𝒜 y := by
  rw [add_comm, maxDegree_add_eq_left 𝒜 hy h]

/-- Strict inequality of least degrees determines `minDegree` of a sum. -/
theorem minDegree_add_eq_left {x y : A} (hx : x ≠ 0)
    (h : minDegree 𝒜 x < minDegree 𝒜 y) : minDegree 𝒜 (x + y) = minDegree 𝒜 x := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [add_zero]
  have hlt : (decomposeLaurent 𝒜 y).supDegree negDeg <
      (decomposeLaurent 𝒜 x).supDegree negDeg := by
    rw [supDegree_negDeg_eq 𝒜 hy, supDegree_negDeg_eq 𝒜 hx, negDeg, WithBot.coe_lt_coe]
    omega
  have heq : (decomposeLaurent 𝒜 (x + y)).supDegree negDeg =
      (decomposeLaurent 𝒜 x).supDegree negDeg := by
    rw [map_add]
    exact AddMonoidAlgebra.supDegree_add_eq_left hlt
  rw [minDegree, minDegree, heq]

/-- Strict inequality of least degrees determines `minDegree` of a sum. -/
theorem minDegree_add_eq_right {x y : A} (hy : y ≠ 0)
    (h : minDegree 𝒜 y < minDegree 𝒜 x) : minDegree 𝒜 (x + y) = minDegree 𝒜 y := by
  rw [add_comm, minDegree_add_eq_left 𝒜 hy h]

end Decomposition

section Ring

variable {A σ : Type*} [Ring A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℤ → σ) [Decomposition 𝒜]

@[simp]
theorem maxDegree_neg (x : A) : maxDegree 𝒜 (-x) = maxDegree 𝒜 x := by
  simp [maxDegree]

@[simp]
theorem minDegree_neg (x : A) : minDegree 𝒜 (-x) = minDegree 𝒜 x := by
  simp [minDegree]

@[simp]
theorem width_neg (x : A) : width 𝒜 (-x) = width 𝒜 x := by
  simp [width]

@[simp]
theorem leadingPart_neg (x : A) : leadingPart 𝒜 (-x) = -leadingPart 𝒜 x := by
  rw [leadingPart_def, leadingPart_def, maxDegree_neg]
  simp [DirectSum.apply_eq_component ℤ]

@[simp]
theorem trailingPart_neg (x : A) : trailingPart 𝒜 (-x) = -trailingPart 𝒜 x := by
  rw [trailingPart_def, trailingPart_def, minDegree_neg]
  simp [DirectSum.apply_eq_component ℤ]

end Ring

section GradedRing

variable {A σ : Type*} [Semiring A] [SetLike σ A] [AddSubmonoidClass σ A]
  (𝒜 : ℤ → σ) [GradedRing 𝒜]

@[simp]
theorem maxDegree_one : maxDegree 𝒜 (1 : A) = 0 := by
  rcases eq_or_ne (1 : A) 0 with h1 | h1
  · simp [h1]
  · exact maxDegree_of_mem 𝒜 (SetLike.one_mem_graded 𝒜) h1

@[simp]
theorem minDegree_one : minDegree 𝒜 (1 : A) = 0 := by
  rcases eq_or_ne (1 : A) 0 with h1 | h1
  · simp [h1]
  · exact minDegree_of_mem 𝒜 (SetLike.one_mem_graded 𝒜) h1

@[simp]
theorem width_one : width 𝒜 (1 : A) = 0 := by
  simp [width]

@[simp]
theorem leadingPart_one : leadingPart 𝒜 (1 : A) = 1 :=
  leadingPart_of_mem 𝒜 (SetLike.one_mem_graded 𝒜)

@[simp]
theorem trailingPart_one : trailingPart 𝒜 (1 : A) = 1 :=
  trailingPart_of_mem 𝒜 (SetLike.one_mem_graded 𝒜)

/-- In any `ℤ`-graded ring, the component of `x * y` at `maxDegree 𝒜 x + maxDegree 𝒜 y` is the
product of their greatest homogeneous parts. -/
theorem coe_decompose_mul_maxDegree_add (x y : A) :
    (decompose 𝒜 (x * y) (maxDegree 𝒜 x + maxDegree 𝒜 y) : A) =
      leadingPart 𝒜 x * leadingPart 𝒜 y := by
  have huniq : UniqueAdd (decomposeLaurent 𝒜 x).coeff.support
      (decomposeLaurent 𝒜 y).coeff.support (maxDegree 𝒜 x) (maxDegree 𝒜 y) := by
    intro i j hi hj hij
    rw [Finsupp.mem_support_iff, coeff_decomposeLaurent] at hi hj
    have hi' := le_maxDegree_of_decompose_ne_zero 𝒜 hi
    have hj' := le_maxDegree_of_decompose_ne_zero 𝒜 hj
    exact ⟨by omega, by omega⟩
  rw [← coeff_decomposeLaurent, decomposeLaurent_mul 𝒜 𝒜,
    AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd huniq,
    coeff_decomposeLaurent, coeff_decomposeLaurent, ← leadingPart_def, ← leadingPart_def]

/-- In any `ℤ`-graded ring, the component of `x * y` at `minDegree 𝒜 x + minDegree 𝒜 y` is the
product of their least homogeneous parts. -/
theorem coe_decompose_mul_minDegree_add (x y : A) :
    (decompose 𝒜 (x * y) (minDegree 𝒜 x + minDegree 𝒜 y) : A) =
      trailingPart 𝒜 x * trailingPart 𝒜 y := by
  have huniq : UniqueAdd (decomposeLaurent 𝒜 x).coeff.support
      (decomposeLaurent 𝒜 y).coeff.support (minDegree 𝒜 x) (minDegree 𝒜 y) := by
    intro i j hi hj hij
    rw [Finsupp.mem_support_iff, coeff_decomposeLaurent] at hi hj
    have hi' := minDegree_le_of_decompose_ne_zero 𝒜 hi
    have hj' := minDegree_le_of_decompose_ne_zero 𝒜 hj
    exact ⟨by omega, by omega⟩
  rw [← coeff_decomposeLaurent, decomposeLaurent_mul 𝒜 𝒜,
    AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd huniq,
    coeff_decomposeLaurent, coeff_decomposeLaurent, ← trailingPart_def, ← trailingPart_def]

/-- Subadditivity of `maxDegree` on nonzero products in any `ℤ`-graded ring. -/
theorem maxDegree_mul_le {x y : A} (hxy : x * y ≠ 0) :
    maxDegree 𝒜 (x * y) ≤ maxDegree 𝒜 x + maxDegree 𝒜 y := by
  have hx : x ≠ 0 := left_ne_zero_of_mul hxy
  have hy : y ≠ 0 := right_ne_zero_of_mul hxy
  have hle : (decomposeLaurent 𝒜 (x * y)).supDegree posDeg ≤
      (decomposeLaurent 𝒜 x).supDegree posDeg + (decomposeLaurent 𝒜 y).supDegree posDeg := by
    rw [decomposeLaurent_mul 𝒜 𝒜]
    exact AddMonoidAlgebra.supDegree_mul_le posDeg_add
  rwa [supDegree_posDeg_eq 𝒜 hxy, supDegree_posDeg_eq 𝒜 hx, supDegree_posDeg_eq 𝒜 hy,
    posDeg, ← WithBot.coe_add, WithBot.coe_le_coe] at hle

/-- Superadditivity of `minDegree` on nonzero products in any `ℤ`-graded ring. -/
theorem le_minDegree_mul {x y : A} (hxy : x * y ≠ 0) :
    minDegree 𝒜 x + minDegree 𝒜 y ≤ minDegree 𝒜 (x * y) := by
  have hx : x ≠ 0 := left_ne_zero_of_mul hxy
  have hy : y ≠ 0 := right_ne_zero_of_mul hxy
  have hle : (decomposeLaurent 𝒜 (x * y)).supDegree negDeg ≤
      (decomposeLaurent 𝒜 x).supDegree negDeg + (decomposeLaurent 𝒜 y).supDegree negDeg := by
    rw [decomposeLaurent_mul 𝒜 𝒜]
    exact AddMonoidAlgebra.supDegree_mul_le negDeg_add
  rw [supDegree_negDeg_eq 𝒜 hxy, supDegree_negDeg_eq 𝒜 hx, supDegree_negDeg_eq 𝒜 hy,
    negDeg, ← WithBot.coe_add, WithBot.coe_le_coe] at hle
  omega

/-- Subadditivity of `width` on nonzero products in any `ℤ`-graded ring. -/
theorem width_mul_le {x y : A} (hxy : x * y ≠ 0) :
    width 𝒜 (x * y) ≤ width 𝒜 x + width 𝒜 y := by
  have hmax := maxDegree_mul_le 𝒜 hxy
  have hmin := le_minDegree_mul 𝒜 hxy
  rw [width_def, width_def, width_def]
  omega

end GradedRing

section NoZeroDivisors

variable {A σ : Type*} [Semiring A] [NoZeroDivisors A] [SetLike σ A] [AddSubmonoidClass σ A]
  (𝒜 : ℤ → σ) [GradedRing 𝒜]

/-- **Additivity of `maxDegree`** on nonzero elements in a `ℤ`-graded ring without zero divisors. -/
theorem maxDegree_mul {x y : A} (hx : x ≠ 0) (hy : y ≠ 0) :
    maxDegree 𝒜 (x * y) = maxDegree 𝒜 x + maxDegree 𝒜 y := by
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  refine le_antisymm (maxDegree_mul_le 𝒜 hxy) (le_maxDegree_of_decompose_ne_zero 𝒜 ?_)
  rw [coe_decompose_mul_maxDegree_add]
  exact mul_ne_zero ((leadingPart_ne_zero 𝒜).mpr hx) ((leadingPart_ne_zero 𝒜).mpr hy)

/-- **Additivity of `minDegree`** on nonzero elements in a `ℤ`-graded ring without zero divisors. -/
theorem minDegree_mul {x y : A} (hx : x ≠ 0) (hy : y ≠ 0) :
    minDegree 𝒜 (x * y) = minDegree 𝒜 x + minDegree 𝒜 y := by
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  refine le_antisymm (minDegree_le_of_decompose_ne_zero 𝒜 ?_) (le_minDegree_mul 𝒜 hxy)
  rw [coe_decompose_mul_minDegree_add]
  exact mul_ne_zero ((trailingPart_ne_zero 𝒜).mpr hx) ((trailingPart_ne_zero 𝒜).mpr hy)

/-- **Additivity of `width`** on nonzero elements in a `ℤ`-graded ring without zero divisors. -/
theorem width_mul {x y : A} (hx : x ≠ 0) (hy : y ≠ 0) :
    width 𝒜 (x * y) = width 𝒜 x + width 𝒜 y := by
  rw [width_def, maxDegree_mul 𝒜 hx hy, minDegree_mul 𝒜 hx hy, width_def, width_def]
  omega

/-- **Multiplicativity of the greatest homogeneous part** in a `ℤ`-graded ring without zero
divisors (commutativity is not required). -/
@[simp]
theorem leadingPart_mul (x y : A) :
    leadingPart 𝒜 (x * y) = leadingPart 𝒜 x * leadingPart 𝒜 y := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  rw [leadingPart_def, maxDegree_mul 𝒜 hx hy, coe_decompose_mul_maxDegree_add]

/-- **Multiplicativity of the least homogeneous part** in a `ℤ`-graded ring without zero divisors
(commutativity is not required). -/
@[simp]
theorem trailingPart_mul (x y : A) :
    trailingPart 𝒜 (x * y) = trailingPart 𝒜 x * trailingPart 𝒜 y := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  rw [trailingPart_def, minDegree_mul 𝒜 hx hy, coe_decompose_mul_minDegree_add]

/-- The greatest homogeneous part as a multiplicative homomorphism with zero. -/
def leadingPartHom : A →*₀ A where
  toFun := leadingPart 𝒜
  map_zero' := leadingPart_zero 𝒜
  map_one' := leadingPart_one 𝒜
  map_mul' := leadingPart_mul 𝒜

@[simp]
theorem coe_leadingPartHom : ⇑(leadingPartHom 𝒜) = leadingPart 𝒜 :=
  (rfl)

/-- The least homogeneous part as a multiplicative homomorphism with zero. -/
def trailingPartHom : A →*₀ A where
  toFun := trailingPart 𝒜
  map_zero' := trailingPart_zero 𝒜
  map_one' := trailingPart_one 𝒜
  map_mul' := trailingPart_mul 𝒜

@[simp]
theorem coe_trailingPartHom : ⇑(trailingPartHom 𝒜) = trailingPart 𝒜 :=
  (rfl)

@[simp]
theorem maxDegree_pow (x : A) (n : ℕ) : maxDegree 𝒜 (x ^ n) = n • maxDegree 𝒜 x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · rw [pow_succ, maxDegree_mul 𝒜 (pow_ne_zero n hx) hx, ih, succ_nsmul]

@[simp]
theorem minDegree_pow (x : A) (n : ℕ) : minDegree 𝒜 (x ^ n) = n • minDegree 𝒜 x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · rw [pow_succ, minDegree_mul 𝒜 (pow_ne_zero n hx) hx, ih, succ_nsmul]

@[simp]
theorem width_pow (x : A) (n : ℕ) : width 𝒜 (x ^ n) = n • width 𝒜 x := by
  rw [width_def, maxDegree_pow, minDegree_pow, width_def, nsmul_sub]

/-- Left factors of a nonzero product have smaller or equal width. -/
theorem width_le_of_mul_eq_left {x y z : A} (hz : z ≠ 0) (h : x * y = z) :
    width 𝒜 x ≤ width 𝒜 z := by
  subst h
  have hx : x ≠ 0 := left_ne_zero_of_mul hz
  have hy : y ≠ 0 := right_ne_zero_of_mul hz
  have h0 : 0 ≤ width 𝒜 y := width_nonneg 𝒜 y
  rw [width_mul 𝒜 hx hy]
  omega

/-- Right factors of a nonzero product have smaller or equal width. -/
theorem width_le_of_mul_eq_right {x y z : A} (hz : z ≠ 0) (h : x * y = z) :
    width 𝒜 y ≤ width 𝒜 z := by
  subst h
  have hx : x ≠ 0 := left_ne_zero_of_mul hz
  have hy : y ≠ 0 := right_ne_zero_of_mul hz
  have h0 : 0 ≤ width 𝒜 x := width_nonneg 𝒜 x
  rw [width_mul 𝒜 hx hy]
  omega

/-- Any divisor of a nonzero element has smaller or equal width. -/
theorem width_le_of_dvd {x y : A} (hy : y ≠ 0) (h : x ∣ y) :
    width 𝒜 x ≤ width 𝒜 y := by
  obtain ⟨z, rfl⟩ := h
  exact width_le_of_mul_eq_left 𝒜 hy rfl

/-- Every unit of a `ℤ`-graded ring without zero divisors has width zero. -/
theorem width_eq_zero_of_isUnit {u : A} (hu : IsUnit u) : width 𝒜 u = 0 := by
  rcases eq_or_ne (1 : A) 0 with h1 | h1
  · have : Subsingleton A := subsingleton_of_zero_eq_one h1.symm
    rw [Subsingleton.elim u 0, width_zero]
  · obtain ⟨v, hv, -⟩ := isUnit_iff_exists.mp hu
    exact le_antisymm (by simpa using width_le_of_mul_eq_left 𝒜 h1 hv) (width_nonneg 𝒜 u)

@[simp]
theorem width_units (u : Aˣ) : width 𝒜 (u : A) = 0 :=
  width_eq_zero_of_isUnit 𝒜 u.isUnit

/-- **Units of a `ℤ`-graded domain are homogeneous.** Commutativity is not required. -/
theorem isHomogeneousElem_of_isUnit {u : A} (hu : IsUnit u) :
    SetLike.IsHomogeneousElem 𝒜 u :=
  (width_eq_zero_iff 𝒜).mp (width_eq_zero_of_isUnit 𝒜 hu)

theorem isHomogeneousElem_units (u : Aˣ) :
    SetLike.IsHomogeneousElem 𝒜 (u : A) :=
  isHomogeneousElem_of_isUnit 𝒜 u.isUnit

end NoZeroDivisors

end

end TauCeti.GradedAlgebra
