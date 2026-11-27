/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.Order.Ring.WithTop
public import Mathlib.Data.Set.Finite.List
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Numerical classes of coherent sheaves on a curve

A coherent sheaf `F` on a smooth projective geometrically connected curve `X` of genus `g` over a
field has a numerical class `(rk F, deg F)`, with `rk F ≥ 0`. This file develops the numerical
side of slope theory and of the Euler form on these classes, independently of any sheaf.

* The *slope* of a class is `deg / rk` when the rank is positive and `+∞` (the top element `⊤`
  of `WithTop ℚ`) when the rank is zero. Torsion sheaves therefore have slope `+∞`. The zero
  class also receives the value `⊤`; this only totalizes the function, since the zero sheaf has
  no slope.
* A class is *nonzero effective* when it has positive rank, or rank zero and positive degree.
  These are the numerical conditions satisfied by the class of a nonzero coherent sheaf, whose
  torsion part has degree equal to its length weighted by residue degrees. On nonzero effective
  classes, slopes compare by cross-multiplication (`slope_le_slope_iff`), and the slope of a sum
  lies between the slopes of the summands (the see-saw property, `slope_le_slope_add_iff` and
  `slope_add_le_slope_iff`). These are the numerical inputs of every Harder–Narasimhan argument.
* Tensoring by a line bundle of degree `a` acts on classes by `twist a`, which adds `a` to the
  slope.
* The *Euler form* `χ(c, c') = (1 - g) rk c rk c' + rk c deg c' - rk c' deg c` is the value of
  `dim Hom(F, F') - dim Ext¹(F, F')` given by Riemann–Roch for sheaves of classes `c` and `c'`.
  It is additive in each variable, invariant under simultaneous twisting, satisfies the numerical
  form of Serre duality `χ(c, c') = -χ(c', c ⊗ ω)` with `deg ω = 2g - 2`, and its antisymmetric
  part `2 (rk c deg c' - rk c' deg c)` detects the order of slopes.
* A *Harder–Narasimhan type* is a list of nonzero effective classes with strictly decreasing
  slopes, the classes of the successive quotients of a Harder–Narasimhan filtration. For a fixed
  total class only finitely many types have all slopes nonnegative.

## Main declarations

* `TauCeti.CurveSheafClass`: the classes `(rank, degree)`, an additive commutative monoid.
* `TauCeti.CurveSheafClass.slope`: the slope, with values in `WithTop ℚ`.
* `TauCeti.CurveSheafClass.slope_le_slope_iff`: comparison of slopes by cross-multiplication.
* `TauCeti.CurveSheafClass.slope_le_slope_add_iff` and
  `TauCeti.CurveSheafClass.slope_add_le_slope_iff`: the see-saw property.
* `TauCeti.CurveSheafClass.eulerForm`: the Euler form on a curve of genus `g`.
* `TauCeti.CurveSheafClass.eulerForm_twist_swap`: numerical Serre duality.
* `TauCeti.CurveSheafClass.HNType`: numerical Harder–Narasimhan types.
* `TauCeti.CurveSheafClass.HNType.finite_setOf_total_eq_and_slope_nonneg`: finiteness of the
  types of a fixed class with nonnegative slopes.

## References

* C. Schiffmann, *Lectures on Hall algebras*, §2.1 and §4.2, for the Euler form on classes of
  coherent sheaves on a curve, the slope convention for torsion sheaves and the
  Harder–Narasimhan filtration.
* S. S. Shatz, *The decomposition and specialization of algebraic families of vector bundles*,
  Compositio Math. 35 (1977), §1, for the see-saw property and Harder–Narasimhan types.
-/

public section

namespace TauCeti

/-- The numerical class `(rk F, deg F)` of a coherent sheaf `F` on a curve: a natural number,
the rank, and an integer, the degree. -/
@[ext]
structure CurveSheafClass where
  /-- The rank of the class. -/
  rank : ℕ
  /-- The degree of the class. -/
  degree : ℤ

namespace CurveSheafClass

variable {c c' : CurveSheafClass}

instance : Zero CurveSheafClass := ⟨⟨0, 0⟩⟩

instance : Add CurveSheafClass := ⟨fun c c' ↦ ⟨c.rank + c'.rank, c.degree + c'.degree⟩⟩

instance : SMul ℕ CurveSheafClass := ⟨fun n c ↦ ⟨n * c.rank, n * c.degree⟩⟩

@[simp]
theorem rank_zero : (0 : CurveSheafClass).rank = 0 := rfl

@[simp]
theorem degree_zero : (0 : CurveSheafClass).degree = 0 := rfl

@[simp]
theorem rank_add (c c' : CurveSheafClass) : (c + c').rank = c.rank + c'.rank := rfl

@[simp]
theorem degree_add (c c' : CurveSheafClass) : (c + c').degree = c.degree + c'.degree := rfl

@[simp]
theorem rank_nsmul (n : ℕ) (c : CurveSheafClass) : (n • c).rank = n * c.rank := rfl

@[simp]
theorem degree_nsmul (n : ℕ) (c : CurveSheafClass) : (n • c).degree = n * c.degree := rfl

instance : AddCommMonoid CurveSheafClass :=
  Function.Injective.addCommMonoid (fun c ↦ (c.rank, c.degree))
    (fun c c' h ↦ by ext <;> simp_all [Prod.ext_iff]) rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- The rank of a sum of classes is the sum of the ranks. -/
@[simp]
theorem rank_list_sum (l : List CurveSheafClass) : l.sum.rank = (l.map rank).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- The degree of a sum of classes is the sum of the degrees. -/
@[simp]
theorem degree_list_sum (l : List CurveSheafClass) : l.sum.degree = (l.map degree).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-! ### Nonzero effective classes -/

/-- A class is *nonzero effective* when it has positive rank, or rank zero and positive degree.
The class of a nonzero coherent sheaf on a curve is nonzero effective: a torsion sheaf has as
degree its length weighted by residue degrees, which is positive unless the sheaf is zero. -/
def IsNonzeroEffective (c : CurveSheafClass) : Prop :=
  0 < c.rank ∨ 0 < c.degree

theorem isNonzeroEffective_iff : c.IsNonzeroEffective ↔ 0 < c.rank ∨ 0 < c.degree :=
  Iff.rfl

/-- A class of positive rank is nonzero effective. -/
theorem IsNonzeroEffective.of_rank_pos (h : 0 < c.rank) : c.IsNonzeroEffective :=
  Or.inl h

/-- A class of nonzero rank is nonzero effective. -/
theorem IsNonzeroEffective.of_rank_ne_zero (h : c.rank ≠ 0) : c.IsNonzeroEffective :=
  .of_rank_pos (Nat.pos_of_ne_zero h)

/-- A class of positive degree is nonzero effective. -/
theorem IsNonzeroEffective.of_degree_pos (h : 0 < c.degree) : c.IsNonzeroEffective :=
  Or.inr h

theorem IsNonzeroEffective.ne_zero (hc : c.IsNonzeroEffective) : c ≠ 0 := by
  rintro rfl
  simp [isNonzeroEffective_iff] at hc

/-- A nonzero effective class of rank zero has positive degree. -/
theorem IsNonzeroEffective.degree_pos_of_rank_eq_zero (hc : c.IsNonzeroEffective)
    (h : c.rank = 0) : 0 < c.degree := by
  rcases hc with hc | hc
  · omega
  · exact hc

theorem IsNonzeroEffective.add (hc : c.IsNonzeroEffective) (hc' : c'.IsNonzeroEffective) :
    (c + c').IsNonzeroEffective := by
  rw [isNonzeroEffective_iff] at *
  simp only [rank_add, degree_add]
  omega

/-! ### Slopes -/

/-- The slope `deg c / rk c` of a class of positive rank, and `⊤`, standing for `+∞`, for a
class of rank zero. The zero class also has slope `⊤`. -/
def slope (c : CurveSheafClass) : WithTop ℚ :=
  if c.rank = 0 then ⊤ else ((c.degree / c.rank : ℚ) : WithTop ℚ)

theorem slope_def (c : CurveSheafClass) :
    c.slope = if c.rank = 0 then ⊤ else ((c.degree / c.rank : ℚ) : WithTop ℚ) :=
  (rfl)

theorem slope_of_rank_eq_zero (h : c.rank = 0) : c.slope = ⊤ := by
  simp [slope, h]

theorem slope_of_rank_ne_zero (h : c.rank ≠ 0) :
    c.slope = ((c.degree / c.rank : ℚ) : WithTop ℚ) := by
  simp [slope, h]

@[simp]
theorem slope_eq_top_iff : c.slope = ⊤ ↔ c.rank = 0 := by
  by_cases h : c.rank = 0
  · simp [slope_of_rank_eq_zero h, h]
  · simp [slope_of_rank_ne_zero h, h]

@[simp]
theorem slope_zero : (0 : CurveSheafClass).slope = ⊤ :=
  slope_of_rank_eq_zero rfl

/-- Slopes of nonzero effective classes compare by cross-multiplication:
`μ(c) ≤ μ(c')` if and only if `rk c' deg c ≤ rk c deg c'`. -/
theorem slope_le_slope_iff (hc : c.IsNonzeroEffective) (hc' : c'.IsNonzeroEffective) :
    c.slope ≤ c'.slope ↔ (c'.rank : ℤ) * c.degree ≤ c.rank * c'.degree := by
  by_cases h : c.rank = 0
  · have hd := hc.degree_pos_of_rank_eq_zero h
    simp only [slope_of_rank_eq_zero h, top_le_iff, slope_eq_top_iff, h, Nat.cast_zero, zero_mul]
    exact ⟨fun h' ↦ by simp [h'], fun h' ↦ by nlinarith⟩
  by_cases h' : c'.rank = 0
  · have hd := hc'.degree_pos_of_rank_eq_zero h'
    simp only [slope_of_rank_eq_zero h', le_top, h', Nat.cast_zero, zero_mul, true_iff]
    positivity
  rw [slope_of_rank_ne_zero h, slope_of_rank_ne_zero h', WithTop.coe_le_coe,
    div_le_div_iff₀ (by positivity) (by positivity)]
  norm_cast
  constructor <;> intro <;> linarith

/-- Slopes of nonzero effective classes compare strictly by cross-multiplication:
`μ(c) < μ(c')` if and only if `rk c' deg c < rk c deg c'`. -/
theorem slope_lt_slope_iff (hc : c.IsNonzeroEffective) (hc' : c'.IsNonzeroEffective) :
    c.slope < c'.slope ↔ (c'.rank : ℤ) * c.degree < c.rank * c'.degree := by
  rw [← not_le, slope_le_slope_iff hc' hc, not_le]

/-- **See-saw**: if `c'` is nonzero effective, then `μ(c) ≤ μ(c + c')` if and only if
`μ(c) ≤ μ(c')`. When `c` has rank zero, both sides say that `c'` has rank zero. -/
theorem slope_le_slope_add_iff (hc' : c'.IsNonzeroEffective) :
    c.slope ≤ (c + c').slope ↔ c.slope ≤ c'.slope := by
  by_cases h : c.rank = 0
  · simp [slope_of_rank_eq_zero h, h]
  have hc : c.IsNonzeroEffective := .of_rank_ne_zero h
  rw [slope_le_slope_iff hc (hc.add hc'), slope_le_slope_iff hc hc', rank_add, degree_add]
  push_cast
  constructor <;> intro <;> linarith

/-- **See-saw**: if `c` is nonzero effective, then `μ(c + c') ≤ μ(c')` if and only if
`μ(c) ≤ μ(c')`. When `c'` has rank zero, both sides hold. -/
theorem slope_add_le_slope_iff (hc : c.IsNonzeroEffective) :
    (c + c').slope ≤ c'.slope ↔ c.slope ≤ c'.slope := by
  by_cases h : c'.rank = 0
  · simp [slope_of_rank_eq_zero h]
  have hc' : c'.IsNonzeroEffective := .of_rank_ne_zero h
  rw [slope_le_slope_iff (hc.add hc') hc', slope_le_slope_iff hc hc', rank_add, degree_add]
  push_cast
  constructor <;> intro <;> linarith

/-- **See-saw**, strict form: if `c'` is nonzero effective, then `μ(c) < μ(c + c')` if and only
if `μ(c) < μ(c')`. -/
theorem slope_lt_slope_add_iff (hc' : c'.IsNonzeroEffective) :
    c.slope < (c + c').slope ↔ c.slope < c'.slope := by
  rw [← not_le, ← not_le, add_comm, slope_add_le_slope_iff hc']

/-- **See-saw**, strict form: if `c` is nonzero effective, then `μ(c + c') < μ(c')` if and only
if `μ(c) < μ(c')`. -/
theorem slope_add_lt_slope_iff (hc : c.IsNonzeroEffective) :
    (c + c').slope < c'.slope ↔ c.slope < c'.slope := by
  rw [← not_le, ← not_le, add_comm, slope_le_slope_add_iff hc]

/-- The slope of a sum of nonzero effective classes is at least the smaller of their slopes. -/
theorem min_slope_le_slope_add (hc : c.IsNonzeroEffective) (hc' : c'.IsNonzeroEffective) :
    min c.slope c'.slope ≤ (c + c').slope := by
  rcases le_total c.slope c'.slope with h | h
  · exact (min_le_left _ _).trans ((slope_le_slope_add_iff hc').2 h)
  · rw [add_comm]
    exact (min_le_right _ _).trans ((slope_le_slope_add_iff hc).2 h)

/-- The slope of a sum of classes is at most the larger of their slopes. -/
theorem slope_add_le_max_slope (c c' : CurveSheafClass) :
    (c + c').slope ≤ max c.slope c'.slope := by
  by_cases h : c.rank = 0
  · simp [slope_of_rank_eq_zero h]
  by_cases h' : c'.rank = 0
  · simp [slope_of_rank_eq_zero h']
  rcases le_total c.slope c'.slope with hle | hle
  · exact ((slope_add_le_slope_iff (.of_rank_ne_zero h)).2 hle).trans
      (le_max_right _ _)
  · rw [add_comm]
    exact ((slope_add_le_slope_iff (.of_rank_ne_zero h')).2 hle).trans
      (le_max_left _ _)

/-- A nonzero effective class has nonnegative slope exactly when its degree is nonnegative. -/
theorem slope_nonneg_iff (hc : c.IsNonzeroEffective) : 0 ≤ c.slope ↔ 0 ≤ c.degree := by
  by_cases h : c.rank = 0
  · simp [slope_of_rank_eq_zero h, (hc.degree_pos_of_rank_eq_zero h).le]
  · rw [slope_of_rank_ne_zero h, ← WithTop.coe_zero, WithTop.coe_le_coe]
    have : (0 : ℚ) < c.rank := by positivity
    rw [le_div_iff₀ this, zero_mul]
    exact_mod_cast Iff.rfl

/-! ### Twisting by a line bundle -/

/-- The class `(rk c, deg c + a rk c)` of `F ⊗ L` for a sheaf `F` of class `c` and a line bundle
`L` of degree `a`. -/
def twist (a : ℤ) (c : CurveSheafClass) : CurveSheafClass :=
  ⟨c.rank, c.degree + c.rank * a⟩

@[simp]
theorem rank_twist (a : ℤ) (c : CurveSheafClass) : (twist a c).rank = c.rank := (rfl)

@[simp]
theorem degree_twist (a : ℤ) (c : CurveSheafClass) :
    (twist a c).degree = c.degree + c.rank * a := (rfl)

@[simp]
theorem twist_zero (c : CurveSheafClass) : twist 0 c = c := by
  ext <;> simp

@[simp]
theorem twist_twist (a b : ℤ) (c : CurveSheafClass) : twist a (twist b c) = twist (a + b) c := by
  ext <;> simp only [rank_twist, degree_twist]
  ring

theorem twist_add (a : ℤ) (c c' : CurveSheafClass) :
    twist a (c + c') = twist a c + twist a c' := by
  ext <;> simp only [rank_twist, degree_twist, rank_add, degree_add]
  push_cast
  ring

@[simp]
theorem isNonzeroEffective_twist (a : ℤ) :
    (twist a c).IsNonzeroEffective ↔ c.IsNonzeroEffective := by
  simp only [isNonzeroEffective_iff, rank_twist, degree_twist]
  rcases Nat.eq_zero_or_pos c.rank with h | h <;> simp [h]

/-- Twisting by a line bundle of degree `a` adds `a` to the slope. -/
@[simp]
theorem slope_twist (a : ℤ) (c : CurveSheafClass) :
    (twist a c).slope = c.slope + ((a : ℚ) : WithTop ℚ) := by
  by_cases h : c.rank = 0
  · rw [slope_of_rank_eq_zero h, slope_of_rank_eq_zero (by simpa using h), WithTop.top_add]
  · rw [slope_of_rank_ne_zero (by simpa using h), slope_of_rank_ne_zero h, ← WithTop.coe_add,
      rank_twist, degree_twist]
    congr 1
    have : (c.rank : ℚ) ≠ 0 := by exact_mod_cast h
    field_simp
    push_cast
    ring

/-! ### The Euler form -/

/-- The Euler form `χ(c, c') = (1 - g) rk c rk c' + rk c deg c' - rk c' deg c` on classes of
coherent sheaves on a curve of genus `g`. By Riemann–Roch and Serre duality on a smooth projective
geometrically connected curve of genus `g` over a field, this is
`dim Hom(F, F') - dim Ext¹(F, F')` for coherent sheaves `F` and `F'` of classes `c` and `c'`. -/
def eulerForm (g : ℕ) (c c' : CurveSheafClass) : ℤ :=
  (1 - g) * c.rank * c'.rank + c.rank * c'.degree - c'.rank * c.degree

theorem eulerForm_def (g : ℕ) (c c' : CurveSheafClass) :
    eulerForm g c c' = (1 - g) * c.rank * c'.rank + c.rank * c'.degree - c'.rank * c.degree :=
  (rfl)

@[simp]
theorem eulerForm_zero_left (g : ℕ) (c : CurveSheafClass) : eulerForm g 0 c = 0 := by
  simp [eulerForm_def]

@[simp]
theorem eulerForm_zero_right (g : ℕ) (c : CurveSheafClass) : eulerForm g c 0 = 0 := by
  simp [eulerForm_def]

theorem eulerForm_add_left (g : ℕ) (c₁ c₂ c' : CurveSheafClass) :
    eulerForm g (c₁ + c₂) c' = eulerForm g c₁ c' + eulerForm g c₂ c' := by
  simp only [eulerForm_def, rank_add, degree_add]
  push_cast
  ring

theorem eulerForm_add_right (g : ℕ) (c c₁ c₂ : CurveSheafClass) :
    eulerForm g c (c₁ + c₂) = eulerForm g c c₁ + eulerForm g c c₂ := by
  simp only [eulerForm_def, rank_add, degree_add]
  push_cast
  ring

/-- **Riemann–Roch**, numerically: `χ(𝒪_X, c) = deg c + (1 - g) rk c`. -/
theorem eulerForm_structureSheaf_left (g : ℕ) (c : CurveSheafClass) :
    eulerForm g ⟨1, 0⟩ c = c.degree + (1 - g) * c.rank := by
  simp only [eulerForm_def]
  push_cast
  ring

/-- The Euler form of a class with itself depends only on the rank: `χ(c, c) = (1 - g) rk c ²`. -/
theorem eulerForm_self (g : ℕ) (c : CurveSheafClass) :
    eulerForm g c c = (1 - g) * c.rank ^ 2 := by
  simp only [eulerForm_def]
  ring

/-- The antisymmetric part of the Euler form: `χ(c, c') - χ(c', c) = 2 (rk c deg c' - rk c' deg c)`.
-/
theorem eulerForm_sub_eulerForm_swap (g : ℕ) (c c' : CurveSheafClass) :
    eulerForm g c c' - eulerForm g c' c = 2 * (c.rank * c'.degree - c'.rank * c.degree) := by
  simp only [eulerForm_def]
  ring

/-- The Euler form is invariant under twisting both classes by the same line bundle. -/
@[simp]
theorem eulerForm_twist (g : ℕ) (a : ℤ) (c c' : CurveSheafClass) :
    eulerForm g (twist a c) (twist a c') = eulerForm g c c' := by
  simp only [eulerForm_def, rank_twist, degree_twist]
  ring

/-- Twisting the first class by a line bundle of degree `a` is twisting the second by its
inverse: `χ(c ⊗ L, c') = χ(c, c' ⊗ L⁻¹)`. -/
theorem eulerForm_twist_left (g : ℕ) (a : ℤ) (c c' : CurveSheafClass) :
    eulerForm g (twist a c) c' = eulerForm g c (twist (-a) c') := by
  simp only [eulerForm_def, rank_twist, degree_twist]
  ring

/-- **Serre duality**, numerically: `χ(c', c ⊗ ω) = -χ(c, c')` for a canonical bundle `ω` of
degree `2g - 2`. -/
theorem eulerForm_twist_swap (g : ℕ) (c c' : CurveSheafClass) :
    eulerForm g c' (twist (2 * g - 2) c) = -eulerForm g c c' := by
  simp only [eulerForm_def, rank_twist, degree_twist]
  ring

/-- For nonzero effective classes, `χ(c, c') ≤ (1 - g) rk c rk c'` exactly when
`μ(c') ≤ μ(c)`. -/
theorem eulerForm_le_iff_slope_le (g : ℕ) (hc : c.IsNonzeroEffective)
    (hc' : c'.IsNonzeroEffective) :
    eulerForm g c c' ≤ (1 - g) * c.rank * c'.rank ↔ c'.slope ≤ c.slope := by
  rw [slope_le_slope_iff hc' hc, eulerForm_def]
  constructor <;> intro <;> linarith

/-- For nonzero effective classes, `χ(c, c') < (1 - g) rk c rk c'` exactly when
`μ(c') < μ(c)`. -/
theorem eulerForm_lt_iff_slope_lt (g : ℕ) (hc : c.IsNonzeroEffective)
    (hc' : c'.IsNonzeroEffective) :
    eulerForm g c c' < (1 - g) * c.rank * c'.rank ↔ c'.slope < c.slope := by
  rw [slope_lt_slope_iff hc' hc, eulerForm_def]
  constructor <;> intro <;> linarith

/-! ### Harder–Narasimhan types -/

/-- A *Harder–Narasimhan type*: a list of nonzero effective classes with strictly decreasing
slopes. The classes of the successive quotients of the Harder–Narasimhan filtration of a
coherent sheaf on a curve form such a list; the zero sheaf has the empty type. -/
@[ext]
structure HNType where
  /-- The classes of the successive quotients, in order. -/
  classes : List CurveSheafClass
  /-- Every quotient is nonzero. -/
  isNonzeroEffective : ∀ c ∈ classes, c.IsNonzeroEffective
  /-- The slopes of the quotients decrease strictly. -/
  pairwise_slope_lt : classes.Pairwise fun c c' ↦ c'.slope < c.slope

namespace HNType

/-- The total class of a Harder–Narasimhan type, the class of the filtered sheaf. -/
def total (τ : HNType) : CurveSheafClass :=
  τ.classes.sum

theorem total_def (τ : HNType) : τ.total = τ.classes.sum :=
  (rfl)

theorem classes_injective : Function.Injective HNType.classes :=
  fun _ _ ↦ HNType.ext

/-- The classes of a Harder–Narasimhan type are pairwise distinct. -/
theorem nodup_classes (τ : HNType) : τ.classes.Nodup :=
  τ.pairwise_slope_lt.imp fun h heq ↦ by subst heq; exact lt_irrefl _ h

/-- Each class of a Harder–Narasimhan type with nonnegative slopes has rank at most the total
rank and degree between zero and the total degree. -/
private theorem bounds_of_mem_classes {τ : HNType} (hτ : ∀ a ∈ τ.classes, 0 ≤ a.slope)
    {a : CurveSheafClass} (ha : a ∈ τ.classes) :
    a.rank ≤ τ.total.rank ∧ 0 ≤ a.degree ∧ a.degree ≤ τ.total.degree := by
  have hdeg : ∀ b ∈ τ.classes, 0 ≤ b.degree := fun b hb ↦
    (slope_nonneg_iff (τ.isNonzeroEffective b hb)).1 (hτ b hb)
  refine ⟨?_, hdeg a ha, ?_⟩
  · rw [total_def, rank_list_sum]
    exact List.le_sum_of_mem (List.mem_map_of_mem ha)
  · rw [total_def, degree_list_sum]
    exact List.single_le_sum (by simpa using hdeg) _ (List.mem_map_of_mem ha)

/-- For a fixed class `c`, only finitely many Harder–Narasimhan types with nonnegative slopes
have total class `c`. -/
theorem finite_setOf_total_eq_and_slope_nonneg (c : CurveSheafClass) :
    {τ : HNType | τ.total = c ∧ ∀ a ∈ τ.classes, 0 ≤ a.slope}.Finite := by
  -- The possible classes of the quotients form a finite set `S`.
  set S : Set CurveSheafClass :=
    (fun a ↦ (a.rank, a.degree)) ⁻¹' (Set.Iic c.rank ×ˢ Set.Icc 0 c.degree) with hS_def
  have hS : S.Finite :=
    ((Set.finite_Iic c.rank).prod (Set.finite_Icc 0 c.degree)).preimage fun a _ b _ h ↦ by
      ext <;> simp_all [Prod.ext_iff]
  let : Fintype S := hS.fintype
  -- A list of distinct elements of `S` has length at most `|S|`.
  have hT : {l : List CurveSheafClass | l.Nodup ∧ ∀ a ∈ l, a ∈ S}.Finite := by
    refine ((List.finite_length_le S (Fintype.card S)).image (List.map Subtype.val)).subset ?_
    rintro l ⟨hnd, hl⟩
    exact ⟨l.attachWith (· ∈ S) hl, (List.nodup_attachWith.2 hnd).length_le_card,
      List.attachWith_map_subtype_val hl⟩
  refine (hT.preimage classes_injective.injOn).subset ?_
  rintro τ ⟨rfl, hτ⟩
  refine ⟨τ.nodup_classes, fun a ha ↦ ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := bounds_of_mem_classes hτ ha
  simp [hS_def, h₁, h₂, h₃]

end HNType

/-! ### Examples -/

/-- On the projective line, `𝒪(2) ⊕ 𝒪(-1)` has Harder–Narasimhan type `[(1, 2), (1, -1)]`, with
slopes `2 > -1` in this order; the reversed order is not a type. -/
example : ([⟨1, 2⟩, ⟨1, -1⟩] : List CurveSheafClass).Pairwise (fun c c' ↦ c'.slope < c.slope) ∧
    ¬ ([⟨1, -1⟩, ⟨1, 2⟩] : List CurveSheafClass).Pairwise (fun c c' ↦ c'.slope < c.slope) := by
  have h : (⟨1, -1⟩ : CurveSheafClass).slope < (⟨1, 2⟩ : CurveSheafClass).slope :=
    (slope_lt_slope_iff (.of_rank_pos one_pos) (.of_rank_pos one_pos)).2 (by norm_num)
  simp only [List.pairwise_pair]
  exact ⟨h, lt_asymm h⟩

/-- A skyscraper of length one at a point of degree `3` has class `(0, 3)` and slope `⊤`, as
does the zero class `(0, 0)`, while `(2, 1)` has slope `1 / 2`. -/
example : (⟨0, 3⟩ : CurveSheafClass).slope = ⊤ ∧ (⟨0, 0⟩ : CurveSheafClass).slope = ⊤ ∧
    (⟨2, 1⟩ : CurveSheafClass).slope = ((1 / 2 : ℚ) : WithTop ℚ) := by
  refine ⟨slope_of_rank_eq_zero rfl, slope_of_rank_eq_zero rfl, ?_⟩
  rw [slope_of_rank_ne_zero (by decide)]
  norm_num

/-- `χ(𝒪, 𝒪) = 1 - g`; on the projective line `χ(𝒪, 𝒪(1)) = 2` while `χ(𝒪(1), 𝒪) = 0`. -/
example (g : ℕ) : eulerForm g ⟨1, 0⟩ ⟨1, 0⟩ = 1 - g ∧ eulerForm 0 ⟨1, 0⟩ ⟨1, 1⟩ = 2 ∧
    eulerForm 0 ⟨1, 1⟩ ⟨1, 0⟩ = 0 := by
  simp [eulerForm_def]

end CurveSheafClass

end TauCeti
