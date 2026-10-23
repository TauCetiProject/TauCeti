/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Support
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.Set.Finite.Lemmas

/-!
# Novikov series

Let `H` be an additive group and `N : H →+ ℝ` a period homomorphism. A *Novikov series* with
coefficients in `R` is a coefficient function `a : H → R` with only finitely many nonzero
coefficients below every real period cutoff: `{h | a h ≠ 0 ∧ N h < C}` is finite for every
`C : ℝ`. Under convolution, these series form the Novikov completion of the group ring `R[H]`
along the period filtration; it is the coefficient ring of the Novikov complex of a closed
one-form whose periods are recorded by `N`.

Neither injectivity nor discreteness of `N` is assumed: finitely many nonzero coefficients may
share a period value, and the periods of an infinite support tend to `+∞`.

This file sets up the carrier and its additive structure, the monomials, and the finiteness facts
on which the convolution product of `TauCeti.RingTheory.NovikovSeries.Multiplication` rests. The
design of the additive API follows that of Mathlib's `HahnSeries` in
`Mathlib/RingTheory/HahnSeries/Addition.lean`; no code is copied from there.

## Main definitions

* `TauCeti.NovikovSeries R H N`: Novikov series over `R` on `H` for the period map `N`.
* `TauCeti.NovikovSeries.ofFinsupp`: a finitely supported coefficient function as a Novikov
  series.
* `TauCeti.NovikovSeries.single`: the monomial `r e^h`, with coefficient `r` at `h` and `0`
  elsewhere.
* `TauCeti.NovikovSeries.order`: the least period of the support of a Novikov series, and `0` for
  the zero series.
* `TauCeti.NovikovSeries.trunc C a`: the finitely supported truncation of `a` below the period
  cutoff `C`.

## Main results

* `TauCeti.NovikovSeries.forall_finite_lt_iff_forall_finite_le`: the support condition may be
  stated with `N h ≤ C` in place of `N h < C`.
* `TauCeti.NovikovSeries.bddBelow_image_support` and
  `TauCeti.NovikovSeries.exists_isLeast_image_support`: the periods of the support are bounded
  below, and a nonzero series attains a least period on its support.
* `TauCeti.NovikovSeries.isLeast_order`: the order of a nonzero series is the least period of its
  support.
* `TauCeti.NovikovSeries.forall_finite_lt_iff_bddBelow_support`: on `ℤ` with the period map
  `k ↦ k`, the support condition says exactly that the support is bounded below.
* `TauCeti.NovikovSeries.finite_setOf_period_add_lt`: for two Novikov series, the pairs of
  support exponents whose sum has period below a fixed cutoff form a finite set. In particular
  (`TauCeti.NovikovSeries.finite_setOf_add_eq`) each coefficient of the convolution is a finite
  sum.
* `TauCeti.NovikovSeries.finite_setOf_period_add_add_lt` and
  `TauCeti.NovikovSeries.finite_setOf_add_add_eq`: the same uniform cutoff finiteness for triples
  of support exponents, on which associativity of the convolution rests.
* `TauCeti.NovikovSeries.ofFinsupp_surjective_iff`: over a nontrivial coefficient type, every
  Novikov series is finitely supported if and only if `N = 0`.

## References

* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory and Reidemeister torsion*,
  Geom. Topol. 3 (1999), Section 2.
* A. Pajitnov, *Circle-valued Morse Theory*, de Gruyter 2006, Chapter 3.
-/

public section

noncomputable section

open Function Set

namespace TauCeti

/-- A Novikov series over `R` on the additive group `H`, for the period homomorphism
`N : H →+ ℝ`: a coefficient function `H → R` with only finitely many nonzero coefficients below
each real period cutoff. -/
structure NovikovSeries (R H : Type*) [Zero R] [AddZeroClass H] (N : H →+ ℝ) where
  /-- The coefficient of a Novikov series at an exponent. -/
  coeff : H → R
  /-- Only finitely many coefficients are nonzero below each period cutoff. -/
  finite_lt : ∀ C : ℝ, {h | coeff h ≠ 0 ∧ N h < C}.Finite

namespace NovikovSeries

section Zero

variable {R H : Type*} [Zero R] [AddZeroClass H] {N : H →+ ℝ}

theorem coeff_injective : Injective (coeff : NovikovSeries R H N → H → R) := by
  rintro ⟨a, _⟩ ⟨b, _⟩ rfl
  rfl

@[ext]
theorem ext {a b : NovikovSeries R H N} (h : ∀ g, a.coeff g = b.coeff g) : a = b :=
  coeff_injective (funext h)

/-- The support of a Novikov series: the exponents with nonzero coefficient. -/
def support (a : NovikovSeries R H N) : Set H :=
  Function.support a.coeff

@[simp]
theorem mem_support {a : NovikovSeries R H N} {h : H} : h ∈ a.support ↔ a.coeff h ≠ 0 :=
  Iff.rfl

/-- The support condition of Novikov series is equivalent to the one with non-strict
period cutoffs. -/
theorem forall_finite_lt_iff_forall_finite_le (f : H → R) :
    (∀ C : ℝ, {h | f h ≠ 0 ∧ N h < C}.Finite) ↔ ∀ C : ℝ, {h | f h ≠ 0 ∧ N h ≤ C}.Finite :=
  ⟨fun hf C => (hf (C + 1)).subset fun _ hh => ⟨hh.1, hh.2.trans_lt (lt_add_one C)⟩,
    fun hf C => (hf C).subset fun _ hh => ⟨hh.1, hh.2.le⟩⟩

theorem finite_le (a : NovikovSeries R H N) (C : ℝ) :
    {h | a.coeff h ≠ 0 ∧ N h ≤ C}.Finite :=
  (forall_finite_lt_iff_forall_finite_le a.coeff).1 a.finite_lt C

/-- The periods of the support of a Novikov series are bounded below. -/
theorem bddBelow_image_support (a : NovikovSeries R H N) : BddBelow (N '' a.support) := by
  obtain ⟨m, hm⟩ := ((a.finite_lt 0).image N).bddBelow
  refine ⟨min m 0, ?_⟩
  rintro _ ⟨h, hh, rfl⟩
  rcases lt_or_ge (N h) 0 with hN | hN
  · exact (min_le_left _ _).trans (hm ⟨h, ⟨hh, hN⟩, rfl⟩)
  · exact (min_le_right _ _).trans hN

/-- A Novikov series with nonempty support attains a least period on its support. -/
theorem exists_isLeast_image_support {a : NovikovSeries R H N} (ha : a.support.Nonempty) :
    ∃ h ∈ a.support, IsLeast (N '' a.support) (N h) := by
  obtain ⟨h₀, hh₀⟩ := ha
  obtain ⟨h, hh, hmin⟩ := exists_min_image _ N (a.finite_le (N h₀)) ⟨h₀, hh₀, le_rfl⟩
  refine ⟨h, hh.1, ⟨h, hh.1, rfl⟩, ?_⟩
  rintro _ ⟨g, hg, rfl⟩
  rcases le_total (N g) (N h₀) with hgh₀ | hgh₀
  · exact hmin g ⟨hg, hgh₀⟩
  · exact hh.2.trans hgh₀

/-- On the exponent group `ℤ` with the period map `k ↦ k`, a coefficient function has only
finitely many nonzero coefficients below every real cutoff if and only if its support is bounded
below. -/
theorem forall_finite_lt_iff_bddBelow_support (f : ℤ → R) :
    (∀ C : ℝ, {k : ℤ | f k ≠ 0 ∧ Int.castAddHom ℝ k < C}.Finite) ↔
      BddBelow (Function.support f) := by
  refine ⟨fun hf => ?_, fun ⟨m, hm⟩ C => ?_⟩
  · obtain ⟨m, hm⟩ := (hf 0).bddBelow
    refine ⟨min m 0, fun k hk => ?_⟩
    rcases lt_or_ge k 0 with hk₀ | hk₀
    · exact (min_le_left _ _).trans (hm ⟨hk, by simpa using hk₀⟩)
    · exact (min_le_right _ _).trans hk₀
  · refine (finite_Icc m ⌈C⌉).subset fun k hk => ⟨hm hk.1, ?_⟩
    have hkC : (k : ℝ) < C := by simpa using hk.2
    exact Int.cast_le.1 (hkC.le.trans (Int.le_ceil C))

/-- The support of a Novikov series on `ℤ` for the period map `k ↦ k` is bounded below. -/
theorem bddBelow_support_int (a : NovikovSeries R ℤ (Int.castAddHom ℝ)) :
    BddBelow a.support :=
  (forall_finite_lt_iff_bddBelow_support a.coeff).1 a.finite_lt |>.mono fun _ => mem_support.1

/-- The zero Novikov series. -/
instance : Zero (NovikovSeries R H N) :=
  ⟨⟨0, fun C => by simp⟩⟩

@[simp]
theorem coeff_zero' : (0 : NovikovSeries R H N).coeff = 0 :=
  rfl

theorem coeff_zero (h : H) : (0 : NovikovSeries R H N).coeff h = 0 :=
  rfl

@[simp]
theorem support_zero : (0 : NovikovSeries R H N).support = ∅ :=
  Function.support_zero

@[simp]
theorem support_eq_empty {a : NovikovSeries R H N} : a.support = ∅ ↔ a = 0 := by
  rw [support, Function.support_eq_empty_iff, ← coeff_zero', coeff_injective.eq_iff]

theorem support_nonempty_iff {a : NovikovSeries R H N} : a.support.Nonempty ↔ a ≠ 0 := by
  rw [nonempty_iff_ne_empty, Ne, support_eq_empty]

instance : Inhabited (NovikovSeries R H N) :=
  ⟨0⟩

end Zero

section Convolution

variable {R S H : Type*} [Zero R] [Zero S] [AddZeroClass H] {N : H →+ ℝ}

/-- Uniform cutoff finiteness for convolution: for Novikov series `a` and `b`, only finitely many
pairs `(u, v)` of support exponents have `N (u + v) < C`. -/
theorem finite_setOf_period_add_lt (a : NovikovSeries R H N) (b : NovikovSeries S H N)
    (C : ℝ) :
    {p : H × H | N (p.1 + p.2) < C ∧ a.coeff p.1 ≠ 0 ∧ b.coeff p.2 ≠ 0}.Finite := by
  obtain ⟨ma, hma⟩ := a.bddBelow_image_support
  obtain ⟨mb, hmb⟩ := b.bddBelow_image_support
  refine ((a.finite_lt (C - mb)).prod (b.finite_lt (C - ma))).subset ?_
  rintro ⟨u, v⟩ ⟨huv, hu, hv⟩
  have hu' : ma ≤ N u := hma ⟨u, hu, rfl⟩
  have hv' : mb ≤ N v := hmb ⟨v, hv, rfl⟩
  rw [map_add] at huv
  exact ⟨⟨hu, by linarith⟩, ⟨hv, by linarith⟩⟩

/-- For Novikov series `a` and `b` and an exponent `h`, only finitely many pairs `(u, v)` with
`u + v = h` have both coefficients `a.coeff u` and `b.coeff v` nonzero. -/
theorem finite_setOf_add_eq (a : NovikovSeries R H N) (b : NovikovSeries S H N) (h : H) :
    {p : H × H | p.1 + p.2 = h ∧ a.coeff p.1 ≠ 0 ∧ b.coeff p.2 ≠ 0}.Finite :=
  (finite_setOf_period_add_lt a b (N h + 1)).subset fun p hp =>
    ⟨by rw [hp.1]; exact lt_add_one _, hp.2⟩

/-- For Novikov series `a` and `b` and an exponent `h`, only finitely many pairs `(u, v)` with
`u + v = h` have nonzero coefficient product `a.coeff u * b.coeff v`. -/
theorem finite_setOf_add_eq_mul_ne_zero {R : Type*} [MulZeroClass R]
    (a b : NovikovSeries R H N) (h : H) :
    {p : H × H | p.1 + p.2 = h ∧ a.coeff p.1 * b.coeff p.2 ≠ 0}.Finite :=
  (finite_setOf_add_eq a b h).subset fun _ hp =>
    ⟨hp.1, left_ne_zero_of_mul hp.2, right_ne_zero_of_mul hp.2⟩

/-- Uniform cutoff finiteness for triple products: for Novikov series `a`, `b` and `c`, only
finitely many triples `(u, v, w)` of support exponents have `N (u + v + w) < C`. -/
theorem finite_setOf_period_add_add_lt {T : Type*} [Zero T] (a : NovikovSeries R H N)
    (b : NovikovSeries S H N) (c : NovikovSeries T H N) (C : ℝ) :
    {t : H × H × H | N (t.1 + t.2.1 + t.2.2) < C ∧ a.coeff t.1 ≠ 0 ∧ b.coeff t.2.1 ≠ 0 ∧
      c.coeff t.2.2 ≠ 0}.Finite := by
  obtain ⟨ma, hma⟩ := a.bddBelow_image_support
  obtain ⟨mb, hmb⟩ := b.bddBelow_image_support
  obtain ⟨mc, hmc⟩ := c.bddBelow_image_support
  refine ((a.finite_lt (C - mb - mc)).prod
    ((b.finite_lt (C - ma - mc)).prod (c.finite_lt (C - ma - mb)))).subset ?_
  rintro ⟨u, v, w⟩ ⟨huvw, hu, hv, hw⟩
  have hu' : ma ≤ N u := hma ⟨u, hu, rfl⟩
  have hv' : mb ≤ N v := hmb ⟨v, hv, rfl⟩
  have hw' : mc ≤ N w := hmc ⟨w, hw, rfl⟩
  rw [map_add, map_add] at huvw
  exact ⟨⟨hu, by linarith⟩, ⟨hv, by linarith⟩, ⟨hw, by linarith⟩⟩

/-- For Novikov series `a`, `b` and `c` and an exponent `h`, only finitely many triples
`(u, v, w)` with `u + v + w = h` have all three coefficients nonzero. -/
theorem finite_setOf_add_add_eq {T : Type*} [Zero T] (a : NovikovSeries R H N)
    (b : NovikovSeries S H N) (c : NovikovSeries T H N) (h : H) :
    {t : H × H × H | t.1 + t.2.1 + t.2.2 = h ∧ a.coeff t.1 ≠ 0 ∧ b.coeff t.2.1 ≠ 0 ∧
      c.coeff t.2.2 ≠ 0}.Finite :=
  (finite_setOf_period_add_add_lt a b c (N h + 1)).subset fun t ht =>
    ⟨by rw [ht.1]; exact lt_add_one _, ht.2⟩

end Convolution

section Additive

variable {R S H : Type*} [AddZeroClass H] {N : H →+ ℝ}

section SMulZeroClass

variable [Zero R] [SMulZeroClass S R]

/-- Coefficientwise scalar multiplication of a Novikov series. -/
instance : SMul S (NovikovSeries R H N) :=
  ⟨fun s a => ⟨s • a.coeff, fun C => (a.finite_lt C).subset fun _ hh =>
    ⟨right_ne_zero_of_smul hh.1, hh.2⟩⟩⟩

@[simp]
theorem coeff_smul' (s : S) (a : NovikovSeries R H N) : (s • a).coeff = s • a.coeff :=
  rfl

theorem coeff_smul (s : S) (a : NovikovSeries R H N) (h : H) :
    (s • a).coeff h = s • a.coeff h :=
  rfl

theorem support_smul_subset (s : S) (a : NovikovSeries R H N) : (s • a).support ⊆ a.support :=
  Function.support_const_smul_subset s a.coeff

end SMulZeroClass

section AddZeroClass

variable [AddZeroClass R]

/-- Coefficientwise addition of Novikov series. -/
instance : Add (NovikovSeries R H N) :=
  ⟨fun a b => ⟨a.coeff + b.coeff, fun C => ((a.finite_lt C).union (b.finite_lt C)).subset
    fun h hh => by
      by_contra hab
      simp_all⟩⟩

@[simp]
theorem coeff_add' (a b : NovikovSeries R H N) : (a + b).coeff = a.coeff + b.coeff :=
  rfl

theorem coeff_add (a b : NovikovSeries R H N) (h : H) :
    (a + b).coeff h = a.coeff h + b.coeff h :=
  rfl

theorem support_add_subset (a b : NovikovSeries R H N) :
    (a + b).support ⊆ a.support ∪ b.support :=
  Function.support_add a.coeff b.coeff

end AddZeroClass

instance [AddMonoid R] : AddMonoid (NovikovSeries R H N) :=
  coeff_injective.addMonoid _ coeff_zero' coeff_add' fun _ _ => coeff_smul' _ _

instance [AddCommMonoid R] : AddCommMonoid (NovikovSeries R H N) :=
  coeff_injective.addCommMonoid _ coeff_zero' coeff_add' fun _ _ => coeff_smul' _ _

section NegZeroClass

variable [NegZeroClass R]

/-- Coefficientwise negation of a Novikov series. -/
instance : Neg (NovikovSeries R H N) :=
  ⟨fun a => ⟨-a.coeff, fun C => (a.finite_lt C).subset fun _ hh =>
    ⟨fun h => hh.1 (by simp [h]), hh.2⟩⟩⟩

@[simp]
theorem coeff_neg' (a : NovikovSeries R H N) : (-a).coeff = -a.coeff :=
  rfl

theorem coeff_neg (a : NovikovSeries R H N) (h : H) : (-a).coeff h = -a.coeff h :=
  rfl

end NegZeroClass

section AddGroup

variable [AddGroup R]

/-- Coefficientwise subtraction of Novikov series. -/
instance : Sub (NovikovSeries R H N) :=
  ⟨fun a b => ⟨a.coeff - b.coeff, fun C => ((a.finite_lt C).union (b.finite_lt C)).subset
    fun h hh => by
      by_contra hab
      simp_all⟩⟩

@[simp]
theorem coeff_sub' (a b : NovikovSeries R H N) : (a - b).coeff = a.coeff - b.coeff :=
  rfl

theorem coeff_sub (a b : NovikovSeries R H N) (h : H) :
    (a - b).coeff h = a.coeff h - b.coeff h :=
  rfl

@[simp]
theorem support_neg (a : NovikovSeries R H N) : (-a).support = a.support :=
  Function.support_neg a.coeff

theorem support_sub_subset (a b : NovikovSeries R H N) :
    (a - b).support ⊆ a.support ∪ b.support :=
  Function.support_sub a.coeff b.coeff

instance : AddGroup (NovikovSeries R H N) :=
  coeff_injective.addGroup _ coeff_zero' coeff_add' coeff_neg' coeff_sub'
    (fun _ _ => coeff_smul' _ _) fun _ _ => coeff_smul' _ _

end AddGroup

instance [AddCommGroup R] : AddCommGroup (NovikovSeries R H N) :=
  coeff_injective.addCommGroup _ coeff_zero' coeff_add' coeff_neg' coeff_sub'
    (fun _ _ => coeff_smul' _ _) fun _ _ => coeff_smul' _ _

/-- The coefficient function of Novikov series, as an additive monoid homomorphism. -/
def coeffAddMonoidHom [AddMonoid R] : NovikovSeries R H N →+ (H → R) where
  toFun := coeff
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem coeffAddMonoidHom_apply [AddMonoid R] (a : NovikovSeries R H N) :
    coeffAddMonoidHom a = a.coeff := by
  rfl

instance [Semiring S] [AddCommMonoid R] [Module S R] : Module S (NovikovSeries R H N) :=
  (funext (coeffAddMonoidHom_apply (R := R) (N := N)) ▸ coeff_injective).module S coeffAddMonoidHom
    fun _ _ => by simp

end Additive

section ofFinsupp

variable {R H : Type*} [AddZeroClass H] {N : H →+ ℝ} [AddMonoid R]

/-- A finitely supported coefficient function, viewed as a Novikov series. -/
def ofFinsupp : (H →₀ R) →+ NovikovSeries R H N where
  toFun f := ⟨f, fun _ => f.hasFiniteSupport.subset fun _ hh => hh.1⟩
  map_zero' := rfl
  map_add' _ _ := by
    ext
    simp

@[simp]
theorem coeff_ofFinsupp (f : H →₀ R) : (ofFinsupp (N := N) f).coeff = f := by
  rfl

@[simp]
theorem support_ofFinsupp (f : H →₀ R) : (ofFinsupp (N := N) f).support = f.support :=
  Finsupp.fun_support_eq f

@[simp]
theorem ofFinsupp_smul {S : Type*} [SMulZeroClass S R] (s : S) (f : H →₀ R) :
    ofFinsupp (N := N) (s • f) = s • ofFinsupp f := by
  ext
  simp

theorem ofFinsupp_injective : Injective (ofFinsupp (R := R) (N := N)) := fun _ _ h =>
  DFunLike.coe_injective (congrArg coeff h)

theorem mem_range_ofFinsupp_iff {a : NovikovSeries R H N} :
    a ∈ range (ofFinsupp (N := N)) ↔ a.support.Finite := by
  refine ⟨?_, fun ha => ⟨Finsupp.ofSupportFinite a.coeff ha, coeff_injective rfl⟩⟩
  rintro ⟨f, rfl⟩
  simp

end ofFinsupp

section Single

variable {R H : Type*} [AddZeroClass H] {N : H →+ ℝ}

section Zero

variable [Zero R]

open scoped Classical in
/-- The monomial `r e^h`: the Novikov series with coefficient `r` at `h` and `0` elsewhere. -/
def single (h : H) (r : R) : NovikovSeries R H N where
  coeff := Pi.single h r
  finite_lt _ := (finite_singleton h).subset fun _ hg => mem_singleton_iff.2 <| by
    by_contra hgh
    exact hg.1 (by simp [hgh])

theorem coeff_single [DecidableEq H] (h : H) (r : R) :
    (single h r : NovikovSeries R H N).coeff = Pi.single h r := by
  ext g
  simp only [single, Pi.single_apply]
  congr

@[simp]
theorem coeff_single_same (h : H) (r : R) : (single h r : NovikovSeries R H N).coeff h = r := by
  classical
  rw [coeff_single, Pi.single_eq_same]

@[simp]
theorem coeff_single_of_ne {g h : H} (hgh : g ≠ h) (r : R) :
    (single h r : NovikovSeries R H N).coeff g = 0 := by
  classical
  rw [coeff_single, Pi.single_eq_of_ne hgh]

theorem support_single_subset (h : H) (r : R) :
    (single h r : NovikovSeries R H N).support ⊆ {h} := fun g hg => by
  by_contra hgh
  exact hg (coeff_single_of_ne hgh r)

@[simp]
theorem support_single_of_ne {h : H} {r : R} (hr : r ≠ 0) :
    (single h r : NovikovSeries R H N).support = {h} := by
  classical
  rw [support, coeff_single, Pi.support_single_of_ne hr]

@[simp]
theorem single_zero (h : H) : (single h 0 : NovikovSeries R H N) = 0 := by
  ext g
  by_cases hgh : g = h
  · rw [hgh, coeff_single_same, coeff_zero]
  · rw [coeff_single_of_ne hgh, coeff_zero]

theorem single_injective (h : H) : Injective (single h : R → NovikovSeries R H N) :=
  fun r s hrs => by rw [← coeff_single_same (N := N) h r, hrs, coeff_single_same]

@[simp]
theorem single_eq_zero_iff {h : H} {r : R} : (single h r : NovikovSeries R H N) = 0 ↔ r = 0 :=
  ⟨fun hr => single_injective h (hr.trans (single_zero h).symm), fun hr => hr ▸ single_zero h⟩

instance [Nontrivial R] : Nontrivial (NovikovSeries R H N) := by
  obtain ⟨r, hr⟩ := exists_ne (0 : R)
  exact ⟨⟨single 0 r, 0, single_eq_zero_iff.not.2 hr⟩⟩

end Zero

@[simp]
theorem single_add [AddZeroClass R] (h : H) (r s : R) :
    (single h (r + s) : NovikovSeries R H N) = single h r + single h s := by
  ext g
  by_cases hgh : g = h
  · rw [hgh, coeff_add, coeff_single_same, coeff_single_same, coeff_single_same]
  · rw [coeff_add, coeff_single_of_ne hgh, coeff_single_of_ne hgh, coeff_single_of_ne hgh, add_zero]

@[simp]
theorem single_neg [NegZeroClass R] (h : H) (r : R) :
    (single h (-r) : NovikovSeries R H N) = -single h r := by
  classical
  refine coeff_injective ?_
  rw [coeff_neg', coeff_single, coeff_single]
  exact Pi.single_op (fun _ => (Neg.neg : R → R)) (fun _ => neg_zero) h r

@[simp]
theorem single_sub [AddGroup R] (h : H) (r s : R) :
    (single h (r - s) : NovikovSeries R H N) = single h r - single h s := by
  rw [sub_eq_add_neg, single_add, single_neg, sub_eq_add_neg]

theorem smul_single {S : Type*} [Zero R] [SMulZeroClass S R] (s : S) (h : H) (r : R) :
    s • (single h r : NovikovSeries R H N) = single h (s • r) := by
  ext g
  by_cases hgh : g = h
  · rw [hgh, coeff_smul, coeff_single_same, coeff_single_same]
  · rw [coeff_smul, coeff_single_of_ne hgh, coeff_single_of_ne hgh, smul_zero]

@[simp]
theorem ofFinsupp_single [AddMonoid R] (h : H) (r : R) :
    ofFinsupp (N := N) (Finsupp.single h r) = single h r := by
  classical
  ext g
  rw [coeff_ofFinsupp, coeff_single, Finsupp.single_eq_pi_single]

end Single

section Order

variable {R H : Type*} [AddZeroClass H] {N : H →+ ℝ} [Zero R] {a : NovikovSeries R H N} {h : H}
  {C : ℝ}

/-- The order of a Novikov series: the least period of its support, and `0` for the zero series.
-/
def order (a : NovikovSeries R H N) : ℝ :=
  sInf (N '' a.support)

@[simp]
theorem order_zero : (0 : NovikovSeries R H N).order = 0 := by
  simp [order]

/-- The order of a nonzero Novikov series is the least period of its support. -/
theorem isLeast_order (ha : a ≠ 0) : IsLeast (N '' a.support) a.order := by
  obtain ⟨g, -, hg⟩ := exists_isLeast_image_support (support_nonempty_iff.2 ha)
  rwa [order, hg.csInf_eq]

/-- A Novikov series whose support has least period `C` has order `C`. -/
theorem order_eq_of_isLeast (hC : IsLeast (N '' a.support) C) : a.order = C :=
  hC.csInf_eq

theorem order_le_of_coeff_ne_zero (hh : a.coeff h ≠ 0) : a.order ≤ N h :=
  csInf_le a.bddBelow_image_support ⟨h, mem_support.2 hh, rfl⟩

theorem coeff_eq_zero_of_lt_order (hh : N h < a.order) : a.coeff h = 0 := by
  by_contra ha
  exact (order_le_of_coeff_ne_zero ha).not_gt hh

/-- A nonzero Novikov series has a nonzero coefficient at an exponent of period equal to its
order. -/
theorem exists_coeff_ne_zero_and_period_eq_order (ha : a ≠ 0) :
    ∃ h, a.coeff h ≠ 0 ∧ N h = a.order := by
  obtain ⟨h, hh, hN⟩ := (isLeast_order ha).1
  exact ⟨h, mem_support.1 hh, hN⟩

/-- A nonzero Novikov series vanishes below the period cutoff `C` exactly when `C` is at most its
order. -/
theorem le_order_iff (ha : a ≠ 0) : C ≤ a.order ↔ ∀ h, N h < C → a.coeff h = 0 := by
  refine ⟨fun hC h hh => coeff_eq_zero_of_lt_order (hh.trans_le hC), fun hC => ?_⟩
  obtain ⟨h, hh, hN⟩ := exists_coeff_ne_zero_and_period_eq_order ha
  rw [← hN]
  by_contra hlt
  exact hh (hC h (not_le.1 hlt))

@[simp]
theorem order_single {r : R} (hr : r ≠ 0) : (single h r : NovikovSeries R H N).order = N h :=
  order_eq_of_isLeast <| by simp [support_single_of_ne hr]

end Order

section Truncation

variable {R H : Type*} [AddZeroClass H] {N : H →+ ℝ} {C : ℝ}

section Zero

variable [Zero R] {a : NovikovSeries R H N}

/-- The truncation of a Novikov series `a` below the period cutoff `C`: the finitely supported
coefficient function that agrees with `a` at exponents of period `< C` and vanishes elsewhere. -/
def trunc (C : ℝ) (a : NovikovSeries R H N) : H →₀ R :=
  Finsupp.ofSupportFinite ({h | N h < C}.indicator a.coeff) <| by
    rw [support_indicator]
    exact (a.finite_lt C).subset fun _ hh => ⟨hh.2, hh.1⟩

@[simp]
theorem trunc_apply (C : ℝ) (a : NovikovSeries R H N) (h : H) :
    trunc C a h = if N h < C then a.coeff h else 0 := by
  simp [trunc, Finsupp.ofSupportFinite_coe, indicator_apply]

theorem trunc_apply_of_lt {h : H} (hh : N h < C) : trunc C a h = a.coeff h := by
  simp [hh]

theorem trunc_apply_of_le {h : H} (hh : C ≤ N h) : trunc C a h = 0 := by
  simp [hh.not_gt]

@[simp]
theorem trunc_zero (C : ℝ) : trunc C (0 : NovikovSeries R H N) = 0 := by
  ext h
  simp

end Zero

@[simp]
theorem trunc_add [AddZeroClass R] (C : ℝ) (a b : NovikovSeries R H N) :
    trunc C (a + b) = trunc C a + trunc C b := by
  ext h
  by_cases hh : N h < C <;> simp [hh]

@[simp]
theorem trunc_neg [NegZeroClass R] (C : ℝ) (a : NovikovSeries R H N) :
    trunc C (-a) = -trunc C a := by
  ext h
  by_cases hh : N h < C <;> simp [hh]

@[simp]
theorem trunc_sub [AddGroup R] (C : ℝ) (a b : NovikovSeries R H N) :
    trunc C (a - b) = trunc C a - trunc C b := by
  ext h
  by_cases hh : N h < C <;> simp [hh]

@[simp]
theorem trunc_smul {S : Type*} [Zero R] [SMulZeroClass S R] (C : ℝ) (s : S)
    (a : NovikovSeries R H N) : trunc C (s • a) = s • trunc C a := by
  ext h
  by_cases hh : N h < C <;> simp [hh]

end Truncation

section Surjective

variable {R H : Type*} [AddGroup H] {N : H →+ ℝ}

/-- The Novikov series with coefficient `r` at every natural multiple of `h` and `0` elsewhere,
for an exponent `h` of positive period. -/
private def geometric [Zero R] (N : H →+ ℝ) {h : H} (hh : 0 < N h) (r : R) :
    NovikovSeries R H N where
  coeff := (range fun k : ℕ => k • h).indicator fun _ => r
  finite_lt C := by
    refine ((Finset.range ⌈C / N h⌉₊).finite_toSet.image fun k : ℕ => k • h).subset ?_
    rintro g ⟨hg, hgC⟩
    obtain ⟨k, rfl⟩ := mem_of_indicator_ne_zero hg
    refine ⟨k, Finset.mem_coe.2 (Finset.mem_range.2 (Nat.lt_ceil.2 ?_)), rfl⟩
    rw [map_nsmul, nsmul_eq_mul] at hgC
    exact (lt_div_iff₀ hh).2 hgC

private theorem infinite_support_geometric [Zero R] {h : H} (hh : 0 < N h) {r : R} (hr : r ≠ 0) :
    (geometric N hh r).support.Infinite := by
  have hinj : Injective fun k : ℕ => k • h := fun k l hkl => by
    have := congrArg N hkl
    simp only [map_nsmul, nsmul_eq_mul] at this
    exact_mod_cast mul_right_cancel₀ hh.ne' this
  refine (infinite_range_of_injective hinj).mono fun g hg => ?_
  simpa [support, geometric, hr] using hg

/-- Over a nontrivial coefficient type, every Novikov series is finitely supported if and only if
the period homomorphism vanishes. -/
theorem ofFinsupp_surjective_iff [AddMonoid R] [Nontrivial R] :
    Surjective (ofFinsupp (R := R) (N := N)) ↔ N = 0 := by
  refine ⟨fun hsurj => ?_, fun hN a => ?_⟩
  · by_contra hN
    obtain ⟨h, hh⟩ : ∃ h, 0 < N h := by
      obtain ⟨g, hg⟩ := DFunLike.ne_iff.1 hN
      simp only [AddMonoidHom.zero_apply] at hg
      rcases hg.lt_or_gt with hg | hg
      · exact ⟨-g, by simpa using hg⟩
      · exact ⟨g, hg⟩
    obtain ⟨r, hr⟩ := exists_ne (0 : R)
    exact infinite_support_geometric hh hr
      (mem_range_ofFinsupp_iff.1 (hsurj (geometric N hh r)))
  · refine mem_range_ofFinsupp_iff.2 ((a.finite_lt 1).subset fun g hg => ⟨hg, ?_⟩)
    simp [hN]

end Surjective

end NovikovSeries

end TauCeti
