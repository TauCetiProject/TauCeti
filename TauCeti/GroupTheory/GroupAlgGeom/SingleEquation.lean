/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.CSA
public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet
import Mathlib.Order.CompleteLattice.Finset

/-!
# Finite systems and finite unions of algebraic sets as single equations

A group `H` satisfies *Vaught's condition* when `x ^ 2 * y ^ 2 * z ^ 2 = 1` forces `x`, `y` and
`z` to commute pairwise; by Lyndon's theorem every free group does. In a torsion-free CSA group
satisfying Vaught's condition and containing two noncommuting elements `a` and `b`, Malcev's
equation `x ^ 2 * a * x ^ 2 * a⁻¹ = (y * b * y * b⁻¹) ^ 2` has only the trivial solution
`x = y = 1`. Thus the single word `malcevWord a b x y` vanishes exactly when both `x` and `y` do.
In a CSA group, `x = 1 ∨ y = 1` holds exactly when `x` commutes with `y`, `a * y * a⁻¹` and
`b * y * b⁻¹` (`Group.IsCSA.eq_one_or_eq_one_iff_commute_conj`); combining these three
commutators with Malcev's word gives one word `malcevOrWord a b x y` that vanishes exactly when
`x` or `y` does.

Applied to equations over a coefficient group `G`, with `a` and `b` coefficients whose images in
`H` do not commute, these words turn a conjunction or a disjunction of two equations into one
equation with the same solutions in `H`. Hence every finite system of equations over `G`, and
every finite union of algebraic sets of finite systems, is the algebraic set in `H` of a single
equation. Nonabelian free groups are torsion-free and CSA, and satisfy Vaught's condition by
Lyndon's theorem; over them this is the reduction of conjunctions and disjunctions of equations to
a single equation, on which Merzljakov's theorem on formal solutions of positive sentences is
built.

## Main definitions

* `Group.IsVaught G`: Vaught's condition `x ^ 2 * y ^ 2 * z ^ 2 = 1 → [x, y] = [x, z] = [y, z] = 1`.
* `TauCeti.GroupAlgGeom.malcevWord a b x y`: Malcev's word
  `x ^ 2 * a * x ^ 2 * a⁻¹ * ((y * b * y * b⁻¹) ^ 2)⁻¹`.
* `TauCeti.GroupAlgGeom.malcevOrWord a b x y`: a word vanishing exactly when `x` or `y` does.

## Main results

* `Group.IsVaught.malcevWord_eq_one_iff`: Malcev's equation has only the trivial solution.
* `Group.IsVaught.malcevOrWord_eq_one_iff`: the disjunction as a single word.
* `TauCeti.GroupAlgGeom.V_singleton_malcevWord`,
  `TauCeti.GroupAlgGeom.V_singleton_malcevOrWord`: intersections and unions of the solution sets
  of two equations are solution sets of one equation.
* `TauCeti.GroupAlgGeom.exists_V_singleton_eq_of_finite`: a finite system has the same solutions
  as a single equation.
* `TauCeti.GroupAlgGeom.exists_V_singleton_eq_biUnion`: a finite union of algebraic sets of
  finite systems is the algebraic set of a single equation.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §3.1, Definition 7, Lemmas 3–4 and Corollaries 2–5.
* G. S. Makanin, *Decidability of the universal and positive theories of a free group*,
  Math. USSR Izv. 25 (1985), §4, Lemmas 3–4.
* R. C. Lyndon, *The equation `a²b² = c²` in free groups*, Michigan Math. J. 6 (1959).
-/

public section

open Monoid.Coprod
open scoped commutatorElement

namespace Group

variable (G : Type*) [Group G]

/-- A group satisfies *Vaught's condition* when `x ^ 2 * y ^ 2 * z ^ 2 = 1` forces `x`, `y` and
`z` to commute pairwise. By Lyndon's theorem every free group satisfies it. -/
def IsVaught : Prop :=
  ∀ x y z : G, x ^ 2 * y ^ 2 * z ^ 2 = 1 → Commute x y ∧ Commute x z ∧ Commute y z

/-- The defining condition for Vaught's condition. -/
theorem isVaught_iff : IsVaught G ↔
    ∀ x y z : G, x ^ 2 * y ^ 2 * z ^ 2 = 1 → Commute x y ∧ Commute x z ∧ Commute y z :=
  Iff.rfl

end Group

namespace TauCeti.GroupAlgGeom

open Group

variable {G H : Type*} [Group G] [Group H]

/-- Malcev's word `x ^ 2 * a * x ^ 2 * a⁻¹ * ((y * b * y * b⁻¹) ^ 2)⁻¹`. It vanishes exactly when
`x ^ 2 * a * x ^ 2 * a⁻¹ = (y * b * y * b⁻¹) ^ 2`, which in a torsion-free CSA group satisfying
Vaught's condition, with `a` and `b` not commuting, means `x = 1` and `y = 1`. -/
def malcevWord (a b x y : G) : G :=
  x ^ 2 * a * x ^ 2 * a⁻¹ * ((y * b * y * b⁻¹) ^ 2)⁻¹

/-- A word in `x` and `y` with constants `a` and `b`, built from Malcev's word and the
commutators of `x` with `y`, `a * y * a⁻¹` and `b * y * b⁻¹`. In a torsion-free CSA group
satisfying Vaught's condition, with `a` and `b` not commuting, it vanishes exactly when `x = 1`
or `y = 1`. -/
def malcevOrWord (a b x y : G) : G :=
  malcevWord a b ⁅x, y⁆ (malcevWord a b ⁅x, a * y * a⁻¹⁆ ⁅x, b * y * b⁻¹⁆)

/-- Malcev's word vanishes exactly when Malcev's equation holds. -/
theorem malcevWord_eq_one_iff_eq {a b x y : G} :
    malcevWord a b x y = 1 ↔ x ^ 2 * a * x ^ 2 * a⁻¹ = (y * b * y * b⁻¹) ^ 2 :=
  mul_inv_eq_one

@[simp]
theorem map_malcevWord {F : Type*} [FunLike F G H] [MonoidHomClass F G H] (f : F)
    (a b x y : G) : f (malcevWord a b x y) = malcevWord (f a) (f b) (f x) (f y) := by
  simp [malcevWord]

@[simp]
theorem map_malcevOrWord {F : Type*} [FunLike F G H] [MonoidHomClass F G H] (f : F)
    (a b x y : G) : f (malcevOrWord a b x y) = malcevOrWord (f a) (f b) (f x) (f y) := by
  simp [malcevOrWord, map_commutatorElement]

/-- **Malcev's equation** (Kharlampovich–Myasnikov, Lemma 3). In a torsion-free CSA group
satisfying Vaught's condition, if `a` and `b` do not commute, then
`x ^ 2 * a * x ^ 2 * a⁻¹ = (y * b * y * b⁻¹) ^ 2` holds only for `x = y = 1`. -/
theorem _root_.Group.IsVaught.malcevWord_eq_one_iff [IsMulTorsionFree G] (hV : IsVaught G)
    (hG : IsCSA G) {a b x y : G} (hab : ¬Commute a b) :
    malcevWord a b x y = 1 ↔ x = 1 ∧ y = 1 := by
  refine ⟨fun h => ?_, fun ⟨hx, hy⟩ => by simp [hx, hy, malcevWord]⟩
  have hT := (isCommTransitive_iff G).1 hG.isCommTransitive
  have := hG.isCommTransitive.hasUniqueRoots
  have hconj := (isCSA_iff_isCommTransitive_and_commute_conj.1 hG).2
  set r := y * b * y * b⁻¹ with hr
  have heq : x ^ 2 * a * x ^ 2 * a⁻¹ = r ^ 2 := malcevWord_eq_one_iff_eq.1 h
  -- Vaught's condition for `x`, `a * x * a⁻¹` and `r⁻¹` makes `x` commute with `a * x * a⁻¹`.
  have h₁ : x ^ 2 * (a * x * a⁻¹) ^ 2 * r⁻¹ ^ 2 = 1 := by
    rw [conj_pow, inv_pow, mul_inv_eq_one, ← heq]
    group
  obtain ⟨hxa, -, -⟩ := hV _ _ _ h₁
  obtain rfl | hx := eq_or_ne x 1
  · -- Then `r ^ 2 = 1`, so `r = 1`, that is `(y * b) ^ 2 = b ^ 2`, and `y * b = b`.
    have hr₁ : y * b * y * b⁻¹ = 1 := (pow_eq_one_iff_left two_ne_zero).1 <| by
      rw [← hr, ← heq]
      group
    have hyb : (y * b) ^ 2 = b ^ 2 :=
      calc (y * b) ^ 2 = y * b * y * b := by rw [sq]; group
        _ = b ^ 2 := by rw [mul_inv_eq_one.1 hr₁, sq]
    exact ⟨rfl, mul_eq_right.1 (pow_left_injective two_ne_zero hyb)⟩
  · -- Otherwise `x` commutes with `a`, so `r ^ 2 = x ^ 4` and `r = x ^ 2`. Vaught's condition for
    -- `y * b`, `b⁻¹` and `x⁻¹` then makes `x` commute with `b`, hence `a` with `b`.
    have hax : Commute a (x ^ 2) := (hconj x a hx hxa).symm.pow_right 2
    have hrx : r = x ^ 2 := pow_left_injective two_ne_zero (by
      rw [← heq, mul_assoc (x ^ 2), hax.eq, ← mul_assoc, mul_inv_cancel_right, sq (x ^ 2)] :
        r ^ 2 = (x ^ 2) ^ 2)
    have h₂ : (y * b) ^ 2 * b⁻¹ ^ 2 * x⁻¹ ^ 2 = 1 := by
      rw [inv_pow, inv_pow, ← hrx, hr, sq (y * b)]
      group
    obtain ⟨-, -, hbx⟩ := hV _ _ _ h₂
    exact (hab (hT a x b hx (hconj x a hx hxa).symm (Commute.inv_inv_iff.1 hbx).symm)).elim

/-- In a torsion-free CSA group satisfying Vaught's condition, if `a` and `b` do not commute,
then `malcevOrWord a b x y` vanishes exactly when `x = 1` or `y = 1`. -/
theorem _root_.Group.IsVaught.malcevOrWord_eq_one_iff [IsMulTorsionFree G] (hV : IsVaught G)
    (hG : IsCSA G) {a b x y : G} (hab : ¬Commute a b) :
    malcevOrWord a b x y = 1 ↔ x = 1 ∨ y = 1 := by
  rw [hG.eq_one_or_eq_one_iff_commute_conj hab, malcevOrWord, hV.malcevWord_eq_one_iff hG hab,
    hV.malcevWord_eq_one_iff hG hab]
  simp only [commutatorElement_eq_one_iff_commute]

/-! ### Single equations over a coefficient group -/

section Equations

variable {X : Type*} {ι : G →* H} [IsMulTorsionFree H] {a b : G}

/-- Over a torsion-free CSA group satisfying Vaught's condition, Malcev's word in two equations,
with noncommuting coefficients, has the solutions common to both equations. -/
theorem V_singleton_malcevWord (hV : IsVaught H) (hH : IsCSA H) (hab : ¬Commute (ι a) (ι b))
    (s t : GX G X) : V ι {malcevWord (inl a) (inl b) s t} = V ι {s, t} := by
  ext v
  simp [hV.malcevWord_eq_one_iff hH hab]

/-- Over a torsion-free CSA group satisfying Vaught's condition, `malcevOrWord` in two equations,
with noncommuting coefficients, has the solutions of either equation. -/
theorem V_singleton_malcevOrWord (hV : IsVaught H) (hH : IsCSA H) (hab : ¬Commute (ι a) (ι b))
    (s t : GX G X) : V ι {malcevOrWord (inl a) (inl b) s t} = V ι {s} ∪ V ι {t} := by
  ext v
  simp [hV.malcevOrWord_eq_one_iff hH hab]

/-- Over a torsion-free CSA group satisfying Vaught's condition in which two coefficients do not
commute, every finite system of equations has the same solutions as a single equation. -/
theorem exists_V_singleton_eq_of_finite (hV : IsVaught H) (hH : IsCSA H)
    (hab : ¬Commute (ι a) (ι b)) {S : Set (GX G X)} (hS : S.Finite) :
    ∃ s, V ι {s} = V ι S := by
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨1, by ext v; simp⟩
  | @insert u T _ _ ih =>
    obtain ⟨s, hs⟩ := ih
    refine ⟨malcevWord (inl a) (inl b) u s, ?_⟩
    rw [V_singleton_malcevWord hV hH hab]
    simp only [Set.insert_eq, V_union, hs]

/-- Over a torsion-free CSA group satisfying Vaught's condition in which two coefficients do not
commute, every finite union of algebraic sets of finite systems is the algebraic set of a single
equation. The empty union is cut out by the commutator of the two coefficients. -/
theorem exists_V_singleton_eq_biUnion (hV : IsVaught H) (hH : IsCSA H)
    (hab : ¬Commute (ι a) (ι b)) {κ : Type*} (t : Finset κ) (S : κ → Set (GX G X))
    (hS : ∀ i ∈ t, (S i).Finite) : ∃ s, V ι {s} = ⋃ i ∈ t, V ι (S i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    refine ⟨inl ⁅a, b⁆, ?_⟩
    rw [V_singleton_inl_eq_empty (by rwa [map_commutatorElement, ne_eq,
      commutatorElement_eq_one_iff_commute])]
    simp
  | insert i t _ ih =>
    obtain ⟨s, hs⟩ := ih fun j hj => hS j (Finset.mem_insert_of_mem hj)
    obtain ⟨u, hu⟩ := exists_V_singleton_eq_of_finite hV hH hab (hS i (Finset.mem_insert_self i t))
    refine ⟨malcevOrWord (inl a) (inl b) u s, ?_⟩
    rw [V_singleton_malcevOrWord hV hH hab, hu, hs, Finset.set_biUnion_insert]

end Equations

end TauCeti.GroupAlgGeom
