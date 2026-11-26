/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet
public import TauCeti.GroupTheory.GroupAlgGeom.ReducedWord
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.Algebra.Group.Commutator
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Group.Commute.Hom
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Finite.Range
import Mathlib.Algebra.Group.Submonoid.BigOperators
import TauCeti.Data.List.Forall2
import TauCeti.GroupTheory.FreeGroup.Basic
import TauCeti.Logic.Function.Extend

/-!
# Quadratic words and standard quadratic equations

An equation over a group `G` in the variables `X` is an element of `G[X] = G ∗ F(X)`. It is
quadratic when every variable occurs in it at most twice, as `x` or as `x⁻¹`. Quadratic equations
are the equations whose solution theory is governed by surfaces: the four standard quadratic
words below are the relators of orientable and non-orientable surfaces with boundary components
labelled by coefficients, and [IFT] uses automorphisms of `G[X]` fixing `G` to bring strictly
quadratic equations into these standard forms. This file does not prove that reduction, whose
precise form has to account for words conjugate to coefficients: for instance the coefficients
themselves and their conjugates `x c x⁻¹` are strictly quadratic but are not standard. It proves
its first step, cyclic reduction relative to `G`: a strictly quadratic word is conjugate to a
cyclically reduced strictly quadratic word, from which the variables of the conjugator have
disappeared.

This file defines quadratic and strictly quadratic finite systems using `GX.occurrences`, the
four types of standard quadratic equations together with their atoms, variables, coefficients,
atomic rank, genus, Euler characteristic and the invariant `κ(S)` of [IFT], Definition 6, and
degenerate, commutative and general-position solutions. It also records the standard equation
`[x, y] = [a, b]` of genus one and its solutions.

Following [IFT], the standard quadratic equations over `G` are, with `[x, y] = x⁻¹ y⁻¹ x y`
(Mathlib's `⁅x⁻¹, y⁻¹⁆`) and `z⁻¹ c z` the conjugate of a coefficient,
1. `∏ᵢ₌₁ⁿ [xᵢ, yᵢ] = 1` with `n > 0`;
2. `∏ᵢ₌₁ⁿ [xᵢ, yᵢ] ∏ⱼ₌₁ᵐ zⱼ⁻¹ cⱼ zⱼ d = 1` with `n + m ≥ 1`;
3. `∏ᵢ₌₁ⁿ xᵢ² = 1` with `n > 0`;
4. `∏ᵢ₌₁ⁿ xᵢ² ∏ⱼ₌₁ᵐ zⱼ⁻¹ cⱼ zⱼ d = 1` with `n > 0`,

where the variables are pairwise distinct and the coefficients `cⱼ` and `d` are nontrivial.
Equations without commutators or squares are of type (2), so the non-orientable types have
positive genus. The factors `[xᵢ, yᵢ]`, `xᵢ²` and `zⱼ⁻¹ cⱼ zⱼ` are the atoms.

The atoms are words in pairwise disjoint sets of variables, so their values can be prescribed
independently, and the values of each atom are closed under conjugation: standard equations are
*separable* and their atoms have *complete spectrum* ([VAR-I], §2).

## Main definitions

* `TauCeti.GroupAlgGeom.Quadratic.IsQuadratic`,
  `TauCeti.GroupAlgGeom.Quadratic.IsStrictlyQuadratic`: every variable occurs in a finite system
  at most twice, respectively zero times or exactly twice.
* `TauCeti.GroupAlgGeom.Quadratic.Standard G X`: the standard quadratic equations of types
  (1)–(4), with `Standard.toWord`, `Standard.atoms`, `Standard.vars`, `Standard.coeffs`,
  `Standard.atomicRank`, `Standard.genus`, `Standard.IsOrientable`, `Standard.eulerChar` and
  `Standard.kappa`.
* `Standard.IsDegenerate`, `Standard.IsCommutative`, `Standard.IsGeneralPosition`: a point at
  which some atom vanishes, at which consecutive atoms commute, at which no two consecutive atoms
  commute.
* `TauCeti.GroupAlgGeom.Quadratic.oneCommutatorEquation a b`: the equation `[x, y] = [a, b]` over
  `G`.

## Main results

* `TauCeti.GroupAlgGeom.Quadratic.isQuadratic_map_iff`,
  `TauCeti.GroupAlgGeom.Quadratic.isStrictlyQuadratic_map_iff`: an injective map transporting
  occurrence counts along a bijection of the variables preserves (strictly) quadratic systems.
* `TauCeti.GroupAlgGeom.Quadratic.IsQuadratic.image_map`: every change of coefficients
  `G →* H`, injective or not, keeps a system quadratic.
* `TauCeti.GroupAlgGeom.Quadratic.exists_isCyclicallyReduced_conj`,
  `TauCeti.GroupAlgGeom.Quadratic.IsStrictlyQuadratic.exists_isCyclicallyReduced_conj`: cyclic
  reduction relative to `G`, and of strictly quadratic words.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.isQuadratic`,
  `TauCeti.GroupAlgGeom.Quadratic.Standard.isStrictlyQuadratic`: standard equations are strictly
  quadratic, with every variable of `S.vars` occurring twice
  (`TauCeti.GroupAlgGeom.Quadratic.Standard.occurrences_toWord_of_mem_vars`).
* `TauCeti.GroupAlgGeom.Quadratic.Standard.isCyclicallyReduced_reducedWord`: the reduced word of
  a standard equation is cyclically reduced.
* `TauCeti.GroupAlgGeom.Quadratic.isStandard_oneCommutatorEquation`: `[x, y] = [a, b]` is a
  standard orientable quadratic equation of genus one.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.kappa_eq_ncard_vars`,
  `TauCeti.GroupAlgGeom.Quadratic.Standard.kappa_eq_ncard_vars_add_one`: `κ(S)` is the number of
  variables of `S`, plus one when the coefficient `d` occurs; it equals `2 - χ(S)`
  (`TauCeti.GroupAlgGeom.Quadratic.Standard.eulerChar_eq_two_sub_kappa`). When every variable of
  `X` occurs in `S`, this is the count `κ(S) = |X| + ε(S)` of [IFT], Definition 6
  (`TauCeti.GroupAlgGeom.Quadratic.Standard.kappa_eq_card_of_vars_eq_univ`,
  `TauCeti.GroupAlgGeom.Quadratic.Standard.kappa_eq_card_add_one_of_vars_eq_univ`).
* `TauCeti.GroupAlgGeom.Quadratic.Standard.exists_map_eval_atoms_eq`: separability, values that
  each atom takes at some point are taken by all the atoms at one point.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.exists_eval_eq_of_mem_atoms_of_isConj`: complete
  spectrum, the values of an atom are closed under conjugation. This holds for every word in the
  variables alone (`FreeGroup.exists_lift_eq_of_isConj`) and for every conjugate `z⁻¹ c z` of a
  coefficient by a variable, whose values are exactly the conjugates of the image of `c`
  (`TauCeti.GroupAlgGeom.exists_eval_inv_mul_inl_mul_eq_iff_isConj`).
* `TauCeti.GroupAlgGeom.Quadratic.Standard.isDegenerate_iff_of_genus_eq_zero`,
  `TauCeti.GroupAlgGeom.Quadratic.Standard.not_isDegenerate_of_genus_eq_zero_of_injective`: a
  point is degenerate for an equation of genus `0` exactly when a coefficient `cⱼ` is mapped to
  `1`, so never when the coefficients embed.
* `TauCeti.GroupAlgGeom.Quadratic.exists_standard_toWord_eq_commutator`: the commutator
  `x⁻¹ y⁻¹ x y` is a standard quadratic word.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.isCommutative_of_mem_V_genusTwo`: every solution of
  `[x₁, y₁][x₂, y₂] = 1` is commutative, so this equation has no solution in general position.
* `TauCeti.GroupAlgGeom.Quadratic.isGeneralPosition_genusThree`: `[x₁, y₁][x₂, y₂][x₃, y₃] = 1`
  has a solution in general position in `F(a, b)`.
* `TauCeti.GroupAlgGeom.Quadratic.not_isQuadratic_cubic`: `x y x⁻¹ y⁻¹ x` is not quadratic.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §2.2 and §2.7, Definitions 2–6 and Lemma 1.
* [VAR-I] O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I:
  Irreducibility of quadratic equations and Nullstellensatz*, J. Algebra 200 (1998), §1 and §2,
  Definitions 14–16 and the proof of Proposition 5.
-/

public section

open Monoid.Coprod
open scoped commutatorElement

namespace TauCeti.GroupAlgGeom.Quadratic

variable {G H X : Type*} [Group G] [Group H]

/-! ### Quadratic systems -/

section IsQuadratic

/-- A finite system `S ⊆ G[X]` is quadratic when every variable occurs in `S`, counted over all
its elements, at most twice. -/
def IsQuadratic (S : Finset (GX G X)) : Prop := ∀ x, ∑ w ∈ S, GX.occurrences x w ≤ 2

/-- A finite system `S ⊆ G[X]` is strictly quadratic when every variable occurring in `S` occurs
in it, counted over all its elements, exactly twice. -/
def IsStrictlyQuadratic (S : Finset (GX G X)) : Prop :=
  ∀ x, ∑ w ∈ S, GX.occurrences x w = 0 ∨ ∑ w ∈ S, GX.occurrences x w = 2

theorem isQuadratic_iff {S : Finset (GX G X)} :
    IsQuadratic S ↔ ∀ x, ∑ w ∈ S, GX.occurrences x w ≤ 2 := Iff.rfl

theorem isStrictlyQuadratic_iff {S : Finset (GX G X)} :
    IsStrictlyQuadratic S ↔
      ∀ x, ∑ w ∈ S, GX.occurrences x w = 0 ∨ ∑ w ∈ S, GX.occurrences x w = 2 :=
  Iff.rfl

@[simp] theorem isQuadratic_singleton {w : GX G X} :
    IsQuadratic {w} ↔ ∀ x, GX.occurrences x w ≤ 2 := by simp [isQuadratic_iff]

@[simp] theorem isStrictlyQuadratic_singleton {w : GX G X} :
    IsStrictlyQuadratic {w} ↔ ∀ x, GX.occurrences x w = 0 ∨ GX.occurrences x w = 2 := by
  simp [isStrictlyQuadratic_iff]

/-- Every coefficient word is strictly quadratic. -/
theorem isStrictlyQuadratic_inl (c : G) : IsStrictlyQuadratic {(inl c : GX G X)} := by simp

theorem IsStrictlyQuadratic.isQuadratic {S : Finset (GX G X)} (h : IsStrictlyQuadratic S) :
    IsQuadratic S := fun x => by rcases h x with h | h <;> omega

theorem IsQuadratic.mono {S T : Finset (GX G X)} (hT : IsQuadratic T) (h : S ⊆ T) :
    IsQuadratic S := fun x => (Finset.sum_le_sum_of_subset h).trans (hT x)

/-- A change of coefficients `f : G →* H` keeps a system quadratic: it does not increase the
number of occurrences of a variable in a word, and identifying words only lowers the counts. -/
theorem IsQuadratic.image_map [DecidableEq (GX H X)] {S : Finset (GX G X)} (hS : IsQuadratic S)
    (f : G →* H) : IsQuadratic (S.image (Monoid.Coprod.map f (FreeGroup.map id))) := fun x =>
  calc ∑ w ∈ S.image (Monoid.Coprod.map f (FreeGroup.map id)), GX.occurrences x w
      ≤ ∑ w ∈ S, GX.occurrences x (Monoid.Coprod.map f (FreeGroup.map id) w) :=
        Finset.sum_image_le_of_nonneg fun _ _ => Nat.zero_le _
    _ ≤ ∑ w ∈ S, GX.occurrences x w := Finset.sum_le_sum fun w _ =>
        GX.occurrences_map_le _ x x (by simp [GX.occurrences_inl])
          (by simp [GX.occurrences_inr_of_self])
          (fun z hz => by simp [GX.occurrences_inr_of_of_ne hz]) w
    _ ≤ 2 := hS x

section Map

variable {Y : Type*} {S : Finset (GX G X)} (φ : GX G X ↪ GX H Y) (σ : X ≃ Y)

private theorem sum_occurrences_map
    (h : ∀ x, ∀ w ∈ S, GX.occurrences (σ x) (φ w) = GX.occurrences x w) (y : Y) :
    ∑ w ∈ S.map φ, GX.occurrences y w = ∑ w ∈ S, GX.occurrences (σ.symm y) w := by
  rw [Finset.sum_map]
  exact Finset.sum_congr rfl fun w hw => by simpa using h (σ.symm y) w hw

/-- An injective map `G[X] → H[Y]` transporting the occurrence counts in the words of a system
along a bijection of the variables preserves quadratic systems. -/
theorem isQuadratic_map_iff
    (h : ∀ x, ∀ w ∈ S, GX.occurrences (σ x) (φ w) = GX.occurrences x w) :
    IsQuadratic (S.map φ) ↔ IsQuadratic S := by
  simp only [isQuadratic_iff, sum_occurrences_map φ σ h]
  exact σ.symm.forall_congr_right (q := fun x => ∑ w ∈ S, GX.occurrences x w ≤ 2)

/-- An injective map `G[X] → H[Y]` transporting the occurrence counts in the words of a system
along a bijection of the variables preserves strictly quadratic systems. -/
theorem isStrictlyQuadratic_map_iff
    (h : ∀ x, ∀ w ∈ S, GX.occurrences (σ x) (φ w) = GX.occurrences x w) :
    IsStrictlyQuadratic (S.map φ) ↔ IsStrictlyQuadratic S := by
  simp only [isStrictlyQuadratic_iff, sum_occurrences_map φ σ h]
  exact σ.symm.forall_congr_right
    (q := fun x => ∑ w ∈ S, GX.occurrences x w = 0 ∨ ∑ w ∈ S, GX.occurrences x w = 2)

end Map

end IsQuadratic

/-! ### Cyclic reduction -/

section CyclicReduction

open GX

/-- Cyclic reduction relative to `G`: every `w ∈ G[X]` is a conjugate `u l u⁻¹` of the product of
a cyclically reduced word `l`, and every variable occurs in `w` as often as in `l` plus twice as
often as in `u`. -/
theorem exists_isCyclicallyReduced_conj (w : GX G X) :
    ∃ (u : GX G X) (l : List (G ⊕ X × Bool)), IsCyclicallyReduced l ∧
      u * (l.map letter).prod * u⁻¹ = w ∧
      ∀ x, occurrences x w = occurrences x (l.map letter).prod + 2 * occurrences x u := by
  obtain ⟨u, l, hu, hl, hprod, hcount⟩ := (isReduced_reducedWord w).exists_isCyclicallyReduced
  refine ⟨(u.map letter).prod, l, hl, by rw [hprod, prod_reducedWord], fun x => ?_⟩
  rw [occurrences_eq_countVar_reducedWord, hcount, hl.isReduced.occurrences_prod,
    ((isReduced_reducedWord w).infix hu.isInfix).occurrences_prod]

/-- Cyclic reduction of a strictly quadratic word `w`: it is a conjugate `u l u⁻¹` of the product
of a cyclically reduced word `l` which is again strictly quadratic. Every variable either occurs in
`l` as often as in `w` and not in the conjugator `u`, or occurs twice in `w`, once in `u` and not
in `l`. -/
theorem IsStrictlyQuadratic.exists_isCyclicallyReduced_conj {w : GX G X}
    (hw : IsStrictlyQuadratic {w}) :
    ∃ (u : GX G X) (l : List (G ⊕ X × Bool)), IsCyclicallyReduced l ∧
      u * (l.map letter).prod * u⁻¹ = w ∧ IsStrictlyQuadratic {(l.map letter).prod} ∧
      ∀ x, occurrences x (l.map letter).prod = occurrences x w ∧ occurrences x u = 0 ∨
        occurrences x w = 2 ∧ occurrences x (l.map letter).prod = 0 ∧ occurrences x u = 1 := by
  obtain ⟨u, l, hl, hprod, hocc⟩ := Quadratic.exists_isCyclicallyReduced_conj w
  rw [isStrictlyQuadratic_singleton] at hw
  refine ⟨u, l, hl, hprod, isStrictlyQuadratic_singleton.2 fun x => ?_, fun x => ?_⟩ <;>
    have := hocc x <;> rcases hw x with h | h <;> omega

/-- For a nontrivial coefficient `a`, the variable `z` occurs exactly twice in the conjugate
`z⁻¹ a z`. -/
theorem occurrences_inv_mul_inl_mul_self {a : G} (ha : a ≠ 1) (z : X) :
    occurrences z ((inr (FreeGroup.of z))⁻¹ * inl a * inr (FreeGroup.of z) : GX G X) = 2 := by
  simp [occurrences_eq_countVar_reducedWord, reducedWord_inv_mul_inl_mul ha]

/-- The conjugate `z⁻¹ c z` of a coefficient by a variable is strictly quadratic. -/
theorem isStrictlyQuadratic_inv_mul_inl_mul_self (c : G) (z : X) :
    IsStrictlyQuadratic {((inr (FreeGroup.of z) : GX G X)⁻¹ * inl c * inr (FreeGroup.of z))} := by
  by_cases hc : c = 1
  · simp [hc]
  · refine isStrictlyQuadratic_singleton.2 fun x => ?_
    rw [occurrences_eq_countVar_reducedWord, reducedWord_inv_mul_inl_mul hc]
    by_cases hx : x = z
    · subst hx; exact .inr (by simp)
    · exact .inl (by simp [Ne.symm hx])

end CyclicReduction

/-! ### Quadratic atoms -/

section Atoms

private def commLetters (x y : X) : List (G ⊕ X × Bool) :=
  [.inr (x, false), .inr (y, false), .inr (x, true), .inr (y, true)]
private def sqLetters (x : X) : List (G ⊕ X × Bool) := [.inr (x, true), .inr (x, true)]
private def conjLetters (z : X) (c : G) : List (G ⊕ X × Bool) :=
  [.inr (z, false), .inl c, .inr (z, true)]

private theorem isReduced_commLetters {x y : X} (h : x ≠ y) :
    GX.IsReduced (commLetters (G := G) x y) := by simp [commLetters, h, h.symm]
private theorem isReduced_sqLetters (x : X) :
    GX.IsReduced (sqLetters (G := G) x) := by simp [sqLetters]
private theorem isReduced_conjLetters {z : X} {c : G} (hc : c ≠ 1) :
    GX.IsReduced (conjLetters z c) := by simp [conjLetters, hc]

/-- The commutator atom `x⁻¹ y⁻¹ x y` (Mathlib's `⁅x⁻¹, y⁻¹⁆`) associated to a pair `(x, y)`. -/
def commWord (p : X × X) : GX G X :=
  ⁅(inr (FreeGroup.of p.1) : GX G X)⁻¹, (inr (FreeGroup.of p.2))⁻¹⁆

theorem commWord_def (p : X × X) :
    commWord (G := G) p = ⁅(inr (FreeGroup.of p.1) : GX G X)⁻¹, (inr (FreeGroup.of p.2))⁻¹⁆ := (rfl)

@[simp] theorem occVars_commWord [DecidableEq X] (p : X × X) :
    GX.occVars (commWord (G := G) p) = if p.1 = p.2 then ∅ else {p.1, p.2} := by
  by_cases hp : p.1 = p.2
  · simp [commWord_def, hp]
  · have hprod : ((commLetters (G := G) p.1 p.2).map GX.letter).prod = commWord p := by
      simp [commLetters, commWord_def, commutatorElement_def, mul_assoc]
    ext v; simp only [hp, ite_false, Finset.mem_insert, Finset.mem_singleton, GX.mem_occVars_iff]
    rw [← hprod, (isReduced_commLetters hp).occurrences_prod]
    by_cases h1 : p.1 = v <;> by_cases h2 : p.2 = v <;> simp [commLetters, h1, h2, Ne.symm]

/-- The square atom `x²` associated to a variable `x`. -/
def sqWord (x : X) : GX G X := (inr (FreeGroup.of x) : GX G X) ^ 2

theorem sqWord_def (x : X) : sqWord (G := G) x = (inr (FreeGroup.of x) : GX G X) ^ 2 := (rfl)

@[simp] theorem occVars_sqWord (x : X) : GX.occVars (sqWord (G := G) x) = {x} := by
  have hprod : ((sqLetters (G := G) x).map GX.letter).prod = sqWord x := by
    simp [sqLetters, sqWord_def, pow_two]
  ext v; simp only [Finset.mem_singleton, GX.mem_occVars_iff]
  rw [← hprod, (isReduced_sqLetters x).occurrences_prod]
  by_cases hv : x = v <;> simp [sqLetters, hv, Ne.symm]

/-- The conjugate atom `z⁻¹ c z` associated to a pair `(z, c)`. -/
def conjWord (p : X × G) : GX G X :=
  (inr (FreeGroup.of p.1) : GX G X)⁻¹ * inl p.2 * inr (FreeGroup.of p.1)

theorem conjWord_def (p : X × G) :
    conjWord p = (inr (FreeGroup.of p.1) : GX G X)⁻¹ * inl p.2 * inr (FreeGroup.of p.1) := (rfl)

@[simp] theorem conjWord_one (z : X) : conjWord (z, (1 : G)) = 1 := by simp [conjWord_def]

@[simp]
theorem occVars_conjWord [DecidableEq G] (p : X × G) :
    GX.occVars (conjWord p) = if p.2 = 1 then ∅ else {p.1} := by
  classical
  by_cases hp : p.2 = 1
  · simp [conjWord_def, hp]
  · ext v; simp only [hp, ite_false, Finset.mem_singleton, GX.mem_occVars_iff,
      GX.occurrences_eq_countVar_reducedWord, conjWord_def, GX.reducedWord_inv_mul_inl_mul hp]
    by_cases hv : p.1 = v <;> simp [hv, Ne.symm]

/-- A commutator atom `commWord p` avoids a variable `v` when neither `p.1` nor `p.2` is `v`. -/
theorem commWord_mem_avoiding [DecidableEq X] {p : X × X} {v : X}
    (h₁ : p.1 ≠ v) (h₂ : p.2 ≠ v) : commWord (G := G) p ∈ GX.avoiding v := by
  have ha : (inr (FreeGroup.of p.1) : GX G X) ∈ GX.avoiding v := GX.inr_of_mem_avoiding h₁
  have hb : (inr (FreeGroup.of p.2) : GX G X) ∈ GX.avoiding v := GX.inr_of_mem_avoiding h₂
  rw [commWord_def, commutatorElement_def, inv_inv, inv_inv]
  exact mul_mem (mul_mem (mul_mem (inv_mem ha) (inv_mem hb)) ha) hb

/-- A square atom `sqWord x` avoids a variable `v` when `x ≠ v`. -/
theorem sqWord_mem_avoiding [DecidableEq X] {x v : X} (hx : x ≠ v) :
    sqWord (G := G) x ∈ GX.avoiding v := by
  rw [sqWord_def]
  exact pow_mem (GX.inr_of_mem_avoiding hx) 2

/-- A conjugate atom `conjWord p` avoids a variable `v` when `p.1 ≠ v`. -/
theorem conjWord_mem_avoiding [DecidableEq X] {p : X × G} {v : X} (hp : p.1 ≠ v) :
    conjWord p ∈ GX.avoiding v := by
  rw [conjWord_def]
  exact mul_mem (mul_mem (inv_mem (GX.inr_of_mem_avoiding hp)) (GX.inl_mem_avoiding _ _))
    (GX.inr_of_mem_avoiding hp)

end Atoms

/-! ### Standard quadratic equations -/

/-- The standard quadratic equations over `G` in the variables `X`, of types (1)–(4). The
variables `xᵢ`, `yᵢ`, `zⱼ` are pairwise distinct and the coefficients `cⱼ` and `d` are
nontrivial; equations without commutators or squares are of type (2), so the non-orientable types
have positive genus. -/
inductive Standard (G X : Type*) [Group G] where
  /-- Type (1): `∏ᵢ₌₁ⁿ [xᵢ, yᵢ] = 1` with `n > 0`. -/
  | orientable (n : ℕ) (hn : 0 < n) (x y : Fin n → X) (inj : (Sum.elim x y).Injective)
  /-- Type (2): `∏ᵢ₌₁ⁿ [xᵢ, yᵢ] ∏ⱼ₌₁ᵐ zⱼ⁻¹ cⱼ zⱼ d = 1` with `n + m ≥ 1`. -/
  | orientableCoeff (n m : ℕ) (hnm : 0 < n + m) (x y : Fin n → X) (z : Fin m → X)
      (inj : (Sum.elim (Sum.elim x y) z).Injective) (c : Fin m → G) (hc : ∀ j, c j ≠ 1) (d : G)
      (hd : d ≠ 1)
  /-- Type (3): `∏ᵢ₌₁ⁿ xᵢ² = 1` with `n > 0`. -/
  | nonorientable (n : ℕ) (hn : 0 < n) (x : Fin n → X) (inj : x.Injective)
  /-- Type (4): `∏ᵢ₌₁ⁿ xᵢ² ∏ⱼ₌₁ᵐ zⱼ⁻¹ cⱼ zⱼ d = 1` with `n > 0`. -/
  | nonorientableCoeff (n m : ℕ) (hn : 0 < n) (x : Fin n → X) (z : Fin m → X)
      (inj : (Sum.elim x z).Injective) (c : Fin m → G) (hc : ∀ j, c j ≠ 1) (d : G) (hd : d ≠ 1)

namespace Standard

private inductive AtomSpec (G X : Type*) where
  | comm (x y : X)
  | sq (x : X)
  | conj (z : X) (c : G)

private def AtomSpec.toWord : AtomSpec G X → GX G X
  | .comm x y => commWord (x, y)
  | .sq x => sqWord x
  | .conj z c => conjWord (z, c)

private def atomSpecs : Standard G X → List (AtomSpec G X)
  | orientable _ _ x y _ => List.ofFn fun i => .comm (x i) (y i)
  | orientableCoeff _ _ _ x y z _ c _ _ _ =>
    List.ofFn (fun i => .comm (x i) (y i)) ++ List.ofFn fun j => .conj (z j) (c j)
  | nonorientable _ _ x _ => List.ofFn fun i => .sq (x i)
  | nonorientableCoeff _ _ _ x z _ c _ _ _ =>
    List.ofFn (fun i => .sq (x i)) ++ List.ofFn fun j => .conj (z j) (c j)

/-- The atoms of a standard quadratic equation, in order: the commutators `[xᵢ, yᵢ]` or the
squares `xᵢ²`, followed by the conjugates `zⱼ⁻¹ cⱼ zⱼ`. -/
def atoms (S : Standard G X) : List (GX G X) :=
  S.atomSpecs.map AtomSpec.toWord

/-- The constant coefficient `d` of a standard quadratic equation of type (2) or (4), and `1` for
the types (1) and (3), which have no constant. -/
def constant : Standard G X → G
  | orientable .. => 1
  | orientableCoeff _ _ _ _ _ _ _ _ _ d _ => d
  | nonorientable .. => 1
  | nonorientableCoeff _ _ _ _ _ _ _ _ d _ => d

/-- The left side `r₁ ⋯ r_k d` of a standard quadratic equation `r₁ ⋯ r_k d = 1`, as an element of
`G[X]`. -/
def toWord (S : Standard G X) : GX G X :=
  S.atoms.prod * inl S.constant

/-- The atomic rank `r(S)` of a standard quadratic equation: the number of its atoms. -/
def atomicRank (S : Standard G X) : ℕ :=
  S.atoms.length

/-- The genus `n` of a standard quadratic equation: its number of commutators or squares. -/
def genus : Standard G X → ℕ
  | orientable n .. => n
  | orientableCoeff n .. => n
  | nonorientable n .. => n
  | nonorientableCoeff n .. => n

/-- A standard quadratic equation is orientable when it is of type (1) or (2). -/
def IsOrientable : Standard G X → Prop
  | orientable .. => True
  | orientableCoeff .. => True
  | nonorientable .. => False
  | nonorientableCoeff .. => False

/-- The Euler characteristic `χ(S)` of the surface of a standard quadratic equation: of genus `n`,
orientable or not, with one boundary component for each coefficient `cⱼ` and one for `d` when it
occurs. -/
def eulerChar : Standard G X → ℤ
  | orientable n .. => 2 - 2 * n
  | orientableCoeff n m .. => 2 - 2 * n - (m + 1)
  | nonorientable n .. => 2 - n
  | nonorientableCoeff n m .. => 2 - n - (m + 1)

/-- The set of variables occurring in a standard quadratic equation. -/
def vars : Standard G X → Set X
  | orientable _ _ x y _ => Set.range (Sum.elim x y)
  | orientableCoeff _ _ _ x y z _ _ _ _ _ => Set.range (Sum.elim (Sum.elim x y) z)
  | nonorientable _ _ x _ => Set.range x
  | nonorientableCoeff _ _ _ x z _ _ _ _ _ => Set.range (Sum.elim x z)

/-- The coefficients `d, c₁, …, c_m` of a standard quadratic equation. -/
def coeffs : Standard G X → List G
  | orientable .. => []
  | orientableCoeff _ _ _ _ _ _ _ c _ d _ => d :: List.ofFn c
  | nonorientable .. => []
  | nonorientableCoeff _ _ _ _ _ _ c _ d _ => d :: List.ofFn c

/-- The invariant `κ(S)` of a standard quadratic equation: the number of its variables, plus one
when the coefficient `d` occurs. -/
def kappa : Standard G X → ℕ
  | orientable n .. => 2 * n
  | orientableCoeff n m .. => 2 * n + m + 1
  | nonorientable n .. => n
  | nonorientableCoeff n m .. => n + m + 1

section Accessors

variable {n m : ℕ} {x y : Fin n → X} {z : Fin m → X} {c : Fin m → G} {d : G}

@[simp]
theorem atoms_orientable (hn : 0 < n) (inj : (Sum.elim x y).Injective) :
    (orientable n hn x y inj).atoms =
      List.ofFn fun i => ⁅(inr (FreeGroup.of (x i)) : GX G X)⁻¹,
        (inr (FreeGroup.of (y i)) : GX G X)⁻¹⁆ := by
  simp [atoms, atomSpecs, AtomSpec.toWord, Function.comp_def, commWord_def]

@[simp]
theorem atoms_orientableCoeff (hnm : 0 < n + m) (inj : (Sum.elim (Sum.elim x y) z).Injective)
    (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    (orientableCoeff n m hnm x y z inj c hc d hd).atoms =
      List.ofFn (fun i => ⁅(inr (FreeGroup.of (x i)) : GX G X)⁻¹,
          (inr (FreeGroup.of (y i)) : GX G X)⁻¹⁆) ++
        List.ofFn fun j => (inr (FreeGroup.of (z j)) : GX G X)⁻¹ * inl (c j) *
          inr (FreeGroup.of (z j)) := by
  simp [atoms, atomSpecs, AtomSpec.toWord, Function.comp_def, commWord_def, conjWord_def]

@[simp]
theorem atoms_nonorientable {x : Fin n → X} (hn : 0 < n) (inj : x.Injective) :
    (nonorientable (G := G) n hn x inj).atoms =
      List.ofFn fun i => (inr (FreeGroup.of (x i)) : GX G X) ^ 2 := by
  simp [atoms, atomSpecs, AtomSpec.toWord, Function.comp_def, sqWord_def]

@[simp]
theorem atoms_nonorientableCoeff {x : Fin n → X} (hn : 0 < n) (inj : (Sum.elim x z).Injective)
    (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    (nonorientableCoeff n m hn x z inj c hc d hd).atoms =
      List.ofFn (fun i => (inr (FreeGroup.of (x i)) : GX G X) ^ 2) ++
        List.ofFn fun j => (inr (FreeGroup.of (z j)) : GX G X)⁻¹ * inl (c j) *
          inr (FreeGroup.of (z j)) := by
  simp [atoms, atomSpecs, AtomSpec.toWord, Function.comp_def, sqWord_def, conjWord_def]

@[simp]
theorem constant_orientable (hn : 0 < n) (inj : (Sum.elim x y).Injective) :
    (orientable (G := G) n hn x y inj).constant = 1 := (rfl)

@[simp]
theorem constant_orientableCoeff (hnm : 0 < n + m) (inj : (Sum.elim (Sum.elim x y) z).Injective)
    (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    (orientableCoeff n m hnm x y z inj c hc d hd).constant = d := (rfl)

@[simp]
theorem constant_nonorientable {x : Fin n → X} (hn : 0 < n) (inj : x.Injective) :
    (nonorientable (G := G) n hn x inj).constant = 1 := (rfl)

@[simp]
theorem constant_nonorientableCoeff {x : Fin n → X} (hn : 0 < n)
    (inj : (Sum.elim x z).Injective) (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    (nonorientableCoeff n m hn x z inj c hc d hd).constant = d := (rfl)

theorem toWord_def (S : Standard G X) : S.toWord = S.atoms.prod * inl S.constant := (rfl)

/-- The standard quadratic equation of type (4) with one square and no conjugated coefficient is
`x² d = 1`. -/
@[simp]
theorem toWord_nonorientableCoeff_one_zero {x : Fin 1 → X} {z : Fin 0 → X} {c : Fin 0 → G}
    (inj : (Sum.elim x z).Injective) (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    (nonorientableCoeff 1 0 one_pos x z inj c hc d hd).toWord =
      inr (FreeGroup.of (x 0)) ^ 2 * inl d := by
  simp [toWord_def]

theorem atomicRank_def (S : Standard G X) : S.atomicRank = S.atoms.length := (rfl)

@[simp]
theorem atomicRank_orientable (hn : 0 < n) (inj : (Sum.elim x y).Injective) :
    (orientable (G := G) n hn x y inj).atomicRank = n := by
  simp [atomicRank_def]

@[simp]
theorem atomicRank_orientableCoeff (hnm : 0 < n + m)
    (inj : (Sum.elim (Sum.elim x y) z).Injective) (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    (orientableCoeff n m hnm x y z inj c hc d hd).atomicRank = n + m := by
  simp [atomicRank_def]

@[simp]
theorem atomicRank_nonorientable {x : Fin n → X} (hn : 0 < n) (inj : x.Injective) :
    (nonorientable (G := G) n hn x inj).atomicRank = n := by
  simp [atomicRank_def]

@[simp]
theorem atomicRank_nonorientableCoeff {x : Fin n → X} (hn : 0 < n)
    (inj : (Sum.elim x z).Injective) (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    (nonorientableCoeff n m hn x z inj c hc d hd).atomicRank = n + m := by
  simp [atomicRank_def]

@[simp]
theorem genus_orientable (hn : 0 < n) (inj : (Sum.elim x y).Injective) :
    (orientable (G := G) n hn x y inj).genus = n := (rfl)

@[simp]
theorem genus_orientableCoeff (hnm : 0 < n + m) (inj : (Sum.elim (Sum.elim x y) z).Injective)
    (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    (orientableCoeff n m hnm x y z inj c hc d hd).genus = n := (rfl)

@[simp]
theorem genus_nonorientable {x : Fin n → X} (hn : 0 < n) (inj : x.Injective) :
    (nonorientable (G := G) n hn x inj).genus = n := (rfl)

@[simp]
theorem genus_nonorientableCoeff {x : Fin n → X} (hn : 0 < n) (inj : (Sum.elim x z).Injective)
    (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    (nonorientableCoeff n m hn x z inj c hc d hd).genus = n := (rfl)

@[simp]
theorem isOrientable_orientable (hn : 0 < n) (inj : (Sum.elim x y).Injective) :
    (orientable (G := G) n hn x y inj).IsOrientable := trivial

@[simp]
theorem isOrientable_orientableCoeff (hnm : 0 < n + m)
    (inj : (Sum.elim (Sum.elim x y) z).Injective) (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    (orientableCoeff n m hnm x y z inj c hc d hd).IsOrientable := trivial

@[simp]
theorem not_isOrientable_nonorientable {x : Fin n → X} (hn : 0 < n) (inj : x.Injective) :
    ¬(nonorientable (G := G) n hn x inj).IsOrientable := not_false

@[simp]
theorem not_isOrientable_nonorientableCoeff {x : Fin n → X} (hn : 0 < n)
    (inj : (Sum.elim x z).Injective) (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    ¬(nonorientableCoeff n m hn x z inj c hc d hd).IsOrientable := not_false

@[simp]
theorem eulerChar_orientable (hn : 0 < n) (inj : (Sum.elim x y).Injective) :
    (orientable (G := G) n hn x y inj).eulerChar = 2 - 2 * n := (rfl)

@[simp]
theorem eulerChar_orientableCoeff (hnm : 0 < n + m)
    (inj : (Sum.elim (Sum.elim x y) z).Injective) (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    (orientableCoeff n m hnm x y z inj c hc d hd).eulerChar = 2 - 2 * n - (m + 1) := (rfl)

@[simp]
theorem eulerChar_nonorientable {x : Fin n → X} (hn : 0 < n) (inj : x.Injective) :
    (nonorientable (G := G) n hn x inj).eulerChar = 2 - n := (rfl)

@[simp]
theorem eulerChar_nonorientableCoeff {x : Fin n → X} (hn : 0 < n)
    (inj : (Sum.elim x z).Injective) (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    (nonorientableCoeff n m hn x z inj c hc d hd).eulerChar = 2 - n - (m + 1) := (rfl)

@[simp]
theorem vars_orientable (hn : 0 < n) (inj : (Sum.elim x y).Injective) :
    (orientable (G := G) n hn x y inj).vars = Set.range (Sum.elim x y) := (rfl)

@[simp]
theorem vars_orientableCoeff (hnm : 0 < n + m) (inj : (Sum.elim (Sum.elim x y) z).Injective)
    (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    (orientableCoeff n m hnm x y z inj c hc d hd).vars =
      Set.range (Sum.elim (Sum.elim x y) z) := (rfl)

@[simp]
theorem vars_nonorientable {x : Fin n → X} (hn : 0 < n) (inj : x.Injective) :
    (nonorientable (G := G) n hn x inj).vars = Set.range x := (rfl)

@[simp]
theorem vars_nonorientableCoeff {x : Fin n → X} (hn : 0 < n) (inj : (Sum.elim x z).Injective)
    (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    (nonorientableCoeff n m hn x z inj c hc d hd).vars = Set.range (Sum.elim x z) := (rfl)

@[simp]
theorem coeffs_orientable (hn : 0 < n) (inj : (Sum.elim x y).Injective) :
    (orientable (G := G) n hn x y inj).coeffs = [] := (rfl)

@[simp]
theorem coeffs_orientableCoeff (hnm : 0 < n + m) (inj : (Sum.elim (Sum.elim x y) z).Injective)
    (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    (orientableCoeff n m hnm x y z inj c hc d hd).coeffs = d :: List.ofFn c := (rfl)

@[simp]
theorem coeffs_nonorientable {x : Fin n → X} (hn : 0 < n) (inj : x.Injective) :
    (nonorientable (G := G) n hn x inj).coeffs = [] := (rfl)

@[simp]
theorem coeffs_nonorientableCoeff {x : Fin n → X} (hn : 0 < n) (inj : (Sum.elim x z).Injective)
    (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    (nonorientableCoeff n m hn x z inj c hc d hd).coeffs = d :: List.ofFn c := (rfl)

@[simp]
theorem kappa_orientable (hn : 0 < n) (inj : (Sum.elim x y).Injective) :
    (orientable (G := G) n hn x y inj).kappa = 2 * n := (rfl)

@[simp]
theorem kappa_orientableCoeff (hnm : 0 < n + m) (inj : (Sum.elim (Sum.elim x y) z).Injective)
    (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    (orientableCoeff n m hnm x y z inj c hc d hd).kappa = 2 * n + m + 1 := (rfl)

@[simp]
theorem kappa_nonorientable {x : Fin n → X} (hn : 0 < n) (inj : x.Injective) :
    (nonorientable (G := G) n hn x inj).kappa = n := (rfl)

@[simp]
theorem kappa_nonorientableCoeff {x : Fin n → X} (hn : 0 < n) (inj : (Sum.elim x z).Injective)
    (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    (nonorientableCoeff n m hn x z inj c hc d hd).kappa = n + m + 1 := (rfl)

end Accessors

/-- A standard quadratic equation has positive atomic rank. -/
theorem atomicRank_pos (S : Standard G X) : 0 < S.atomicRank := by
  cases S <;> simp <;> lia

/-! ### Variables, coefficients and `κ` -/

section Kappa

variable {S : Standard G X}

/-- The coefficients of a standard quadratic equation are nontrivial. -/
theorem ne_one_of_mem_coeffs {g : G} (hg : g ∈ S.coeffs) : g ≠ 1 := by
  cases S <;> simp_all [List.mem_ofFn] <;> grind

@[simp]
theorem one_notMem_coeffs (S : Standard G X) : (1 : G) ∉ S.coeffs :=
  fun h => ne_one_of_mem_coeffs h rfl

@[simp]
theorem coeffs_eq_nil_iff : S.coeffs = [] ↔ S.constant = 1 := by
  cases S <;> simp_all

@[simp]
theorem constant_mem_coeffs_iff : S.constant ∈ S.coeffs ↔ S.constant ≠ 1 := by
  cases S <;> simp_all

theorem finite_vars (S : Standard G X) : S.vars.Finite := by
  cases S <;> exact Set.finite_range _

instance (S : Standard G X) : Finite S.vars :=
  S.finite_vars.to_subtype

/-- A standard quadratic equation without the coefficient `d` has `κ(S)` variables. -/
theorem kappa_eq_ncard_vars (h : S.constant = 1) : S.kappa = S.vars.ncard := by
  cases S <;> simp_all [-Set.Sum.elim_range, Set.ncard_range_of_injective, two_mul]

/-- A standard quadratic equation with the coefficient `d` has `κ(S) - 1` variables. -/
theorem kappa_eq_ncard_vars_add_one (h : S.constant ≠ 1) : S.kappa = S.vars.ncard + 1 := by
  cases S <;> simp_all [-Set.Sum.elim_range, Set.ncard_range_of_injective, two_mul]

/-- A standard quadratic equation without the coefficient `d` in which every variable of `X`
occurs has `κ(S) = |X|`. -/
theorem kappa_eq_card_of_vars_eq_univ (hX : S.vars = Set.univ) (h : S.constant = 1) :
    S.kappa = Nat.card X := by
  rw [kappa_eq_ncard_vars h, hX, Set.ncard_univ]

/-- A standard quadratic equation with the coefficient `d` in which every variable of `X` occurs
has `κ(S) = |X| + 1`. -/
theorem kappa_eq_card_add_one_of_vars_eq_univ (hX : S.vars = Set.univ) (h : S.constant ≠ 1) :
    S.kappa = Nat.card X + 1 := by
  rw [kappa_eq_ncard_vars_add_one h, hX, Set.ncard_univ]

/-- An orientable standard quadratic equation of genus `n` with `r` atoms has `n + r`
variables. -/
theorem ncard_vars_of_isOrientable (h : S.IsOrientable) :
    S.vars.ncard = S.genus + S.atomicRank := by
  cases S <;> simp_all [-Set.Sum.elim_range, Set.ncard_range_of_injective, add_assoc]

/-- A non-orientable standard quadratic equation has one variable for each atom. -/
theorem ncard_vars_of_not_isOrientable (h : ¬S.IsOrientable) : S.vars.ncard = S.atomicRank := by
  cases S <;> simp_all [-Set.Sum.elim_range, Set.ncard_range_of_injective]

/-- An orientable standard quadratic equation without the constant `d` is of type (1),
`∏ᵢ₌₁ⁿ [xᵢ, yᵢ] = 1`. -/
theorem exists_eq_orientable_of_isOrientable (ho : S.IsOrientable) (hc : S.constant = 1) :
    ∃ n hn x y inj, S = orientable n hn x y inj := by
  cases S with
  | orientable n hn x y inj => exact ⟨n, hn, x, y, inj, rfl⟩
  | _ => simp_all [IsOrientable]

/-- A non-orientable standard quadratic equation without the constant `d` is of type (3),
`∏ᵢ₌₁ⁿ xᵢ² = 1`. -/
theorem exists_eq_nonorientable_of_not_isOrientable (ho : ¬S.IsOrientable)
    (hc : S.constant = 1) : ∃ n hn x inj, S = nonorientable n hn x inj := by
  cases S with
  | nonorientable n hn x inj => exact ⟨n, hn, x, inj, rfl⟩
  | _ => simp_all [IsOrientable]

/-- The Euler characteristic of a standard quadratic equation is `2 - κ(S)`. -/
theorem eulerChar_eq_two_sub_kappa (S : Standard G X) : S.eulerChar = 2 - S.kappa := by
  cases S <;> simp <;> lia

/-- A standard quadratic equation with `κ(S) ≥ 4` has at least two atoms. -/
theorem two_le_atomicRank_of_four_le_kappa (h : 4 ≤ S.kappa) : 2 ≤ S.atomicRank := by
  cases S <;> simp_all <;> lia

/-- The value of `r₁ ⋯ r_k d` at a point is the product of the values of the atoms `rᵢ` and of the
constant `d` (which is `1` for the types without coefficients). -/
-- Low priority: the closed forms of the four types of equation (`eval_toWord_orientable` and its
-- analogues in `Quadratic/Surface.lean`) and of restrictions are tried first.
@[simp low]
theorem eval_toWord (S : Standard G X) (ι : G →* H) (v : X → H) :
    eval ι v S.toWord = (S.atoms.map (eval ι v)).prod * ι S.constant := by
  simp [toWord_def, map_list_prod]

/-- A point is a solution of `r₁ ⋯ r_k d = 1` exactly when the product of the values of the atoms
is the inverse of the value of `d`. -/
theorem mem_V_toWord_iff {ι : G →* H} {v : X → H} :
    v ∈ V ι {S.toWord} ↔ (S.atoms.map (eval ι v)).prod * ι S.constant = 1 := by
  rw [mem_V, Set.forall_mem_singleton, eval_toWord]

/-- The values of the atoms of a standard quadratic equation depend only on the values of its
coefficients and of its variables. -/
theorem map_eval_atoms_congr {ι ι' : G →* H} {v v' : X → H} (hι : ∀ g ∈ S.coeffs, ι g = ι' g)
    (hv : ∀ x ∈ S.vars, v x = v' x) : S.atoms.map (eval ι v) = S.atoms.map (eval ι' v') := by
  refine List.map_congr_left ?_
  cases S <;> simp_all [or_imp, forall_and, map_commutatorElement]

/-- The value of a standard quadratic equation depends only on the values of its coefficients
and of its variables. -/
theorem eval_toWord_congr {ι ι' : G →* H} {v v' : X → H} (hι : ∀ g ∈ S.coeffs, ι g = ι' g)
    (hv : ∀ x ∈ S.vars, v x = v' x) : eval ι v S.toWord = eval ι' v' S.toWord := by
  rw [eval_toWord, eval_toWord, map_eval_atoms_congr hι hv]
  by_cases h : S.constant = 1
  · simp [h]
  · rw [hι _ (constant_mem_coeffs_iff.2 h)]

end Kappa

/-! ### Separability and complete spectrum -/

section Atoms

variable {S : Standard G X} {ι : G →* H}

-- Values of the words `F i` can be prescribed independently when, along an injective `e`, each
-- `F i` depends only on the variables `e a` with `p a = i`.
private theorem exists_map_eval_ofFn_eq {k : ℕ} {K : Type*} {e : K → X} (he : e.Injective)
    (p : K → Fin k) {F : Fin k → GX G X}
    (hF : ∀ i, DependsOn (fun v : X → H => eval ι v (F i)) (e '' (p ⁻¹' {i})))
    {l : List H} (h : List.Forall₂ (fun r a => ∃ v : X → H, eval ι v r = a) (List.ofFn F) l) :
    ∃ v : X → H, (List.ofFn F).map (eval ι v) = l := by
  obtain ⟨a, ha, rfl⟩ := List.forall₂_ofFn_left_iff.1 h
  choose V hV using ha
  refine ⟨Function.extend e (fun a => V (p a) (e a)) 1, ?_⟩
  rw [List.map_ofFn, List.ofFn_inj]
  funext i
  exact ((he.factorsThrough _).apply_extend_eq_apply 1 (hF i)).trans (hV i)

/-- **Separability.** The atoms of a standard quadratic equation are words in pairwise disjoint
sets of variables, so values that each atom takes at some point are taken by all the atoms at one
point. -/
theorem exists_map_eval_atoms_eq {l : List H}
    (h : List.Forall₂ (fun r a => ∃ v : X → H, eval ι v r = a) S.atoms l) :
    ∃ v : X → H, S.atoms.map (eval ι v) = l := by
  cases S with
  | orientable n hn x y inj =>
    rw [atoms_orientable] at h ⊢
    refine exists_map_eval_ofFn_eq inj (Sum.elim id id) (fun i v w hvw => ?_) h
    simp_all [map_commutatorElement]
  | orientableCoeff n m hnm x y z inj c hc d hd =>
    rw [atoms_orientableCoeff, ← List.ofFn_fin_append] at h ⊢
    refine exists_map_eval_ofFn_eq inj
      (Sum.elim (Sum.elim (Fin.castAdd m) (Fin.castAdd m)) (Fin.natAdd n)) (fun i v w hvw => ?_) h
    induction i using Fin.addCases <;> simp_all [Sum.forall, map_commutatorElement]
  | nonorientable n hn x inj =>
    rw [atoms_nonorientable] at h ⊢
    refine exists_map_eval_ofFn_eq inj id (fun i v w hvw => ?_) h
    simp_all
  | nonorientableCoeff n m hn x z inj c hc d hd =>
    rw [atoms_nonorientableCoeff, ← List.ofFn_fin_append] at h ⊢
    refine exists_map_eval_ofFn_eq inj (Sum.elim (Fin.castAdd m) (Fin.natAdd n))
      (fun i v w hvw => ?_) h
    induction i using Fin.addCases <;> simp_all

-- Each atom is a word in the variables alone, a commutator or a square, or the conjugate
-- `z⁻¹ c z` of a coefficient.
private theorem exists_inr_eq_or_exists_conj_eq_of_mem_atoms :
    ∀ r ∈ S.atoms, (∃ w : FreeGroup X, inr w = r) ∨
      ∃ (z : X) (c : G), (inr (FreeGroup.of z))⁻¹ * inl c * inr (FreeGroup.of z) = r := by
  have hcomm (a b : X) : (inr ⁅(FreeGroup.of a)⁻¹, (FreeGroup.of b)⁻¹⁆ : GX G X) =
      ⁅(inr (FreeGroup.of a) : GX G X)⁻¹, (inr (FreeGroup.of b))⁻¹⁆ := by
    simp [map_commutatorElement]
  cases S <;> simp only [atoms_orientable, atoms_orientableCoeff, atoms_nonorientable,
    atoms_nonorientableCoeff, List.forall_mem_append, List.forall_mem_ofFn_iff]
  · exact fun i => .inl ⟨_, hcomm ..⟩
  · exact ⟨fun i => .inl ⟨_, hcomm ..⟩, fun j => .inr ⟨_, _, rfl⟩⟩
  · exact fun i => .inl ⟨_, map_pow ..⟩
  · exact ⟨fun i => .inl ⟨_, map_pow ..⟩, fun j => .inr ⟨_, _, rfl⟩⟩

/-- **Complete spectrum.** The values of an atom of a standard quadratic equation are closed under
conjugation. -/
theorem exists_eval_eq_of_mem_atoms_of_isConj {r : GX G X} (hr : r ∈ S.atoms) (v : X → H) {a : H}
    (ha : IsConj (eval ι v r) a) : ∃ w : X → H, eval ι w r = a := by
  obtain ⟨u, rfl⟩ | ⟨z, c, rfl⟩ := exists_inr_eq_or_exists_conj_eq_of_mem_atoms r hr
  · rw [eval_inr] at ha
    simpa only [eval_inr] using FreeGroup.exists_lift_eq_of_isConj v ha
  · exact exists_eval_inv_mul_inl_mul_eq_iff_isConj.2
      ((exists_eval_inv_mul_inl_mul_eq_iff_isConj.1 ⟨v, rfl⟩).trans ha)

end Atoms

/-! ### Standard equations are quadratic -/

section IsQuadratic

private def AtomSpec.letters : AtomSpec G X → List (G ⊕ X × Bool)
  | .comm x y => commLetters x y
  | .sq x => sqLetters x
  | .conj z c => conjLetters z c

private def AtomSpec.vars : AtomSpec G X → List X
  | .comm x y => [x, y]
  | .sq x => [x]
  | .conj z _ => [z]

private def AtomSpec.headVar : AtomSpec G X → X
  | .comm x _ | .sq x | .conj x _ => x

private def AtomSpec.lastVar : AtomSpec G X → X
  | .comm _ y | .sq y | .conj y _ => y

omit [Group G] in
private theorem AtomSpec.letters_ne_nil (a : AtomSpec G X) : a.letters ≠ [] := by
  cases a <;> simp [AtomSpec.letters, commLetters, sqLetters, conjLetters]

omit [Group G] in
private theorem AtomSpec.mem_head? {a : AtomSpec G X} {l : G ⊕ X × Bool}
    (hl : l ∈ a.letters.head?) : ∃ b, l = .inr (a.headVar, b) := by
  cases a <;> simp_all [AtomSpec.letters, commLetters, sqLetters, conjLetters, AtomSpec.headVar]

omit [Group G] in
private theorem AtomSpec.mem_getLast? {a : AtomSpec G X} {l : G ⊕ X × Bool}
    (hl : l ∈ a.letters.getLast?) : l = .inr (a.lastVar, true) := by
  cases a <;> simp_all [AtomSpec.letters, commLetters, sqLetters, conjLetters, AtomSpec.lastVar]

omit [Group G] in
private theorem AtomSpec.not_combines_of_ne {a₁ a₂ : AtomSpec G X}
    (hne : a₁.lastVar ≠ a₂.headVar) :
    ∀ x ∈ a₁.letters.getLast?, ∀ y ∈ a₂.letters.head?, ¬GX.Combines x y := by
  intro x hx y hy
  obtain rfl := a₁.mem_getLast? hx
  obtain ⟨b, rfl⟩ := a₂.mem_head? hy
  simp [hne]

omit [Group G] in
private theorem AtomSpec.not_combines_sq (a₁ : AtomSpec G X) (x : X) :
    ∀ u ∈ a₁.letters.getLast?, ∀ v ∈ (AtomSpec.sq x : AtomSpec G X).letters.head?,
      ¬GX.Combines u v := by
  intro u hu v hv
  obtain rfl := a₁.mem_getLast? hu
  simp only [AtomSpec.letters, sqLetters, List.head?_cons, Option.mem_def, Option.some.injEq] at hv
  subst hv
  simp

omit [Group G] in
private theorem AtomSpec.not_combines_inl_head (d : G) (a : AtomSpec G X) :
    ∀ b ∈ a.letters.head?, ¬GX.Combines (.inl d) b := by
  intro b hb
  obtain ⟨e, rfl⟩ := a.mem_head? hb
  simp

omit [Group G] in
private theorem AtomSpec.not_combines_getLast_inl (a : AtomSpec G X) (d : G) :
    ∀ c ∈ a.letters.getLast?, ¬GX.Combines c (.inl d) := by
  intro c hc
  obtain rfl := a.mem_getLast? hc
  simp

private def wordLetters : Standard G X → List (G ⊕ X × Bool)
  | S@(orientable ..) | S@(nonorientable ..) => (S.atomSpecs.map AtomSpec.letters).flatten
  | S@(orientableCoeff _ _ _ _ _ _ _ _ _ d _) | S@(nonorientableCoeff _ _ _ _ _ _ _ _ d _) =>
    (S.atomSpecs.map AtomSpec.letters).flatten ++ [.inl d]

private theorem AtomSpec.prod_letters (a : AtomSpec G X) :
    (a.letters.map GX.letter).prod = a.toWord := by
  cases a with
  | comm a b => simp [AtomSpec.letters, AtomSpec.toWord, commLetters, commWord_def,
      commutatorElement_def, mul_assoc]
  | sq a => simp [AtomSpec.letters, AtomSpec.toWord, sqLetters, sqWord_def, pow_two]
  | conj a c => simp [AtomSpec.letters, AtomSpec.toWord, conjLetters, conjWord_def, mul_assoc]

private theorem prod_wordLetters (S : Standard G X) :
    ((wordLetters S).map GX.letter).prod = S.toWord := by
  have hprod : ((S.atomSpecs.map AtomSpec.letters).flatten.map GX.letter).prod = S.atoms.prod := by
    simp [atoms, List.map_flatten, List.prod_flatten, List.map_map, Function.comp_def,
      AtomSpec.prod_letters]
  cases S <;>
    simp only [wordLetters, List.map_append, List.map_cons, List.map_nil, List.prod_append,
      List.prod_cons, List.prod_nil, GX.letter_inl, mul_one, hprod, toWord_def, constant_orientable,
      constant_orientableCoeff, constant_nonorientable, constant_nonorientableCoeff, map_one]

/-- Flattening the reduced letter blocks of a list of `AtomSpec`s whose adjacent and wraparound
pairs do not combine across boundaries yields a cyclically reduced word. -/
private theorem isCyclicallyReduced_flatten_atomSpecs (as : List (AtomSpec G X))
    (hred : ∀ a ∈ as, GX.IsReduced a.letters)
    (hadj : as.IsChain fun a₁ a₂ =>
      ∀ x ∈ a₁.letters.getLast?, ∀ y ∈ a₂.letters.head?, ¬GX.Combines x y)
    (hwrap : ∀ a₁ ∈ as.getLast?, ∀ a₂ ∈ as.head?,
      ∀ x ∈ a₁.letters.getLast?, ∀ y ∈ a₂.letters.head?, ¬GX.Combines x y) :
    GX.IsCyclicallyReduced (as.map AtomSpec.letters).flatten := by
  refine (GX.isCyclicallyReduced_flatten_iff (fun _ hl => by
    obtain ⟨_, _, rfl⟩ := List.mem_map.1 hl; exact AtomSpec.letters_ne_nil _)).2 ⟨?_, ?_, ?_⟩
  · intro l hl
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hl
    exact hred a ha
  · rwa [List.isChain_map]
  · intro _ l₁ hl₁ l₂ hl₂
    rw [List.getLast?_map, Option.mem_map] at hl₁
    rw [List.head?_map, Option.mem_map] at hl₂
    obtain ⟨a₁, ha₁, rfl⟩ := hl₁
    obtain ⟨a₂, ha₂, rfl⟩ := hl₂
    exact hwrap a₁ ha₁ a₂ ha₂

/-- Appending a nontrivial constant `.inl d` to the flattened letter blocks of a nodup-indexed
family of reduced `AtomSpec`s whose distinct indices have `lastVar ≠ headVar` yields a cyclically
reduced word. -/
private theorem isCyclicallyReduced_flatten_atomSpecs_append_inl {n m : ℕ}
    (g : Fin n ⊕ Fin m → AtomSpec G X) {d : G}
    (hred : ∀ s, GX.IsReduced (g s).letters)
    (hne : ∀ s₁ s₂, s₁ ≠ s₂ → (g s₁).lastVar ≠ (g s₂).headVar)
    (hd : d ≠ 1) :
    GX.IsCyclicallyReduced
      (((((List.finRange n).map Sum.inl ++ (List.finRange m).map Sum.inr).map g).map
        AtomSpec.letters).flatten ++ [.inl d]) := by
  have hnd : ((List.finRange n).map Sum.inl ++ (List.finRange m).map Sum.inr :
      List (Fin n ⊕ Fin m)).Nodup :=
    ((List.nodup_finRange n).map Sum.inl_injective).append
      ((List.nodup_finRange m).map Sum.inr_injective) (by simp [List.Disjoint])
  refine GX.isCyclicallyReduced_flatten_append_singleton
    (fun _ hl => by obtain ⟨_, _, rfl⟩ := List.mem_map.1 hl; exact AtomSpec.letters_ne_nil _)
    (fun l hl => by
      obtain ⟨_, ha, rfl⟩ := List.mem_map.1 hl
      obtain ⟨s, _, rfl⟩ := List.mem_map.1 ha
      exact hred s)
    ?_ (fun l hl => by
      obtain ⟨a, _, rfl⟩ := List.mem_map.1 (List.mem_of_head? hl)
      exact AtomSpec.not_combines_inl_head d a)
    (fun l hl => by
      obtain ⟨a, _, rfl⟩ := List.mem_map.1 (List.mem_of_getLast? hl)
      exact AtomSpec.not_combines_getLast_inl a d)
    (by simpa using hd)
  rw [List.map_map, List.isChain_map]
  exact hnd.isChain.imp fun s₁ s₂ hs => AtomSpec.not_combines_of_ne (hne s₁ s₂ hs)

-- Types (1) and (3) flatten `atomSpecs` via `isCyclicallyReduced_flatten_atomSpecs`;
-- types (2) and (4) append `.inl d` via `isCyclicallyReduced_flatten_atomSpecs_append_inl`.
private theorem isCyclicallyReduced_wordLetters (S : Standard G X) :
    GX.IsCyclicallyReduced (wordLetters S) := by
  cases S with
  | orientable n hn x y inj =>
    have hxy (i j : Fin n) : y i ≠ x j := ((Sum.elim_injective.1 inj).2.2 j i).symm
    refine isCyclicallyReduced_flatten_atomSpecs _
      (fun a ha => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 (by simpa [atomSpecs] using ha)
        exact isReduced_commLetters (hxy i i).symm)
      (by
        rw [atomSpecs, List.ofFn_eq_map, List.isChain_map]
        exact (List.nodup_finRange n).isChain.imp fun _ _ _ =>
          AtomSpec.not_combines_of_ne (hxy _ _))
      (fun _ ha₁ _ ha₂ => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 (by simpa [atomSpecs] using List.mem_of_getLast? ha₁)
        obtain ⟨j, rfl⟩ := List.mem_ofFn.1 (by simpa [atomSpecs] using List.mem_of_head? ha₂)
        exact AtomSpec.not_combines_of_ne (hxy i j))
  | nonorientable n hn x inj =>
    refine isCyclicallyReduced_flatten_atomSpecs _
      (fun a ha => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 (by simpa [atomSpecs] using ha)
        exact isReduced_sqLetters _)
      (by
        rw [atomSpecs, List.ofFn_eq_map, List.isChain_map]
        exact (List.nodup_finRange n).isChain.imp fun _ _ _ => AtomSpec.not_combines_sq _ _)
      (fun _ ha₁ _ ha₂ => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 (by simpa [atomSpecs] using List.mem_of_getLast? ha₁)
        obtain ⟨j, rfl⟩ := List.mem_ofFn.1 (by simpa [atomSpecs] using List.mem_of_head? ha₂)
        exact AtomSpec.not_combines_sq _ _)
  | orientableCoeff n m hnm x y z inj c hc d hd =>
    have hinj₁ := (Sum.elim_injective.1 inj).1
    let g : Fin n ⊕ Fin m → AtomSpec G X :=
      Sum.elim (fun i => .comm (x i) (y i)) (fun j => .conj (z j) (c j))
    have hatoms : (orientableCoeff n m hnm x y z inj c hc d hd).atomSpecs =
        ((List.finRange n).map Sum.inl ++ (List.finRange m).map Sum.inr).map g := by
      simp [atomSpecs, g, List.map_append, List.map_map, Function.comp_def, List.ofFn_eq_map]
    rw [wordLetters, hatoms]
    refine isCyclicallyReduced_flatten_atomSpecs_append_inl g (fun s => by
      rcases s with i | j
      · exact isReduced_commLetters ((Sum.elim_injective.1 hinj₁).2.2 i i)
      · exact isReduced_conjLetters (hc j)) (fun s₁ s₂ hs => ?_) hd
    rcases s₁ with i₁ | j₁ <;> rcases s₂ with i₂ | j₂
    · exact ((Sum.elim_injective.1 hinj₁).2.2 i₂ i₁).symm
    · exact (Sum.elim_injective.1 inj).2.2 (.inr i₁) j₂
    · exact ((Sum.elim_injective.1 inj).2.2 (.inl i₂) j₁).symm
    · exact fun h => hs (congrArg Sum.inr ((Sum.elim_injective.1 inj).2.1 h))
  | nonorientableCoeff n m hn x z inj c hc d hd =>
    let g : Fin n ⊕ Fin m → AtomSpec G X :=
      Sum.elim (fun i => .sq (x i)) (fun j => .conj (z j) (c j))
    have hatoms : (nonorientableCoeff n m hn x z inj c hc d hd).atomSpecs =
        ((List.finRange n).map Sum.inl ++ (List.finRange m).map Sum.inr).map g := by
      simp [atomSpecs, g, List.map_append, List.map_map, Function.comp_def, List.ofFn_eq_map]
    rw [wordLetters, hatoms]
    refine isCyclicallyReduced_flatten_atomSpecs_append_inl g (fun s => by
      rcases s with i | j
      · exact isReduced_sqLetters (x i)
      · exact isReduced_conjLetters (hc j)) (fun s₁ s₂ hs => ?_) hd
    have hne_v : Sum.elim x z s₁ ≠ Sum.elim x z s₂ := inj.ne hs
    rcases s₁ with i₁ | j₁ <;> rcases s₂ with i₂ | j₂ <;> exact hne_v

/-- The reduced word of the left side of a standard quadratic equation is cyclically reduced. -/
@[simp] theorem isCyclicallyReduced_reducedWord (S : Standard G X) :
    GX.IsCyclicallyReduced (GX.reducedWord S.toWord) := by
  have hc := isCyclicallyReduced_wordLetters S
  rwa [(GX.reducedWord_eq_iff hc.isReduced).2 (prod_wordLetters S)]

omit [Group G] in
private theorem AtomSpec.countVar_letters [DecidableEq X] (x : X) (a : AtomSpec G X) :
    GX.countVar x a.letters = 2 * a.vars.count x := by
  cases a with
  | comm u v =>
    by_cases hu : u = x <;> by_cases hv : v = x <;>
      simp [AtomSpec.letters, AtomSpec.vars, commLetters, hu, hv]
  | sq u =>
    by_cases hu : u = x <;> simp [AtomSpec.letters, AtomSpec.vars, sqLetters, hu]
  | conj u c =>
    by_cases hu : u = x <;> simp [AtomSpec.letters, AtomSpec.vars, conjLetters, hu]

private theorem countVar_wordLetters [DecidableEq X] (x : X) (S : Standard G X) :
    GX.countVar x (wordLetters S) = 2 * (S.atomSpecs.flatMap AtomSpec.vars).count x := by
  have hfl (as : List (AtomSpec G X)) :
      GX.countVar x (as.map AtomSpec.letters).flatten = 2 * (as.flatMap AtomSpec.vars).count x := by
    induction as with
    | nil => simp
    | cons a as ih =>
      simp [GX.countVar_append, AtomSpec.countVar_letters, List.count_append, ih, mul_add]
  cases S <;> simp [wordLetters, GX.countVar_append, hfl]

private theorem nodup_flatMap_atomSpecs_vars (S : Standard G X) :
    (S.atomSpecs.flatMap AtomSpec.vars).Nodup := by
  have hcomm {n : ℕ} {x y : Fin n → X} (h : (Sum.elim x y).Injective) :
      ((List.ofFn fun i => AtomSpec.comm (G := G) (x i) (y i)).flatMap AtomSpec.vars).Nodup := by
    have ⟨hx, hy, hxy⟩ := Sum.elim_injective.1 h
    rw [List.ofFn_eq_map, List.flatMap_map, List.nodup_flatMap]
    refine ⟨fun i _ => ?_, (List.nodup_finRange n).imp fun {i j} hij v hv₁ hv₂ => ?_⟩
    · simp only [AtomSpec.vars, List.nodup_cons, List.mem_singleton, List.not_mem_nil,
        not_false_eq_true, List.nodup_nil, and_true]
      exact hxy i i
    · simp only [AtomSpec.vars, List.mem_cons, List.not_mem_nil, or_false] at hv₁ hv₂
      rcases hv₁ with rfl | rfl <;> rcases hv₂ with h' | h'
      · exact hij (hx h')
      · exact hxy i j h'
      · exact hxy j i h'.symm
      · exact hij (hy h')
  have hsingle {n : ℕ} (f : Fin n → AtomSpec G X) (u : Fin n → X) (hu : u.Injective)
      (hvars : ∀ i, (f i).vars = [u i]) : ((List.ofFn f).flatMap AtomSpec.vars).Nodup := by
    rw [List.ofFn_eq_map, List.flatMap_map, List.nodup_flatMap]
    refine ⟨fun i _ => by simp [hvars], (List.nodup_finRange n).imp fun {i j} hij v hv₁ hv₂ => ?_⟩
    simp only [hvars, List.mem_singleton] at hv₁ hv₂
    exact hij (hu (hv₁.symm.trans hv₂))
  cases S with
  | orientable _ _ _ _ inj => exact hcomm inj
  | nonorientable _ _ _ inj => exact hsingle _ _ inj fun _ => rfl
  | orientableCoeff _ _ _ x y z inj _ _ _ _ =>
    have hinj := Sum.elim_injective.1 inj
    rw [atomSpecs, List.flatMap_append]
    refine (hcomm hinj.1).append (hsingle _ _ hinj.2.1 fun _ => rfl) fun v hv₁ hv₂ => ?_
    simp only [List.mem_flatMap, List.mem_ofFn] at hv₁ hv₂
    obtain ⟨_, ⟨i, rfl⟩, h₁⟩ := hv₁
    obtain ⟨_, ⟨j, rfl⟩, h₂⟩ := hv₂
    simp only [AtomSpec.vars, List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
    rcases h₁ with rfl | rfl
    · exact hinj.2.2 (.inl i) j h₂
    · exact hinj.2.2 (.inr i) j h₂
  | nonorientableCoeff _ _ _ x z inj _ _ _ _ =>
    have hinj := Sum.elim_injective.1 inj
    rw [atomSpecs, List.flatMap_append]
    refine (hsingle _ _ hinj.1 fun _ => rfl).append (hsingle _ _ hinj.2.1 fun _ => rfl)
      fun v hv₁ hv₂ => ?_
    simp only [List.mem_flatMap, List.mem_ofFn] at hv₁ hv₂
    obtain ⟨_, ⟨i, rfl⟩, h₁⟩ := hv₁
    obtain ⟨_, ⟨j, rfl⟩, h₂⟩ := hv₂
    simp only [AtomSpec.vars, List.mem_singleton] at h₁ h₂
    subst h₁
    exact hinj.2.2 i j h₂

private theorem mem_flatMap_atomSpecs_vars {S : Standard G X} {v : X} :
    v ∈ S.atomSpecs.flatMap AtomSpec.vars ↔ v ∈ S.vars := by
  cases S <;> simp [atomSpecs, AtomSpec.vars, List.mem_flatMap, List.mem_ofFn, exists_or, eq_comm]

/-- Each variable occurs twice in a standard quadratic equation if it belongs to `S.vars`, and
zero times otherwise. -/
theorem occurrences_toWord (S : Standard G X) (x : X) [Decidable (x ∈ S.vars)] :
    GX.occurrences x S.toWord = if x ∈ S.vars then 2 else 0 := by
  classical
  rw [← prod_wordLetters S, (isCyclicallyReduced_wordLetters S).isReduced.occurrences_prod,
    countVar_wordLetters]
  simp only [List.Nodup.count (nodup_flatMap_atomSpecs_vars S), mem_flatMap_atomSpecs_vars,
    mul_ite, mul_one, mul_zero]

/-- Every variable in `S.vars` occurs twice in the standard quadratic equation `S`. -/
theorem occurrences_toWord_of_mem_vars {S : Standard G X} {x : X} (hx : x ∈ S.vars) :
    GX.occurrences x S.toWord = 2 := by classical simp [occurrences_toWord, hx]

/-- A variable outside `S.vars` does not occur in the standard quadratic equation `S`. -/
theorem occurrences_toWord_of_notMem_vars {S : Standard G X} {x : X} (hx : x ∉ S.vars) :
    GX.occurrences x S.toWord = 0 := by classical simp [occurrences_toWord, hx]

/-- Every standard quadratic equation is strictly quadratic (see `occurrences_toWord` for the
per-variable occurrence counts). -/
theorem isStrictlyQuadratic (S : Standard G X) : IsStrictlyQuadratic {S.toWord} := by
  classical
  exact isStrictlyQuadratic_singleton.2 fun x => by rw [occurrences_toWord]; split_ifs <;> simp

/-- Every standard quadratic equation is quadratic: each of its variables occurs at most twice. -/
theorem isQuadratic (S : Standard G X) : IsQuadratic {S.toWord} := S.isStrictlyQuadratic.isQuadratic

/-- A variable belongs to `S.vars` if and only if it occurs in `S.toWord`. -/
theorem mem_vars_iff_occurrences_toWord_ne_zero {S : Standard G X} {x : X} :
    x ∈ S.vars ↔ GX.occurrences x S.toWord ≠ 0 := by
  classical rw [occurrences_toWord]; split_ifs with hx <;> simp [hx]

/-- The finite support of `S.toWord` coerces to `S.vars`. -/
theorem coe_occVars_toWord (S : Standard G X) : (GX.occVars S.toWord : Set X) = S.vars := by
  ext x; simp [mem_vars_iff_occurrences_toWord_ne_zero]

@[simp] theorem occurrences_toWord_eq_zero_iff {S : Standard G X} {x : X} :
    GX.occurrences x S.toWord = 0 ↔ x ∉ S.vars := by
  rw [← not_iff_not, not_not, mem_vars_iff_occurrences_toWord_ne_zero]

@[simp] theorem occurrences_toWord_eq_two_iff {S : Standard G X} {x : X} :
    GX.occurrences x S.toWord = 2 ↔ x ∈ S.vars :=
  ⟨fun h => mem_vars_iff_occurrences_toWord_ne_zero.2 (by omega), occurrences_toWord_of_mem_vars⟩

/-- A variable is avoided by the left side of a standard quadratic equation if and only if it is
outside `S.vars`. -/
@[simp]
theorem toWord_mem_avoiding_iff [DecidableEq X] {S : Standard G X} {x : X} :
    S.toWord ∈ GX.avoiding x ↔ x ∉ S.vars := by
  rw [GX.mem_avoiding_iff_occurrences_eq_zero, ← not_iff_not, not_not,
    S.mem_vars_iff_occurrences_toWord_ne_zero]

/-- Every standard quadratic equation involves at least one variable. -/
theorem vars_nonempty (S : Standard G X) : S.vars.Nonempty := by
  cases S with
  | orientable n hn x _ _ => rw [vars_orientable]; exact ⟨_, ⟨.inl ⟨0, hn⟩, rfl⟩⟩
  | orientableCoeff n m hnm x _ z _ _ _ _ _ =>
    rw [vars_orientableCoeff]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨_, ⟨.inr ⟨0, by omega⟩, rfl⟩⟩
    · exact ⟨_, ⟨.inl (.inl ⟨0, hn⟩), rfl⟩⟩
  | nonorientable n hn x _ => rw [vars_nonorientable]; exact ⟨_, ⟨⟨0, hn⟩, rfl⟩⟩
  | nonorientableCoeff n _ hn x _ _ _ _ _ _ =>
    rw [vars_nonorientableCoeff]; exact ⟨_, ⟨.inl ⟨0, hn⟩, rfl⟩⟩

end IsQuadratic

/-! ### Degenerate, commutative and general-position solutions -/

section Solutions

variable (S : Standard G X) (ι : G →* H) (v : X → H)

/-- A point `v` is degenerate for a standard quadratic equation `r₁ ⋯ r_k d = 1` when some atom
`rᵢ` vanishes at `v`. -/
def IsDegenerate : Prop :=
  ∃ r ∈ S.atoms, eval ι v r = 1

/-- A point `v` is commutative for a standard quadratic equation `r₁ ⋯ r_k d = 1` when the values
of consecutive atoms `rᵢ` and `rᵢ₊₁` at `v` commute. -/
def IsCommutative : Prop :=
  (S.atoms.map (eval ι v)).IsChain Commute

/-- A point `v` is in general position for a standard quadratic equation `r₁ ⋯ r_k d = 1` when
the values of no two consecutive atoms `rᵢ` and `rᵢ₊₁` at `v` commute. -/
def IsGeneralPosition : Prop :=
  (S.atoms.map (eval ι v)).IsChain fun a b => ¬Commute a b

theorem isDegenerate_iff : S.IsDegenerate ι v ↔ ∃ r ∈ S.atoms, eval ι v r = 1 := Iff.rfl

theorem isCommutative_iff : S.IsCommutative ι v ↔ (S.atoms.map (eval ι v)).IsChain Commute :=
  Iff.rfl

theorem isGeneralPosition_iff :
    S.IsGeneralPosition ι v ↔ (S.atoms.map (eval ι v)).IsChain fun a b => ¬Commute a b :=
  Iff.rfl

variable {S ι v}

/-- A standard quadratic equation of genus `0` is `∏ⱼ zⱼ⁻¹ cⱼ zⱼ d = 1`, so a point is degenerate
for it exactly when some coefficient `cⱼ` is mapped to `1`. -/
theorem isDegenerate_iff_of_genus_eq_zero (hg : S.genus = 0) :
    S.IsDegenerate ι v ↔ ∃ c ∈ S.coeffs.tail, ι c = 1 := by
  cases S <;> simp only [genus_orientable, genus_orientableCoeff, genus_nonorientable,
    genus_nonorientableCoeff] at hg <;> subst hg <;>
    simp_all [isDegenerate_iff, List.mem_ofFn, mul_assoc, inv_mul_eq_one]

/-- When the coefficients embed into `H`, a standard quadratic equation of genus `0` has no
degenerate point, since its atoms are conjugates of the nontrivial coefficients `cⱼ`. -/
theorem not_isDegenerate_of_genus_eq_zero_of_injective (hg : S.genus = 0)
    (hι : Function.Injective ι) : ¬S.IsDegenerate ι v := by
  rw [isDegenerate_iff_of_genus_eq_zero hg]
  rintro ⟨c, hc, h⟩
  exact ne_one_of_mem_coeffs (List.mem_of_mem_tail hc) ((map_eq_one_iff ι hι).1 h)

/-- With at least two atoms, a point in general position is not commutative. -/
theorem IsGeneralPosition.not_isCommutative (h : S.IsGeneralPosition ι v)
    (hS : 2 ≤ S.atomicRank) : ¬S.IsCommutative ι v := by
  rw [isGeneralPosition_iff] at h; rw [isCommutative_iff]; rw [atomicRank_def] at hS
  obtain ⟨a, b, l, hl⟩ : ∃ a b l, S.atoms.map (eval ι v) = a :: b :: l := by
    match h' : S.atoms.map (eval ι v) with
    | [] => simp_all
    | [_] => rw [← List.length_map (eval ι v), h'] at hS; simp at hS
    | a :: b :: l => exact ⟨a, b, l, rfl⟩
  rw [hl, List.isChain_cons_cons] at h ⊢
  exact fun h' => h.1 h'.1

/-- Composing a point with an injective `G`-homomorphism neither creates nor destroys
commutativity. -/
theorem isCommutative_comp_iff {K : Type*} [Group K] {ιK : G →* K} (f : GHom ι ιK)
    (hf : Function.Injective f) : S.IsCommutative ιK (f ∘ v) ↔ S.IsCommutative ι v := by
  have h : S.atoms.map (eval ιK (f ∘ v)) = (S.atoms.map (eval ι v)).map f := by
    simp [Function.comp_def]
  rw [isCommutative_iff, isCommutative_iff, h, List.isChain_map]
  exact ⟨(·.imp fun _ _ => Commute.of_map hf), (·.imp fun _ _ h => h.map f)⟩

end Solutions

/-! ### Solutions of the commutator equations -/

section Commutators

variable {n : ℕ} {x y : Fin n → X}

/-- A point at which the two variables of each commutator take commuting values is a solution of
`∏ᵢ₌₁ⁿ [xᵢ, yᵢ] = 1`. -/
theorem mem_V_orientable_of_commute (ι : G →* H) (hn : 0 < n) (inj : (Sum.elim x y).Injective)
    {v : X → H} (hv : ∀ i, Commute (v (x i)) (v (y i))) :
    v ∈ V ι {(orientable n hn x y inj).toWord} := by
  rw [mem_V_toWord_iff, constant_orientable, map_one, mul_one]
  exact List.prod_eq_one <| by
    simp [map_commutatorElement, commutatorElement_eq_one_iff_commute, hv]

/-- The trivial point is a solution of `∏ᵢ₌₁ⁿ [xᵢ, yᵢ] = 1`. -/
theorem one_mem_V_orientable (ι : G →* H) (hn : 0 < n) (inj : (Sum.elim x y).Injective) :
    1 ∈ V ι {(orientable n hn x y inj).toWord} :=
  mem_V_orientable_of_commute ι hn inj fun _ => .one_left 1

/-- The trivial solution of `∏ᵢ₌₁ⁿ [xᵢ, yᵢ] = 1` is degenerate. -/
theorem isDegenerate_one_orientable (ι : G →* H) (hn : 0 < n) (inj : (Sum.elim x y).Injective) :
    (orientable n hn x y inj).IsDegenerate ι 1 :=
  ⟨_, (atoms_orientable (G := G) hn inj).symm ▸ List.mem_ofFn.2 ⟨⟨0, hn⟩, rfl⟩,
    by simp [map_commutatorElement]⟩

/-- The trivial solution of `∏ᵢ₌₁ⁿ [xᵢ, yᵢ] = 1` is commutative. -/
theorem isCommutative_one_orientable (ι : G →* H) (hn : 0 < n) (inj : (Sum.elim x y).Injective) :
    (orientable n hn x y inj).IsCommutative ι 1 := by
  have h : ∀ r ∈ (orientable (G := G) n hn x y inj).atoms, eval ι 1 r = 1 := by
    simp [List.mem_ofFn, map_commutatorElement]
  rw [isCommutative_iff, List.map_congr_left h, List.map_const']
  exact List.isChain_replicate_of_rel _ (Commute.refl 1)

/-- Every solution of the genus-two equation `[x₁, y₁][x₂, y₂] = 1` is commutative: the values of
its two atoms are inverse to each other. -/
theorem isCommutative_of_mem_V_genusTwo {ι : G →* H} {v : X → H} {x y : Fin 2 → X}
    (inj : (Sum.elim x y).Injective) (hv : v ∈ V ι {(orientable 2 two_pos x y inj).toWord}) :
    (orientable 2 two_pos x y inj).IsCommutative ι v := by
  rw [mem_V_toWord_iff, constant_orientable, map_one, mul_one] at hv
  rw [isCommutative_iff]
  simp only [atoms_orientable, List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, List.isChain_cons_cons, List.isChain_singleton,
    and_true] at hv ⊢
  rw [mul_eq_one_iff_eq_inv.1 hv]
  exact (Commute.refl _).inv_left

/-- The genus-two equation `[x₁, y₁][x₂, y₂] = 1` has no solution in general position. -/
theorem not_isGeneralPosition_of_mem_V_genusTwo {ι : G →* H} {v : X → H} {x y : Fin 2 → X}
    (inj : (Sum.elim x y).Injective) (hv : v ∈ V ι {(orientable 2 two_pos x y inj).toWord}) :
    ¬(orientable 2 two_pos x y inj).IsGeneralPosition ι v := fun h =>
  h.not_isCommutative (by simp) (isCommutative_of_mem_V_genusTwo inj hv)

end Commutators

/-! ### The value at the trivial point -/

/- The priority `high` makes this formula fire before the evaluation formulas at a general point,
`eval_toWord_orientable` and its analogues in `Quadratic.Surface`, which would rewrite the value at
the trivial point into a surface word. -/

/-- The value of a standard quadratic equation `r₁ ⋯ r_k d = 1` at the trivial point is the product
`(∏ⱼ₌₁ᵐ cⱼ) d` of its coefficients, mapped to `H`, where `c₁, …, c_m` are the coefficients of its
conjugate atoms `zⱼ⁻¹ cⱼ zⱼ`. It is `1` for the types (1) and (3), which have no coefficients. -/
@[simp high]
theorem eval_one_toWord (ι : G →* H) (S : Standard G X) :
    eval ι 1 S.toWord = ι (S.coeffs.tail.prod * S.constant) := by
  cases S <;>
    simp [toWord_def, map_list_prod, List.map_ofFn, Function.comp_def, map_commutatorElement]

end Standard

/-! ### The equation `[x, y] = [a, b]` -/

section OneCommutator

variable (a b : G)

/-- The equation `[x, y] = [a, b]` over `G`, where `[x, y] = x⁻¹ y⁻¹ x y`: the element
`[x, y] [a, b]⁻¹` of `G[x, y]`. -/
def oneCommutatorEquation : GX G (Fin 2) :=
  ⁅(inr (FreeGroup.of 0) : GX G (Fin 2))⁻¹, (inr (FreeGroup.of 1))⁻¹⁆ * inl ⁅a⁻¹, b⁻¹⁆⁻¹

/-- The left side `[x, y] [a, b]⁻¹` of the equation `[x, y] = [a, b]`. -/
theorem oneCommutatorEquation_def : oneCommutatorEquation a b =
    ⁅(inr (FreeGroup.of 0) : GX G (Fin 2))⁻¹, (inr (FreeGroup.of 1))⁻¹⁆ * inl ⁅a⁻¹, b⁻¹⁆⁻¹ := (rfl)

/-- The equation `[x, y] = [a, b]` is a standard orientable quadratic equation of genus one: it
has a nontrivial constant if `a` and `b` do not commute, and is `[x, y] = 1` otherwise. -/
theorem isStandard_oneCommutatorEquation :
    ∃ S : Standard G (Fin 2),
      S.toWord = oneCommutatorEquation a b ∧ S.IsOrientable ∧ S.genus = 1 := by
  by_cases hd : ⁅a⁻¹, b⁻¹⁆⁻¹ = 1
  · exact ⟨.orientable 1 one_pos ![0] ![1] (by decide),
      by simp [Standard.toWord_def, oneCommutatorEquation_def, hd], by simp, by simp⟩
  · exact ⟨.orientableCoeff 1 0 one_pos ![0] ![1] Fin.elim0 (by decide) Fin.elim0
      (fun j => j.elim0) _ hd, by simp [Standard.toWord_def, oneCommutatorEquation_def],
      by simp, by simp⟩

variable {a b} {ι : G →* H} {v : Fin 2 → H}

/-- The value of the left side of `[x, y] = [a, b]` at a pair. -/
@[simp]
theorem eval_oneCommutatorEquation : eval ι v (oneCommutatorEquation a b) =
    ⁅(v 0)⁻¹, (v 1)⁻¹⁆ * ⁅(ι a)⁻¹, (ι b)⁻¹⁆⁻¹ := by
  simp [oneCommutatorEquation_def, map_commutatorElement]

/-- The solutions of `[x, y] = [a, b]` are the pairs with the commutator of `(a, b)`. -/
theorem mem_V_oneCommutatorEquation :
    v ∈ V ι {oneCommutatorEquation a b} ↔ ⁅(v 0)⁻¹, (v 1)⁻¹⁆ = ⁅(ι a)⁻¹, (ι b)⁻¹⁆ := by
  simp [mul_eq_one_iff_eq_inv]

end OneCommutator

/-! ### Examples -/

section Examples

/-- The commutator `x⁻¹ y⁻¹ x y` is a standard quadratic word. -/
theorem exists_standard_toWord_eq_commutator : ∃ S : Standard G (Fin 2),
    S.toWord = (inr (.of 0))⁻¹ * (inr (.of 1))⁻¹ * inr (.of 0) * inr (.of 1) :=
  ⟨.orientable 1 one_pos ![0] ![1] ((Function.injective_of_subsingleton _).sumElim
      (Function.injective_of_subsingleton _) (by simp)), by
    simp [Standard.toWord_def, commutatorElement_def, mul_assoc]⟩

/-- `x₁² x₂² x₃² = 1` is a standard quadratic equation of type (3), non-orientable of genus `3`,
with atomic rank `3` and Euler characteristic `-1`. -/
theorem isStandard_x2y2z2 : ∃ S : Standard G (Fin 3),
    S.toWord = inr (.of 0) ^ 2 * inr (.of 1) ^ 2 * inr (.of 2) ^ 2 ∧ ¬S.IsOrientable ∧
      S.genus = 3 ∧ S.atomicRank = 3 ∧ S.eulerChar = -1 :=
  ⟨.nonorientable 3 (by omega) id Function.injective_id, by
    simp [Standard.toWord_def, List.ofFn_succ, mul_assoc], by simp, by simp, by simp,
    by simp⟩

/-- `x₁² x₂² x₃²` is strictly quadratic. -/
theorem isStrictlyQuadratic_x2y2z2 :
    IsStrictlyQuadratic {(inr (.of 0) ^ 2 * inr (.of 1) ^ 2 * inr (.of 2) ^ 2 : GX G (Fin 3))} := by
  obtain ⟨S, hS, -⟩ := isStandard_x2y2z2 (G := G)
  exact hS ▸ S.isStrictlyQuadratic

/-- `x y x⁻¹ y⁻¹ x` is not quadratic: the variable `x` occurs three times. -/
theorem not_isQuadratic_cubic :
    ¬IsQuadratic {(inr (.of 0) * inr (.of 1) * (inr (.of 0))⁻¹ * (inr (.of 1))⁻¹ * inr (.of 0) :
      GX G (Fin 2))} := by
  rw [isQuadratic_singleton]
  intro h
  have := (GX.countP_toWord_snd_le_occurrences 0 _).trans (h 0)
  simp only [_root_.map_mul, _root_.map_inv, snd_apply_inr] at this
  revert this
  decide

/-- In `F(a, b)`, the point `x₁ = a`, `y₁ = b`, `x₂ = b`, `y₂ = a²`, `x₃ = a`, `y₃ = a⁻¹ b a` is a
solution of the genus-three equation `[x₁, y₁][x₂, y₂][x₃, y₃] = 1` in general position. -/
theorem isGeneralPosition_genusThree :
    let S : Standard (FreeGroup (Fin 2)) (Fin 3 ⊕ Fin 3) :=
      .orientable 3 (by omega) Sum.inl Sum.inr (by simp [Function.injective_id])
    let v : Fin 3 ⊕ Fin 3 → FreeGroup (Fin 2) := Sum.elim ![.of 0, .of 1, .of 0]
      ![.of 1, .of 0 ^ 2, (.of 0)⁻¹ * .of 1 * .of 0]
    v ∈ V (.id _) {S.toWord} ∧ S.IsGeneralPosition (.id _) v := by
  intro S v
  refine ⟨?_, ?_⟩
  · simp only [S, v, Standard.mem_V_toWord_iff, Standard.atoms_orientable,
      Standard.constant_orientable, List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, _root_.map_one, map_commutatorElement, _root_.map_inv,
      eval_inr, FreeGroup.lift_apply_of, mul_one]
    decide
  · simp only [S, v, Standard.isGeneralPosition_iff, Standard.atoms_orientable, List.ofFn_succ,
      List.ofFn_zero, List.map_cons, List.map_nil, List.isChain_cons_cons, List.isChain_singleton,
      map_commutatorElement, _root_.map_inv, eval_inr, FreeGroup.lift_apply_of, Commute,
      SemiconjBy, and_true]
    decide

/-- Over `F(a, b)`, `z₁⁻¹ a z₁ · z₂⁻¹ b z₂ · z₃⁻¹ a z₃ · (a b a)⁻¹ = 1` is a standard quadratic
equation of type (2), orientable of genus `0` with atomic rank `3` and Euler characteristic `-2`.
The trivial point is a solution in general position: the adjacent atom values are `a`, `b`,
`a`. -/
theorem isGeneralPosition_conjugates :
    let S : Standard (FreeGroup (Fin 2)) (Fin 3) :=
      .orientableCoeff 0 3 (by omega) Fin.elim0 Fin.elim0 id (by decide) ![.of 0, .of 1, .of 0]
        (by decide) (.of 0 * .of 1 * .of 0)⁻¹ (by decide)
    S.IsOrientable ∧ S.genus = 0 ∧ S.atomicRank = 3 ∧ S.eulerChar = -2 ∧
      1 ∈ V (.id _) {S.toWord} ∧ S.IsGeneralPosition (.id _) 1 := by
  intro S
  refine ⟨by simp [S], by simp [S], by simp [S], by simp [S], ?_, ?_⟩
  · simp only [S, Standard.mem_V_toWord_iff, Standard.atoms_orientableCoeff,
      Standard.constant_orientableCoeff, List.ofFn_succ, List.ofFn_zero, List.nil_append,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, _root_.map_mul, _root_.map_inv,
      eval_inr, eval_inl, mul_one]
    decide
  · simp only [S, Standard.isGeneralPosition_iff, Standard.atoms_orientableCoeff, List.ofFn_succ,
      List.ofFn_zero, List.nil_append, List.map_cons, List.map_nil, List.isChain_cons_cons,
      List.isChain_singleton, _root_.map_mul, _root_.map_inv, eval_inr, eval_inl, Commute,
      SemiconjBy, and_true]
    decide

end Examples

end TauCeti.GroupAlgGeom.Quadratic
