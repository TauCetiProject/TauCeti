/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet
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
import Mathlib.Order.Lattice.Nat

/-!
# Quadratic words and standard quadratic equations

An equation over a group `G` in the variables `X` is an element of `G[X] = G ∗ F(X)`. It is
quadratic when every variable occurs in it at most twice, as `x` or as `x⁻¹`. Quadratic equations
are the equations whose solution theory is governed by surfaces: the four standard quadratic
words below are the relators of orientable and non-orientable surfaces with boundary components
labelled by coefficients, and [IFT] uses automorphisms of `G[X]` fixing `G` to bring strictly
quadratic equations into these standard forms. This file neither states nor proves that
reduction, whose precise form has to account for cyclic reduction and for words conjugate to
coefficients: for instance the coefficients themselves and their conjugates `x c x⁻¹` are
strictly quadratic but are not standard.

This file defines the number of occurrences of a variable in an element of `G[X]`, quadratic and
strictly quadratic finite systems, the four types of standard quadratic equations together with
their atoms, variables, coefficients, atomic rank, genus, Euler characteristic and the invariant
`κ(S)` of [IFT], Definition 6, and degenerate, commutative and general-position solutions. It also
records the standard equation `[x, y] = [a, b]` of genus one and its solutions.

The number of occurrences `occurrences x w` of `x` in `w` is defined as the least number of
letters `x^{±1}` in an expression of `w` as a product of coefficients and letters `y^{±1}`. By
the normal form theorem for free products this is the number of occurrences of `x^{±1}` in the
reduced form of `w`; the definition as a minimum needs no choice of normal form, and it is
characterized as the largest subadditive function bounded by `1` on `x^{±1}` and vanishing on
coefficients and on the other variables (`le_occurrences`). Lower bounds come from reduced words
in the free group `F(X)` obtained by deleting the coefficients
(`countP_toWord_snd_le_occurrences`).

Following [IFT], the standard quadratic equations over `G` are, with `[x, y] = x⁻¹ y⁻¹ x y`
(Mathlib's `⁅x⁻¹, y⁻¹⁆`) and `z⁻¹ c z` the conjugate of a coefficient,
1. `∏ᵢ₌₁ⁿ [xᵢ, yᵢ] = 1` with `n > 0`;
2. `∏ᵢ₌₁ⁿ [xᵢ, yᵢ] ∏ⱼ₌₁ᵐ zⱼ⁻¹ cⱼ zⱼ d = 1` with `n + m ≥ 1`;
3. `∏ᵢ₌₁ⁿ xᵢ² = 1` with `n > 0`;
4. `∏ᵢ₌₁ⁿ xᵢ² ∏ⱼ₌₁ᵐ zⱼ⁻¹ cⱼ zⱼ d = 1` with `n > 0`,

where the variables are pairwise distinct and the coefficients `cⱼ` and `d` are nontrivial.
Equations without commutators or squares are of type (2), so the non-orientable types have
positive genus. The factors `[xᵢ, yᵢ]`, `xᵢ²` and `zⱼ⁻¹ cⱼ zⱼ` are the atoms.

## Main definitions

* `TauCeti.GroupAlgGeom.Quadratic.occurrences x w`: the number of occurrences of `x` in `w`.
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

* `TauCeti.GroupAlgGeom.Quadratic.le_occurrences`: the extremal characterization of
  `occurrences`.
* `TauCeti.GroupAlgGeom.Quadratic.occurrences_map_le`,
  `TauCeti.GroupAlgGeom.Quadratic.occurrences_map_eq_zero`: bounds on the occurrence counts in the
  images under a homomorphism `G[X] → H[Y]`, from those in the images of the generators.
* `TauCeti.GroupAlgGeom.Quadratic.isQuadratic_map_iff`,
  `TauCeti.GroupAlgGeom.Quadratic.isStrictlyQuadratic_map_iff`: an injective map transporting
  occurrence counts along a bijection of the variables preserves (strictly) quadratic systems.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.isQuadratic`: standard equations are quadratic.
* `TauCeti.GroupAlgGeom.Quadratic.isStandard_oneCommutatorEquation`: `[x, y] = [a, b]` is a
  standard orientable quadratic equation of genus one.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.kappa_eq_ncard_vars`,
  `TauCeti.GroupAlgGeom.Quadratic.Standard.kappa_eq_ncard_vars_add_one`: `κ(S)` is the number of
  variables of `S`, plus one when the coefficient `d` occurs; it equals `2 - χ(S)`
  (`TauCeti.GroupAlgGeom.Quadratic.Standard.eulerChar_eq_two_sub_kappa`).
* `TauCeti.GroupAlgGeom.Quadratic.Standard.isCommutative_of_mem_V_genusTwo`: every solution of
  `[x₁, y₁][x₂, y₂] = 1` is commutative, so this equation has no solution in general position.
* `TauCeti.GroupAlgGeom.Quadratic.isGeneralPosition_genusThree`: `[x₁, y₁][x₂, y₂][x₃, y₃] = 1`
  has a solution in general position in `F(a, b)`.
* `TauCeti.GroupAlgGeom.Quadratic.not_isQuadratic_cubic`: `x y x⁻¹ y⁻¹ x` is not quadratic.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §2.7, Definitions 2–6.
* [VAR-I] O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I:
  Irreducibility of quadratic equations and Nullstellensatz*, J. Algebra 200 (1998), §1.
-/

public section

open Monoid.Coprod
open scoped commutatorElement

namespace TauCeti.GroupAlgGeom.Quadratic

variable {G H X : Type*} [Group G] [Group H]

/-! ### Occurrences of a variable -/

section Occurrences

/-- The element of `G[X]` spelled by a letter: a coefficient, or a variable `y` or its inverse. -/
private def letter : G ⊕ X × Bool → GX G X
  | .inl g => inl g
  | .inr (y, true) => inr (FreeGroup.of y)
  | .inr (y, false) => (inr (FreeGroup.of y))⁻¹

open Classical in
/-- The number of letters `x^{±1}` in a spelling. -/
private noncomputable def spellCount (x : X) (l : List (G ⊕ X × Bool)) : ℕ :=
  l.countP fun a => a.elim (fun _ => false) (fun p => p.1 = x)

omit [Group G] in
private theorem spellCount_nil (x : X) : spellCount x ([] : List (G ⊕ X × Bool)) = 0 := by
  simp [spellCount]

omit [Group G] in
private theorem spellCount_append (x : X) (l₁ l₂ : List (G ⊕ X × Bool)) :
    spellCount x (l₁ ++ l₂) = spellCount x l₁ + spellCount x l₂ := by
  simp [spellCount]

omit [Group G] in
private theorem spellCount_cons_inl (x : X) (g : G) (l : List (G ⊕ X × Bool)) :
    spellCount x (.inl g :: l) = spellCount x l := by
  simp [spellCount]

omit [Group G] in
private theorem spellCount_cons_inr_self (x : X) (b : Bool) (l : List (G ⊕ X × Bool)) :
    spellCount x (.inr (x, b) :: l) = spellCount x l + 1 := by
  simp [spellCount]

omit [Group G] in
private theorem spellCount_cons_inr_of_ne {x y : X} (h : y ≠ x) (b : Bool)
    (l : List (G ⊕ X × Bool)) : spellCount x (.inr (y, b) :: l) = spellCount x l := by
  simp [spellCount, h]

private theorem exists_spelling (w : GX G X) :
    ∃ l : List (G ⊕ X × Bool), (l.map letter).prod = w := by
  induction w using Monoid.Coprod.induction_on with
  | inl g => exact ⟨[.inl g], by simp [letter]⟩
  | inr f =>
    induction f using FreeGroup.induction_on with
    | one => exact ⟨[], by simp⟩
    | of y => exact ⟨[.inr (y, true)], by simp [letter]⟩
    | inv_of y _ => exact ⟨[.inr (y, false)], by simp [letter]⟩
    | mul f₁ f₂ h₁ h₂ =>
      obtain ⟨l₁, hl₁⟩ := h₁
      obtain ⟨l₂, hl₂⟩ := h₂
      exact ⟨l₁ ++ l₂, by simp [hl₁, hl₂]⟩
  | mul u v hu hv =>
    obtain ⟨l₁, hl₁⟩ := hu
    obtain ⟨l₂, hl₂⟩ := hv
    exact ⟨l₁ ++ l₂, by simp [hl₁, hl₂]⟩

/-- The number of occurrences of the variable `x` in `w ∈ G[X]`: the least number of letters
`x^{±1}` in an expression of `w` as a product of coefficients and letters `y^{±1}`. By the normal
form theorem for free products this is the number of letters `x^{±1}` in the reduced form of
`w`. -/
noncomputable def occurrences (x : X) (w : GX G X) : ℕ :=
  sInf {n | ∃ l : List (G ⊕ X × Bool), (l.map letter).prod = w ∧ spellCount x l = n}

private theorem occurrences_le_spellCount (x : X) {w : GX G X} {l : List (G ⊕ X × Bool)}
    (h : (l.map letter).prod = w) : occurrences x w ≤ spellCount x l :=
  Nat.sInf_le ⟨l, h, rfl⟩

private theorem exists_spellCount_eq_occurrences (x : X) (w : GX G X) :
    ∃ l : List (G ⊕ X × Bool), (l.map letter).prod = w ∧ spellCount x l = occurrences x w := by
  obtain ⟨l, hl⟩ := exists_spelling w
  exact Nat.sInf_mem (s := {n | ∃ l : List (G ⊕ X × Bool), (l.map letter).prod = w ∧
    spellCount x l = n}) ⟨_, l, hl, rfl⟩

/-- `occurrences x` is the largest subadditive function on `G[X]` vanishing on coefficients and
on the letters `y^{±1}` with `y ≠ x`, and bounded by `1` on the letters `x^{±1}`. -/
theorem le_occurrences (x : X) (f : GX G X → ℕ) (hmul : ∀ u v, f (u * v) ≤ f u + f v)
    (hcoeff : ∀ g, f (inl g) = 0) (hx : f (inr (FreeGroup.of x)) ≤ 1)
    (hx' : f (inr (FreeGroup.of x))⁻¹ ≤ 1)
    (hy : ∀ y, y ≠ x → f (inr (FreeGroup.of y)) = 0 ∧ f (inr (FreeGroup.of y))⁻¹ = 0)
    (w : GX G X) :
    f w ≤ occurrences x w := by
  obtain ⟨l, rfl, hl⟩ := exists_spellCount_eq_occurrences x w
  rw [← hl]
  clear hl
  induction l with
  | nil => simpa [spellCount_nil] using (hcoeff 1).le
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons]
    refine (hmul _ _).trans ?_
    rcases a with g | ⟨y, b⟩
    · simpa [letter, hcoeff, spellCount_cons_inl] using ih
    · by_cases h : y = x
      · subst h
        rw [spellCount_cons_inr_self, add_comm (spellCount y l)]
        refine add_le_add ?_ ih
        cases b <;> simpa [letter]
      · rw [spellCount_cons_inr_of_ne h]
        cases b <;> simpa [letter, hy y h] using ih

theorem occurrences_mul_le (x : X) (u v : GX G X) :
    occurrences x (u * v) ≤ occurrences x u + occurrences x v := by
  obtain ⟨l₁, hl₁, h₁⟩ := exists_spellCount_eq_occurrences x u
  obtain ⟨l₂, hl₂, h₂⟩ := exists_spellCount_eq_occurrences x v
  calc occurrences x (u * v) ≤ spellCount x (l₁ ++ l₂) :=
        occurrences_le_spellCount x (by simp [hl₁, hl₂])
    _ = _ := by rw [spellCount_append, h₁, h₂]

@[simp]
theorem occurrences_inl (x : X) (g : G) : occurrences x (inl g : GX G X) = 0 :=
  Nat.eq_zero_of_le_zero <| (occurrences_le_spellCount x (l := [.inl g]) (by simp [letter])).trans
    (by simp [spellCount])

@[simp]
theorem occurrences_one (x : X) : occurrences x (1 : GX G X) = 0 := by
  simpa using occurrences_inl (G := G) x 1

private theorem occurrences_letter_self_le (x : X) (b : Bool) :
    occurrences x (letter (G := G) (.inr (x, b))) ≤ 1 :=
  (occurrences_le_spellCount x (l := [.inr (x, b)]) (by simp)).trans
    (by simp [spellCount_cons_inr_self, spellCount_nil])

private theorem occurrences_letter_of_ne {x y : X} (h : y ≠ x) (b : Bool) :
    occurrences x (letter (G := G) (.inr (y, b))) = 0 :=
  Nat.eq_zero_of_le_zero <| (occurrences_le_spellCount x (l := [.inr (y, b)]) (by simp)).trans
    (by simp [spellCount_cons_inr_of_ne h, spellCount_nil])

theorem occurrences_inv_le (x : X) (w : GX G X) : occurrences x w⁻¹ ≤ occurrences x w := by
  refine le_occurrences x (fun u => occurrences x u⁻¹) (fun u v => ?_) (fun g => ?_) ?_ ?_
    (fun y hy => ⟨?_, ?_⟩) w
  · simpa using occurrences_mul_le x v⁻¹ u⁻¹ |>.trans_eq (add_comm _ _)
  · simp [← map_inv]
  · exact occurrences_letter_self_le (G := G) x false
  · simpa [letter] using occurrences_letter_self_le (G := G) x true
  · exact occurrences_letter_of_ne (G := G) hy false
  · simpa [letter] using occurrences_letter_of_ne (G := G) hy true

@[simp]
theorem occurrences_inv (x : X) (w : GX G X) : occurrences x w⁻¹ = occurrences x w :=
  (occurrences_inv_le x w).antisymm (by simpa using occurrences_inv_le x w⁻¹)

theorem occurrences_pow_le (x : X) (w : GX G X) (n : ℕ) :
    occurrences x (w ^ n) ≤ n * occurrences x w := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, add_one_mul]
    exact (occurrences_mul_le x _ _).trans (by omega)

theorem occurrences_list_prod_le (x : X) (l : List (GX G X)) :
    occurrences x l.prod ≤ (l.map (occurrences x)).sum := by
  induction l with
  | nil => simp
  | cons w l ih =>
    rw [List.prod_cons, List.map_cons, List.sum_cons]
    exact (occurrences_mul_le x _ _).trans (by omega)

theorem occurrences_commutatorElement_le (x : X) (u v : GX G X) :
    occurrences x ⁅u, v⁆ ≤ 2 * (occurrences x u + occurrences x v) := by
  rw [commutatorElement_def]
  have h₁ := occurrences_mul_le x (u * v * u⁻¹) v⁻¹
  have h₂ := occurrences_mul_le x (u * v) u⁻¹
  have h₃ := occurrences_mul_le x u v
  simp only [occurrences_inv] at h₁ h₂
  omega

theorem occurrences_conj_le (x : X) (u w : GX G X) :
    occurrences x (u⁻¹ * w * u) ≤ 2 * occurrences x u + occurrences x w := by
  have h₁ := occurrences_mul_le x (u⁻¹ * w) u
  have h₂ := occurrences_mul_le x u⁻¹ w
  simp only [occurrences_inv] at h₂
  omega

/-- The number of letters `x^{±1}` in the reduced word of the image of `w` in `F(X)`, where the
coefficients are deleted, is a lower bound for the number of occurrences of `x` in `w`. -/
theorem countP_toWord_snd_le_occurrences [DecidableEq X] (x : X) (w : GX G X) :
    ((snd w).toWord.countP fun p => p.1 = x) ≤ occurrences x w := by
  refine le_occurrences x (fun u => (snd u).toWord.countP fun p => p.1 = x) (fun u v => ?_)
    (fun _ => by simp) (by simp [FreeGroup.toWord_of]) ?_ (fun y hy => ⟨?_, ?_⟩) w
  · rw [map_mul, ← List.countP_append]
    exact (FreeGroup.toWord_mul_sublist _ _).countP_le
  · simp [FreeGroup.toWord_inv, FreeGroup.toWord_of, FreeGroup.invRev]
  · simp [FreeGroup.toWord_of, hy]
  · simp [FreeGroup.toWord_inv, FreeGroup.toWord_of, FreeGroup.invRev, hy]

@[simp]
theorem occurrences_inr_of_self (x : X) : occurrences x (inr (FreeGroup.of x) : GX G X) = 1 := by
  classical
  refine le_antisymm (occurrences_letter_self_le (G := G) x true) ?_
  simpa [FreeGroup.toWord_of] using
    countP_toWord_snd_le_occurrences (G := G) x (inr (FreeGroup.of x))

@[simp]
theorem occurrences_inr_of_of_ne {x y : X} (h : y ≠ x) :
    occurrences x (inr (FreeGroup.of y) : GX G X) = 0 :=
  occurrences_letter_of_ne (G := G) h true

theorem occurrences_inr_of [DecidableEq X] (x y : X) :
    occurrences x (inr (FreeGroup.of y) : GX G X) = if y = x then 1 else 0 := by
  split_ifs with h
  · subst h; exact occurrences_inr_of_self y
  · exact occurrences_inr_of_of_ne h

/-- A homomorphism `φ : G[X] → H[Y]` does not increase occurrence counts from `x` to `y` when
`y` does not occur in the images of the coefficients and of the variables other than `x`, and
occurs at most once in the image of `x`. -/
theorem occurrences_map_le {Y F : Type*} [FunLike F (GX G X) (GX H Y)]
    [MonoidHomClass F (GX G X) (GX H Y)] (φ : F) (x : X) (y : Y)
    (hcoeff : ∀ g, occurrences y (φ (inl g)) = 0)
    (hx : occurrences y (φ (inr (FreeGroup.of x))) ≤ 1)
    (hne : ∀ z, z ≠ x → occurrences y (φ (inr (FreeGroup.of z))) = 0) (w : GX G X) :
    occurrences y (φ w) ≤ occurrences x w :=
  le_occurrences x (fun u => occurrences y (φ u))
    (fun u v => by simpa using occurrences_mul_le y (φ u) (φ v)) hcoeff hx (by simpa using hx)
    (fun z hz => ⟨hne z hz, by simpa using hne z hz⟩) w

/-- A variable `y` occurs in no image under a homomorphism `φ : G[X] → H[Y]` when it occurs
neither in the images of the coefficients nor in the images of the variables. -/
theorem occurrences_map_eq_zero {Y F : Type*} [FunLike F (GX G X) (GX H Y)]
    [MonoidHomClass F (GX G X) (GX H Y)] (φ : F) (y : Y)
    (hcoeff : ∀ g, occurrences y (φ (inl g)) = 0)
    (hvar : ∀ x, occurrences y (φ (inr (FreeGroup.of x))) = 0) (w : GX G X) :
    occurrences y (φ w) = 0 := by
  have hmul : ∀ u v, occurrences y (φ u) = 0 → occurrences y (φ v) = 0 →
      occurrences y (φ (u * v)) = 0 := fun u v hu hv =>
    Nat.eq_zero_of_le_zero <| by simpa [hu, hv] using occurrences_mul_le y (φ u) (φ v)
  induction w using Monoid.Coprod.induction_on with
  | inl g => exact hcoeff g
  | inr f =>
    induction f using FreeGroup.induction_on with
    | one => simp
    | of x => exact hvar x
    | inv_of x ih => simpa using ih
    | mul f₁ f₂ h₁ h₂ => simpa using hmul _ _ h₁ h₂
  | mul u v hu hv => exact hmul u v hu hv

end Occurrences

/-! ### Quadratic systems -/

section IsQuadratic

/-- A finite system `S ⊆ G[X]` is quadratic when every variable occurs in `S`, counted over all
its elements, at most twice. -/
def IsQuadratic (S : Finset (GX G X)) : Prop :=
  ∀ x, ∑ w ∈ S, occurrences x w ≤ 2

/-- A finite system `S ⊆ G[X]` is strictly quadratic when every variable occurring in `S` occurs
in it, counted over all its elements, exactly twice. -/
def IsStrictlyQuadratic (S : Finset (GX G X)) : Prop :=
  ∀ x, ∑ w ∈ S, occurrences x w = 0 ∨ ∑ w ∈ S, occurrences x w = 2

theorem isQuadratic_iff {S : Finset (GX G X)} :
    IsQuadratic S ↔ ∀ x, ∑ w ∈ S, occurrences x w ≤ 2 := Iff.rfl

theorem isStrictlyQuadratic_iff {S : Finset (GX G X)} :
    IsStrictlyQuadratic S ↔ ∀ x, ∑ w ∈ S, occurrences x w = 0 ∨ ∑ w ∈ S, occurrences x w = 2 :=
  Iff.rfl

@[simp]
theorem isQuadratic_singleton {w : GX G X} : IsQuadratic {w} ↔ ∀ x, occurrences x w ≤ 2 := by
  simp [isQuadratic_iff]

@[simp]
theorem isStrictlyQuadratic_singleton {w : GX G X} :
    IsStrictlyQuadratic {w} ↔ ∀ x, occurrences x w = 0 ∨ occurrences x w = 2 := by
  simp [isStrictlyQuadratic_iff]

theorem IsStrictlyQuadratic.isQuadratic {S : Finset (GX G X)} (h : IsStrictlyQuadratic S) :
    IsQuadratic S := fun x => by rcases h x with h | h <;> omega

theorem IsQuadratic.mono {S T : Finset (GX G X)} (hT : IsQuadratic T) (h : S ⊆ T) :
    IsQuadratic S := fun x => (Finset.sum_le_sum_of_subset h).trans (hT x)

section Map

variable {Y : Type*} {S : Finset (GX G X)} (φ : GX G X ↪ GX H Y) (σ : X ≃ Y)

private theorem sum_occurrences_map
    (h : ∀ x, ∀ w ∈ S, occurrences (σ x) (φ w) = occurrences x w) (y : Y) :
    ∑ w ∈ S.map φ, occurrences y w = ∑ w ∈ S, occurrences (σ.symm y) w := by
  rw [Finset.sum_map]
  exact Finset.sum_congr rfl fun w hw => by simpa using h (σ.symm y) w hw

/-- An injective map `G[X] → H[Y]` transporting the occurrence counts in the words of a system
along a bijection of the variables preserves quadratic systems. -/
theorem isQuadratic_map_iff (h : ∀ x, ∀ w ∈ S, occurrences (σ x) (φ w) = occurrences x w) :
    IsQuadratic (S.map φ) ↔ IsQuadratic S := by
  simp only [isQuadratic_iff, sum_occurrences_map φ σ h]
  exact σ.symm.forall_congr_right (q := fun x => ∑ w ∈ S, occurrences x w ≤ 2)

/-- An injective map `G[X] → H[Y]` transporting the occurrence counts in the words of a system
along a bijection of the variables preserves strictly quadratic systems. -/
theorem isStrictlyQuadratic_map_iff
    (h : ∀ x, ∀ w ∈ S, occurrences (σ x) (φ w) = occurrences x w) :
    IsStrictlyQuadratic (S.map φ) ↔ IsStrictlyQuadratic S := by
  simp only [isStrictlyQuadratic_iff, sum_occurrences_map φ σ h]
  exact σ.symm.forall_congr_right
    (q := fun x => ∑ w ∈ S, occurrences x w = 0 ∨ ∑ w ∈ S, occurrences x w = 2)

end Map

end IsQuadratic

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

/-- The atoms of a standard quadratic equation, in order: the commutators `[xᵢ, yᵢ]` or the
squares `xᵢ²`, followed by the conjugates `zⱼ⁻¹ cⱼ zⱼ`. -/
def atoms : Standard G X → List (GX G X)
  | orientable _ _ x y _ => List.ofFn fun i => ⁅(inr (FreeGroup.of (x i)) : GX G X)⁻¹,
        (inr (FreeGroup.of (y i)) : GX G X)⁻¹⁆
  | orientableCoeff _ _ _ x y z _ c _ _ _ =>
    List.ofFn (fun i => ⁅(inr (FreeGroup.of (x i)) : GX G X)⁻¹,
        (inr (FreeGroup.of (y i)) : GX G X)⁻¹⁆) ++
      List.ofFn fun j => (inr (FreeGroup.of (z j)) : GX G X)⁻¹ * inl (c j) *
        inr (FreeGroup.of (z j))
  | nonorientable _ _ x _ => List.ofFn fun i => (inr (FreeGroup.of (x i)) : GX G X) ^ 2
  | nonorientableCoeff _ _ _ x z _ c _ _ _ =>
    List.ofFn (fun i => (inr (FreeGroup.of (x i)) : GX G X) ^ 2) ++
      List.ofFn fun j => (inr (FreeGroup.of (z j)) : GX G X)⁻¹ * inl (c j) *
        inr (FreeGroup.of (z j))

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
        (inr (FreeGroup.of (y i)) : GX G X)⁻¹⁆ := (rfl)

@[simp]
theorem atoms_orientableCoeff (hnm : 0 < n + m) (inj : (Sum.elim (Sum.elim x y) z).Injective)
    (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    (orientableCoeff n m hnm x y z inj c hc d hd).atoms =
      List.ofFn (fun i => ⁅(inr (FreeGroup.of (x i)) : GX G X)⁻¹,
          (inr (FreeGroup.of (y i)) : GX G X)⁻¹⁆) ++
        List.ofFn fun j => (inr (FreeGroup.of (z j)) : GX G X)⁻¹ * inl (c j) *
          inr (FreeGroup.of (z j)) := (rfl)

@[simp]
theorem atoms_nonorientable {x : Fin n → X} (hn : 0 < n) (inj : x.Injective) :
    (nonorientable (G := G) n hn x inj).atoms =
      List.ofFn fun i => (inr (FreeGroup.of (x i)) : GX G X) ^ 2 := (rfl)

@[simp]
theorem atoms_nonorientableCoeff {x : Fin n → X} (hn : 0 < n) (inj : (Sum.elim x z).Injective)
    (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    (nonorientableCoeff n m hn x z inj c hc d hd).atoms =
      List.ofFn (fun i => (inr (FreeGroup.of (x i)) : GX G X) ^ 2) ++
        List.ofFn fun j => (inr (FreeGroup.of (z j)) : GX G X)⁻¹ * inl (c j) *
          inr (FreeGroup.of (z j)) := (rfl)

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

/-- An orientable standard quadratic equation of genus `n` with `r` atoms has `n + r`
variables. -/
theorem ncard_vars_of_isOrientable (h : S.IsOrientable) :
    S.vars.ncard = S.genus + S.atomicRank := by
  cases S <;> simp_all [-Set.Sum.elim_range, Set.ncard_range_of_injective, add_assoc]

/-- A non-orientable standard quadratic equation has one variable for each atom. -/
theorem ncard_vars_of_not_isOrientable (h : ¬S.IsOrientable) : S.vars.ncard = S.atomicRank := by
  cases S <;> simp_all [-Set.Sum.elim_range, Set.ncard_range_of_injective]

/-- The Euler characteristic of a standard quadratic equation is `2 - κ(S)`. -/
theorem eulerChar_eq_two_sub_kappa (S : Standard G X) : S.eulerChar = 2 - S.kappa := by
  cases S <;> simp <;> lia

/-- A standard quadratic equation with `κ(S) ≥ 4` has at least two atoms. -/
theorem two_le_atomicRank_of_four_le_kappa (h : 4 ≤ S.kappa) : 2 ≤ S.atomicRank := by
  cases S <;> simp_all <;> lia

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
  simp only [toWord_def, map_mul, map_list_prod, map_eval_atoms_congr hι hv, eval_inl]
  by_cases h : S.constant = 1
  · simp [h]
  · rw [hι _ (constant_mem_coeffs_iff.2 h)]

end Kappa

/-! ### Standard equations are quadratic -/

section IsQuadratic

/-- For an injective `e`, the variable `x` is the value of at most one index. -/
private theorem sum_occurrences_le_one {ι : Type*} [Fintype ι] {e : ι → X} (he : e.Injective)
    (x : X) : ∑ s, occurrences x (inr (FreeGroup.of (e s)) : GX G X) ≤ 1 := by
  classical
  simp only [occurrences_inr_of, Finset.sum_boole, Nat.cast_id]
  exact Finset.card_le_one.2 fun a ha b hb => he <| by simp_all

private theorem occurrences_ofFn_prod_le {k : ℕ} (x : X) (f : Fin k → GX G X) :
    occurrences x (List.ofFn f).prod ≤ ∑ i, occurrences x (f i) :=
  (occurrences_list_prod_le x _).trans_eq (by rw [List.map_ofFn, Fin.sum_ofFn]; rfl)

/-- Every standard quadratic equation is quadratic: each of its variables occurs in at most one
atom, and at most twice there. -/
theorem isQuadratic (S : Standard G X) : IsQuadratic {S.toWord} := by
  rw [isQuadratic_singleton]
  intro x
  have hsq := fun i => occurrences_pow_le (G := G) x (inr (FreeGroup.of i)) 2
  have hconj := fun (i : X) (c : G) => by
    simpa using occurrences_conj_le (G := G) x (inr (FreeGroup.of i)) (inl c)
  have hcomm := fun (i j : X) => by
    simpa using occurrences_commutatorElement_le (G := G) x (inr (FreeGroup.of i))⁻¹
      (inr (FreeGroup.of j))⁻¹
  refine (occurrences_mul_le x _ _).trans ?_
  rw [occurrences_inl, add_zero]
  cases S with
  | orientable n hn y₁ y₂ inj =>
    have h := sum_occurrences_le_one (G := G) inj x
    rw [Fintype.sum_sum_type] at h
    simp only [Sum.elim_inl, Sum.elim_inr] at h
    refine (occurrences_ofFn_prod_le x _).trans ((Finset.sum_le_sum fun i _ => hcomm _ _).trans ?_)
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    omega
  | orientableCoeff n m hnm y₁ y₂ z inj c hc d hd =>
    have h := sum_occurrences_le_one (G := G) inj x
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at h
    simp only [Sum.elim_inl, Sum.elim_inr] at h
    rw [atoms_orientableCoeff, List.prod_append]
    refine (occurrences_mul_le x _ _).trans (add_le_add (occurrences_ofFn_prod_le x _)
      (occurrences_ofFn_prod_le x _)) |>.trans ?_
    refine (add_le_add (Finset.sum_le_sum fun i _ => hcomm _ _)
      (Finset.sum_le_sum fun j _ => hconj _ _)).trans ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib]
    omega
  | nonorientable n hn y inj =>
    have h := sum_occurrences_le_one (G := G) inj x
    refine (occurrences_ofFn_prod_le x _).trans ((Finset.sum_le_sum fun i _ => hsq _).trans ?_)
    rw [← Finset.mul_sum]
    omega
  | nonorientableCoeff n m hn y z inj c hc d hd =>
    have h := sum_occurrences_le_one (G := G) inj x
    rw [Fintype.sum_sum_type] at h
    simp only [Sum.elim_inl, Sum.elim_inr] at h
    rw [atoms_nonorientableCoeff, List.prod_append]
    refine (occurrences_mul_le x _ _).trans (add_le_add (occurrences_ofFn_prod_le x _)
      (occurrences_ofFn_prod_le x _)) |>.trans ?_
    refine (add_le_add (Finset.sum_le_sum fun i _ => hsq _)
      (Finset.sum_le_sum fun j _ => hconj _ _)).trans ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    omega

/-- A variable outside `S.vars` does not occur in the standard quadratic equation `S`. -/
theorem occurrences_toWord_of_notMem_vars {S : Standard G X} {x : X} (hx : x ∉ S.vars) :
    occurrences x S.toWord = 0 := by
  have hcomm (a b : X) (ha : a ≠ x) (hb : b ≠ x) :
      occurrences x ⁅(inr (FreeGroup.of a) : GX G X)⁻¹, (inr (FreeGroup.of b))⁻¹⁆ = 0 :=
    Nat.eq_zero_of_le_zero <| (occurrences_commutatorElement_le ..).trans (by simp [ha, hb])
  have hsq (a : X) (ha : a ≠ x) : occurrences x ((inr (FreeGroup.of a) : GX G X) ^ 2) = 0 :=
    Nat.eq_zero_of_le_zero <| (occurrences_pow_le ..).trans (by simp [ha])
  have hconj (a : X) (c : G) (ha : a ≠ x) :
      occurrences x ((inr (FreeGroup.of a) : GX G X)⁻¹ * inl c * inr (FreeGroup.of a)) = 0 :=
    Nat.eq_zero_of_le_zero <| (occurrences_conj_le ..).trans (by simp [ha])
  have hatom : ∀ r ∈ S.atoms, occurrences x r = 0 := by
    cases S <;> simp_all [or_imp, forall_and]
  refine Nat.eq_zero_of_le_zero <| (occurrences_mul_le x _ _).trans ?_
  rw [occurrences_inl, add_zero]
  exact (occurrences_list_prod_le x _).trans_eq (List.sum_eq_zero (by simpa using hatom))

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

/-- With at least two atoms, a point in general position is not commutative. -/
theorem IsGeneralPosition.not_isCommutative (h : S.IsGeneralPosition ι v)
    (hS : 2 ≤ S.atomicRank) : ¬S.IsCommutative ι v := by
  rw [isGeneralPosition_iff] at h
  rw [isCommutative_iff]
  rw [atomicRank_def] at hS
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
  simp only [mem_V, Set.mem_singleton_iff, forall_eq, toWord_def, constant_orientable, map_one,
    mul_one, map_list_prod, atoms_orientable]
  exact List.prod_eq_one <| by
    simp [map_commutatorElement, commutatorElement_eq_one_iff_commute, hv]

/-- The trivial point is a solution of `∏ᵢ₌₁ⁿ [xᵢ, yᵢ] = 1`. -/
theorem one_mem_V_orientable (ι : G →* H) (hn : 0 < n) (inj : (Sum.elim x y).Injective) :
    1 ∈ V ι {(orientable n hn x y inj).toWord} :=
  mem_V_orientable_of_commute ι hn inj fun _ => .one_left 1

/-- The trivial solution of `∏ᵢ₌₁ⁿ [xᵢ, yᵢ] = 1` is degenerate. -/
theorem isDegenerate_one_orientable (ι : G →* H) (hn : 0 < n) (inj : (Sum.elim x y).Injective) :
    (orientable n hn x y inj).IsDegenerate ι 1 :=
  ⟨_, List.mem_ofFn.2 ⟨⟨0, hn⟩, rfl⟩, by simp [map_commutatorElement]⟩

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
  simp only [mem_V, Set.mem_singleton_iff, forall_eq, toWord_def, constant_orientable, map_mul,
    map_one, mul_one, atoms_orientable, List.ofFn_succ, List.ofFn_zero, List.prod_cons,
    List.prod_nil] at hv
  rw [isCommutative_iff]
  simp only [atoms_orientable, List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil,
    List.isChain_cons_cons, List.isChain_singleton, and_true]
  rw [mul_eq_one_iff_eq_inv] at hv
  rw [hv]
  exact (Commute.refl _).inv_left

/-- The genus-two equation `[x₁, y₁][x₂, y₂] = 1` has no solution in general position. -/
theorem not_isGeneralPosition_of_mem_V_genusTwo {ι : G →* H} {v : X → H} {x y : Fin 2 → X}
    (inj : (Sum.elim x y).Injective) (hv : v ∈ V ι {(orientable 2 two_pos x y inj).toWord}) :
    ¬(orientable 2 two_pos x y inj).IsGeneralPosition ι v := fun h =>
  h.not_isCommutative (by simp) (isCommutative_of_mem_V_genusTwo inj hv)

end Commutators

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
  have hle := hS ▸ isQuadratic_singleton.1 S.isQuadratic
  refine isStrictlyQuadratic_singleton.2 fun x => .inr <| (hle x).antisymm ?_
  have h := countP_toWord_snd_le_occurrences x
    (inr (.of 0) ^ 2 * inr (.of 1) ^ 2 * inr (.of 2) ^ 2 : GX G (Fin 3))
  simp only [_root_.map_mul, map_pow, snd_apply_inr] at h
  have key : ∀ x : Fin 3, 2 ≤ ((FreeGroup.of 0 ^ 2 * FreeGroup.of 1 ^ 2 * FreeGroup.of 2 ^ 2 :
      FreeGroup (Fin 3)).toWord.countP fun p => p.1 = x) := by
    decide
  exact (key x).trans h

/-- `x y x⁻¹ y⁻¹ x` is not quadratic: the variable `x` occurs three times. -/
theorem not_isQuadratic_cubic :
    ¬IsQuadratic {(inr (.of 0) * inr (.of 1) * (inr (.of 0))⁻¹ * (inr (.of 1))⁻¹ * inr (.of 0) :
      GX G (Fin 2))} := by
  rw [isQuadratic_singleton]
  intro h
  have := (countP_toWord_snd_le_occurrences 0 _).trans (h 0)
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
  · simp only [S, v, mem_V, Set.mem_singleton_iff, forall_eq, Standard.toWord_def,
      Standard.atoms_orientable, Standard.constant_orientable, List.ofFn_succ, List.ofFn_zero,
      List.prod_cons, List.prod_nil, _root_.map_mul, _root_.map_one, map_commutatorElement,
      _root_.map_inv, eval_inr, FreeGroup.lift_apply_of, mul_one]
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
  · simp only [S, mem_V, Set.mem_singleton_iff, forall_eq, Standard.toWord_def,
      Standard.atoms_orientableCoeff, Standard.constant_orientableCoeff, List.ofFn_succ,
      List.ofFn_zero, List.nil_append, List.prod_cons, List.prod_nil, _root_.map_mul,
      _root_.map_inv, eval_inr, eval_inl, mul_one]
    decide
  · simp only [S, Standard.isGeneralPosition_iff, Standard.atoms_orientableCoeff, List.ofFn_succ,
      List.ofFn_zero, List.nil_append, List.map_cons, List.map_nil, List.isChain_cons_cons,
      List.isChain_singleton, _root_.map_mul, _root_.map_inv, eval_inr, eval_inl, Commute,
      SemiconjBy, and_true]
    decide

end Examples

end TauCeti.GroupAlgGeom.Quadratic
