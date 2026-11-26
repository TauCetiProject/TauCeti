/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Image
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Fin.VecNotation
public import TauCeti.GroupTheory.FreeGroup.EqIneqSystem.Basic
public import TauCeti.GroupTheory.FreeGroup.Reduce
public import TauCeti.GroupTheory.FreeGroup.Substitution
public import TauCeti.GroupTheory.GroupAlgGeom.AlgebraicSet

/-!
# Generalised equations over a free group

A *combinatorial generalised equation* `Ω` with constants from `A^{±1}` (Makanin; in the form of
Kharlampovich–Myasnikov, Definition 8) is the following finite data. There are `ρ + 1` boundaries
`0, …, ρ` and `ρ` items `h₀, …, h_{ρ-1}`, item `hₖ` lying between boundaries `k` and `k + 1`.
A variable base `μ` spans the items between its boundaries `α(μ) < β(μ)`, carries a sign `ε(μ)`
and a dual base `Δ(μ)` with `Δ(Δ(μ)) = μ`. A constant base occupies a single item and carries a
letter of `A^{±1}`. A boundary connection `(p, μ, q)` relates a boundary `p` strictly inside `μ`
to a boundary `q` strictly inside `Δ(μ)`; with it, `(q, Δ(μ), p)` is also a boundary connection.

Writing `h[i, j] = hᵢ ⋯ h_{j-1}`, the data define three kinds of equations in the items:

* basic equations `h[α(μ), β(μ)] ^ ε(μ) = h[α(Δμ), β(Δμ)] ^ ε(Δμ)`;
* coefficient equations `hₖ = a` for a constant base on item `k` labelled `a`;
* boundary equations `h[α(μ), p] = h[α(Δμ), q]` when `ε(μ) = ε(Δμ)`, and
  `h[α(μ), p] = h[q, β(Δμ)]⁻¹` otherwise.

Each side is a word in the items and the letters of `A`, an element of
`List ((Fin ρ ⊕ A) × Bool)`. A *solution* is a tuple of nonempty reduced words over `A^{±1}`,
one for each item, such that after substitution every side is reduced as written and both sides
of every equation agree letter by letter (Definition 9). Reading the equations in the free group
gives the system `Ω*` over `F(A)` in the items (`TauCeti.GenEq.toSystem`); its coordinate group
`F_{R(Ω)}` is the coordinate group of algebraic geometry over groups, and every solution of `Ω`
gives a point of `Ω*`, hence an `F(A)`-homomorphism `F_{R(Ω)} → F(A)`. The converse fails:
a group solution may cancel within a side (see the examples at the end of the file). It holds for
a tuple of nonempty reduced words which makes every side reduced as written (Remark 4), since two
reduced words representing the same element of `F(A)` are equal. This is the form in which the
elementary transformations of Makanin's process produce solutions: they change the equations in a
way that is easy to follow in the group, and it remains to check that every side is reduced.

A generalised equation is *formally consistent* (Definition 10) when five combinatorial
conditions hold. They are decidable, and every generalised equation with a solution is formally
consistent (Lemma 12): the conditions are forced by comparing lengths of the substituted words,
together with the fact that a nonempty reduced word is not its own formal inverse.

Generalised equations are the objects on which Makanin's process acts: a system of equations and
inequations over `F(A)` is equivalent to a finite family of generalised equations, and the
elementary transformations of the process act on generalised equations.

## Main definitions

* `TauCeti.GenEq A`: combinatorial generalised equations with constants from `A^{±1}`.
* `TauCeti.GenEq.equations`: the basic, coefficient and boundary equations, as pairs of words.
* `TauCeti.GenEq.Solution`: solutions by nonempty reduced words, with graphical equality.
* `TauCeti.GenEq.IsFormallyConsistent`: the conditions of Definition 10, with a `Decidable`
  instance.
* `TauCeti.GenEq.toSystem`: the system `Ω*` of group equations over `F(A)` in the items.
* `TauCeti.GenEq.coordGroup`: the coordinate group `F_{R(Ω)}` of `Ω*` over `F(A)`.
* `TauCeti.GenEq.Solution.toHom`: the `F(A)`-homomorphism `F_{R(Ω)} → F(A)` of a solution.
* `TauCeti.GenEq.Solution.ofMemV`: the solution given by a tuple of nonempty reduced words which
  is a point of `Ω*` and makes every side reduced as written.
* `TauCeti.GenEq.Solution.ofNumBasesEqZero`: without variable or constant bases, every tuple of
  nonempty reduced words is a solution.
* `TauCeti.GenEq.Solution.prefixLength`: the position of a boundary in the words of a solution.
* `TauCeti.GenEq.ofBases`: the generalised equation without boundary connections whose variable
  bases are indexed by a finite type with an involution.

## Main results

* `TauCeti.GenEq.mem_V_toSystem_iff`: the points of `Ω*` are the group solutions of the
  equations of `Ω`.
* `TauCeti.GenEq.Solution.point_mem_V`: a solution of `Ω` is a solution of `Ω*` in `F(A)`.
* `TauCeti.GenEq.substituteVars_eq_of_mem_V`: for a point of `Ω*`, the two sides of an equation
  are equal as words as soon as both are reduced as written.
* `TauCeti.GenEq.forall_mem_equations_isReduced_iff`: a tuple of reduced words makes both sides of
  every equation reduced as written if and only if it makes the word of every variable base reduced
  as written.
* `TauCeti.GenEq.Solution.isFormallyConsistent`: a generalised equation with a solution is
  formally consistent.
* `TauCeti.GenEq.Solution.substituteVars_boundaryEquation_eq_iff`: under a solution, the
  boundary equation of a triple `(p, μ, q)` with `p ≤ β(μ)` holds exactly when its two sides have
  the same length; for a boundary `q` of `Δ(μ)`, when `p` and `q` lie at the same position of the
  words of `μ` and `Δ(μ)`.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §4.1, Definitions 8–10, Remark 4 and Lemma 12.
* G. S. Makanin, *Equations in a free group*, Izv. Akad. Nauk SSSR Ser. Mat. 46 (1982).
-/

public section

namespace TauCeti

open Monoid.Coprod GroupAlgGeom
open FreeGroup (substituteVars substituteVars_append substituteVars_invRev substituteVars_map_inl
  substituteVars_singleton_inl substituteVars_singleton_inr mk_substituteVars)

/-- A combinatorial generalised equation with constants from `A^{±1}` (Kharlampovich–Myasnikov,
Definition 8): `numItems` items between the boundaries `0, …, numItems`, `numBases` variable bases
with end-points, signs and duals, a finite set of constant bases (an item together with a letter
of `A^{±1}`), and a finite set of boundary connections `(p, μ, q)`, closed under passing to the
dual connection `(q, Δμ, p)` as in the source. -/
structure GenEq (A : Type*) where
  /-- The number `ρ` of items. Item `k` lies between the boundaries `k` and `k + 1`. -/
  numItems : ℕ
  /-- The number of variable bases. -/
  numBases : ℕ
  /-- The initial boundary `α(μ)` of a variable base. -/
  left : Fin numBases → Fin (numItems + 1)
  /-- The terminal boundary `β(μ)` of a variable base. -/
  right : Fin numBases → Fin (numItems + 1)
  /-- A variable base spans at least one item. -/
  left_lt_right : ∀ μ, left μ < right μ
  /-- The sign `ε(μ)` of a variable base; `true` stands for `+1` and `false` for `-1`. -/
  sign : Fin numBases → Bool
  /-- The dual `Δ(μ)` of a variable base. -/
  dual : Fin numBases → Fin numBases
  /-- Duality of bases is an involution. -/
  dual_involutive : Function.Involutive dual
  /-- The constant bases: a constant base occupies one item and is labelled by a letter of
  `A^{±1}`. -/
  constBases : Finset (Fin numItems × (A × Bool))
  /-- The boundary connections `(p, μ, q)`. -/
  connections : Finset (Fin (numItems + 1) × Fin numBases × Fin (numItems + 1))
  /-- A boundary connection `(p, μ, q)` joins a boundary `p` strictly inside `μ` to a boundary
  `q` strictly inside `Δ(μ)`. -/
  bounds_of_mem_connections : ∀ c ∈ connections,
    left c.2.1 < c.1 ∧ c.1 < right c.2.1 ∧ left (dual c.2.1) < c.2.2 ∧ c.2.2 < right (dual c.2.1)
  /-- With `(p, μ, q)`, the dual connection `(q, Δ(μ), p)` is a boundary connection. -/
  dual_mem_connections : ∀ c ∈ connections, (c.2.2, dual c.2.1, c.1) ∈ connections

namespace GenEq

variable {A : Type*} (Ω : GenEq A)

/-! ### The equations of a generalised equation -/

/-- The word `h[i, j] ^ ±1` in the items: the items `hᵢ, …, h_{j-1}` in order when `s = true`,
and its formal inverse when `s = false`. -/
def segment (i j : ℕ) (s : Bool) : List ((Fin Ω.numItems ⊕ A) × Bool) :=
  let w := (((List.finRange Ω.numItems).take j).drop i).map fun k => (Sum.inl k, true)
  if s then w else FreeGroup.invRev w

/-- The word `h[i, j]` lists the items `hᵢ, …, h_{j-1}` in order. -/
theorem segment_true (i j : ℕ) : Ω.segment i j true =
    (((List.finRange Ω.numItems).take j).drop i).map fun k => (Sum.inl k, true) := by
  simp [segment]

/-- The word `h[i, j] ^ -1` is the formal inverse of `h[i, j]`. -/
theorem segment_false (i j : ℕ) : Ω.segment i j false = FreeGroup.invRev (Ω.segment i j true) := by
  simp [segment]

/-- The letters of `h[i, j]` are the items `hₖ` with `i ≤ k < j`, each with exponent `1`. -/
theorem mem_segment_true_iff {i j : ℕ} {p : (Fin Ω.numItems ⊕ A) × Bool} :
    p ∈ Ω.segment i j true ↔
      ∃ k : Fin Ω.numItems, (i ≤ k ∧ (k : ℕ) < j) ∧ (Sum.inl k, true) = p := by
  have hmem (k : Fin Ω.numItems) :
      k ∈ ((List.finRange Ω.numItems).take j).drop i ↔ i ≤ k ∧ (k : ℕ) < j := by
    simp only [List.mem_iff_getElem, List.getElem_drop, List.getElem_take, List.getElem_finRange,
      List.length_drop, List.length_take, List.length_finRange, Fin.ext_iff, Fin.val_cast]
    exact ⟨by grind, fun h => ⟨k - i, by grind⟩⟩
  simp only [segment_true, List.mem_map, hmem]

/-- A homomorphism out of the free group on the items and constants evaluates `h[i, j] ^ ±1` as
its value on `h[i, j]`, or the inverse of that value. -/
theorem lift_mk_segment {H : Type*} [Group H] (f : Fin Ω.numItems ⊕ A → H) (i j : ℕ) (s : Bool) :
    FreeGroup.lift f (FreeGroup.mk (Ω.segment i j s)) =
      cond s (FreeGroup.lift f (FreeGroup.mk (Ω.segment i j true)))
        (FreeGroup.lift f (FreeGroup.mk (Ω.segment i j true)))⁻¹ := by
  cases s
  · rw [segment_false, ← FreeGroup.inv_mk, map_inv]
    rfl
  · rfl

/-- A homomorphism out of the free group on the items and constants evaluates `h[i, j] ^ -1` as
the inverse of its value on `h[i, j]`. -/
theorem lift_mk_segment_false {H : Type*} [Group H] (f : Fin Ω.numItems ⊕ A → H) (i j : ℕ) :
    FreeGroup.lift f (FreeGroup.mk (Ω.segment i j false)) =
      (FreeGroup.lift f (FreeGroup.mk (Ω.segment i j true)))⁻¹ :=
  Ω.lift_mk_segment f i j false

/-- The word `h[i, j] ^ ±1` has one letter for each item between the boundaries `i` and `j`. -/
@[simp]
theorem length_segment (i j : ℕ) (s : Bool) :
    (Ω.segment i j s).length = min j Ω.numItems - i := by
  cases s <;> simp [segment, FreeGroup.invRev_length]

/-- The word `h[i, j] ^ ±1` is empty for `j ≤ i`. -/
theorem segment_eq_nil_of_le {i j : ℕ} (h : j ≤ i) (s : Bool) : Ω.segment i j s = [] :=
  List.eq_nil_of_length_eq_zero (by simp; omega)

/-- The word of a single item: `h[k, k + 1] ^ ±1 = hₖ ^ ±1`. -/
@[simp]
theorem segment_succ (k : Fin Ω.numItems) (s : Bool) :
    Ω.segment k (k + 1) s = [(Sum.inl k, s)] := by
  have h : Ω.segment k (k + 1) true = [(Sum.inl k, true)] := by
    apply List.ext_getElem <;> simp [segment] <;> grind
  cases s
  · simp [segment_false, h, FreeGroup.invRev]
  · exact h

/-- Concatenation of segments: `h[i, j] h[j, k] = h[i, k]` for `i ≤ j ≤ k`. -/
theorem segment_append {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    Ω.segment i j true ++ Ω.segment j k true = Ω.segment i k true := by
  simp only [segment_true, ← List.map_append]
  congr 1
  rcases le_or_gt i Ω.numItems with hi | hi
  · set M := (List.finRange Ω.numItems).take k
    have hM : (List.finRange Ω.numItems).take j = M.take j := by
      simp [M, List.take_take, min_eq_left hjk]
    rw [hM]
    conv_rhs => rw [← List.take_append_drop j M]
    rw [List.drop_append_of_le_length (by rw [← hM]; simp [hij, hi])]
  · rw [List.drop_eq_nil_of_le (by simp; omega), List.drop_eq_nil_of_le (by simp; omega),
      List.drop_eq_nil_of_le (by simp; omega), List.append_nil]

/-- An empty segment `h[i, j] ^ ±1` with `j ≤ i` evaluates to `1` in every group. -/
theorem lift_mk_segment_eq_one {H : Type*} [Group H] (f : Fin Ω.numItems ⊕ A → H) {i j : ℕ}
    (h : j ≤ i) (s : Bool) : FreeGroup.lift f (FreeGroup.mk (Ω.segment i j s)) = 1 := by
  rw [Ω.segment_eq_nil_of_le h, ← FreeGroup.one_eq_mk, map_one]

/-- Evaluation of `h[i, k]` in a group factors as `h[i, j] * h[j, k]` for `i ≤ j ≤ k`. -/
theorem lift_mk_segment_eq_mul {H : Type*} [Group H] (f : Fin Ω.numItems ⊕ A → H) {i j k : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k) :
    FreeGroup.lift f (FreeGroup.mk (Ω.segment i k true)) =
      FreeGroup.lift f (FreeGroup.mk (Ω.segment i j true)) *
        FreeGroup.lift f (FreeGroup.mk (Ω.segment j k true)) := by
  rw [← Ω.segment_append hij hjk, ← FreeGroup.mul_mk, map_mul]

/-- The word `h[i, j]` is a prefix of `h[i, k]` for `j ≤ k`. -/
theorem segment_prefix_segment {i j k : ℕ} (hjk : j ≤ k) :
    Ω.segment i j true <+: Ω.segment i k true := by
  simp only [segment_true]
  exact ((List.take_prefix_take_left hjk).drop i).map _

/-- The word `h[j, k]` is a suffix of `h[i, k]` for `i ≤ j`. -/
theorem segment_suffix_segment {i j k : ℕ} (hij : i ≤ j) :
    Ω.segment j k true <:+ Ω.segment i k true := by
  simp only [segment_true]
  exact (List.drop_suffix_drop_left _ hij).map _

/-- The word `h[i, j]⁻¹` is the inverse of `h[i, j]` in `F(A)[h]`. -/
theorem toGX_segment_false (i j : ℕ) :
    EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.segment i j false)) =
      (EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.segment i j true)))⁻¹ := by
  rw [segment_false, ← FreeGroup.inv_mk, map_inv]

/-- The word `h[i, j] ^ ±1` avoids the items outside the section `[i, j]`. -/
theorem toGX_segment_mem_avoiding {i j : ℕ} (s : Bool) {k : Fin Ω.numItems}
    (hk : (k : ℕ) < i ∨ j ≤ k) :
    EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.segment i j s)) ∈ GX.avoiding k := by
  have htrue :
      EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.segment i j true)) ∈ GX.avoiding k := by
    refine EqIneqSystem.toGX_mk_mem_avoiding fun p hp => ?_
    obtain ⟨k', hk', rfl⟩ := Ω.mem_segment_true_iff.1 hp
    simp only [ne_eq, Sum.inl.injEq, Fin.ext_iff]
    omega
  cases s
  · rw [toGX_segment_false]
    exact inv_mem htrue
  · exact htrue

/-- `h[l, r] = h[l, k] hₖ h[k + 1, r]` in `F(A)[h]` for `l ≤ k < r ≤ ρ`. -/
theorem toGX_segment_eq_mul {l k r : ℕ} (hlk : l ≤ k) (hkr : k < r) (hr : r ≤ Ω.numItems) :
    EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.segment l r true)) =
      EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.segment l k true)) *
        inr (FreeGroup.of ⟨k, by omega⟩) *
          EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.segment (k + 1) r true)) := by
  have hseg : Ω.segment l r true = Ω.segment l k true ++ [(Sum.inl ⟨k, by omega⟩, true)] ++
      Ω.segment (k + 1) r true := by
    rw [← Ω.segment_succ ⟨k, by omega⟩, Ω.segment_append hlk (by simp),
      Ω.segment_append (by simp; omega) (by simp; omega)]
  rw [hseg, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, map_mul, map_mul]
  simp [EqIneqSystem.toGX_eq_lift, FreeGroup.lift_mk]

/-- `h[l, r] = h[l, p] (h_p h_{p+1}) h[p + 2, r]` in `F(A)[h]` for `l ≤ p` and `p + 2 ≤ r ≤ ρ`. -/
theorem toGX_segment_eq_mul_pair {l p r : ℕ} (hlp : l ≤ p) (hpr : p + 2 ≤ r)
    (hr : r ≤ Ω.numItems) :
    EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.segment l r true)) =
      EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.segment l p true)) *
        (inr (FreeGroup.of ⟨p, by omega⟩) * inr (FreeGroup.of ⟨p + 1, by omega⟩)) *
          EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk (Ω.segment (p + 2) r true)) := by
  have hnil : Ω.segment (p + 1) (p + 1) true = [] := List.eq_nil_of_length_eq_zero (by simp)
  rw [Ω.toGX_segment_eq_mul hlp (by omega) hr,
    Ω.toGX_segment_eq_mul (l := p + 1) (k := p + 1) le_rfl (by omega) hr, hnil]
  simp [← FreeGroup.one_eq_mk, mul_assoc]

/-- The letters of `A` used by a word `h[i, j] ^ ±1` after substitution of words for the items
are the letters used by the words of the items between the boundaries `i` and `j`. -/
theorem exists_mem_substituteVars_segment_iff (u : Fin Ω.numItems → List (A × Bool))
    {i j : ℕ} {s : Bool} {a : A} :
    (∃ l ∈ substituteVars u (Ω.segment i j s), l.1 = a) ↔
      ∃ k : Fin Ω.numItems, i ≤ k ∧ (k : ℕ) < j ∧ ∃ l ∈ u k, l.1 = a := by
  have htrue : (∃ l ∈ substituteVars u (Ω.segment i j true), l.1 = a) ↔
      ∃ k : Fin Ω.numItems, i ≤ k ∧ (k : ℕ) < j ∧ ∃ l ∈ u k, l.1 = a := by
    simp only [substituteVars, List.mem_flatMap, mem_segment_true_iff, exists_exists_and_eq_and,
      FreeGroup.substituteLetter_true, Sum.elim_inl]
    grind
  cases s
  · rw [← htrue, segment_false, substituteVars_invRev]
    simp [FreeGroup.invRev, or_comm]
  · exact htrue

/-- After substituting words for the items, `h[i, j] ^ ±1` is reduced exactly when `h[i, j]` is,
since a formal inverse is reduced exactly when the word is. -/
theorem isReduced_substituteVars_segment_iff (U : Fin Ω.numItems → List (A × Bool)) (i j : ℕ)
    (s : Bool) : FreeGroup.IsReduced (substituteVars U (Ω.segment i j s)) ↔
      FreeGroup.IsReduced (substituteVars U (Ω.segment i j true)) := by
  cases s
  · rw [segment_false, substituteVars_invRev, FreeGroup.isReduced_invRev]
  · rfl

/-- After substituting words for the items, a subword `h[i', j']` of `h[i, j]`, for `i ≤ i'` and
`j' ≤ j`, is reduced as written if `h[i, j]` is. -/
theorem isReduced_substituteVars_segment_of_le_of_le {w : Fin Ω.numItems → List (A × Bool)}
    {i j i' j' : ℕ} (h : FreeGroup.IsReduced (substituteVars w (Ω.segment i j true)))
    (hi : i ≤ i') (hj : j' ≤ j) :
    FreeGroup.IsReduced (substituteVars w (Ω.segment i' j' true)) := by
  obtain ⟨t, ht⟩ := Ω.segment_prefix_segment (i := i') hj
  obtain ⟨t', ht'⟩ := Ω.segment_suffix_segment (k := j) hi
  rw [← ht', ← ht, substituteVars_append, substituteVars_append] at h
  exact h.infix ⟨substituteVars w t', substituteVars w t, List.append_assoc _ _ _⟩

/-- If two substituted segments `u[a, b] ^ ±1` and `u[c, d] ^ ±1` (with the same sign `s`) are
reduced and `u[c, b] ^ ±1` is nonempty, then `u[a, d] ^ ±1` is reduced. -/
theorem isReduced_substituteVars_segment_of_overlap {u : Fin Ω.numItems → List (A × Bool)}
    {a b c d : ℕ} {s : Bool}
    (h₁ : FreeGroup.IsReduced (substituteVars u (Ω.segment a b s)))
    (h₂ : FreeGroup.IsReduced (substituteVars u (Ω.segment c d s)))
    (hne : substituteVars u (Ω.segment c b s) ≠ []) :
    FreeGroup.IsReduced (substituteVars u (Ω.segment a d s)) := by
  rw [isReduced_substituteVars_segment_iff] at h₁ h₂ ⊢
  have hne' : substituteVars u (Ω.segment c b true) ≠ [] := by
    cases s
    · rw [segment_false, substituteVars_invRev] at hne
      exact fun h => hne (by rw [h, FreeGroup.invRev_empty])
    · exact hne
  rcases le_or_gt c a with hca | hac
  · exact h₂.infix ((Ω.segment_suffix_segment hca).flatMap _).isInfix
  rcases le_or_gt d b with hdb | hbd
  · exact h₁.infix ((Ω.segment_prefix_segment hdb).flatMap _).isInfix
  have hseg (x y : ℕ) : Ω.segment x y true = Ω.segment x (min y Ω.numItems) true := by
    have hlen : (List.finRange Ω.numItems).take Ω.numItems = List.finRange Ω.numItems :=
      List.take_of_length_le (by simp)
    simp only [segment_true, ← List.take_take, hlen]
  set b' := min b Ω.numItems
  set d' := min d Ω.numItems
  have hcb' : c < b' := by
    by_contra h
    apply hne'
    have hnil : Ω.segment c b true = [] :=
      List.eq_nil_of_length_eq_zero (by rw [length_segment]; omega)
    rw [hnil, FreeGroup.substituteVars_nil]
  have hb'd' : b' ≤ d' := min_le_min_right _ hbd.le
  rw [hseg a b, ← Ω.segment_append hac.le hcb'.le, substituteVars_append] at h₁
  rw [hseg c d, ← Ω.segment_append hcb'.le hb'd', substituteVars_append] at h₂
  rw [hseg c b] at hne'
  rw [hseg a d, ← Ω.segment_append (hac.le.trans hcb'.le) hb'd',
    ← Ω.segment_append hac.le hcb'.le,
    substituteVars_append, substituteVars_append]
  exact h₁.append_overlap h₂ hne'

/-- The basic equation `h[α(μ), β(μ)] ^ ε(μ) = h[α(Δμ), β(Δμ)] ^ ε(Δμ)` of a variable base. -/
def basicEquation (μ : Fin Ω.numBases) :
    List ((Fin Ω.numItems ⊕ A) × Bool) × List ((Fin Ω.numItems ⊕ A) × Bool) :=
  (Ω.segment (Ω.left μ) (Ω.right μ) (Ω.sign μ),
    Ω.segment (Ω.left (Ω.dual μ)) (Ω.right (Ω.dual μ)) (Ω.sign (Ω.dual μ)))

/-- The coefficient equation `hₖ = a` of a constant base on item `k` labelled `a`. -/
def coeffEquation (b : Fin Ω.numItems × (A × Bool)) :
    List ((Fin Ω.numItems ⊕ A) × Bool) × List ((Fin Ω.numItems ⊕ A) × Bool) :=
  ([(Sum.inl b.1, true)], [(Sum.inr b.2.1, b.2.2)])

/-- The boundary equation of a boundary connection `(p, μ, q)`: `h[α(μ), p] = h[α(Δμ), q]` when
`ε(μ) = ε(Δμ)`, and `h[α(μ), p] = h[q, β(Δμ)]⁻¹` otherwise. -/
def boundaryEquation (c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)) :
    List ((Fin Ω.numItems ⊕ A) × Bool) × List ((Fin Ω.numItems ⊕ A) × Bool) :=
  if Ω.sign c.2.1 = Ω.sign (Ω.dual c.2.1) then
    (Ω.segment (Ω.left c.2.1) c.1 true, Ω.segment (Ω.left (Ω.dual c.2.1)) c.2.2 true)
  else
    (Ω.segment (Ω.left c.2.1) c.1 true, Ω.segment c.2.2 (Ω.right (Ω.dual c.2.1)) false)

/-- The left side of the basic equation of `μ` is `h[α(μ), β(μ)] ^ ε(μ)`. -/
@[simp]
theorem basicEquation_fst (μ : Fin Ω.numBases) :
    (Ω.basicEquation μ).1 = Ω.segment (Ω.left μ) (Ω.right μ) (Ω.sign μ) :=
  (rfl)

/-- The right side of the basic equation of `μ` is `h[α(Δμ), β(Δμ)] ^ ε(Δμ)`. -/
@[simp]
theorem basicEquation_snd (μ : Fin Ω.numBases) :
    (Ω.basicEquation μ).2 =
      Ω.segment (Ω.left (Ω.dual μ)) (Ω.right (Ω.dual μ)) (Ω.sign (Ω.dual μ)) :=
  (rfl)

/-- The basic equation of `Δ(μ)` is the basic equation of `μ` with its sides exchanged. -/
theorem basicEquation_dual (μ : Fin Ω.numBases) :
    Ω.basicEquation (Ω.dual μ) = (Ω.basicEquation μ).swap :=
  Prod.ext (by simp) (by simp [Ω.dual_involutive μ])

/-- The basic equations of `μ` and `Δ(μ)` have the same two sides, exchanged: as relators, each is
the inverse of the other. -/
theorem mk_basicEquation_dual (μ : Fin Ω.numBases) :
    FreeGroup.mk (Ω.basicEquation (Ω.dual μ)).1 * (FreeGroup.mk (Ω.basicEquation (Ω.dual μ)).2)⁻¹ =
      (FreeGroup.mk (Ω.basicEquation μ).1 * (FreeGroup.mk (Ω.basicEquation μ).2)⁻¹)⁻¹ := by
  rw [basicEquation_dual, Prod.fst_swap, Prod.snd_swap, mul_inv_rev, inv_inv]

/-- The left side of the coefficient equation of a constant base on item `k` is `hₖ`. -/
@[simp]
theorem coeffEquation_fst (b : Fin Ω.numItems × (A × Bool)) :
    (Ω.coeffEquation b).1 = [(Sum.inl b.1, true)] :=
  (rfl)

/-- The right side of the coefficient equation of a constant base is its letter. -/
@[simp]
theorem coeffEquation_snd (b : Fin Ω.numItems × (A × Bool)) :
    (Ω.coeffEquation b).2 = [(Sum.inr b.2.1, b.2.2)] :=
  (rfl)

/-- The left side of the boundary equation of a connection `(p, μ, q)` is `h[α(μ), p]`. -/
@[simp]
theorem boundaryEquation_fst (c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)) :
    (Ω.boundaryEquation c).1 = Ω.segment (Ω.left c.2.1) c.1 true := by
  unfold boundaryEquation
  split_ifs <;> rfl

/-- When `ε(μ) = ε(Δμ)`, the right side of the boundary equation of a connection `(p, μ, q)` is
`h[α(Δμ), q]`. -/
theorem boundaryEquation_snd_of_sign_eq
    {c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)}
    (h : Ω.sign c.2.1 = Ω.sign (Ω.dual c.2.1)) :
    (Ω.boundaryEquation c).2 = Ω.segment (Ω.left (Ω.dual c.2.1)) c.2.2 true := by
  simp only [boundaryEquation, h, ite_true]

/-- When `ε(μ) ≠ ε(Δμ)`, the right side of the boundary equation of a connection `(p, μ, q)` is
`h[q, β(Δμ)]⁻¹`. -/
theorem boundaryEquation_snd_of_sign_ne
    {c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)}
    (h : Ω.sign c.2.1 ≠ Ω.sign (Ω.dual c.2.1)) :
    (Ω.boundaryEquation c).2 = Ω.segment c.2.2 (Ω.right (Ω.dual c.2.1)) false := by
  simp only [boundaryEquation, h, ite_false]

/-- The equations of a generalised equation: its basic, coefficient and boundary equations, each
recorded as the pair of its two sides. -/
def equations : Set (List ((Fin Ω.numItems ⊕ A) × Bool) × List ((Fin Ω.numItems ⊕ A) × Bool)) :=
  Set.range Ω.basicEquation ∪ Ω.coeffEquation '' Ω.constBases ∪
    Ω.boundaryEquation '' Ω.connections

/-- The basic equation of a variable base is an equation of `Ω`. -/
theorem basicEquation_mem_equations (μ : Fin Ω.numBases) : Ω.basicEquation μ ∈ Ω.equations :=
  Or.inl (Or.inl ⟨μ, rfl⟩)

/-- The coefficient equation of a constant base is an equation of `Ω`. -/
theorem coeffEquation_mem_equations {b : Fin Ω.numItems × (A × Bool)} (hb : b ∈ Ω.constBases) :
    Ω.coeffEquation b ∈ Ω.equations :=
  Or.inl (Or.inr ⟨b, hb, rfl⟩)

/-- The boundary equation of a boundary connection is an equation of `Ω`. -/
theorem boundaryEquation_mem_equations
    {c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)}
    (hc : c ∈ Ω.connections) : Ω.boundaryEquation c ∈ Ω.equations :=
  Or.inr ⟨c, hc, rfl⟩

/-- The equations of `Ω` are its basic, coefficient and boundary equations. -/
theorem mem_equations_iff
    {e : List ((Fin Ω.numItems ⊕ A) × Bool) × List ((Fin Ω.numItems ⊕ A) × Bool)} :
    e ∈ Ω.equations ↔ (∃ μ, Ω.basicEquation μ = e) ∨
      (∃ b ∈ Ω.constBases, Ω.coeffEquation b = e) ∨
      (∃ c ∈ Ω.connections, Ω.boundaryEquation c = e) := by
  simp only [equations, Set.mem_union, Set.mem_range, Set.mem_image, Finset.mem_coe, or_assoc]

/-- A property holds for all equations of `Ω` exactly when it holds for its basic, coefficient
and boundary equations. -/
theorem forall_mem_equations
    {P : List ((Fin Ω.numItems ⊕ A) × Bool) × List ((Fin Ω.numItems ⊕ A) × Bool) → Prop} :
    (∀ e ∈ Ω.equations, P e) ↔ (∀ μ, P (Ω.basicEquation μ)) ∧
      (∀ b ∈ Ω.constBases, P (Ω.coeffEquation b)) ∧
      (∀ c ∈ Ω.connections, P (Ω.boundaryEquation c)) := by
  refine ⟨fun h => ⟨fun μ => h _ (Ω.basicEquation_mem_equations μ),
    fun b hb => h _ (Ω.coeffEquation_mem_equations hb),
    fun c hc => h _ (Ω.boundaryEquation_mem_equations hc)⟩, ?_⟩
  rintro ⟨h₁, h₂, h₃⟩ e ((⟨μ, rfl⟩ | ⟨b, hb, rfl⟩) | ⟨c, hc, rfl⟩)
  exacts [h₁ μ, h₂ b hb, h₃ c hc]

/-! ### Solutions -/

/-- A solution of a generalised equation (Kharlampovich–Myasnikov, Definition 9): a tuple of
nonempty reduced words over `A^{±1}`, one for each item, such that after substitution both sides
of every equation are reduced as written and agree letter by letter. In particular no item may be
assigned the empty word. -/
@[ext]
structure Solution where
  /-- The word assigned to each item. -/
  word : Fin Ω.numItems → List (A × Bool)
  /-- Each item is assigned a reduced word. -/
  isReduced_word : ∀ k, FreeGroup.IsReduced (word k)
  /-- Each item is assigned a nonempty word. -/
  word_ne_nil : ∀ k, word k ≠ []
  /-- Both sides of every equation are reduced as written. -/
  isReduced_subst : ∀ e ∈ Ω.equations,
    FreeGroup.IsReduced (substituteVars word e.1) ∧ FreeGroup.IsReduced (substituteVars word e.2)
  /-- Both sides of every equation are equal as words. -/
  subst_eq : ∀ e ∈ Ω.equations, substituteVars word e.1 = substituteVars word e.2

/-! ### The system of group equations and the coordinate group -/

/-- The system `Ω*` of group equations over `F(A)` in the items: `L R⁻¹` for each equation
`L = R` of `Ω`. -/
def toSystem : Set (GX (FreeGroup A) (Fin Ω.numItems)) :=
  (fun e => EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk e.1 * (FreeGroup.mk e.2)⁻¹)) ''
    Ω.equations

/-- The elements of `Ω*` are the words `L R⁻¹` for the equations `L = R` of `Ω`. -/
theorem mem_toSystem_iff {w : GX (FreeGroup A) (Fin Ω.numItems)} :
    w ∈ Ω.toSystem ↔ ∃ e ∈ Ω.equations,
      EqIneqSystem.toGX _ FreeGroup.of (FreeGroup.mk e.1 * (FreeGroup.mk e.2)⁻¹) = w :=
  Iff.rfl

/-- The points of `Ω*` are the group solutions of the equations of `Ω`: the assignments under
which both sides of every equation agree in the group, possibly after cancellation. -/
theorem mem_V_toSystem_iff {H : Type*} [Group H] {ι : FreeGroup A →* H}
    {v : Fin Ω.numItems → H} :
    v ∈ V ι Ω.toSystem ↔ ∀ e ∈ Ω.equations,
      FreeGroup.lift (Sum.elim v (ι ∘ FreeGroup.of)) (FreeGroup.mk e.1) =
        FreeGroup.lift (Sum.elim v (ι ∘ FreeGroup.of)) (FreeGroup.mk e.2) := by
  simp only [toSystem, mem_V, Set.forall_mem_image, EqIneqSystem.eval_toGX,
    EqIneqSystem.eval_eq_lift, map_mul, map_inv, mul_inv_eq_one]

variable {Ω} in
/-- If a tuple of words is a point of `Ω*` in `F(A)` and both sides of an equation of `Ω` are
reduced as written after substitution, the two sides are equal as words. -/
theorem substituteVars_eq_of_mem_V {w : Fin Ω.numItems → List (A × Bool)}
    (hV : (fun k => FreeGroup.mk (w k)) ∈ V (MonoidHom.id (FreeGroup A)) Ω.toSystem)
    {e : List ((Fin Ω.numItems ⊕ A) × Bool) × List ((Fin Ω.numItems ⊕ A) × Bool)}
    (he : e ∈ Ω.equations) (h₁ : FreeGroup.IsReduced (substituteVars w e.1))
    (h₂ : FreeGroup.IsReduced (substituteVars w e.2)) :
    substituteVars w e.1 = substituteVars w e.2 := by
  refine h₁.eq_of_mk_eq h₂ ?_
  simpa [mk_substituteVars] using Ω.mem_V_toSystem_iff.1 hV e he

/-- After substituting reduced words, both sides of a coefficient equation are reduced as written:
one is the word of an item, the other a single letter. -/
theorem isReduced_substituteVars_coeffEquation {w : Fin Ω.numItems → List (A × Bool)}
    (hw : ∀ k, FreeGroup.IsReduced (w k)) (b : Fin Ω.numItems × (A × Bool)) :
    FreeGroup.IsReduced (substituteVars w (Ω.coeffEquation b).1) ∧
      FreeGroup.IsReduced (substituteVars w (Ω.coeffEquation b).2) := by
  simp [hw b.1, FreeGroup.IsReduced.singleton]

/-- For a tuple of reduced words, both sides of every equation of `Ω` are reduced as written after
substitution if and only if the word `h[α(μ), β(μ)]` of every variable base is reduced as written:
coefficient equations substitute to an item word or a single letter, and the two sides of a
boundary equation are factors (or formal inverses of factors) of the words of its base and dual
base. -/
theorem forall_mem_equations_isReduced_iff {w : Fin Ω.numItems → List (A × Bool)}
    (hw : ∀ k, FreeGroup.IsReduced (w k)) :
    (∀ e ∈ Ω.equations, FreeGroup.IsReduced (substituteVars w e.1) ∧
        FreeGroup.IsReduced (substituteVars w e.2)) ↔
      ∀ μ, FreeGroup.IsReduced (substituteVars w (Ω.segment (Ω.left μ) (Ω.right μ) true)) := by
  refine ⟨fun h μ => (Ω.isReduced_substituteVars_segment_iff w _ _ (Ω.sign μ)).1
    (h _ (Ω.basicEquation_mem_equations μ)).1, fun h => Ω.forall_mem_equations.2 ⟨?_, ?_, ?_⟩⟩
  · intro μ
    exact ⟨(Ω.isReduced_substituteVars_segment_iff w _ _ _).2 (h μ),
      (Ω.isReduced_substituteVars_segment_iff w _ _ _).2 (h (Ω.dual μ))⟩
  · exact fun b _ => Ω.isReduced_substituteVars_coeffEquation hw b
  · intro c hc
    obtain ⟨h₁, h₂, h₃, h₄⟩ := Ω.bounds_of_mem_connections c hc
    rw [boundaryEquation_fst]
    refine ⟨?_, ?_⟩
    · have h' := h c.2.1
      rw [← Ω.segment_append h₁.le h₂.le, substituteVars_append] at h'
      exact h'.infix (List.prefix_append _ _).isInfix
    · have h' := h (Ω.dual c.2.1)
      rw [← Ω.segment_append h₃.le h₄.le, substituteVars_append] at h'
      by_cases hs : Ω.sign c.2.1 = Ω.sign (Ω.dual c.2.1)
      · rw [Ω.boundaryEquation_snd_of_sign_eq hs]
        exact h'.infix (List.prefix_append _ _).isInfix
      · rw [Ω.boundaryEquation_snd_of_sign_ne hs, Ω.isReduced_substituteVars_segment_iff]
        exact h'.infix (List.suffix_append _ _).isInfix

/-- The coordinate group `F_{R(Ω)}` of a generalised equation: the coordinate group of the system
`Ω*` over `F(A)`, with solutions taken in `F(A)`. -/
abbrev coordGroup : Type _ :=
  CoordGroup (MonoidHom.id (FreeGroup A)) Ω.toSystem

namespace Solution

variable {Ω} (U : Ω.Solution)

/-- The point of `F(A)^ρ` given by a solution. -/
def point : Fin Ω.numItems → FreeGroup A :=
  fun k => FreeGroup.mk (U.word k)

@[simp]
theorem point_apply (k : Fin Ω.numItems) : U.point k = FreeGroup.mk (U.word k) := (rfl)

/-- A solution is determined by its point, since a reduced word is determined by the element of
`F(A)` it represents. -/
theorem point_injective : Function.Injective (point : Ω.Solution → Fin Ω.numItems → FreeGroup A) :=
  fun U U' h => Solution.ext <| funext fun k =>
    (U.isReduced_word k).eq_of_mk_eq (U'.isReduced_word k) (congrFun h k)

/-- Evaluating a word in the items and the letters of `A` at the point of a solution is
substituting the words of the items and reducing. -/
@[simp]
theorem eval_point_mk (w : List ((Fin Ω.numItems ⊕ A) × Bool)) :
    EqIneqSystem.eval U.point FreeGroup.of (FreeGroup.mk w) =
      FreeGroup.mk (substituteVars U.word w) := by
  rw [mk_substituteVars, EqIneqSystem.eval_eq_lift]
  rfl

/-- Both sides of any equation of `Ω` evaluate to the same element of `F(A)` under the item words
of a solution `U`. -/
theorem lift_mk_eq_of_mem_equations
    {e : List ((Fin Ω.numItems ⊕ A) × Bool) × List ((Fin Ω.numItems ⊕ A) × Bool)}
    (he : e ∈ Ω.equations) :
    FreeGroup.lift (Sum.elim (fun x => FreeGroup.mk (U.word x)) FreeGroup.of)
        (FreeGroup.mk e.1) =
      FreeGroup.lift (Sum.elim (fun x => FreeGroup.mk (U.word x)) FreeGroup.of)
        (FreeGroup.mk e.2) := by
  simpa only [mk_substituteVars] using congrArg FreeGroup.mk (U.subst_eq e he)

/-- A solution of a generalised equation is a solution of the system `Ω*` in `F(A)`. -/
theorem point_mem_V : U.point ∈ V (MonoidHom.id (FreeGroup A)) Ω.toSystem :=
  Ω.mem_V_toSystem_iff.2 fun _ he => by
    simpa only [MonoidHom.coe_id, Function.id_comp, funext U.point_apply] using
      U.lift_mk_eq_of_mem_equations he

/-- In a solution, a nonempty word in the items and the letters of `A` has a nonempty substituted
word: every item carries a nonempty word. -/
theorem substituteVars_word_ne_nil {w : List ((Fin Ω.numItems ⊕ A) × Bool)} (hw : w ≠ []) :
    substituteVars U.word w ≠ [] := by
  obtain ⟨⟨c | a, s⟩, w, rfl⟩ := List.exists_cons_of_ne_nil hw
  · rw [FreeGroup.substituteVars_cons]
    cases s <;> simp [U.word_ne_nil c, FreeGroup.invRev]
  · rw [FreeGroup.substituteVars_cons]
    simp

/-- In a solution, the substituted word of a word in the items and the letters of `A` is empty
exactly when the word is empty. -/
@[simp]
theorem substituteVars_word_eq_nil_iff {w : List ((Fin Ω.numItems ⊕ A) × Bool)} :
    substituteVars U.word w = [] ↔ w = [] :=
  ⟨not_imp_not.1 U.substituteVars_word_ne_nil, fun h => h ▸ FreeGroup.substituteVars_nil _⟩

/-- The solution given by a tuple of nonempty reduced words which is a point of `Ω*` in `F(A)` and
makes both sides of every equation reduced as written. -/
def ofMemV (w : Fin Ω.numItems → List (A × Bool)) (hw : ∀ k, FreeGroup.IsReduced (w k))
    (hw' : ∀ k, w k ≠ [])
    (hred : ∀ e ∈ Ω.equations, FreeGroup.IsReduced (substituteVars w e.1) ∧
      FreeGroup.IsReduced (substituteVars w e.2))
    (hV : (fun k => FreeGroup.mk (w k)) ∈ V (MonoidHom.id (FreeGroup A)) Ω.toSystem) :
    Ω.Solution where
  word := w
  isReduced_word := hw
  word_ne_nil := hw'
  isReduced_subst := hred
  subst_eq e he := substituteVars_eq_of_mem_V hV he (hred e he).1 (hred e he).2

/-- The words of the solution built from a point of `Ω*` are the given words. -/
@[simp]
theorem ofMemV_word (w : Fin Ω.numItems → List (A × Bool)) (hw : ∀ k, FreeGroup.IsReduced (w k))
    (hw' : ∀ k, w k ≠ [])
    (hred : ∀ e ∈ Ω.equations, FreeGroup.IsReduced (substituteVars w e.1) ∧
      FreeGroup.IsReduced (substituteVars w e.2))
    (hV : (fun k => FreeGroup.mk (w k)) ∈ V (MonoidHom.id (FreeGroup A)) Ω.toSystem) :
    (ofMemV w hw hw' hred hV).word = w :=
  (rfl)

/-- A generalised equation without variable or constant bases imposes no condition: every tuple of
nonempty reduced words is a solution. -/
def ofNumBasesEqZero (h : Ω.numBases = 0) (hb : Ω.constBases = ∅)
    (w : Fin Ω.numItems → List (A × Bool)) (hw : ∀ k, FreeGroup.IsReduced (w k))
    (hw' : ∀ k, w k ≠ []) : Ω.Solution where
  word := w
  isReduced_word := hw
  word_ne_nil := hw'
  isReduced_subst := (forall_mem_equations _).2 ⟨fun μ => (Fin.cast h μ).elim0,
    fun _ h' => absurd h' (hb ▸ Finset.notMem_empty _), fun c _ => (Fin.cast h c.2.1).elim0⟩
  subst_eq := (forall_mem_equations _).2 ⟨fun μ => (Fin.cast h μ).elim0,
    fun _ h' => absurd h' (hb ▸ Finset.notMem_empty _), fun c _ => (Fin.cast h c.2.1).elim0⟩

/-- The words of the solution of a generalised equation without bases are the given words. -/
@[simp]
theorem ofNumBasesEqZero_word (h : Ω.numBases = 0) (hb : Ω.constBases = ∅)
    (w : Fin Ω.numItems → List (A × Bool)) (hw : ∀ k, FreeGroup.IsReduced (w k))
    (hw' : ∀ k, w k ≠ []) : (ofNumBasesEqZero h hb w hw hw').word = w :=
  (rfl)

/-- The `F(A)`-homomorphism `F_{R(Ω)} → F(A)` of a solution, sending each item to its word. -/
def toHom : GHom (CoordGroup.coeff (MonoidHom.id (FreeGroup A)) Ω.toSystem)
    (MonoidHom.id (FreeGroup A)) :=
  CoordGroup.evalGHom U.point U.point_mem_V

@[simp]
theorem toHom_mk (w : GX (FreeGroup A) (Fin Ω.numItems)) :
    U.toHom (w : Ω.coordGroup) = eval (MonoidHom.id (FreeGroup A)) U.point w :=
  CoordGroup.evalGHom_mk U.point_mem_V w

/-- The homomorphism of a solution sends each item to its word. -/
theorem toHom_inr_of (k : Fin Ω.numItems) :
    U.toHom ((inr (FreeGroup.of k) : GX (FreeGroup A) (Fin Ω.numItems)) : Ω.coordGroup) =
      FreeGroup.mk (U.word k) := by
  simp

end Solution

/-! ### Formal consistency -/

/-- A generalised equation is *formally consistent* (Kharlampovich–Myasnikov, Definition 10)
when:
1. dual bases of opposite signs do not overlap: neither contains an item of the other;
2. boundary connections through the same base preserve the order of boundaries when the dual
   bases have equal signs, and reverse it otherwise;
3. a boundary connection through a base starting at the same boundary as its dual connects a
   boundary to itself;
4. two constant bases on the same item carry the same letter;
5. boundary connections through the same base at the two ends of a constant base end at adjacent
   boundaries. -/
structure IsFormallyConsistent : Prop where
  disjoint_of_sign_ne : ∀ μ, Ω.sign μ ≠ Ω.sign (Ω.dual μ) →
    Ω.right μ ≤ Ω.left (Ω.dual μ) ∨ Ω.right (Ω.dual μ) ≤ Ω.left μ
  connections_monotone_or_antitone : ∀ c ∈ Ω.connections, ∀ c' ∈ Ω.connections, c.2.1 = c'.2.1 →
    c.1 ≤ c'.1 →
      if Ω.sign c.2.1 = Ω.sign (Ω.dual c.2.1) then c.2.2 ≤ c'.2.2 else c'.2.2 ≤ c.2.2
  eq_of_left_eq : ∀ c ∈ Ω.connections, Ω.left c.2.1 = Ω.left (Ω.dual c.2.1) → c.1 = c.2.2
  label_eq : ∀ b ∈ Ω.constBases, ∀ b' ∈ Ω.constBases, b.1 = b'.1 → b.2 = b'.2
  connections_adjacent : ∀ b ∈ Ω.constBases, ∀ c ∈ Ω.connections, ∀ c' ∈ Ω.connections,
    c.2.1 = c'.2.1 → c.1 = b.1.castSucc → c'.1 = b.1.succ →
      (c.2.2 : ℕ) + 1 = c'.2.2 ∨ (c'.2.2 : ℕ) + 1 = c.2.2

/-- Formal consistency as a conjunction of its five conditions. -/
theorem isFormallyConsistent_iff : Ω.IsFormallyConsistent ↔
    (∀ μ, Ω.sign μ ≠ Ω.sign (Ω.dual μ) →
      Ω.right μ ≤ Ω.left (Ω.dual μ) ∨ Ω.right (Ω.dual μ) ≤ Ω.left μ) ∧
    (∀ c ∈ Ω.connections, ∀ c' ∈ Ω.connections, c.2.1 = c'.2.1 → c.1 ≤ c'.1 →
      if Ω.sign c.2.1 = Ω.sign (Ω.dual c.2.1) then c.2.2 ≤ c'.2.2 else c'.2.2 ≤ c.2.2) ∧
    (∀ c ∈ Ω.connections, Ω.left c.2.1 = Ω.left (Ω.dual c.2.1) → c.1 = c.2.2) ∧
    (∀ b ∈ Ω.constBases, ∀ b' ∈ Ω.constBases, b.1 = b'.1 → b.2 = b'.2) ∧
    (∀ b ∈ Ω.constBases, ∀ c ∈ Ω.connections, ∀ c' ∈ Ω.connections,
      c.2.1 = c'.2.1 → c.1 = b.1.castSucc → c'.1 = b.1.succ →
        (c.2.2 : ℕ) + 1 = c'.2.2 ∨ (c'.2.2 : ℕ) + 1 = c.2.2) :=
  ⟨fun ⟨h₁, h₂, h₃, h₄, h₅⟩ => ⟨h₁, h₂, h₃, h₄, h₅⟩,
    fun ⟨h₁, h₂, h₃, h₄, h₅⟩ => ⟨h₁, h₂, h₃, h₄, h₅⟩⟩

/-- Formal consistency is decidable (Kharlampovich–Myasnikov, Lemma 12(2)). -/
instance [DecidableEq A] : Decidable Ω.IsFormallyConsistent :=
  letI : Decidable (∀ c ∈ Ω.connections, ∀ c' ∈ Ω.connections, c.2.1 = c'.2.1 → c.1 ≤ c'.1 →
      if Ω.sign c.2.1 = Ω.sign (Ω.dual c.2.1) then c.2.2 ≤ c'.2.2 else c'.2.2 ≤ c.2.2) :=
    Finset.decidableDforallFinset (_hp := fun _ _ => Finset.decidableDforallFinset)
  letI : Decidable (∀ c ∈ Ω.connections, Ω.left c.2.1 = Ω.left (Ω.dual c.2.1) → c.1 = c.2.2) :=
    Finset.decidableDforallFinset
  letI : Decidable (∀ b ∈ Ω.constBases, ∀ c ∈ Ω.connections, ∀ c' ∈ Ω.connections,
      c.2.1 = c'.2.1 → c.1 = b.1.castSucc → c'.1 = b.1.succ →
        (c.2.2 : ℕ) + 1 = c'.2.2 ∨ (c'.2.2 : ℕ) + 1 = c.2.2) :=
    Finset.decidableDforallFinset (_hp := fun _ _ =>
      Finset.decidableDforallFinset (_hp := fun _ _ => Finset.decidableDforallFinset))
  decidable_of_iff _ Ω.isFormallyConsistent_iff.symm

variable {Ω} in
/-- In a formally consistent generalised equation, dual bases starting at the same boundary (a
matched pair) have the same sign, since they overlap. -/
theorem IsFormallyConsistent.sign_eq_of_left_eq (hΩ : Ω.IsFormallyConsistent) {μ : Fin Ω.numBases}
    (hl : Ω.left μ = Ω.left (Ω.dual μ)) : Ω.sign μ = Ω.sign (Ω.dual μ) := by
  by_contra hs
  rcases hΩ.disjoint_of_sign_ne μ hs with h | h
  · exact absurd (h.trans_lt (hl ▸ Ω.left_lt_right μ)) (lt_irrefl _)
  · exact absurd (h.trans_lt (hl ▸ Ω.left_lt_right (Ω.dual μ))) (lt_irrefl _)

variable {Ω} in
/-- A generalised equation without constant bases or boundary connections whose dual bases have
equal signs is formally consistent. -/
theorem isFormallyConsistent_of_sign_eq (hs : ∀ μ, Ω.sign μ = Ω.sign (Ω.dual μ))
    (hb : Ω.constBases = ∅) (hc : Ω.connections = ∅) : Ω.IsFormallyConsistent where
  disjoint_of_sign_ne μ h := absurd (hs μ) h
  connections_monotone_or_antitone _ h := absurd h (hc ▸ Finset.notMem_empty _)
  eq_of_left_eq _ h := absurd h (hc ▸ Finset.notMem_empty _)
  label_eq _ h := absurd h (hb ▸ Finset.notMem_empty _)
  connections_adjacent _ h := absurd h (hb ▸ Finset.notMem_empty _)

/-! ### Solutions force formal consistency -/

namespace Solution

variable {Ω} (U : Ω.Solution)

/-- The total length of the words of the items before boundary `i`: the position of boundary `i`
in the words of a solution. -/
def prefixLength (i : ℕ) : ℕ :=
  (((List.finRange Ω.numItems).take i).map fun k => (U.word k).length).sum

theorem prefixLength_def (i : ℕ) :
    U.prefixLength i = (((List.finRange Ω.numItems).take i).map fun k => (U.word k).length).sum :=
  (rfl)

/-- Boundary `0` sits at the start of the words of a solution. -/
@[simp]
theorem prefixLength_zero : U.prefixLength 0 = 0 := by
  simp [prefixLength]

/-- The length of the substituted word `h[i, j] ^ ±1` is the total length of the words of the
items between the boundaries `i` and `j`. -/
theorem length_substituteVars_segment (s : Bool) (i j : ℕ) :
    (substituteVars U.word (Ω.segment i j s)).length =
      ((((List.finRange Ω.numItems).take j).drop i).map fun k => (U.word k).length).sum := by
  have h : (substituteVars U.word (Ω.segment i j true)).length =
      ((((List.finRange Ω.numItems).take j).drop i).map fun k => (U.word k).length).sum := by
    rw [segment_true, substituteVars_map_inl, List.length_flatMap]
  cases s
  · rw [segment_false, substituteVars_invRev, FreeGroup.invRev_length, h]
  · exact h

/-- The word `U[α(μ), β(μ)]` of a variable base is reduced as written. -/
theorem isReduced_substituteVars_segment (μ : Fin Ω.numBases) :
    FreeGroup.IsReduced (substituteVars U.word (Ω.segment (Ω.left μ) (Ω.right μ) true)) :=
  (Ω.isReduced_substituteVars_segment_iff U.word _ _ (Ω.sign μ)).1
    (U.isReduced_subst _ (Ω.basicEquation_mem_equations μ)).1

/-- Inside a variable base the words of a solution are reduced as written: for
`α(ν) ≤ i ≤ j ≤ β(ν)`, the word `U[i, j]` is a factor of `U[α(ν), β(ν)]`, and for `j < i` it is
empty. -/
theorem isReduced_substituteVars_segment_of_le (ν : Fin Ω.numBases) {i j : ℕ}
    (hi : Ω.left ν ≤ i) (hj : j ≤ Ω.right ν) :
    FreeGroup.IsReduced (substituteVars U.word (Ω.segment i j true)) :=
  Ω.isReduced_substituteVars_segment_of_le_of_le (U.isReduced_substituteVars_segment ν) hi hj

/-- When `ε(μ) = ε(Δμ)`, a solution assigns the same word to the bases `μ` and `Δ(μ)`. -/
theorem substituteVars_segment_eq_of_sign_eq {μ : Fin Ω.numBases}
    (hs : Ω.sign μ = Ω.sign (Ω.dual μ)) :
    substituteVars U.word (Ω.segment (Ω.left μ) (Ω.right μ) true) =
      substituteVars U.word (Ω.segment (Ω.left (Ω.dual μ)) (Ω.right (Ω.dual μ)) true) := by
  have e := U.subst_eq _ (Ω.basicEquation_mem_equations μ)
  rw [basicEquation_fst, basicEquation_snd, ← hs] at e
  cases h : Ω.sign μ <;> rw [h] at e
  · rw [segment_false, segment_false, substituteVars_invRev, substituteVars_invRev] at e
    exact FreeGroup.invRev_injective e
  · exact e

/-- When `ε(μ) ≠ ε(Δμ)`, a solution assigns to the base `μ` the formal inverse of the word of
`Δ(μ)`. -/
theorem substituteVars_segment_eq_invRev_of_sign_ne {μ : Fin Ω.numBases}
    (hs : Ω.sign μ ≠ Ω.sign (Ω.dual μ)) :
    substituteVars U.word (Ω.segment (Ω.left μ) (Ω.right μ) true) = FreeGroup.invRev
      (substituteVars U.word (Ω.segment (Ω.left (Ω.dual μ)) (Ω.right (Ω.dual μ)) true)) := by
  have e := U.subst_eq _ (Ω.basicEquation_mem_equations μ)
  rw [basicEquation_fst, basicEquation_snd] at e
  cases h : Ω.sign μ <;> cases h' : Ω.sign (Ω.dual μ) <;> rw [h, h'] at e <;>
    simp only [h, h', ne_eq, not_true_eq_false] at hs
  · rw [segment_false, substituteVars_invRev] at e
    rw [← e, FreeGroup.invRev_invRev]
  · rwa [segment_false, substituteVars_invRev] at e

/-- The substituted word `h[i, j] ^ ±1` spans the words of a solution from boundary `i` to
boundary `j`. -/
theorem length_substituteVars_segment_add_prefixLength (s : Bool) {i j : ℕ} (hij : i ≤ j) :
    (substituteVars U.word (Ω.segment i j s)).length + U.prefixLength i = U.prefixLength j := by
  rw [U.length_substituteVars_segment, prefixLength, prefixLength]
  conv_rhs => rw [← List.take_append_drop i (List.take j (List.finRange Ω.numItems))]
  rw [List.map_append, List.sum_append, List.take_take, min_eq_left hij, add_comm]

/-- The word of an item `hₖ` spans the words of a solution from boundary `k` to boundary `k + 1`:
the prefix length grows across `hₖ` by the length of its word. -/
theorem prefixLength_succ (k : Fin Ω.numItems) :
    U.prefixLength (k + 1) = U.prefixLength k + (U.word k).length := by
  have := U.length_substituteVars_segment_add_prefixLength true (Nat.le_add_right k 1)
  rw [segment_succ, substituteVars_singleton_inl] at this
  omega

/-- Each item carries a nonempty word, so the prefix length grows at least by the number of items
between two boundaries. -/
theorem prefixLength_add_le {i j : ℕ} (hij : i ≤ j) (hj : j ≤ Ω.numItems) :
    U.prefixLength i + (j - i) ≤ U.prefixLength j := by
  rw [← U.length_substituteVars_segment_add_prefixLength true hij, add_comm]
  refine Nat.add_le_add_right ?_ _
  rw [U.length_substituteVars_segment]
  refine le_trans (le_of_eq ?_) (List.length_le_sum_of_one_le _ ?_)
  · simp [hj]
  · simp only [List.mem_map]
    rintro _ ⟨k, -, rfl⟩
    exact List.length_pos_iff.2 (U.word_ne_nil k)

/-- The prefix length is strictly increasing on the boundaries. -/
theorem prefixLength_lt {i j : ℕ} (hij : i < j) (hj : j ≤ Ω.numItems) :
    U.prefixLength i < U.prefixLength j := by
  have := U.prefixLength_add_le hij.le hj
  omega

/-- The prefix length is monotone. -/
theorem prefixLength_mono : Monotone U.prefixLength := fun i j hij => by
  have := U.length_substituteVars_segment_add_prefixLength true hij
  omega

/-- The substituted word `h[i, j] ^ ±1` has length `P(j) - P(i)` for the prefix length `P` of a
solution; for `j ≤ i` both are zero. -/
theorem length_substituteVars_segment_eq_sub (s : Bool) (i j : ℕ) :
    (substituteVars U.word (Ω.segment i j s)).length = U.prefixLength j - U.prefixLength i := by
  rcases le_total i j with hij | hji
  · have := U.length_substituteVars_segment_add_prefixLength s hij
    omega
  · rw [Ω.segment_eq_nil_of_le hji, FreeGroup.substituteVars_nil, List.length_nil]
    have := U.prefixLength_mono hji
    omega

/-- The basic equation of a base `μ` of a generalised equation with a solution, as an identity
between prefix lengths: the words of the dual bases `μ` and `Δ(μ)` have the same length. -/
theorem prefixLength_right_add_prefixLength_left_dual (μ : Fin Ω.numBases) :
    U.prefixLength (Ω.right μ) + U.prefixLength (Ω.left (Ω.dual μ)) =
      U.prefixLength (Ω.right (Ω.dual μ)) + U.prefixLength (Ω.left μ) := by
  have e := congrArg List.length (U.subst_eq _ (Ω.basicEquation_mem_equations μ))
  have l₁ := U.length_substituteVars_segment_add_prefixLength (Ω.sign μ) (Ω.left_lt_right μ).le
  have l₂ := U.length_substituteVars_segment_add_prefixLength (Ω.sign (Ω.dual μ))
    (Ω.left_lt_right (Ω.dual μ)).le
  rw [basicEquation_fst, basicEquation_snd] at e
  omega

/-- Distinct boundaries have distinct prefix lengths. -/
theorem prefixLength_injOn : Set.InjOn U.prefixLength (Set.Iic Ω.numItems) := by
  intro i hi j hj h
  rw [Set.mem_Iic] at hi hj
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact absurd h (U.prefixLength_lt hij hj).ne
  · rfl
  · exact absurd h (U.prefixLength_lt hij hi).ne'

/-- A reduced substituted segment `h[a, b]` cannot equal the formal inverse of a substituted
segment `h[c, d]` with `a ≤ c < b`: an overlap would be a nonempty reduced word equal to its own
formal inverse, and a segment inside another one is too short. This is applied to the two bases of
the basic equation of `μ`, for `ε(μ) = 1` and `ε(Δμ) = -1`, to show that they cannot overlap. -/
private theorem not_overlap {a b c d : ℕ} (hab : a < b) (hb : b ≤ Ω.numItems) (hcd : c < d)
    (hac : a ≤ c) (hcb : c < b)
    (hred : FreeGroup.IsReduced (substituteVars U.word (Ω.segment a b true)))
    (heq : substituteVars U.word (Ω.segment a b true) =
      FreeGroup.invRev (substituteVars U.word (Ω.segment c d true))) : False := by
  have hlen := congrArg List.length heq
  rw [FreeGroup.invRev_length] at hlen
  have h₁ := U.length_substituteVars_segment_add_prefixLength true hab.le
  have h₂ := U.length_substituteVars_segment_add_prefixLength true hcd.le
  rcases le_or_gt b d with hbd | hdb
  · -- The overlap `h[c, b]` is a nonempty reduced word equal to its formal inverse.
    rw [← Ω.segment_append hac hcb.le, ← Ω.segment_append hcb.le hbd,
      substituteVars_append, substituteVars_append, FreeGroup.invRev_append] at heq
    have hX := U.length_substituteVars_segment_add_prefixLength true hac
    have hZ := U.length_substituteVars_segment_add_prefixLength true hbd
    have hXZ : (substituteVars U.word (Ω.segment a c true)).length =
        (FreeGroup.invRev (substituteVars U.word (Ω.segment b d true))).length := by
      rw [FreeGroup.invRev_length]
      omega
    have hCC := (List.append_inj heq hXZ).2
    have hCred : FreeGroup.IsReduced (substituteVars U.word (Ω.segment c b true)) := by
      refine hred.infix ⟨substituteVars U.word (Ω.segment a c true), [], ?_⟩
      rw [List.append_nil, ← substituteVars_append, Ω.segment_append hac hcb.le]
    have hCne : substituteVars U.word (Ω.segment c b true) ≠ [] :=
      U.substituteVars_word_ne_nil (List.ne_nil_of_length_pos (by rw [length_segment]; omega))
    exact hCred.invRev_ne_self hCne hCC.symm
  · -- The base `[c, d]` lies strictly inside `[a, b]`, so its word is shorter.
    have := U.prefixLength_mono hac
    have := U.prefixLength_lt hdb hb
    omega

include U in
/-- Dual bases of opposite signs in a generalised equation with a solution do not overlap. -/
private theorem disjoint_of_sign_ne (μ : Fin Ω.numBases) (hμ : Ω.sign μ ≠ Ω.sign (Ω.dual μ)) :
    Ω.right μ ≤ Ω.left (Ω.dual μ) ∨ Ω.right (Ω.dual μ) ≤ Ω.left μ := by
  -- Reduce to a base `x` of sign `+1` whose dual `y` has sign `-1`.
  suffices H : ∀ x : Fin Ω.numBases, Ω.sign x = true → Ω.sign (Ω.dual x) = false →
      Ω.right x ≤ Ω.left (Ω.dual x) ∨ Ω.right (Ω.dual x) ≤ Ω.left x by
    cases hs : Ω.sign μ
    · have := H (Ω.dual μ) (by simpa [hs] using hμ.symm) (by rw [Ω.dual_involutive]; exact hs)
      rw [Ω.dual_involutive] at this
      exact this.symm
    · exact H μ hs (by simpa [hs] using hμ.symm)
  intro x hx hy
  have ex := U.subst_eq _ (Ω.basicEquation_mem_equations x)
  have rx := (U.isReduced_subst _ (Ω.basicEquation_mem_equations x)).1
  have ry := (U.isReduced_subst _ (Ω.basicEquation_mem_equations x)).2
  simp only [basicEquation_fst, basicEquation_snd] at ex rx ry
  rw [hx, hy, segment_false, substituteVars_invRev] at ex
  rw [hy, segment_false, substituteVars_invRev, FreeGroup.isReduced_invRev] at ry
  rw [hx] at rx
  by_contra hne
  push Not at hne
  have hx' := Ω.left_lt_right x
  have hy' := Ω.left_lt_right (Ω.dual x)
  rcases le_total (Ω.left x : ℕ) (Ω.left (Ω.dual x)) with h | h
  · exact U.not_overlap hx' (Ω.right x).is_le hy' h hne.1 rx ex
  · refine U.not_overlap hy' (Ω.right (Ω.dual x)).is_le hx' h hne.2 ry ?_
    rw [ex, FreeGroup.invRev_invRev]

/-- The boundary equation of a connection `(p, μ, q)` of a generalised equation with a solution,
as an identity between prefix lengths. -/
theorem prefixLength_boundary {c : Fin (Ω.numItems + 1) × Fin Ω.numBases ×
    Fin (Ω.numItems + 1)} (hc : c ∈ Ω.connections) :
    if Ω.sign c.2.1 = Ω.sign (Ω.dual c.2.1) then
      U.prefixLength c.1 + U.prefixLength (Ω.left (Ω.dual c.2.1)) =
        U.prefixLength c.2.2 + U.prefixLength (Ω.left c.2.1)
    else
      U.prefixLength c.1 + U.prefixLength c.2.2 =
        U.prefixLength (Ω.right (Ω.dual c.2.1)) + U.prefixLength (Ω.left c.2.1) := by
  obtain ⟨h₁, -, h₃, h₄⟩ := Ω.bounds_of_mem_connections c hc
  have e := congrArg List.length (U.subst_eq _ (Ω.boundaryEquation_mem_equations hc))
  have l₁ := U.length_substituteVars_segment_add_prefixLength true h₁.le
  split_ifs with hs
  · rw [boundaryEquation_fst, Ω.boundaryEquation_snd_of_sign_eq hs] at e
    have l₂ := U.length_substituteVars_segment_add_prefixLength true h₃.le
    omega
  · rw [boundaryEquation_fst, Ω.boundaryEquation_snd_of_sign_ne hs] at e
    have l₂ := U.length_substituteVars_segment_add_prefixLength false h₄.le
    omega

include U in
private theorem connections_monotone_or_antitone (c : Fin (Ω.numItems + 1) × Fin Ω.numBases ×
    Fin (Ω.numItems + 1)) (hc : c ∈ Ω.connections) (c' : Fin (Ω.numItems + 1) × Fin Ω.numBases ×
    Fin (Ω.numItems + 1)) (hc' : c' ∈ Ω.connections) (hμ : c.2.1 = c'.2.1) (hp : c.1 ≤ c'.1) :
    if Ω.sign c.2.1 = Ω.sign (Ω.dual c.2.1) then c.2.2 ≤ c'.2.2 else c'.2.2 ≤ c.2.2 := by
  obtain ⟨p, μ, q⟩ := c
  obtain ⟨p', μ', q'⟩ := c'
  obtain rfl : μ = μ' := hμ
  have e := U.prefixLength_boundary hc
  have e' := U.prefixLength_boundary hc'
  have hpp := U.prefixLength_mono (Fin.le_def.1 hp)
  simp only at e e' hpp ⊢
  split_ifs at e e' ⊢
  · rw [Fin.le_def]
    by_contra hq
    have := U.prefixLength_lt (not_le.1 hq) q.is_le
    omega
  · rw [Fin.le_def]
    by_contra hq
    have := U.prefixLength_lt (not_le.1 hq) q'.is_le
    omega

include U in
private theorem eq_of_left_eq (c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1))
    (hc : c ∈ Ω.connections) (hleft : Ω.left c.2.1 = Ω.left (Ω.dual c.2.1)) : c.1 = c.2.2 := by
  obtain ⟨p, μ, q⟩ := c
  simp only at hleft ⊢
  -- Dual bases starting at the same boundary overlap, so they have the same sign.
  have hs : Ω.sign μ = Ω.sign (Ω.dual μ) := by
    by_contra hs
    rcases U.disjoint_of_sign_ne μ hs with h | h
    · exact absurd (h.trans_lt (hleft ▸ Ω.left_lt_right μ)) (lt_irrefl _)
    · exact absurd (h.trans_lt (hleft ▸ Ω.left_lt_right (Ω.dual μ))) (lt_irrefl _)
  have e := U.prefixLength_boundary hc
  simp only [hs, ite_true] at e
  rw [hleft] at e
  exact Fin.ext (U.prefixLength_injOn (Set.mem_Iic.2 p.is_le) (Set.mem_Iic.2 q.is_le) (by omega))

/-- The item of a constant base carries the one-letter word of its label. -/
theorem word_of_mem_constBases {b : Fin Ω.numItems × (A × Bool)} (hb : b ∈ Ω.constBases) :
    U.word b.1 = [b.2] := by
  simpa using U.subst_eq _ (Ω.coeffEquation_mem_equations hb)

include U in
private theorem label_eq (b : Fin Ω.numItems × (A × Bool)) (hb : b ∈ Ω.constBases)
    (b' : Fin Ω.numItems × (A × Bool)) (hb' : b' ∈ Ω.constBases) (hk : b.1 = b'.1) :
    b.2 = b'.2 :=
  List.singleton_inj.1 ((U.word_of_mem_constBases hb).symm.trans
    (hk ▸ U.word_of_mem_constBases hb'))

/-- Two boundaries whose positions in the words of a solution differ by one are adjacent: every
item carries a nonempty word. -/
private theorem eq_add_one_of_prefixLength_eq {i j : ℕ} (hj : j ≤ Ω.numItems)
    (h : U.prefixLength j = U.prefixLength i + 1) : j = i + 1 := by
  have hlt : i < j := not_le.1 fun hc => by have := U.prefixLength_mono hc; omega
  have := U.prefixLength_add_le hlt.le hj
  omega

/-- Let the boundaries `q` and `q'` lie, in the words of a solution, at the positions of the two
end-points of an item `hₖ` carrying a one-letter word, in the sense of the boundary equations of
`(k, μ, q)` and `(k + 1, μ, q')` (`TauCeti.GenEq.Solution.prefixLength_boundary`). Then `q` and
`q'` are adjacent. -/
theorem adjacent_of_length_word_eq_one_of_prefixLength_eq {k : Fin Ω.numItems}
    (hk : (U.word k).length = 1) {μ : Fin Ω.numBases} {q q' : Fin (Ω.numItems + 1)}
    (e : if Ω.sign μ = Ω.sign (Ω.dual μ) then
        U.prefixLength k.castSucc + U.prefixLength (Ω.left (Ω.dual μ)) =
          U.prefixLength q + U.prefixLength (Ω.left μ)
      else
        U.prefixLength k.castSucc + U.prefixLength q =
          U.prefixLength (Ω.right (Ω.dual μ)) + U.prefixLength (Ω.left μ))
    (e' : if Ω.sign μ = Ω.sign (Ω.dual μ) then
        U.prefixLength k.succ + U.prefixLength (Ω.left (Ω.dual μ)) =
          U.prefixLength q' + U.prefixLength (Ω.left μ)
      else
        U.prefixLength k.succ + U.prefixLength q' =
          U.prefixLength (Ω.right (Ω.dual μ)) + U.prefixLength (Ω.left μ)) :
    (q : ℕ) + 1 = q' ∨ (q' : ℕ) + 1 = q := by
  have hsucc := U.prefixLength_succ k
  simp only [Fin.val_castSucc, Fin.val_succ] at e e'
  -- The prefix lengths at `q` and `q'` differ by one, which forces adjacent boundaries.
  split_ifs at e e'
  · exact Or.inl (U.eq_add_one_of_prefixLength_eq q'.is_le (by omega)).symm
  · exact Or.inr (U.eq_add_one_of_prefixLength_eq q.is_le (by omega)).symm

include U in
private theorem connections_adjacent (b : Fin Ω.numItems × (A × Bool)) (hb : b ∈ Ω.constBases)
    (c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)) (hc : c ∈ Ω.connections)
    (c' : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)) (hc' : c' ∈ Ω.connections)
    (hμ : c.2.1 = c'.2.1) (hp : c.1 = b.1.castSucc) (hp' : c'.1 = b.1.succ) :
    (c.2.2 : ℕ) + 1 = c'.2.2 ∨ (c'.2.2 : ℕ) + 1 = c.2.2 := by
  obtain ⟨p, μ, q⟩ := c
  obtain ⟨p', μ', q'⟩ := c'
  obtain rfl : μ = μ' := hμ
  simp only at hp hp' ⊢
  subst hp hp'
  exact U.adjacent_of_length_word_eq_one_of_prefixLength_eq
    (by rw [U.word_of_mem_constBases hb, List.length_singleton]) (U.prefixLength_boundary hc)
    (U.prefixLength_boundary hc')

include U in
/-- **Kharlampovich–Myasnikov, Lemma 12(1).** A generalised equation with a solution is formally
consistent. -/
theorem isFormallyConsistent : Ω.IsFormallyConsistent :=
  ⟨U.disjoint_of_sign_ne, U.connections_monotone_or_antitone, U.eq_of_left_eq, U.label_eq,
    U.connections_adjacent⟩

end Solution

/-! ### Boundary equations under a solution

For a boundary `p` of a variable base `μ` and a boundary `q` of `Δ(μ)`, the boundary equation of
the triple `(p, μ, q)` makes sense whether or not `(p, μ, q)` is a boundary connection of `Ω`.
Under a solution `U`, its two sides are factors of the words of `μ` and `Δ(μ)`, so it holds
exactly when `p` and `q` lie at the same position of these words. -/

namespace Solution

variable {Ω} (U : Ω.Solution) {p : Fin (Ω.numItems + 1)} {μ : Fin Ω.numBases}
  {q : Fin (Ω.numItems + 1)}

/-- Under a solution, the left side `h[α(μ), p]` of the boundary equation of `(p, μ, q)` is
reduced as written for `p ≤ β(μ)`: it is a prefix of the word of `μ`. -/
theorem isReduced_substituteVars_boundaryEquation_fst (hp : p ≤ Ω.right μ) :
    FreeGroup.IsReduced (substituteVars U.word (Ω.boundaryEquation (p, μ, q)).1) := by
  rw [boundaryEquation_fst]
  exact U.isReduced_substituteVars_segment_of_le μ le_rfl hp

/-- Under a solution, the right side of the boundary equation of `(p, μ, q)` is reduced as
written for a boundary `q` of `Δ(μ)`: it is a factor of the word of `Δ(μ)`, or the formal inverse
of one. -/
theorem isReduced_substituteVars_boundaryEquation_snd (hq₁ : Ω.left (Ω.dual μ) ≤ q)
    (hq₂ : q ≤ Ω.right (Ω.dual μ)) :
    FreeGroup.IsReduced (substituteVars U.word (Ω.boundaryEquation (p, μ, q)).2) := by
  by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
  · rw [Ω.boundaryEquation_snd_of_sign_eq (c := (p, μ, q)) hs]
    exact U.isReduced_substituteVars_segment_of_le _ le_rfl hq₂
  · rw [Ω.boundaryEquation_snd_of_sign_ne (c := (p, μ, q)) hs,
      isReduced_substituteVars_segment_iff]
    exact U.isReduced_substituteVars_segment_of_le _ hq₁ le_rfl

/-- Under a solution and for `p ≤ β(μ)`, the boundary equation of `(p, μ, q)` holds letter by
letter exactly when its two sides have the same length: `|U[α(μ), p]| = |U[α(Δμ), q]|` when
`ε(μ) = ε(Δμ)`, and `|U[α(μ), p]| = |U[q, β(Δμ)]|` otherwise. For a boundary `q` of `Δ(μ)`, this
says that `p` and `q` lie at the same position of the words of `μ` and `Δ(μ)`, counted from the
left end of both when `ε(μ) = ε(Δμ)` and from the right end of `Δ(μ)` otherwise. -/
theorem substituteVars_boundaryEquation_eq_iff (hp : p ≤ Ω.right μ) :
    substituteVars U.word (Ω.boundaryEquation (p, μ, q)).1 =
        substituteVars U.word (Ω.boundaryEquation (p, μ, q)).2 ↔
      U.prefixLength p - U.prefixLength (Ω.left μ) =
        if Ω.sign μ = Ω.sign (Ω.dual μ) then
          U.prefixLength q - U.prefixLength (Ω.left (Ω.dual μ))
        else U.prefixLength (Ω.right (Ω.dual μ)) - U.prefixLength q := by
  -- The left side is a prefix of the word of `μ`, which is as long as the word of `Δ(μ)`.
  have h₁ : substituteVars U.word (Ω.segment (Ω.left μ) p true) <+:
      substituteVars U.word (Ω.segment (Ω.left μ) (Ω.right μ) true) :=
    (Ω.segment_prefix_segment hp).flatMap _
  have e := U.prefixLength_right_add_prefixLength_left_dual μ
  have l₁ := U.length_substituteVars_segment_eq_sub true (Ω.left μ) p
  have lμ := U.length_substituteVars_segment_eq_sub true (Ω.left μ) (Ω.right μ)
  have hΔ := U.prefixLength_mono (Ω.left_lt_right (Ω.dual μ)).le
  have hlen := h₁.length_le
  rw [boundaryEquation_fst]
  split_ifs with hs
  · rw [Ω.boundaryEquation_snd_of_sign_eq (c := (p, μ, q)) hs]
    dsimp only
    have l₂ := U.length_substituteVars_segment_eq_sub true (Ω.left (Ω.dual μ)) q
    refine ⟨fun h => by have := congrArg List.length h; omega, fun h => ?_⟩
    rcases le_or_gt q (Ω.right (Ω.dual μ)) with hq | hq
    · -- Both sides are prefixes of the word of `μ = Δ(μ)` of the same length.
      have h₂ : substituteVars U.word (Ω.segment (Ω.left (Ω.dual μ)) q true) <+:
          substituteVars U.word (Ω.segment (Ω.left μ) (Ω.right μ) true) := by
        rw [U.substituteVars_segment_eq_of_sign_eq hs]
        exact (Ω.segment_prefix_segment hq).flatMap _
      exact (List.prefix_of_prefix_length_le h₁ h₂ (by omega)).eq_of_length (by omega)
    · -- The right side is longer than the word of `Δ(μ)`.
      have := U.prefixLength_lt hq q.is_le
      omega
  · rw [Ω.boundaryEquation_snd_of_sign_ne (c := (p, μ, q)) hs]
    dsimp only
    have l₂ := U.length_substituteVars_segment_eq_sub false q (Ω.right (Ω.dual μ))
    refine ⟨fun h => by have := congrArg List.length h; omega, fun h => ?_⟩
    rcases le_or_gt (Ω.left (Ω.dual μ)) q with hq | hq
    · -- Both sides are prefixes of the word of `μ = Δ(μ)⁻¹` of the same length.
      have h₂ : substituteVars U.word (Ω.segment q (Ω.right (Ω.dual μ)) false) <+:
          substituteVars U.word (Ω.segment (Ω.left μ) (Ω.right μ) true) := by
        rw [segment_false, substituteVars_invRev, U.substituteVars_segment_eq_invRev_of_sign_ne hs]
        exact (((Ω.segment_suffix_segment hq).flatMap _).map _).reverse
      exact (List.prefix_of_prefix_length_le h₁ h₂ (by omega)).eq_of_length (by omega)
    · -- The right side is longer than the word of `Δ(μ)`.
      have := U.prefixLength_lt hq (Ω.left (Ω.dual μ)).is_le
      omega

/-- Under a solution, the boundary equation of the dual triple `(q, Δ(μ), p)` holds exactly when
the boundary equation of `(p, μ, q)` holds, for a boundary `p` of `μ` and a boundary `q` of
`Δ(μ)`: the words of `μ` and `Δ(μ)` have the same length. -/
theorem substituteVars_boundaryEquation_dual_eq_iff (hp₁ : Ω.left μ ≤ p) (hp₂ : p ≤ Ω.right μ)
    (hq₁ : Ω.left (Ω.dual μ) ≤ q) (hq₂ : q ≤ Ω.right (Ω.dual μ)) :
    substituteVars U.word (Ω.boundaryEquation (q, Ω.dual μ, p)).1 =
        substituteVars U.word (Ω.boundaryEquation (q, Ω.dual μ, p)).2 ↔
      substituteVars U.word (Ω.boundaryEquation (p, μ, q)).1 =
        substituteVars U.word (Ω.boundaryEquation (p, μ, q)).2 := by
  rw [U.substituteVars_boundaryEquation_eq_iff hq₂, U.substituteVars_boundaryEquation_eq_iff hp₂]
  have e := U.prefixLength_right_add_prefixLength_left_dual μ
  have m₁ := U.prefixLength_mono hp₁
  have m₂ := U.prefixLength_mono hp₂
  have m₃ := U.prefixLength_mono hq₁
  have m₄ := U.prefixLength_mono hq₂
  simp only [Ω.dual_involutive μ, eq_comm (a := Ω.sign (Ω.dual μ))]
  split_ifs <;> omega

end Solution

/-- When `ε(μ) = ε(Δμ)`, any group assignment satisfying the basic equation of `μ` gives the same
value to `h[α(μ), β(μ)]` and `h[α(Δμ), β(Δμ)]`. -/
theorem lift_mk_segment_eq_of_sign_eq {H : Type*} [Group H] {f : Fin Ω.numItems ⊕ A → H}
    {μ : Fin Ω.numBases} (hs : Ω.sign μ = Ω.sign (Ω.dual μ))
    (hb : FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).1) =
      FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).2)) :
    FreeGroup.lift f (FreeGroup.mk (Ω.segment (Ω.left μ) (Ω.right μ) true)) =
      FreeGroup.lift f
        (FreeGroup.mk (Ω.segment (Ω.left (Ω.dual μ)) (Ω.right (Ω.dual μ)) true)) := by
  rw [basicEquation_fst, basicEquation_snd, Ω.lift_mk_segment f _ _ (Ω.sign μ),
    Ω.lift_mk_segment f _ _ (Ω.sign (Ω.dual μ)), ← hs] at hb
  cases h₁ : Ω.sign μ <;> simp only [h₁, Bool.cond_false, Bool.cond_true, inv_inj] at hb <;>
    exact hb

/-- When `ε(μ) ≠ ε(Δμ)`, any group assignment satisfying the basic equation of `μ` evaluates
`h[α(μ), β(μ)]` to the inverse of `h[α(Δμ), β(Δμ)]`. -/
theorem lift_mk_segment_eq_inv_of_sign_ne {H : Type*} [Group H] {f : Fin Ω.numItems ⊕ A → H}
    {μ : Fin Ω.numBases} (hs : Ω.sign μ ≠ Ω.sign (Ω.dual μ))
    (hb : FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).1) =
      FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).2)) :
    FreeGroup.lift f (FreeGroup.mk (Ω.segment (Ω.left μ) (Ω.right μ) true)) =
      (FreeGroup.lift f
        (FreeGroup.mk (Ω.segment (Ω.left (Ω.dual μ)) (Ω.right (Ω.dual μ)) true)))⁻¹ := by
  rw [basicEquation_fst, basicEquation_snd, Ω.lift_mk_segment f _ _ (Ω.sign μ),
    Ω.lift_mk_segment f _ _ (Ω.sign (Ω.dual μ))] at hb
  cases h₁ : Ω.sign μ <;> cases h₂ : Ω.sign (Ω.dual μ)
  · exact absurd (h₁.trans h₂.symm) hs
  · simpa only [h₁, h₂, Bool.cond_false, Bool.cond_true, inv_eq_iff_eq_inv] using hb
  · simpa only [h₁, h₂, Bool.cond_false, Bool.cond_true] using hb
  · exact absurd (h₁.trans h₂.symm) hs

/-- Under any group assignment satisfying the basic equation of `μ`, the boundary equation of the
dual triple `(q, Δ(μ), p)` holds in the group if and only if that of `(p, μ, q)` holds, for a
boundary `p` of `μ` and a boundary `q` of `Δ(μ)`. -/
theorem lift_mk_boundaryEquation_dual_iff {H : Type*} [Group H] (f : Fin Ω.numItems ⊕ A → H)
    {p : Fin (Ω.numItems + 1)} {μ : Fin Ω.numBases} {q : Fin (Ω.numItems + 1)}
    (hp₁ : Ω.left μ ≤ p) (hp₂ : p ≤ Ω.right μ)
    (hq₁ : Ω.left (Ω.dual μ) ≤ q) (hq₂ : q ≤ Ω.right (Ω.dual μ))
    (hb : FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).1) =
      FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).2)) :
    FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation (q, Ω.dual μ, p)).1) =
        FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation (q, Ω.dual μ, p)).2) ↔
      FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation (p, μ, q)).1) =
        FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation (p, μ, q)).2) := by
  by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
  · have hs' : Ω.sign (Ω.dual μ) = Ω.sign (Ω.dual (Ω.dual μ)) := by
      rw [Ω.dual_involutive μ]
      exact hs.symm
    rw [boundaryEquation_fst, Ω.boundaryEquation_snd_of_sign_eq (c := (q, Ω.dual μ, p)) hs',
      boundaryEquation_fst, Ω.boundaryEquation_snd_of_sign_eq (c := (p, μ, q)) hs,
      Ω.dual_involutive μ]
    exact eq_comm
  · have hs' : Ω.sign (Ω.dual μ) ≠ Ω.sign (Ω.dual (Ω.dual μ)) := by
      rw [Ω.dual_involutive μ]
      exact Ne.symm hs
    have hbase := Ω.lift_mk_segment_eq_inv_of_sign_ne hs hb
    rw [Ω.lift_mk_segment_eq_mul f hp₁ hp₂, Ω.lift_mk_segment_eq_mul f hq₁ hq₂,
      mul_inv_rev] at hbase
    rw [boundaryEquation_fst, Ω.boundaryEquation_snd_of_sign_ne (c := (q, Ω.dual μ, p)) hs',
      boundaryEquation_fst, Ω.boundaryEquation_snd_of_sign_ne (c := (p, μ, q)) hs,
      Ω.dual_involutive μ, Ω.lift_mk_segment_false, Ω.lift_mk_segment_false]
    refine ⟨fun h1 => ?_, fun h2 => ?_⟩
    · have h1' : (FreeGroup.lift f (FreeGroup.mk (Ω.segment (Ω.left (Ω.dual μ)) q true)))⁻¹ =
          FreeGroup.lift f (FreeGroup.mk (Ω.segment p (Ω.right μ) true)) := by
        rw [h1, inv_inv]
      rw [h1'] at hbase
      exact mul_right_cancel hbase
    · rw [h2] at hbase
      rw [← inv_inv (FreeGroup.lift f (FreeGroup.mk (Ω.segment (Ω.left (Ω.dual μ)) q true))),
        ← mul_left_cancel hbase]

/-! ### Generalised equations with bases indexed by a finite type -/

section OfBases

variable {β : Type*} [Finite β] (ρ : ℕ) (left right : β → Fin (ρ + 1))
  (left_lt_right : ∀ b, left b < right b) (sign : β → Bool) (dual : β → β)
  (dual_involutive : Function.Involutive dual) (constBases : Finset (Fin ρ × (A × Bool)))

/-- The generalised equation with `ρ` items whose variable bases are indexed by a finite type `β`:
the base `b` spans the items between the boundaries `left b < right b`, has sign `sign b` and
dual `dual b`, for an involution `dual` of `β`. Its constant bases are `constBases`, and it has
no boundary connections. The bases are numbered by an arbitrary enumeration of `β`. -/
noncomputable abbrev ofBases : GenEq A :=
  letI := Fintype.ofFinite β
  { numItems := ρ
    numBases := Fintype.card β
    left μ := left ((Fintype.equivFin β).symm μ)
    right μ := right ((Fintype.equivFin β).symm μ)
    left_lt_right _ := left_lt_right _
    sign μ := sign ((Fintype.equivFin β).symm μ)
    dual μ := Fintype.equivFin β (dual ((Fintype.equivFin β).symm μ))
    dual_involutive μ := by simp [dual_involutive _]
    constBases := constBases
    connections := ∅
    bounds_of_mem_connections := by simp
    dual_mem_connections := by simp }

/-- The equations of `ofBases` are the basic equations
`h[left b, right b] ^ sign b = h[left (dual b), right (dual b)] ^ sign (dual b)` of the bases
indexed by `β` and the coefficient equations of the constant bases. -/
theorem mem_equations_ofBases_iff {e : List ((Fin ρ ⊕ A) × Bool) × List ((Fin ρ ⊕ A) × Bool)} :
    e ∈ (ofBases ρ left right left_lt_right sign dual dual_involutive constBases).equations ↔
      (∃ b, ((ofBases ρ left right left_lt_right sign dual dual_involutive constBases).segment
          (left b) (right b) (sign b),
        (ofBases ρ left right left_lt_right sign dual dual_involutive constBases).segment
          (left (dual b)) (right (dual b)) (sign (dual b))) = e) ∨
      ∃ c ∈ constBases,
        (ofBases ρ left right left_lt_right sign dual dual_involutive constBases).coeffEquation
          c = e := by
  let := Fintype.ofFinite β
  rw [mem_equations_iff]
  simp only [Finset.notMem_empty, false_and, exists_false, or_false]
  refine or_congr_left ⟨?_, ?_⟩
  · rintro ⟨μ, rfl⟩
    exact ⟨(Fintype.equivFin β).symm μ, by simp [basicEquation]⟩
  · rintro ⟨b, rfl⟩
    exact ⟨Fintype.equivFin β b, by simp [basicEquation]⟩

end OfBases

/-! ### Examples -/

/-- The generalised equation with no items and no bases. -/
@[expose] def empty : GenEq A where
  numItems := 0
  numBases := 0
  left := Fin.elim0
  right := Fin.elim0
  left_lt_right := fun μ => μ.elim0
  sign := Fin.elim0
  dual := Fin.elim0
  dual_involutive := fun μ => μ.elim0
  constBases := ∅
  connections := ∅
  bounds_of_mem_connections := by simp
  dual_mem_connections := by simp

/-- A generalised equation without items is the empty one: a base spans at least one item. -/
theorem eq_empty_of_numItems_eq_zero {Ω : GenEq A} (h : Ω.numItems = 0) : Ω = empty := by
  obtain ⟨ρ, n, left, right, hlr, sign, dual, _, C, BC, _, _⟩ := Ω
  obtain rfl : ρ = 0 := h
  obtain rfl : n = 0 :=
    Nat.eq_zero_of_not_pos fun hn => (hlr ⟨0, hn⟩).ne (Fin.subsingleton_one.elim _ _)
  obtain rfl : C = ∅ := Finset.eq_empty_of_forall_notMem fun b _ => b.1.elim0
  obtain rfl : BC = ∅ := Finset.eq_empty_of_forall_notMem fun c _ => c.2.1.elim0
  obtain rfl : left = Fin.elim0 := funext fun μ => μ.elim0
  obtain rfl : right = Fin.elim0 := funext fun μ => μ.elim0
  obtain rfl : sign = Fin.elim0 := funext fun μ => μ.elim0
  obtain rfl : dual = Fin.elim0 := funext fun μ => μ.elim0
  rfl

/-- The generalised equation with no items and no bases has exactly one solution, the empty
tuple. -/
instance : Unique (empty : GenEq A).Solution where
  default := Solution.ofNumBasesEqZero rfl rfl Fin.elim0 (fun k => k.elim0) fun k => k.elim0
  uniq _ := Solution.ext (funext fun k => k.elim0)

/-- The generalised equation of Kharlampovich–Myasnikov, Fig. 2, read off a cancellation tree of
the Malcev equation `[x, y][b, a] = 1` over `F(a, b)`, with `a = 0` and `b = 1`. Numbering the
items `h₁, …, h₁₀` as in the source, its basic equations are `h₁ = h₇`, `h₂ = h₈`, `h₅ = h₆`,
`h₁h₂h₃h₄ = h₆h₇` and `h₅ = h₈h₉h₁₀`, and its coefficient equations are `h₃ = b`, `h₄ = a`,
`h₉ = a` and `h₁₀ = b`. -/
private abbrev malcevExample : GenEq (Fin 2) where
  numItems := 10
  numBases := 10
  left := ![0, 6, 1, 7, 4, 5, 0, 5, 4, 7]
  right := ![1, 7, 2, 8, 5, 6, 4, 7, 5, 10]
  left_lt_right := by decide
  sign := fun _ => true
  dual := ![1, 0, 3, 2, 5, 4, 7, 6, 9, 8]
  dual_involutive := by unfold Function.Involutive; decide
  constBases := {(2, (1, true)), (3, (0, true)), (8, (0, true)), (9, (1, true))}
  connections := ∅
  bounds_of_mem_connections := fun _ hc => absurd hc (Finset.notMem_empty _)
  dual_mem_connections := fun _ hc => absurd hc (Finset.notMem_empty _)

/-- A solution of the generalised equation of Fig. 2: `h₁ = h₇ = ba`, `h₂ = h₈ = b`,
`h₅ = h₆ = bab`, together with the letters `h₃ = b`, `h₄ = a`, `h₉ = a` and `h₁₀ = b`. Both sides
of `h₁h₂h₃h₄ = h₆h₇` become the reduced word `babba`. -/
private def malcevSolution : malcevExample.Solution where
  word := ![[(1, true), (0, true)], [(1, true)], [(1, true)], [(0, true)],
    [(1, true), (0, true), (1, true)], [(1, true), (0, true), (1, true)], [(1, true), (0, true)],
    [(1, true)], [(0, true)], [(1, true)]]
  isReduced_word := by unfold FreeGroup.IsReduced; decide
  word_ne_nil := by decide
  isReduced_subst := (forall_mem_equations _).2 ⟨by unfold FreeGroup.IsReduced; decide,
    by unfold FreeGroup.IsReduced; decide, fun _ hc => absurd hc (Finset.notMem_empty _)⟩
  subst_eq := (forall_mem_equations _).2 ⟨by decide, by decide,
    fun _ hc => absurd hc (Finset.notMem_empty _)⟩

/-- The generalised equation of Fig. 2 is formally consistent, since it has a solution. -/
example : malcevExample.IsFormallyConsistent :=
  malcevSolution.isFormallyConsistent

/-- The generalised equation with the single basic equation `h₁h₂ = h₃`. -/
private abbrev cancelExample : GenEq (Fin 2) where
  numItems := 3
  numBases := 2
  left := ![0, 2]
  right := ![2, 3]
  left_lt_right := by decide
  sign := fun _ => true
  dual := ![1, 0]
  dual_involutive := by unfold Function.Involutive; decide
  constBases := ∅
  connections := ∅
  bounds_of_mem_connections := fun _ hc => absurd hc (Finset.notMem_empty _)
  dual_mem_connections := fun _ hc => absurd hc (Finset.notMem_empty _)

/-- The assignment `h₁ = a`, `h₂ = a⁻¹b`, `h₃ = b`, with `a = 0` and `b = 1`. -/
private def cancelWord : Fin 3 → List (Fin 2 × Bool) :=
  ![[(0, true)], [(0, false), (1, true)], [(1, true)]]

/-- The assignment `h₁ = a`, `h₂ = a⁻¹b`, `h₃ = b` is not a solution of `h₁h₂ = h₃`: the word
`a a⁻¹ b` is not reduced as written and differs from `b`. -/
example (U : cancelExample.Solution) : U.word ≠ cancelWord := by
  intro hU
  have h := U.subst_eq _ (cancelExample.basicEquation_mem_equations 0)
  rw [hU] at h
  revert h
  decide

/-- The assignment `h₁ = a`, `h₂ = a⁻¹b`, `h₃ = b` is a solution of `h₁h₂ = h₃` in the group
`F(a, b)`, that is, a point of the system `Ω*`. -/
example : (fun k => FreeGroup.mk (cancelWord k)) ∈
    V (MonoidHom.id (FreeGroup (Fin 2))) cancelExample.toSystem := by
  rw [mem_V_toSystem_iff, forall_mem_equations]
  refine ⟨by decide, fun _ hb => absurd hb (Finset.notMem_empty _),
    fun _ hc => absurd hc (Finset.notMem_empty _)⟩

/-- The generalised equation with the single basic equation `h₁ = h₂`. -/
private abbrev equalExample : GenEq A where
  numItems := 2
  numBases := 2
  left := ![0, 1]
  right := ![1, 2]
  left_lt_right := by decide
  sign := fun _ => true
  dual := ![1, 0]
  dual_involutive := by unfold Function.Involutive; decide
  constBases := ∅
  connections := ∅
  bounds_of_mem_connections := fun _ hc => absurd hc (Finset.notMem_empty _)
  dual_mem_connections := fun _ hc => absurd hc (Finset.notMem_empty _)

/-- Every nonempty reduced word `u` gives the solution `h₁ = h₂ = u` of the generalised equation
`h₁ = h₂`: the tuple `(u, u)` is a point of `Ω*`, and both sides of the equation are the reduced
word `u`. -/
example {u : List (A × Bool)} (hu : FreeGroup.IsReduced u) (hu' : u ≠ []) :
    ∃ U : (equalExample (A := A)).Solution, ∀ k, U.word k = u := by
  have h₀ : (equalExample (A := A)).segment 0 1 true = [(Sum.inl 0, true)] :=
    equalExample.segment_succ 0 true
  have h₁ : (equalExample (A := A)).segment 1 2 true = [(Sum.inl 1, true)] :=
    equalExample.segment_succ 1 true
  have hsub : ∀ e ∈ (equalExample (A := A)).equations,
      substituteVars (fun _ => u) e.1 = u ∧ substituteVars (fun _ => u) e.2 = u := by
    refine (forall_mem_equations _).2 ⟨?_, by simp, by simp⟩
    rw [Fin.forall_fin_two]
    simp [h₀, h₁, substituteVars_singleton_inl]
  refine ⟨Solution.ofMemV (fun _ => u) (fun _ => hu) (fun _ => hu')
    (fun e he => by rw [(hsub e he).1, (hsub e he).2]; exact ⟨hu, hu⟩) ?_,
    fun k => congrFun (Solution.ofMemV_word ..) k⟩
  refine (mem_V_toSystem_iff _).2 fun e he => ?_
  rw [MonoidHom.coe_id, Function.id_comp, ← mk_substituteVars, ← mk_substituteVars,
    (hsub e he).1, (hsub e he).2]

end GenEq

end TauCeti
