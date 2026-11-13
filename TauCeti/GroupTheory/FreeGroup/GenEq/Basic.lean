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
* `TauCeti.GenEq.Solution.isFormallyConsistent`: a generalised equation with a solution is
  formally consistent.

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

/-- The word `h[i, j] ^ ±1` has one letter for each item between the boundaries `i` and `j`. -/
@[simp]
theorem length_segment (i j : ℕ) (s : Bool) :
    (Ω.segment i j s).length = min j Ω.numItems - i := by
  cases s <;> simp [segment, FreeGroup.invRev_length]

/-- The word of a single item: `h[k, k + 1] ^ ±1 = hₖ ^ ±1`. -/
@[simp]
theorem segment_succ (k : Fin Ω.numItems) (s : Bool) :
    Ω.segment k (k + 1) s = [(Sum.inl k, s)] := by
  have h : Ω.segment k (k + 1) true = [(Sum.inl k, true)] := by
    apply List.ext_getElem <;> simp [segment] <;> grind
  cases s
  · simp [segment_false, h, FreeGroup.invRev]
  · exact h

/-- Concatenation of segments: `h[i, j] h[j, k] = h[i, k]` for `i ≤ j ≤ k ≤ ρ`. -/
theorem segment_append {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (hk : k ≤ Ω.numItems) :
    Ω.segment i j true ++ Ω.segment j k true = Ω.segment i k true := by
  simp only [segment_true, ← List.map_append]
  congr 1
  set M := (List.finRange Ω.numItems).take k
  have hM : (List.finRange Ω.numItems).take j = M.take j := by
    simp [M, List.take_take, min_eq_left hjk]
  rw [hM]
  conv_rhs => rw [← List.take_append_drop j M]
  rw [List.drop_append_of_le_length (by simp [M]; omega)]

/-- The letters of `A` used by a word `h[i, j] ^ ±1` after substitution of words for the items
are the letters used by the words of the items between the boundaries `i` and `j`. -/
theorem exists_mem_substituteVars_segment_iff (u : Fin Ω.numItems → List (A × Bool))
    {i j : ℕ} {s : Bool} {a : A} :
    (∃ l ∈ substituteVars u (Ω.segment i j s), l.1 = a) ↔
      ∃ k : Fin Ω.numItems, i ≤ k ∧ (k : ℕ) < j ∧ ∃ l ∈ u k, l.1 = a := by
  have hmem (k : Fin Ω.numItems) :
      k ∈ ((List.finRange Ω.numItems).take j).drop i ↔ i ≤ k ∧ (k : ℕ) < j := by
    simp only [List.mem_iff_getElem, List.getElem_drop, List.getElem_take, List.getElem_finRange,
      List.length_drop, List.length_take, List.length_finRange, Fin.ext_iff, Fin.val_cast]
    exact ⟨by grind, fun h => ⟨k - i, by grind⟩⟩
  have htrue : (∃ l ∈ substituteVars u (Ω.segment i j true), l.1 = a) ↔
      ∃ k : Fin Ω.numItems, i ≤ k ∧ (k : ℕ) < j ∧ ∃ l ∈ u k, l.1 = a := by
    simp only [segment_true, substituteVars_map_inl, List.mem_flatMap, hmem]
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

/-- A solution of a generalised equation is a solution of the system `Ω*` in `F(A)`. -/
theorem point_mem_V : U.point ∈ V (MonoidHom.id (FreeGroup A)) Ω.toSystem := by
  refine Ω.mem_V_toSystem_iff.2 fun e he => ?_
  have h (w : List ((Fin Ω.numItems ⊕ A) × Bool)) :
      FreeGroup.lift (Sum.elim U.point (MonoidHom.id (FreeGroup A) ∘ FreeGroup.of))
        (FreeGroup.mk w) = FreeGroup.mk (substituteVars U.word w) := by
    have hU : Sum.elim U.point FreeGroup.of =
        Sum.elim (fun k => FreeGroup.mk (U.word k)) FreeGroup.of := by
      funext y
      cases y <;> simp
    rw [mk_substituteVars, MonoidHom.coe_id, Function.id_comp, hU]
  rw [h, h, U.subst_eq e he]

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

/-- The substituted word `h[i, j] ^ ±1` spans the words of a solution from boundary `i` to
boundary `j`. -/
theorem length_substituteVars_segment_add_prefixLength (s : Bool) {i j : ℕ} (hij : i ≤ j) :
    (substituteVars U.word (Ω.segment i j s)).length + U.prefixLength i = U.prefixLength j := by
  rw [U.length_substituteVars_segment, prefixLength, prefixLength]
  conv_rhs => rw [← List.take_append_drop i (List.take j (List.finRange Ω.numItems))]
  rw [List.map_append, List.sum_append, List.take_take, min_eq_left hij, add_comm]

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
    (hd : d ≤ Ω.numItems) (hac : a ≤ c) (hcb : c < b)
    (hred : FreeGroup.IsReduced (substituteVars U.word (Ω.segment a b true)))
    (heq : substituteVars U.word (Ω.segment a b true) =
      FreeGroup.invRev (substituteVars U.word (Ω.segment c d true))) : False := by
  have hlen := congrArg List.length heq
  rw [FreeGroup.invRev_length] at hlen
  have h₁ := U.length_substituteVars_segment_add_prefixLength true hab.le
  have h₂ := U.length_substituteVars_segment_add_prefixLength true hcd.le
  rcases le_or_gt b d with hbd | hdb
  · -- The overlap `h[c, b]` is a nonempty reduced word equal to its formal inverse.
    rw [← Ω.segment_append hac hcb.le hb, ← Ω.segment_append hcb.le hbd hd,
      substituteVars_append, substituteVars_append, FreeGroup.invRev_append] at heq
    have hX := U.length_substituteVars_segment_add_prefixLength true hac
    have hZ := U.length_substituteVars_segment_add_prefixLength true hbd
    have hC := U.length_substituteVars_segment_add_prefixLength true hcb.le
    have hXZ : (substituteVars U.word (Ω.segment a c true)).length =
        (FreeGroup.invRev (substituteVars U.word (Ω.segment b d true))).length := by
      rw [FreeGroup.invRev_length]
      omega
    have hCC := (List.append_inj heq hXZ).2
    have hCred : FreeGroup.IsReduced (substituteVars U.word (Ω.segment c b true)) := by
      refine hred.infix ⟨substituteVars U.word (Ω.segment a c true), [], ?_⟩
      rw [List.append_nil, ← substituteVars_append, Ω.segment_append hac hcb.le hb]
    have hCne : substituteVars U.word (Ω.segment c b true) ≠ [] := by
      have := U.prefixLength_lt hcb hb
      intro h
      rw [h, List.length_nil] at hC
      omega
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
  · exact U.not_overlap hx' (Ω.right x).is_le hy' (Ω.right (Ω.dual x)).is_le h hne.1 rx ex
  · refine U.not_overlap hy' (Ω.right (Ω.dual x)).is_le hx' (Ω.right x).is_le h hne.2 ry ?_
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

include U in
private theorem label_eq (b : Fin Ω.numItems × (A × Bool)) (hb : b ∈ Ω.constBases)
    (b' : Fin Ω.numItems × (A × Bool)) (hb' : b' ∈ Ω.constBases) (hk : b.1 = b'.1) :
    b.2 = b'.2 := by
  have e := U.subst_eq _ (Ω.coeffEquation_mem_equations hb)
  have e' := U.subst_eq _ (Ω.coeffEquation_mem_equations hb')
  simp only [coeffEquation_fst, coeffEquation_snd, substituteVars_singleton_inl,
    substituteVars_singleton_inr] at e e'
  rw [hk, e'] at e
  simp only [List.cons.injEq, and_true] at e
  exact e.symm

/-- The item of a constant base carries a one-letter word, so the prefix length grows by one
across it. -/
theorem prefixLength_succ_of_mem_constBases {b : Fin Ω.numItems × (A × Bool)}
    (hb : b ∈ Ω.constBases) : U.prefixLength (b.1 + 1) = U.prefixLength b.1 + 1 := by
  have hone : (U.word b.1).length = 1 := by
    have e := U.subst_eq _ (Ω.coeffEquation_mem_equations hb)
    simp only [coeffEquation_fst, coeffEquation_snd, substituteVars_singleton_inl,
      substituteVars_singleton_inr] at e
    simp [e]
  have := U.length_substituteVars_segment_add_prefixLength true (Nat.le_add_right b.1 1)
  rw [segment_succ, substituteVars_singleton_inl, hone] at this
  omega

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
  have hsucc := U.prefixLength_succ_of_mem_constBases hb
  have e := U.prefixLength_boundary hc
  have e' := U.prefixLength_boundary hc'
  simp only [Fin.val_castSucc, Fin.val_succ] at e e'
  -- The prefix lengths at `q` and `q'` differ by one, which forces adjacent boundaries.
  split_ifs at e e'
  · have hlt : (q : ℕ) < q' := by
      by_contra h
      have := U.prefixLength_mono (not_lt.1 h)
      omega
    have := U.prefixLength_add_le hlt.le q'.is_le
    omega
  · have hlt : (q' : ℕ) < q := by
      by_contra h
      have := U.prefixLength_mono (not_lt.1 h)
      omega
    have := U.prefixLength_add_le hlt.le q.is_le
    omega

include U in
/-- **Kharlampovich–Myasnikov, Lemma 12(1).** A generalised equation with a solution is formally
consistent. -/
theorem isFormallyConsistent : Ω.IsFormallyConsistent :=
  ⟨U.disjoint_of_sign_ne, U.connections_monotone_or_antitone, U.eq_of_left_eq, U.label_eq,
    U.connections_adjacent⟩

end Solution

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
