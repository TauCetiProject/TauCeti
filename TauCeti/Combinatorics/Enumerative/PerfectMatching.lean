/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import TauCeti.GroupTheory.Perm.OrbitCount.Basic

/-!
# Perfect matchings of a finite type

A **perfect matching** of a type `α` is a permutation of `α` that is an involution without
fixed points; equivalently, it partitions `α` into the unordered pairs `{a, f a}`. This file
defines perfect matchings, transports them along an equivalence of the underlying types,
reconnects two of their arcs, shows that a perfect matching restricted to the complement of one
of its arcs is again a perfect matching, and counts the perfect matchings of a finite type: a
type of cardinality `2 * m` has `(2 * m - 1)‼` of them, and a type of odd cardinality has none.
Finally it records the parity consequences of being a product of `m` disjoint transpositions: the
sign of a perfect matching, and the evenness of the number of orbits of a product of two perfect
matchings.

The counting theorem is the combinatorial content behind the dimension of the Brauer algebra;
see `TauCeti/Combinatorics/Brauer/Diagram.lean`.

## Main definitions

* `TauCeti.IsPerfectMatching f`: the permutation `f` is an involution with no fixed point.
* `TauCeti.PerfectMatching α`: the type of perfect matchings of `α`.
* `TauCeti.PerfectMatching.congr`: transporting a perfect matching along an equivalence.
* `TauCeti.PerfectMatching.reconnect`: cutting two arcs and joining their ends the other way.
* `TauCeti.PerfectMatching.restrict`: the perfect matching induced on the complement of an arc.
* `TauCeti.PerfectMatching.extend`: the perfect matching obtained by adjoining an arc.
* `TauCeti.PerfectMatching.fiberEquiv`: the two constructions above are mutually inverse.

## Main results

* `TauCeti.even_card_of_nonempty_perfectMatching`: a matched type has even cardinality.
* `TauCeti.card_perfectMatching`: a type of cardinality `2 * m` has `(2 * m - 1)‼` perfect
  matchings.
* `TauCeti.IsPerfectMatching.sign_eq`: a perfect matching of a type of cardinality `2 * m` has
  sign `(-1) ^ m`.
* `TauCeti.IsPerfectMatching.two_mul_orbitCount`: a perfect matching has half as many orbits as
  points.
* `TauCeti.IsPerfectMatching.even_orbitCount_mul`: the product of two perfect matchings has an even
  number of orbits.

## References

* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 9.
-/

public section

open scoped Nat

namespace TauCeti

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-- A permutation of `α` is a **perfect matching** when it is an involution with no fixed
point, so that it pairs off the elements of `α`. -/
def IsPerfectMatching (f : Equiv.Perm α) : Prop :=
  (∀ a, f (f a) = a) ∧ ∀ a, f a ≠ a

/-- A permutation is a perfect matching exactly when it is an involution with no fixed
point. -/
theorem isPerfectMatching_iff {f : Equiv.Perm α} :
    IsPerfectMatching f ↔ (∀ a, f (f a) = a) ∧ ∀ a, f a ≠ a := Iff.rfl

/-- A perfect matching is an involution. -/
@[simp]
theorem IsPerfectMatching.apply_apply {f : Equiv.Perm α} (hf : IsPerfectMatching f) (a : α) :
    f (f a) = a :=
  hf.1 a

/-- A perfect matching moves every point. -/
@[simp]
theorem IsPerfectMatching.apply_ne {f : Equiv.Perm α} (hf : IsPerfectMatching f) (a : α) :
    f a ≠ a :=
  hf.2 a

instance instDecidableIsPerfectMatching [DecidableEq α] [Fintype α] (f : Equiv.Perm α) :
    Decidable (IsPerfectMatching f) :=
  inferInstanceAs (Decidable ((∀ a, f (f a) = a) ∧ ∀ a, f a ≠ a))

/-- The type of perfect matchings of `α`, a subtype of `Equiv.Perm α` so that the finiteness
and decidability instances of permutations carry over unchanged. -/
@[expose]
def PerfectMatching (α : Type u) : Type _ := {f : Equiv.Perm α // IsPerfectMatching f}

namespace PerfectMatching

instance [DecidableEq α] [Fintype α] : Fintype (PerfectMatching α) :=
  inferInstanceAs (Fintype {f : Equiv.Perm α // IsPerfectMatching f})

instance [DecidableEq α] [Fintype α] : DecidableEq (PerfectMatching α) :=
  inferInstanceAs (DecidableEq {f : Equiv.Perm α // IsPerfectMatching f})

/-- Bundle a permutation that is an involution with no fixed point as a perfect matching. -/
def mk (f : Equiv.Perm α) (hinv : ∀ a, f (f a) = a) (hne : ∀ a, f a ≠ a) : PerfectMatching α :=
  ⟨f, hinv, hne⟩

@[simp]
theorem val_mk (f : Equiv.Perm α) (hinv : ∀ a, f (f a) = a) (hne : ∀ a, f a ≠ a) :
    (mk f hinv hne).val = f := (rfl)

variable {a b : α} {D : PerfectMatching α}

/-- A perfect matching is an involution. -/
@[simp]
theorem apply_apply (D : PerfectMatching α) (x : α) : D.val (D.val x) = x := D.prop.1 x

/-- A perfect matching moves every point. -/
@[simp]
theorem apply_ne (D : PerfectMatching α) (x : α) : D.val x ≠ x := D.prop.2 x

/-- The two ends of an arc determine each other. -/
theorem apply_eq_of_apply_eq (D : PerfectMatching α) {x y : α} (h : D.val x = y) :
    D.val y = x := by rw [← h, D.apply_apply]

/-- A perfect matching that joins `a` to `b` preserves the complement of `{a, b}`. -/
theorem apply_ne_and_ne_iff (hab : D.val a = b) (x : α) :
    (D.val x ≠ a ∧ D.val x ≠ b) ↔ (x ≠ a ∧ x ≠ b) := by
  have hba : D.val b = a := D.apply_eq_of_apply_eq hab
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun h => h₂ (h ▸ hab), fun h => h₁ (h ▸ hba)⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun h => h₂ ?_, fun h => h₁ ?_⟩
    · rw [← hab, ← D.apply_eq_of_apply_eq h]
    · rw [← hba, ← D.apply_eq_of_apply_eq h]

/-- The perfect matching induced on the complement of the arc joining `a` to `b`. -/
def restrict (D : PerfectMatching α) (hab : D.val a = b) :
    PerfectMatching {x : α // x ≠ a ∧ x ≠ b} :=
  ⟨D.val.subtypePerm (apply_ne_and_ne_iff hab), fun x => Subtype.ext (D.apply_apply x.val),
    fun x h => D.apply_ne x.val (congrArg Subtype.val h)⟩

@[simp]
theorem restrict_apply_coe (D : PerfectMatching α) (hab : D.val a = b)
    (x : {x : α // x ≠ a ∧ x ≠ b}) : ((D.restrict hab).val x : α) = D.val x := (rfl)

section Extend

variable [DecidableEq α]

/-- The permutation of `α` that acts as `E` away from `{a, b}` and swaps `a` with `b`; it
underlies `PerfectMatching.extend`. -/
private def extendPerm (E : PerfectMatching {x : α // x ≠ a ∧ x ≠ b}) : Equiv.Perm α :=
  Equiv.swap a b * Equiv.Perm.ofSubtype E.val

/-- Away from `{a, b}`, the extended permutation acts through `E`. -/
private theorem extendPerm_apply_of_mem (E : PerfectMatching {x : α // x ≠ a ∧ x ≠ b}) {x : α}
    (hx : x ≠ a ∧ x ≠ b) : extendPerm E x = (E.val ⟨x, hx⟩ : α) := by
  have hmem : Equiv.Perm.ofSubtype E.val x = (E.val ⟨x, hx⟩ : α) :=
    Equiv.Perm.ofSubtype_apply_of_mem E.val hx
  have hne := (E.val ⟨x, hx⟩).2
  rw [extendPerm, Equiv.Perm.mul_apply, hmem, Equiv.swap_apply_of_ne_of_ne hne.1 hne.2]

/-- The extended permutation sends `a` to `b`. -/
private theorem extendPerm_apply_left (E : PerfectMatching {x : α // x ≠ a ∧ x ≠ b}) :
    extendPerm E a = b := by
  rw [extendPerm, Equiv.Perm.mul_apply,
    Equiv.Perm.ofSubtype_apply_of_not_mem E.val (by simp), Equiv.swap_apply_left]

/-- The extended permutation sends `b` to `a`. -/
private theorem extendPerm_apply_right (E : PerfectMatching {x : α // x ≠ a ∧ x ≠ b}) :
    extendPerm E b = a := by
  rw [extendPerm, Equiv.Perm.mul_apply,
    Equiv.Perm.ofSubtype_apply_of_not_mem E.val (by simp), Equiv.swap_apply_right]

/-- The perfect matching of `α` obtained from a perfect matching of the complement of
`{a, b}` by adjoining the arc joining `a` to `b`. -/
def extend (hab : a ≠ b) (E : PerfectMatching {x : α // x ≠ a ∧ x ≠ b}) : PerfectMatching α := by
  refine ⟨extendPerm E, fun x => ?_, fun x => ?_⟩
  · by_cases hx : x ≠ a ∧ x ≠ b
    · rw [extendPerm_apply_of_mem E hx, extendPerm_apply_of_mem E (E.val ⟨x, hx⟩).2]
      exact congrArg Subtype.val (E.apply_apply ⟨x, hx⟩)
    · rcases not_and_or.mp hx with hx | hx
      · rw [not_ne_iff.mp hx, extendPerm_apply_left, extendPerm_apply_right]
      · rw [not_ne_iff.mp hx, extendPerm_apply_right, extendPerm_apply_left]
  · by_cases hx : x ≠ a ∧ x ≠ b
    · rw [extendPerm_apply_of_mem E hx]
      exact fun h => E.apply_ne ⟨x, hx⟩ (Subtype.ext h)
    · rcases not_and_or.mp hx with hx | hx
      · rw [not_ne_iff.mp hx, extendPerm_apply_left]; exact hab.symm
      · rw [not_ne_iff.mp hx, extendPerm_apply_right]; exact hab

/-- Away from `{a, b}`, the extended matching acts through `E`. -/
theorem extend_apply_of_mem (hab : a ≠ b) (E : PerfectMatching {x : α // x ≠ a ∧ x ≠ b}) {x : α}
    (hx : x ≠ a ∧ x ≠ b) : (extend hab E).val x = (E.val ⟨x, hx⟩ : α) :=
  extendPerm_apply_of_mem E hx

/-- Adjoining the arc `{a, b}` sends `a` to `b`. -/
@[simp]
theorem extend_apply_left (hab : a ≠ b) (E : PerfectMatching {x : α // x ≠ a ∧ x ≠ b}) :
    (extend hab E).val a = b := extendPerm_apply_left E

/-- Adjoining the arc `{a, b}` sends `b` to `a`. -/
@[simp]
theorem extend_apply_right (hab : a ≠ b) (E : PerfectMatching {x : α // x ≠ a ∧ x ≠ b}) :
    (extend hab E).val b = a := extendPerm_apply_right E

/-- Adjoining an arc and then restricting it away recovers the smaller matching. -/
@[simp]
theorem restrict_extend (hab : a ≠ b) (E : PerfectMatching {x : α // x ≠ a ∧ x ≠ b}) :
    (extend hab E).restrict (extend_apply_left hab E) = E := by
  refine Subtype.ext (Equiv.ext fun x => Subtype.ext ?_)
  rw [restrict_apply_coe, extend_apply_of_mem hab E x.2]

/-- Restricting away an arc and then adjoining it back recovers the original matching. -/
@[simp]
theorem extend_restrict (hab : a ≠ b) (D : PerfectMatching α) (h : D.val a = b) :
    extend hab (D.restrict h) = D := by
  refine Subtype.ext (Equiv.ext fun x => ?_)
  by_cases hx : x ≠ a ∧ x ≠ b
  · rw [extend_apply_of_mem hab _ hx, restrict_apply_coe]
  · rcases not_and_or.mp hx with hx | hx
    · rw [not_ne_iff.mp hx, extend_apply_left]; exact h.symm
    · rw [not_ne_iff.mp hx, extend_apply_right]
      exact (D.apply_eq_of_apply_eq h).symm

/-- Restricting away an arc and adjoining it back are mutually inverse: the perfect matchings
of `α` joining `a` to `b` are the perfect matchings of the complement of `{a, b}`. -/
def fiberEquiv (hab : a ≠ b) :
    {D : PerfectMatching α // D.val a = b} ≃ PerfectMatching {x : α // x ≠ a ∧ x ≠ b} where
  toFun D := D.1.restrict D.2
  invFun E := ⟨extend hab E, extend_apply_left hab E⟩
  left_inv D := Subtype.ext (extend_restrict hab D.1 D.2)
  right_inv E := restrict_extend hab E

/-- The fiber equivalence restricts away the arc joining `a` to `b`. -/
@[simp]
theorem fiberEquiv_apply (hab : a ≠ b) (D : {D : PerfectMatching α // D.val a = b}) :
    fiberEquiv hab D = D.1.restrict D.2 := (rfl)

/-- The inverse of the fiber equivalence adjoins the arc joining `a` to `b`. -/
@[simp]
theorem fiberEquiv_symm_apply (hab : a ≠ b) (E : PerfectMatching {x : α // x ≠ a ∧ x ≠ b}) :
    ((fiberEquiv hab).symm E : PerfectMatching α) = extend hab E := (rfl)

end Extend

section Congr

/-- Transporting an involution without fixed points along an equivalence leaves it an involution
without fixed points. -/
theorem isPerfectMatching_permCongr (e : α ≃ β) {f : Equiv.Perm α} (hf : IsPerfectMatching f) :
    IsPerfectMatching (e.permCongr f) := by
  refine ⟨fun b => by simp [hf.1], fun b hb => hf.2 (e.symm b) ?_⟩
  simpa using congrArg e.symm hb

/-- A permutation is a perfect matching exactly when its transport along an equivalence is. -/
theorem isPerfectMatching_permCongr_iff (e : α ≃ β) {f : Equiv.Perm α} :
    IsPerfectMatching (e.permCongr f) ↔ IsPerfectMatching f := by
  refine ⟨fun h => ?_, isPerfectMatching_permCongr e⟩
  have hf : e.symm.permCongr (e.permCongr f) = f := by
    rw [← Equiv.permCongr_symm, Equiv.symm_apply_apply]
  exact hf ▸ isPerfectMatching_permCongr e.symm h

/-- **Transporting a perfect matching along an equivalence** of the underlying types: the arc
joining `a` to `b` becomes the arc joining `e a` to `e b`. -/
def congr (e : α ≃ β) : PerfectMatching α ≃ PerfectMatching β :=
  e.permCongr.subtypeEquiv fun _ => (isPerfectMatching_permCongr_iff e).symm

/-- The involution underlying a transported matching is the transported involution. -/
@[simp]
theorem congr_val (e : α ≃ β) (D : PerfectMatching α) :
    (congr e D).val = e.permCongr D.val := (rfl)

/-- The transported matching matches `b` with the image of the partner of `e.symm b`. -/
theorem congr_val_apply (e : α ≃ β) (D : PerfectMatching α) (b : β) :
    (congr e D).val b = e (D.val (e.symm b)) := (rfl)

/-- The transported matching matches `e a` with the image of the partner of `a`. -/
theorem congr_val_apply_apply (e : α ≃ β) (D : PerfectMatching α) (a : α) :
    (congr e D).val (e a) = e (D.val a) := by
  rw [congr_val_apply, Equiv.symm_apply_apply]

/-- Transporting along the identity equivalence changes nothing. -/
@[simp]
theorem congr_refl (D : PerfectMatching α) : congr (Equiv.refl α) D = D :=
  Subtype.ext <| Equiv.ext fun a => by
    rw [congr_val_apply, Equiv.refl_symm, Equiv.refl_apply, Equiv.refl_apply]

/-- **Transports compose**: transporting along `e` and then along `e'` is transporting along
`e.trans e'`, both matchings sending `c` to `e' (e (D.val (e.symm (e'.symm c))))`. -/
@[simp]
theorem congr_trans (e : α ≃ β) (e' : β ≃ γ) (D : PerfectMatching α) :
    congr e' (congr e D) = congr (e.trans e') D :=
  Subtype.ext <| Equiv.ext fun c => by
    rw [congr_val_apply, congr_val_apply, congr_val_apply, Equiv.symm_trans_apply,
      Equiv.trans_apply]

/-- Transporting back along `e` is transporting along `e.symm`, since transports compose. -/
@[simp]
theorem congr_symm (e : α ≃ β) : (congr e).symm = congr e.symm :=
  Equiv.ext fun D => by
    rw [Equiv.symm_apply_eq, congr_trans, Equiv.symm_trans_self, congr_refl]

end Congr

section Reconnect

variable [DecidableEq α]

/-- **Reconnecting two arcs.** Cut the arc of `D` at `a` and the arc at `b`, and join `a` to `b`
and `D.val a` to `D.val b`; every other arc is kept. It is `D` transported along the
transposition of `D.val a` with `b`. The arcs at `a` and `b` are distinct when `b ≠ a` and
`b ≠ D.val a`; when `b = D.val a` the transposition is trivial and the result is `D` itself. -/
def reconnect (D : PerfectMatching α) (a b : α) : PerfectMatching α :=
  congr (Equiv.swap (D.val a) b) D

/-- The involution underlying a reconnected matching is the old one conjugated by the
transposition of `D.val a` with `b`. -/
theorem reconnect_val (D : PerfectMatching α) (a b : α) :
    (D.reconnect a b).val = (Equiv.swap (D.val a) b).permCongr D.val :=
  congr_val _ _

/-- Reconnecting the two ends of one arc leaves the matching unchanged. -/
@[simp]
theorem reconnect_partner (D : PerfectMatching α) (a : α) :
    D.reconnect a (D.val a) = D := by
  rw [reconnect, Equiv.swap_self, congr_refl]

variable (hba : b ≠ a)
include hba

/-- After reconnecting, `a` is joined to `b`. -/
@[simp]
theorem reconnect_val_self : (D.reconnect a b).val a = b := by
  rw [reconnect_val, Equiv.permCongr_apply, Equiv.symm_swap,
    Equiv.swap_apply_of_ne_of_ne (D.apply_ne a).symm hba.symm, Equiv.swap_apply_left]

/-- After reconnecting, `b` is joined to `a`. -/
@[simp]
theorem reconnect_val_right : (D.reconnect a b).val b = a := by
  rw [reconnect_val, Equiv.permCongr_apply, Equiv.symm_swap, Equiv.swap_apply_right,
    D.apply_apply, Equiv.swap_apply_of_ne_of_ne (D.apply_ne a).symm hba.symm]

/-- After reconnecting, the other end `D.val a` of the first arc is joined to the other end
`D.val b` of the second. -/
@[simp]
theorem reconnect_val_val_self : (D.reconnect a b).val (D.val a) = D.val b := by
  have h : D.val b ≠ D.val a := fun h => hba (D.val.injective h)
  rw [reconnect_val, Equiv.permCongr_apply, Equiv.symm_swap, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne h (D.apply_ne b)]

/-- After reconnecting, the other end `D.val b` of the second arc is joined to the other end
`D.val a` of the first. -/
@[simp]
theorem reconnect_val_val_right : (D.reconnect a b).val (D.val b) = D.val a := by
  have h : D.val b ≠ D.val a := fun h => hba (D.val.injective h)
  rw [reconnect_val, Equiv.permCongr_apply, Equiv.symm_swap,
    Equiv.swap_apply_of_ne_of_ne h (D.apply_ne b), D.apply_apply, Equiv.swap_apply_right]

omit hba in
/-- Reconnecting keeps every arc that does not end at `a` or `b`. -/
@[simp]
theorem reconnect_val_of_ne {x : α} (hxa : x ≠ a) (hxb : x ≠ b) (hxa' : x ≠ D.val a)
    (hxb' : x ≠ D.val b) : (D.reconnect a b).val x = D.val x := by
  have h₁ : D.val x ≠ D.val a := fun h => hxa (D.val.injective h)
  have h₂ : D.val x ≠ b := fun h => hxb' (by rw [← h, D.apply_apply])
  rw [reconnect_val, Equiv.permCongr_apply, Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hxa' hxb,
    Equiv.swap_apply_of_ne_of_ne h₁ h₂]

omit hba in
/-- Reconnecting an endpoint with itself leaves the matching unchanged. -/
@[simp]
theorem reconnect_self (D : PerfectMatching α) (a : α) : D.reconnect a a = D := by
  refine Subtype.ext (Equiv.ext fun x => ?_)
  by_cases hxa : x = a
  · subst x
    simp [reconnect_val]
  by_cases hxa' : x = D.val a
  · subst x
    simp [reconnect_val]
  exact reconnect_val_of_ne hxa hxa hxa' hxa'

end Reconnect

end PerfectMatching

/-- Deleting two distinct points from a finite type drops its cardinality by two. -/
private theorem card_subtype_ne_ne {α : Type u} [Fintype α] [DecidableEq α] {a b : α}
    (hab : a ≠ b) : Fintype.card {x : α // x ≠ a ∧ x ≠ b} = Fintype.card α - 2 := by
  have hcompl : Fintype.card {x : α // x ≠ a ∧ x ≠ b}
      = Fintype.card {x : α // ¬(x = a ∨ x = b)} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun _ => not_or.symm)
  rw [hcompl, Fintype.card_subtype_compl, Fintype.card_subtype_eq_or_eq_of_ne hab]

private theorem even_card_aux :
    ∀ (n : ℕ) {α : Type u} [Fintype α], Fintype.card α = n →
      Nonempty (PerfectMatching α) → Even n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro α _ hcard hne
    classical
    obtain ⟨D⟩ := hne
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, rfl⟩
    obtain ⟨a⟩ := (Fintype.card_pos_iff (α := α)).mp (by omega)
    have hab : a ≠ D.val a := (D.apply_ne a).symm
    have hlt : 1 < Fintype.card α := Fintype.one_lt_card_iff_nontrivial.mpr ⟨a, D.val a, hab⟩
    have hsub : Fintype.card {x : α // x ≠ a ∧ x ≠ D.val a} = n - 2 := by
      rw [card_subtype_ne_ne hab, hcard]
    obtain ⟨r, hr⟩ := ih (n - 2) (by omega) hsub ⟨D.restrict rfl⟩
    exact ⟨r + 1, by omega⟩

/-- A type carrying a perfect matching has even cardinality: the arcs pair its elements. -/
theorem even_card_of_nonempty_perfectMatching (α : Type u) [Fintype α]
    (h : Nonempty (PerfectMatching α)) : Even (Fintype.card α) :=
  even_card_aux _ rfl h

/-- A type of odd cardinality carries no perfect matching. -/
theorem isEmpty_perfectMatching_of_not_even {α : Type u} [Fintype α]
    (h : ¬Even (Fintype.card α)) : IsEmpty (PerfectMatching α) :=
  ⟨fun D => h (even_card_of_nonempty_perfectMatching α ⟨D⟩)⟩

/-- An empty type has exactly one perfect matching, the empty one. -/
private theorem card_perfectMatching_of_isEmpty (α : Type u) [Fintype α] [DecidableEq α]
    [IsEmpty α] :
    Fintype.card (PerfectMatching α) = 1 := by
  have : Subsingleton (PerfectMatching α) :=
    ⟨fun D E => Subtype.ext (Equiv.ext fun x => isEmptyElim x)⟩
  have : Unique (PerfectMatching α) :=
    uniqueOfSubsingleton ⟨1, fun a => isEmptyElim a, fun a => isEmptyElim a⟩
  exact Fintype.card_unique

/-- There are as many perfect matchings pairing a fixed `a` with a fixed `b ≠ a` as there are
perfect matchings of the complement of `{a, b}`. -/
private theorem card_filter_val_eq_card_perfectMatching_compl {α : Type u} [Fintype α]
    [DecidableEq α] {a b : α} (hba : b ≠ a) :
    (Finset.univ.filter fun D : PerfectMatching α => D.val a = b).card
      = Fintype.card (PerfectMatching {x : α // x ≠ a ∧ x ≠ b}) :=
  (Fintype.card_subtype _).symm.trans
    (Fintype.card_congr (PerfectMatching.fiberEquiv hba.symm))

/-- If every `2 * m`-element type has `(2 * m - 1)‼` perfect matchings, then every
`2 * (m + 1)`-element type has `(2 * (m + 1) - 1)‼` of them. -/
private theorem card_perfectMatching_succ {m : ℕ} (α : Type u) [Fintype α] [DecidableEq α]
    (hcard : Fintype.card α = 2 * (m + 1))
    (ih : ∀ (β : Type u) [Fintype β] [DecidableEq β], Fintype.card β = 2 * m →
      Fintype.card (PerfectMatching β) = (2 * m - 1)‼) :
    Fintype.card (PerfectMatching α) = (2 * (m + 1) - 1)‼ := by
  obtain ⟨a⟩ := (Fintype.card_pos_iff (α := α)).mp (by omega)
  have key : ∀ b ∈ Finset.univ.erase a,
      (Finset.univ.filter fun D : PerfectMatching α => D.val a = b).card = (2 * m - 1)‼ := by
    intro b hb
    have hba : b ≠ a := (Finset.mem_erase.mp hb).1
    rw [card_filter_val_eq_card_perfectMatching_compl hba]
    refine ih _ ?_
    rw [card_subtype_ne_ne hba.symm, hcard]
    omega
  have hmem : ∀ D ∈ (Finset.univ : Finset (PerfectMatching α)),
      D.val a ∈ Finset.univ.erase a :=
    fun D _ => Finset.mem_erase.mpr ⟨D.apply_ne a, Finset.mem_univ _⟩
  have hodd : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  have herase : (Finset.univ.erase a).card = 2 * m + 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcard]
    omega
  calc Fintype.card (PerfectMatching α)
      = (Finset.univ : Finset (PerfectMatching α)).card := Finset.card_univ.symm
    _ = ∑ b ∈ Finset.univ.erase a,
          (Finset.univ.filter fun D : PerfectMatching α => D.val a = b).card :=
        Finset.card_eq_sum_card_fiberwise hmem
    _ = (Finset.univ.erase a).card * (2 * m - 1)‼ := Finset.sum_const_nat key
    _ = (2 * m + 1) * (2 * m - 1)‼ := by rw [herase]
    _ = (2 * m + 1)‼ := (Nat.doubleFactorial_add_one (2 * m)).symm
    _ = (2 * (m + 1) - 1)‼ := by rw [hodd]

private theorem card_perfectMatching_aux :
    ∀ (m : ℕ) {α : Type u} [Fintype α] [DecidableEq α], Fintype.card α = 2 * m →
      Fintype.card (PerfectMatching α) = (2 * m - 1)‼ := by
  intro m
  induction m with
  | zero =>
    intro α _ _ hcard
    have : IsEmpty α := Fintype.card_eq_zero_iff.mp (by omega)
    rw [card_perfectMatching_of_isEmpty α]
    rfl
  | succ m ih =>
    intro α _ _ hcard
    exact card_perfectMatching_succ α hcard fun β _ _ h => ih h

/-- **The number of perfect matchings of a finite type.** A type with `2 * m` elements has
exactly `(2 * m - 1)‼ = 1 · 3 · 5 ⋯ (2 * m - 1)` perfect matchings. -/
theorem card_perfectMatching (α : Type u) [Fintype α] [DecidableEq α] {m : ℕ}
    (hcard : Fintype.card α = 2 * m) : Fintype.card (PerfectMatching α) = (2 * m - 1)‼ :=
  card_perfectMatching_aux m hcard

section Parity

/-- **The sign of a perfect matching.** A perfect matching of a finite type is a product of half
as many disjoint transpositions as the type has elements. -/
theorem IsPerfectMatching.sign_eq [Fintype α] [DecidableEq α] {f : Equiv.Perm α}
    (hf : IsPerfectMatching f) :
    Equiv.Perm.sign f = (-1 : ℤˣ) ^ (Fintype.card α / 2) := by
  have hsq : f ^ 2 = 1 := Equiv.ext fun a => by simp [sq, hf.1 a]
  have hfix : Fintype.card (Function.fixedPoints f) = 0 :=
    Fintype.card_eq_zero_iff.mpr ⟨fun a => hf.2 a a.2⟩
  rw [Equiv.Perm.sign_of_pow_two_eq_one hsq, hfix, Nat.sub_zero]

/-- **A product of two perfect matchings has an even number of orbits.** Both factors have the
same sign, so the product is even, while the type has even cardinality; the sign of a permutation
is the parity of the number of points minus the number of orbits. -/
theorem IsPerfectMatching.even_orbitCount_mul [Finite α] {f g : Equiv.Perm α}
    (hf : IsPerfectMatching f) (hg : IsPerfectMatching g) : Even (orbitCount (f * g)) := by
  classical
  have := Fintype.ofFinite α
  have hs := Equiv.Perm.sign_eq_neg_one_pow_card_sub_orbitCount (f * g)
  rw [map_mul, hf.sign_eq, hg.sign_eq, ← pow_add, ← two_mul, pow_mul, Int.units_sq, one_pow,
    Int.units_pow_eq_pow_mod_two] at hs
  have hle := (f * g).orbitCount_le_card.trans_eq Nat.card_eq_fintype_card
  obtain ⟨m, hm⟩ := even_card_of_nonempty_perfectMatching α ⟨⟨f, hf⟩⟩
  by_contra hodd
  obtain ⟨j, hj⟩ := Nat.not_even_iff_odd.mp hodd
  have hparity : (Fintype.card α - orbitCount (f * g)) % 2 = 1 := by omega
  rw [hparity, pow_one] at hs
  exact absurd hs (by decide)

/-- **A perfect matching has half as many orbits as points**: its orbits are its pairs. -/
theorem IsPerfectMatching.two_mul_orbitCount [Finite α] {f : Equiv.Perm α}
    (hf : IsPerfectMatching f) : 2 * orbitCount f = Nat.card α := by
  classical
  have := Fintype.ofFinite α
  have hsupp : f.support = Finset.univ :=
    Finset.eq_univ_of_forall fun a => Equiv.Perm.mem_support.mpr (hf.2 a)
  have hsq : f ^ 2 = 1 := Equiv.ext fun a => by simp [sq, hf.1 a]
  -- Every orbit of `f` is a pair: `f` has no fixed points, and its cycles have length `2`.
  have hpair : ∀ k ∈ f.partition.parts, k = 2 := fun k hk => by
    rw [Equiv.Perm.parts_partition, Equiv.Perm.cycleType_of_pow_prime_eq_one hsq] at hk
    exact Multiset.eq_of_mem_replicate (by simpa [hsupp] using hk)
  rw [f.orbitCount_eq_card_parts_partition, Nat.card_eq_fintype_card]
  refine .trans ?_ f.partition.parts_sum
  rw [Multiset.eq_replicate_of_mem hpair]
  simp [mul_comm]

end Parity

end TauCeti
