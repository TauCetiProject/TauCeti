/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Symmetric
public import Mathlib.Data.Fintype.EquivFin

/-!
# Indexed quiver paths, concatenation, and reversal

`TauCeti.Quiver.TotalPath Q` records a path of a quiver together with its source and target. Two
such paths can be concatenated when the target of the second is the source of the first. The
partial operation `TauCeti.Quiver.TotalPath.mul?` records this condition with an `Option` result,
using the later-factor-first order: `x.mul? y` traces `y` and then `x`.

Concatenation adds path lengths and keeps the source of the factor written second — the one traced
first — so it is the trivial path at a vertex exactly when both its factors are. It is associative
as a partial operation, and trivial paths are left and right units at the appropriate endpoints.
These operations supply the path index and multiplication of the path algebra, independently of any
coefficient semiring.

When the quiver has arrow reversal, indexed paths can also be reversed, exchanging their source and
target and reversing the order of partial concatenation. Involutive arrow reversal makes path
reversal involutive.

## Main definitions

* `TauCeti.Quiver.TotalPath`: the total space `Σ a b, Quiver.Path a b` of paths.
* `TauCeti.Quiver.TotalPath.mul?`: concatenation when the paths meet, and `none` otherwise.
* `TauCeti.Quiver.TotalPath.reverse`: reversal of an indexed path, including its endpoints.

## Main results

* `TauCeti.Quiver.finite_of_finite_totalPath`: a quiver with finitely many indexed paths has
  finitely many vertices.
* `TauCeti.Quiver.TotalPath.eq_nil_iff`: a path is trivial at a vertex exactly when it starts
  there and has length zero.
* `TauCeti.Quiver.TotalPath.mul?_eq_none_iff`: concatenation is undefined exactly when the
  endpoints do not meet.
* `TauCeti.Quiver.TotalPath.length_eq_add_of_mul?_eq_some` and
  `TauCeti.Quiver.TotalPath.fst_of_mul?_eq_some`: concatenation adds lengths and keeps the source
  of the factor written second, which is traced first.
* `TauCeti.Quiver.TotalPath.eq_nil_iff_of_mul?_eq_some`: a concatenation is the trivial path at a
  vertex exactly when both its factors are.
* `TauCeti.Quiver.TotalPath.mul?_nil_left`, `TauCeti.Quiver.TotalPath.mul?_nil_right`, and
  `TauCeti.Quiver.TotalPath.mul?_assoc`: trivial-path units and associativity.
* `TauCeti.Quiver.TotalPath.map_reverse_mul?`: reversal reverses the order of partial concatenation.
* `TauCeti.Quiver.TotalPath.mk_cons_eq_mk_cons_iff`: a path into a vertex is determined by its
  last arrow and the path before it.

## References

Assem--Simson--Skowroński,
*Elements of the Representation Theory of Associative Algebras I*, Ch. II.
-/

public section

namespace TauCeti

open _root_.Quiver

universe u v

/-- The total space of the paths of a quiver: a path together with its source and target. This is
the index type of the path basis of the path algebra. -/
abbrev Quiver.TotalPath (Q : Type u) [Quiver.{v} Q] : Type _ :=
  Σ a b : Q, _root_.Quiver.Path a b

/-- A quiver with finitely many total paths has finitely many vertices. -/
instance Quiver.finite_of_finite_totalPath (Q : Type u) [Quiver.{v} Q]
    [Finite (Quiver.TotalPath Q)] : Finite Q :=
  Finite.of_injective (fun q : Q ↦ (⟨q, q, _root_.Quiver.Path.nil⟩ : Quiver.TotalPath Q))
    (fun _ _ h ↦ congrArg Sigma.fst h)

namespace Quiver.TotalPath

variable {Q : Type u} [Quiver.{v} Q]

/-- Reverse an indexed path and exchange its source and target. -/
def reverse [HasReverse Q] (x : TotalPath Q) : TotalPath Q :=
  ⟨x.2.1, x.1, x.2.2.reverse⟩

/-- Reversal of an explicitly indexed path reverses its underlying path. -/
@[simp]
theorem reverse_mk [HasReverse Q] {a b : Q} (p : Path a b) :
    reverse (⟨a, b, p⟩ : TotalPath Q) = ⟨b, a, p.reverse⟩ :=
  (rfl)

/-- Reversing an indexed path twice returns the original path. -/
@[simp]
theorem reverse_reverse [HasInvolutiveReverse Q] (x : TotalPath Q) :
    x.reverse.reverse = x := by
  obtain ⟨a, b, p⟩ := x
  simp

/-- An indexed path is the trivial path at `v` exactly when it starts at `v` and has length zero.
Stated this way the equality is checked against two non-dependent conditions, so recognizing a
trivial path inside a concatenation needs no transport along the endpoints. -/
@[simp]
theorem eq_nil_iff {v : Q} {x : TotalPath Q} :
    x = ⟨v, v, _root_.Quiver.Path.nil⟩ ↔ x.1 = v ∧ x.2.2.length = 0 := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · obtain ⟨a, b, p⟩ := x
    rintro ⟨rfl, hlen⟩
    obtain rfl : a = b := p.eq_of_length_zero hlen
    obtain rfl : p = _root_.Quiver.Path.nil := p.eq_nil_of_length_zero hlen
    rfl

open scoped Classical in
/-- Concatenation of indexed paths in the *later factor first* order used by the path algebra:
`x.mul? y` traces `y` and then `x`, and is `none` unless `y` ends where `x` starts. -/
noncomputable def mul? (x y : TotalPath Q) : Option (TotalPath Q) :=
  if h : y.2.1 = x.1 then some ⟨y.1, x.2.1, (h ▸ y.2.2).comp x.2.2⟩ else none

/-- Composable indexed paths concatenate, the later factor written first. -/
@[simp]
theorem mul?_mk {a b c : Q} (p : _root_.Quiver.Path a b) (q : _root_.Quiver.Path c a) :
    mul? (⟨a, b, p⟩ : TotalPath Q) ⟨c, a, q⟩ = some ⟨c, b, q.comp p⟩ := by
  simp [mul?]

/-- Indexed paths that do not meet have no concatenation. -/
theorem mul?_eq_none {x y : TotalPath Q} (h : y.2.1 ≠ x.1) : mul? x y = none := by
  simp only [mul?, dite_eq_right h]

/-- The concatenation of two indexed paths is undefined exactly when they do not meet. -/
theorem mul?_eq_none_iff {x y : TotalPath Q} : mul? x y = none ↔ y.2.1 ≠ x.1 := by
  refine ⟨fun h hne => ?_, mul?_eq_none⟩
  rw [mul?, dite_eq_left hne] at h
  exact Option.some_ne_none _ h

/-- Reversal reverses the order of partial concatenation, preserving undefined products. -/
@[simp]
theorem map_reverse_mul? [HasReverse Q] (x y : TotalPath Q) :
    (x.mul? y).map reverse = y.reverse.mul? x.reverse := by
  obtain ⟨a, b, p⟩ := x
  obtain ⟨c, d, q⟩ := y
  by_cases h : d = a
  · subst d
    simp [Path.reverse_comp]
  · rw [mul?_eq_none h, Option.map_none, reverse_mk, reverse_mk,
      mul?_eq_none (fun he ↦ h he.symm)]

/-- **Concatenation adds lengths**: a path produced by `mul?` is as long as its two factors
together. -/
theorem length_eq_add_of_mul?_eq_some {x y z : TotalPath Q} (h : mul? x y = some z) :
    z.2.2.length = x.2.2.length + y.2.2.length := by
  obtain ⟨a, b, p⟩ := x
  obtain ⟨c, d, q⟩ := y
  by_cases hda : d = a
  · subst hda
    rw [mul?_mk, Option.some.injEq] at h
    subst h
    simp [Nat.add_comm]
  · rw [mul?_eq_none hda] at h
    exact absurd h.symm (Option.some_ne_none z)

/-- **Concatenation keeps the source**: a path produced by `mul?` starts where the factor written
second, which is traced first, starts. -/
theorem fst_of_mul?_eq_some {x y z : TotalPath Q} (h : mul? x y = some z) : z.1 = y.1 := by
  obtain ⟨a, b, p⟩ := x
  obtain ⟨c, d, q⟩ := y
  by_cases hda : d = a
  · subst hda
    rw [mul?_mk] at h
    obtain rfl := Option.some.inj h
    rfl
  · rw [mul?_eq_none hda] at h
    exact absurd h.symm (Option.some_ne_none z)

/-- **A concatenation is the trivial path at `v` exactly when both its factors are.** Lengths add
under `mul?`, so both factors have length zero, and the concatenation starts where the factor
written second does, so that common endpoint is `v`. -/
theorem eq_nil_iff_of_mul?_eq_some {v : Q} {x y z : TotalPath Q} (h : mul? x y = some z) :
    z = ⟨v, v, _root_.Quiver.Path.nil⟩ ↔
      x = ⟨v, v, _root_.Quiver.Path.nil⟩ ∧ y = ⟨v, v, _root_.Quiver.Path.nil⟩ := by
  have hcomp : y.2.1 = x.1 := by
    by_contra hne
    rw [mul?_eq_none hne] at h
    exact absurd h.symm (Option.some_ne_none z)
  simp only [eq_nil_iff, fst_of_mul?_eq_some h, length_eq_add_of_mul?_eq_some h]
  constructor
  · rintro ⟨hy, hlen⟩
    have hylen : y.2.2.length = 0 := by omega
    refine ⟨⟨?_, by omega⟩, hy, hylen⟩
    rw [← hcomp, ← y.2.2.eq_of_length_zero hylen]
    exact hy
  · rintro ⟨⟨-, hx⟩, hy, hy'⟩
    exact ⟨hy, by omega⟩

/-- The trivial path at the target of `x` is a left unit for `x`. -/
@[simp]
theorem mul?_nil_left (x : TotalPath Q) :
    mul? (⟨x.2.1, x.2.1, _root_.Quiver.Path.nil⟩ : TotalPath Q) x = some x := by
  obtain ⟨a, b, p⟩ := x
  simp

/-- The trivial path at the source of `x` is a right unit for `x`. -/
@[simp]
theorem mul?_nil_right (x : TotalPath Q) :
    mul? x (⟨x.1, x.1, _root_.Quiver.Path.nil⟩ : TotalPath Q) = some x := by
  obtain ⟨a, b, p⟩ := x
  simp [_root_.Quiver.Path.nil_comp]

/-- Concatenation of indexed paths is associative as a partial operation. -/
theorem mul?_assoc (x y z : TotalPath Q) :
    ((x.mul? y).bind fun w => w.mul? z) = (y.mul? z).bind fun w => x.mul? w := by
  obtain ⟨a, b, p⟩ := x
  obtain ⟨c, d, q⟩ := y
  obtain ⟨e, f, r⟩ := z
  by_cases h₁ : d = a
  · subst h₁
    by_cases h₂ : f = c
    · subst h₂
      simp [_root_.Quiver.Path.comp_assoc]
    · rw [mul?_mk, Option.bind_some, mul?_eq_none (by simpa using h₂),
        mul?_eq_none (by simpa using h₂), Option.bind_none]
  · rw [mul?_eq_none (by simpa using h₁), Option.bind_none]
    by_cases h₂ : f = c
    · subst h₂
      rw [mul?_mk, Option.bind_some, mul?_eq_none (by simpa using h₁)]
    · rw [mul?_eq_none (by simpa using h₂), Option.bind_none]

/-- **A path into `j` is determined by its last arrow and the path before it**: two indexed paths
ending in arrows into `j` agree exactly when their prefixes and their last arrows do. -/
theorem mk_cons_eq_mk_cons_iff {s s' i i' j : Q} {p : _root_.Quiver.Path s i}
    {p' : _root_.Quiver.Path s' i'} {b : i ⟶ j} {b' : i' ⟶ j} :
    (⟨s', j, p'.cons b'⟩ : TotalPath Q) = ⟨s, j, p.cons b⟩ ↔
      (⟨s', i', p'⟩ : TotalPath Q) = ⟨s, i, p⟩ ∧ (⟨i', b'⟩ : Σ a, a ⟶ j) = ⟨i, b⟩ := by
  constructor
  · intro h
    obtain ⟨rfl, h⟩ := Sigma.mk.inj h
    have h := eq_of_heq (Sigma.mk.inj (eq_of_heq h)).2
    obtain rfl := _root_.Quiver.Path.obj_eq_of_cons_eq_cons h
    obtain ⟨hp, hb⟩ := (_root_.Quiver.Path.cons.inj h).2
    obtain rfl := eq_of_heq hp
    obtain rfl := eq_of_heq hb
    exact ⟨rfl, rfl⟩
  · rintro ⟨h, h'⟩
    obtain ⟨rfl, h'⟩ := Sigma.mk.inj h'
    obtain rfl := eq_of_heq h'
    obtain ⟨rfl, h⟩ := Sigma.mk.inj h
    obtain rfl := eq_of_heq (Sigma.mk.inj (eq_of_heq h)).2
    rfl

end Quiver.TotalPath

end TauCeti
