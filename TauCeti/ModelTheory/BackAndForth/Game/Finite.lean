/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.Equivalence

/-!
# Finite Ehrenfeucht–Fraïssé strategies

`EFStrategy L k a b` is a winning strategy for Duplicator for `k` more rounds, starting with
paired tuples `a` and `b`. At each round Spoiler chooses an element of either structure and
Duplicator supplies a matching element and a continuation strategy. Atomic agreement is checked
also at the initial position, so empty structures with different nullary relations cannot win
by having no legal moves.

Existence of a strategy is equivalent to finite-level `BFEquiv`. The strategy is data, rather
than just the alternating-quantifier condition: its branches specify responses to every move.
Different finite lengths need not choose compatible responses; a coherent infinite strategy is
a separate object.

The game interpretation is the classical Ehrenfeucht–Fraïssé interpretation of back-and-forth
relations; see Wilfrid Hodges, *Model Theory* (1993), the treatment of back-and-forth games.
-/

public section

universe u v w w' o

namespace TauCeti

open FirstOrder Fin

variable (L : Language.{u, v}) [L.IsRelational]
variable {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

/-- A winning finite-round Duplicator strategy. Every branch records a response and a winning
continuation, and every reached position must preserve the atomic type. -/
inductive EFStrategy : ℕ → {n : ℕ} → (Fin n → M) → (Fin n → N) → Type (max w w') where
  /-- With no moves remaining, atomic agreement is exactly the winning condition. -/
  | zero {n} {a : Fin n → M} {b : Fin n → N} (atomic : SameAtomicType (L := L) a b) :
      EFStrategy 0 a b
  /-- Respond to a move on either side, with a strategy for the remaining rounds. -/
  | succ {k n} {a : Fin n → M} {b : Fin n → N} (atomic : SameAtomicType (L := L) a b)
      (forth : M → N) (back : N → M)
      (forth_cont : ∀ x : M, EFStrategy k (snoc a x) (snoc b (forth x)))
      (back_cont : ∀ y : N, EFStrategy k (snoc a (back y)) (snoc b y)) :
      EFStrategy (k + 1) a b

namespace EFStrategy

variable {L} {k n : ℕ} {a : Fin n → M} {b : Fin n → N}

/-- Forget the last round of a finite strategy. -/
def dropLast : ∀ {k n : ℕ} {a : Fin n → M} {b : Fin n → N},
    EFStrategy L (k + 1) a b → EFStrategy L k a b
  | 0, _, _, _, .succ h _ _ _ _ => .zero h
  | _ + 1, _, _, _, .succ h f g fc gc =>
    .succ h f g (fun x => dropLast (fc x)) (fun y => dropLast (gc y))

@[simp]
theorem dropLast_one (h : SameAtomicType (L := L) a b) (f : M → N) (g : N → M)
    (fc : ∀ x, EFStrategy L 0 (snoc a x) (snoc b (f x)))
    (gc : ∀ y, EFStrategy L 0 (snoc a (g y)) (snoc b y)) :
    dropLast (.succ h f g fc gc) = .zero h := (rfl)

@[simp]
theorem dropLast_succ (h : SameAtomicType (L := L) a b) (f : M → N) (g : N → M)
    (fc : ∀ x, EFStrategy L (k + 1) (snoc a x) (snoc b (f x)))
    (gc : ∀ y, EFStrategy L (k + 1) (snoc a (g y)) (snoc b y)) :
    dropLast (.succ h f g fc gc) =
      .succ h f g (fun x => dropLast (fc x)) (fun y => dropLast (gc y)) := (rfl)

/-- A winning `k`-round strategy implies back-and-forth equivalence at level `k`. -/
theorem bfEquiv (s : EFStrategy L k a b) : BFEquiv (L := L) (k : Ordinal.{o}) n a b := by
  induction k generalizing n with
  | zero =>
    cases s with
    | zero h => exact BFEquiv.zero.mpr h
  | succ k ih =>
    have hprev := ih s.dropLast
    cases s with
    | succ h f g fc gc =>
      simpa only [Nat.cast_add, Nat.cast_one] using
        (BFEquiv.add_one (k : Ordinal.{o}) a b).mpr
          ⟨hprev, fun x => ⟨f x, ih (fc x)⟩, fun y => ⟨g y, ih (gc y)⟩⟩

/-- Finite back-and-forth equivalence is exactly existence of a winning finite strategy. -/
theorem nonempty_iff_bfEquiv :
    Nonempty (EFStrategy L k a b) ↔ BFEquiv (L := L) (k : Ordinal.{o}) n a b := by
  classical
  refine ⟨fun ⟨s⟩ => s.bfEquiv, ?_⟩
  intro h
  induction k generalizing n with
  | zero => exact ⟨.zero (BFEquiv.zero.mp h)⟩
  | succ k ih =>
    have hs := (BFEquiv.add_one (k : Ordinal.{o}) a b).mp
      (by simpa only [Nat.cast_add, Nat.cast_one] using h)
    exact ⟨.succ hs.1.sameAtomicType
      (fun x => Classical.choose (hs.2.1 x)) (fun y => Classical.choose (hs.2.2 y))
      (fun x => Classical.choice (ih (Classical.choose_spec (hs.2.1 x))))
      (fun y => Classical.choice (ih (Classical.choose_spec (hs.2.2 y))))⟩

/-- An unrelated winning strategy for every finite length amounts only to level-`ω`
back-and-forth equivalence. No compatibility between these strategies is imposed. -/
theorem nonempty_family_iff_bfEquiv_omega0 :
    Nonempty (∀ k : ℕ, EFStrategy L k a b) ↔
      BFEquiv (L := L) (Ordinal.omega0 : Ordinal.{o}) n a b := by
  classical
  rw [BFEquiv.limit Ordinal.isSuccLimit_omega0]
  constructor
  · rintro ⟨s⟩ α hα
    obtain ⟨k, rfl⟩ := Ordinal.lt_omega0.mp hα
    exact (s k).bfEquiv
  · intro h
    exact ⟨fun k => Classical.choice
      (nonempty_iff_bfEquiv.mpr (h k (Ordinal.natCast_lt_omega0 k)))⟩

end EFStrategy

end TauCeti
