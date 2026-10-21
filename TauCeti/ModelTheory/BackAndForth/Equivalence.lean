/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.AtomicType
public import Mathlib.Data.Fin.Tuple.Basic
public import TauCeti.Data.Fin.Tuple.Basic
public import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Ordinal back-and-forth equivalence

`BFEquiv α n a b` compares finite tuples at ordinal depth `α`. At zero it is atomic-type
agreement; a successor retains the previous level and requires matching one-element extensions
in both directions; a limit requires every earlier level. Keeping the previous level prevents
empty structures with different nullary relations from becoming equivalent at a successor.

The equivalence laws and lowering of the ordinal are the basic tools for internal stabilization
and for the characteristic formulas of tuples. No countability or nonemptiness is assumed.
As with `SameAtomicType`, the language is required to be relational, so the initial level
compares all atomic formulas.

The recursion follows Cameron Freer's `cameronfreer/infinitary-logic`,
`InfinitaryLogic/Scott/BackAndForth.lean`. Here the ordinal universe is independent of the
universes of the structures.
-/

public section

universe u v w w' w'' o

namespace TauCeti

open FirstOrder Fin

variable {L : Language.{u, v}} [L.IsRelational]
variable {M : Type w} {N : Type w'} {P : Type w''}
variable [L.Structure M] [L.Structure N] [L.Structure P]

/-- Ordinal back-and-forth equivalence of tuples. At successors the previous level is retained,
in addition to the forth and back requirements. The language is relational. -/
noncomputable def BFEquiv (α : Ordinal.{o}) (n : ℕ) (a : Fin n → M) (b : Fin n → N) : Prop :=
  Ordinal.limitRecOn
    (motive := fun _ => (k : ℕ) → (Fin k → M) → (Fin k → N) → Prop) α
    (fun _ a b => SameAtomicType (L := L) a b)
    (fun _ ih k a b => ih k a b ∧
      (∀ x : M, ∃ y : N, ih (k + 1) (snoc a x) (snoc b y)) ∧
      (∀ y : N, ∃ x : M, ih (k + 1) (snoc a x) (snoc b y)))
    (fun _ _ ih k a b => ∀ β (hβ : β < _), ih β hβ k a b)
    n a b

namespace BFEquiv

variable {n : ℕ} {a : Fin n → M} {b : Fin n → N} {c : Fin n → P}

/-- Level zero is precisely atomic-type agreement. -/
@[simp]
theorem zero : BFEquiv (L := L) (0 : Ordinal.{o}) n a b ↔ SameAtomicType (L := L) a b := by
  simp [BFEquiv]

/-- The successor step consists of the previous level and the two extension requirements. -/
@[simp]
theorem add_one (α : Ordinal.{o}) (a : Fin n → M) (b : Fin n → N) :
    BFEquiv (L := L) (α + 1) n a b ↔
      BFEquiv (L := L) α n a b ∧
      (∀ x : M, ∃ y : N, BFEquiv (L := L) α (n + 1) (snoc a x) (snoc b y)) ∧
      (∀ y : N, ∃ x : M, BFEquiv (L := L) α (n + 1) (snoc a x) (snoc b y)) := by
  simp [BFEquiv]

/-- Level one consists of atomic-type agreement and atomic-type matching of one-element
extensions in both directions. -/
@[simp]
theorem one (a : Fin n → M) (b : Fin n → N) :
    BFEquiv (L := L) (1 : Ordinal.{o}) n a b ↔
      SameAtomicType (L := L) a b ∧
      (∀ x : M, ∃ y : N, SameAtomicType (L := L) (snoc a x) (snoc b y)) ∧
      (∀ y : N, ∃ x : M, SameAtomicType (L := L) (snoc a x) (snoc b y)) := by
  rw [← zero_add (1 : Ordinal.{o}), add_one]
  simp only [zero]

/-- At a limit ordinal, equivalence means equivalence at every smaller ordinal. -/
@[simp]
theorem limit {α : Ordinal.{o}} (hα : Order.IsSuccLimit α)
    (a : Fin n → M) (b : Fin n → N) :
    BFEquiv (L := L) α n a b ↔ ∀ β < α, BFEquiv (L := L) β n a b := by
  simp [BFEquiv, Ordinal.limitRecOn_limit _ _ _ _ hα]

/-- Equivalence at a level implies equivalence at every lower level. -/
theorem mono {α β : Ordinal.{o}} (h : BFEquiv (L := L) β n a b) (hαβ : α ≤ β) :
    BFEquiv (L := L) α n a b := by
  induction β using Ordinal.limitRecOn generalizing α with
  | zero =>
    obtain rfl := le_antisymm hαβ bot_le
    exact h
  | add_one β ih =>
    rcases eq_or_lt_of_le hαβ with rfl | hlt
    · exact h
    · exact ih ((add_one β a b).mp h).1 (Order.le_of_lt_succ hlt)
  | limit β hβ ih =>
    rcases eq_or_lt_of_le hαβ with rfl | hlt
    · exact h
    · exact (limit hβ a b).mp h α hlt

/-- Atomic type is preserved at every back-and-forth level. -/
theorem sameAtomicType {α : Ordinal.{o}} (h : BFEquiv (L := L) α n a b) :
    SameAtomicType (L := L) a b := zero.mp (h.mono bot_le)

/-- Every tuple is back-and-forth equivalent to itself. -/
@[refl, simp]
theorem refl (α : Ordinal.{o}) (a : Fin n → M) : BFEquiv (L := L) α n a a := by
  induction α using Ordinal.limitRecOn generalizing n with
  | zero => exact zero.mpr (SameAtomicType.refl a)
  | add_one α ih =>
    exact (add_one α a a).mpr ⟨ih a, fun x => ⟨x, ih _⟩, fun x => ⟨x, ih _⟩⟩
  | limit α hα ih => exact (limit hα a a).mpr fun β hβ => ih β hβ a

/-- Back-and-forth equivalence is symmetric, including between different structure universes. -/
@[symm]
theorem symm {α : Ordinal.{o}} (h : BFEquiv (L := L) α n a b) :
    BFEquiv (L := L) α n b a := by
  induction α using Ordinal.limitRecOn generalizing n with
  | zero => exact zero.mpr (zero.mp h).symm
  | add_one α ih =>
    obtain ⟨h, hforth, hback⟩ := (add_one α a b).mp h
    refine (add_one α b a).mpr ⟨ih h, ?_, ?_⟩
    · intro y
      obtain ⟨x, hx⟩ := hback y
      exact ⟨x, ih hx⟩
    · intro x
      obtain ⟨y, hy⟩ := hforth x
      exact ⟨y, ih hy⟩
  | limit α hα ih =>
    exact (limit hα b a).mpr fun β hβ => ih β hβ ((limit hα a b).mp h β hβ)

/-- Back-and-forth equivalence is transitive across three structures. -/
@[trans]
theorem trans {α : Ordinal.{o}} (hab : BFEquiv (L := L) α n a b)
    (hbc : BFEquiv (L := L) α n b c) : BFEquiv (L := L) α n a c := by
  induction α using Ordinal.limitRecOn generalizing n with
  | zero => exact zero.mpr ((zero.mp hab).trans (zero.mp hbc))
  | add_one α ih =>
    obtain ⟨hab, habf, habb⟩ := (add_one α a b).mp hab
    obtain ⟨hbc, hbcf, hbcb⟩ := (add_one α b c).mp hbc
    refine (add_one α a c).mpr ⟨ih hab hbc, ?_, ?_⟩
    · intro x
      obtain ⟨y, hy⟩ := habf x
      obtain ⟨z, hz⟩ := hbcf y
      exact ⟨z, ih hy hz⟩
    · intro z
      obtain ⟨y, hy⟩ := hbcb z
      obtain ⟨x, hx⟩ := habb y
      exact ⟨x, ih hx hy⟩
  | limit α hα ih =>
    exact (limit hα a c).mpr fun β hβ =>
      ih β hβ ((limit hα a b).mp hab β hβ) ((limit hα b c).mp hbc β hβ)

/-- Back-and-forth equivalence is preserved when the two tuples are reindexed in the same way. -/
theorem comp {α : Ordinal.{o}} (h : BFEquiv (L := L) α n a b) {m : ℕ}
    (g : Fin m → Fin n) : BFEquiv (L := L) α m (a ∘ g) (b ∘ g) := by
  induction α using Ordinal.limitRecOn generalizing n m with
  | zero => exact zero.mpr ((zero.mp h).comp g)
  | add_one α ih =>
    obtain ⟨h, hforth, hback⟩ := (add_one α a b).mp h
    let g' : Fin (m + 1) → Fin (n + 1) := snoc (castSucc ∘ g) (last n)
    refine (add_one α (a ∘ g) (b ∘ g)).mpr ⟨ih h g, ?_, ?_⟩
    · intro x
      obtain ⟨y, hy⟩ := hforth x
      exact ⟨y, by simpa only [g', snoc_comp_snoc_castSucc_comp] using ih hy g'⟩
    · intro y
      obtain ⟨x, hx⟩ := hback y
      exact ⟨x, by simpa only [g', snoc_comp_snoc_castSucc_comp] using ih hx g'⟩
  | limit α hα ih =>
    exact (limit hα (a ∘ g) (b ∘ g)).mpr fun β hβ =>
      ih β hβ ((limit hα a b).mp h β hβ) g

/-- Swapping the two tuples does not change back-and-forth equivalence. -/
theorem symm_iff (α : Ordinal.{o}) (a : Fin n → M) (b : Fin n → N) :
    BFEquiv (L := L) α n a b ↔ BFEquiv (L := L) α n b a := ⟨symm, symm⟩

end BFEquiv

/-- An isomorphism carries every tuple to a tuple back-and-forth equivalent to it at every
level. In particular, tuples in one automorphism orbit are equivalent at every level. -/
theorem _root_.FirstOrder.Language.Equiv.bfEquiv (e : M ≃[L] N) (α : Ordinal.{o}) {n : ℕ}
    (a : Fin n → M) : BFEquiv (L := L) α n a (e ∘ a) := by
  induction α using Ordinal.limitRecOn generalizing n with
  | zero =>
    refine BFEquiv.zero.mpr ((sameAtomicType_iff _ _).mpr ⟨fun i j => ?_, fun r f => ?_⟩)
    · exact e.injective.eq_iff.symm
    · exact (e.map_rel r (a ∘ f)).symm
  | add_one α ih =>
    refine (BFEquiv.add_one α a _).mpr ⟨ih a, fun x => ⟨e x, ?_⟩, fun y => ⟨e.symm y, ?_⟩⟩
    · simpa only [Fin.comp_snoc] using ih (snoc a x)
    · simpa only [Fin.comp_snoc, e.apply_symm_apply] using ih (snoc a (e.symm y))
  | limit α hα ih => exact (BFEquiv.limit hα a _).mpr fun β hβ => ih β hβ a

/-! ## Empty-structure regression examples -/

namespace BackAndForthExamples

private abbrev nullaryLanguage : Language :=
  ⟨fun _ => Empty, fun k => PLift (k = 0)⟩

private instance : nullaryLanguage.IsRelational := fun _ => inferInstance

private noncomputable instance : nullaryLanguage.Structure Empty where
  funMap f _ := Empty.elim f
  RelMap _ _ := True

private noncomputable instance : nullaryLanguage.Structure (ULift Empty) where
  funMap f _ := Empty.elim f
  RelMap _ _ := False

-- The nullary relation is visible even to the empty tuples, at every level.
example (α : Ordinal) :
    ¬ BFEquiv (L := nullaryLanguage) α 0
      (Fin.elim0 : Fin 0 → Empty) (Fin.elim0 : Fin 0 → ULift Empty) := by
  intro h
  exact (h.sameAtomicType.rel_iff (k := 0) ⟨rfl⟩ Fin.elim0).mp trivial

-- Both extension requirements are vacuous, so retaining the previous level is essential.
example :
    (∀ x : Empty, ∃ y : ULift Empty,
      BFEquiv (L := nullaryLanguage) 0 1 (snoc Fin.elim0 x) (snoc Fin.elim0 y)) ∧
    (∀ y : ULift Empty, ∃ x : Empty,
      BFEquiv (L := nullaryLanguage) 0 1 (snoc Fin.elim0 x) (snoc Fin.elim0 y)) := by
  exact ⟨fun x => isEmptyElim x, fun y => isEmptyElim y⟩

private instance : Language.empty.Structure Empty := Language.emptyStructure
private instance : Language.empty.Structure Unit := Language.emptyStructure

-- Without nullary relations, an empty structure and a singleton agree at zero.
example : BFEquiv (L := Language.empty) 0 0
    (Fin.elim0 : Fin 0 → Empty) (Fin.elim0 : Fin 0 → Unit) := by
  apply BFEquiv.zero.mpr
  apply (sameAtomicType_iff _ _).mpr
  exact ⟨fun i => Fin.elim0 i, fun r => isEmptyElim r⟩

-- The back requirement distinguishes the same structures at the first successor.
example : ¬ BFEquiv (L := Language.empty) 1 0
    (Fin.elim0 : Fin 0 → Empty) (Fin.elim0 : Fin 0 → Unit) := by
  intro h
  have h' := (BFEquiv.add_one (L := Language.empty) 0 _ _).mp
    (by simpa only [zero_add] using h)
  obtain ⟨x, _⟩ := h'.2.2 ()
  exact isEmptyElim x

-- Nonempty tuples in a nonempty structure satisfy all levels.
example (α : Ordinal) :
    BFEquiv (L := Language.empty) α 2 (fun _ => ()) (fun _ => ()) := by
  simp

end BackAndForthExamples

end TauCeti
