/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.Game.Finite
public import TauCeti.ModelTheory.BackAndForth.Presentation

/-!
# Coherent infinite Ehrenfeucht–Fraïssé strategies

`CoherentEFStrategy L a b` records the paired tuples after every finite history of Spoiler
moves, preserving atomic type and extending the preceding position by exactly the chosen move
and its response. Histories list the most recent move first. An `M ⊕ N` move specifies both
which structure Spoiler plays in and the chosen element. Every such history is legal, so the
strategy carries no arbitrary values on unreachable histories.

Existence of a coherent strategy from the empty tuples is equivalent to potential isomorphism.
A tuple back-and-forth system constructs a strategy by recursively choosing responses within
the same system; conversely, the reached positions of one strategy form a system.

There is a genuine quantifier-order distinction: `BFEquiv ω` gives a winning strategy for each
finite length, allowing the response to depend on that length. A coherent strategy must fix a
response before knowing how many further moves will be made. The former condition does not
supply the latter: a response that works for every finite continuation must be chosen once,
not separately for each length. `EFStrategy.nonempty_family_iff_bfEquiv_omega0` states precisely
what the unrelated family expresses, while `potentialIso_iff_nonempty_coherentEFStrategy`
characterizes the coherent object.

See Wilfrid Hodges, *Model Theory* (1993), for back-and-forth games, and Carol Karp,
*Finite-quantifier equivalence* (1965), for back-and-forth systems. This construction uses the
existing tuple-system API, not a family of unrelated finite strategies.
-/

public section

universe u v w w'

namespace TauCeti

open FirstOrder Fin

variable (L : Language.{u, v}) [L.IsRelational]
variable {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]
variable {n : ℕ} (a : Fin n → M) (b : Fin n → N)

/-- One winning Duplicator strategy for arbitrarily long play. The positions at all histories
are compatible, so responses cannot depend on the future length of the game. -/
structure CoherentEFStrategy where
  /-- The first tuple after a history of Spoiler moves, newest move first. -/
  left : (h : List (M ⊕ N)) → Fin (n + h.length) → M
  /-- The second tuple after the same history. -/
  right : (h : List (M ⊕ N)) → Fin (n + h.length) → N
  /-- The first tuple starts at `a`. -/
  left_nil : left [] = a
  /-- The second tuple starts at `b`. -/
  right_nil : right [] = b
  /-- A move in the first structure appends exactly the element played. -/
  forth_left (h : List (M ⊕ N)) (x : M) : left (.inl x :: h) = snoc (left h) x
  /-- The matching response extends, rather than changes, the second tuple. -/
  forth_right (h : List (M ⊕ N)) (x : M) :
    right (.inl x :: h) = snoc (right h) (right (.inl x :: h) (last (n + h.length)))
  /-- The matching response extends, rather than changes, the first tuple. -/
  back_left (h : List (M ⊕ N)) (y : N) :
    left (.inr y :: h) = snoc (left h) (left (.inr y :: h) (last (n + h.length)))
  /-- A move in the second structure appends exactly the element played. -/
  back_right (h : List (M ⊕ N)) (y : N) : right (.inr y :: h) = snoc (right h) y
  /-- Duplicator wins at every finite position, including the initial position. -/
  sameAtomicType (h : List (M ⊕ N)) : SameAtomicType (L := L) (left h) (right h)

namespace CoherentEFStrategy

attribute [simp] left_nil right_nil forth_left back_right

variable {L a b}

/-- A response to a move in the first structure preserves every earlier entry. -/
@[simp]
theorem forth_right_castSucc (s : CoherentEFStrategy L a b) (h : List (M ⊕ N)) (x : M)
    (i : Fin (n + h.length)) : s.right (.inl x :: h) i.castSucc = s.right h i := by
  rw [s.forth_right]
  exact snoc_castSucc _ _ _

/-- A response to a move in the second structure preserves every earlier entry. -/
@[simp]
theorem back_left_castSucc (s : CoherentEFStrategy L a b) (h : List (M ⊕ N)) (y : N)
    (i : Fin (n + h.length)) : s.left (.inr y :: h) i.castSucc = s.left h i := by
  rw [s.back_left]
  exact snoc_castSucc _ _ _

/-- A coherent strategy is determined by its paired positions at every history. -/
@[ext]
theorem ext {s t : CoherentEFStrategy L a b} (hl : ∀ h, s.left h = t.left h)
    (hr : ∀ h, s.right h = t.right h) : s = t := by
  cases s
  cases t
  simp_all [mk.injEq, funext_iff]

/-- Restrict one coherent strategy, at any reached history, to a finite number of future rounds.
All these restrictions use the same responses at their common histories. -/
def toFinite (s : CoherentEFStrategy L a b) (k : ℕ) (h : List (M ⊕ N)) :
    EFStrategy L k (s.left h) (s.right h) := by
  induction k generalizing h with
  | zero => exact .zero (s.sameAtomicType h)
  | succ k ih =>
    refine .succ (s.sameAtomicType h)
      (fun x => s.right (.inl x :: h) (last _))
      (fun y => s.left (.inr y :: h) (last _)) ?_ ?_
    · intro x
      have hs := ih (.inl x :: h)
      rw [s.forth_left, s.forth_right] at hs
      exact hs
    · intro y
      have hs := ih (.inr y :: h)
      rw [s.back_left, s.back_right] at hs
      exact hs

@[simp]
theorem toFinite_zero (s : CoherentEFStrategy L a b) (h : List (M ⊕ N)) :
    s.toFinite 0 h = .zero (s.sameAtomicType h) := (rfl)

/-- Finite restriction uses the coherent response, independently of the remaining length. -/
@[simp]
theorem toFinite_succ (s : CoherentEFStrategy L a b) (k : ℕ) (h : List (M ⊕ N)) :
    s.toFinite (k + 1) h =
      .succ (s.sameAtomicType h)
        (fun x => s.right (.inl x :: h) (last _))
        (fun y => s.left (.inr y :: h) (last _))
        (fun x => by
          have hs := s.toFinite k (.inl x :: h)
          rw [s.forth_left, s.forth_right] at hs
          exact hs)
        (fun y => by
          have hs := s.toFinite k (.inr y :: h)
          rw [s.back_left, s.back_right] at hs
          exact hs) := (rfl)

/-- A coherent infinite strategy gives a winning strategy for every finite number of rounds. -/
theorem nonempty_finite (s : CoherentEFStrategy L a b) (k : ℕ) :
    Nonempty (EFStrategy L k a b) := by
  have hs := s.toFinite k []
  rw [s.left_nil, s.right_nil] at hs
  exact ⟨hs⟩

end CoherentEFStrategy

namespace IsTupleBFSystem

variable {L a b} {S : Set (Σ n, (Fin n → M) × (Fin n → N))}

/-- Recursively choose the reached pair while retaining its membership in the fixed system. -/
private noncomputable def play (hS : IsTupleBFSystem (L := L) S)
    (hab : ⟨n, a, b⟩ ∈ S) : (h : List (M ⊕ N)) →
      {p : (Fin (n + h.length) → M) × (Fin (n + h.length) → N) //
        ⟨n + h.length, p.1, p.2⟩ ∈ S}
  | [] => ⟨(a, b), hab⟩
  | .inl x :: h =>
    let p := play hS hab h
    ⟨(snoc p.val.1 x, snoc p.val.2 (Classical.choose (hS.forth p.property x))),
      Classical.choose_spec (hS.forth p.property x)⟩
  | .inr y :: h =>
    let p := play hS hab h
    ⟨(snoc p.val.1 (Classical.choose (hS.back p.property y)), snoc p.val.2 y),
      Classical.choose_spec (hS.back p.property y)⟩

/-- A pair in a tuple back-and-forth system admits one coherent infinite strategy: each response
and its continuation stay inside the same system. -/
noncomputable def coherentEFStrategy (hS : IsTupleBFSystem (L := L) S)
    (hab : ⟨n, a, b⟩ ∈ S) : CoherentEFStrategy L a b where
  left h := (play hS hab h).val.1
  right h := (play hS hab h).val.2
  left_nil := rfl
  right_nil := rfl
  forth_left _ _ := rfl
  forth_right h x := by
    dsimp only [play]
    congr 1
    exact (Fin.snoc_last (α := fun _ => N) _ _).symm
  back_left h y := by
    dsimp only [play]
    congr 1
    exact (Fin.snoc_last (α := fun _ => M) _ _).symm
  back_right _ _ := rfl
  sameAtomicType h := hS.sameAtomicType (play hS hab h).property

end IsTupleBFSystem

namespace CoherentEFStrategy

variable {L}

/-- Reindexing the reached positions of a coherent strategy gives a tuple back-and-forth
system containing its starting pair, even when the starting tuples are nonempty. -/
theorem exists_isTupleBFSystem_mem (s : CoherentEFStrategy L a b) :
    ∃ S : Set (Σ n, (Fin n → M) × (Fin n → N)),
      IsTupleBFSystem (L := L) S ∧ ⟨n, a, b⟩ ∈ S := by
  let S : Set (Σ k, (Fin k → M) × (Fin k → N)) :=
    {p | ∃ (h : List (M ⊕ N)) (f : Fin p.1 → Fin (n + h.length)),
      p.2.1 = s.left h ∘ f ∧ p.2.2 = s.right h ∘ f}
  refine ⟨S, ?_, [], id, ?_, ?_⟩
  · constructor
    · exact ⟨[], Fin.elim0, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    · rintro k c d ⟨h, f, hc, hd⟩
      dsimp only at f hc hd
      subst c d
      exact (sameAtomicType_iff _ _).mpr
        ⟨fun i j => (s.sameAtomicType h).eq_iff (f i) (f j),
          fun r g => (s.sameAtomicType h).rel_iff r (f ∘ g)⟩
    · rintro k c d ⟨h, f, hc, hd⟩
      dsimp only at f hc hd
      subst c d
      intro x
      refine ⟨s.right (.inl x :: h) (last _), .inl x :: h,
        snoc (Fin.castSucc ∘ f) (last _), ?_, ?_⟩
      · rw [s.forth_left]
        exact (snoc_comp_snoc_castSucc_comp _ _ _).symm
      · rw [s.forth_right]
        simpa using (snoc_comp_snoc_castSucc_comp _ _ _).symm
    · rintro k c d ⟨h, f, hc, hd⟩
      dsimp only at f hc hd
      subst c d
      intro y
      refine ⟨s.left (.inr y :: h) (last _), .inr y :: h,
        snoc (Fin.castSucc ∘ f) (last _), ?_, ?_⟩
      · rw [s.back_left]
        simpa using (snoc_comp_snoc_castSucc_comp _ _ _).symm
      · rw [s.back_right]
        exact (snoc_comp_snoc_castSucc_comp _ _ _).symm
  · simp
  · simp

/-- A pair admits a coherent strategy exactly when it belongs to a tuple back-and-forth
system. This includes arbitrary starting tuples. -/
theorem nonempty_iff_exists_isTupleBFSystem_mem :
    Nonempty (CoherentEFStrategy L a b) ↔
      ∃ S : Set (Σ n, (Fin n → M) × (Fin n → N)),
        IsTupleBFSystem (L := L) S ∧ ⟨n, a, b⟩ ∈ S :=
  ⟨fun ⟨s⟩ => s.exists_isTupleBFSystem_mem,
    fun ⟨_, hS, hab⟩ => ⟨hS.coherentEFStrategy hab⟩⟩

/-- The reached positions of a coherent strategy from the empty tuples form a tuple
back-and-forth system. -/
theorem exists_isTupleBFSystem
    (s : CoherentEFStrategy L (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)) :
    ∃ S : Set (Σ n, (Fin n → M) × (Fin n → N)), IsTupleBFSystem (L := L) S := by
  obtain ⟨S, hS, _⟩ := s.exists_isTupleBFSystem_mem
  exact ⟨S, hS⟩

end CoherentEFStrategy

variable {L}

/-- Potential isomorphism is exactly existence of one winning coherent infinite strategy.
Unlike a family of finite-round strategies, the responses are fixed across all lengths. -/
theorem potentialIso_iff_nonempty_coherentEFStrategy :
    PotentialIso (L := L) M N ↔
      Nonempty (CoherentEFStrategy L (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)) := by
  constructor
  · intro h
    obtain ⟨S, hS⟩ := h.exists_isTupleBFSystem
    exact ⟨hS.coherentEFStrategy hS.empty_mem⟩
  · rintro ⟨s⟩
    obtain ⟨S, hS⟩ := s.exists_isTupleBFSystem
    exact hS.potentialIso

/-! ## Regression examples -/

namespace GameExamples

section General

variable {L : Language.{u, v}} [L.IsRelational]
variable {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]
variable {n : ℕ} {a : Fin n → M} {b : Fin n → N}

-- Repeated entries cause no problem: the identity matching wins every finite game.
example (a : Fin n → M) (k : ℕ) : Nonempty (EFStrategy L k a a) := by
  exact EFStrategy.nonempty_iff_bfEquiv.mpr (BFEquiv.refl (k : Ordinal.{0}) a)

-- One strategy makes its responses before the future length of play is specified.
example (s : CoherentEFStrategy L a b) : Nonempty (∀ k, EFStrategy L k a b) :=
  ⟨fun k => Classical.choice (s.nonempty_finite k)⟩

-- A separately chosen strategy at each length states only level-omega equivalence.
example : Nonempty (∀ k, EFStrategy L k a b) ↔
    BFEquiv (L := L) (Ordinal.omega0 : Ordinal.{0}) n a b :=
  EFStrategy.nonempty_family_iff_bfEquiv_omega0

-- Old entries never change when Spoiler chooses the left side.
example (s : CoherentEFStrategy L a b) (h : List (M ⊕ N)) (x : M)
    (i : Fin (n + h.length)) : s.right (.inl x :: h) i.castSucc = s.right h i := by
  simp

-- Nor when Spoiler chooses the right side.
example (s : CoherentEFStrategy L a b) (h : List (M ⊕ N)) (y : N)
    (i : Fin (n + h.length)) : s.left (.inr y :: h) i.castSucc = s.left h i := by
  simp

-- Any isomorphism supplies a coherent strategy, without countability assumptions.
example (e : M ≃[L] N) :
    Nonempty (CoherentEFStrategy L (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)) :=
  potentialIso_iff_nonempty_coherentEFStrategy.mp e.potentialIso

end General

section EmptyStructures

private abbrev nullaryLanguage : Language :=
  ⟨fun _ => Empty, fun k => PLift (k = 0)⟩

private instance : nullaryLanguage.IsRelational := fun _ => inferInstance

private noncomputable instance : nullaryLanguage.Structure Empty where
  funMap f _ := Empty.elim f
  RelMap _ _ := True

private noncomputable instance : nullaryLanguage.Structure (ULift Empty) where
  funMap f _ := Empty.elim f
  RelMap _ _ := False

-- Even a zero-round strategy must notice the nullary discrepancy.
example : ¬ Nonempty (EFStrategy nullaryLanguage 0
    (Fin.elim0 : Fin 0 → Empty) (Fin.elim0 : Fin 0 → ULift Empty)) := by
  rintro ⟨s⟩
  have h : BFEquiv (L := nullaryLanguage) (0 : Ordinal.{0}) 0 _ _ := s.bfEquiv
  exact (h.sameAtomicType.rel_iff (k := 0) ⟨rfl⟩ Fin.elim0).mp trivial

-- An infinite strategy must also pass the initial check, even with no legal moves.
example : ¬ Nonempty (CoherentEFStrategy nullaryLanguage
    (Fin.elim0 : Fin 0 → Empty) (Fin.elim0 : Fin 0 → ULift Empty)) := by
  rintro ⟨s⟩
  have h := s.sameAtomicType []
  rw [s.left_nil, s.right_nil] at h
  exact (h.rel_iff (k := 0) ⟨rfl⟩ Fin.elim0).mp trivial

private instance : Language.empty.Structure Empty := Language.emptyStructure
private instance : Language.empty.Structure Unit := Language.emptyStructure

-- The first move from a singleton cannot be answered in the empty structure.
example : ¬ Nonempty (EFStrategy Language.empty 1
    (Fin.elim0 : Fin 0 → Empty) (Fin.elim0 : Fin 0 → Unit)) := by
  rintro ⟨s⟩
  cases s with
  | succ _ _ back _ _ => exact isEmptyElim (back ())

end EmptyStructures

end GameExamples

end TauCeti
