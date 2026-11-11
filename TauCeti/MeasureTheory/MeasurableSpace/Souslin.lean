/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.MeasureTheory.MeasurableSpace.Defs

/-!
# The Souslin operation on families of sets

A scheme assigns a set to each finite sequence of natural numbers. Its Souslin operation
is the union, over infinite branches, of the intersections along their nonempty prefixes.
The Souslin closure of a family consists of all sets obtained from schemes in that family.
It contains the original family and is closed under natural-number-indexed unions and
intersections, without any finite-lattice assumption on the original family.

The intersection construction interleaves countably many branches with the natural-number
pairing function. In particular it does not assume the scheme sets are measurable or compact.
These set-theoretic closure properties underlie measurable and predictable section arguments.
The empty prefix is deliberately ignored; its value can be any member of the original family.
If the empty set, full set and complements of the generators are Souslin over the family,
every set in the generated sigma algebra is also Souslin over it.

## References

* S. Theodorakopoulos, *New proofs to measurable, predictable and optional section theorems*,
  arXiv:2310.13086v2, §2.
-/

public section

open Set
open scoped MeasureTheory

namespace TauCeti

variable {α : Type*}

/-- The Souslin operation: take the intersection along each infinite branch, then the union
of those intersections. Only nonempty finite prefixes occur. -/
def souslinOperation (f : List ℕ → Set α) : Set α :=
  ⋃ a : ℕ → ℕ, ⋂ n : ℕ, f (List.ofFn fun i : Fin (n + 1) ↦ a i)

/-- Membership in the Souslin operation means that one branch satisfies every finite
prefix constraint. -/
theorem mem_souslinOperation_iff {f : List ℕ → Set α} {x : α} :
    x ∈ souslinOperation f ↔
      ∃ a : ℕ → ℕ, ∀ n : ℕ, x ∈ f (List.ofFn fun i : Fin (n + 1) ↦ a i) := by
  simp [souslinOperation]

/-- Enlarging every scheme set enlarges its Souslin operation. -/
theorem souslinOperation_mono {f g : List ℕ → Set α} (h : ∀ l, f l ⊆ g l) :
    souslinOperation f ⊆ souslinOperation g := by
  intro x hx
  obtain ⟨a, ha⟩ := mem_souslinOperation_iff.mp hx
  exact mem_souslinOperation_iff.mpr ⟨a, fun n ↦ h _ (ha n)⟩

/-- A constant scheme has its constant value as Souslin operation. -/
@[simp]
theorem souslinOperation_const (s : Set α) : souslinOperation (fun _ ↦ s) = s := by
  ext x
  simp [mem_souslinOperation_iff]

/-- The Souslin closure of a family of sets, using schemes valued in that family. -/
def souslinClosure (E : Set (Set α)) : Set (Set α) :=
  {s | ∃ f : List ℕ → Set α, (∀ l, f l ∈ E) ∧ souslinOperation f = s}

/-- A set belongs to the Souslin closure precisely when it is represented by a scheme in
the original family. -/
theorem mem_souslinClosure_iff {E : Set (Set α)} {s : Set α} :
    s ∈ souslinClosure E ↔
      ∃ f : List ℕ → Set α, (∀ l, f l ∈ E) ∧ souslinOperation f = s :=
  Iff.rfl

/-- Each member of a family belongs to its Souslin closure, by the constant scheme. -/
theorem subset_souslinClosure (E : Set (Set α)) : E ⊆ souslinClosure E := by
  intro s hs
  exact ⟨fun _ ↦ s, fun _ ↦ hs, souslinOperation_const s⟩

/-- Souslin closure is monotone in its generating family. -/
theorem souslinClosure_mono {E F : Set (Set α)} (h : E ⊆ F) :
    souslinClosure E ⊆ souslinClosure F := by
  rintro s ⟨f, hf, rfl⟩
  exact ⟨f, fun l ↦ h (hf l), rfl⟩

-- The first digit encodes both the family index and the first original branch digit.
-- Thus even the length-one constraint stays in the original family.
private def unionScheme (f : ℕ → List ℕ → Set α) (l : List ℕ) : Set α :=
  f (Nat.unpair (l.headD 0)).1 ((Nat.unpair (l.headD 0)).2 :: l.tail)

private theorem souslinOperation_unionScheme (f : ℕ → List ℕ → Set α) :
    souslinOperation (unionScheme f) = ⋃ i, souslinOperation (f i) := by
  ext x
  simp only [mem_souslinOperation_iff, mem_iUnion]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨(Nat.unpair (a 0)).1, ?_⟩
    refine ⟨fun k ↦ if k = 0 then (Nat.unpair (a 0)).2 else a k, ?_⟩
    intro n
    simpa [unionScheme, List.ofFn_succ] using ha n
  · rintro ⟨i, a, ha⟩
    refine ⟨fun k ↦ if k = 0 then Nat.pair i (a 0) else a k, ?_⟩
    intro n
    simpa [unionScheme, List.ofFn_succ] using ha n

-- At stage pair i j, test row i through its j-th digit. Monotonicity of pairing
-- ensures that every digit this test reads is already present in the finite prefix.
private def interScheme (f : ℕ → List ℕ → Set α) (l : List ℕ) : Set α :=
  let p := Nat.unpair (l.length - 1)
  f p.1 (List.ofFn fun k : Fin (p.2 + 1) ↦ l.getD (Nat.pair p.1 k) 0)

private theorem interScheme_prefix (f : ℕ → List ℕ → Set α) (a : ℕ → ℕ) (n : ℕ) :
    interScheme f (List.ofFn fun i : Fin (n + 1) ↦ a i) =
      f (Nat.unpair n).1 (List.ofFn fun k : Fin ((Nat.unpair n).2 + 1) ↦
        a (Nat.pair (Nat.unpair n).1 k)) := by
  simp only [interScheme, List.length_ofFn, Nat.add_sub_cancel]
  congr 1
  apply congrArg List.ofFn
  funext k
  have hk : Nat.pair (Nat.unpair n).1 k < n + 1 := by
    have hpair : StrictMono (Nat.pair (Nat.unpair n).1) :=
      fun _ _ h ↦ Nat.pair_lt_pair_right _ h
    have := hpair.monotone (Nat.le_of_lt_succ k.isLt)
    simpa [Nat.pair_unpair] using Nat.lt_succ_of_le this
  rw [← List.getElem_eq_getD (h := by simpa only [List.length_ofFn, Fin.val_cast] using hk),
    List.getElem_ofFn]
  rfl

private theorem souslinOperation_interScheme (f : ℕ → List ℕ → Set α) :
    souslinOperation (interScheme f) = ⋂ i, souslinOperation (f i) := by
  classical
  ext x
  simp only [mem_souslinOperation_iff, mem_iInter]
  constructor
  · rintro ⟨a, ha⟩ i
    refine ⟨fun j ↦ a (Nat.pair i j), fun j ↦ ?_⟩
    have h := ha (Nat.pair i j)
    rw [interScheme_prefix] at h
    simpa only [Nat.unpair_pair, Fin.val_cast] using h
  · intro h
    choose a ha using h
    refine ⟨fun n ↦ a (Nat.unpair n).1 (Nat.unpair n).2, fun n ↦ ?_⟩
    rw [interScheme_prefix f (fun n ↦ a (Nat.unpair n).1 (Nat.unpair n).2)]
    simpa only [Nat.unpair_pair] using ha (Nat.unpair n).1 (Nat.unpair n).2

/-- The Souslin closure is closed under countable unions indexed by the natural numbers.
No union-closure hypothesis on the original family is required. -/
theorem iUnion_mem_souslinClosure {E : Set (Set α)} {s : ℕ → Set α}
    (hs : ∀ n, s n ∈ souslinClosure E) : (⋃ n, s n) ∈ souslinClosure E := by
  classical
  choose f hf heq using hs
  refine ⟨unionScheme f, fun l ↦ hf _ _, ?_⟩
  simp [souslinOperation_unionScheme, heq]

/-- The Souslin closure is closed under countable intersections indexed by the natural
numbers, even when the original family is not closed under finite intersections. -/
theorem iInter_mem_souslinClosure {E : Set (Set α)} {s : ℕ → Set α}
    (hs : ∀ n, s n ∈ souslinClosure E) : (⋂ n, s n) ∈ souslinClosure E := by
  classical
  choose f hf heq using hs
  refine ⟨interScheme f, fun l ↦ hf _ _, ?_⟩
  simp [souslinOperation_interScheme, heq]

/-- If complements of the generators, the empty set and the full set are Souslin over a
family, then so is every set in the generated sigma algebra. The original family need not
itself be an algebra, and no measurability hypothesis on its members is needed. -/
theorem measurableSet_mem_souslinClosure {E : Set (Set α)}
    (hcompl : ∀ s ∈ E, sᶜ ∈ souslinClosure E)
    (hempty : ∅ ∈ souslinClosure E) (huniv : univ ∈ souslinClosure E)
    {s : Set α} (hs : MeasurableSet[MeasurableSpace.generateFrom E] s) :
    s ∈ souslinClosure E := by
  have h : s ∈ souslinClosure E ∧ sᶜ ∈ souslinClosure E := by
    induction s, hs using MeasurableSpace.generateFrom_induction with
    | hC t ht => exact ⟨subset_souslinClosure E ht, hcompl t ht⟩
    | empty => simpa only [compl_empty] using And.intro hempty huniv
    | compl t _ ih => simpa only [compl_compl] using ih.symm
    | iUnion t _ ih =>
      refine ⟨iUnion_mem_souslinClosure (fun n ↦ (ih n).1), ?_⟩
      rw [compl_iUnion]
      exact iInter_mem_souslinClosure (fun n ↦ (ih n).2)
  exact h.1

end TauCeti
