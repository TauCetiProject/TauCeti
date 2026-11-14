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
It contains the original family and is closed under nonempty countable unions and
intersections, without any finite-lattice assumption on the original family.

The intersection construction interleaves countably many branches with the natural-number
pairing function. In particular it does not assume the scheme sets are measurable or compact.
These set-theoretic closure properties underlie measurable and predictable section arguments.
The empty prefix is deliberately ignored; its value can be any member of the original family.
If the family is nonempty and complements of its generators are Souslin over it,
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

/-- The Souslin operation as an indexed union of branch intersections. -/
theorem souslinOperation_def (f : List ℕ → Set α) :
    souslinOperation f = ⋃ a : ℕ → ℕ, ⋂ n : ℕ,
      f (List.ofFn fun i : Fin (n + 1) ↦ a i) := (rfl)

/-- Membership in the Souslin operation means that one branch satisfies every nonempty finite
prefix constraint. -/
@[simp, grind =]
theorem mem_souslinOperation_iff {f : List ℕ → Set α} {x : α} :
    x ∈ souslinOperation f ↔
      ∃ a : ℕ → ℕ, ∀ n : ℕ, x ∈ f (List.ofFn fun i : Fin (n + 1) ↦ a i) := by
  simp [souslinOperation]

/-- Enlarging a scheme's values on every nonempty prefix enlarges its Souslin operation. -/
@[gcongr]
theorem souslinOperation_mono {f g : List ℕ → Set α} (h : ∀ l ≠ [], f l ⊆ g l) :
    souslinOperation f ⊆ souslinOperation g := by
  intro x hx
  obtain ⟨a, ha⟩ := mem_souslinOperation_iff.mp hx
  exact mem_souslinOperation_iff.mpr ⟨a, fun n ↦ h _ (by simp) (ha n)⟩

/-- Changing the unused empty prefix does not affect the Souslin operation. -/
theorem souslinOperation_congr {f g : List ℕ → Set α}
    (h : ∀ l ≠ [], f l = g l) : souslinOperation f = souslinOperation g :=
  subset_antisymm (souslinOperation_mono fun l hl ↦ (h l hl).subset)
    (souslinOperation_mono fun l hl ↦ (h l hl).superset)

/-- A constant scheme has its constant value as Souslin operation. -/
@[simp]
theorem souslinOperation_const (s : Set α) : souslinOperation (fun _ ↦ s) = s := by
  ext x
  simp [mem_souslinOperation_iff]

/-- The Souslin closure of a family of sets, using schemes valued in that family. -/
def souslinClosure (E : Set (Set α)) : Set (Set α) :=
  {s | ∃ f : List ℕ → Set α, (∀ l, f l ∈ E) ∧ souslinOperation f = s}

/-- The Souslin closure as the sets represented by schemes in the original family. -/
theorem souslinClosure_def (E : Set (Set α)) :
    souslinClosure E =
      {s | ∃ f : List ℕ → Set α, (∀ l, f l ∈ E) ∧ souslinOperation f = s} := (rfl)

/-- A set belongs to the Souslin closure precisely when it is represented by a scheme in
the original family. -/
theorem mem_souslinClosure_iff {E : Set (Set α)} {s : Set α} :
    s ∈ souslinClosure E ↔
      ∃ f : List ℕ → Set α, (∀ l, f l ∈ E) ∧ souslinOperation f = s :=
  Iff.rfl

/-- Each member of a family belongs to its Souslin closure, by the constant scheme. -/
@[simp]
theorem subset_souslinClosure {E : Set (Set α)} : E ⊆ souslinClosure E := by
  intro s hs
  exact ⟨fun _ ↦ s, fun _ ↦ hs, souslinOperation_const s⟩

grind_pattern subset_souslinClosure => souslinClosure E

/-- The Souslin operation of a scheme belongs to the Souslin closure if all its values on
nonempty prefixes belong to the family. -/
@[grind ←]
theorem souslinOperation_mem_souslinClosure {E : Set (Set α)} {f : List ℕ → Set α}
    (hf : ∀ l ≠ [], f l ∈ E) : souslinOperation f ∈ souslinClosure E := by
  classical
  refine ⟨fun l ↦ if l = [] then f [0] else f l, ?_, ?_⟩
  · intro l
    dsimp only
    split_ifs with hl
    · exact hf [0] (by simp)
    · exact hf l hl
  · exact souslinOperation_congr fun l hl ↦ by simp only [hl, ↓reduceIte]

/-- The empty family has empty Souslin closure. -/
@[simp, grind =]
theorem souslinClosure_empty : souslinClosure (∅ : Set (Set α)) = ∅ := by
  ext s
  simp [mem_souslinClosure_iff]

/-- A singleton family is its own Souslin closure. -/
@[simp, grind =]
theorem souslinClosure_singleton (s : Set α) : souslinClosure {s} = {s} := by
  apply subset_antisymm
  · rintro t ⟨f, hf, rfl⟩
    have heq : f = fun _ ↦ s := funext fun l ↦ mem_singleton_iff.mp (hf l)
    simp [heq]
  · exact subset_souslinClosure

/-- The family of all sets is its own Souslin closure. -/
@[simp, grind =]
theorem souslinClosure_univ : souslinClosure (univ : Set (Set α)) = univ :=
  subset_antisymm (subset_univ _) subset_souslinClosure

/-- Souslin closure is monotone in its generating family. -/
@[gcongr, grind ←]
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
  -- The cast only changes the bound of the finite index, not its natural-number value.
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

/-- The Souslin closure is closed under nonempty countable unions.
No union-closure hypothesis on the original family is required. -/
@[grind ←]
theorem iUnion_mem_souslinClosure {ι : Sort*} [Countable ι] [Nonempty ι]
    {E : Set (Set α)} {s : ι → Set α}
    (hs : ∀ i, s i ∈ souslinClosure E) : (⋃ i, s i) ∈ souslinClosure E := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat ι
  rw [← iUnion_congr_of_surjective e he (fun _ ↦ rfl)]
  choose f hf heq using fun n ↦ hs (e n)
  refine ⟨unionScheme f, fun l ↦ hf _ _, ?_⟩
  simp [souslinOperation_unionScheme, heq]

/-- The Souslin closure is closed under nonempty countable intersections,
even when the original family is not closed under finite intersections. -/
@[grind ←]
theorem iInter_mem_souslinClosure {ι : Sort*} [Countable ι] [Nonempty ι]
    {E : Set (Set α)} {s : ι → Set α}
    (hs : ∀ i, s i ∈ souslinClosure E) : (⋂ i, s i) ∈ souslinClosure E := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat ι
  rw [← iInter_congr_of_surjective e he (fun _ ↦ rfl)]
  choose f hf heq using fun n ↦ hs (e n)
  refine ⟨interScheme f, fun l ↦ hf _ _, ?_⟩
  simp [souslinOperation_interScheme, heq]

/-- The Souslin closure is closed under binary unions. -/
@[grind ←]
theorem union_mem_souslinClosure {E : Set (Set α)} {s t : Set α}
    (hs : s ∈ souslinClosure E) (ht : t ∈ souslinClosure E) :
    s ∪ t ∈ souslinClosure E := by
  rw [union_eq_iUnion]
  apply iUnion_mem_souslinClosure
  intro b
  cases b <;> assumption

/-- The Souslin closure is closed under binary intersections. -/
@[grind ←]
theorem inter_mem_souslinClosure {E : Set (Set α)} {s t : Set α}
    (hs : s ∈ souslinClosure E) (ht : t ∈ souslinClosure E) :
    s ∩ t ∈ souslinClosure E := by
  rw [inter_eq_iInter]
  apply iInter_mem_souslinClosure
  intro b
  cases b <;> assumption

/-- If a family is nonempty and complements of its generators are Souslin over it, then so
is every set in the generated sigma algebra. The original family need not itself be an
algebra, and no measurability hypothesis on its members is needed. -/
theorem mem_souslinClosure_of_measurableSet_generateFrom {E : Set (Set α)}
    (hE : E.Nonempty) (hcompl : ∀ s ∈ E, sᶜ ∈ souslinClosure E)
    {s : Set α} (hs : MeasurableSet[MeasurableSpace.generateFrom E] s) :
    s ∈ souslinClosure E := by
  obtain ⟨t, ht⟩ := hE
  have ht' := subset_souslinClosure ht
  have htc := hcompl t ht
  have hempty : ∅ ∈ souslinClosure E := by
    simpa only [inter_compl_self] using inter_mem_souslinClosure ht' htc
  have huniv : univ ∈ souslinClosure E := by
    simpa only [union_compl_self] using union_mem_souslinClosure ht' htc
  have h : s ∈ souslinClosure E ∧ sᶜ ∈ souslinClosure E := by
    induction s, hs using MeasurableSpace.generateFrom_induction with
    | hC t ht => exact ⟨subset_souslinClosure ht, hcompl t ht⟩
    | empty => simpa only [compl_empty] using And.intro hempty huniv
    | compl t _ ih => simpa only [compl_compl] using ih.symm
    | iUnion t _ ih =>
      refine ⟨iUnion_mem_souslinClosure (fun n ↦ (ih n).1), ?_⟩
      rw [compl_iUnion]
      exact iInter_mem_souslinClosure (fun n ↦ (ih n).2)
  exact h.1

end TauCeti
