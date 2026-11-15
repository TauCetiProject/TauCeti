/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Order.Basic

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

When the generating family `E` is closed under binary unions and intersections and `I` is a
monotone `ℝ≥0∞`-valued set function continuous along increasing countable unions, any strict
lower bound `r < I s` on a set `s ∈ souslinClosure E` is witnessed by an antitone sequence
`e : ℕ → Set α` in `E` whose intersection is contained in `s` and whose values satisfy
`r < ⨅ k, I (e k)` (`TauCeti.exists_antitone_mem_of_lt_of_mem_souslinClosure`). No topology or
measurability structure on the carrier is assumed.

## References

* S. Theodorakopoulos, *New proofs to measurable, predictable and optional section theorems*,
  arXiv:2310.13086v2, §2 (Theorem 2.5).
-/

public section

open Filter Set Topology
open scoped ENNReal MeasureTheory NNReal

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

/-! ### Capacity approximation over binary-lattice pavings -/

-- Intersect the values of `f` along all nonempty prefixes of `w : Fin (k + 1) → ℕ`.
private def prefixInter (f : List ℕ → Set α) : ∀ k : ℕ, (Fin (k + 1) → ℕ) → Set α
  | 0, w => f (List.ofFn w)
  | k + 1, w => prefixInter f k (Fin.init w) ∩ f (List.ofFn w)

private lemma prefixInter_mem {E : Set (Set α)} (hinter : ∀ u ∈ E, ∀ v ∈ E, u ∩ v ∈ E)
    {f : List ℕ → Set α} (hf : ∀ l, f l ∈ E) :
    ∀ (k : ℕ) (w : Fin (k + 1) → ℕ), prefixInter f k w ∈ E
  | 0, w => hf (List.ofFn w)
  | k + 1, w => hinter _ (prefixInter_mem hinter hf k (Fin.init w)) _ (hf (List.ofFn w))

private lemma mem_prefixInter_of_forall {f : List ℕ → Set α} {x : α} {β : ℕ → ℕ}
    (hβ : ∀ n : ℕ, x ∈ f (List.ofFn fun i : Fin (n + 1) ↦ β i)) :
    ∀ k : ℕ, x ∈ prefixInter f k (fun i : Fin (k + 1) ↦ β i)
  | 0 => hβ 0
  | k + 1 => ⟨mem_prefixInter_of_forall hβ k, hβ (k + 1)⟩

private lemma mem_of_mem_prefixInter {f : List ℕ → Set α} {x : α} :
    ∀ {k : ℕ} {w : Fin (k + 1) → ℕ}, x ∈ prefixInter f k w → x ∈ f (List.ofFn w)
  | 0, _, hx => hx
  | _ + 1, _, hx => hx.2

private def prefixBox (N : ℕ → ℕ) (k : ℕ) : Finset (Fin (k + 1) → ℕ) :=
  Fintype.piFinset fun i ↦ Finset.Iic (N i)

private lemma prefixBox_nonempty (N : ℕ → ℕ) (k : ℕ) : (prefixBox N k).Nonempty :=
  ⟨fun _ ↦ 0, Fintype.mem_piFinset.mpr fun _ ↦ Finset.mem_Iic.mpr (Nat.zero_le _)⟩

private lemma biUnion_mem_of_nonempty {ι : Type*} {E : Set (Set α)}
    (hunion : ∀ u ∈ E, ∀ v ∈ E, u ∪ v ∈ E) {s : Finset ι} (hs : s.Nonempty)
    {g : ι → Set α} (hg : ∀ i ∈ s, g i ∈ E) : (⋃ i ∈ s, g i) ∈ E := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simpa using hg a (Finset.mem_singleton_self a)
  | cons a t hat _ ih =>
    have heq : (⋃ i ∈ t.cons a hat, g i) = g a ∪ ⋃ i ∈ t, g i := by ext; simp
    rw [heq]
    exact hunion _ (hg a (Finset.mem_cons_self a t)) _
      (ih fun i hi ↦ hg i (Finset.mem_cons_of_mem hi))

private def prunedSet (f : List ℕ → Set α) (N : ℕ → ℕ) (k : ℕ) : Set α :=
  ⋃ w ∈ prefixBox N k, prefixInter f k w

private lemma prunedSet_mem {E : Set (Set α)} (hunion : ∀ u ∈ E, ∀ v ∈ E, u ∪ v ∈ E)
    (hinter : ∀ u ∈ E, ∀ v ∈ E, u ∩ v ∈ E) {f : List ℕ → Set α} (hf : ∀ l, f l ∈ E)
    (N : ℕ → ℕ) (k : ℕ) : prunedSet f N k ∈ E :=
  biUnion_mem_of_nonempty hunion (prefixBox_nonempty N k) fun w _ ↦ prefixInter_mem hinter hf k w

private lemma prunedSet_anti (f : List ℕ → Set α) (N : ℕ → ℕ) : Antitone (prunedSet f N) := by
  refine antitone_nat_of_succ_le fun k x hx ↦ ?_
  obtain ⟨w, hw, hxw⟩ := mem_iUnion₂.mp hx
  refine mem_iUnion₂.mpr ⟨Fin.init w, ?_, hxw.1⟩
  exact Fintype.mem_piFinset.mpr fun i ↦ Fintype.mem_piFinset.mp hw i.castSucc

private lemma iInter_prunedSet_subset (f : List ℕ → Set α) (N : ℕ → ℕ) :
    (⋂ k, prunedSet f N k) ⊆ souslinOperation f := by
  intro x hx
  let K : ℕ → Set (ℕ → ℕ) := fun k ↦
    {β | ∀ i, β i ≤ N i} ∩ {β | x ∈ prefixInter f k (fun i : Fin (k + 1) ↦ β i)}
  have hbox : IsCompact {β : ℕ → ℕ | ∀ i, β i ≤ N i} := by
    have heq : {β : ℕ → ℕ | ∀ i, β i ≤ N i} = univ.pi fun i ↦ Iic (N i) := by
      ext β; simp [Pi.le_def]
    exact heq ▸ isCompact_univ_pi fun i ↦ (finite_Iic (N i)).isCompact
  have hK_closed (k : ℕ) : IsClosed (K k) :=
    hbox.isClosed.inter <| (isClosed_discrete {w | x ∈ prefixInter f k w}).preimage
      (continuous_pi fun i : Fin (k + 1) ↦
        (continuous_apply (i : ℕ) : Continuous fun β : ℕ → ℕ ↦ β i))
  have hK0_compact : IsCompact (K 0) := hbox.of_isClosed_subset (hK_closed 0) inter_subset_left
  have hK_ne (k : ℕ) : (K k).Nonempty := by
    obtain ⟨w, hw, hxw⟩ := mem_iUnion₂.mp (mem_iInter.mp hx k)
    refine ⟨fun m ↦ if hm : m < k + 1 then w ⟨m, hm⟩ else 0, fun m ↦ ?_, ?_⟩
    · dsimp only
      split_ifs with hm
      · exact Finset.mem_Iic.mp (Fintype.mem_piFinset.mp hw ⟨m, hm⟩)
      · exact Nat.zero_le _
    · have heq : (fun i : Fin (k + 1) ↦ if hm : (i : ℕ) < k + 1 then w ⟨i, hm⟩ else 0) = w :=
        funext fun i ↦ dite_eq_left i.2
      simpa only [mem_ofPred_eq, heq] using hxw
  obtain ⟨β, hβ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K
    (fun k β hβ ↦ ⟨hβ.1, hβ.2.1⟩) hK_ne hK0_compact hK_closed
  exact mem_souslinOperation_iff.mpr
    ⟨β, fun k ↦ mem_of_mem_prefixInter (mem_iInter.mp hβ k).2⟩

-- Choose a bound `M` on coordinate `n` preserving a strict lower bound along upward continuity.
private lemma exists_coord_bound_of_lt {I : Set α → ℝ≥0∞}
    (hiUnion : ∀ A : ℕ → Set α, Monotone A → I (⋃ m, A m) = ⨆ m, I (A m))
    (f : List ℕ → Set α) {a b : ℝ≥0∞} (hab : a < b) (n : ℕ) (T : Set (ℕ → ℕ)) :
    ∃ M : ℕ, b ≤ I (⋃ β ∈ T, ⋂ m : ℕ, f (List.ofFn fun i : Fin (m + 1) ↦ β i)) →
      a ≤ I (⋃ β ∈ T ∩ {β | β n ≤ M}, ⋂ m : ℕ, f (List.ofFn fun i : Fin (m + 1) ↦ β i)) := by
  let S : Set (ℕ → ℕ) → Set α := fun U ↦
    ⋃ β ∈ U, ⋂ m : ℕ, f (List.ofFn fun i : Fin (m + 1) ↦ β i)
  by_cases hT : b ≤ I (S T)
  · have hm : Monotone fun M : ℕ ↦ S (T ∩ {β | β n ≤ M}) := fun _ _ hMM' ↦
      biUnion_mono (inter_subset_inter_right _ fun _ hβ ↦ hβ.trans hMM') fun _ _ ↦ Subset.rfl
    have hu : (⋃ M : ℕ, S (T ∩ {β | β n ≤ M})) = S T := by
      ext x; simp only [S, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
      exact ⟨fun ⟨_, β, ⟨hβ, _⟩, hx⟩ ↦ ⟨β, hβ, hx⟩, fun ⟨β, hβ, hx⟩ ↦ ⟨β n, β, ⟨hβ, le_rfl⟩, hx⟩⟩
    obtain ⟨M, hM⟩ := lt_iSup_iff.mp (by rw [← hiUnion _ hm, hu]; exact hab.trans_le hT)
    exact ⟨M, fun _ ↦ hM.le⟩
  · exact ⟨0, fun h ↦ (hT h).elim⟩

/-- **Strict capacity approximation of Souslin sets over a paving** (Theodorakopoulos, Theorem 2.5).
If `E` is closed under binary unions and intersections and `I : Set α → ℝ≥0∞` is monotone and
upward continuous along increasing countable unions, then for every `s ∈ souslinClosure E` and
`r < I s` there exists an antitone sequence `e : ℕ → Set α` in `E` with `(⋂ k, e k) ⊆ s` and
`r < ⨅ k, I (e k)`. No topology, measurability, or finiteness assumption on `α` or `I` is needed. -/
theorem exists_antitone_mem_of_lt_of_mem_souslinClosure {E : Set (Set α)}
    (hunion : ∀ u ∈ E, ∀ v ∈ E, u ∪ v ∈ E) (hinter : ∀ u ∈ E, ∀ v ∈ E, u ∩ v ∈ E)
    {I : Set α → ℝ≥0∞} (hmono : Monotone I)
    (hiUnion : ∀ A : ℕ → Set α, Monotone A → I (⋃ n, A n) = ⨆ n, I (A n))
    {s : Set α} (hs : s ∈ souslinClosure E) {r : ℝ≥0∞} (hr : r < I s) :
    ∃ e : ℕ → Set α, Antitone e ∧ (∀ k, e k ∈ E) ∧ (⋂ k, e k) ⊆ s ∧ r < ⨅ k, I (e k) := by
  obtain ⟨f, hf, rfl⟩ := hs
  obtain ⟨p, hrp, hp⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hr
  obtain ⟨q, hpq, hq⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp
  let a : ℕ → ℝ≥0 := fun n ↦ p + (q - p) / 2 ^ n
  have ha_lt (n : ℕ) : ((a (n + 1) : ℝ≥0) : ℝ≥0∞) < (a n : ℝ≥0) := by
    refine ENNReal.coe_lt_coe.mpr (add_lt_add_right ?_ p)
    exact div_lt_div_of_pos_left (tsub_pos_of_lt (ENNReal.coe_lt_coe.mp hpq)) (by positivity)
      (pow_lt_pow_right₀ one_lt_two (Nat.lt_succ_self n))
  let S : Set (ℕ → ℕ) → Set α := fun T ↦
    ⋃ β ∈ T, ⋂ m : ℕ, f (List.ofFn fun i : Fin (m + 1) ↦ β i)
  choose Mof hMof using fun n T ↦ exists_coord_bound_of_lt hiUnion f (ha_lt n) n T
  let F : ℕ → Set (ℕ → ℕ) := fun n ↦ Nat.rec univ (fun n Fn ↦ Fn ∩ {β | β n ≤ Mof n Fn}) n
  let N : ℕ → ℕ := fun n ↦ Mof n (F n)
  have hF_mem : ∀ n (β : ℕ → ℕ), β ∈ F n → ∀ k < n, β k ≤ N k := by
    intro n
    induction n with
    | zero => intro _ _ k hk; exact (Nat.not_lt_zero k hk).elim
    | succ n ih =>
      intro β ⟨hpre, hn⟩ k hk
      exact (Nat.lt_succ_iff_lt_or_eq.mp hk).elim (ih β hpre k) (· ▸ hn)
  have hinv : ∀ n, ((a n : ℝ≥0) : ℝ≥0∞) ≤ I (S (F n)) := by
    intro n
    induction n with
    | zero =>
      have ha0 : a 0 = q := by simp [a, add_tsub_cancel_of_le (ENNReal.coe_lt_coe.mp hpq).le]
      have hS0 : S (F 0) = souslinOperation f := by simp [S, F, souslinOperation]
      simpa only [ha0, hS0] using hq.le
    | succ n ih => exact hMof n (F n) ih
  refine ⟨prunedSet f N, prunedSet_anti f N, prunedSet_mem hunion hinter hf N,
    iInter_prunedSet_subset f N, hrp.trans_le (le_iInf fun k ↦ ?_)⟩
  refine (ENNReal.coe_le_coe.mpr le_self_add).trans ((hinv (k + 1)).trans (hmono ?_))
  rintro x hx
  obtain ⟨β, hβF, hxβ⟩ := mem_iUnion₂.mp hx
  exact mem_iUnion₂.mpr ⟨fun i : Fin (k + 1) ↦ β i,
    Fintype.mem_piFinset.mpr fun i ↦ Finset.mem_Iic.mpr (hF_mem (k + 1) β hβF i i.2),
    mem_prefixInter_of_forall (mem_iInter.mp hxβ) k⟩

end TauCeti
