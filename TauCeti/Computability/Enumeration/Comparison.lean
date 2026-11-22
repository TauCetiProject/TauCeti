/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Enumeration.Stage
public import TauCeti.Computability.RecursiveIn
public import TauCeti.Data.Nat.BitIndices
import Mathlib.Data.Set.Finite.Lattice
import TauCeti.Computability.Primrec.Bitwise

/-!
# Uniform stage comparison for finite-stage enumerations

To compare two finite-stage enumerations `A` and `B`, `TauCeti.Enumeration.stageCompare A B s`
searches for the least stage `t` with `A s ⊆ B t`. Its actual domain is `{s | ∃ t, A s ⊆ B t}`,
it is uniformly recursive in any oracle and stage parameters without totality or directedness
premises, and when `B` is directed under inclusion its totality characterizes
`stageLimit A ⊆ stageLimit B`.

## Main definitions

* `TauCeti.Enumeration.stageCompare`: partial least-stage comparison map searching for the first
  stage `t` with `A s ⊆ B t`.

## Main results

* `TauCeti.Enumeration.stageCompare_def`: unfolding equation of `stageCompare` as `Nat.rfind`.
* `TauCeti.Enumeration.mem_stageCompare`, `TauCeti.Enumeration.stageCompare_dom`: membership and
  domain characterizations.
* `TauCeti.Enumeration.stageLimit_subset_iff_forall_stageCompare_dom`,
  `TauCeti.Enumeration.stageLimit_eq_iff_forall_stageCompare_dom`: totality of `stageCompare`
  characterizes limiting-set inclusion and equality for directed enumerations.
* `TauCeti.Enumeration.recursiveIn_stageCompare`, `TauCeti.Enumeration.partrec_stageCompare`,
  `TauCeti.Enumeration.computableIn_stageCompare_get`,
  `TauCeti.Enumeration.computable_stageCompare_get`,
  `TauCeti.Enumeration.exists_computableIn_stage_comparison`,
  `TauCeti.Enumeration.exists_computable_stage_comparison`: uniform effectivity and total
  stage-transfer maps.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapters II.1–2.
-/

public section

namespace TauCeti.Enumeration

/-- Partial stage comparison: the least stage `t` at which `B t` contains every element of `A s`.
Defined whenever such a stage exists, without requiring totality or directedness in the
definition. -/
def stageCompare (A B : ℕ → Finset ℕ) (s : ℕ) : Part ℕ :=
  Nat.rfind (PFun.lift fun t => decide (A s ⊆ B t))

/-- Unfolding equation for `stageCompare` as least-stage search. -/
theorem stageCompare_def (A B : ℕ → Finset ℕ) (s : ℕ) :
    stageCompare A B s = Nat.rfind (PFun.lift fun t => decide (A s ⊆ B t)) := by
  rw [stageCompare]

/-- `stageCompare A B s` returns the least stage `t` with `A s ⊆ B t`. -/
@[simp]
theorem mem_stageCompare {A B : ℕ → Finset ℕ} {s t : ℕ} :
    t ∈ stageCompare A B s ↔ A s ⊆ B t ∧ ∀ t' < t, ¬ A s ⊆ B t' := by
  rw [stageCompare_def, Nat.mem_rfind]
  simp

/-- Any value returned by `stageCompare A B s` is a stage at which `B` contains `A s`. -/
theorem subset_of_mem_stageCompare {A B : ℕ → Finset ℕ} {s t : ℕ} (h : t ∈ stageCompare A B s) :
    A s ⊆ B t :=
  (mem_stageCompare.1 h).1

/-- `stageCompare A B s` is defined exactly when some stage of `B` contains `A s`. -/
@[simp]
theorem stageCompare_dom {A B : ℕ → Finset ℕ} {s : ℕ} :
    (stageCompare A B s).Dom ↔ ∃ t, A s ⊆ B t := by
  rw [stageCompare_def, Nat.rfind_dom]
  simp

/-- If `B` is directed under inclusion and `stageLimit A ⊆ stageLimit B`, then `stageCompare A B`
is total. -/
theorem stageCompare_dom_of_stageLimit_subset {A B : ℕ → Finset ℕ} (hB : Directed (· ⊆ ·) B)
    (hsub : stageLimit A ⊆ stageLimit B) (s : ℕ) : (stageCompare A B s).Dom := by
  have hB' : Directed (· ⊆ ·) fun t => (B t : Set ℕ) := fun i j => by
    obtain ⟨k, hik, hjk⟩ := hB i j
    exact ⟨k, Finset.coe_subset.2 hik, Finset.coe_subset.2 hjk⟩
  obtain ⟨t, ht⟩ := hB'.exists_mem_subset_of_finset_subset_biUnion (s := A s) fun x hx => by
    rw [← stageLimit_eq_iUnion]
    exact hsub (subset_stageLimit A s hx)
  exact stageCompare_dom.2 ⟨t, Finset.coe_subset.1 ht⟩

/-- For directed `B`, inclusion of limiting sets is equivalent to totality of `stageCompare A B`. -/
theorem stageLimit_subset_iff_forall_stageCompare_dom {A B : ℕ → Finset ℕ}
    (hB : Directed (· ⊆ ·) B) :
    stageLimit A ⊆ stageLimit B ↔ ∀ s, (stageCompare A B s).Dom := by
  refine ⟨fun hsub s => stageCompare_dom_of_stageLimit_subset hB hsub s, fun hdom x hx => ?_⟩
  obtain ⟨s, hs⟩ := mem_stageLimit.1 hx
  obtain ⟨t, ht⟩ := stageCompare_dom.1 (hdom s)
  exact mem_stageLimit.2 ⟨t, ht hs⟩

/-- For directed enumerations, equality of limiting sets is equivalent to totality of both
directions of `stageCompare`. -/
theorem stageLimit_eq_iff_forall_stageCompare_dom {A B : ℕ → Finset ℕ}
    (hA : Directed (· ⊆ ·) A) (hB : Directed (· ⊆ ·) B) :
    stageLimit A = stageLimit B ↔
      (∀ s, (stageCompare A B s).Dom) ∧ (∀ s, (stageCompare B A s).Dom) := by
  rw [Set.Subset.antisymm_iff, stageLimit_subset_iff_forall_stageCompare_dom hB,
    stageLimit_subset_iff_forall_stageCompare_dom hA]

/-- Stage comparison is recursive in `G`, uniformly in all parameters of the two enumerations. -/
theorem recursiveIn_stageCompare {α : Type*} [Primcodable α] {G : Set (ℕ →. ℕ)}
    {A B : α → ℕ → Finset ℕ}
    (hA : ComputableIn G fun p : α × ℕ => Finset.equivBitIndices.symm (A p.1 p.2))
    (hB : ComputableIn G fun p : α × ℕ => Finset.equivBitIndices.symm (B p.1 p.2)) :
    RecursiveIn G fun p : α × ℕ => stageCompare (A p.1) (B p.1) p.2 := by
  have hm : ComputableIn G fun q : (α × ℕ) × ℕ => Finset.equivBitIndices.symm (A q.1.1 q.1.2) :=
    hA.comp ComputableIn.fst
  have hn : ComputableIn G fun q : (α × ℕ) × ℕ => Finset.equivBitIndices.symm (B q.1.1 q.2) :=
    hB.comp ((ComputableIn.fst.comp ComputableIn.fst).pair ComputableIn.snd)
  have hcmp : Primrec fun p : ℕ × ℕ => decide (p.1 &&& p.2 = p.1) :=
    Primrec.eq.decide.comp Primrec.nat_land Primrec.fst
  have htest : ComputableIn G fun q : (α × ℕ) × ℕ => decide (A q.1.1 q.1.2 ⊆ B q.1.1 q.2) :=
    RecursiveIn.of_eq (hcmp.computableIn.comp (hm.pair hn)) fun q => by
      simp only [← Finset.equivBitIndices_subset_iff, Equiv.apply_symm_apply]
  exact (RecursiveIn.rfind (ComputableIn₂.recursiveIn₂ (f := fun (p : α × ℕ) t =>
    decide (A p.1 p.2 ⊆ B p.1 t)) htest)).of_eq fun p => by
      rw [stageCompare_def]

/-- Stage comparison is partial computable, uniformly in all parameters of the two enumerations. -/
theorem partrec_stageCompare {α : Type*} [Primcodable α] {A B : α → ℕ → Finset ℕ}
    (hA : Computable fun p : α × ℕ => Finset.equivBitIndices.symm (A p.1 p.2))
    (hB : Computable fun p : α × ℕ => Finset.equivBitIndices.symm (B p.1 p.2)) :
    Partrec fun p : α × ℕ => stageCompare (A p.1) (B p.1) p.2 :=
  recursiveIn_empty_iff.1 (recursiveIn_stageCompare hA.computableIn hB.computableIn)

/-- Totality corollary: whenever `stageCompare` is total across a uniformly oracle-computable
family of pairs of enumerations, the resulting stage-transfer map is total and oracle-computable. -/
theorem computableIn_stageCompare_get {α : Type*} [Primcodable α] {G : Set (ℕ →. ℕ)}
    {A B : α → ℕ → Finset ℕ}
    (hA : ComputableIn G fun p : α × ℕ => Finset.equivBitIndices.symm (A p.1 p.2))
    (hB : ComputableIn G fun p : α × ℕ => Finset.equivBitIndices.symm (B p.1 p.2))
    (hdom : ∀ a s, (stageCompare (A a) (B a) s).Dom) :
    ComputableIn G fun p : α × ℕ => (stageCompare (A p.1) (B p.1) p.2).get (hdom p.1 p.2) :=
  (recursiveIn_stageCompare hA hB).of_eq_tot fun p => Part.get_mem (hdom p.1 p.2)

/-- Totality corollary: whenever `stageCompare` is total across a uniformly computable family of
pairs of enumerations, the resulting stage-transfer map is total and computable. -/
theorem computable_stageCompare_get {α : Type*} [Primcodable α] {A B : α → ℕ → Finset ℕ}
    (hA : Computable fun p : α × ℕ => Finset.equivBitIndices.symm (A p.1 p.2))
    (hB : Computable fun p : α × ℕ => Finset.equivBitIndices.symm (B p.1 p.2))
    (hdom : ∀ a s, (stageCompare (A a) (B a) s).Dom) :
    Computable fun p : α × ℕ => (stageCompare (A p.1) (B p.1) p.2).get (hdom p.1 p.2) :=
  TauCeti.computableIn_empty_iff.1
    (computableIn_stageCompare_get hA.computableIn hB.computableIn hdom)

/-- Uniformly oracle-computable families of directed enumerations with equal limiting sets admit
jointly oracle-computable stage-comparison maps witnessing both inclusions
`A a s ⊆ B a (f (a, s))` and `B a s ⊆ A a (g (a, s))`. -/
theorem exists_computableIn_stage_comparison {α : Type*} [Primcodable α] {G : Set (ℕ →. ℕ)}
    {A B : α → ℕ → Finset ℕ}
    (hA_dir : ∀ a, Directed (· ⊆ ·) (A a)) (hB_dir : ∀ a, Directed (· ⊆ ·) (B a))
    (hA : ComputableIn G fun p : α × ℕ => Finset.equivBitIndices.symm (A p.1 p.2))
    (hB : ComputableIn G fun p : α × ℕ => Finset.equivBitIndices.symm (B p.1 p.2))
    (heq : ∀ a, stageLimit (A a) = stageLimit (B a)) :
    ∃ f g : α × ℕ → ℕ, ComputableIn G f ∧ ComputableIn G g ∧
      (∀ a s, A a s ⊆ B a (f (a, s))) ∧ (∀ a s, B a s ⊆ A a (g (a, s))) := by
  have hdomAB : ∀ a s, (stageCompare (A a) (B a) s).Dom :=
    fun a s => stageCompare_dom_of_stageLimit_subset (hB_dir a) (heq a).le s
  have hdomBA : ∀ a s, (stageCompare (B a) (A a) s).Dom :=
    fun a s => stageCompare_dom_of_stageLimit_subset (hA_dir a) (heq a).ge s
  exact ⟨_, _, computableIn_stageCompare_get hA hB hdomAB,
    computableIn_stageCompare_get hB hA hdomBA,
    fun a s => subset_of_mem_stageCompare (Part.get_mem (hdomAB a s)),
    fun a s => subset_of_mem_stageCompare (Part.get_mem (hdomBA a s))⟩

/-- Uniformly computable families of directed enumerations with equal limiting sets admit jointly
computable stage-comparison maps witnessing both inclusions `A a s ⊆ B a (f (a, s))` and
`B a s ⊆ A a (g (a, s))`. -/
theorem exists_computable_stage_comparison {α : Type*} [Primcodable α] {A B : α → ℕ → Finset ℕ}
    (hA_dir : ∀ a, Directed (· ⊆ ·) (A a)) (hB_dir : ∀ a, Directed (· ⊆ ·) (B a))
    (hA : Computable fun p : α × ℕ => Finset.equivBitIndices.symm (A p.1 p.2))
    (hB : Computable fun p : α × ℕ => Finset.equivBitIndices.symm (B p.1 p.2))
    (heq : ∀ a, stageLimit (A a) = stageLimit (B a)) :
    ∃ f g : α × ℕ → ℕ, Computable f ∧ Computable g ∧
      (∀ a s, A a s ⊆ B a (f (a, s))) ∧ (∀ a s, B a s ⊆ A a (g (a, s))) := by
  obtain ⟨f, g, hf, hg, hfg, hgf⟩ := exists_computableIn_stage_comparison (G := ∅)
    hA_dir hB_dir hA.computableIn hB.computableIn heq
  exact ⟨f, g, TauCeti.computableIn_empty_iff.1 hf, TauCeti.computableIn_empty_iff.1 hg, hfg, hgf⟩

end TauCeti.Enumeration
