/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.Presentation

/-!
# Back-and-forth equivalence from extension pairs

Mathlib's `Language.IsExtensionPair M N` says that every finitely generated partial equivalence
from `M` to `N` extends to any given element of `M`. In a relational language a pair of tuples with
the same atomic type is the same thing as a finite partial equivalence, so when `M`, `N` form an
extension pair in both directions, the pairs of tuples with the same atomic type form a tuple
back-and-forth system. Consequently atomic-type agreement already gives back-and-forth
equivalence at every ordinal level: the back-and-forth hierarchy between such structures
collapses at level zero. Conversely, an extension pair needs nothing beyond matching one-point
extensions of tuples with the same atomic type, which reduces checking `IsExtensionPair` to a
statement about tuples.

This applies to dense linear orders without endpoints (Mathlib's `dlo_isExtensionPair`), and to
countably generated ultrahomogeneous structures (Mathlib's
`isUltrahomogeneous_iff_IsExtensionPair`).
No countability or nonemptiness is assumed; the agreement on nullary relations needed by the
empty tuples is carried by the given pair of tuples.

## Main results

* `TauCeti.SameAtomicType.exists_snoc_of_isExtensionPair`: matching one-point extensions.
* `TauCeti.isExtensionPair_iff_exists_snoc`: conversely, matching one-point extensions of
  tuples characterize extension pairs.
* `TauCeti.isTupleBFSystem_sameAtomicType`: the atomic-type pairs form a tuple back-and-forth
  system.
* `TauCeti.SameAtomicType.bfEquiv_of_isExtensionPair`: atomic-type agreement implies
  back-and-forth equivalence at every level.
-/

public section

universe u v w w' o

namespace TauCeti

open FirstOrder FirstOrder.Language Fin

variable {L : Language.{u, v}} [L.IsRelational]
variable {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

namespace SameAtomicType

variable {n : ℕ} {a : Fin n → M} {b : Fin n → N}

/-- If every finitely generated partial equivalence from `M` to `N` extends to each element of
`M`, then tuples with the same atomic type have matching one-point extensions on the `M` side. -/
theorem exists_snoc_of_isExtensionPair (h : SameAtomicType (L := L) a b)
    (hMN : L.IsExtensionPair M N) (x : M) :
    ∃ y : N, SameAtomicType (L := L) (snoc a x) (snoc b y) := by
  obtain ⟨f, a', ha, hb, -⟩ := h.exists_fgEquiv
  obtain ⟨g, hx, hfg⟩ := hMN f x
  let c : Fin (n + 1) → g.1.dom :=
    snoc (Substructure.inclusion (PartialEquiv.dom_le_dom hfg) ∘ a') ⟨x, hx⟩
  have hgb (i : Fin n) :
      g.1.toEmbedding (Substructure.inclusion (PartialEquiv.dom_le_dom hfg) (a' i)) = b i :=
    (congrArg Subtype.val (PartialEquiv.toEquiv_inclusion_apply hfg (a' i))).trans (hb i)
  refine ⟨g.1.toEmbedding ⟨x, hx⟩, ?_⟩
  convert g.1.sameAtomicType c using 1 <;> funext i <;> refine lastCases ?_ (fun j => ?_) i
  · simp [c]
  · simpa [c] using (ha j).symm
  · simp [c]
  · simpa [c] using (hgb j).symm

end SameAtomicType

/-- `M` and `N` form an extension pair exactly when tuples with the same atomic type always have
matching one-point extensions on the `M` side. -/
theorem isExtensionPair_iff_exists_snoc :
    L.IsExtensionPair M N ↔ ∀ {n : ℕ} {a : Fin n → M} {b : Fin n → N},
      SameAtomicType (L := L) a b → ∀ x : M, ∃ y : N,
        SameAtomicType (L := L) (snoc a x) (snoc b y) := by
  refine ⟨fun hMN _ _ _ h x => h.exists_snoc_of_isExtensionPair hMN x, fun h => ?_⟩
  refine isExtensionPair_iff_exists_embedding_closure_singleton_sup.mpr fun S hS f x => ?_
  obtain ⟨n, a, rfl⟩ := Substructure.fg_iff_exists_fin_generating_family.mp hS
  -- In a relational language a generated substructure is just the set of its generators.
  have hmem {s : Set M} {z : M} : z ∈ Substructure.closure L s ↔ z ∈ s :=
    Substructure.mem_closure_iff_of_isRelational L s z
  let a' : Fin n → Substructure.closure L (Set.range a) := fun i =>
    ⟨a i, hmem.mpr (Set.mem_range_self i)⟩
  obtain ⟨y, hy⟩ := h (b := f ∘ a')
    (((Substructure.subtype _).sameAtomicType a').symm.trans (f.sameAtomicType a')) x
  -- Enumerate the extended domain by the extended tuple, and embed it along `snoc (f ∘ a') y`.
  let D := Substructure.closure L {x} ⊔ Substructure.closure L (Set.range a)
  have hD {z : M} : z ∈ D ↔ z = x ∨ z ∈ Set.range a := by
    simp only [D]
    rw [← Substructure.closure_union, hmem, Set.mem_union, Set.mem_singleton_iff]
  have hcD (i : Fin (n + 1)) : snoc (α := fun _ => M) a x i ∈ D := by
    induction i using lastCases <;> simp [hD]
  let c : Fin (n + 1) → D := fun i => ⟨snoc (α := fun _ => M) a x i, hcD i⟩
  have hc : Function.Surjective c := by
    rintro ⟨z, hz⟩
    rcases hD.mp hz with rfl | ⟨i, rfl⟩
    · exact ⟨last n, Subtype.ext (by simp [c])⟩
    · exact ⟨i.castSucc, Subtype.ext (by simp [c])⟩
  obtain ⟨g, hg⟩ :=
    (((Substructure.subtype D).sameAtomicType c).trans hy).exists_embedding_comp_eq hc
  refine ⟨g, Embedding.ext fun z => ?_⟩
  obtain ⟨i, hi⟩ := hmem.mp z.property
  obtain rfl : a' i = z := Subtype.ext hi
  have hgi : g (c i.castSucc) = f (a' i) := by simpa using congrFun hg i.castSucc
  rw [Embedding.comp_apply, ← hgi]
  exact congrArg g (Subtype.ext (by simp [c, a']))

/-- When `M` and `N` form an extension pair in both directions and their empty tuples agree (that
is, on the nullary relations), the pairs of tuples with the same atomic type form a tuple
back-and-forth system. -/
theorem isTupleBFSystem_sameAtomicType (hMN : L.IsExtensionPair M N)
    (hNM : L.IsExtensionPair N M)
    (h₀ : SameAtomicType (L := L) (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)) :
    IsTupleBFSystem (L := L)
      {p : Σ n, (Fin n → M) × (Fin n → N) | SameAtomicType (L := L) p.2.1 p.2.2} where
  empty_mem := h₀
  sameAtomicType h := h
  forth h x := h.exists_snoc_of_isExtensionPair hMN x
  back h y := by
    obtain ⟨x, hx⟩ := h.symm.exists_snoc_of_isExtensionPair hNM y
    exact ⟨x, hx.symm⟩

/-- When `M` and `N` form an extension pair in both directions, atomic-type agreement implies
back-and-forth equivalence at every ordinal level. -/
theorem SameAtomicType.bfEquiv_of_isExtensionPair {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : SameAtomicType (L := L) a b)
    (hMN : L.IsExtensionPair M N) (hNM : L.IsExtensionPair N M) (α : Ordinal.{o}) :
    BFEquiv (L := L) α n a b := by
  have h₀ : SameAtomicType (L := L) (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) := by
    convert h.comp Fin.elim0
  exact (isTupleBFSystem_sameAtomicType hMN hNM h₀).bfEquiv α h

end TauCeti
