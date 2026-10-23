/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Order.Lattice.Submodular
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Order.Sublattice
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Tactic.FinCases

/-!
# Terminal-set minimum cuts

A terminal cut is a finite vertex set containing all source terminals and no sink terminals.
For a set function with linearly ordered values on a finite vertex type, disjoint terminal
sets guarantee attainment of a minimum. For a submodular function, the minimizing sides form
a distributive sublattice under inclusion; on a finite vertex type with linearly ordered
values, it is finite, with a smallest and a largest side. These extremal sides describe which
vertices occur in every minimum cut and which occur in at least one.

For two vertices, `pairMinimumValue f s t` is the minimum cut value `λ(s, t)`, with `λ(s, s) = 0`.
It satisfies the ultrametric inequality `min (λ(s, v)) (λ(v, t)) ≤ λ(s, t)` for distinct `s, t`.

The theory is independent of a graph representation and does not require symmetry of the
set function. Either terminal set may be empty.
-/

public section

namespace TauCeti.TerminalCut

open Finset

variable {V W K : Type*}

/-- An admissible source side contains `A` and avoids `B`. -/
def IsAdmissible (A B S : Finset V) : Prop := A ⊆ S ∧ Disjoint S B

/-- The characteristic conditions for a terminal cut. -/
theorem isAdmissible_iff {A B S : Finset V} :
    IsAdmissible A B S ↔ A ⊆ S ∧ Disjoint S B := Iff.rfl

/-- Every source terminal belongs to an admissible side. -/
theorem IsAdmissible.subset {A B S : Finset V} (hS : IsAdmissible A B S) : A ⊆ S := hS.1

/-- An admissible side contains no sink terminal. -/
theorem IsAdmissible.disjoint {A B S : Finset V} (hS : IsAdmissible A B S) :
    Disjoint S B := hS.2

/-- With a finite vertex type, admissible sides form the interval from `A` to `Bᶜ`. -/
theorem isAdmissible_iff_mem_Icc [DecidableEq V] [Fintype V] {A B S : Finset V} :
    IsAdmissible A B S ↔ S ∈ Set.Icc A Bᶜ := by
  simp [isAdmissible_iff, Finset.disjoint_left, Finset.subset_iff]

/-- Complementing a source side exchanges the source and sink terminal sets. -/
@[simp]
theorem isAdmissible_compl_iff [Fintype V] [DecidableEq V] {A B S : Finset V} :
    IsAdmissible B A Sᶜ ↔ IsAdmissible A B S := by
  rw [isAdmissible_iff_mem_Icc, isAdmissible_iff_mem_Icc]
  constructor
  · rintro ⟨hB, hA⟩
    exact ⟨compl_le_compl_iff_le.mp hA, le_compl_comm.mp hB⟩
  · rintro ⟨hA, hB⟩
    exact ⟨le_compl_comm.mp hB, compl_le_compl_iff_le.mpr hA⟩

/-- The complement of an admissible side is admissible for the exchanged terminal sets. -/
theorem IsAdmissible.compl [Fintype V] [DecidableEq V] {A B S : Finset V}
    (hS : IsAdmissible A B S) : IsAdmissible B A Sᶜ :=
  isAdmissible_compl_iff.mpr hS

/-- Disjoint terminal sets admit the source terminal set itself as a cut. -/
theorem isAdmissible_self {A B : Finset V} (hAB : Disjoint A B) :
    IsAdmissible A B A := ⟨Subset.rfl, hAB⟩

/-- Admissibility is closed under union. -/
theorem IsAdmissible.union [DecidableEq V] {A B S T : Finset V}
    (hS : IsAdmissible A B S) (hT : IsAdmissible A B T) :
    IsAdmissible A B (S ∪ T) :=
  ⟨hS.1.trans subset_union_left, disjoint_union_left.mpr ⟨hS.2, hT.2⟩⟩

/-- Admissibility is closed under intersection. -/
theorem IsAdmissible.inter [DecidableEq V] {A B S T : Finset V}
    (hS : IsAdmissible A B S) (hT : IsAdmissible A B T) :
    IsAdmissible A B (S ∩ T) :=
  ⟨subset_inter hS.1 hT.1, hS.2.mono_left inter_subset_left⟩

/-- For disjoint terminal sets, adding `A` to any vertex set and removing `B` gives an admissible
side. -/
theorem isAdmissible_union_sdiff [DecidableEq V] {A B : Finset V} (hAB : Disjoint A B)
    (S : Finset V) : IsAdmissible A B ((S ∪ A) \ B) :=
  ⟨fun _ ha ↦ mem_sdiff.mpr ⟨mem_union_right S ha, disjoint_left.mp hAB ha⟩, sdiff_disjoint⟩

/-- A minimum terminal cut is an admissible side minimizing `f` over all admissible sides. -/
def IsMinimum [Preorder K] (f : Finset V → K) (A B S : Finset V) : Prop :=
  IsAdmissible A B S ∧ IsMinOn f {T | IsAdmissible A B T} S

/-- Membership and optimality characterize a minimum terminal cut. -/
theorem isMinimum_iff [Preorder K] {f : Finset V → K} {A B S : Finset V} :
    IsMinimum f A B S ↔
      IsAdmissible A B S ∧ ∀ T, IsAdmissible A B T → f S ≤ f T :=
  and_congr_right fun _ ↦ isMinOn_iff

/-- Every minimum side is an admissible cut. -/
theorem IsMinimum.admissible [Preorder K] {f : Finset V → K} {A B S : Finset V}
    (hS : IsMinimum f A B S) : IsAdmissible A B S := hS.1

/-- The value at a minimum side bounds the value at any admissible cut. -/
theorem IsMinimum.le [Preorder K] {f : Finset V → K} {A B S T : Finset V}
    (hS : IsMinimum f A B S) (hT : IsAdmissible A B T) : f S ≤ f T :=
  isMinOn_iff.mp hS.2 T hT

/-- All minimum cuts have the same value. -/
theorem IsMinimum.value_eq [PartialOrder K] {f : Finset V → K} {A B S T : Finset V}
    (hS : IsMinimum f A B S) (hT : IsMinimum f A B T) : f S = f T :=
  le_antisymm (hS.le hT.admissible) (hT.le hS.admissible)

/-- On a finite vertex type, disjoint terminal sets have an attaining minimum cut. -/
theorem exists_minimum [Finite V] [LinearOrder K] (f : Finset V → K)
    {A B : Finset V} (hAB : Disjoint A B) : ∃ S, IsMinimum f A B S := by
  let := Fintype.ofFinite V
  obtain ⟨S, hS, hmin⟩ := Set.exists_min_image {S | IsAdmissible A B S} f
    (Set.toFinite _) ⟨A, isAdmissible_self hAB⟩
  exact ⟨S, hS, isMinOn_iff.mpr hmin⟩

section Value

variable [Finite V] [LinearOrder K] (f : Finset V → K) {A B : Finset V}

/-- The attained minimum value among cuts separating the disjoint terminal sets. -/
noncomputable def minimumValue (hAB : Disjoint A B) : K :=
  f (Classical.choose (exists_minimum f hAB))

/-- The minimum value is no larger than the value of any admissible cut. -/
theorem minimumValue_le (hAB : Disjoint A B) {S : Finset V}
    (hS : IsAdmissible A B S) : minimumValue f hAB ≤ f S :=
  (Classical.choose_spec (exists_minimum f hAB)).le hS

/-- An admissible side is minimum exactly when its value is the minimum value. -/
theorem isMinimum_iff_value_eq (hAB : Disjoint A B) {S : Finset V} :
    IsMinimum f A B S ↔ IsAdmissible A B S ∧ f S = minimumValue f hAB := by
  constructor
  · intro hS
    exact ⟨hS.admissible, hS.value_eq (Classical.choose_spec (exists_minimum f hAB))⟩
  · rintro ⟨hS, heq⟩
    exact isMinimum_iff.mpr ⟨hS, fun T hT ↦ heq.le.trans (minimumValue_le f hAB hT)⟩

end Value

/-- An injective relabeling preserves the conditions on terminal cuts. -/
@[simp] theorem isAdmissible_map_iff (e : V ↪ W) {A B S : Finset V} :
    IsAdmissible (A.map e) (B.map e) (S.map e) ↔ IsAdmissible A B S := by
  simp [isAdmissible_iff, Finset.map_subset_map, Finset.disjoint_map]

/-- Relabeling all vertices preserves minimum cuts whenever it preserves the set function. -/
theorem isMinimum_map_iff [Preorder K] (e : V ≃ W)
    {f : Finset V → K} {g : Finset W → K}
    (hfg : ∀ S, g (S.map e.toEmbedding) = f S) {A B S : Finset V} :
    IsMinimum g (A.map e.toEmbedding) (B.map e.toEmbedding) (S.map e.toEmbedding) ↔
      IsMinimum f A B S := by
  constructor
  · intro hS
    refine isMinimum_iff.mpr
      ⟨(isAdmissible_map_iff e.toEmbedding).mp hS.admissible, fun T hT ↦ ?_⟩
    simpa only [hfg] using hS.le ((isAdmissible_map_iff e.toEmbedding).mpr hT)
  · intro hS
    refine isMinimum_iff.mpr
      ⟨(isAdmissible_map_iff e.toEmbedding).mpr hS.admissible, fun T hT ↦ ?_⟩
    have hT' : IsAdmissible A B (T.map e.symm.toEmbedding) := by
      simpa [Finset.map_map] using (isAdmissible_map_iff e.symm.toEmbedding).mpr hT
    simpa [← hfg, Finset.map_map] using hS.le hT'

/-- Relabeling vertices does not change the minimum cut value. -/
theorem minimumValue_map [Finite V] [Finite W] [LinearOrder K] (e : V ≃ W)
    {f : Finset V → K} {g : Finset W → K}
    (hfg : ∀ S, g (S.map e.toEmbedding) = f S) {A B : Finset V}
    (hAB : Disjoint A B) :
    minimumValue g ((Finset.disjoint_map e.toEmbedding).mpr hAB) = minimumValue f hAB := by
  obtain ⟨S, hS⟩ := exists_minimum f hAB
  have hm := (isMinimum_map_iff e hfg).mpr hS
  rw [← ((isMinimum_iff_value_eq g _).mp hm).2,
    ← ((isMinimum_iff_value_eq f hAB).mp hS).2, hfg]

section Lattice

variable [DecidableEq V] [AddCommMonoid K] [PartialOrder K] [IsOrderedCancelAddMonoid K]
variable {f : Finset V → K} (hf : IsSubmodular f) (A B : Finset V)

/-- The minimum terminal cuts, as a sublattice of finite vertex sets. Its induced lattice is
distributive, and is finite when the vertex type is finite. -/
def minimizers : Sublattice (Finset V) :=
  Sublattice.ofIsSublattice _ (hf.isSublattice_minimizers
    (s := {T | IsAdmissible A B T})
    ⟨fun _ hS _ hT ↦ hS.union hT, fun _ hS _ hT ↦ hS.inter hT⟩)

/-- Membership in the cut lattice is precisely minimum-cut optimality. -/
@[simp] theorem mem_minimizers {S : Finset V} :
    S ∈ minimizers hf A B ↔ IsMinimum f A B S := Iff.rfl

include hf

/-- The union of minimum cuts is minimum. -/
theorem IsMinimum.union {A B S T : Finset V}
    (hS : IsMinimum f A B S) (hT : IsMinimum f A B T) :
    IsMinimum f A B (S ∪ T) :=
  (mem_minimizers hf A B).mp ((minimizers hf A B).sup_mem hS hT)

/-- The intersection of minimum cuts is minimum. -/
theorem IsMinimum.inter {A B S T : Finset V}
    (hS : IsMinimum f A B S) (hT : IsMinimum f A B T) :
    IsMinimum f A B (S ∩ T) :=
  (mem_minimizers hf A B).mp ((minimizers hf A B).inf_mem hS hT)

/-- A value-preserving vertex equivalence identifies the lattices of minimum cuts. -/
def minimizersOrderIso [DecidableEq W] (e : V ≃ W) {g : Finset W → K}
    (hg : IsSubmodular g) (hfg : ∀ S, g (S.map e.toEmbedding) = f S) :
    minimizers hf A B ≃o minimizers hg (A.map e.toEmbedding) (B.map e.toEmbedding) where
  toEquiv := e.finsetCongr.subtypeEquiv fun _ ↦ (isMinimum_map_iff e hfg).symm
  map_rel_iff' := Finset.map_subset_map

/-- The minimum-cut order isomorphism maps each source side by the vertex equivalence. -/
@[simp] theorem minimizersOrderIso_apply [DecidableEq W] (e : V ≃ W)
    {g : Finset W → K} (hg : IsSubmodular g)
    (hfg : ∀ S, g (S.map e.toEmbedding) = f S) (S : minimizers hf A B) :
    (minimizersOrderIso hf A B e hg hfg S : Finset W) = (S : Finset V).map e.toEmbedding :=
  (rfl)

/-- The inverse minimum-cut isomorphism relabels by the inverse vertex equivalence. -/
@[simp] theorem minimizersOrderIso_symm_apply [DecidableEq W] (e : V ≃ W)
    {g : Finset W → K} (hg : IsSubmodular g)
    (hfg : ∀ S, g (S.map e.toEmbedding) = f S)
    (S : minimizers hg (A.map e.toEmbedding) (B.map e.toEmbedding)) :
    ((minimizersOrderIso hf A B e hg hfg).symm S : Finset V) =
      (S : Finset W).map e.symm.toEmbedding := (rfl)

end Lattice

section Extremal

variable [DecidableEq V] [Finite V] [AddCommMonoid K] [LinearOrder K]
  [IsOrderedCancelAddMonoid K]
variable {f : Finset V → K} (hf : IsSubmodular f) {A B : Finset V}

include hf

/-- The finite nonempty lattice of minimum cuts has bottom and top elements. -/
noncomputable abbrev minimizersBoundedOrder (hAB : Disjoint A B) :
    BoundedOrder (minimizers hf A B) := by
  let := Fintype.ofFinite V
  let L := minimizers hf A B
  let : Fintype L := Fintype.ofFinite L
  have : Nonempty L := by
    obtain ⟨S, hS⟩ := exists_minimum f hAB
    exact ⟨⟨S, (mem_minimizers hf A B).mpr hS⟩⟩
  exact Fintype.toBoundedOrder L

/-- Minimum terminal cuts have a least side under inclusion. -/
theorem exists_isLeast (hAB : Disjoint A B) :
    ∃ S, IsLeast {T | IsMinimum f A B T} S := by
  let L := minimizers hf A B
  let := minimizersBoundedOrder hf hAB
  refine ⟨(⊥ : L), (⊥ : L).property, fun T hT ↦ ?_⟩
  exact Subtype.coe_le_coe.mpr (bot_le (a := (⟨T, hT⟩ : L)))

/-- Minimum terminal cuts have a greatest side under inclusion. -/
theorem exists_isGreatest (hAB : Disjoint A B) :
    ∃ S, IsGreatest {T | IsMinimum f A B T} S := by
  let L := minimizers hf A B
  let := minimizersBoundedOrder hf hAB
  refine ⟨(⊤ : L), (⊤ : L).property, fun T hT ↦ ?_⟩
  exact Subtype.coe_le_coe.mpr (le_top (a := (⟨T, hT⟩ : L)))

/-- The smallest minimum source side. -/
noncomputable def smallest (hAB : Disjoint A B) : Finset V :=
  Classical.choose (exists_isLeast hf hAB)

/-- The largest minimum source side. -/
noncomputable def largest (hAB : Disjoint A B) : Finset V :=
  Classical.choose (exists_isGreatest hf hAB)

/-- The smallest side is minimum and contained in every minimum side. -/
theorem isLeast_smallest (hAB : Disjoint A B) :
    IsLeast {T | IsMinimum f A B T} (smallest hf hAB) :=
  Classical.choose_spec (exists_isLeast hf hAB)

/-- The largest side is minimum and contains every minimum side. -/
theorem isGreatest_largest (hAB : Disjoint A B) :
    IsGreatest {T | IsMinimum f A B T} (largest hf hAB) :=
  Classical.choose_spec (exists_isGreatest hf hAB)

/-- The smallest minimum side belongs to the minimizer lattice. -/
theorem smallest_mem_minimizers (hAB : Disjoint A B) :
    smallest hf hAB ∈ minimizers hf A B :=
  (mem_minimizers hf A B).mpr (isLeast_smallest hf hAB).1

/-- The largest minimum side belongs to the minimizer lattice. -/
theorem largest_mem_minimizers (hAB : Disjoint A B) :
    largest hf hAB ∈ minimizers hf A B :=
  (mem_minimizers hf A B).mpr (isGreatest_largest hf hAB).1

/-- The least property characterizes the smallest side uniquely. -/
theorem smallest_eq_iff (hAB : Disjoint A B) {S : Finset V} :
    smallest hf hAB = S ↔ IsLeast {T | IsMinimum f A B T} S :=
  ⟨fun h ↦ h ▸ isLeast_smallest hf hAB, fun h ↦ (isLeast_smallest hf hAB).unique h⟩

/-- The greatest property characterizes the largest side uniquely. -/
theorem largest_eq_iff (hAB : Disjoint A B) {S : Finset V} :
    largest hf hAB = S ↔ IsGreatest {T | IsMinimum f A B T} S :=
  ⟨fun h ↦ h ▸ isGreatest_largest hf hAB, fun h ↦ (isGreatest_largest hf hAB).unique h⟩

/-- The bottom of the bounded minimizer lattice is the smallest minimum source side. -/
@[simp] theorem coe_bot_minimizers (hAB : Disjoint A B) :
    letI := minimizersBoundedOrder hf hAB
    ((⊥ : minimizers hf A B) : Finset V) = smallest hf hAB := by
  let := minimizersBoundedOrder hf hAB
  symm
  apply (smallest_eq_iff hf hAB).mpr
  exact ⟨(⊥ : minimizers hf A B).property, fun T hT ↦
    Subtype.coe_le_coe.mpr (bot_le (a := (⟨T, hT⟩ : minimizers hf A B)))⟩

/-- The top of the bounded minimizer lattice is the largest minimum source side. -/
@[simp] theorem coe_top_minimizers (hAB : Disjoint A B) :
    letI := minimizersBoundedOrder hf hAB
    ((⊤ : minimizers hf A B) : Finset V) = largest hf hAB := by
  let := minimizersBoundedOrder hf hAB
  symm
  apply (largest_eq_iff hf hAB).mpr
  exact ⟨(⊤ : minimizers hf A B).property, fun T hT ↦
    Subtype.coe_le_coe.mpr (le_top (a := (⟨T, hT⟩ : minimizers hf A B)))⟩

/-- Relabeling vertices transports the smallest minimum source side. -/
theorem smallest_map [DecidableEq W] [Finite W] (e : V ≃ W)
    {g : Finset W → K} (hg : IsSubmodular g)
    (hfg : ∀ S, g (S.map e.toEmbedding) = f S) (hAB : Disjoint A B) :
    smallest hg ((Finset.disjoint_map e.toEmbedding).mpr hAB) =
      (smallest hf hAB).map e.toEmbedding := by
  apply (smallest_eq_iff hg _).mpr
  refine ⟨(isMinimum_map_iff e hfg).mpr (isLeast_smallest hf hAB).1, ?_⟩
  intro T hT
  obtain ⟨S, rfl⟩ := e.finsetCongr.surjective T
  exact Finset.map_subset_map.mpr
    ((isLeast_smallest hf hAB).2 ((isMinimum_map_iff e hfg).mp hT))

/-- Relabeling vertices transports the largest minimum source side. -/
theorem largest_map [DecidableEq W] [Finite W] (e : V ≃ W)
    {g : Finset W → K} (hg : IsSubmodular g)
    (hfg : ∀ S, g (S.map e.toEmbedding) = f S) (hAB : Disjoint A B) :
    largest hg ((Finset.disjoint_map e.toEmbedding).mpr hAB) =
      (largest hf hAB).map e.toEmbedding := by
  apply (largest_eq_iff hg _).mpr
  refine ⟨(isMinimum_map_iff e hfg).mpr (isGreatest_largest hf hAB).1, ?_⟩
  intro T hT
  obtain ⟨S, rfl⟩ := e.finsetCongr.surjective T
  exact Finset.map_subset_map.mpr
    ((isGreatest_largest hf hAB).2 ((isMinimum_map_iff e hfg).mp hT))

/-- A vertex belongs to the smallest cut exactly when it belongs to every minimum cut. -/
@[simp] theorem mem_smallest_iff (hAB : Disjoint A B) {v : V} :
    v ∈ smallest hf hAB ↔ ∀ S, IsMinimum f A B S → v ∈ S := by
  constructor
  · exact fun hv S hS ↦ (isLeast_smallest hf hAB).2 hS hv
  · exact fun h ↦ h _ (isLeast_smallest hf hAB).1

/-- A vertex belongs to the largest cut exactly when it belongs to some minimum cut. -/
@[simp] theorem mem_largest_iff (hAB : Disjoint A B) {v : V} :
    v ∈ largest hf hAB ↔ ∃ S, IsMinimum f A B S ∧ v ∈ S := by
  constructor
  · exact fun hv ↦ ⟨_, (isGreatest_largest hf hAB).1, hv⟩
  · rintro ⟨S, hS, hv⟩
    exact (isGreatest_largest hf hAB).2 hS hv

/-- There is a unique minimum cut exactly when the smallest and largest sides agree. -/
theorem existsUnique_minimum_iff (hAB : Disjoint A B) :
    (∃! S, IsMinimum f A B S) ↔ smallest hf hAB = largest hf hAB := by
  constructor
  · rintro ⟨S, _, hS⟩
    exact (hS _ (isLeast_smallest hf hAB).1).trans
      (hS _ (isGreatest_largest hf hAB).1).symm
  · intro heq
    refine ⟨smallest hf hAB, (isLeast_smallest hf hAB).1, fun S hS ↦ ?_⟩
    exact le_antisymm (heq ▸ (isGreatest_largest hf hAB).2 hS)
      ((isLeast_smallest hf hAB).2 hS)

end Extremal

/-- Singleton terminal sets recover the usual source-membership and sink-exclusion conditions. -/
@[simp] theorem isAdmissible_singleton {s t : V} {S : Finset V} :
    IsAdmissible {s} {t} S ↔ s ∈ S ∧ t ∉ S := by
  classical
  simp [isAdmissible_iff]

/-- A minimum cut for a pair of singleton terminal sets has the usual source-membership,
sink-exclusion, and optimality characterization. -/
theorem isMinimum_singleton_iff [Preorder K] {f : Finset V → K} {s t : V}
    {S : Finset V} :
    IsMinimum f {s} {t} S ↔
      s ∈ S ∧ t ∉ S ∧ ∀ T, s ∈ T → t ∉ T → f S ≤ f T := by
  simp only [isMinimum_iff, isAdmissible_singleton]
  aesop

section PairValue

variable [Finite V] [Zero K] [LinearOrder K] (f : Finset V → K)

open scoped Classical in
/-- The minimum cut value `λ(s, t)` between two vertices: the minimum value of a cut containing
`s` and not `t` when `s ≠ t`, and zero on the diagonal. -/
noncomputable def pairMinimumValue (s t : V) : K :=
  if h : s = t then 0 else minimumValue f (disjoint_singleton.mpr h)

/-- The minimum cut value between a vertex and itself is zero by convention. -/
@[simp] theorem pairMinimumValue_self (s : V) : pairMinimumValue f s s = 0 := by
  simp [pairMinimumValue]

/-- Between distinct vertices, the minimum cut value is that of the singleton terminal sets. -/
theorem pairMinimumValue_of_ne {s t : V} (hst : s ≠ t) :
    pairMinimumValue f s t = minimumValue f (disjoint_singleton.mpr hst) := by
  simp [pairMinimumValue, hst]

/-- The minimum cut value between two vertices is no larger than the value of any cut
separating them. -/
theorem pairMinimumValue_le {s t : V} {S : Finset V} (hs : s ∈ S) (ht : t ∉ S) :
    pairMinimumValue f s t ≤ f S := by
  have hst : s ≠ t := fun h ↦ ht (h ▸ hs)
  rw [pairMinimumValue_of_ne f hst]
  exact minimumValue_le f _ (isAdmissible_singleton.mpr ⟨hs, ht⟩)

/-- A minimum cut between two vertices attains their minimum cut value. -/
theorem IsMinimum.pairMinimumValue_eq {f : Finset V → K} {s t : V} {S : Finset V}
    (hS : IsMinimum f {s} {t} S) : pairMinimumValue f s t = f S := by
  obtain ⟨hs, ht⟩ := isAdmissible_singleton.mp hS.admissible
  have hst : s ≠ t := fun h ↦ ht (h ▸ hs)
  rw [pairMinimumValue_of_ne f hst]
  exact (((isMinimum_iff_value_eq f _).mp hS).2).symm

/-- A cut separating two vertices is minimum exactly when it attains their minimum cut value. -/
theorem isMinimum_singleton_iff_pairMinimumValue_eq {s t : V} {S : Finset V} :
    IsMinimum f {s} {t} S ↔ s ∈ S ∧ t ∉ S ∧ f S = pairMinimumValue f s t := by
  refine ⟨fun hS ↦ ?_, fun ⟨hs, ht, heq⟩ ↦ ?_⟩
  · exact ⟨(isAdmissible_singleton.mp hS.admissible).1,
      (isAdmissible_singleton.mp hS.admissible).2, hS.pairMinimumValue_eq.symm⟩
  · exact isMinimum_singleton_iff.mpr ⟨hs, ht, fun T hsT htT ↦
      heq.le.trans (pairMinimumValue_le f hsT htT)⟩

/-- **Ultrametric inequality** for minimum cut values: every cut separating `s` from `t`
separates `s` from `v` or `v` from `t`. The intermediate vertex `v` is arbitrary. -/
theorem min_pairMinimumValue_le {s t : V} (hst : s ≠ t) (v : V) :
    min (pairMinimumValue f s v) (pairMinimumValue f v t) ≤ pairMinimumValue f s t := by
  obtain ⟨S, hS⟩ := exists_minimum f (disjoint_singleton.mpr hst)
  obtain ⟨hs, ht⟩ := isAdmissible_singleton.mp hS.admissible
  rw [hS.pairMinimumValue_eq]
  by_cases hv : v ∈ S
  · exact min_le_of_right_le (pairMinimumValue_le f hv ht)
  · exact min_le_of_left_le (pairMinimumValue_le f hs hv)

end PairValue

/-!
## Examples

On six vertices, charge one unit for including vertex `4`, and nothing for the other vertices.
With sources `0, 1` and sinks `2, 3`, the two minimum source sides are `{0, 1}` and `{0, 1, 5}`.
This nonconstant modular function also illustrates that empty terminal sets cause no exception
to attainment or to the smallest and largest cut formulas.
-/

private def cost (S : Finset (Fin 6)) : ℕ := if 4 ∈ S then 1 else 0

private theorem submodular_cost : IsSubmodular cost := by
  rw [isSubmodular_def]
  intro S T
  by_cases hS : 4 ∈ S <;> by_cases hT : 4 ∈ T <;> simp [cost, hS, hT]

private theorem minimum_cost_iff {A B S : Finset (Fin 6)}
    (hAB : Disjoint A B) (hA : 4 ∉ A) :
    IsMinimum cost A B S ↔ IsAdmissible A B S ∧ 4 ∉ S := by
  constructor
  · intro hS
    refine ⟨hS.admissible, ?_⟩
    have := hS.le (isAdmissible_self hAB)
    simpa [cost, hA] using this
  · rintro ⟨hS, h4⟩
    refine isMinimum_iff.mpr ⟨hS, fun T _ ↦ ?_⟩
    simp [cost, h4]

private theorem smallest_cost {A B : Finset (Fin 6)}
    (hAB : Disjoint A B) (hA : 4 ∉ A) : smallest submodular_cost hAB = A := by
  apply (smallest_eq_iff submodular_cost hAB).mpr
  exact ⟨(minimum_cost_iff hAB hA).mpr ⟨isAdmissible_self hAB, hA⟩,
    fun S hS ↦ hS.admissible.subset⟩

private theorem largest_cost {A B : Finset (Fin 6)}
    (hAB : Disjoint A B) (hA : 4 ∉ A) :
    largest submodular_cost hAB = (B ∪ {4})ᶜ := by
  apply (largest_eq_iff submodular_cost hAB).mpr
  constructor
  · apply (minimum_cost_iff hAB hA).mpr
    simp only [isAdmissible_iff, Finset.subset_iff, mem_compl, mem_union, mem_singleton]
    refine ⟨⟨fun v hv ↦ ?_, ?_⟩, by simp⟩
    · exact not_or.mpr ⟨Finset.disjoint_left.mp hAB hv, fun h ↦ hA (h ▸ hv)⟩
    · apply Finset.disjoint_left.mpr
      intro v hv hvB
      simp only [mem_compl, mem_union, mem_singleton] at hv
      exact hv (Or.inl hvB)
  · intro S hS v hv
    have h4 := ((minimum_cost_iff hAB hA).mp hS).2
    simp only [mem_compl, mem_union, mem_singleton]
    exact not_or.mpr ⟨Finset.disjoint_left.mp hS.admissible.disjoint hv, fun h ↦ h4 (h ▸ hv)⟩

-- More than one source, more than one sink, and a free vertex give two minimum cuts.
example (S : Finset (Fin 6)) :
    IsMinimum cost {0, 1} {2, 3} S ↔ S = {0, 1} ∨ S = {0, 1, 5} := by
  rw [minimum_cost_iff (by decide) (by decide)]
  simp only [isAdmissible_iff, Finset.disjoint_left, Finset.subset_iff]
  constructor
  · rintro ⟨⟨hA, hB⟩, h4⟩
    have h2 : (2 : Fin 6) ∉ S := fun h ↦ hB h (by simp)
    have h3 : (3 : Fin 6) ∉ S := fun h ↦ hB h (by simp)
    by_cases h5 : 5 ∈ S
    · right
      ext v
      fin_cases v <;> simp_all
    · left
      ext v
      fin_cases v <;> simp_all
  · rintro (rfl | rfl) <;> decide

example : smallest submodular_cost (A := {0, 1}) (B := {2, 3}) (by decide) = {0, 1} :=
  smallest_cost (by decide) (by decide)

example : largest submodular_cost (A := {0, 1}) (B := {2, 3}) (by decide) = {0, 1, 5} := by
  rw [largest_cost _ (by decide)]
  decide

-- The same formulas include empty source sets, empty sink sets, and both empty.
example : smallest submodular_cost (A := ∅) (B := {2, 3}) (by simp) = ∅ :=
  smallest_cost (by simp) (by simp)

example : largest submodular_cost (A := {0, 1}) (B := ∅) (by simp) = {0, 1, 2, 3, 5} := by
  rw [largest_cost _ (by decide)]
  decide

example : smallest submodular_cost (A := ∅) (B := ∅) (by simp) = ∅ :=
  smallest_cost (by simp) (by simp)

example : largest submodular_cost (A := ∅) (B := ∅) (by simp) = {0, 1, 2, 3, 5} := by
  rw [largest_cost _ (by simp)]
  decide

end TauCeti.TerminalCut
