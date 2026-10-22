/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Setoid.Partition
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Set.Finite.Range

/-!
# Finite partition helpers

This file contains general-purpose constructions and facts about finite partitions: the partition
of the top element into an element and its complement, the decidability of the refinement order,
the single part of the coarsest partition of a non-bottom element, the fact that a partition having
the whole element as a part is the coarsest, the partition of a type into the
fibres of a map to a finite type, the associated indexed partition, the sizes of the traces of a
subset on the parts, cardinality bounds for common refinements, a bound on the sum of the squared
part sizes, the refinement relations of `Finpartition.bind` and of a refining partition's parts,
the monotonicity of `Finpartition.bind`, products over its parts, its parts through each point,
and the fact that it is inverse to restricting a refinement to the parts of the coarser partition,
the behavior of intersections of parts under refinement, the symmetry of lying in a common part,
the determination of a partition by its parts through each point, the parts of a restriction, the
monotonicity of `Finpartition.part` under refinement, the coarse parent
`Finpartition.refinementParent` of a part of a finer partition, together with decomposition and
summation formulas for the fine parts below a coarse part and for sums over points of functions of
the fine and coarse parts through them, the fact that a set with at most two elements has no finite
partitions other than the finest and the coarsest, and the position of the parts of
`Finpartition.atomise` relative to the sets it cuts along.
-/

public section

namespace Finpartition

open Finset

/-- The finite partition of the top element into an element and its complement, omitting either
part when it is bottom. -/
noncomputable def bipartition {α : Type*} [BooleanAlgebra α] [DecidableEq α] (s : α) :
    Finpartition (⊤ : α) :=
  Finpartition.ofErase {s, sᶜ} (Set.PairwiseDisjoint.supIndep (by
    simp [Set.pairwiseDisjoint_insert, disjoint_compl_right])) (by simp)

@[simp]
theorem parts_bipartition {α : Type*} [BooleanAlgebra α] [DecidableEq α] (s : α) :
    (bipartition s).parts = ({s, sᶜ} : Finset α).erase ⊥ :=
  by simp [bipartition]

/-- A bipartition has at most two parts. -/
theorem card_parts_bipartition_le {α : Type*} [BooleanAlgebra α] [DecidableEq α] (s : α) :
    (bipartition s).parts.card ≤ 2 := by
  rw [parts_bipartition]
  exact Finset.card_erase_le.trans (Finset.card_insert_le _ _ |>.trans_eq (by simp))

/-- A non-bottom element is a part of its bipartition. -/
theorem mem_bipartition_of_ne_bot {α : Type*} [BooleanAlgebra α] [DecidableEq α] {s : α}
    (hs : s ≠ ⊥) :
    s ∈ (bipartition s).parts := by
  simp [parts_bipartition, hs]

/-- Unfolding of the refinement order: `P ≤ Q` when each part of `P` lies below a part of `Q`. -/
theorem le_def {α : Type*} [Lattice α] [OrderBot α] {a : α} {P Q : Finpartition a} :
    P ≤ Q ↔ ∀ b ∈ P.parts, ∃ c ∈ Q.parts, b ≤ c :=
  Iff.rfl

/-- Refinement of finite partitions is decidable when the order on parts is. -/
instance instDecidableLE {α : Type*} [Lattice α] [OrderBot α] [DecidableLE α] {a : α} :
    DecidableLE (Finpartition a) :=
  fun _ _ => decidable_of_iff _ le_def.symm

/-- The coarsest finite partition of a non-bottom element `a` has the single part `a`. -/
@[simp]
theorem parts_top {α : Type*} [Lattice α] [OrderBot α] {a : α} [Decidable (a = ⊥)]
    (ha : a ≠ ⊥) : (⊤ : Finpartition a).parts = {a} := by
  refine (parts_top_subset a).antisymm ?_
  obtain ⟨b, hb⟩ := parts_nonempty ⊤ ha
  obtain rfl := Finset.mem_singleton.1 (parts_top_subset a hb)
  exact Finset.singleton_subset_iff.2 hb

/-- A finite partition of `a` that has `a` itself as a part is the partition into one part. -/
theorem eq_top_of_mem_parts {α : Type*} [Lattice α] [OrderBot α] {a : α} [Decidable (a = ⊥)]
    {P : Finpartition a} (h : a ∈ P.parts) : P = ⊤ :=
  top_le_iff.1 fun _ hb => ⟨a, h, (Finset.mem_singleton.1 (parts_top_subset a hb)).le⟩

/-- The number of parts in a common refinement is at most the product of the two part counts. -/
theorem card_parts_inf_le_mul {α : Type*} [DistribLattice α] [OrderBot α] [DecidableEq α]
    {a : α} (P Q : Finpartition a) :
    (P ⊓ Q).parts.card ≤ P.parts.card * Q.parts.card := by
  rw [Finpartition.parts_inf]
  exact Finset.card_erase_le.trans
    (Finset.card_image_le.trans_eq (Finset.card_product _ _))

/-- The traces of a subset of `s` on the parts of a finite partition of `s` partition it, so their
sizes sum to its size. -/
theorem sum_card_inter_parts {ι : Type*} [DecidableEq ι] {s X : Finset ι} (P : Finpartition s)
    (hX : X ⊆ s) : ∑ C ∈ P.parts, (X ∩ C).card = X.card := by
  have h := P.sum_restrict hX (fun C ↦ C.card) (by simp)
  rw [Finpartition.sum_card_parts] at h
  simp_rw [h, Finset.inf_eq_inter, Finset.inter_comm]

/-- Juxtaposing finite partitions of the parts of `P` refines `P`. -/
theorem bind_le {α : Type*} [Lattice α] [OrderBot α] [IsModularLattice α] [DecidableEq α]
    {a : α} (P : Finpartition a) (Q : ∀ i ∈ P.parts, Finpartition i) : P.bind Q ≤ P := by
  intro b hb
  obtain ⟨A, hA, hb⟩ := mem_bind.1 hb
  exact ⟨A, hA, (Q A hA).le hb⟩

/-- Juxtaposition is monotone in the finite partitions of the parts. -/
theorem bind_mono {α : Type*} [Lattice α] [OrderBot α] [IsModularLattice α] [DecidableEq α]
    {a : α} {P : Finpartition a} {Q Q' : ∀ i ∈ P.parts, Finpartition i}
    (h : ∀ i hi, Q i hi ≤ Q' i hi) : P.bind Q ≤ P.bind Q' := by
  intro b hb
  obtain ⟨A, hA, hb⟩ := mem_bind.1 hb
  obtain ⟨c, hc, hbc⟩ := h A hA hb
  exact ⟨c, mem_bind.2 ⟨A, hA, hc⟩, hbc⟩

/-- A sum over the parts of the juxtaposition `P.bind Q` is the sum, over the parts `A` of `P`,
of the sums over the parts of `Q A`. -/
theorem sum_parts_bind {α M : Type*} [Lattice α] [OrderBot α] [IsModularLattice α]
    [DecidableEq α] [AddCommMonoid M] {a : α} (P : Finpartition a)
    (Q : ∀ i ∈ P.parts, Finpartition i) (g : α → M) :
    ∑ b ∈ (P.bind Q).parts, g b = ∑ A ∈ P.parts.attach, ∑ b ∈ (Q A.1 A.2).parts, g b := by
  rw [bind_parts, ← combine_parts (fun A : P.parts => Q A.1 A.2) P.supIndep.attach, sum_combine]

/-- A product over the parts of the juxtaposition `P.bind Q` is the product, over the parts `A`
of `P`, of the products over the parts of `Q A`. -/
@[to_additive existing]
theorem prod_parts_bind {α M : Type*} [Lattice α] [OrderBot α] [IsModularLattice α]
    [DecidableEq α] [CommMonoid M] {a : α} (P : Finpartition a)
    (Q : ∀ i ∈ P.parts, Finpartition i) (g : α → M) :
    ∏ b ∈ (P.bind Q).parts, g b = ∏ A ∈ P.parts.attach, ∏ b ∈ (Q A.1 A.2).parts, g b :=
  -- Mathlib only provides the additive `Finpartition.sum_combine`, so we transfer `sum_parts_bind`
  -- through `Additive M`, whose finite sums are by definition the finite products in `M`.
  sum_parts_bind (M := Additive M) P Q (Additive.ofMul ∘ g)

/-- If `Q` refines `P`, then each part of `P` is the union of the parts of `Q` it contains. -/
theorem biUnion_filter_subset_eq_of_le {ι : Type*} [DecidableEq ι] {s B : Finset ι}
    {P Q : Finpartition s} (hQP : Q ≤ P) (hB : B ∈ P.parts) :
    {C ∈ Q.parts | C ⊆ B}.biUnion id = B := by
  refine Finset.Subset.antisymm
    (Finset.biUnion_subset.2 fun C hC ↦ (Finset.mem_filter.1 hC).2) fun x hx ↦ ?_
  obtain ⟨C, hC, hxC⟩ := Q.exists_mem (P.le hB hx)
  obtain ⟨B', hB', hCB'⟩ := hQP hC
  obtain rfl := P.eq_of_mem_parts hB' hB (hCB' hxC) hx
  exact Finset.mem_biUnion.2 ⟨C, Finset.mem_filter.2 ⟨hC, hCB'⟩, hxC⟩

/-- If all parts of `P` have size at most `m`, then `∑ A ∈ P.parts, A.card ^ 2 ≤ m * s.card`. -/
theorem sum_sq_card_parts_le {ι : Type*} [DecidableEq ι] {s : Finset ι} (P : Finpartition s)
    {m : ℕ} (hm : ∀ A ∈ P.parts, A.card ≤ m) :
    ∑ A ∈ P.parts, A.card ^ 2 ≤ m * s.card := by
  rw [← P.sum_card_parts, Finset.mul_sum]
  exact Finset.sum_le_sum fun A hA ↦ by rw [sq]; exact Nat.mul_le_mul_right _ (hm A hA)

variable {Ω : Type*} {u : Set Ω}

section Fibers

variable {κ : Type*} [Finite κ] {g : Ω → κ} {s : Set Ω}

open Classical in
/-- The finite partition of `Set.univ` into the nonempty fibres of a map to a finite type. -/
noncomputable def ofFibers (g : Ω → κ) : Finpartition (Set.univ : Set Ω) :=
  ofErase (Set.finite_range fun i : κ => g ⁻¹' {i}).toFinset
    (Finset.supIndep_iff_pairwiseDisjoint.mpr fun s hs t ht hst => by
      rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hs ht
      obtain ⟨i, rfl⟩ := hs
      obtain ⟨j, rfl⟩ := ht
      exact (Set.disjoint_singleton.2 fun hij =>
        hst (congrArg (fun k => g ⁻¹' {k}) hij)).preimage g)
    (by
      rw [Finset.sup_id_set_eq_sUnion, Set.Finite.coe_toFinset, Set.sUnion_range]
      exact Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨g x, rfl⟩)

/-- The parts of `Finpartition.ofFibers g` are the fibres of `g` through the points of `Ω`. -/
@[simp]
theorem mem_ofFibers_parts : s ∈ (ofFibers g).parts ↔ ∃ x, g ⁻¹' {g x} = s := by
  classical
  rw [ofFibers, ofErase_parts, Finset.mem_erase, Set.Finite.mem_toFinset, Set.bot_eq_empty,
    ← Set.nonempty_iff_ne_empty]
  constructor
  · rintro ⟨⟨x, hx⟩, i, rfl⟩
    exact ⟨x, by rw [Set.mem_preimage, Set.mem_singleton_iff] at hx; rw [hx]⟩
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x, rfl⟩, g x, rfl⟩

/-- The map `g` is constant on every part of `Finpartition.ofFibers g`. -/
theorem apply_eq_of_mem_ofFibers_parts (hs : s ∈ (ofFibers g).parts) {x x' : Ω} (hx : x ∈ s)
    (hx' : x' ∈ s) : g x = g x' := by
  obtain ⟨y, rfl⟩ := mem_ofFibers_parts.1 hs
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hx hx'
  rw [hx, hx']

end Fibers

/-- The indexed partition associated to a finite partition of `Set.univ`, indexed by its actual
parts.  Its `index` sends each point to the unique part containing it. -/
noncomputable def indexedPartition (P : Finpartition (Set.univ : Set Ω)) :
    IndexedPartition (fun p : P.parts => (p : Set Ω)) :=
  IndexedPartition.mk' _
    (fun p q hne => P.disjoint p.property q.property fun h => hne (Subtype.ext h))
    (fun p => Set.nonempty_iff_ne_empty.mpr (P.ne_bot p.property))
    (fun x => by
      obtain ⟨p, ⟨hp, hxp⟩, _⟩ := P.isPartition_parts.2 x
      exact ⟨⟨p, hp⟩, hxp⟩)

/-- Under refinement, a part of the finer partition is either contained in a given part of the
coarser one or disjoint from it. -/
theorem inter_part_eq_self_or_eq_empty_of_le {P Q : Finpartition u} (href : Q ≤ P)
    {r : Set Ω} (hr : r ∈ Q.parts) {p : Set Ω} (hp : p ∈ P.parts) :
    r ∩ p = r ∨ r ∩ p = ∅ := by
  obtain ⟨p', hp', hrp'⟩ := href hr
  by_cases h : p' = p
  · exact Or.inl (Set.inter_eq_self_of_subset_left (h ▸ hrp'))
  · refine Or.inr (Set.eq_empty_of_subset_empty fun x hx => ?_)
    exact absurd hx.2 (Set.disjoint_left.mp (P.disjoint hp' hp h) (hrp' hx.1))

section Refinement

variable {α : Type*} [Lattice α] [OrderBot α] {a : α} {P Q : Finpartition a}

/-- Distinct parts of a finite partition, viewed as elements of the subtype of parts, are
disjoint. -/
theorem pairwiseDisjoint_subtype_val (P : Finpartition a) (t : Set P.parts) :
    t.PairwiseDisjoint Subtype.val :=
  fun B _ D _ hBD => P.disjoint B.2 D.2 (Subtype.coe_injective.ne hBD)

/-- The part of a coarser partition `P` containing a part `B` of a finer partition `Q ≤ P`. It is
uniquely determined, since parts are nonzero and pairwise disjoint; see
`Finpartition.refinementParent_eq_iff`. -/
noncomputable def refinementParent (h : Q ≤ P) (B : Q.parts) : P.parts :=
  ⟨(h B.2).choose, (h B.2).choose_spec.1⟩

/-- A part of a finer partition lies below its coarse parent. -/
theorem le_refinementParent (h : Q ≤ P) (B : Q.parts) : B.1 ≤ (refinementParent h B).1 :=
  (h B.2).choose_spec.2

/-- The coarse parent of `B` is the unique coarse part lying above `B`. -/
@[simp]
theorem refinementParent_eq_iff (h : Q ≤ P) {B : Q.parts} {A : P.parts} :
    refinementParent h B = A ↔ B.1 ≤ A.1 := by
  refine ⟨fun hA => hA ▸ le_refinementParent h B, fun hBA => ?_⟩
  by_contra hne
  exact Q.ne_bot B.2 <| disjoint_self.1 <|
    (P.disjoint (refinementParent h B).2 A.2 (Subtype.coe_injective.ne hne)).mono
      (le_refinementParent h B) hBA

/-- A double sum over the fine parts can be grouped by the coarse parents of both parts. -/
theorem sum_sum_eq_sum_sum_fiber [DecidableEq α] {M : Type*} [AddCommMonoid M] (h : Q ≤ P)
    (F : Q.parts → Q.parts → M) :
    ∑ B : Q.parts, ∑ D : Q.parts, F B D = ∑ A : P.parts, ∑ C : P.parts,
      ∑ B with refinementParent h B = A, ∑ D with refinementParent h D = C, F B D := by
  rw [← Finset.sum_fiberwise Finset.univ (refinementParent h) fun B => ∑ D, F B D]
  refine Finset.sum_congr rfl fun A _ => ?_
  conv_rhs => rw [sum_comm]
  refine Finset.sum_congr rfl fun B _ => ?_
  exact (Finset.sum_fiberwise Finset.univ (refinementParent h) (F B)).symm

end Refinement

section FinsetRefinement

open scoped Finset

variable {α : Type*} [DecidableEq α] {s : Finset α} {P Q : Finpartition s}

/-- The sizes of the parts of a finite partition add up to the size of its support. -/
theorem sum_card_subtype {R : Type*} [AddCommMonoidWithOne R] (P : Finpartition s) :
    ∑ A : P.parts, (#A.1 : R) = #s := by
  rw [Finset.sum_coe_sort P.parts fun A => (#A : R)]
  rw [← Nat.cast_sum, P.sum_card_parts]

/-- The weights `|A||B| / |s|²` of the ordered pairs of parts sum to at most one.
No compatibility between the preorder and arithmetic is needed beyond `0 ≤ 1`. -/
theorem sum_sum_weight_le_one {K : Type*} [DivisionSemiring K] [Preorder K] [ZeroLEOneClass K]
    (P : Finpartition s) :
    ∑ A : P.parts, ∑ C : P.parts, (#A.1 * #C.1 / (#s : K) ^ 2) ≤ 1 := by
  simp_rw [← Finset.sum_div, ← Finset.sum_mul_sum, sum_card_subtype, ← sq]
  exact div_self_le_one _

/-- Summing a function of the part containing each point groups the points by part. -/
theorem sum_apply_part {M : Type*} [AddCommMonoid M] (P : Finpartition s) (f : Finset α → M) :
    ∑ x ∈ s, f (P.part x) = ∑ A ∈ P.parts, #A • f A := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := P.part) (t := P.parts)
    fun x hx => P.part_mem.2 hx]
  refine Finset.sum_congr rfl fun A hA => ?_
  rw [Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.1 hx).2], Finset.sum_const]
  congr 2
  ext x
  simp only [Finset.mem_filter, P.part_eq_iff_mem hA, and_iff_right_iff_imp]
  exact fun hx => P.le hA hx

/-- Refining a partition shrinks the part containing each point. -/
@[gcongr]
theorem part_mono (h : P ≤ Q) (a : α) : P.part a ⊆ Q.part a := by
  by_cases ha : a ∈ s
  · obtain ⟨C, hC, hPC⟩ := h (P.part_mem.2 ha)
    rw [Q.part_eq_of_mem hC (hPC (P.mem_part_self.2 ha))]
    exact hPC
  · simp [P.part_eq_empty.2 ha]

/-- Lying in the same part of a finite partition is symmetric. -/
theorem mem_part_comm {a b : α} : b ∈ P.part a ↔ a ∈ P.part b := by
  simp only [mem_part_iff_exists, and_comm]

/-- A finite partition of a finset is determined by the part containing each point. -/
theorem part_injective : Function.Injective (part : Finpartition s → α → Finset α) := by
  have key {P Q : Finpartition s} (h : P.part = Q.part) {B : Finset α} (hB : B ∈ P.parts) :
      B ∈ Q.parts := by
    obtain ⟨a, ha⟩ := P.nonempty_of_mem_parts hB
    rw [← P.part_eq_of_mem hB ha, h]
    exact Q.part_mem.2 (P.le hB ha)
  exact fun P Q h => Finpartition.ext <| Finset.ext fun B => ⟨key h, key h.symm⟩

/-- Two finite partitions of `s` coincide when they have the same part through each point of
`s`. -/
theorem ext_of_part (h : ∀ a ∈ s, P.part a = Q.part a) : P = Q :=
  part_injective <| funext fun a => by
    by_cases ha : a ∈ s
    · exact h a ha
    · rw [P.part_eq_empty.2 ha, Q.part_eq_empty.2 ha]

/-- Restricting a partition to a subset `t` cuts the part through each point of `t` down to `t`. -/
@[simp]
theorem part_restrict {t : Finset α} (P : Finpartition s) (hts : t ≤ s) {a : α} (ha : a ∈ t) :
    (P.restrict hts).part a = P.part a ∩ t := by
  have hat : a ∈ P.part a ∩ t := mem_inter.2 ⟨P.mem_part_self.2 (hts ha), ha⟩
  refine part_eq_of_mem _ ?_ hat
  rw [parts_restrict, mem_erase]
  exact ⟨ne_empty_of_mem hat, mem_image_of_mem _ (P.part_mem.2 (hts ha))⟩

/-- A coarse part is the disjoint union of the fine parts whose coarse parent it is. -/
theorem biUnion_filter_refinementParent_eq (h : Q ≤ P) (A : P.parts) :
    ({B | refinementParent h B = A} : Finset Q.parts).biUnion Subtype.val = A.1 := by
  classical
  calc
    _ = {B ∈ Q.parts | B ⊆ A.1}.biUnion id := by
      ext x
      simp [Subtype.exists, and_assoc, and_left_comm]
    _ = _ := biUnion_filter_subset_eq_of_le h A.2

/-- The traces on `X` of the fine parts with a given coarse parent add up to the trace of `X` on
that parent. -/
theorem sum_card_inter_filter_refinementParent_eq (h : Q ≤ P) (A : P.parts) (X : Finset α) :
    ∑ B with refinementParent h B = A, #(X ∩ B.1) = #(X ∩ A.1) := by
  conv_rhs => rw [← biUnion_filter_refinementParent_eq h A, Finset.inter_biUnion]
  rw [Finset.card_biUnion fun B _ D _ hBD ↦
    (Q.pairwiseDisjoint_subtype_val _ (Set.mem_univ B) (Set.mem_univ D) hBD).mono
      Finset.inter_subset_right Finset.inter_subset_right]

/-- The sizes of the fine parts with a given coarse parent add up to the size of that parent. -/
theorem sum_card_filter_refinementParent_eq (h : Q ≤ P) (A : P.parts) :
    ∑ B with refinementParent h B = A, #B.1 = #A.1 := by
  calc ∑ B with refinementParent h B = A, #B.1
      = ∑ B with refinementParent h B = A, #(s ∩ B.1) :=
        Finset.sum_congr rfl fun B _ ↦ by rw [Finset.inter_eq_right.2 (Q.le B.2)]
    _ = #A.1 := by
        rw [sum_card_inter_filter_refinementParent_eq, Finset.inter_eq_right.2 (P.le A.2)]

/-- Under a refinement `Q ≤ P`, the coarse part through a point of a fine part `B` is the coarse
parent of `B`. -/
theorem part_eq_refinementParent (h : Q ≤ P) (B : Q.parts) {a : α} (ha : a ∈ B.1) :
    P.part a = (refinementParent h B).1 :=
  P.part_eq_of_mem (refinementParent h B).2 (le_refinementParent h B ha)

/-- Under a refinement `Q ≤ P`, a sum of a function of the fine and coarse parts through each
point groups the points by fine part, each fine part paired with its coarse parent. -/
theorem sum_apply_part_part (h : Q ≤ P) {M : Type*} [AddCommMonoid M]
    (f : Finset α → Finset α → M) :
    ∑ a ∈ s, f (Q.part a) (P.part a) = ∑ B : Q.parts, #B.1 • f B.1 (refinementParent h B).1 := by
  have hs : ∑ a ∈ s, f (Q.part a) (P.part a) =
      ∑ B ∈ Q.parts, ∑ a ∈ B, f (Q.part a) (P.part a) := by
    calc ∑ a ∈ s, f (Q.part a) (P.part a)
        = ∑ a ∈ Q.parts.biUnion id, f (Q.part a) (P.part a) := by rw [Q.biUnion_parts]
      _ = _ := Finset.sum_biUnion Q.supIndep.pairwiseDisjoint
  rw [hs, ← Finset.sum_coe_sort Q.parts]
  refine Finset.sum_congr rfl fun B _ => ?_
  rw [← Finset.sum_const]
  exact Finset.sum_congr rfl fun a ha => by
    rw [Q.part_eq_of_mem B.2 ha, part_eq_refinementParent h B ha]

/-- A finite partition of a set with at most two elements is either the partition into singletons
or the partition into one part. -/
theorem eq_bot_or_eq_top_of_pair {i j : α} (P : Finpartition ({i, j} : Finset α)) :
    P = ⊥ ∨ P = ⊤ := by
  have hi : i ∈ ({i, j} : Finset α) := mem_insert_self i {j}
  have hj : j ∈ ({i, j} : Finset α) := mem_insert_of_mem (mem_singleton_self j)
  by_cases hji : j ∈ P.part i
  · refine Or.inr (top_le_iff.1 fun t ht => ⟨P.part i, P.part_mem.2 hi, ?_⟩)
    rw [mem_singleton.1 (parts_top_subset _ ht)]
    exact insert_subset_iff.2 ⟨P.mem_part hi, singleton_subset_iff.2 hji⟩
  · refine Or.inl (le_bot_iff.1 fun t ht => ?_)
    obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts ht
    refine ⟨{x}, mem_bot_iff.2 ⟨x, P.le ht hx, rfl⟩, fun y hy => ?_⟩
    rw [← P.part_eq_of_mem ht hx] at hy
    have hxs := P.le ht hx
    rw [mem_singleton]
    rcases mem_insert.1 hxs with rfl | hx'
    · rcases mem_insert.1 (P.part_subset x hy) with rfl | hy'
      · rfl
      · exact absurd (mem_singleton.1 hy' ▸ hy) hji
    · rw [mem_singleton.1 hx'] at hy ⊢
      rcases mem_insert.1 (P.part_subset j hy) with rfl | hy'
      · rw [P.mem_part_iff_part_eq_part hi hj] at hy
        exact absurd (hy ▸ P.mem_part hj) hji
      · exact mem_singleton.1 hy'

/-- In the juxtaposition `P.bind Q`, the part through a point of a part `B` of `P` is its part in
`Q B`. -/
theorem part_bind {Q : ∀ i ∈ P.parts, Finpartition i} {B : Finset α} (hB : B ∈ P.parts) {a : α}
    (ha : a ∈ B) : (P.bind Q).part a = (Q B hB).part a :=
  part_eq_of_mem _ (mem_bind.2 ⟨B, hB, (Q B hB).part_mem.2 ha⟩) ((Q B hB).mem_part_self.2 ha)

/-- Restricting the juxtaposition `P.bind Q` to a part `B` of `P` recovers `Q B`. -/
@[simp]
theorem restrict_bind {Q : ∀ i ∈ P.parts, Finpartition i} {B : Finset α} (hB : B ∈ P.parts) :
    (P.bind Q).restrict (P.le hB) = Q B hB :=
  ext_of_part fun a ha => by
    rw [part_restrict _ _ ha, part_bind hB ha, inter_eq_left.2 ((Q B hB).part_subset a)]

/-- Juxtaposing the restrictions of a refinement `Q ≤ P` to the parts of `P` recovers `Q`. -/
@[simp]
theorem bind_restrict (h : Q ≤ P) : (P.bind fun _ hB => Q.restrict (P.le hB)) = Q :=
  ext_of_part fun a ha => by
    rw [part_bind (P.part_mem.2 ha) (P.mem_part_self.2 ha),
      part_restrict _ _ (P.mem_part_self.2 ha), inter_eq_left.2 (part_mono h a)]

end FinsetRefinement

section Atomise

variable {α : Type*} [DecidableEq α] {s : Finset α}

/-- Each part of `atomise s F` lies inside or outside each member of `F`. -/
theorem subset_or_disjoint_of_mem_atomise {F : Finset (Finset α)} {t u : Finset α}
    (ht : t ∈ (atomise s F).parts) (hu : u ∈ F) : t ⊆ u ∨ Disjoint t u := by
  obtain ⟨-, R, -, rfl⟩ := mem_atomise.1 ht
  by_cases huR : u ∈ R
  · exact Or.inl fun i hi ↦ ((Finset.mem_filter.1 hi).2 u hu).1 huR
  · exact Or.inr <| Finset.disjoint_left.2 fun i hi hiu ↦
      huR (((Finset.mem_filter.1 hi).2 u hu).2 hiu)

end Atomise

end Finpartition
