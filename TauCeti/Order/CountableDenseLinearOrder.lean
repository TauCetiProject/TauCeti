/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.CountableDenseLinearOrder

/-!
# Cantor's isomorphism theorem for coloured dense linear orders

Let `α` and `β` be countable nonempty linear orders without endpoints, coloured by maps
`c : α → ι` and `d : β → ι` such that every colour class is dense: between any two points of
`α` there is a point of each colour, and likewise in `β`. Then some order isomorphism
`π : α ≃o β` preserves colours, `d ∘ π = c`.

This is the coloured form of Cantor's isomorphism theorem `Order.iso_of_countable_dense`, and the
proof is the same back-and-forth argument through `Order.PartialIso` and the Rasiowa–Sikorski
lemma `Order.idealOfCofinals`: a finite colour-preserving partial isomorphism extends to any new
point, which the density of its colour class supplies in the gap that the order type of the point
prescribes. Taking `α = β` and colours permuted by a bijection of `ι` gives automorphisms realising
every permutation of a dense colouring; such automorphisms of `ℚ` move the vertices of a coded
countable structure when it is unravelled into a coloured linear order.

## Main results

* `Order.exists_between_finsets_eq`: between two finite sets, one entirely below the other,
  there is a point of any prescribed dense colour.
* `Order.exists_orderIso_comp_eq_of_dense`: the coloured Cantor isomorphism theorem.

## References

* A. Montalbán, *Computable structure theory: within the arithmetic*, the coloured dense orders
  in the proof of Lemma VI.18.
* The construction follows `Order.iso_of_countable_dense` in
  `Mathlib/Order/CountableDenseLinearOrder.lean`, by David Wärn.
-/

public section

namespace Order

variable {α β ι : Type*} [LinearOrder α] [LinearOrder β]

/-- If every colour class of `c` is dense in a linear order without endpoints, then between two
finite sets, the first entirely below the second, there is a point of any prescribed colour. -/
theorem exists_between_finsets_eq [NoMinOrder α] [NoMaxOrder α] [Nonempty α] {c : α → ι}
    (hc : ∀ i ⦃a b : α⦄, a < b → ∃ x, a < x ∧ x < b ∧ c x = i) (lo hi : Finset α)
    (lo_lt_hi : ∀ x ∈ lo, ∀ y ∈ hi, x < y) (i : ι) :
    ∃ m, (∀ x ∈ lo, x < m) ∧ (∀ y ∈ hi, m < y) ∧ c m = i := by
  have : DenselyOrdered α :=
    ⟨fun _ _ h ↦ (hc i h).imp fun _ hx ↦ ⟨hx.1, hx.2.1⟩⟩
  obtain ⟨m₁, hlo, hhi⟩ := exists_between_finsets lo hi lo_lt_hi
  obtain ⟨m₂, hm, hhi'⟩ := exists_between_finsets {m₁} hi (by simpa using hhi)
  obtain ⟨m, h₁, h₂, rfl⟩ := hc i (hm m₁ (Finset.mem_singleton_self _))
  exact ⟨m, fun x hx ↦ (hlo x hx).trans h₁, fun y hy ↦ h₂.trans (hhi' y hy), rfl⟩

namespace PartialIso

/-- A colour-preserving finite partial isomorphism extends to any new point of a densely coloured
target: the image lies in the gap prescribed by the domain and carries the colour of the point.
This is the coloured form of `Order.PartialIso.exists_across`. -/
theorem exists_across_eq [NoMinOrder β] [NoMaxOrder β] [Nonempty β] {c : α → ι}
    {d : β → ι} (hd : ∀ i ⦃a b : β⦄, a < b → ∃ x, a < x ∧ x < b ∧ d x = i)
    (f : PartialIso α β) (hf : ∀ p ∈ f.val, d p.2 = c p.1) (a : α) :
    ∃ b, (∀ p ∈ f.val, cmp p.1 a = cmp p.2 b) ∧ d b = c a := by
  by_cases h : ∃ b, (a, b) ∈ f.val
  · obtain ⟨b, hb⟩ := h
    exact ⟨b, fun p hp ↦ f.prop _ hp _ hb, hf _ hb⟩
  have hlt : ∀ x ∈ {p ∈ f.val | p.1 < a}.image Prod.snd,
      ∀ y ∈ {p ∈ f.val | a < p.1}.image Prod.snd, x < y := by
    simp only [Finset.mem_image, Finset.mem_filter]
    rintro _ ⟨p, ⟨hp, hpa⟩, rfl⟩ _ ⟨q, ⟨hq, haq⟩, rfl⟩
    rw [← lt_iff_lt_of_cmp_eq_cmp (f.prop _ hp _ hq)]
    exact hpa.trans haq
  obtain ⟨b, hblo, hbhi, hb⟩ := exists_between_finsets_eq hd _ _ hlt (c a)
  refine ⟨b, fun p hp ↦ ?_, hb⟩
  rcases lt_or_gt_of_ne (fun he : p.1 = a ↦ h ⟨p.2, he ▸ hp⟩) with hpa | hap
  · rw [(cmp_eq_lt_iff _ _).2 hpa, (cmp_eq_lt_iff _ _).2
      (hblo _ (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hp, hpa⟩)))]
  · rw [(cmp_eq_gt_iff _ _).2 hap, (cmp_eq_gt_iff _ _).2
      (hbhi _ (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hp, hap⟩)))]

/-- Adding a pair `(a, b)` that is placed compatibly with every pair of a finite partial
isomorphism gives a finite partial isomorphism. -/
def insert (f : PartialIso α β) (a : α) (b : β)
    (hab : ∀ p ∈ f.val, cmp p.1 a = cmp p.2 b) : PartialIso α β :=
  ⟨Insert.insert (a, b) f.val, fun p hp q hq ↦ by
    rw [Finset.mem_insert] at hp hq
    rcases hp with rfl | hp <;> rcases hq with rfl | hq
    · simp only [cmp_self_eq_eq]
    · rw [cmp_eq_cmp_symm]
      exact hab _ hq
    · exact hab _ hp
    · exact f.prop _ hp _ hq⟩

@[simp]
theorem val_insert (f : PartialIso α β) (a : α) (b : β)
    (hab : ∀ p ∈ f.val, cmp p.1 a = cmp p.2 b) :
    (f.insert a b hab).val = Insert.insert (a, b) f.val :=
  (rfl)

theorem le_insert (f : PartialIso α β) (a : α) (b : β)
    (hab : ∀ p ∈ f.val, cmp p.1 a = cmp p.2 b) : f ≤ f.insert a b hab :=
  Subtype.coe_le_coe.1 (by rw [val_insert]; exact Finset.subset_insert _ _)

end PartialIso

/-- The finite partial isomorphisms from `α` to `β` sending each point to a point of the same
colour. -/
private abbrev ColouredPartialIso (c : α → ι) (d : β → ι) :=
  {f : PartialIso α β // ∀ p ∈ f.val, d p.2 = c p.1}

/-- The colour-preserving finite partial isomorphisms defined at `a`, a cofinal set. -/
private def definedAtLeft [NoMinOrder β] [NoMaxOrder β] [Nonempty β] {c : α → ι} {d : β → ι}
    (hd : ∀ i ⦃a b : β⦄, a < b → ∃ x, a < x ∧ x < b ∧ d x = i) (a : α) :
    Cofinal (ColouredPartialIso c d) where
  carrier := {f | ∃ b, (a, b) ∈ f.val.val}
  isCofinal f := by
    obtain ⟨b, hab, hb⟩ := PartialIso.exists_across_eq hd f.val f.property a
    refine ⟨⟨f.val.insert a b hab, ?_⟩, ⟨b, by simp⟩, Subtype.mk_le_mk.2 (f.val.le_insert a b hab)⟩
    intro p hp
    rw [PartialIso.val_insert, Finset.mem_insert] at hp
    rcases hp with rfl | hp
    exacts [hb, f.property p hp]

/-- The colour-preserving finite partial isomorphisms with `b` in their image, a cofinal set. -/
private def definedAtRight [NoMinOrder α] [NoMaxOrder α] [Nonempty α] {c : α → ι} {d : β → ι}
    (hc : ∀ i ⦃a b : α⦄, a < b → ∃ x, a < x ∧ x < b ∧ c x = i) (b : β) :
    Cofinal (ColouredPartialIso c d) where
  carrier := {f | ∃ a, (a, b) ∈ f.val.val}
  isCofinal f := by
    -- Extend the inverse partial isomorphism at `b`, then insert the reversed pair. The pairs of
    -- `f.comm` are the swapped pairs of `f`, the image under `Equiv.prodComm`.
    have hcomm : ∀ q ∈ f.val.comm.val, c q.2 = d q.1 := by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
      exact (f.property p hp).symm
    obtain ⟨a, hba, ha⟩ := PartialIso.exists_across_eq hc f.val.comm hcomm b
    have hab : ∀ p ∈ f.val.val, cmp p.1 a = cmp p.2 b := fun p hp ↦
      (hba (p.2, p.1) (Finset.mem_image_of_mem _ hp)).symm
    refine ⟨⟨f.val.insert a b hab, ?_⟩, ⟨a, by simp⟩, Subtype.mk_le_mk.2 (f.val.le_insert a b hab)⟩
    intro p hp
    rw [PartialIso.val_insert, Finset.mem_insert] at hp
    rcases hp with rfl | hp
    exacts [ha.symm, f.property p hp]

/-- **Cantor's isomorphism theorem for coloured orders.** Two countable nonempty linear orders
without endpoints, coloured so that every colour class is dense, are isomorphic by an order
isomorphism preserving colours. -/
theorem exists_orderIso_comp_eq_of_dense [Countable α] [NoMinOrder α] [NoMaxOrder α]
    [Nonempty α] [Countable β] [NoMinOrder β] [NoMaxOrder β] [Nonempty β] {c : α → ι}
    {d : β → ι} (hc : ∀ i ⦃a b : α⦄, a < b → ∃ x, a < x ∧ x < b ∧ c x = i)
    (hd : ∀ i ⦃a b : β⦄, a < b → ∃ x, a < x ∧ x < b ∧ d x = i) :
    ∃ π : α ≃o β, d ∘ π = c := by
  cases nonempty_encodable α
  cases nonempty_encodable β
  let D : α ⊕ β → Cofinal (ColouredPartialIso c d) :=
    Sum.elim (definedAtLeft hd) (definedAtRight hc)
  let I : Ideal (ColouredPartialIso c d) := idealOfCofinals ⟨⟨∅, by simp⟩, by simp⟩ D
  have hF (a : α) : ∃ b, ∃ f ∈ I, (a, b) ∈ f.val.val := by
    obtain ⟨f, ⟨b, hb⟩, hf⟩ := cofinal_meets_idealOfCofinals _ D (Sum.inl a)
    exact ⟨b, f, hf, hb⟩
  have hG (b : β) : ∃ a, ∃ f ∈ I, (a, b) ∈ f.val.val := by
    obtain ⟨f, ⟨a, ha⟩, hf⟩ := cofinal_meets_idealOfCofinals _ D (Sum.inr b)
    exact ⟨a, f, hf, ha⟩
  choose F hF using hF
  choose G hG using hG
  refine ⟨OrderIso.ofCmpEqCmp F G fun a b ↦ ?_, funext fun a ↦ ?_⟩
  · obtain ⟨f, hf, ha⟩ := hF a
    obtain ⟨g, hg, hb⟩ := hG b
    obtain ⟨h, -, fh, gh⟩ := I.directed _ hf _ hg
    exact h.val.prop (a, _) (fh ha) (_, b) (gh hb)
  · obtain ⟨f, -, ha⟩ := hF a
    exact f.property _ ha

end Order
