/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.OrderClass
public import TauCeti.SetTheory.Cardinal.AlephOne

/-!
# Examples: coded linear orders and coded trees

The code of `(ℕ, ≤)` is a coded linear order and a coded tree (one infinite branch). The code of
`(ℕ, <)` is not a coded linear order, as it is irreflexive, and the code of `(ℕ, ≥)` is not a
coded tree, as it has no least element. The coded trees on `ℕ` do not form a closed class.

The code in which every pair is related fails antisymmetry, and the code of divisibility on `ℕ` is
a partial order that is not total, so neither is a coded linear order. The code of the star, in
which `0` lies below every element and other pairs are incomparable, is a coded tree, while the
code of `(ℤ, ≤)` transported to `ℕ` is not, having no least element. Inserting `n` between `0`
and `1` in the star still gives a coded tree.

A finite tree of finite sequences, such as `{[], [0], [1], [0, 0]}`, has no code on `ℕ`, while the
full tree `List ℕ` has a code in `treeClass`.

The coded linear orders on `ℕ` meet uncountably many isomorphism classes. Adding the diagonal to
the relation of a coded strict well-order gives a coded linear order. By
`exists_mem_wellOrderClass_type_eq`, every order type `β` with `ω ≤ β < ω₁` is the type of a coded
strict well-order on `ℕ`, and isomorphic codes with the diagonal added have strict parts of the
same type. So `β ↦` the class of the reflexive closure of a code of type `β` is injective on the
uncountable interval `[ω, ω₁)`, and `linearOrderClass` meets uncountably many classes of
`isoSetoid Language.order ℕ`.
-/

public section

open FirstOrder FirstOrder.Language TauCeti RelationalConfiguration Set
open scoped Ordinal

-- The code of `(ℕ, ≤)` is a coded linear order.
example : @ofStructure Language.order ℕ (orderStructure ℕ) ∈ linearOrderClass :=
  ofStructure_mem_linearOrderClass

-- The code of `(ℕ, ≤)` is a coded tree.
example : @ofStructure Language.order ℕ (orderStructure ℕ) ∈ treeClass :=
  ofStructure_mem_treeClass strictMono_id

-- The code of `(ℕ, <)` is not a coded linear order: it is irreflexive.
example : ofRel (fun x y : ℕ => x < y) ∉ linearOrderClass := by
  rw [mem_linearOrderClass, codeRel_ofRel]
  intro h
  exact lt_irrefl 0 (h.refl 0)

-- The code of `(ℕ, ≥)` is not a coded tree: it has no least element.
example : ofRel (fun x y : ℕ => y ≤ x) ∉ treeClass := by
  rw [mem_treeClass, codeRel_ofRel]
  intro h
  obtain ⟨a, ha⟩ := h.exists_forall
  exact Nat.not_succ_le_self a (ha (a + 1))

-- The coded trees on `ℕ` do not form a closed class.
example : ¬ IsClosed (treeClass (V := ℕ)) :=
  not_isClosed_treeClass

-- The code in which every pair is related is not a coded linear order: it is not antisymmetric.
example : ofRel (fun _ _ : ℕ => True) ∉ linearOrderClass := by
  rw [mem_linearOrderClass, codeRel_ofRel]
  intro h
  exact absurd (h.antisymm 0 1 trivial trivial) (by decide)

-- The code of divisibility on `ℕ` is a partial order.
example : IsPartialOrder ℕ (codeRel leSymb (ofRel (fun x y : ℕ => x ∣ y))) := by
  rw [codeRel_ofRel]
  infer_instance

-- The code of divisibility on `ℕ` is not a coded linear order: `2` and `3` are incomparable.
example : ofRel (fun x y : ℕ => x ∣ y) ∉ linearOrderClass := by
  rw [mem_linearOrderClass, codeRel_ofRel]
  intro h
  rcases h.total 2 3 with h₂ | h₃
  · exact absurd h₂ (by decide)
  · exact absurd h₃ (by decide)

-- The code of `(ℤ, ≤)` transported to `ℕ` is not a coded tree: it has no least element.
example :
    ofRel (fun x y : ℕ => Equiv.intEquivNat.symm x ≤ Equiv.intEquivNat.symm y) ∉ treeClass := by
  rw [mem_treeClass, codeRel_ofRel]
  intro h
  obtain ⟨a, ha⟩ := h.exists_forall
  have := ha (Equiv.intEquivNat (Equiv.intEquivNat.symm a - 1))
  simp at this

namespace TauCeti.Examples.ModelTheory.OrderClass

/-- **The coded linear orders on `ℕ` meet uncountably many isomorphism classes.** -/
theorem not_countable_image_mk_linearOrderClass :
    ¬ ((Quotient.mk (isoSetoid Language.order ℕ)) '' linearOrderClass).Countable := by
  intro h
  -- A code of type `β` for each `β ∈ [ω, ω₁)`.
  have hcode (β : (Ico ω ω₁ : Set Ordinal.{0})) :=
    exists_mem_wellOrderClass_type_eq (V := ℕ) (L := Language.order) leSymb
      (β := (β : Ordinal.{0})) β.property.1 β.property.2
  choose c hc htype using hcode
  let f : (Ico ω ω₁ : Set Ordinal.{0}) →
      (Quotient.mk (isoSetoid Language.order ℕ)) '' linearOrderClass :=
    fun β =>
      have := mem_wellOrderClass.1 (hc β)
      ⟨Quotient.mk _ (addDiag (c β)), addDiag (c β), addDiag_mem_linearOrderClass, rfl⟩
  have hf : Function.Injective f := fun β γ hβγ => by
    have := type_eq_of_isoSetoid_addDiag (hc β) (hc γ)
      (Quotient.exact (congrArg Subtype.val hβγ))
    exact Subtype.ext ((htype β).symm.trans (this.trans (htype γ)))
  have : Countable (Ico ω ω₁ : Set Ordinal.{0}) := by
    have := h.to_subtype
    exact hf.countable
  exact not_countable_Ico_omega_one Ordinal.omega0_lt_omega_one (countable_coe_iff.1 this)

/-! ### The star -/

/-- The code of the star, in which `0` lies below every element and other pairs are
incomparable. -/
noncomputable abbrev star : RelationalConfiguration Language.order ℕ :=
  ofRel fun x y : ℕ => x = 0 ∨ x = y

/-- The star with `n` inserted between `0` and `1`: for `2 ≤ n`, `0 < n < 1` and every other
vertex is a leaf above `0`; for `n = 0` and `n = 1` this is the star. -/
noncomputable abbrev starInsert (n : ℕ) : RelationalConfiguration Language.order ℕ :=
  ofRel fun x y : ℕ => x = y ∨ x = 0 ∨ x = n ∧ y = 1

/-- The star with `n` inserted between `0` and `1` is a coded tree. -/
theorem starInsert_mem_treeClass (n : ℕ) : starInsert n ∈ treeClass := by
  rw [mem_treeClass, codeRel_ofRel]
  have hpo : IsPartialOrder ℕ (fun x y : ℕ => x = y ∨ x = 0 ∨ x = n ∧ y = 1) :=
    { refl := fun _ => .inl rfl
      trans := by
        rintro a b c (h | h | ⟨h, h'⟩) (k | k | ⟨k, k'⟩) <;> omega
      antisymm := by
        rintro a b (h | h | ⟨h, h'⟩) (k | k | ⟨k, k'⟩) <;> omega }
  refine ⟨hpo, ⟨0, fun _ => .inr (.inl rfl)⟩, fun x => ?_, fun x => ?_⟩
  · exact (((Set.finite_singleton x).union (Set.finite_singleton 0)).union
      (Set.finite_singleton n)).subset fun y hy => by
        simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq] at hy ⊢
        omega
  · rintro a ha b hb -
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    omega

/-- Inserting `0` between `0` and `1` leaves the star unchanged. -/
theorem starInsert_zero : starInsert 0 = star :=
  congrArg ofRel (funext₂ fun _ _ => propext (by omega))

/-- The star is a coded tree. -/
theorem star_mem_treeClass : star ∈ treeClass :=
  starInsert_zero ▸ starInsert_mem_treeClass 0

/-! ### Trees of finite sequences -/

/-- A finite tree of finite sequences has no code on `ℕ`: its prefix order is isomorphic to the
order of no coded tree, since `ℕ` is infinite. -/
theorem isEmpty_relIso_of_finite {T : Descriptive.tree ℕ} (hT : (T : Set (List ℕ)).Finite)
    (c : RelationalConfiguration Language.order ℕ) :
    IsEmpty (codeRel leSymb c ≃r fun x y : T => (x : List ℕ) <+: y) :=
  ⟨fun e => have : Finite T := hT.to_subtype
    not_finite_iff_infinite.2 inferInstance (Finite.of_injective e e.injective)⟩

/-- The tree `{[], [0], [1], [0, 0]}`. -/
def smallTree : Descriptive.tree ℕ :=
  ⟨{[], [0], [1], [0, 0]}, by
    intro x a h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
    rcases h with h | h | h | h
    · simp at h
    · obtain ⟨rfl, -⟩ := List.append_eq_singleton_iff.1 h |>.resolve_right (by simp)
      simp
    · obtain ⟨rfl, -⟩ := List.append_eq_singleton_iff.1 h |>.resolve_right (by simp)
      simp
    · obtain rfl : x = [0] := by simpa using congrArg List.dropLast h
      simp⟩

/-- The sequences of `smallTree`. -/
theorem coe_smallTree : (smallTree : Set (List ℕ)) = {[], [0], [1], [0, 0]} := (rfl)

/-- The tree `{[], [0], [1], [0, 0]}` is finite and so has no code on `ℕ`. -/
example (c : RelationalConfiguration Language.order ℕ) :
    IsEmpty (codeRel leSymb c ≃r fun x y : smallTree => (x : List ℕ) <+: y) :=
  isEmpty_relIso_of_finite (coe_smallTree ▸ Set.toFinite _) c

/-- The full tree `List ℕ`, infinitely branching, has a code in `treeClass`. -/
example : ∃ c : RelationalConfiguration Language.order ℕ, c ∈ treeClass ∧
    Nonempty (codeRel leSymb c ≃r fun x y : (⊤ : Descriptive.tree ℕ) => (x : List ℕ) <+: y) :=
  exists_mem_treeClass_relIso (by simpa using Set.infinite_univ)

end TauCeti.Examples.ModelTheory.OrderClass
