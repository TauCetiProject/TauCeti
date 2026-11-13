/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# The measurable structure on optional values

The measurable structure on `Option X` is transported from `X ⊕ PUnit` through
`Equiv.optionEquivSumPUnit`. Thus `none` is a measurable singleton and `some` is a measurable
embedding. This permits measurable sequences that terminate, without requiring a
default element of `X`. The last result partitions a space into countably many disjoint measurable
sets together with the complement of their union, indexed by `Option`.
-/

public section

open MeasureTheory

namespace Option

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The disjoint-union measurable structure on optional values. -/
instance instMeasurableSpace : MeasurableSpace (Option X) :=
  MeasurableSpace.comap (Equiv.optionEquivSumPUnit.{0} X)
    Sum.instMeasurableSpace

/-- Optional values are measurably equivalent to a disjoint union with one cemetery value. -/
def measurableEquivSum : Option X ≃ᵐ X ⊕ PUnit where
  toEquiv := Equiv.optionEquivSumPUnit X
  measurable_toFun := comap_measurable _
  measurable_invFun := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := hs
    convert ht using 1
    ext x
    simp

/-- The equivalence sends a present value into the first summand. -/
@[simp] theorem measurableEquivSum_some (x : X) :
    measurableEquivSum (some x) = Sum.inl x := (rfl)

/-- The equivalence sends the cemetery value into the second summand. -/
@[simp] theorem measurableEquivSum_none :
    measurableEquivSum (none : Option X) = Sum.inr PUnit.unit := (rfl)

/-- Inserting a present value is a measurable embedding. -/
theorem measurableEmbedding_some : MeasurableEmbedding (some : X → Option X) := by
  exact measurableEquivSum.symm.measurableEmbedding.comp
    ⟨Sum.inl_injective, measurable_inl, fun _ hs => hs.inl_image⟩

/-- Inserting a present value is measurable. -/
@[fun_prop] theorem measurable_some : Measurable (some : X → Option X) :=
  measurableEmbedding_some.measurable

/-- The cemetery value is a measurable singleton. -/
theorem measurableSet_none : MeasurableSet ({none} : Set (Option X)) := by
  convert measurableEquivSum.measurable (measurableSet_range_inr (α := X) (β := PUnit)) using 1
  ext x
  cases x <;> simp

/-- An optional-valued function can be evaluated measurably, with a fixed cemetery value. -/
@[fun_prop] theorem measurable_elim (y : Y) {f : X → Y} (hf : Measurable f) :
    Measurable (fun x : Option X => x.elim y f) := by
  convert (hf.sumElim (measurable_const (a := y))).comp
    measurableEquivSum.measurable using 1
  ext x
  cases x <;> rfl

/-- Measurability on optional values is determined by the present-value branch;
the single cemetery value imposes no additional condition. -/
@[simp] theorem measurable_iff {f : Option X → Y} :
    Measurable f ↔ Measurable (fun x => f (some x)) := by
  refine ⟨fun hf => hf.comp measurable_some, fun hf => ?_⟩
  convert measurable_elim (f none) hf using 1
  ext x
  cases x <;> rfl

end Option

namespace TauCeti

open Function Set

/-- Disjoint measurable sets `Z i`, together with the complement of their union as one more cell
indexed by `none`, form a measurable partition of the space. -/
theorem measurable_disjoint_iUnion_option {X κ : Type*} [MeasurableSpace X] [Countable κ]
    {Z : κ → Set X} (hZm : ∀ i, MeasurableSet (Z i)) (hZd : Pairwise (Disjoint on Z)) :
    (∀ o : Option κ, MeasurableSet (o.elim (⋃ i, Z i)ᶜ Z)) ∧
      Pairwise (Disjoint on fun o : Option κ ↦ o.elim (⋃ i, Z i)ᶜ Z) ∧
      ⋃ o : Option κ, o.elim (⋃ i, Z i)ᶜ Z = univ := by
  refine ⟨?_, ?_, ?_⟩
  · rintro (_ | i)
    exacts [(MeasurableSet.iUnion hZm).compl, hZm _]
  · rintro (_ | i) (_ | j) hij
    · exact absurd rfl hij
    · exact disjoint_compl_left_iff_subset.2 (subset_iUnion Z j)
    · exact (disjoint_compl_left_iff_subset.2 (subset_iUnion Z i)).symm
    · exact hZd fun h ↦ hij (congrArg some h)
  · rw [iUnion_option]
    exact compl_union_self _

end TauCeti
