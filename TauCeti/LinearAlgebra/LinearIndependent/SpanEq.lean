/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Independent families spanning a given subspace

For a finite-dimensional subspace `W` of a vector space `V` and a finite index type `ι` with as
many elements as the dimension of `W`, the linearly independent families `ι → V` whose span is
`W` are exactly the linearly independent families `ι → W`. Counting arguments that group
independent tuples by their span, such as the count of subspaces of a given dimension over a
finite field, reduce the size of each group to a count of independent tuples in `W` this way.

## Main results

* `Submodule.linearIndependentSpanEqEquiv`: linearly independent families in `V` spanning `W`
  are equivalent to linearly independent families in `W`, with its value on elements given by
  `Submodule.linearIndependentSpanEqEquiv_apply_coe` and
  `Submodule.linearIndependentSpanEqEquiv_symm_apply_coe_coe`.
-/

public section

open Module

namespace Submodule

variable {ι K V : Type*} [Fintype ι] [DivisionRing K] [AddCommGroup V] [Module K V]

/-- For a finite-dimensional subspace `W` with `finrank K W = Fintype.card ι`, the linearly
independent families `ι → V` spanning `W` are the linearly independent families `ι → W`. -/
def linearIndependentSpanEqEquiv (W : Submodule K V) [FiniteDimensional K W]
    (hW : finrank K W = Fintype.card ι) :
    {s : {s : ι → V // LinearIndependent K s} // span K (Set.range s.val) = W} ≃
      {t : ι → W // LinearIndependent K t} where
  toFun s := ⟨fun i ↦ ⟨s.val.val i, s.property.le (subset_span (Set.mem_range_self i))⟩,
    LinearIndependent.of_comp W.subtype s.val.property⟩
  invFun t := ⟨⟨W.subtype ∘ t.val, t.property.map' _ (ker_subtype _)⟩, by
    rw [Set.range_comp, span_image, t.property.span_eq_top_of_card_eq_finrank' hW.symm,
      map_subtype_top]⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable (W : Submodule K V) [FiniteDimensional K W] (hW : finrank K W = Fintype.card ι)

/-- `Submodule.linearIndependentSpanEqEquiv` keeps each vector of the family, viewed in `W`. -/
@[simp]
theorem linearIndependentSpanEqEquiv_apply_coe
    (s : {s : {s : ι → V // LinearIndependent K s} // span K (Set.range s.val) = W}) (i : ι) :
    ((W.linearIndependentSpanEqEquiv hW s).val i : V) = s.val.val i :=
  (rfl)

/-- The inverse of `Submodule.linearIndependentSpanEqEquiv` views a family in `W` as a family
in `V`. -/
@[simp]
theorem linearIndependentSpanEqEquiv_symm_apply_coe_coe
    (t : {t : ι → W // LinearIndependent K t}) :
    ((W.linearIndependentSpanEqEquiv hW).symm t).val.val = Subtype.val ∘ t.val :=
  (rfl)

end Submodule
