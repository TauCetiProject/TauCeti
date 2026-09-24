/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import TauCeti.FieldTheory.IntermediateField.Lift
public import TauCeti.Order.Hom.Set

/-!
# The subfield dictionary for a field that need not be Galois

Mathlib's fundamental theorem of Galois theory, `IsGalois.intermediateFieldEquivSubgroup`,
describes the intermediate fields of a **Galois** extension `L / F` as the subgroups of
`Gal(L/F)`. It says nothing directly about the intermediate fields of `K / F` for an
intermediate field `K` that is not itself Galois over `F` — and for a general number field `K`
that is exactly the case of interest, `K` being presented inside its normal closure.

The correct statement is a relative one. The intermediate fields of `K / F` are an *interval*:
they are the intermediate fields of `L / F` below `K`, and under the Galois correspondence those
are the subgroups of `Gal(L/F)` **containing** `K.fixingSubgroup`. So

`IntermediateField F K ≃o (Set.Ici K.fixingSubgroup)ᵒᵈ`,

order-reversing, with the bottom `F` matching the top `⊤` and the top `K` matching
`K.fixingSubgroup` itself. Nothing here needs `K / F` to be normal; only `L / F` is Galois.

Both steps are existing order isomorphisms, composed:

* `IntermediateField.liftOrderIso` identifies `IntermediateField F K` with the interval
  `Set.Iic K` inside `IntermediateField F L`, replacing the abstract field `K` by a subfield of
  `L` (`TauCeti/FieldTheory/IntermediateField/Lift.lean`);
* `OrderIso.Iic` restricts the Galois correspondence itself to that interval. Its codomain,
  `Set.Iic (IsGalois.intermediateFieldEquivSubgroup K)`, is the down-set of
  `OrderDual.toDual K.fixingSubgroup` in `(Subgroup Gal(L/F))ᵒᵈ`, which is definitionally
  `(Set.Ici K.fixingSubgroup)ᵒᵈ` — so the composition needs no bridging step.

## Main results

* `IntermediateField.intermediateFieldEquivSubgroup`: the dictionary,
  `IntermediateField F K ≃o (Set.Ici K.fixingSubgroup)ᵒᵈ`.

The evaluation rules for `OrderIso.Iic`, which Mathlib does not state, are in
`TauCeti/Order/Hom/Set.lean`.

## References

* S. Lang, *Algebra*, Chapter VI §1, Theorem 1.1, for the fundamental theorem of Galois theory
  that the second step restricts.
-/

public section

namespace IntermediateField

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
variable (K : IntermediateField F L)

/-- **The subfield dictionary.** For `L / F` finite Galois and `K` any intermediate field, the
intermediate fields of `K / F` correspond order-reversingly to the subgroups of `Gal(L/F)`
containing `K.fixingSubgroup`. `K` itself need not be normal over `F`. -/
noncomputable def intermediateFieldEquivSubgroup :
    IntermediateField F K ≃o (Set.Ici K.fixingSubgroup)ᵒᵈ :=
  -- The codomain is reached by a definitional equality: `Set.Iic (toDual K.fixingSubgroup)` and
  -- `(Set.Ici K.fixingSubgroup)ᵒᵈ` agree as types and as `LE` instances, but not syntactically,
  -- which is why the evaluation lemmas below rewrite with `erw` rather than `rw`.
  (liftOrderIso K).trans ((IsGalois.intermediateFieldEquivSubgroup (F := F) (E := L)).Iic K)

/-- **The dictionary sends an intermediate field of `K / F` to the fixing subgroup of its lift.**
-/
@[simp]
theorem coe_intermediateFieldEquivSubgroup_apply (E' : IntermediateField F K) :
    (OrderDual.ofDual (K.intermediateFieldEquivSubgroup E')).1 = (lift E').fixingSubgroup := by
  erw [OrderIso.trans_apply, OrderIso.Iic_apply_coe]
  simp [liftOrderIso_apply]
  rfl

/-- **The inverse sends a subgroup to its fixed field**, read inside `L` through `lift`. -/
@[simp]
theorem lift_intermediateFieldEquivSubgroup_symm_apply (H : (Set.Ici K.fixingSubgroup)ᵒᵈ) :
    lift (K.intermediateFieldEquivSubgroup.symm H) = fixedField (OrderDual.ofDual H).1 := by
  erw [OrderIso.symm_trans_apply, liftOrderIso_symm_apply, lift_restrict,
    OrderIso.Iic_symm_apply_coe]
  simp [IsGalois.intermediateFieldEquivSubgroup_symm_apply]
  rfl

end IntermediateField

end
