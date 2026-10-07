/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import TauCeti.FieldTheory.IntermediateField.Lift
public import TauCeti.FieldTheory.IntermediateField.Map
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

The same dictionary holds for an *abstract* field `K` given with an embedding
`φ : K →ₐ[F] L`, which is how a number field sits inside its normal closure:

`IntermediateField F K ≃o (Set.Ici φ.fieldRange.fixingSubgroup)ᵒᵈ`,

sending `E` to the subgroup fixing `φ(E)` and a subgroup `H` to the preimage `φ⁻¹(L^H)`. It is
the intermediate-field dictionary for `φ(K)`, transported along `φ.equivFieldRange` by
`IntermediateField.orderIsoMapComap`. The base subgroup `φ.fieldRange.fixingSubgroup` is the
stabilizer of `φ` under postcomposition, by
`TauCeti.FieldTheory.stabilizer_algHom_eq_fixingSubgroup`. Under the dictionary the degree
`[E : F]` of an intermediate field is the index of its subgroup.

## Main results

* `IntermediateField.intermediateFieldEquivSubgroup`: the dictionary,
  `IntermediateField F K ≃o (Set.Ici K.fixingSubgroup)ᵒᵈ`.
* `AlgHom.intermediateFieldEquivSubgroup`: the dictionary of an embedded field,
  `IntermediateField F K ≃o (Set.Ici φ.fieldRange.fixingSubgroup)ᵒᵈ`, with the evaluation rules
  `AlgHom.coe_intermediateFieldEquivSubgroup_apply` and
  `AlgHom.intermediateFieldEquivSubgroup_symm_apply`.
* `AlgHom.index_intermediateFieldEquivSubgroup_apply`: the subgroup attached to `E` has index
  `[E : F]`.

The evaluation rules for `OrderIso.Iic`, which Mathlib does not state, are in
`TauCeti/Order/Hom/Set.lean`.

## References

* S. Lang, *Algebra*, Chapter VI §1, Theorem 1.1, for the fundamental theorem of Galois theory
  that the second step restricts.
* J. Neukirch, *Algebraic Number Theory*, Chapter I, §9, for subfields of a number field read
  off its normal closure.
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

namespace AlgHom

variable {F K L : Type*} [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]
  [FiniteDimensional F L] [IsGalois F L]

/-- **The subfield dictionary of an embedded field.** For `L / F` finite Galois and any
embedding `φ : K →ₐ[F] L`, the intermediate fields of `K / F` correspond order-reversingly to the
subgroups of `Gal(L/F)` containing the subgroup fixing `φ(K)` pointwise. `K` is an abstract
field, not a subfield of `L`, and need not be normal over `F`. -/
noncomputable def intermediateFieldEquivSubgroup (φ : K →ₐ[F] L) :
    IntermediateField F K ≃o (Set.Ici φ.fieldRange.fixingSubgroup)ᵒᵈ :=
  (IntermediateField.orderIsoMapComap φ.equivFieldRange).trans
    φ.fieldRange.intermediateFieldEquivSubgroup

/-- **The dictionary sends an intermediate field of `K / F` to the subgroup fixing its image.** -/
@[simp]
theorem coe_intermediateFieldEquivSubgroup_apply (φ : K →ₐ[F] L) (E : IntermediateField F K) :
    (OrderDual.ofDual (φ.intermediateFieldEquivSubgroup E)).1 = (E.map φ).fixingSubgroup := by
  -- the image of `E` in `φ(K)`, lifted back to `L`, is the image of `E` under `φ` itself
  have hφ : (IntermediateField.val φ.fieldRange).comp φ.equivFieldRange.toAlgHom = φ :=
    AlgHom.ext (equivFieldRange_apply_coe φ)
  rw [intermediateFieldEquivSubgroup, OrderIso.trans_apply,
    IntermediateField.coe_intermediateFieldEquivSubgroup_apply,
    IntermediateField.orderIsoMapComap_apply, IntermediateField.lift, IntermediateField.map_map,
    hφ]

/-- **The inverse sends a subgroup to the preimage of its fixed field.** -/
@[simp]
theorem intermediateFieldEquivSubgroup_symm_apply (φ : K →ₐ[F] L)
    (H : (Set.Ici φ.fieldRange.fixingSubgroup)ᵒᵈ) :
    φ.intermediateFieldEquivSubgroup.symm H =
      (IntermediateField.fixedField (OrderDual.ofDual H).1).comap φ := by
  rw [← IntermediateField.lift_intermediateFieldEquivSubgroup_symm_apply,
    intermediateFieldEquivSubgroup, OrderIso.symm_trans_apply,
    IntermediateField.orderIsoMapComap_symm_apply]
  ext x
  rw [IntermediateField.mem_comap, IntermediateField.mem_comap,
    ← equivFieldRange_apply_coe φ x, IntermediateField.mem_lift, AlgEquiv.coe_toAlgHom]

/-- **Degree is index.** The subgroup attached to an intermediate field `E` of `K / F` has index
`[E : F]` in `Gal(L/F)`. -/
theorem index_intermediateFieldEquivSubgroup_apply (φ : K →ₐ[F] L) (E : IntermediateField F K) :
    (OrderDual.ofDual (φ.intermediateFieldEquivSubgroup E)).1.index = Module.finrank F E := by
  rw [coe_intermediateFieldEquivSubgroup_apply,
    ← IntermediateField.finrank_eq_fixingSubgroup_index, (E.equivMap φ).toLinearEquiv.finrank_eq]

end AlgHom

end
