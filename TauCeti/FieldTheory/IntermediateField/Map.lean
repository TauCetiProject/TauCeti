/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

/-!
# Intermediate fields along an algebra equivalence

An `F`-algebra equivalence `e : K ≃ₐ[F] L` identifies the intermediate fields of `K / F` with
those of `L / F`: pushing forward along `e` and pulling back along `e` are mutually inverse and
both monotone. Mathlib has the two maps, `IntermediateField.map` and `IntermediateField.comap`,
and the round trips `IntermediateField.comap_map` and
`IntermediateField.map_comap_eq_self_of_surjective`, but not the resulting order isomorphism,
nor the membership rule for `comap` that `Subalgebra.mem_comap` states one level down.

Having it as a single `OrderIso` is what lets the intermediate fields of an abstract field `K`
be transported to those of the subfield `φ(K)` of an ambient field along `φ.equivFieldRange`,
and then composed with the Galois correspondence; that composition is the embedding form of the
subfield dictionary in `TauCeti/FieldTheory/Galois/SubfieldDictionary.lean`.

## Main results

* `IntermediateField.mem_comap`: `x ∈ S.comap f ↔ f x ∈ S`.
* `IntermediateField.orderIsoMapComap`: the order isomorphism
  `IntermediateField F K ≃o IntermediateField F L` induced by `e : K ≃ₐ[F] L`, with
  `IntermediateField.orderIsoMapComap_apply` and `IntermediateField.orderIsoMapComap_symm_apply`
  giving its two directions as `map` and `comap`.

The name follows Mathlib's `Submodule.orderIsoMapComap`, the same construction for submodules.
-/

public section

namespace IntermediateField

variable {F K L : Type*} [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]

/-- **Membership in a preimage**: `x` lies in `S.comap f` exactly when `f x` lies in `S`. -/
@[simp]
theorem mem_comap {f : K →ₐ[F] L} {S : IntermediateField F L} {x : K} :
    x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl

/-- **An algebra equivalence identifies the intermediate fields of its source and target**: the
order isomorphism sending `E` to its image `E.map e`, with inverse the preimage `S.comap e`. -/
def orderIsoMapComap (e : K ≃ₐ[F] L) : IntermediateField F K ≃o IntermediateField F L where
  toFun E := E.map e.toAlgHom
  invFun S := S.comap e.toAlgHom
  left_inv E := comap_map e.toAlgHom E
  right_inv S := map_comap_eq_self_of_surjective e.surjective S
  map_rel_iff' {a b} := by
    simp only [Equiv.coe_fn_mk]
    rw [map_le_iff_le_comap, comap_map]

@[simp]
theorem orderIsoMapComap_apply (e : K ≃ₐ[F] L) (E : IntermediateField F K) :
    orderIsoMapComap e E = E.map e.toAlgHom :=
  (rfl)

@[simp]
theorem orderIsoMapComap_symm_apply (e : K ≃ₐ[F] L) (S : IntermediateField F L) :
    (orderIsoMapComap e).symm S = S.comap e.toAlgHom :=
  (rfl)

end IntermediateField

end
