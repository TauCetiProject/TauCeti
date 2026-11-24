/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Coalgebra.Basic

/-!
# Subcoalgebras

This file defines subcoalgebras of a coalgebra as submodules whose elements have
comultiplication in the tensor square of the submodule. It is deliberately a lightweight
predicate-style API: over a general commutative semiring, the map `D ⊗ D → C ⊗ C` need not be
known injective, so the induced coalgebra structure on `D` is not registered here (see
`TauCeti.Algebra.Coalgebra.Subcoalgebra.Structure` for the flat case). Since the definition only
involves the comultiplication, it is stated for a `CoalgebraStruct`. Finitely generated
subcoalgebras can be expressed with `Module.Finite R D.toSubmodule`.

## Main definitions

* `TauCeti.Subcoalgebra`: a submodule stable under comultiplication.
* `TauCeti.Subcoalgebra.toSubmodule`: the underlying submodule.
* `TauCeti.Subcoalgebra.ofSubmodule`: the subcoalgebra given by a stable submodule.
* `⊤` and `⊥`: the full and zero subcoalgebras.

## References

This follows the standard coalgebra definition: a subcoalgebra `D ≤ C` satisfies
`Δ(D) ⊆ D ⊗ D`. See Sweedler, *Hopf Algebras*, Chapter 2.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v

variable (R : Type u) (C : Type v)
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [CoalgebraStruct R C]

/-- A subcoalgebra of an `R`-coalgebra `C`. Only the comultiplication of `C` is used, so `C`
need only carry a `CoalgebraStruct`.

It is an `R`-submodule `carrier` such that the comultiplication of every element of
`carrier` lies in the range of `carrier ⊗ carrier → C ⊗ C`. -/
structure Subcoalgebra where
  /-- The underlying submodule of a subcoalgebra. -/
  carrier : Submodule R C
  /-- The comultiplication of an element of the submodule lies in its tensor square. -/
  comul_mem' :
    ∀ ⦃c : C⦄, c ∈ carrier →
      Coalgebra.comul (R := R) c ∈
        LinearMap.range (TensorProduct.map carrier.subtype carrier.subtype)

namespace Subcoalgebra

variable {R C}

instance : SetLike (Subcoalgebra R C) C where
  coe D := D.carrier
  coe_injective D E h := by
    cases D; cases E
    congr
    exact SetLike.ext' h

instance : AddSubmonoidClass (Subcoalgebra R C) C where
  add_mem {D} := D.carrier.add_mem
  zero_mem D := D.carrier.zero_mem

instance : SMulMemClass (Subcoalgebra R C) R C where
  smul_mem {D} r {_} hc := D.carrier.smul_mem r hc

instance : PartialOrder (Subcoalgebra R C) :=
  .ofSetLike (Subcoalgebra R C)

/-- The underlying submodule of a subcoalgebra. -/
@[expose] def toSubmodule (D : Subcoalgebra R C) : Submodule R C :=
  D.carrier

@[simp]
theorem mem_carrier {D : Subcoalgebra R C} {c : C} : c ∈ D.carrier ↔ c ∈ D :=
  Iff.rfl

@[simp]
theorem mem_toSubmodule {D : Subcoalgebra R C} {c : C} : c ∈ D.toSubmodule ↔ c ∈ D :=
  Iff.rfl

theorem toSubmodule_carrier (D : Subcoalgebra R C) : D.toSubmodule = D.carrier :=
  rfl

theorem toSubmodule_le_toSubmodule {D E : Subcoalgebra R C} :
    D.toSubmodule ≤ E.toSubmodule ↔ D ≤ E :=
  Iff.rfl

/-- Two subcoalgebras are equal when they contain the same elements. -/
@[ext]
theorem ext {D E : Subcoalgebra R C} (h : ∀ c : C, c ∈ D ↔ c ∈ E) : D = E :=
  SetLike.ext h

/-- The comultiplication of an element of a subcoalgebra belongs to its tensor square. -/
theorem comul_mem (D : Subcoalgebra R C) {c : C} (hc : c ∈ D) :
    Coalgebra.comul (R := R) (A := C) c ∈
      LinearMap.range (TensorProduct.map D.carrier.subtype D.carrier.subtype) :=
  D.comul_mem' hc

/-- Constructor from a submodule and the tensor-square stability condition. -/
@[expose] def ofSubmodule (D : Submodule R C) (hD :
      ∀ ⦃c : C⦄, c ∈ D →
        Coalgebra.comul (R := R) (A := C) c ∈
          LinearMap.range (TensorProduct.map D.subtype D.subtype)) :
    Subcoalgebra R C where
  carrier := D
  comul_mem' := hD

@[simp]
theorem ofSubmodule_carrier (D : Submodule R C) (hD) :
    (ofSubmodule (R := R) (C := C) D hD).carrier = D :=
  rfl

@[simp]
theorem mem_ofSubmodule {D : Submodule R C} {hD} {c : C} :
    c ∈ ofSubmodule (R := R) (C := C) D hD ↔ c ∈ D :=
  Iff.rfl

/-- The full coalgebra as a subcoalgebra. -/
instance instTop : Top (Subcoalgebra R C) where
  top :=
    { carrier := ⊤
      comul_mem' c _ := by
        rw [TensorProduct.range_mapIncl, TensorProduct.map₂_mk_top_top_eq_top]
        exact Submodule.mem_top }

@[simp]
theorem top_toSubmodule : (⊤ : Subcoalgebra R C).toSubmodule = (⊤ : Submodule R C) :=
  rfl

@[simp]
theorem mem_top (c : C) : c ∈ (⊤ : Subcoalgebra R C) :=
  Submodule.mem_top

instance : OrderTop (Subcoalgebra R C) where
  top := ⊤
  le_top _ _ _ := Submodule.mem_top

/-- The zero submodule as a subcoalgebra. -/
instance instBot : Bot (Subcoalgebra R C) where
  bot :=
    { carrier := ⊥
      comul_mem' c hc := by
        rw [(Submodule.mem_bot R).1 hc, map_zero]
        exact zero_mem _ }

@[simp]
theorem bot_toSubmodule : (⊥ : Subcoalgebra R C).toSubmodule = (⊥ : Submodule R C) :=
  rfl

@[simp]
theorem mem_bot {c : C} : c ∈ (⊥ : Subcoalgebra R C) ↔ c = 0 :=
  Submodule.mem_bot (R := R) (M := C)

/-- The zero subcoalgebra is contained in every subcoalgebra. -/
instance : OrderBot (Subcoalgebra R C) where
  bot := ⊥
  bot_le D c hc := by
    rw [mem_bot.1 hc]
    exact zero_mem D

end Subcoalgebra

end TauCeti
