/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.Model.Basic
import TauCeti.FieldTheory.FunctionField.Belyi.BaseChange
import TauCeti.FieldTheory.FunctionField.ConstantExtension.RatFunc

/-!
# Constructing a Belyi model by adjoining a primitive element

Given an algebraic Belyi pair `X = (F, k(t) ↪ F)` over a field `k` of characteristic zero and a
subfield `K → k` over which `t` remains transcendental, a primitive element `z` of `F / k(t)` that
is integral over `K(t)` and satisfies `[K(t)⟮z⟯ : K(t)] = [F : k(t)]` defines a model of `X` over
`K` (`TauCeti.AlgebraicBelyiPair.modelOfAdjoinSimple`) without requiring `k / K` to be algebraic.

## Main definitions

* `TauCeti.AlgebraicBelyiPair.modelOfAdjoinSimple`: promotes a primitive element of `X / k(t)` with
  full degree over `K(t)` to a model of `X` over `K`.

## Main results

* `TauCeti.AlgebraicBelyiPair.finrank_modelOfAdjoinSimple_pair`: the constructed model has the same
  Belyi degree as `X`.
-/

public section

universe u

open IntermediateField

namespace TauCeti.AlgebraicBelyiPair

variable {k : Type u} [Field k] [CharZero k] (X : AlgebraicBelyiPair k)

/-- Promote a primitive element `z` of `X / k(t)` that is integral over `K(t)` of full degree
`[K(t)⟮z⟯ : K(t)] = [X : k(t)]` to a model of `X` over `K`. -/
noncomputable def modelOfAdjoinSimple {K : Type u} [Field K] [CharZero K] [Algebra K k]
    [Algebra (RatFunc K) (RatFunc k)]
    [Algebra (RatFunc K) X] [IsScalarTower (RatFunc K) (RatFunc k) X]
    (hC : ∀ c : K,
      algebraMap (RatFunc K) (RatFunc k) (algebraMap K (RatFunc K) c) =
        algebraMap k (RatFunc k) (algebraMap K k c))
    (hX : algebraMap (RatFunc K) (RatFunc k) RatFunc.X = RatFunc.X)
    {z : X} (hgen : (RatFunc k)⟮z⟯ = ⊤) (hz_int : IsIntegral (RatFunc K) z)
    (hfinrank : Module.finrank (RatFunc K) (RatFunc K)⟮z⟯ = Module.finrank (RatFunc k) X) :
    Model K X :=
  letI : Algebra K X := ((algebraMap k X).comp (algebraMap K k)).toAlgebra
  haveI : IsScalarTower K k X := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower K (RatFunc K) X :=
    IsScalarTower.of_algebraMap_eq (R := K) (S := RatFunc K) (A := X) fun c ↦ by
      rw [IsScalarTower.algebraMap_apply K k X,
        IsScalarTower.algebraMap_apply k (RatFunc k) X,
        ← hC c, ← IsScalarTower.algebraMap_apply (RatFunc K) (RatFunc k) X]
  let E : IntermediateField (RatFunc K) X := (RatFunc K)⟮z⟯
  letI : Algebra K E := ((algebraMap (RatFunc K) E).comp (algebraMap K (RatFunc K))).toAlgebra
  haveI : IsScalarTower K (RatFunc K) E := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower K E X :=
    IsScalarTower.of_algebraMap_eq (R := K) (S := E) (A := X) fun c ↦ by
      rw [IsScalarTower.algebraMap_apply K (RatFunc K) X,
        IsScalarTower.algebraMap_apply (RatFunc K) E X,
        ← IsScalarTower.algebraMap_apply K (RatFunc K) E]
  haveI : FiniteDimensional (RatFunc K) E := IntermediateField.adjoin.finiteDimensional hz_int
  have hX_E : algebraMap E X (algebraMap (RatFunc K) E RatFunc.X) =
      algebraMap (RatFunc k) X RatFunc.X := by
    rw [← IsScalarTower.algebraMap_apply (RatFunc K) E X,
      IsScalarTower.algebraMap_apply (RatFunc K) (RatFunc k) X, hX]
  have hcomp : constantCompositum E k X = ⊤ :=
    constantCompositum_adjoin_simple_ratFunc_eq_top hX hgen
  have hadj : IntermediateField.adjoin k (Set.range (algebraMap E X)) = ⊤ := by
    have h := hcomp
    rw [← IntermediateField.toSubfield_inj, IntermediateField.top_toSubfield,
      constantCompositum_def, IntermediateField.adjoin_toSubfield] at h
    rw [← IntermediateField.toSubfield_inj, IntermediateField.top_toSubfield,
      IntermediateField.adjoin_toSubfield, Set.union_comm, h]
  have hembed : ∀ c : K,
      algebraMap E X (algebraMap K E c) = algebraMap k X (algebraMap K k c) := fun c ↦ by
    rw [← IsScalarTower.algebraMap_apply K E X, IsScalarTower.algebraMap_apply K k X]
  { pair :=
      { carrier := E
        isAlgebraicBelyiPair :=
          X.isAlgebraicBelyiPair.of_finrank_eq hcomp hX_E hfinrank }
    embedding := algebraMap E X
    embedding_algebraMap := hembed
    embedding_algebraMap_X := hX_E
    adjoin_range_embedding := hadj }

/-- The model constructed from a primitive element `z` has the same Belyi degree as `X`. -/
@[simp]
theorem finrank_modelOfAdjoinSimple_pair {K : Type u} [Field K] [CharZero K] [Algebra K k]
    [Algebra (RatFunc K) (RatFunc k)]
    [Algebra (RatFunc K) X] [IsScalarTower (RatFunc K) (RatFunc k) X]
    (hC : ∀ c : K,
      algebraMap (RatFunc K) (RatFunc k) (algebraMap K (RatFunc K) c) =
        algebraMap k (RatFunc k) (algebraMap K k c))
    (hX : algebraMap (RatFunc K) (RatFunc k) RatFunc.X = RatFunc.X)
    {z : X} (hgen : (RatFunc k)⟮z⟯ = ⊤) (hz_int : IsIntegral (RatFunc K) z)
    (hfinrank : Module.finrank (RatFunc K) (RatFunc K)⟮z⟯ = Module.finrank (RatFunc k) X) :
    Module.finrank (RatFunc K)
        (X.modelOfAdjoinSimple hC hX hgen hz_int hfinrank).pair =
      Module.finrank (RatFunc k) X :=
  hfinrank

end TauCeti.AlgebraicBelyiPair
