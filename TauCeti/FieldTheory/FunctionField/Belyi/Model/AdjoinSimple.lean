/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.Model.Basic
public import TauCeti.FieldTheory.FunctionField.Belyi.BaseChange
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.RatFunc

/-!
# Constructing a Belyi model by adjoining a primitive element

Given an algebraic Belyi pair `X = (F, k(t) ↪ F)` over a field `k` of characteristic zero and a
subfield `K → k`, using the canonical coefficient-extension map
`TauCeti.ratFuncMapRingHom K k : K(t) →+* k(t)` (which respects `K → k` and fixes `t`) and the
induced `K(t)`-action on `F` factoring through `k(t)`, a primitive element `z` of `F / k(t)`
satisfying `[K(t)⟮z⟯ : K(t)] = [F : k(t)]` defines a model of `X` over `K`
(`TauCeti.AlgebraicBelyiPair.modelOfAdjoinSimple`) without requiring `k / K` to be algebraic.

## Main definitions

* `TauCeti.AlgebraicBelyiPair.modelOfAdjoinSimple`: promotes a primitive element of `X / k(t)` with
  full degree over `K(t)` (with respect to the canonical map `K(t) → k(t) → X` fixing `K` and
  `t`) to a model of `X` over `K`.

## Main results

* `TauCeti.AlgebraicBelyiPair.modelOfAdjoinSimple_pair_carrier`: the underlying field of the
  constructed model is `K(t)⟮z⟯`.
* `TauCeti.AlgebraicBelyiPair.modelOfAdjoinSimple_embedding`: the embedding of the constructed
  model is the inclusion `K(t)⟮z⟯ →+* X`.
* `TauCeti.AlgebraicBelyiPair.fieldRange_modelOfAdjoinSimple_embedding`: the embedding image of the
  constructed model is `K(t)⟮z⟯`.
-/

public section

universe u

open IntermediateField

namespace TauCeti.AlgebraicBelyiPair

variable {k : Type u} [Field k] [CharZero k] (X : AlgebraicBelyiPair k)

/-- Promote a primitive element `z` of `X / k(t)` of full degree `[K(t)⟮z⟯ : K(t)] = [X : k(t)]`
to a model of `X` over `K`, using the canonical coefficient-extension map
`TauCeti.ratFuncMapRingHom K k : K(t) →+* k(t)` (which respects `K → k` and fixes `t`) and the
induced `K(t)`-action on `X` factoring through `k(t)`. -/
@[expose]
noncomputable def modelOfAdjoinSimple {K : Type u} [Field K] [CharZero K] [Algebra K k]
    {z : X} (hgen : (RatFunc k)⟮z⟯ = ⊤)
    (hfinrank :
      letI := X.ratFuncAlgebra K
      Module.finrank (RatFunc K) (RatFunc K)⟮z⟯ = Module.finrank (RatFunc k) X) :
    Model K X :=
  letI : Algebra (RatFunc K) (RatFunc k) := (ratFuncMapRingHom K k).toAlgebra
  letI := X.ratFuncAlgebra K
  haveI : IsScalarTower (RatFunc K) (RatFunc k) X := X.isScalarTower_ratFuncAlgebra K
  letI : Algebra K X := ((algebraMap k X).comp (algebraMap K k)).toAlgebra
  haveI : IsScalarTower K k X := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower K (RatFunc K) X :=
    IsScalarTower.of_algebraMap_eq (R := K) (S := RatFunc K) (A := X) fun c ↦ by
      rw [IsScalarTower.algebraMap_apply K k X, IsScalarTower.algebraMap_apply k (RatFunc k) X,
        algebraMap_ratFuncAlgebra_apply]
      simp only [_root_.RatFunc.algebraMap_eq_C, ratFuncMapRingHom_C]
  let E : IntermediateField (RatFunc K) X := (RatFunc K)⟮z⟯
  letI : Algebra K E := ((algebraMap (RatFunc K) E).comp (algebraMap K (RatFunc K))).toAlgebra
  haveI : IsScalarTower K (RatFunc K) E := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower K E X :=
    IsScalarTower.of_algebraMap_eq (R := K) (S := E) (A := X) fun c ↦ by
      rw [IsScalarTower.algebraMap_apply K (RatFunc K) X,
        IsScalarTower.algebraMap_apply (RatFunc K) E X,
        ← IsScalarTower.algebraMap_apply K (RatFunc K) E]
  haveI : FiniteDimensional (RatFunc K) E :=
    FiniteDimensional.of_finrank_pos (hfinrank ▸ Module.finrank_pos)
  have hX_E : algebraMap E X (algebraMap (RatFunc K) E RatFunc.X) =
      algebraMap (RatFunc k) X RatFunc.X := by
    rw [← IsScalarTower.algebraMap_apply (RatFunc K) E X,
      IsScalarTower.algebraMap_apply (RatFunc K) (RatFunc k) X,
      RingHom.algebraMap_toAlgebra, ratFuncMapRingHom_X]
  have hcomp : constantCompositum E k X = ⊤ :=
    constantCompositum_adjoin_simple_ratFunc_eq_top (ratFuncMapRingHom_X K k) hgen
  have hadj : IntermediateField.adjoin k (Set.range (algebraMap E X)) = ⊤ :=
    (constantCompositum_eq_top_iff_adjoin_range_eq_top E k X).mp hcomp
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

/-- The underlying field of the model constructed from `z` is `K(t)⟮z⟯`. -/
@[simp]
theorem modelOfAdjoinSimple_pair_carrier {K : Type u} [Field K] [CharZero K] [Algebra K k]
    {z : X} (hgen : (RatFunc k)⟮z⟯ = ⊤)
    (hfinrank :
      letI := X.ratFuncAlgebra K
      Module.finrank (RatFunc K) (RatFunc K)⟮z⟯ = Module.finrank (RatFunc k) X) :
    (X.modelOfAdjoinSimple hgen hfinrank).pair.carrier =
      (letI := X.ratFuncAlgebra K
      ↥(RatFunc K)⟮z⟯) :=
  (rfl)

/-- The embedding of the model constructed from `z` is the inclusion of `K(t)⟮z⟯` into `X`. -/
theorem modelOfAdjoinSimple_embedding {K : Type u} [Field K] [CharZero K] [Algebra K k]
    {z : X} (hgen : (RatFunc k)⟮z⟯ = ⊤)
    (hfinrank :
      letI := X.ratFuncAlgebra K
      Module.finrank (RatFunc K) (RatFunc K)⟮z⟯ = Module.finrank (RatFunc k) X) :
    (X.modelOfAdjoinSimple hgen hfinrank).embedding =
      (letI := X.ratFuncAlgebra K
      algebraMap (RatFunc K)⟮z⟯ X) :=
  (rfl)

/-- The embedding image of the model constructed from `z` is `K(t)⟮z⟯`. -/
@[simp]
theorem fieldRange_modelOfAdjoinSimple_embedding {K : Type u} [Field K] [CharZero K] [Algebra K k]
    {z : X} (hgen : (RatFunc k)⟮z⟯ = ⊤)
    (hfinrank :
      letI := X.ratFuncAlgebra K
      Module.finrank (RatFunc K) (RatFunc K)⟮z⟯ = Module.finrank (RatFunc k) X) :
    (X.modelOfAdjoinSimple hgen hfinrank).embedding.fieldRange =
      (letI := X.ratFuncAlgebra K
      ((RatFunc K)⟮z⟯).toSubfield) := by
  let _ := X.ratFuncAlgebra K
  rw [modelOfAdjoinSimple_embedding]
  exact Subfield.fieldRange_subtype ((RatFunc K)⟮z⟯).toSubfield

end TauCeti.AlgebraicBelyiPair
