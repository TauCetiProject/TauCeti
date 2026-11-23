/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Adjoint.Basic
public import TauCeti.RepresentationTheory.ClassicalGroups.Adjoint.Square.Products
public import TauCeti.RepresentationTheory.ClassicalGroups.Adjoint.Square.Surjectivity
public import TauCeti.RepresentationTheory.ClassicalGroups.Adjoint.Square.TracePairing
public import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.RepresentationTheory.Intertwining

/-!
# Trace transposes into the tensor square of the adjoint representation

The tensor product of the two trace pairings is a perfect invariant pairing.
Its inverse turns the dual of each contraction into an equivariant embedding.
The evaluation formulas characterize the images on arbitrary test tensors.
-/

public section

namespace TauCeti.AdjointSquare

open scoped TensorProduct
variable {K : Type*} [Field K] [NeZero (3 : K)]
local notation "V" => LieAlgebra.SpecialLinear.sl (Fin 3) K
local notation "T" => V ⊗[K] V
local notation "ρ" => SLAdjoint.adjointRep K 3
local notation "σ" => Representation.tprod ρ ρ

private noncomputable def liftMap (f : Representation.IntertwiningMap σ ρ) :
    Representation.IntertwiningMap ρ σ :=
  let hf : Representation.IsIntertwiningMap σ ρ f.toLinearMap := ⟨f.isIntertwining⟩
  squareTraceEquiv.symm.toIntertwiningMap.comp
    ((f.toLinearMap.dualMap.intertwiningMap_of_isIntertwiningMap _ _ hf.dualMap.isIntertwining).comp
      (SLAdjoint.traceDualEquiv K 3).toIntertwiningMap)

private theorem liftMap_apply (f : Representation.IntertwiningMap σ ρ) (x : V) :
    liftMap f x =
      squareTraceEquiv.symm (f.toLinearMap.dualMap (SLAdjoint.traceDualEquiv K 3 x)) := by
  simp only [liftMap, Representation.IntertwiningMap.comp_apply,
    Representation.Equiv.coe_toIntertwiningMap, LinearMap.toIntertwiningMap]

private theorem liftMap_injective (f : Representation.IntertwiningMap σ ρ)
    (hf : Function.Surjective f) : Function.Injective (liftMap f) := by
  intro x y h
  simp only [liftMap_apply] at h
  exact (SLAdjoint.traceDualEquiv K 3).toLinearEquiv.injective
    (LinearMap.dualMap_injective_of_surjective hf (squareTraceEquiv.symm.toLinearEquiv.injective h))

private theorem liftMap_pairing (f : Representation.IntertwiningMap σ ρ) (x : V) (t : T) :
    squareTrace (liftMap f x) t = (SLAdjoint.traceDualEquiv K 3 x) (f t) := by
  rw [← squareTraceEquiv_apply, liftMap_apply, Representation.Equiv.apply_symm_apply,
    LinearMap.dualMap_apply, Representation.IntertwiningMap.toLinearMap_apply]

/-- The trace transpose of the Lie bracket as an equivariant map into the tensor square. -/
noncomputable def alternatingEmbeddingMap : Representation.IntertwiningMap ρ σ :=
  liftMap (alternatingProductMap (K := K) (n := 3))

/-- The alternating product is surjective, so its trace transpose is injective. -/
theorem alternatingEmbeddingMap_injective : Function.Injective (alternatingEmbeddingMap (K := K)) :=
  liftMap_injective _ (alternatingProductMap_surjective K)

/-- The trace pairing on the tensor square characterizes the alternating embedding. -/
theorem alternatingEmbeddingMap_pairing (x : V) (t : T) :
    squareTrace (alternatingEmbeddingMap x) t =
      (SLAdjoint.traceDualEquiv K 3 x) (alternatingProductMap K 3 t) :=
  liftMap_pairing _ x t

/-- The trace transpose of the traceless symmetric product into the tensor square. -/
noncomputable def symmetricEmbeddingMap : Representation.IntertwiningMap ρ σ :=
  liftMap (symmetricProductMap K 3)

/-- The symmetric product is surjective, so its trace transpose is injective. -/
theorem symmetricEmbeddingMap_injective : Function.Injective (symmetricEmbeddingMap (K := K)) :=
  liftMap_injective _ (symmetricProductMap_surjective K)

/-- The trace pairing on the tensor square characterizes the symmetric embedding. -/
theorem symmetricEmbeddingMap_pairing (x : V) (t : T) :
    squareTrace (symmetricEmbeddingMap x) t =
      (SLAdjoint.traceDualEquiv K 3 x) (symmetricProductMap K 3 t) :=
  liftMap_pairing _ x t

end TauCeti.AdjointSquare
