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
Its inverse turns the dual of each contraction into an equivariant map. The alternating map is
injective whenever the size is nonzero in the field. The symmetric map is injective in sizes
at least three under the same field hypothesis.
The evaluation formulas characterize the images on arbitrary test tensors.
-/

public section

namespace TauCeti.AdjointSquare

open scoped TensorProduct
variable {K : Type*} [Field K] {n : ℕ} [NeZero (n : K)]
local notation "V" => LieAlgebra.SpecialLinear.sl (Fin n) K
local notation "T" => V ⊗[K] V
local notation "ρ" => SLAdjoint.adjointRep K n
local notation "σ" => Representation.tprod ρ ρ

private noncomputable def liftMap (f : Representation.IntertwiningMap σ ρ) :
    Representation.IntertwiningMap ρ σ :=
  squareTraceEquiv.symm.toIntertwiningMap.comp
    (f.dualMap.comp (SLAdjoint.traceDualEquiv K n).toIntertwiningMap)

private theorem liftMap_apply (f : Representation.IntertwiningMap σ ρ) (x : V) :
    liftMap f x =
      squareTraceEquiv.symm (f.toLinearMap.dualMap (SLAdjoint.traceDualEquiv K n x)) := by
  simp only [liftMap, Representation.IntertwiningMap.comp_apply,
    Representation.Equiv.coe_toIntertwiningMap]
  congr 1
  ext t
  simp

private theorem liftMap_injective (f : Representation.IntertwiningMap σ ρ)
    (hf : Function.Surjective f) : Function.Injective (liftMap f) := by
  intro x y h
  simp only [liftMap_apply] at h
  exact (SLAdjoint.traceDualEquiv K n).toLinearEquiv.injective
    (LinearMap.dualMap_injective_of_surjective hf (squareTraceEquiv.symm.toLinearEquiv.injective h))

private theorem liftMap_pairing (f : Representation.IntertwiningMap σ ρ) (x : V) (t : T) :
    squareTrace (liftMap f x) t = (SLAdjoint.traceDualEquiv K n x) (f t) := by
  rw [← squareTraceEquiv_apply, liftMap_apply, Representation.Equiv.apply_symm_apply,
    LinearMap.dualMap_apply, Representation.IntertwiningMap.toLinearMap_apply]

variable (K n)

/-- The trace transpose of the Lie bracket as an equivariant map into the tensor square. -/
noncomputable def alternatingEmbeddingMap : Representation.IntertwiningMap ρ σ :=
  liftMap (alternatingProductMap K n)

/-- The Lie bracket has injective trace transpose when the size is nonzero in the field. -/
theorem alternatingEmbeddingMap_injective :
    Function.Injective (alternatingEmbeddingMap K n) :=
  liftMap_injective _ (alternatingProductMap_surjective_of_isUnit K n (NeZero.ne (n : K)).isUnit)

variable {K n}

/-- The trace pairing on the tensor square characterizes the alternating embedding. -/
theorem alternatingEmbeddingMap_pairing (x : V) (t : T) :
    squareTrace (alternatingEmbeddingMap K n x) t =
      (SLAdjoint.traceDualEquiv K n x) (alternatingProductMap K n t) :=
  liftMap_pairing _ x t

local instance : Invertible (Fintype.card (Fin n) : K) :=
  invertibleOfNonzero (by simpa only [Fintype.card_fin] using NeZero.ne (n : K))

variable (K n)

/-- The trace transpose of the traceless symmetric product into the tensor square. -/
noncomputable def symmetricEmbeddingMap : Representation.IntertwiningMap ρ σ :=
  liftMap (symmetricProductMap K n)

/-- For sizes at least three, the transpose of the symmetric contraction is injective. -/
theorem symmetricEmbeddingMap_injective (hn : 3 ≤ n) :
    Function.Injective (symmetricEmbeddingMap K n) :=
  liftMap_injective _ (symmetricProductMap_surjective K n hn)

variable {K n}

/-- The trace pairing on the tensor square characterizes the symmetric transpose, which is
injective for sizes at least three. -/
theorem symmetricEmbeddingMap_pairing (x : V) (t : T) :
    squareTrace (symmetricEmbeddingMap K n x) t =
      (SLAdjoint.traceDualEquiv K n x) (symmetricProductMap K n t) :=
  liftMap_pairing _ x t

end TauCeti.AdjointSquare
