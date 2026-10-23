/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Differential
public import TauCeti.Algebra.AlgebraicGroup.Representation.LieStable
public import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType

/-!
# Lie ideals as adjoint subrepresentations

For a connected affine group of finite type over an algebraically closed field of
characteristic zero, Lie ideals in its tangent Lie algebra are exactly the subrepresentations
of its adjoint representation. The identification preserves the underlying subspace and its
order. In particular, it turns the solvable radical of the tangent Lie algebra into an
adjoint subrepresentation, an input to the comparison of group and Lie-algebra radicals.

Over an arbitrary commutative ring, an adjoint subcomodule is still a Lie ideal. The converse
uses characteristic zero and connectedness through the equivalence between Lie-stable
subspaces and subcomodules, via
`Submodule.coact_mem_range_of_forall_differential_mem`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 22.
* J. E. Humphreys, *Linear Algebraic Groups*, §13.
-/

public section

open TauCeti

universe u

namespace TauCeti.Subcomodule

variable {R H : Type u} [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [Module.Finite R (Bialgebra.CotangentSpace R H)]
variable [Module.Projective R (Bialgebra.CotangentSpace R H)]

attribute [local instance] Derivation.adjointComodule

/-- An adjoint subcomodule is a Lie ideal, without smoothness or characteristic assumptions. -/
noncomputable def toLieIdeal
    (N : Subcomodule R H (Module.Dual R (Bialgebra.CotangentSpace R H))) :
    LieIdeal R (Module.Dual R (Bialgebra.CotangentSpace R H)) where
  __ := N.toSubmodule
  lie_mem := by
    intro x y hy
    have h := N.differential_mem (Derivation.cotangentDualLieEquiv x) hy
    rw [Derivation.differential_adjointComodule, LieEquiv.symm_apply_apply] at h
    exact (Subcomodule.mem_toSubmodule).mpr h

/-- Passage from an adjoint subcomodule to a Lie ideal preserves the underlying submodule. -/
@[simp]
theorem toLieIdeal_toSubmodule
    (N : Subcomodule R H (Module.Dual R (Bialgebra.CotangentSpace R H))) :
    N.toLieIdeal.toSubmodule = N.toSubmodule := (rfl)

/-- Membership in the Lie ideal is membership in the original adjoint subcomodule. -/
@[simp]
theorem mem_toLieIdeal
    (N : Subcomodule R H (Module.Dual R (Bialgebra.CotangentSpace R H)))
    (x : Module.Dual R (Bialgebra.CotangentSpace R H)) :
    x ∈ N.toLieIdeal ↔ x ∈ N := Iff.rfl

end TauCeti.Subcomodule

namespace LieIdeal

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k} [ConnectedSpace (PrimeSpectrum H)]

attribute [local instance] Derivation.adjointComodule

/-- A Lie ideal of a connected affine group in characteristic zero is a subrepresentation
of its adjoint representation, over an algebraically closed field. -/
noncomputable def toAdjointSubcomodule
    (I : LieIdeal k (Module.Dual k (Bialgebra.CotangentSpace k H))) :
    Subcomodule k H (Module.Dual k (Bialgebra.CotangentSpace k H)) where
  carrier := I.toSubmodule
  coact_mem' := by
    intro x hx
    apply Submodule.coact_mem_range_of_forall_differential_mem I.toSubmodule ?_ hx
    intro d y hy
    rw [Derivation.differential_adjointComodule]
    exact I.lie_mem hy

/-- Passage from a Lie ideal to an adjoint subcomodule preserves the underlying submodule. -/
@[simp]
theorem toAdjointSubcomodule_toSubmodule
    (I : LieIdeal k (Module.Dual k (Bialgebra.CotangentSpace k H))) :
    (I.toAdjointSubcomodule (H := H)).toSubmodule = I.toSubmodule := (rfl)

/-- Membership in the adjoint subcomodule is membership in the original Lie ideal. -/
@[simp]
theorem mem_toAdjointSubcomodule
    (I : LieIdeal k (Module.Dual k (Bialgebra.CotangentSpace k H)))
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    x ∈ I.toAdjointSubcomodule (H := H) ↔ x ∈ I := Iff.rfl

/-- Passing from a Lie ideal to its adjoint subcomodule and back recovers the ideal. -/
@[simp]
theorem toAdjointSubcomodule_toLieIdeal
    (I : LieIdeal k (Module.Dual k (Bialgebra.CotangentSpace k H))) :
    (I.toAdjointSubcomodule (H := H)).toLieIdeal = I := by
  ext
  rfl

end LieIdeal

namespace TauCeti

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k} [ConnectedSpace (PrimeSpectrum H)]

attribute [local instance] Derivation.adjointComodule

/-- Passing from an adjoint subcomodule to its Lie ideal and back recovers the subcomodule. -/
@[simp]
theorem Subcomodule.toLieIdeal_toAdjointSubcomodule
    (N : Subcomodule k H (Module.Dual k (Bialgebra.CotangentSpace k H))) :
    N.toLieIdeal.toAdjointSubcomodule (H := H) = N := by
  ext
  rfl

variable (H)

/-- For a connected affine group over an algebraically closed field of characteristic zero,
adjoint subrepresentations and Lie ideals are the same ordered collection of subspaces. -/
noncomputable def adjointSubcomoduleOrderIsoLieIdeal :
    Subcomodule k H (Module.Dual k (Bialgebra.CotangentSpace k H)) ≃o
      LieIdeal k (Module.Dual k (Bialgebra.CotangentSpace k H)) where
  toFun := Subcomodule.toLieIdeal
  invFun := LieIdeal.toAdjointSubcomodule (H := H)
  left_inv := Subcomodule.toLieIdeal_toAdjointSubcomodule
  right_inv := LieIdeal.toAdjointSubcomodule_toLieIdeal
  map_rel_iff' := Iff.rfl

/-- The order isomorphism sends a subcomodule to its Lie ideal. -/
@[simp]
theorem adjointSubcomoduleOrderIsoLieIdeal_apply
    (N : Subcomodule k H (Module.Dual k (Bialgebra.CotangentSpace k H))) :
    adjointSubcomoduleOrderIsoLieIdeal H N = N.toLieIdeal := (rfl)

/-- The inverse order isomorphism sends a Lie ideal to its adjoint subcomodule. -/
@[simp]
theorem adjointSubcomoduleOrderIsoLieIdeal_symm_apply
    (I : LieIdeal k (Module.Dual k (Bialgebra.CotangentSpace k H))) :
    (adjointSubcomoduleOrderIsoLieIdeal H).symm I = I.toAdjointSubcomodule (H := H) := (rfl)

end TauCeti
