/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTwist
public import TauCeti.RepresentationTheory.Symmetric.SignCharacter
public import TauCeti.RepresentationTheory.Symmetric.TensorAction.Basic

/-!
# The sign-twisted permutation action on a tensor power

A permutation `σ` of a finite index type `ι` acts on the tensor power `⨂[R] _ : ι, M` of any
module by reindexing the tensor factors, `PiTensorProduct.reindexRepresentation`. This file twists
that action by the sign character: `σ` acts by `sign σ` times the reindexing. It is
`Representation.charTwist` of the reindexing representation by `TauCeti.signLinearCharacter`, so it
is again a representation, and it still commutes with the diagonal action of every linear map since
the sign is a scalar.

This is the action of the permutation diagrams of the Brauer algebra on the tensor powers of a
symplectic module, where the crossing must carry a sign to be absorbed by the alternating arcs; see
`TauCeti/RepresentationTheory/ClassicalGroups/BrauerGenerators/Symplectic/Crossing.lean`.

## Main definitions

* `PiTensorProduct.signReindexRepresentation`: the sign-twisted permutation action of
  `Equiv.Perm ι` on `⨂[R] _ : ι, M`.

## Main results

* `PiTensorProduct.signReindexRepresentation_tprod`: a permutation reindexes a pure tensor and
  multiplies it by its sign.
* `PiTensorProduct.signReindexRepresentation_swap` and
  `PiTensorProduct.signReindexRepresentation_swap_tprod`: a transposition of two distinct factors
  acts by minus the reindexing.
* `PiTensorProduct.commute_signReindexRepresentation_map`: the action commutes with applying the
  same linear map in every tensor factor.
-/

public section

open TauCeti
open scoped TensorProduct

universe u v w

namespace PiTensorProduct

variable (R : Type u) (M : Type v) (ι : Type w)
variable [CommRing R] [AddCommGroup M] [Module R M] [DecidableEq ι] [Fintype ι]

/-- **The sign-twisted permutation action** of `Equiv.Perm ι` on the `ι`-indexed tensor power of
`M`: a permutation reindexes the tensor factors and multiplies by its sign. -/
noncomputable def signReindexRepresentation :
    Representation R (Equiv.Perm ι) (⨂[R] _ : ι, M) :=
  (reindexRepresentation R M ι).charTwist (signLinearCharacter R ι)

variable {R M ι}

/-- A permutation acts by its sign times `PiTensorProduct.reindex`. -/
theorem signReindexRepresentation_apply (σ : Equiv.Perm ι) :
    signReindexRepresentation R M ι σ =
      ((Equiv.Perm.sign σ : ℤ) : R) • (reindex R (fun _ : ι => M) σ).toLinearMap := by
  rw [signReindexRepresentation, Representation.charTwist_apply, coe_signLinearCharacter_apply,
    reindexRepresentation_apply]

/-- **A permutation on a pure tensor**: the factors are reindexed and the result is multiplied by
the sign of the permutation. -/
@[simp]
theorem signReindexRepresentation_tprod (σ : Equiv.Perm ι) (v : ι → M) :
    signReindexRepresentation R M ι σ (tprod R v) =
      ((Equiv.Perm.sign σ : ℤ) : R) • tprod R fun t => v (σ.symm t) := by
  rw [signReindexRepresentation_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, reindex_tprod]

/-- A transposition of two distinct factors acts by minus the reindexing. -/
theorem signReindexRepresentation_swap {i j : ι} (hij : i ≠ j) :
    signReindexRepresentation R M ι (Equiv.swap i j) =
      -(reindex R (fun _ : ι => M) (Equiv.swap i j)).toLinearMap := by
  rw [signReindexRepresentation_apply, Equiv.Perm.sign_swap hij]
  push_cast
  exact neg_one_smul R (reindex R (fun _ : ι => M) (Equiv.swap i j)).toLinearMap

/-- **A transposition of two distinct factors on a pure tensor** exchanges the two factors and
changes the sign. -/
theorem signReindexRepresentation_swap_tprod {i j : ι} (hij : i ≠ j) (v : ι → M) :
    signReindexRepresentation R M ι (Equiv.swap i j) (tprod R v) =
      -tprod R fun t => v (Equiv.swap i j t) := by
  rw [signReindexRepresentation_swap hij, LinearMap.neg_apply, LinearEquiv.coe_coe,
    reindex_tprod, Equiv.symm_swap]

/-- **The sign-twisted permutation action commutes with the diagonal action** of every linear
map: permuting the tensor factors commutes with applying the same map in each of them, and the
sign is a scalar. -/
theorem commute_signReindexRepresentation_map (σ : Equiv.Perm ι) (f : M →ₗ[R] M) :
    Commute (signReindexRepresentation R M ι σ) (map fun _ : ι => f) := by
  rw [signReindexRepresentation, Representation.charTwist_apply]
  exact (commute_reindexRepresentation_map R M ι σ f).smul_left _

end PiTensorProduct
