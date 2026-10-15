/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.PiTensorProduct.ZMod
public import TauCeti.RepresentationTheory.Tensor.Induction.Basic

/-!
# Tensor induction of trivial cyclic representations

Tensor induction along a finite-index subgroup sends the trivial `ZMod n`-representation to the
trivial `ZMod n`-representation; the case `n = 2` is the trivial `𝔽₂`-representation.  On the
underlying indexed tensor product, the equivalence multiplies the tensor factors.  It is invariant
under the permutation action on the cosets, which makes it an intertwining equivalence.

For `n = 2`, this coefficient identification is the target-side input for the cochain-level Evens
norm.  The construction follows L. Evens, "A generalization of the transfer map in the cohomology
of groups", *Transactions of the American Mathematical Society* 108 (1963), §§2–5.

## Main definitions

* `Subgroup.tensorInducedTrivialZModIso`: tensor induction of the trivial `ZMod n`-representation
  is isomorphic to the trivial representation.
-/

public section

open CategoryTheory
open scoped TensorProduct

universe v

namespace Subgroup

variable {G : Type v} [Group G] (n : ℕ)

/-- The tensor-induced trivial `ZMod n`-representation is equivalent to the trivial `ZMod n`
representation.  The chosen transversal affects the tensor-induced action, but not this
coefficient identification. -/
noncomputable def tensorInducedTrivialZModEquiv (U : Subgroup G) (s : U.LeftTransversal)
    [Fintype (G ⧸ U)] :
    (U.tensorInducedRepresentation s
      (Representation.trivial ℤ U (ULift.{v} (ZMod n)))).Equiv
      (Representation.trivial ℤ G (ULift.{v} (ZMod n))) :=
  Representation.Equiv.mk (PiTensorProduct.uliftZModEquiv n) fun g ↦ by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      tensorInducedRepresentation_apply_tprod, Representation.trivial_apply,
      LinearEquiv.coe_coe, PiTensorProduct.uliftZModEquiv_tprod]
    apply ULift.ext
    exact (Equiv.prod_comp (MulAction.toPerm g⁻¹) fun i ↦ (x i).down)

/-- On a pure tensor, the equivalence from the tensor-induced trivial representation multiplies
the underlying `ZMod n` values. -/
@[simp]
theorem tensorInducedTrivialZModEquiv_apply_tprod (U : Subgroup G) (s : U.LeftTransversal)
    [Fintype (G ⧸ U)] (x : G ⧸ U → ULift.{v} (ZMod n)) :
    U.tensorInducedTrivialZModEquiv n s (PiTensorProduct.tprod ℤ x) =
      ULift.up (∏ i, (x i).down) := by
  simp [tensorInducedTrivialZModEquiv]

/-- Tensor induction sends the trivial `ZMod n`-representation of a finite-index subgroup to the
trivial `ZMod n`-representation of the ambient group. -/
noncomputable def tensorInducedTrivialZModIso (U : Subgroup G) (s : U.LeftTransversal)
    [Fintype (G ⧸ U)] :
    (U.tensorInductionFunctor (R := ℤ) s).obj
      (Rep.trivial ℤ U (ULift.{v} (ZMod n))) ≅
      Rep.trivial ℤ G (ULift.{v} (ZMod n)) := by
  rw [tensorInductionFunctor_obj]
  exact Rep.mkIso (U.tensorInducedTrivialZModEquiv n s)

end Subgroup
