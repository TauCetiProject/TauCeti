/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.PiTensorProduct.ZMod
public import TauCeti.RepresentationTheory.Tensor.Induction

/-!
# Tensor induction of the trivial mod-two representation

Tensor induction along a finite-index subgroup sends the trivial `𝔽₂`-representation to the
trivial `𝔽₂`-representation.  On the underlying indexed tensor product, the equivalence multiplies
the tensor factors.  It is invariant under the permutation action on the cosets, which makes it an
intertwining equivalence.

This coefficient identification is the target-side input for the cochain-level Evens norm.  The
construction follows L. Evens, "A generalization of the transfer map in the cohomology of groups",
*Transactions of the American Mathematical Society* 108 (1963), §§2–5.

## Main definitions

* `PiTensorProduct.trivialF2Equiv`: a finite nonempty tensor power of the universe-lifted `ZMod 2`
  coefficient is the same coefficient.
* `Subgroup.tensorInducedTrivialF2Iso`: tensor induction of the trivial `𝔽₂`-representation is
  isomorphic to the trivial representation.
-/

public section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace PiTensorProduct

variable {ι : Type v} [Fintype ι] [Nonempty ι]

/-- A finite nonempty tensor power over `ℤ` of the universe-lifted `ZMod 2` coefficient is again
that coefficient. -/
noncomputable def trivialF2Equiv :
    (⨂[ℤ] _ : ι, ULift.{u} (ZMod 2)) ≃ₗ[ℤ] ULift.{u} (ZMod 2) :=
  PiTensorProduct.congr (fun _ ↦ ULift.moduleEquiv) ≪≫ₗ
    zmodEquiv (ι := ι) 2 ≪≫ₗ ULift.moduleEquiv.symm

/-- The tensor-power equivalence multiplies the underlying mod-two values of a pure tensor. -/
@[simp]
theorem trivialF2Equiv_tprod (x : ι → ULift.{u} (ZMod 2)) :
    trivialF2Equiv (ι := ι) (tprod ℤ x) = ULift.up (∏ i, (x i).down) := by
  simp [trivialF2Equiv]

end PiTensorProduct

namespace Subgroup

variable {G : Type v} [Group G]

/-- The tensor-induced trivial mod-two representation is equivalent to the trivial mod-two
representation.  The chosen transversal affects the tensor-induced action, but not this
coefficient identification. -/
noncomputable def tensorInducedTrivialF2Equiv (U : Subgroup G) (s : U.LeftTransversal)
    [Fintype (G ⧸ U)] :
    (U.tensorInducedRepresentation s
      (Representation.trivial ℤ U (ULift.{v} (ZMod 2)))).Equiv
      (Representation.trivial ℤ G (ULift.{v} (ZMod 2))) :=
  Representation.Equiv.mk PiTensorProduct.trivialF2Equiv fun g ↦ by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      tensorInducedRepresentation_apply_tprod, Representation.trivial_apply]
    change PiTensorProduct.trivialF2Equiv
        (PiTensorProduct.tprod ℤ fun i ↦ x (g⁻¹ • i)) =
      PiTensorProduct.trivialF2Equiv (PiTensorProduct.tprod ℤ x)
    rw [PiTensorProduct.trivialF2Equiv_tprod, PiTensorProduct.trivialF2Equiv_tprod]
    apply ULift.ext
    exact (Equiv.prod_comp (MulAction.toPerm g⁻¹) fun i ↦ (x i).down)

/-- On a pure tensor, the equivalence from the tensor-induced trivial representation multiplies
the underlying mod-two values. -/
@[simp]
theorem tensorInducedTrivialF2Equiv_apply_tprod (U : Subgroup G) (s : U.LeftTransversal)
    [Fintype (G ⧸ U)] (x : G ⧸ U → ULift.{v} (ZMod 2)) :
    U.tensorInducedTrivialF2Equiv s (PiTensorProduct.tprod ℤ x) =
      ULift.up (∏ i, (x i).down) := by
  simp [tensorInducedTrivialF2Equiv]

/-- Tensor induction sends the trivial mod-two representation of a finite-index subgroup to the
trivial mod-two representation of the ambient group. -/
noncomputable def tensorInducedTrivialF2Iso (U : Subgroup G) (s : U.LeftTransversal)
    [Fintype (G ⧸ U)] :
    (U.tensorInductionFunctor (R := ℤ) s).obj
      (Rep.trivial ℤ U (ULift.{v} (ZMod 2))) ≅
      Rep.trivial ℤ G (ULift.{v} (ZMod 2)) := by
  rw [tensorInductionFunctor_obj]
  exact Rep.mkIso (U.tensorInducedTrivialF2Equiv s)

end Subgroup
