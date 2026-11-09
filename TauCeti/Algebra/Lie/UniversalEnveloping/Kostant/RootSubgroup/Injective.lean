/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Elementary.Basic
public import TauCeti.RingTheory.Nilpotent.Primitive

/-!
# Injective Kostant root parameters

A primitive two-step string in an integral Kostant module detects the root parameter
over any commutative ring. This specializes the basis-free exponential criterion
`TauCeti.baseChangeExp_injective_of_isPrimitive` to `kostantRootSubgroupParam`.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

variable {L I κ V : Type*} [LieRing L] [LieAlgebra ℚ L] [AddCommGroup V] [Module ℚ V]

-- Match the tensor module used by the integral point action.
attribute [local instance high] Algebra.toModule

/-- A primitive two-step root string makes the Kostant root parameter injective after
scalar extension to every commutative ring. -/
theorem kostantRootSubgroupParam_injective_of_isPrimitive (e : I → L) (h : κ → L)
    (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V) (M : AddSubgroup V)
    (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M) (i : I)
    (hnil : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (v w : M) (hvw : ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) (v : V) = (w : V))
    (hw : ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) (w : V) = 0)
    (hp : IsPrimitive w) (A : Type*) [CommRing A] :
    Function.Injective (kostantRootSubgroupParam e h ρ M hM i hnil (CommAlgCat.of ℤ A)) := by
  have hinj := baseChangeExp_injective_of_isPrimitive (R := A)
    (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M
    (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i n hv)
    hnil v w hvw hw hp
  intro u v huv
  apply hinj
  apply LinearMap.ext
  intro z
  have heval := kostantRootSubgroupParam_val_apply e h ρ M hM i hnil (CommAlgCat.of ℤ A)
  exact (heval u z).symm.trans ((congrArg (fun g => g.val z) huv).trans (heval v z))

end TauCeti.UniversalEnvelopingAlgebra
