/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.Complex.FirstChernClass.Tensor

/-!
# Clients of the naturality of `c₁` of a tensor product

The trivial line `B × ℂ` has the nowhere-zero constant section `1`, so tensoring with it on either
side leaves `c₁` unchanged. The tensor square of the pullback of `E` along a continuous map `g` has
the pullback along `g` of `c₁(E ⊗ E)` as its first Chern class.
-/

public noncomputable section

open Bundle Module TauCeti
open scoped TensorProduct TauCeti.ModuleTopology

namespace TauCeti.FirstChernClassTensorClients

variable {B : Type} [TopologicalSpace B]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {E : B → Type} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
  [VectorBundle ℂ F E]

-- Tensoring with the trivial line on the right does not change `c₁`.
example :
    firstChernClass (ProjectiveTensor ℂ F ℂ) (fun x ↦ E x ⊗[ℂ] Trivial B ℂ x) =
      firstChernClass F E :=
  firstChernClass_tensorProduct_eq_of_forall_ne_zero (finrank_self ℂ)
    (s := fun _ ↦ (1 : ℂ))
    ((Trivial.homeomorphProd B ℂ).symm.continuous.comp (continuous_id.prodMk continuous_const))
    fun _ ↦ one_ne_zero

-- Tensoring with the trivial line on the left does not change `c₁`.
example :
    firstChernClass (ProjectiveTensor ℂ ℂ F) (fun x ↦ Trivial B ℂ x ⊗[ℂ] E x) =
      firstChernClass F E :=
  firstChernClass_tensorProduct_eq_of_forall_ne_zero_left (finrank_self ℂ)
    (s := fun _ ↦ (1 : ℂ))
    ((Trivial.homeomorphProd B ℂ).symm.continuous.comp (continuous_id.prodMk continuous_const))
    fun _ ↦ one_ne_zero

-- The tensor square of the pullback of `E` along a map `g` is the pullback of the tensor square.
example {B' : Type} [TopologicalSpace B'] (g : C(B', B)) :
    firstChernClass (ProjectiveTensor ℂ F F) (fun y ↦ (⇑g *ᵖ E) y ⊗[ℂ] (⇑g *ᵖ E) y) =
      TopCat.singularCohomologyMap (TopCat.ofHom g) 2
        (firstChernClass (ProjectiveTensor ℂ F F) (fun x ↦ E x ⊗[ℂ] E x)) :=
  firstChernClass_tensorProduct_pullback g

end TauCeti.FirstChernClassTensorClients
