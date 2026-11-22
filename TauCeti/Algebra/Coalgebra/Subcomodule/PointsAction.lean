/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.PointsAction
public import TauCeti.Algebra.Coalgebra.Subcomodule.Finite
public import TauCeti.Algebra.Coalgebra.Subcomodule.Induced
import Mathlib.RingTheory.Flat.Basic

/-!
# Point actions on finite subcomodules

Over a coalgebra `C` that is projective as an `R`-module, every comodule is the directed union of
its finite subcomodules. This file uses the scalar-extension form of that covering,
`TauCeti.Subcomodule.exists_finite_subcomodule_subset_range`, to reduce bijectivity of a point
action `TauCeti.Comodule.endOfPoint` to finite subcomodules.

## Main declarations

* `TauCeti.Comodule.bijective_endOfPoint_of_forall_finite`: bijectivity on all finite
  subcomodules gives bijectivity on the comodule, for a flat value algebra.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.3, for the covering by finite
  subcomodules.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w x

namespace Comodule

variable {R : Type u} [CommSemiring R] {C : Type v} [Semiring C] [Algebra R C] [Coalgebra R C]
  [Module.Projective R C]
  {M : Type w} [AddCommMonoid M] [Module R M] [Comodule R C M]
  {A : Type x} [CommSemiring A] [Algebra R A]

/-- If a point acts bijectively on the scalar extension of every finite subcomodule, it acts
bijectively on the scalar extension of the whole comodule. This uses that the finite subcomodules
cover the comodule (the coalgebra is projective) and that their scalar extensions embed (the
value algebra is flat). -/
theorem bijective_endOfPoint_of_forall_finite [Module.Flat R A] (g : C →ₐ[R] A)
    (h : ∀ N : Subcomodule R C M, Module.Finite R N.toSubmodule →
      Function.Bijective (endOfPoint N g)) :
    Function.Bijective (endOfPoint M g) := by
  have hι (N : Subcomodule R C M) :
      Function.Injective ((Subcomodule.subtype N).toLinearMap.baseChange A) := by
    rw [LinearMap.baseChange_eq_lTensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ (Subcomodule.subtype_injective N)
  have hnat (N : Subcomodule R C M) (z : A ⊗[R] N) :
      endOfPoint M g ((Subcomodule.subtype N).toLinearMap.baseChange A z) =
        (Subcomodule.subtype N).toLinearMap.baseChange A (endOfPoint N g z) :=
    (LinearMap.congr_fun (baseChange_comp_endOfPoint (Subcomodule.subtype N) g) z).symm
  refine ⟨fun y₁ y₂ hy ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨N, hN, hy₁₂⟩ := Subcomodule.exists_finite_subcomodule_subset_range (C := C) {y₁, y₂}
      (Set.toFinite _)
    obtain ⟨z₂, rfl⟩ := hy₁₂ (Set.mem_insert_of_mem y₁ rfl)
    obtain ⟨z₁, rfl⟩ := hy₁₂ (Set.mem_insert _ _)
    rw [hnat, hnat] at hy
    rw [(h N hN).injective (hι N hy)]
  · obtain ⟨N, hN, hy⟩ := Subcomodule.exists_finite_subcomodule_subset_range (C := C) {y}
      (Set.finite_singleton y)
    obtain ⟨z, rfl⟩ := hy (Set.mem_singleton y)
    obtain ⟨w, rfl⟩ := (h N hN).surjective z
    exact ⟨_, hnat N w⟩

end Comodule

end TauCeti
