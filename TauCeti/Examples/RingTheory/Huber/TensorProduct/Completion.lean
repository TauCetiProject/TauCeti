/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Completion
public import TauCeti.RingTheory.Huber.Padic.Field

/-!
# Using the completed tensor ring

The integral maps from the discrete integers into the `p`-adic integers extend to the
completed self-tensor even though these outgoing maps are not adic. The computations below
use only the public interface. Generic checks test the structures visible to an importing
module, including the zero-factor case.
-/

public section

open TensorProduct Topology TauCeti.Huber

section Generic

variable (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]

noncomputable example : CommRing (CompletedTensor A B C) := inferInstance
noncomputable example : UniformSpace (CompletedTensor A B C) := inferInstance
example : IsUniformAddGroup (CompletedTensor A B C) := inferInstance
example : IsTopologicalRing (CompletedTensor A B C) := inferInstance
example : IsHuberRing (CompletedTensor A B C) := inferInstance
example : CompleteSpace (CompletedTensor A B C) := inferInstance
example : T2Space (CompletedTensor A B C) := inferInstance
example [IsTateRing B] : IsTateRing (CompletedTensor A B C) := inferInstance
example [IsTateRing C] : IsTateRing (CompletedTensor A B C) := inferInstance

example [Subsingleton B] : Subsingleton (CompletedTensor A B C) :=
  (CompletedTensor.inl A B C).codomain_trivial

example [Subsingleton C] : Subsingleton (CompletedTensor A B C) :=
  (CompletedTensor.inr A B C).codomain_trivial

example : letI := tensorTopology A B C; Continuous (CompletedTensor.toCompletion A B C) :=
  CompletedTensor.continuous_toCompletion A B C

example : letI := tensorTopology A B C;
    letI := isTopologicalRing_tensorTopology A B C;
    RingHom.ker (CompletedTensor.toCompletion A B C) = (⊥ : Ideal (B ⊗[A] C)).closure :=
  CompletedTensor.ker_toCompletion A B C

end Generic

section Padic

variable {p : ℕ} [Fact p.Prime]

local instance : IsAdicHom (algebraMap ℤ ℤ) := by
  simpa using (IsAdicHom.id (A := ℤ))

-- Non-adic outgoing maps are deliberately permitted by the universal property.
example : ¬ IsAdicHom (Int.castRingHom ℤ_[p]) := by
  intro hf
  have hopen := hf.isOpen_map (I := ⊥) (isOpen_discrete _)
  have hzero : IsOpen ((⊥ : Ideal ℤ_[p]) : Set ℤ_[p]) := by simpa using hopen
  exact (IsDiscreteValuationRing.isOpen_iff.mp hzero) rfl

example : Nontrivial (CompletedTensor ℤ ℤ ℤ) :=
  (CompletedTensor.lift (Int.castRingHom ℤ_[p]) (Int.castRingHom ℤ_[p]) rfl
    continuous_of_discreteTopology continuous_of_discreteTopology).domain_nontrivial

-- Both factors contribute, with no hypothesis on the residue characteristic.
example : CompletedTensor.lift (Int.castRingHom ℤ_[p]) (Int.castRingHom ℤ_[p]) rfl
    continuous_of_discreteTopology continuous_of_discreteTopology
      (CompletedTensor.toCompletion ℤ ℤ ℤ ((2 : ℤ) ⊗ₜ[ℤ] (3 : ℤ))) = 6 := by
  rw [CompletedTensor.toCompletion_tmul, map_mul, CompletedTensor.lift_inl,
    CompletedTensor.lift_inr]
  norm_num

-- Uniqueness is stated on both prescribed coprojections.
example : ∃! f : CompletedTensor ℤ ℤ ℤ →+* ℤ_[p], Continuous f ∧
    f.comp (CompletedTensor.inl ℤ ℤ ℤ) = Int.castRingHom ℤ_[p] ∧
    f.comp (CompletedTensor.inr ℤ ℤ ℤ) = Int.castRingHom ℤ_[p] :=
  CompletedTensor.existsUnique_lift _ _ rfl
    continuous_of_discreteTopology continuous_of_discreteTopology

end Padic
