/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.UniversalProperty
public import Mathlib.Topology.Algebra.UniformRing
public import TauCeti.RingTheory.Huber.Pair
import TauCeti.RingTheory.Huber.Completion.Basic

import TauCeti.RingTheory.Huber.AdicHom.Completion
import TauCeti.Topology.Algebra.UniformRing
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The separated completed tensor ring

`TauCeti.Huber.CompletedTensor A B C` is the separated completion of `B ⊗[A] C` for
the tensor topology along adic structure maps. It is a complete Hausdorff Huber ring.
Its two coprojections represent compatible continuous ring maps into complete Hausdorff
nonarchimedean commutative rings, with no adicness condition on these outgoing maps.

This module constructs the ring and its continuous universal property. Rings of integral
elements are additional data and are not part of this ring-level construction; the only
statement about them here is that closures of images of rings of integral elements of
`B ⊗[A] C` are rings of integral elements of the completion. The completed tensor product of
Huber pairs is in `TauCeti.RingTheory.Huber.TensorProduct.Pair`.

## References

* S. Morel, *Adic spaces*, §II.3.2, Proposition II.3.2.1.
* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3, proof of Lemma 3.9(i).
-/

public section

open TensorProduct Algebra.TensorProduct UniformSpace Topology

namespace TauCeti.Huber

variable (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  [IsTopologicalRing A] [IsTopologicalRing B] [IsTopologicalRing C]
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A C)]

/-- The tensor topology, registered locally on the algebraic tensor product. -/
noncomputable local instance tensorTopologyInstance : TopologicalSpace (B ⊗[A] C) :=
  tensorTopology A B C

local instance tensorTopologicalRing : IsTopologicalRing (B ⊗[A] C) :=
  isTopologicalRing_tensorTopology A B C

local instance tensorHuberRing : IsHuberRing (B ⊗[A] C) :=
  isHuberRing_tensorTopology A B C

/-- The additive group uniformity of the tensor topology. -/
noncomputable local instance tensorUniformity : UniformSpace (B ⊗[A] C) :=
  IsTopologicalAddGroup.rightUniformSpace _

local instance tensorUniformAddGroup : IsUniformAddGroup (B ⊗[A] C) :=
  isUniformAddGroup_of_addCommGroup

/-- The separated completed tensor ring along adic structure maps, without a chosen plus ring. -/
def CompletedTensor := Completion (B ⊗[A] C)

namespace CompletedTensor

noncomputable instance : CommRing (CompletedTensor A B C) :=
  inferInstanceAs (CommRing (Completion (B ⊗[A] C)))

noncomputable instance : UniformSpace (CompletedTensor A B C) :=
  inferInstanceAs (UniformSpace (Completion (B ⊗[A] C)))

instance : IsUniformAddGroup (CompletedTensor A B C) :=
  inferInstanceAs (IsUniformAddGroup (Completion (B ⊗[A] C)))

instance : IsTopologicalRing (CompletedTensor A B C) :=
  inferInstanceAs (IsTopologicalRing (Completion (B ⊗[A] C)))

instance : CompleteSpace (CompletedTensor A B C) :=
  inferInstanceAs (CompleteSpace (Completion (B ⊗[A] C)))

instance : T2Space (CompletedTensor A B C) :=
  inferInstanceAs (T2Space (Completion (B ⊗[A] C)))

/-- Completion of the tensor topology is a Huber ring. -/
instance : IsHuberRing (CompletedTensor A B C) :=
  inferInstanceAs (IsHuberRing (Completion (B ⊗[A] C)))

/-- The canonical map from the algebraic tensor product to its separated completion. -/
noncomputable def toCompletion : B ⊗[A] C →+* CompletedTensor A B C := Completion.coeRingHom

/-- The left coprojection of the completed tensor ring. -/
noncomputable def inl : B →+* CompletedTensor A B C :=
  (toCompletion A B C).comp includeLeftRingHom

/-- The right coprojection of the completed tensor ring. -/
noncomputable def inr : C →+* CompletedTensor A B C :=
  (toCompletion A B C).comp (includeRight : C →ₐ[A] B ⊗[A] C).toRingHom

/-- The canonical map sends pure tensors to products of the two coprojections. -/
@[simp] theorem toCompletion_tmul (b : B) (c : C) :
    toCompletion A B C (b ⊗ₜ[A] c) = inl A B C b * inr A B C c := by
  simpa only [inl, inr, RingHom.comp_apply, includeLeftRingHom_apply,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, includeRight_apply,
    tmul_mul_tmul, mul_one, one_mul] using
    (map_mul (toCompletion A B C) (b ⊗ₜ[A] (1 : C)) ((1 : B) ⊗ₜ[A] c))

/-- The two coprojections agree on the base ring. -/
@[simp] theorem inl_comp_algebraMap : (inl A B C).comp (algebraMap A B) =
    (inr A B C).comp (algebraMap A C) := by
  ext a
  simp [inl, inr, ← Algebra.TensorProduct.algebraMap_apply]

/-- The canonical tensor map is continuous. -/
@[fun_prop] theorem continuous_toCompletion : Continuous (toCompletion A B C) :=
  Completion.continuous_coe _

/-- The left coprojection is continuous. -/
@[fun_prop] theorem continuous_inl : Continuous (inl A B C) :=
  (continuous_toCompletion A B C).comp (isAdicHom_includeLeft_tensorTopology A B C).continuous

/-- The right coprojection is continuous. -/
@[fun_prop] theorem continuous_inr : Continuous (inr A B C) :=
  (continuous_toCompletion A B C).comp (isAdicHom_includeRight_tensorTopology A B C).continuous

/-- The canonical tensor map is adic. -/
theorem isAdicHom_toCompletion : IsAdicHom (toCompletion A B C) := IsAdicHom.coeRingHom

/-- The left coprojection is adic. -/
theorem isAdicHom_inl : IsAdicHom (inl A B C) :=
  (isAdicHom_toCompletion A B C).comp (isAdicHom_includeLeft_tensorTopology A B C)

/-- The right coprojection is adic. -/
theorem isAdicHom_inr : IsAdicHom (inr A B C) :=
  (isAdicHom_toCompletion A B C).comp (isAdicHom_includeRight_tensorTopology A B C)

/-- A Tate left factor makes the completed tensor ring Tate. -/
instance [IsTateRing B] : IsTateRing (CompletedTensor A B C) :=
  IsTateRing.of_continuous (φ := inl A B C) (continuous_inl A B C)

/-- A Tate right factor makes the completed tensor ring Tate. -/
instance [IsTateRing C] : IsTateRing (CompletedTensor A B C) :=
  IsTateRing.of_continuous (φ := inr A B C) (continuous_inr A B C)

/-- Exactly the closure of zero dies in the separated completion. -/
theorem ker_toCompletion : RingHom.ker (toCompletion A B C) = (⊥ : Ideal (B ⊗[A] C)).closure :=
  Completion.ker_coeRingHom

/-- Algebraic tensors are dense in the separated completed tensor ring. -/
theorem denseRange_toCompletion : DenseRange (toCompletion A B C) := Completion.denseRange_coe

/-- The closure of the image of a ring of integral elements of `B ⊗[A] C`, for the tensor
topology, is a ring of integral elements of the completed tensor ring (Wedhorn, Lemma 7.47). -/
theorem isRingOfIntegralElements_topologicalClosure_map {P : Subring (B ⊗[A] C)}
    (hP : IsRingOfIntegralElements P) :
    IsRingOfIntegralElements (P.map (toCompletion A B C)).topologicalClosure :=
  hP.completion

variable {A B C}

/-- Continuous maps out of the completed tensor ring are determined by the two factors. -/
theorem hom_ext {S : Type*} [Semiring S] [TopologicalSpace S] [T2Space S]
    {f g : CompletedTensor A B C →+* S}
    (hf : Continuous f) (hg : Continuous g)
    (hB : f.comp (inl A B C) = g.comp (inl A B C))
    (hC : f.comp (inr A B C) = g.comp (inr A B C)) : f = g := by
  apply Completion.ringHom_ext_of_continuous hf hg
  exact Algebra.TensorProduct.ringHom_ext hB hC

variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [NonarchimedeanRing R] [CompleteSpace R] [T0Space R]

/-- Compatible continuous maps from the factors extend to the completed tensor ring. -/
noncomputable def lift (φ : B →+* R) (ψ : C →+* R)
    (h : φ.comp (algebraMap A B) = ψ.comp (algebraMap A C))
    (hφ : Continuous φ) (hψ : Continuous ψ) : CompletedTensor A B C →+* R := by
  letI := (φ.comp (algebraMap A B)).toAlgebra
  let φ' : B →ₐ[A] R := { __ := φ, commutes' := fun _ ↦ rfl }
  let ψ' : C →ₐ[A] R :=
    { __ := ψ, commutes' := fun a ↦ (RingHom.congr_fun h a).symm }
  let f := (Algebra.TensorProduct.lift φ' ψ' fun _ _ ↦ Commute.all _ _).toRingHom
  apply Completion.extensionHom f
  apply (RingHom.continuous_tensorTopology_iff f).mpr
  constructor
  · exact hφ.congr fun b ↦ by simp [f, φ', ψ']
  · exact hψ.congr fun c ↦ by simp [f, φ', ψ']

private theorem lift_toCompletion_tmul (φ : B →+* R) (ψ : C →+* R)
    (h : φ.comp (algebraMap A B) = ψ.comp (algebraMap A C))
    (hφ : Continuous φ) (hψ : Continuous ψ) (b : B) (c : C) :
    lift φ ψ h hφ hψ (toCompletion A B C (b ⊗ₜ[A] c)) = φ b * ψ c := by
  rw [lift, toCompletion]
  exact (Completion.extensionHom_coe _ _ (b ⊗ₜ[A] c)).trans (by simp)

/-- The extension computes on the left coprojection. -/
@[simp] theorem lift_inl (φ : B →+* R) (ψ : C →+* R)
    (h : φ.comp (algebraMap A B) = ψ.comp (algebraMap A C))
    (hφ : Continuous φ) (hψ : Continuous ψ) (b : B) :
    lift φ ψ h hφ hψ (inl A B C b) = φ b := by
  simpa only [toCompletion_tmul, map_one, mul_one] using (lift_toCompletion_tmul φ ψ h hφ hψ b 1)

/-- The extension computes on the right coprojection. -/
@[simp] theorem lift_inr (φ : B →+* R) (ψ : C →+* R)
    (h : φ.comp (algebraMap A B) = ψ.comp (algebraMap A C))
    (hφ : Continuous φ) (hψ : Continuous ψ) (c : C) :
    lift φ ψ h hφ hψ (inr A B C c) = ψ c := by
  simpa only [toCompletion_tmul, map_one, one_mul] using (lift_toCompletion_tmul φ ψ h hφ hψ 1 c)

/-- The extension is continuous. -/
@[fun_prop] theorem continuous_lift (φ : B →+* R) (ψ : C →+* R)
    (h : φ.comp (algebraMap A B) = ψ.comp (algebraMap A C))
    (hφ : Continuous φ) (hψ : Continuous ψ) : Continuous (lift φ ψ h hφ hψ) :=
  Completion.continuous_extension

/-- The extension restricts to the prescribed left map. -/
@[simp] theorem lift_comp_inl (φ : B →+* R) (ψ : C →+* R)
    (h : φ.comp (algebraMap A B) = ψ.comp (algebraMap A C))
    (hφ : Continuous φ) (hψ : Continuous ψ) :
    (lift φ ψ h hφ hψ).comp (inl A B C) = φ := by
  ext b
  simp

/-- The extension restricts to the prescribed right map. -/
@[simp] theorem lift_comp_inr (φ : B →+* R) (ψ : C →+* R)
    (h : φ.comp (algebraMap A B) = ψ.comp (algebraMap A C))
    (hφ : Continuous φ) (hψ : Continuous ψ) :
    (lift φ ψ h hφ hψ).comp (inr A B C) = ψ := by
  ext c
  simp

/-- There is exactly one continuous map extending a compatible pair of continuous factor maps. -/
theorem existsUnique_lift (φ : B →+* R) (ψ : C →+* R)
    (h : φ.comp (algebraMap A B) = ψ.comp (algebraMap A C))
    (hφ : Continuous φ) (hψ : Continuous ψ) :
    ∃! f : CompletedTensor A B C →+* R, Continuous f ∧
      f.comp (inl A B C) = φ ∧ f.comp (inr A B C) = ψ := by
  refine ⟨lift φ ψ h hφ hψ, ⟨continuous_lift φ ψ h hφ hψ, by simp, by simp⟩, ?_⟩
  rintro f ⟨hf, hfB, hfC⟩
  exact hom_ext hf (continuous_lift φ ψ h hφ hψ) (by simpa) (by simpa)

/-- The extension of an adic left map is adic. -/
theorem isAdicHom_lift (φ : B →+* R) (ψ : C →+* R)
    (h : φ.comp (algebraMap A B) = ψ.comp (algebraMap A C))
    (hφ : Continuous φ) (hψ : Continuous ψ) (hφa : IsAdicHom φ) :
    IsAdicHom (lift φ ψ h hφ hψ) :=
  IsAdicHom.of_comp ((lift_comp_inl φ ψ h hφ hψ).symm ▸ hφa) (continuous_inl A B C)
    (continuous_lift φ ψ h hφ hψ)

end CompletedTensor

end TauCeti.Huber
