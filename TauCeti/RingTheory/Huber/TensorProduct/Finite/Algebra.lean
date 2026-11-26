/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.ModuleTopology.NaturallyComplete
public import TauCeti.RingTheory.Huber.TensorProduct.Completion
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Topology.Algebra.Algebra
import TauCeti.RingTheory.Huber.ModuleTopology.FiniteAlgebra

/-!
# Completed base change of finite algebras

For a module-finite `A`-algebra `B` carrying its natural `A`-module topology and a Huber
`A`-algebra `C` (with adic structure maps from `A`), the tensor topology on `C ⊗[A] B` agrees with
the natural `C`-module topology (`tensorTopology_eq_moduleTopology_of_finite`). Whenever `C ⊗[A] B`
is naturally complete over `C` — in particular when `C` is complete Hausdorff and `B` is projective
over `A`, or when `C` is complete Hausdorff of noetherian type — the canonical map
`C ⊗[A] B → CompletedTensor A C B` is bijective
(`CompletedTensor.toCompletion_bijective_of_isNaturallyComplete`). Neither completeness of `A` nor
étaleness of `B` is necessary.

Whenever `C ⊗[A] B` is naturally complete over `C`, the equivalence
`CompletedTensor.baseChangeEquiv` is the canonical tensor map, not an unspecified isomorphism,
and is a homeomorphism for the natural `C`-module topology. The corresponding plus-ring transport
for Huber pairs lives in `TauCeti.RingTheory.Huber.TensorProduct.Plus`.

## References

* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §7, proof of Lemma 7.3(ii).
* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371
  (2015), §2.2, Lemma 2.2.12(a), and §2.4, Remark 2.4.2.
-/

public section

open TensorProduct Algebra.TensorProduct

namespace TauCeti.Huber

/-- If the right factor is a finite algebra with its natural topology, the tensor
topology is the natural module topology over the left factor. No completeness,
separatedness, or projectivity hypothesis is needed for this identification. -/
theorem tensorTopology_eq_moduleTopology_of_finite
    (A C B : Type*) [CommRing A] [CommRing C] [CommRing B]
    [Algebra A C] [Algebra A B]
    [TopologicalSpace A] [TopologicalSpace C] [TopologicalSpace B]
    [IsTopologicalRing A] [IsTopologicalRing C] [IsTopologicalRing B] [IsHuberRing C]
    [IsModuleTopology A B] [Module.Finite A B]
    [IsAdicHom (algebraMap A C)] [IsAdicHom (algebraMap A B)] :
    tensorTopology A C B = moduleTopology C (C ⊗[A] B) := by
  let : TopologicalSpace (C ⊗[A] B) := moduleTopology C (C ⊗[A] B)
  have : IsTopologicalRing (C ⊗[A] B) := IsModuleTopology.isTopologicalRing C _
  have : IsHuberRing (C ⊗[A] B) := IsHuberRing.of_isModuleTopology (A := C)
  have hC : Continuous (algebraMap C (C ⊗[A] B)) := continuous_algebraMap C _
  have hA : Continuous (algebraMap A (C ⊗[A] B)) := by
    rw [IsScalarTower.algebraMap_eq A C (C ⊗[A] B)]
    exact hC.comp (IsAdicHom.continuous (inferInstance : IsAdicHom (algebraMap A C)))
  have hB : Continuous (includeRight : B →ₐ[A] C ⊗[A] B) :=
    IsModuleTopology.continuous_of_ringHom (R := A) _ (by simpa using hA)
  have h := (RingHom.continuous_tensorTopology_iff (A := A) (B := C) (C := B)
    (RingHom.id (C ⊗[A] B))).mpr ⟨hC, hB⟩
  apply le_antisymm (continuous_id_iff_le.mp h)
  let : TopologicalSpace (C ⊗[A] B) := tensorTopology A C B
  have : IsTopologicalRing (C ⊗[A] B) := isTopologicalRing_tensorTopology A C B
  have : ContinuousSMul C (C ⊗[A] B) :=
    continuousSMul_of_algebraMap C _ (isAdicHom_includeLeft_tensorTopology A C B).continuous
  exact moduleTopology_le C (C ⊗[A] B)

section NaturallyComplete

variable (A C B : Type*) [CommRing A] [CommRing C] [CommRing B]
  [Algebra A C] [Algebra A B]
  [TopologicalSpace A] [IsTopologicalRing A]
  [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
  [TopologicalSpace B] [IsTopologicalRing B] [IsModuleTopology A B]
  [Module.Finite A B]
  [IsAdicHom (algebraMap A C)] [IsAdicHom (algebraMap A B)]

private theorem isHomeomorph_toCompletion_tensorTopology
    (h : IsNaturallyComplete C (C ⊗[A] B)) :
    letI := tensorTopology A C B
    IsHomeomorph (CompletedTensor.toCompletion A C B) := by
  let := tensorTopology A C B
  have := isTopologicalRing_tensorTopology A C B
  let := IsTopologicalAddGroup.rightUniformSpace (C ⊗[A] B)
  have : IsUniformAddGroup (C ⊗[A] B) := isUniformAddGroup_of_addCommGroup
  have : IsModuleTopology C (C ⊗[A] B) := ⟨tensorTopology_eq_moduleTopology_of_finite A C B⟩
  have ⟨_, _⟩ := (isNaturallyComplete_iff (A := C) (M := C ⊗[A] B)).mp h
  exact CompletedTensor.isHomeomorph_toCompletion A C B inferInstance inferInstance

namespace CompletedTensor

/-- For a module-finite `A`-algebra `B` carrying the `A`-module topology and a Huber `A`-algebra
`C` such that `C ⊗[A] B` is naturally complete over `C`, the canonical map
`C ⊗[A] B → CompletedTensor A C B` is bijective. -/
theorem toCompletion_bijective_of_isNaturallyComplete
    (h : IsNaturallyComplete C (C ⊗[A] B)) :
    Function.Bijective (toCompletion A C B) := by
  let := tensorTopology A C B
  exact (isHomeomorph_toCompletion_tensorTopology A C B h).bijective

attribute [local instance] leftAlgebra

/-- The natural module topology on the finite base change. -/
noncomputable local instance tensorModuleTopology : TopologicalSpace (C ⊗[A] B) :=
  moduleTopology C (C ⊗[A] B)
local instance : IsTopologicalRing (C ⊗[A] B) := IsModuleTopology.isTopologicalRing C _
local instance : IsHuberRing (C ⊗[A] B) := IsHuberRing.of_isModuleTopology (A := C)

/-- **Completed base change of a naturally complete finite algebra needs no completion.**
The forward map is the canonical map on algebraic tensors, as a `C`-algebra isomorphism via
`CompletedTensor.leftAlgebra`. The topology on the source for the homeomorphism theorem below is
the natural `C`-module topology. -/
noncomputable def baseChangeEquiv (h : IsNaturallyComplete C (C ⊗[A] B)) :
    C ⊗[A] B ≃ₐ[C] CompletedTensor A C B :=
  { RingEquiv.ofBijective (toCompletion A C B)
      (toCompletion_bijective_of_isNaturallyComplete A C B h) with
    commutes' := fun c ↦ by
      simp [Algebra.TensorProduct.algebraMap_apply, algebraMap_leftAlgebra] }

/-- The base-change equivalence is the canonical tensor map on every element. -/
@[simp]
theorem baseChangeEquiv_apply (h : IsNaturallyComplete C (C ⊗[A] B)) (x : C ⊗[A] B) :
    baseChangeEquiv A C B h x = toCompletion A C B x := (rfl)

/-- The inverse comparison recovers every algebraic tensor. -/
@[simp]
theorem baseChangeEquiv_symm_toCompletion (h : IsNaturallyComplete C (C ⊗[A] B))
    (x : C ⊗[A] B) :
    (baseChangeEquiv A C B h).symm (toCompletion A C B x) = x :=
  (baseChangeEquiv A C B h).symm_apply_apply x

/-- The inverse comparison takes the left coprojection to the left pure tensor. -/
@[simp]
theorem baseChangeEquiv_symm_inl (h : IsNaturallyComplete C (C ⊗[A] B)) (c : C) :
    (baseChangeEquiv A C B h).symm (inl A C B c) = c ⊗ₜ[A] 1 := by
  apply (baseChangeEquiv A C B h).injective
  simp

/-- The inverse comparison takes the right coprojection to the right pure tensor. -/
@[simp]
theorem baseChangeEquiv_symm_inr (h : IsNaturallyComplete C (C ⊗[A] B)) (b : B) :
    (baseChangeEquiv A C B h).symm (inr A C B b) = 1 ⊗ₜ[A] b := by
  apply (baseChangeEquiv A C B h).injective
  simp

/-- The canonical comparison is a homeomorphism for the natural module topology. -/
theorem isHomeomorph_baseChangeEquiv (h : IsNaturallyComplete C (C ⊗[A] B)) :
    IsHomeomorph (baseChangeEquiv A C B h) := by
  have hfun : (baseChangeEquiv A C B h : C ⊗[A] B → CompletedTensor A C B) =
      toCompletion A C B := funext (baseChangeEquiv_apply A C B h)
  have htop : tensorModuleTopology A C B = tensorTopology A C B :=
    (tensorTopology_eq_moduleTopology_of_finite A C B).symm
  rw [hfun, htop]
  exact isHomeomorph_toCompletion_tensorTopology A C B h

end CompletedTensor

end NaturallyComplete

end TauCeti.Huber
