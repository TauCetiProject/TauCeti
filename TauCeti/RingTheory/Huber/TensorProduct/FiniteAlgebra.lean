/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.ModuleTopology.NaturallyComplete
public import TauCeti.RingTheory.Huber.ModuleTopology.Pair
public import TauCeti.RingTheory.Huber.TensorProduct.Pair
import Mathlib.Topology.Algebra.Algebra

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
`Pair.finiteAlgebra.baseChangeEquiv` is the canonical tensor map, not an unspecified isomorphism,
and is a homeomorphism for the natural `C`-module topology. If `B⁺` is the integral closure of
the image of `A⁺`, it carries the integral closure of `C⁺` onto the completed tensor plus ring.
In particular finite étale base change requires no additional completion, and retains the given
plus ring rather than replacing it by all power-bounded elements.

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

/-- For a module-finite `A`-algebra `B` carrying the `A`-module topology and a Huber `A`-algebra
`C` such that `C ⊗[A] B` is naturally complete over `C`, the canonical map
`C ⊗[A] B → CompletedTensor A C B` is bijective. -/
theorem CompletedTensor.toCompletion_bijective_of_isNaturallyComplete
    (h : IsNaturallyComplete C (C ⊗[A] B)) :
    Function.Bijective (CompletedTensor.toCompletion A C B) := by
  let := tensorTopology A C B
  exact (isHomeomorph_toCompletion_tensorTopology A C B h).bijective

namespace Pair.finiteAlgebra

attribute [local instance] CompletedTensor.leftAlgebra

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
  { RingEquiv.ofBijective (CompletedTensor.toCompletion A C B)
      (CompletedTensor.toCompletion_bijective_of_isNaturallyComplete A C B h) with
    commutes' := fun c ↦ by
      simp [Algebra.TensorProduct.algebraMap_apply, CompletedTensor.algebraMap_leftAlgebra] }

/-- The base-change equivalence is the canonical tensor map on every element. -/
@[simp]
theorem baseChangeEquiv_apply (h : IsNaturallyComplete C (C ⊗[A] B)) (x : C ⊗[A] B) :
    baseChangeEquiv A C B h x = CompletedTensor.toCompletion A C B x := (rfl)

/-- The inverse comparison recovers every algebraic tensor. -/
@[simp]
theorem baseChangeEquiv_symm_toCompletion (h : IsNaturallyComplete C (C ⊗[A] B))
    (x : C ⊗[A] B) :
    (baseChangeEquiv A C B h).symm (CompletedTensor.toCompletion A C B x) = x :=
  (baseChangeEquiv A C B h).symm_apply_apply x

/-- The inverse comparison takes the left coprojection to the left pure tensor. -/
@[simp]
theorem baseChangeEquiv_symm_inl (h : IsNaturallyComplete C (C ⊗[A] B)) (c : C) :
    (baseChangeEquiv A C B h).symm (CompletedTensor.inl A C B c) = c ⊗ₜ[A] 1 := by
  apply (baseChangeEquiv A C B h).injective
  simp

/-- The inverse comparison takes the right coprojection to the right pure tensor. -/
@[simp]
theorem baseChangeEquiv_symm_inr (h : IsNaturallyComplete C (C ⊗[A] B)) (b : B) :
    (baseChangeEquiv A C B h).symm (CompletedTensor.inr A C B b) = 1 ⊗ₜ[A] b := by
  apply (baseChangeEquiv A C B h).injective
  simp

/-- The canonical comparison is a homeomorphism for the natural module topology. -/
theorem isHomeomorph_baseChangeEquiv (h : IsNaturallyComplete C (C ⊗[A] B)) :
    IsHomeomorph (baseChangeEquiv A C B h) := by
  change @IsHomeomorph _ _ (moduleTopology C (C ⊗[A] B)) _ (CompletedTensor.toCompletion A C B)
  rw [← tensorTopology_eq_moduleTopology_of_finite A C B]
  exact isHomeomorph_toCompletion_tensorTopology A C B h

variable {A C B} [IsHuberRing A] [IsHuberRing B]

/-- The comparison transports the integral-closure plus ring of the finite base change
onto the completed tensor plus ring. No uniformity or sheafiness hypothesis is needed. -/
theorem map_plus_baseChangeEquiv (h : IsNaturallyComplete C (C ⊗[A] B))
    (S : Pair A) (T : Pair C) (f : Pair.Hom S T) (hf : f.toRingHom = algebraMap A C) :
    (T.finiteAlgebra (C ⊗[A] B)).plus.map (baseChangeEquiv A C B h).toRingHom =
      (T.completedTensor A (S.finiteAlgebra B)).plus := by
  let : UniformSpace (C ⊗[A] B) := IsTopologicalAddGroup.rightUniformSpace _
  have : IsUniformAddGroup (C ⊗[A] B) := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace (C ⊗[A] B) := (isNaturallyComplete_iff.mp h).1
  have : T2Space (C ⊗[A] B) := (isNaturallyComplete_iff.mp h).2
  let hleft := Pair.completedTensor.inl A T (S.finiteAlgebra B)
  let hforward := Pair.finiteAlgebra.lift hleft
    (by simp [hleft, CompletedTensor.algebraMap_leftAlgebra])
    (baseChangeEquiv A C B h).toAlgHom
  let hright := Pair.finiteAlgebra.lift
    ((Pair.finiteAlgebra.algebraHom T (C ⊗[A] B)).comp f)
    (by ext a; simp [hf, IsScalarTower.algebraMap_apply A C (C ⊗[A] B)])
    (includeRight : B →ₐ[A] C ⊗[A] B)
  let hback := Pair.completedTensor.lift (A := A)
    (Pair.finiteAlgebra.algebraHom T (C ⊗[A] B)) hright
    (by ext a; simp [hright])
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    simpa [hforward] using hforward.map_mem_plus x hx
  · intro x hx
    refine ⟨(baseChangeEquiv A C B h).symm x, ?_, (baseChangeEquiv A C B h).apply_symm_apply x⟩
    have hcont : Continuous (baseChangeEquiv A C B h).symm :=
      ((baseChangeEquiv A C B h).toEquiv.isHomeomorph_iff.mp
        (isHomeomorph_baseChangeEquiv A C B h)).2
    have hmap : hback.toRingHom = (baseChangeEquiv A C B h).symm.toRingHom := by
      apply CompletedTensor.hom_ext hback.continuous_toRingHom hcont
      · ext c
        simp [hback]
      · ext b
        simp [hback, hright]
    have hx' : (baseChangeEquiv A C B h).symm x = hback.toRingHom x :=
      (RingHom.congr_fun hmap x).symm
    rw [hx']
    exact hback.map_mem_plus x hx

end Pair.finiteAlgebra

end NaturallyComplete

end TauCeti.Huber
