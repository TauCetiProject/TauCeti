/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TensorProduct.Pair
public import TauCeti.RingTheory.Huber.ModuleTopology.Pair
import TauCeti.RingTheory.Huber.ModuleTopology.NaturallyComplete
import Mathlib.Topology.Algebra.Algebra

/-!
# Completed base change of finite projective algebras

For a finite projective algebra `B` with its natural topology and a complete Hausdorff
Huber algebra `C`, the canonical map `C ⊗[A] B → CompletedTensor A C B` is an isomorphism
of topological rings, provided the structure maps from `A` are adic. Neither completeness
of `A` nor étaleness of `B` is necessary.

The equivalence `Pair.finiteAlgebra.baseChangeEquiv` is the canonical tensor map, not an
unspecified isomorphism. If `B⁺` is the integral closure of the image of `A⁺`, it carries
the integral closure of `C⁺` onto the completed tensor plus ring. In particular finite
étale base change requires no additional completion, and retains the given plus ring
rather than replacing it by all power-bounded elements.

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

variable (A C B : Type*) [CommRing A] [CommRing C] [CommRing B]
  [Algebra A C] [Algebra A B]
  [TopologicalSpace A] [IsTopologicalRing A]
  [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C] [IsHuberRing C]
  [CompleteSpace C] [T2Space C]
  [TopologicalSpace B] [IsTopologicalRing B] [IsModuleTopology A B]
  [Module.Finite A B] [Module.Projective A B]
  [IsAdicHom (algebraMap A C)] [IsAdicHom (algebraMap A B)]

/-- The natural module topology on the finite base change. -/
noncomputable local instance tensorModuleTopology : TopologicalSpace (C ⊗[A] B) :=
  moduleTopology C (C ⊗[A] B)
local instance : IsTopologicalRing (C ⊗[A] B) := IsModuleTopology.isTopologicalRing C _
local instance : IsHuberRing (C ⊗[A] B) := IsHuberRing.of_isModuleTopology (A := C)
/-- The additive uniformity of the natural module topology. -/
noncomputable local instance tensorModuleUniformity : UniformSpace (C ⊗[A] B) :=
  IsTopologicalAddGroup.rightUniformSpace _
local instance : IsUniformAddGroup (C ⊗[A] B) := isUniformAddGroup_of_addCommGroup

local instance tensorComplete : CompleteSpace (C ⊗[A] B) :=
  (isNaturallyComplete_iff.mp (IsNaturallyComplete.of_projective (A := C) (M := C ⊗[A] B))).1

local instance tensorT2 : T2Space (C ⊗[A] B) :=
  (isNaturallyComplete_iff.mp (IsNaturallyComplete.of_projective (A := C) (M := C ⊗[A] B))).2

private noncomputable def fromCompletion : CompletedTensor A C B →+* C ⊗[A] B :=
  CompletedTensor.lift includeLeftRingHom (includeRight : B →ₐ[A] C ⊗[A] B).toRingHom
    (by ext a; simp [← Algebra.TensorProduct.algebraMap_apply])
    (continuous_algebraMap C _) (by
      have : ContinuousSMul A (C ⊗[A] B) :=
        continuousSMul_of_algebraMap A _ <| by
          rw [IsScalarTower.algebraMap_eq A C (C ⊗[A] B)]
          exact (continuous_algebraMap C _).comp
            (IsAdicHom.continuous (inferInstance : IsAdicHom (algebraMap A C)))
      exact IsModuleTopology.continuous_of_linearMap
        (includeRight : B →ₐ[A] C ⊗[A] B).toLinearMap)

private theorem continuous_fromCompletion : Continuous (fromCompletion A C B) :=
  CompletedTensor.continuous_lift _ _ _ _ _

private theorem fromCompletion_toCompletion (x : C ⊗[A] B) :
    fromCompletion A C B (CompletedTensor.toCompletion A C B x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul c b => simp [fromCompletion]
  | add x y hx hy => simp [hx, hy]

private theorem toCompletion_fromCompletion (x : CompletedTensor A C B) :
    CompletedTensor.toCompletion A C B (fromCompletion A C B x) = x := by
  have hc : Continuous (CompletedTensor.toCompletion A C B) :=
    IsModuleTopology.continuous_of_ringHom (R := C) _ <| by
      convert CompletedTensor.continuous_inl A C B using 1
      ext c
      simp [Algebra.TensorProduct.algebraMap_apply]
  have h : (CompletedTensor.toCompletion A C B).comp (fromCompletion A C B) = RingHom.id _ := by
    apply CompletedTensor.hom_ext (hc.comp (continuous_fromCompletion A C B)) continuous_id
    · ext c
      simp [fromCompletion]
    · ext b
      simp [fromCompletion]
  exact RingHom.congr_fun h x

namespace Pair.finiteAlgebra

/-- **Completed base change of a finite projective algebra needs no completion.**
The forward map is the canonical map on algebraic tensors. The topology on the source
for the homeomorphism theorem below is the natural `C`-module topology. -/
noncomputable def baseChangeEquiv : C ⊗[A] B ≃+* CompletedTensor A C B :=
  RingEquiv.ofBijective (CompletedTensor.toCompletion A C B)
    ⟨Function.LeftInverse.injective (fromCompletion_toCompletion A C B),
      Function.RightInverse.surjective (toCompletion_fromCompletion A C B)⟩

/-- The base-change equivalence is the canonical tensor map on every element. -/
@[simp]
theorem baseChangeEquiv_apply (x : C ⊗[A] B) :
    baseChangeEquiv A C B x = CompletedTensor.toCompletion A C B x := (rfl)

/-- The inverse comparison recovers every algebraic tensor. -/
@[simp]
theorem baseChangeEquiv_symm_toCompletion (x : C ⊗[A] B) :
    (baseChangeEquiv A C B).symm (CompletedTensor.toCompletion A C B x) = x :=
  (baseChangeEquiv A C B).symm_apply_apply x

/-- The inverse comparison takes the left coprojection to the left pure tensor. -/
@[simp]
theorem baseChangeEquiv_symm_inl (c : C) :
    (baseChangeEquiv A C B).symm (CompletedTensor.inl A C B c) = c ⊗ₜ[A] 1 := by
  apply (baseChangeEquiv A C B).injective
  simp

/-- The inverse comparison takes the right coprojection to the right pure tensor. -/
@[simp]
theorem baseChangeEquiv_symm_inr (b : B) :
    (baseChangeEquiv A C B).symm (CompletedTensor.inr A C B b) = 1 ⊗ₜ[A] b := by
  apply (baseChangeEquiv A C B).injective
  simp

/-- The canonical comparison is a homeomorphism for the natural module topology. -/
theorem isHomeomorph_baseChangeEquiv : IsHomeomorph (baseChangeEquiv A C B) := by
  have hc : Continuous (CompletedTensor.toCompletion A C B) :=
    IsModuleTopology.continuous_of_ringHom (R := C) _ <| by
      convert CompletedTensor.continuous_inl A C B using 1
      ext c
      simp [Algebra.TensorProduct.algebraMap_apply]
  apply Homeomorph.isHomeomorph
    (Homeomorph.mk (baseChangeEquiv A C B).toEquiv hc ?_)
  have h : (fun x ↦ (baseChangeEquiv A C B).symm x) = fromCompletion A C B := by
    funext x
    apply (baseChangeEquiv A C B).injective
    simp [toCompletion_fromCompletion]
  exact (continuous_fromCompletion A C B).congr (congrFun h.symm)

variable {A C B} [IsHuberRing A] [IsHuberRing B]

/-- The comparison transports the integral-closure plus ring of the finite base change
onto the completed tensor plus ring. No uniformity or sheafiness hypothesis is needed. -/
theorem map_plus_baseChangeEquiv (S : Pair A) (T : Pair C)
    (f : Pair.Hom S T) (hf : f.toRingHom = algebraMap A C) :
    (T.finiteAlgebra (C ⊗[A] B)).plus.map (baseChangeEquiv A C B).toRingHom =
      (T.completedTensor A (S.finiteAlgebra B)).plus := by
  let : Algebra C (CompletedTensor A C B) := (CompletedTensor.inl A C B).toAlgebra
  let hleft := Pair.completedTensor.inl A T (S.finiteAlgebra B)
  let hforward := Pair.finiteAlgebra.lift hleft
    (by simp [hleft, RingHom.algebraMap_toAlgebra])
    ({ CompletedTensor.toCompletion A C B with
      commutes' := fun c ↦ by
        simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.algebraMap_apply] } :
      C ⊗[A] B →ₐ[C] CompletedTensor A C B)
  let hright := Pair.finiteAlgebra.lift
    ((Pair.finiteAlgebra.algebraHom T (C ⊗[A] B)).comp f)
    (by ext a; simp [hf, IsScalarTower.algebraMap_apply A C (C ⊗[A] B)])
    (includeRight : B →ₐ[A] C ⊗[A] B)
  let hback := Pair.completedTensor.lift (A := A)
    (Pair.finiteAlgebra.algebraHom T (C ⊗[A] B)) hright
    (by ext a; simp [hright, IsScalarTower.algebraMap_apply A C (C ⊗[A] B)])
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    simpa [hforward] using hforward.map_mem_plus x hx
  · intro x hx
    refine ⟨fromCompletion A C B x, ?_, toCompletion_fromCompletion A C B x⟩
    have hmap : hback.toRingHom = fromCompletion A C B := by
      apply CompletedTensor.hom_ext hback.continuous_toRingHom
        (continuous_fromCompletion A C B)
      · ext c
        simp [hback, fromCompletion, Algebra.TensorProduct.algebraMap_apply]
      · ext b
        simp [hback, hright, fromCompletion]
    rw [← hmap]
    exact hback.map_mem_plus x hx

end Pair.finiteAlgebra

end TauCeti.Huber
